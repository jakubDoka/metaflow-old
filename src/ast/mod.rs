//! Module ast handles the ast construction. The main entity [`Ast`] + [`AstEnt`]
//! create a tree structure that tries to take as little space as possible. And even then,
//! it provides tools to reorganize and drop no longer needed trees.
use cranelift::{
    codegen::packed_option::ReservedValue,
    entity::{EntityList, ListPool, PrimaryMap, SecondaryMap},
};
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use crate::{
    entities::{Ast, Source, CallConv, Vis},
    lexer::{
        self, token, Token, 
        Sources, Span, 
        SourceEnt, 
        LineData
    }, util::pool::PoolRef,
};

use std::{
    fmt::Write,
    sync::atomic::{AtomicU64, Ordering}, time::SystemTime,
};

pub use ast_ent::{AstEnt, AKind, AstDisplay, OpKind};
pub use error::{Error, AEKind};
pub use context::Context;
pub use ast_data::{AstData, RelocContext};
pub use state::State;
pub use dep::Dep;
pub use import::Import;
pub use manifest::Manifest;

type Result<T = ()> = std::result::Result<T, Error>;

/// Parses the tokens into ast tree. Result is stored in [`AstData`]
/// and some temporary details are stored in context.
pub struct Parser<'a> {
    sources: &'a Sources,
    state: &'a mut State,
    data: &'a mut AstData,
    ctx: &'a mut Context,
}

impl<'a> Parser<'a> {
    /// Because of private fields.
    pub fn new(
        sources: &'a Sources, 
        state: &'a mut State,
        data: &'a mut AstData, 
        ctx: &'a mut Context,
    ) -> Self {
        Self {
            sources,
            state,
            ctx,
            data,
        }
    }

    /// Parses the manifest, assuming state is pointing to manifest source.
    pub fn parse_manifest(&mut self) -> Result<Manifest> {
        let mut attrs = vec![];
        let mut deps = vec![];
        loop {
            match self.state.current_kind() {
                token::Kind::Eof => break,
                token::Kind::Indent(_) => {
                    self.next()?;
                    continue;
                }
                token::Kind::Ident => (),
                _ => {
                    return Err(self.unexpected_str("every item in manifest starts with identifier"))
                }
            }
            let name = self.state.current().span();
            self.next()?;
            match self.state.current_kind() {
                token::Kind::Op if self.display(self.state.current()) == "=" => {
                    self.next()?;

                    if self.state.current_kind() != token::Kind::String {
                        return Err(self.unexpected_str("expected string literal"));
                    }

                    attrs.push((name, self.state.current().span().slice(1..self.state.current().len() - 2)));

                    self.next()?;
                }
                token::Kind::Colon => match self.sources.display(name) {
                    "dependencies" => {
                        self.next()?;
                        self.walk_block(|s| {
                            let token = s.state.current();

                            s.expect_str(token::Kind::Ident, "expected dependency name")?;
                            let name = token.span();
                            s.next()?;

                            if s.state.current_kind() != token::Kind::String {
                                return Err(s.unexpected_str("expected string literal as repository link with version or local path"));
                            }
                            let path_and_version = s.state.current().span().slice(1..s.state.current().len() - 2);
                            s.next()?;

                            let (path_end, version_start) = s
                                .sources
                                .display(path_and_version)
                                .find('@')
                                .map(|i| (i, i + 1))
                                .unwrap_or((path_and_version.len(), path_and_version.len()));

                            let path = path_and_version.slice(0..path_end);
                            let version = path_and_version.slice(version_start..path_and_version.len());

                            let token = token.join(s.state.current());

                            let external = s.sources.display(path).starts_with("github.com");

                            let dependency = Dep {
                                external,
                                name,
                                path,
                                version,
                                token
                            };

                            deps.push(dependency);
                            Ok(())
                        })?;
                    }
                    _ => {
                        return Err(self.unexpected(format!(
                            "unexpected item in manifest '{}'",
                            self.sources.display(name)
                        )));
                    }
                },
                _ => {
                    return Err(
                        self.unexpected_str("expected '=' or ':' after identifier in manifest")
                    );
                }
            }
        }

        Ok(Manifest::new(attrs, deps))
    }

    /// Parses juts import statement from the file. 
    /// It can optionally return module doc tokens.
    pub fn parse_imports(&mut self, imports: &mut Vec<Import>) -> Result<Vec<Token>> {
        debug_assert!(imports.is_empty());
        let mut comments = vec![];
        loop {
            match self.state.current_kind() {
                token::Kind::Indent(_) => {
                    self.next()?;
                    continue;
                }
                token::Kind::Comment(true) => {
                    comments.push(self.state.current());
                    self.next()?;
                    continue;
                }
                token::Kind::Use => {
                    self.next()?;
                    self.walk_block(|s| s.import_line(imports))?;
                }
                _ => break,
            }
        }

        Ok(comments)
    }

    /// Parses one import line.
    pub fn import_line(&mut self, imports: &mut Vec<Import>) -> Result {
        let token = self.state.current();

        let nickname = if self.state.current() == token::Kind::Ident {
            let nickname = self.state.current().span();
            self.next()?;
            Some(nickname)
        } else {
            None
        };

        let path = if let token::Kind::String = self.state.current_kind() {
            self.state.current().span().slice(1..self.state.current().len() - 2)
        } else {
            return Err(self.unexpected_str("expected string literal as import path"));
        };

        self.next()?;
        let token = token.join_trimmed(self.state.current());

        imports.push(Import::new(
            nickname,
            path,
            token,
        ));

        Ok(())
    }

    /// Parses rest of the file. It expects state with which the 
    /// [`Self::parse_imports()`] was called.
    pub fn parse(&mut self) -> Result {
        while self.state.current_kind() != token::Kind::Eof {
            self.top_item(
                Ast::reserved_value(),
                concat!(
                    "expected 'fun' | 'attr' | 'struct' | 'enum'",
                    " | 'union' | 'let' | 'var' | 'impl' | '##'",
                ),
            )?;
        }

        Ok(())
    }

    /// Parses impl block.
    pub fn impl_block(&mut self) -> Result {
        let token = self.state.current();
        self.next()?;

        let vis = self.vis()?;

        let generics = if self.state.current() == token::Kind::LBra {
            let token = self.state.current();
            let mut sons = self.ctx.temp_vec();
            self.list(
                &mut sons,
                token::Kind::LBra,
                token::Kind::Comma,
                token::Kind::RBra,
                Self::ident,
            )?;
            let sons = self.data.add_slice(sons.as_slice());
            let token = token.join_trimmed(self.state.current());
            self.data.add(AstEnt::new(AKind::Group, sons, token))
        } else {
            Ast::reserved_value()
        };

        let expr = self.type_expr()?;
        let sons = self.data.add_slice(&[generics, expr]);
        let token = token.join_trimmed(self.state.current());
        let impl_ast = self.data.add(AstEnt::new(AKind::Impl(vis), sons, token));

        self.expect_str(token::Kind::Colon, "expected ':' after 'impl' type")?;
        self.next()?;
        self.walk_block(|s| {
            s.top_item(impl_ast, "expected 'fun' | 'attr' | 'let' | 'var' | '##'")
        })?;

        Ok(())
    }

    /// Parses top item. `impl_ast` is added to each item if provided, `message` is what
    /// gets displayed as error message if invalid item was encountered.
    pub fn top_item(&mut self, impl_ast: Ast, message: &'static str) -> Result {
        let kind = self.state.current_kind();
        let collect_attributes = matches!(
            kind,
            token::Kind::Union | token::Kind::Enum | token::Kind::Struct | token::Kind::Fun | token::Kind::Var | token::Kind::Let
        );

        let attributes = if collect_attributes {
            let sons = self.ctx.create_attribute_slice(self.data);
            if !sons.is_empty() {
                
                self.data.add(AstEnt::new(AKind::Group, sons, Token::default()))
            } else {
                Ast::reserved_value()
            }
        } else {
            Ast::reserved_value()
        };

        match kind {
            token::Kind::Impl if impl_ast == Ast::reserved_value() => {
                self.ctx.push_local_attributes();
                self.impl_block()?;
                self.ctx.pop_attribute_frame();
            }
            token::Kind::Struct | token::Kind::Union | token::Kind::Enum if impl_ast == Ast::reserved_value() => {
                let item = match kind {
                    token::Kind::Struct => self.structure_declaration(false)?,
                    token::Kind::Union => self.structure_declaration(true)?,
                    token::Kind::Enum => self.enum_declaration()?,
                    _ => unreachable!(),
                };
                self.ctx.add_type((item, attributes));
            }
            token::Kind::Fun => {
                let item = self.fun()?;
                self.ctx.add_fun((item, attributes, impl_ast));
            }
            token::Kind::Var | token::Kind::Let => {
                let item = self.var_statement(true)?;
                self.ctx.add_global((item, attributes, impl_ast));
            }
            token::Kind::Attr => {
                self.attr()?;
            }
            token::Kind::Comment(_) => {
                let ast = AstEnt::sonless(AKind::Comment, self.state.current());
                let ast = self.data.add(ast);
                self.ctx.push_local_attribute(ast);
                self.next()?;
            }
            token::Kind::Indent(_) => {
                self.next()?;
            }

            _ => return Err(self.unexpected_str(message)),
        }

        Ok(())
    }

    /// Parses enum declaration.
    pub fn enum_declaration(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let vis = self.vis()?;

        let name = self.ident()?;

        let variants = if self.state.current() == token::Kind::Colon {
            self.block(Self::ident)?
        } else {
            Ast::reserved_value()
        };

        let sons = self.data.add_slice(&[name, variants]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::Enum(vis), sons, token)))
    }

    /// Parses structure declaration, which can be either struct or union.
    pub fn structure_declaration(&mut self, union: bool) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let vis = self.vis()?;
        let kind = if union {
            AKind::Union(vis)
        } else {
            AKind::Struct(vis)
        };

        let expr = self.type_expr()?;

        let body = if self.state.current() == token::Kind::Colon {
            self.block(Self::structure_field)?
        } else {
            Ast::reserved_value()
        };

        let sons = self.data.add_slice(&[expr, body]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(kind, sons, token)))
    }

    /// Parses s structure field, that can be either of union or struct.
    pub fn structure_field(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let vis = self.vis()?;
        let embedded = if self.state.current() == token::Kind::Embed {
            self.next()?;
            true
        } else {
            false
        };

        let mut sons = self.ctx.temp_vec();

        self.list(
            &mut sons,
            token::Kind::None,
            token::Kind::Comma,
            token::Kind::Colon,
            Self::ident,
        )?;

        sons.push(self.type_expr()?);

        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::StructField(vis, embedded), sons, token)))
    }

    /// Parses an attribute.
    pub fn attr(&mut self) -> Result {
        self.next()?;

        let mut sons = self.ctx.temp_vec();

        self.list(
            &mut sons,
            token::Kind::None,
            token::Kind::Comma,
            token::Kind::None,
            Self::attr_element,
        )?;

        self.ctx.add_attributes(sons.as_slice(), self.sources, self.data);

        Ok(())
    }

    /// parses singular attribute element that is directly recursive.
    pub fn attr_element(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let mut sons = self.ctx.temp_vec();
        sons.push(self.ident()?);

        let kind = match self.state.current_kind() {
            token::Kind::LPar => {
                self.list(
                    &mut sons,
                    token::Kind::LPar,
                    token::Kind::Comma,
                    token::Kind::RPar,
                    Self::attr_element,
                )?;
                AKind::AttributeElement
            }
            token::Kind::Op => {
                if self.display(self.state.current()) == "=" {
                    self.next()?;
                    sons.push(self.expr()?);
                } else {
                    return Err(self.unexpected_str("expected '=' or '('"));
                }
                AKind::AttributeAssign
            }
            _ => AKind::AttributeElement,
        };

        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(kind, sons, token)))
    }

    pub fn fun(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let header = self.fun_header(false)?;
        let body = if self.state.current() == token::Kind::Colon && !self.ctx.is_type_expr() {
            self.stmt_block()?
        } else {
            Ast::reserved_value()
        };

        let sons = self.data.add_slice(&[header, body]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::Fun, sons, token)))
    }

    pub fn fun_header(&mut self, anonymous: bool) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let vis = if anonymous { Vis::None } else { self.vis()? };

        let mut sons = self.ctx.temp_vec();

        let previous = self.ctx.is_type_expr();
        self.ctx.set_is_type_expr(true);
        let is_op = self.state.current_kind() == token::Kind::Op;
        let ident = match self.state.current_kind() {
            token::Kind::Ident | token::Kind::Op if !anonymous => self.ident_expr()?,
            _ => Ast::reserved_value(),
        };
        sons.push(ident);
        self.ctx.set_is_type_expr(previous);

        if self.state.current() == token::Kind::LPar {
            let parser = if self.ctx.is_type_expr() {
                Self::expr
            } else {
                Self::fun_argument
            };
            self.list(&mut sons, token::Kind::LPar, token::Kind::Comma, token::Kind::RPar, parser)?;
        }

        let kind = if is_op {
            let arg_count = sons[1..]
                .iter()
                .fold(0, |acc, &i| acc + self.data.sons(i).len() - 1);
            match arg_count {
                1 => OpKind::Unary,
                2 => OpKind::Binary,
                _ => return Err(Error::new(
                    AEKind::UnexpectedToken(
                        "operator functions can have either 1 or 2 arguments, (unary and binary)"
                            .to_string(),
                    ),
                    token,
                )),
            }
        } else {
            OpKind::Normal
        };

        let ret = if self.state.current() == token::Kind::RArrow {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };
        sons.push(ret);

        let call_conv = if self.state.current() == token::Kind::Ident {
            let ident = self.ident()?;
            let token = self.data.ent(ident).token();
            CallConv::from_str(self.display(token))
                .ok_or_else(|| Error::new(AEKind::InvalidCallConv, token))?
        } else {
            CallConv::default()
        };

        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::FunHeader(kind, vis, call_conv), sons, token)))
    }

    pub fn fun_argument(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let mutable = if token.kind() == token::Kind::Var {
            self.next()?;
            true
        } else {
            false
        };

        let mut sons = self.ctx.temp_vec();
        self.list(
            &mut sons,
            token::Kind::None,
            token::Kind::Comma,
            token::Kind::Colon,
            Self::ident,
        )?;

        sons.push(self.type_expr()?);
        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::FunArgument(mutable), sons, token)))
    }

    pub fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    pub fn statement(&mut self) -> Result<Ast> {
        match self.state.current_kind() {
            token::Kind::Return => self.return_statement(),
            token::Kind::Var | token::Kind::Let => self.var_statement(false),
            token::Kind::Break => return self.break_statement(),
            token::Kind::Continue => return self.continue_statement(),
            _ => self.expr(),
        }
    }

    pub fn var_statement(&mut self, top_level: bool) -> Result<Ast> {
        let token = self.state.current();
        let mutable = token.kind() == token::Kind::Var;

        self.next()?;

        let vis = if top_level { self.vis()? } else { Vis::None };
        let kind = AKind::VarStatement(vis, mutable);
        let mut sons = self.ctx.temp_vec();

        self.walk_block(|s| {
            sons.push(s.var_statement_line()?);
            Ok(())
        })?;

        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(kind, sons, token)))
    }

    pub fn var_statement_line(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let mut ident_group = self.ctx.temp_vec();
        self.list(
            &mut ident_group,
            token::Kind::None,
            token::Kind::Comma,
            token::Kind::None,
            Self::ident,
        )?;
        let token = token.join_trimmed(self.state.current());

        let datatype = if self.state.current() == token::Kind::Colon {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };

        let values = if self.display(self.state.current()) == "=" {
            let token = self.state.current();
            let mut values = self.ctx.temp_vec();
            self.next()?;
            self.list(
                &mut values,
                token::Kind::None,
                token::Kind::Comma,
                token::Kind::None,
                Self::expr,
            )?;
            if values.len() == 1 {
                std::iter::repeat(ident_group[0])
                    .take(ident_group.len() - 1)
                    .for_each(|n| values.push(n));
            } else if values.len() != ident_group.len() {
                return Err(self.unexpected_str(
                    "expected one value per identifier or one value for all identifiers",
                ));
            }
            let values = self.data.add_slice(values.as_slice());
            let token = token.join_trimmed(self.state.current());
            self.data.add(AstEnt::new(AKind::Group, values, token))
        } else {
            Ast::reserved_value()
        };

        if datatype == Ast::reserved_value() && values == Ast::reserved_value() {
            return Err(self.unexpected_str("expected '=' or ':' type"));
        }

        let ident_group = self.data.add_slice(ident_group.as_slice());
        let ident_group = self.data.add(AstEnt::new(AKind::Group, ident_group, token));
        let sons = self.data.add_slice(&[ident_group, datatype, values]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::VarAssign, sons, token)))
    }

    pub fn return_statement(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;
        let ret_val = if let token::Kind::Indent(_) | token::Kind::Eof = self.state.current_kind() {
            Ast::reserved_value()
        } else {
            self.expr()?
        };

        let sons = self.data.add_slice(&[ret_val]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::Return, sons, token)))
    }

    pub fn type_expr(&mut self) -> Result<Ast> {
        let prev = self.ctx.is_type_expr();
        self.ctx.set_is_type_expr(true);

        let result = self.simple_expr();

        self.ctx.set_is_type_expr(prev);

        result
    }

    pub fn expr(&mut self) -> Result<Ast> {
        let expr = self.simple_expr()?;
        self.expr_low(expr)
    }

    pub fn expr_low(&mut self, previous: Ast) -> Result<Ast> {
        let mut result = previous;
        while self.state.current() == token::Kind::Op {
            let token = self.state.current();
            let op = AstEnt::sonless(AKind::Ident, token);
            let pre = self.precedence(token);

            self.next()?;
            self.ignore_newlines()?;

            let mut next = self.simple_expr()?;

            if self.state.current() == token::Kind::Op {
                let dif = pre - self.precedence(self.state.current());

                if dif > 0 {
                    next = self.expr_low(next)?;
                }
            }

            let token = self.data.ent(previous).token().join(self.data.ent(next).token());

            // this handles the '{op}=' sugar
            result = if pre == ASSIGN_PRECEDENCE
                && op.len() != 1
                && self.sources.display(op.span()).chars().last().unwrap() == '='
            {
                let op_token =
                    Token::new(token::Kind::Op, op.span().slice(0..op.len() - 1), op.line_data());
                let operator = self.data.add(AstEnt::sonless(AKind::Ident, op_token));

                let eq_token = Token::new(
                    token::Kind::Op,
                    op.span().slice(op.len() - 1..op.len()),
                    token.line_data(),
                );
                let eq = self.data.add(AstEnt::sonless(AKind::Ident, eq_token));

                let sons = self.data.add_slice(&[operator, result, next]);
                let expr = self.data.add(AstEnt::new(AKind::Binary, sons, token));

                let sons = self.data.add_slice(&[eq, result, expr]);
                self.data.add(AstEnt::new(AKind::Binary, sons, token))
            } else {
                let op = self.data.add(op);
                let sons = self.data.add_slice(&[op, result, next]);
                self.data.add(AstEnt::new(AKind::Binary, sons, token))
            };
        }

        Ok(result)
    }

    pub fn precedence(&self, token: Token) -> i64 {
        precedence(self.sources.display_token(token))
    }

    pub fn simple_expr(&mut self) -> Result<Ast> {
        self.simple_expr_low(false)
    }

    pub fn simple_expr_low(&mut self, nested: bool) -> Result<Ast> {
        let token = self.state.current();
        let mut ast = match self.state.current_kind() {
            token::Kind::Ident => self.ident_expr()?,
            token::Kind::Int(..)
            | token::Kind::Uint(..)
            | token::Kind::Bool(..)
            | token::Kind::Char
            | token::Kind::Float(..)
            | token::Kind::String => {
                self.next()?;
                self.data.add(AstEnt::sonless(AKind::Lit, token))
            }
            token::Kind::LPar => {
                self.next()?;
                let expr = self.expr()?;
                let result = if self.state.current_kind() == token::Kind::Comma {
                    let mut sons = self.ctx.temp_vec();
                    sons.push(expr);
                    self.next()?;
                    self.list(
                        &mut sons,
                        token::Kind::None,
                        token::Kind::Comma,
                        token::Kind::RPar,
                        Self::expr,
                    )?;
                    let sons = self.data.add_slice(sons.as_slice());
                    let token = token.join_trimmed(self.state.current());
                    self.data.add(AstEnt::new(AKind::Tuple, sons, token))
                } else {
                    self.expect_str(token::Kind::RPar, "expected ')'")?;
                    self.next()?;
                    expr
                };
                result
            }
            token::Kind::If => return self.if_expr(),
            token::Kind::For => return self.loop_expr(),
            token::Kind::Op => {
                let mut sons = self.ctx.temp_vec();
                let kind = match self.sources.display(token.span()) {
                    "&" => {
                        self.next()?;
                        let mutable = self.state.current_kind() == token::Kind::Var;
                        if mutable {
                            self.next()?;
                        }
                        AKind::Ref(mutable)
                    }
                    "*" => {
                        self.next()?;
                        AKind::Deref
                    }
                    _ => {
                        sons.push(self.data.add(AstEnt::sonless(AKind::Ident, token)));
                        self.next()?;
                        AKind::Ident
                    }
                };
                let ast = self.simple_expr()?;
                sons.push(ast);
                let sons = self.data.add_slice(sons.as_slice());
                let token = token.join_trimmed(self.state.current());
                return Ok(self.data.add(AstEnt::new(kind, sons, token)));
            }
            token::Kind::Pass => {
                self.next()?;
                return Ok(self.data.add(AstEnt::sonless(AKind::Pass, token)));
            }
            token::Kind::LBra => {
                let mut sons = self.ctx.temp_vec();
                self.list(
                    &mut sons,
                    token::Kind::LBra,
                    token::Kind::Comma,
                    token::Kind::RBra,
                    Self::expr,
                )?;
                let sons = self.data.add_slice(sons.as_slice());
                let token = token.join_trimmed(self.state.current());
                return Ok(self.data.add(AstEnt::new(AKind::Array, sons, token)));
            }
            token::Kind::Fun => return self.fun_header(true),
            _ => todo!("unmatched simple expr pattern {:?}", self.state.current()),
        };

        if !nested && !self.ctx.is_type_expr() {
            loop {
                let new_ast = match self.state.current_kind() {
                    token::Kind::Dot => {
                        self.next()?;
                        let expr = self.simple_expr_low(true)?;
                        let sons = self.data.add_slice(&[ast, expr]);
                        let token = token.join_trimmed(self.state.current());
                        AstEnt::new(AKind::Dot, sons, token)
                    }
                    token::Kind::LPar => {
                        let (kind, sons, _) = self.data.ent(ast).parts();
                        let mut new_sons = self.ctx.temp_vec();
                        let kind = if kind == AKind::Dot {
                            new_sons.push(self.data.get(sons, 1));
                            new_sons.push(self.data.get(sons, 0));
                            AKind::Call(true)
                        } else {
                            new_sons.push(ast);
                            AKind::Call(false)
                        };

                        self.list(
                            &mut new_sons,
                            token::Kind::LPar,
                            token::Kind::Comma,
                            token::Kind::RPar,
                            Self::expr,
                        )?;

                        let sons = self.data.add_slice(new_sons.as_slice());
                        let token = token.join_trimmed(self.state.current());
                        AstEnt::new(kind, sons, token)
                    }
                    token::Kind::LBra => {
                        self.next()?;
                        self.ignore_newlines()?;
                        let expr = self.expr()?;
                        self.ignore_newlines()?;
                        self.expect_str(token::Kind::RBra, "expected ']'")?;
                        self.next()?;

                        let sons = self.data.add_slice(&[ast, expr]);
                        let token = token.join_trimmed(self.state.current());
                        AstEnt::new(AKind::Index, sons, token)
                    }

                    _ => break,
                };

                ast = self.data.add(new_ast);
            }
        }

        Ok(ast)
    }

    pub fn continue_statement(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let label = self.optional_tag()?;
        let sons = self.data.add_slice(&[label]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::Continue, sons, token)))
    }

    pub fn break_statement(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let label = self.optional_tag()?;

        let ret = if let token::Kind::Indent(_) | token::Kind::Eof = self.state.current_kind() {
            Ast::reserved_value()
        } else {
            self.expr()?
        };

        let sons = self.data.add_slice(&[label, ret]);
        let token = token.join_trimmed(self.state.current());
        Ok(self.data.add(AstEnt::new(AKind::Break, sons, token)))
    }

    pub fn loop_expr(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;

        let label = self.optional_tag()?;
        let body = self.stmt_block()?;

        let sons = self.data.add_slice(&[label, body]);
        let token = token.join_trimmed(self.state.current());

        Ok(self.data.add(AstEnt::new(AKind::Loop, sons, token)))
    }

    pub fn optional_tag(&mut self) -> Result<Ast> {
        Ok(if self.state.current() == token::Kind::Tag {
            let token = self.state.current();
            self.next()?;
            self.data.add(AstEnt::sonless(AKind::Ident, token))
        } else {
            Ast::reserved_value()
        })
    }

    pub fn ident_expr(&mut self) -> Result<Ast> {
        let token = self.state.current();
        let mut ast = self.ident()?;

        if self.state.current() == token::Kind::DoubleColon && self.state.peeked() == token::Kind::Ident {
            self.next()?;
            let ident = self.ident()?;
            let sons = if self.state.current() == token::Kind::DoubleColon && self.state.peeked() == token::Kind::Ident {
                self.next()?;
                let last_ident = self.ident()?;
                self.data.add_slice(&[ast, ident, last_ident])
            } else {
                self.data.add_slice(&[ast, ident])
            };
            let token = token.join_trimmed(self.state.current());
            ast = self.data.add(AstEnt::new(AKind::Path, sons, token));
        }

        let is_instantiation =
            self.ctx.is_type_expr() && self.state.current() == token::Kind::LBra || self.state.current() == token::Kind::DoubleColon;

        if is_instantiation {
            if self.state.current() == token::Kind::DoubleColon {
                self.next()?;
            }
            self.expect_str(
                token::Kind::LBra,
                "expected '[' as a start of generic instantiation",
            )?;
            let mut sons = self.ctx.temp_vec();
            sons.push(ast);
            self.list(
                &mut sons,
                token::Kind::LBra,
                token::Kind::Comma,
                token::Kind::RBra,
                Self::expr,
            )?;

            let sons = self.data.add_slice(sons.as_slice());
            let token = token.join_trimmed(self.state.current());
            ast = self.data.add(AstEnt::new(AKind::Instantiation, sons, token));
        }

        Ok(ast)
    }

    
    pub fn if_expr(&mut self) -> Result<Ast> {
        let token = self.state.current();
        self.next()?;
        let condition = self.expr()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.state.current_kind() {
            token::Kind::Else => {
                self.next()?;
                self.stmt_block()?
            }
            token::Kind::Elif => {
                let token = self.state.current();
                let branch = self.if_expr()?;
                let sons = self.data.add_slice(&[branch]);
                let token = token.join_trimmed(self.state.current());
                self.data.add(AstEnt::new(AKind::Elif, sons, token))
            }
            token::Kind::Indent(_) => {
                match self.state.peeked_kind() {
                    token::Kind::Else => {
                        self.next()?;
                        self.next()?;
                        self.stmt_block()?
                    }
                    token::Kind::Elif => {
                        self.next()?;
                        let token = self.state.current();
                        let branch = self.if_expr()?;
                        let sons = self.data.add_slice(&[branch]);
                        let token = token.join_trimmed(self.state.current());
                        self.data.add(AstEnt::new(AKind::Elif, sons, token))
                    }
                    _ => Ast::reserved_value(),
                }
            }
            _ => Ast::reserved_value(),
        };

        let sons = self.data.add_slice(&[condition, then_block, else_block]);

        Ok(self.data.add(AstEnt::new(AKind::If, sons, token)))
    }

    pub fn ident(&mut self) -> Result<Ast> {
        self.expect_str(token::Kind::Ident, "expected ident")?;
        let token = self.state.current();
        self.next()?;
        Ok(self.data.add(AstEnt::sonless(AKind::Ident, token)))
    }

    pub fn vis(&mut self) -> Result<Vis> {
        Ok(match self.state.current_kind() {
            token::Kind::Pub => {
                self.next()?;
                Vis::Public
            }
            token::Kind::Priv => {
                self.next()?;
                Vis::Private
            }
            _ => Vis::None,
        })
    }

    pub fn walk_block<F: FnMut(&mut Self) -> Result>(&mut self, mut parser: F) -> Result {
        if let token::Kind::Indent(level) = self.state.current_kind() {
            if level > self.ctx.level() + 1 {
                return Err(self.unexpected_str(
                    "too deep indentation, one indentation level is equal 2 spaces or one tab",
                ));
            }
            self.ctx.push_level();
            while self.level_continues()? {
                parser(self)?;
            }
        } else {
            parser(self)?;
        }
        Ok(())
    }

    pub fn block<F: FnMut(&mut Self) -> Result<Ast>>(&mut self, mut parser: F) -> Result<Ast> {
        self.expect_str(token::Kind::Colon, "expected ':' as a start of block")?;
        let token = self.state.current();
        let mut sons = self.ctx.temp_vec();
        self.next()?;
        self.walk_block(|s| {
            let expr = parser(s)?;
            sons.push(expr);
            Ok(())
        })?;
        let sons = self.data.add_slice(sons.as_slice());
        let token = token.join_trimmed(self.state.current());
        Ok(self.data.add(AstEnt::new(AKind::Group, sons, token)))
    }

    pub fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.state.current_kind(), token::Kind::Indent(_) | token::Kind::Eof) {
            return Err(self.unexpected_str("expected indentation"));
        }

        loop {
            match self.state.peeked_kind() {
                token::Kind::Indent(_) => {
                    self.next()?;
                }
                token::Kind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.state.current_kind() {
            token::Kind::Indent(level) => {
                if level == self.ctx.level() {
                    self.next()?;
                    Ok(true)
                } else if level < self.ctx.level() {
                    self.ctx.pop_level();
                    Ok(false)
                } else {
                    return Err(self.unexpected_str("unexpected indentation dive"));
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn list<F: FnMut(&mut Self) -> Result<Ast>>(
        &mut self,
        sons: &mut Vec<Ast>,
        start: token::Kind,
        separator: token::Kind,
        end: token::Kind,
        mut parser: F,
    ) -> Result {
        if start != token::Kind::None {
            self.expect(start.clone(), format!("expected {}", start))?;
            self.next()?;
            self.ignore_newlines()?;
        }

        if end != token::Kind::None && self.state.current() == end {
            self.next()?;
            return Ok(());
        }

        let expr = parser(self)?;
        sons.push(expr);

        while self.state.current() == separator {
            self.next()?;
            self.ignore_newlines()?;
            // trailing colon allowed
            if end != token::Kind::None && self.state.current() == end {
                break;
            }
            let expr = parser(self)?;
            sons.push(expr);
        }

        if end != token::Kind::None {
            self.ignore_newlines()?;
            self.expect(end.clone(), format!("expected {}", end))?;
            self.next()?;
        }

        Ok(())
    }

    pub fn ignore_newlines(&mut self) -> Result {
        while let token::Kind::Indent(_) = self.state.current_kind() {
            self.next()?;
        }

        Ok(())
    }

    pub fn next(&mut self) -> Result {
        self.state.advance(self.sources)    
    }

    pub fn expect_str(&self, kind: token::Kind, message: &str) -> Result {
        self.expect(kind, message.to_string())
    }

    pub fn expect(&self, kind: token::Kind, message: String) -> Result {
        if self.state.current_kind() == kind {
            Ok(())
        } else {
            Err(self.unexpected(message))
        }
    }

    pub fn unexpected_str(&self, message: &'static str) -> Error {
        self.unexpected(message.to_string())
    }

    pub fn unexpected(&self, message: String) -> Error {
        Error::new(AEKind::UnexpectedToken(message), self.state.current())
    }

    pub fn display(&self, token: Token) -> &str {
        self.sources.display(token.span())
    }
}

mod a_state {
    use super::*;
    
    impl Sources {
        pub fn attr_of(&self, manifest: &Manifest, name: &str) -> Option<Span> {
            manifest
                .attrs()
                .iter()
                .find(|(a_name, _)| self.display(*a_name) == name)
                .map(|(_, value)| value.clone())
        }
    }
}

mod ast_data {
    use super::*;

    #[cfg(debug_assertions)]
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    
    #[cfg(debug_assertions)]
    #[derive(Debug, Default, Clone, Copy, RealQuickSer)]
    struct RelocSafety {
        id: u64,
    }
    
    #[cfg(debug_assertions)]
    impl RelocSafety {
        pub fn new() -> Self {
            Self {
                id: 1 + COUNTER.fetch_add(1, Ordering::Relaxed),
            }
        }
    
        pub fn check(&mut self, other: &mut Self) -> bool {
            if self.id == 0 {
                *self = *other;
                return true;
            }
            self.id == other.id
        }
    }
    
    pub struct RelocContext {
        mapping: SecondaryMap<Ast, Ast>,
        frontier: Vec<Ast>,
        temp_sons: Vec<Ast>,
        #[cfg(debug_assertions)]
        safety: RelocSafety,
    }
    
    impl RelocContext {
        pub fn clear(&mut self) {
            self.mapping.clear();
            #[cfg(debug_assertions)]
            {
                self.safety = RelocSafety::default();
            }
        }
    }
    
    /// AstData holds the ast trees. There are not headers or top of the tree.
    /// Other data-structures are only meant to read the data.
    #[derive(Debug, Clone, QuickDefault, QuickSer)]
    pub struct AstData {
        entities: PrimaryMap<Ast, AstEnt>,
        connections: ListPool<Ast>,
        #[cfg(debug_assertions)]
        #[default(RelocSafety::new())]
        safety: RelocSafety,
    }
    
    impl AstData {
        pub fn add(&mut self, ast_ent: AstEnt) -> Ast {
            self.entities.push(ast_ent)
        }

        pub fn add_slice(&mut self, slice: &[Ast]) -> EntityList<Ast> {
            EntityList::from_slice(slice, &mut self.connections)
        }

        pub fn get(&self, sons: EntityList<Ast>, index: usize) -> Ast {
            self.slice(sons)[index]
        }
    
        pub fn slice(&self, sons: EntityList<Ast>) -> &[Ast] {
            sons.as_slice(&self.connections)
        }
    
        pub fn len(&self, list: EntityList<Ast>) -> usize {
            list.len(&self.connections)
        }
    
        pub fn is_empty(&self, ast: Ast) -> bool {
            self.sons(ast).is_empty()
        }
    
        pub fn son_len(&self, ast: Ast, index: usize) -> usize {
            self.son_ent(ast, index).sons().len(&self.connections)
        }
    
        pub fn son_ent(&self, ast: Ast, index: usize) -> AstEnt {
            self.ent(self.son(ast, index))
        }
    
        pub fn son(&self, ast: Ast, index: usize) -> Ast {
            self.sons(ast)[index]
        }
    
        pub fn get_son(&self, ast: Ast, index: usize) -> Option<Ast> {
            self.sons(ast).get(index).cloned()
        }
    
        /// Returns parts of the ast.
        pub fn parts(&self, ast: Ast) -> (AKind, EntityList<Ast>, Token) {
            self.ent(ast).parts()
        }
    
        /// Returns the kind of the ast.
        pub fn kind(&self, ast: Ast) -> AKind {
            self.ent(ast).kind()
        }
    
        /// Returns the token of the ast.
        pub fn token(&self, ast: Ast) -> Token {
            self.ent(ast).token()
        }
    
        /// Returns the span of the ast.
        pub fn span(&self, ast: Ast) -> Span {
            self.ent(ast).span()
        }
    
        /// Returns the sons of the ast.
        pub fn sons(&self, ast: Ast) -> &[Ast] {
            self.ent(ast).sons().as_slice(&self.connections)
        }
    
        /// Returns the ast.
        pub fn ent(&self, ast: Ast) -> AstEnt {
            self.entities[ast]
        }
    
        /// Relocates the ast tree from `source` to `self`.
        /// When first transferring between the two, context has to be clear.
        /// But clearing context after each relocation can create duplicate
        /// trees. Don't worry, safety is asserted during the debug builds
        /// at runtime.
        pub fn relocate(&mut self, target: Ast, source: &Self, ctx: &mut RelocContext) -> Ast {
            #[cfg(debug_assertions)]
            {
                assert!(ctx.safety.check(&mut self.safety));
                assert!(ctx.frontier.is_empty());
            }
    
            if !ctx.mapping[target].is_reserved_value() {
                return ctx.mapping[target];
            }
    
            ctx.frontier.push(target);
            ctx.mapping[target] = self.entities.push(AstEnt::default());
            while let Some(target) = ctx.frontier.pop() {
                let (kind, sons, token) = source.entities[target].parts();
                let id = ctx.mapping[target];
                ctx.temp_sons.clear();
                ctx.temp_sons
                    .extend_from_slice(sons.as_slice(&source.connections));
                for s in ctx.temp_sons.iter_mut() {
                    let alloc = self.entities.push(AstEnt::default());
                    ctx.mapping[*s] = alloc;
                    *s = alloc;
                }
                let sons = EntityList::from_slice(&ctx.temp_sons, &mut self.connections);
                self.entities[id] = AstEnt::new(kind, sons, token);
            }
    
            ctx.mapping[target]
        }
    
        pub fn clear(&mut self) {
            self.entities.clear();
            self.connections.clear();
        }
    }
}

mod context {
    use crate::util::pool::Pool;

    use super::*;

    #[derive(Debug, Clone, Default)]
    pub struct Context {
        is_type_expr: bool,
        level: u16,
        
        funs: Vec<(Ast, Ast, Ast)>,
        types: Vec<(Ast, Ast)>,
        globals: Vec<(Ast, Ast, Ast)>,
    
        attrib_stack: Vec<Ast>,
        attrib_frames: Vec<usize>,
        current_attributes: Vec<Ast>,

        pool: Pool,
    }
        
    impl Context {
        pub fn clear(&mut self) {
            self.level = 0;
    
            self.funs.clear();
            self.types.clear();
            self.globals.clear();
    
            self.attrib_stack.clear();
            self.attrib_frames.clear();
            self.current_attributes.clear();
        }
    
        pub fn funs(&self) -> &[(Ast, Ast, Ast)] {
            self.funs.as_slice()
        }
    
        pub fn types(&self) -> &[(Ast, Ast)] {
            self.types.as_slice()
        }
    
        pub fn globals(&self) -> &[(Ast, Ast, Ast)] {
            self.globals.as_slice()
        }
    
        pub fn add_fun(&mut self, fun: (Ast, Ast, Ast)) {
            self.funs.push(fun);
        }
    
        pub fn add_global(&mut self, global: (Ast, Ast, Ast)) {
            self.globals.push(global);
        }
    
        pub fn add_type(&mut self, ty: (Ast, Ast)) {
            self.types.push(ty);
        }
    
        pub fn create_attribute_slice(&mut self, data: &mut AstData) -> EntityList<Ast> {
            self.current_attributes.extend_from_slice(&self.attrib_stack);
            let value = data.add_slice(&self.current_attributes);
            self.current_attributes.clear();
            value
        }
    
        pub fn add_attributes(&mut self, sons: &[Ast], state: &Sources, data: &AstData) {
            for &ast in sons {
                let name = state.display(data.son_ent(ast, 0).span());
                if name == "push" {
                    self.attrib_frames.push(self.attrib_stack.len());
                    for &ast in &data.sons(ast)[1..] {
                        self.attrib_stack.push(ast);
                    }
                } else if name == "pop" {
                    let len = self.attrib_frames.pop().unwrap();
                    self.attrib_stack.truncate(len);
                } else {
                    self.current_attributes.push(ast);
                }
            }
        }

        pub fn temp_vec(&mut self) -> PoolRef<Ast> {
            self.pool.get()
        }

        pub fn level(&self) -> u16 {
            self.level
        }

        pub fn pop_level(&mut self) {
            self.level -= 1;
        }

        pub fn push_level(&mut self) {
            self.level += 1;
        }

        pub fn push_local_attributes(&mut self) {
            self
                .attrib_frames
                .push(self.attrib_stack.len());
            self
                .attrib_stack
                .extend_from_slice(&self.current_attributes);
        }

        pub fn pop_attribute_frame(&mut self) {
            self
                .attrib_stack
                .truncate(self.attrib_frames.pop().unwrap());
        }

        pub fn push_local_attribute(&mut self, ast: Ast) {
            self.current_attributes.push(ast);
        }

        pub fn is_type_expr(&self) -> bool {
            self.is_type_expr
        }

        pub fn set_is_type_expr(&mut self, value: bool) {
            self.is_type_expr = value;
        }
    }
}

mod state {
    use super::*;

    #[derive(Default, Clone, Copy, Debug)]
    pub struct State {
        current: Token,
        peeked: Token,
        inner: lexer::State,
    }

    impl State {
        pub fn new(source: Source, sources: &Sources) -> Result<Self> {
            let mut s = Self::default();

            s.inner = lexer::State::new(source);

            s.advance(sources)?;
            s.advance(sources)?;

            Ok(s)
        }

        pub fn current(&self) -> Token {
            self.current
        }

        pub fn peeked(&self) -> Token {
            self.peeked
        }

        pub fn current_kind(&self) -> token::Kind {
            self.current.kind()
        }

        pub fn peeked_kind(&self) -> token::Kind {
            self.peeked.kind()
        }

        pub fn advance(&mut self, sources: &Sources) -> Result {
            self.current = self.peeked;
            self.peeked = loop {
                let token = self.token_err(sources)?;
                if token.kind() == token::Kind::Comment(false) {
                    continue;
                }
                break token;
            };
            Ok(())
        }

        pub fn token_err(&mut self, sources: &Sources) -> Result<Token> {
            sources.token(&mut self.inner)
                .map_err(|err| Error::new(AEKind::LError(err), Token::default()))
        }
    }
}


mod import {
    use super::*;

    #[derive(Clone, Debug, Default)]
    pub struct Import {
        nickname: Option<Span>,
        path: Span,
        token: Token,
    }

    impl Import {
        pub fn new(nickname: Option<Span>, path: Span, token: Token) -> Self {
            Self {
                nickname,
                path,
                token,
            }
        }

        pub fn token(&self) -> Token {
            self.token
        }

        pub fn path(&self) -> Span {
            self.path
        }

        pub fn nickname(&self) -> Option<Span> {
            self.nickname
        }
    }
}

mod manifest {
    use super::*;

    #[derive(Clone, Debug, Default)]
    pub struct Manifest {
        attrs: Vec<(Span, Span)>,
        deps: Vec<Dep>,
    }
    
    impl Manifest {
        pub fn new(attrs: Vec<(Span, Span)>, deps: Vec<Dep>) -> Self {
            Self {
                attrs,
                deps,
            }
        }

        pub fn attrs(&self) -> &[(Span, Span)] {
            self.attrs.as_slice()
        }
        
        pub fn clear(&mut self) {
            self.attrs.clear();
            self.deps.clear();
        }
    }
}

mod dep {
    use super::*;

    #[derive(Clone, Debug, Copy, Default, RealQuickSer)]
    pub struct Dep {
        pub path: Span,
        pub name: Span,
        pub version: Span,
        pub external: bool,
        pub token: Token,
    }

    impl Dep {
        pub fn new(path: Span, name: Span, version: Span, external: bool, token: Token) -> Self {
            Self {
                path,
                name,
                version,
                external,
                token,
            }
        }

        pub fn token(&self) -> Token {
            self.token
        }

        pub fn path(&self) -> Span {
            self.path
        }

        pub fn name(&self) -> Span {
            self.name
        }

        pub fn version(&self) -> Span {
            self.version
        }

        pub fn external(&self) -> bool {
            self.external
        }
    }
}

const ASSIGN_PRECEDENCE: i64 = 15;

fn precedence(op: &str) -> i64 {
    match op {
        "as" => 2,
        "*" | "/" | "%" => 3,
        "+" | "-" => 4,
        "<<" | ">>" => 5,
        "<" | "<=" | ">" | ">=" => 6,
        "==" | "!=" => 7,
        "&" => 8,
        "^" => 9,
        "|" => 10,
        "&&" => 11,
        "||" => 12,
        _ => {
            if op.chars().last().unwrap() == '=' {
                ASSIGN_PRECEDENCE
            } else {
                14
            }
        }
    }
}

mod ast_ent {
    use super::*;

    #[derive(Debug, Clone, Copy, Default, PartialEq, RealQuickSer)]
    pub struct AstEnt {
        kind: AKind,
        sons: EntityList<Ast>,
        token: Token,
    }
    
    impl AstEnt {
        pub fn new(kind: AKind, sons: EntityList<Ast>, token: Token) -> Self {
            Self { kind, sons, token }
        }
    
        pub fn sonless(kind: AKind, token: Token) -> AstEnt {
            Self {
                kind,
                sons: EntityList::new(),
                token,
            }
        }
    
        pub fn parts(&self) -> (AKind, EntityList<Ast>, Token) {
            (self.kind, self.sons, self.token)
        }
    
        pub fn kind(&self) -> AKind {
            self.kind
        }
    
        pub fn sons(&self) -> EntityList<Ast> {
            self.sons
        }
    
        pub fn span(&self) -> Span {
            self.token.span()
        }
    
        pub fn token(&self) -> Token {
            self.token
        }
    
        pub fn len(&self) -> usize {
            self.span().len()
        }
    
        pub fn line_data(&self) -> LineData {
            self.token.line_data()
        }
    }
    
    pub struct AstDisplay<'a> {
        main_state: &'a Sources,
        state: &'a AstData,
        ast: Ast,
    }
    
    impl<'a> AstDisplay<'a> {
        pub fn new(main_state: &'a Sources, state: &'a AstData, ast: Ast) -> Self {
            Self {
                main_state,
                state,
                ast,
            }
        }
    
        pub fn log(&self, ast: Ast, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            std::iter::repeat(())
                .take(level)
                .for_each(|_| f.write_char(' ').unwrap());
            if ast == Ast::reserved_value() {
                return writeln!(f, "None");
            }
            let (kind, sons, token) = self.state.ent(ast).parts();
            write!(f, "{:?} {:?}", kind, self.main_state.display(token.span()))?;
            if self.state.len(sons) > 0 {
                write!(f, ":\n")?;
                for &child in self.state.slice(sons) {
                    self.log(child, level + 1, f)?;
                }
            } else {
                write!(f, "\n")?;
            }
    
            Ok(())
        }
    }
    
    impl std::fmt::Display for AstDisplay<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.log(self.ast, 0, f)
        }
    }
    
    #[derive(Debug, Clone, Copy, PartialEq, RealQuickSer)]
    pub enum AKind {
        UseStatement(bool),
    
        Path,
    
        Comment,
    
        Fun,
        Impl(Vis),
        FunHeader(OpKind, Vis, CallConv),
        FunArgument(bool),
        Call(bool), // true if dot syntax is used
        Index,
    
        Tuple,
        Union(Vis),
        Struct(Vis),
        StructField(Vis, bool),
    
        Enum(Vis),
    
        Attribute,
        AttributeElement,
        AttributeAssign,
    
        VarStatement(Vis, bool),
        VarAssign,
    
        Return,
    
        Binary,
        Unary,
        If,
        Elif,
        Else,
        Dot,
        Ref(bool), // true if mutable
        Deref,
        Array,
        ExprColonExpr,
    
        Loop,
        Break,
        Continue,
    
        Pass,
    
        Group,
    
        Ident,
        Instantiation,
        Lit,
    }
    
    impl Default for AKind {
        fn default() -> Self {
            AKind::Pass
        }
    }
    
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum OpKind {
        Normal,
        Unary,
        Binary,
    }
}


mod error {
    use crate::lexer::{ErrorDisplayState, DisplayError, ErrorDisplay};

    use super::*;

    impl ErrorDisplayState<Error> for Sources {
        fn fmt(&self, e: &Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match e.kind() {
                AEKind::LError(error) => {
                    writeln!(f, "{}", ErrorDisplay::new(self, error))?;
                },
                AEKind::UnexpectedToken(message) => {
                    writeln!(f, "{}", message)?;
                },
                AEKind::InvalidCallConv => {
                    crate::entities::call_conv_error(f)?;
                },
            }

            Ok(())
        }

        fn sources(&self) -> &Sources {
            self
        }
    }

    #[derive(Debug)]
    pub struct Error {
        pub kind: AEKind,
        pub token: Token,
    }
    
    impl Error {
        pub fn new(kind: AEKind, token: Token) -> Error {
            Error { kind, token }
        }

        pub fn kind(&self) -> &AEKind {
            &self.kind
        }
    }

    impl DisplayError for Error {
        fn token(&self) -> Token {
            self.token
        }
    }
    
    #[derive(Debug)]
    pub enum AEKind {
        LError(lexer::Error),
        UnexpectedToken(String),
        InvalidCallConv,
    }

    impl Into<Error> for AEKind {
        fn into(self) -> Error {
            Error {
                kind: self,
                token: Token::default(),
            }
        }
    }
}

pub fn test() {
    let mut sources = Sources::default();
    let source = SourceEnt::new(
        "text_code.mf".to_string(),
        include_str!("ast_test.mf").to_string(),
        SystemTime::UNIX_EPOCH,
    );

    let source = sources.add_source(source);
    let mut context = Context::default();
    let mut data = AstData::default();
    let mut state = State::new(source, &sources).unwrap();

    let mut a_parser = Parser::new(&mut sources, &mut state, &mut data, &mut context);
    a_parser.parse().unwrap();

    for &(global, attrs, header) in context.globals() {
        println!("===global===");
        print!("{}", AstDisplay::new(&sources, &data, header));
        print!("{}", AstDisplay::new(&sources, &data, attrs));
        print!("{}", AstDisplay::new(&sources, &data, global));
    }

    for &(ty, attrs) in context.types() {
        println!("===type===");
        print!("{}", AstDisplay::new(&sources, &data, attrs));
        print!("{}", AstDisplay::new(&sources, &data, ty));
    }

    for &(fun, attrs, header) in context.funs() {
        println!("===fun===");
        print!("{}", AstDisplay::new(&sources, &data, header));
        print!("{}", AstDisplay::new(&sources, &data, attrs));
        print!("{}", AstDisplay::new(&sources, &data, fun));
    }
}
