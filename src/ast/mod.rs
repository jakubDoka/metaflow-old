//! Module ast handles the ast construction. The main entity [`Ast`] + [`AstEnt`]
//! create a tree structure that tries to take as little space as possible. And even then,
//! it provides tools to reorganize and drop no longer needed trees.
use cranelift::{
    codegen::packed_option::ReservedValue,
    entity::{EntityList, ListPool, PrimaryMap, SecondaryMap},
};
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use crate::{
    entities::{Ast, Source},
    lexer::*,
};

use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicU64, Ordering}, time::SystemTime,
};

pub type Result<T = ()> = std::result::Result<T, AError>;

///
pub struct AParser<'a> {
    main_state: &'a mut AState,
    context: &'a mut AContext,
}

crate::inherit!(AParser<'a>, context, AContext);

impl<'a> AParser<'a> {
    pub fn new(main_state: &'a mut AState, context: &'a mut AContext) -> Self {
        Self {
            main_state,
            context,
        }
    }

    pub fn parse_manifest(&mut self) -> Result<Manifest> {
        let mut manifest = Manifest::default();
        loop {
            match self.token_kind() {
                TKind::Eof => break,
                TKind::Indent(_) => {
                    self.next()?;
                    continue;
                }
                TKind::Ident => (),
                _ => {
                    return Err(self.unexpected_str("every item in manifest starts with identifier"))
                }
            }
            let name = self.token.span();
            self.next()?;
            match self.token_kind() {
                TKind::Op if self.display(self.token) == "=" => {
                    self.next()?;

                    if self.token_kind() != TKind::String {
                        return Err(self.unexpected_str("expected string literal"));
                    }

                    manifest
                        .attrs
                        .push((name, self.token.span().slice(1..self.token.len() - 2)));

                    self.next()?;
                }
                TKind::Colon => match self.main_state.display(name) {
                    "dependencies" => {
                        self.next()?;
                        self.walk_block(|s| {
                            let token = s.token;

                            s.expect_str(TKind::Ident, "expected dependency name")?;
                            let name = token.span();
                            s.next()?;

                            if s.token_kind() != TKind::String {
                                return Err(s.unexpected_str("expected string literal as repository link with version or local path"));
                            }
                            let path_and_version = s.token.span().slice(1..s.token.len() - 2);
                            s.next()?;

                            let (path_end, version_start) = s
                                .main_state
                                .display(path_and_version)
                                .find('@')
                                .map(|i| (i, i + 1))
                                .unwrap_or((path_and_version.len(), path_and_version.len()));

                            let path = path_and_version.slice(0..path_end);
                            let version = path_and_version.slice(version_start..path_and_version.len());

                            let token = token.join(s.token);

                            let external = s.main_state.display(path).starts_with("github.com");

                            let dependency = Dep {
                                external,
                                name,
                                path,
                                version,
                                token
                            };

                            manifest.deps.push(dependency);
                            Ok(())
                        })?;
                    }
                    _ => {
                        return Err(self.unexpected(format!(
                            "unexpected item in manifest '{}'",
                            self.main_state.display(name)
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

        Ok(manifest)
    }

    pub fn take_imports(&mut self, imports: &mut Vec<Import>) -> Result {
        debug_assert!(imports.is_empty());
        while let TKind::Indent(_) = self.token_kind() {
            self.next()?;
        }

        if self.token == TKind::Use {
            self.next()?;
            self.walk_block(|s| s.import_line(imports))?;
        }

        Ok(())
    }

    fn import_line(&mut self, imports: &mut Vec<Import>) -> Result {
        let token = self.token;

        let nickname = if self.token == TKind::Ident {
            let nickname = self.token.span();
            self.next()?;
            Some(nickname)
        } else {
            None
        };

        let path = if let TKind::String = self.token_kind() {
            self.token.span().slice(1..self.token.len() - 2)
        } else {
            return Err(self.unexpected_str("expected string literal as import path"));
        };

        self.next()?;
        let token = token.join_trimmed(self.token);

        imports.push(Import {
            nickname,
            path,
            token,
        });

        Ok(())
    }

    pub fn parse(&mut self) -> Result {
        while self.token_kind() != TKind::Eof {
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

    fn impl_block(&mut self) -> Result {
        let token = self.token;
        self.next()?;

        let vis = self.vis()?;

        let generics = if self.token == TKind::LBra {
            let token = self.token;
            let mut sons = EntityList::new();
            self.list(
                &mut sons,
                TKind::LBra,
                TKind::Comma,
                TKind::RBra,
                Self::ident,
            )?;
            let token = token.join_trimmed(self.token);
            self.add(AstEnt::new(AKind::Group, sons, token))
        } else {
            Ast::reserved_value()
        };

        let expr = self.type_expr()?;
        let sons = self.add_slice(&[generics, expr]);
        let token = token.join_trimmed(self.token);
        let impl_ast = self.add(AstEnt::new(AKind::Impl(vis), sons, token));

        self.expect_str(TKind::Colon, "expected ':' after 'impl' type")?;
        self.next()?;
        self.walk_block(|s| {
            s.top_item(impl_ast, "expected 'fun' | 'attr' | 'let' | 'var' | '##'")
        })?;

        Ok(())
    }

    fn top_item(&mut self, impl_ast: Ast, message: &'static str) -> Result {
        let kind = self.token_kind();
        let collect_attributes = matches!(
            kind,
            TKind::Union | TKind::Enum | TKind::Struct | TKind::Fun | TKind::Var | TKind::Let
        );

        let attributes = if collect_attributes {
            self.context
                .current_attributes
                .extend_from_slice(&self.context.attrib_stack);
            if !self.context.current_attributes.is_empty() {
                let sons = self.context.create_attribute_slice();
                self.add(AstEnt::new(AKind::Group, sons, Token::default()))
            } else {
                Ast::reserved_value()
            }
        } else {
            Ast::reserved_value()
        };

        match kind {
            TKind::Impl if impl_ast == Ast::reserved_value() => {
                self.context
                    .attrib_frames
                    .push(self.context.attrib_stack.len());
                self.context
                    .attrib_stack
                    .extend_from_slice(&self.context.current_attributes);
                self.impl_block()?;
                self.context
                    .attrib_stack
                    .truncate(self.context.attrib_frames.pop().unwrap());
            }
            TKind::Struct | TKind::Union | TKind::Enum if impl_ast == Ast::reserved_value() => {
                let item = match kind {
                    TKind::Struct => self.structure_declaration(false)?,
                    TKind::Union => self.structure_declaration(true)?,
                    TKind::Enum => self.enum_declaration()?,
                    _ => unreachable!(),
                };
                self.add_type((item, attributes));
            }
            TKind::Fun => {
                let item = self.fun()?;
                self.add_fun((item, attributes, impl_ast));
            }
            TKind::Var | TKind::Let => {
                let item = self.var_statement(true)?;
                self.add_global((item, attributes, impl_ast));
            }
            TKind::Attr => {
                self.attr()?;
            }
            TKind::Comment(_) => {
                let ast = AstEnt::sonless(AKind::Comment, self.token);
                let ast = self.add(ast);
                self.context.current_attributes.push(ast);
                self.next()?;
            }
            TKind::Indent(_) => {
                self.next()?;
            }

            _ => return Err(self.unexpected_str(message)),
        }

        Ok(())
    }

    fn enum_declaration(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let vis = self.vis()?;

        let name = self.ident()?;

        let variants = if self.token == TKind::Colon {
            self.block(Self::ident)?
        } else {
            Ast::reserved_value()
        };

        let sons = self.add_slice(&[name, variants]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::Enum(vis), sons, token)))
    }

    fn structure_declaration(&mut self, union: bool) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let vis = self.vis()?;
        let kind = if union {
            AKind::Union(vis)
        } else {
            AKind::Struct(vis)
        };

        let expr = self.type_expr()?;

        let body = if self.token == TKind::Colon {
            self.block(Self::struct_field)?
        } else {
            Ast::reserved_value()
        };

        let sons = self.add_slice(&[expr, body]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(kind, sons, token)))
    }

    fn struct_field(&mut self) -> Result<Ast> {
        let token = self.token;
        let vis = self.vis()?;
        let embedded = if self.token == TKind::Embed {
            self.next()?;
            true
        } else {
            false
        };

        let mut sons = EntityList::new();

        self.list(
            &mut sons,
            TKind::None,
            TKind::Comma,
            TKind::Colon,
            Self::ident,
        )?;

        let expr = self.type_expr()?;
        self.push(&mut sons, expr);

        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::StructField(vis, embedded), sons, token)))
    }

    fn attr(&mut self) -> Result {
        self.next()?;

        let mut sons = EntityList::new();

        self.list(
            &mut sons,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::attr_element,
        )?;

        self.context.add_attributes(sons, self.main_state);

        Ok(())
    }

    fn attr_element(&mut self) -> Result<Ast> {
        let token = self.token;
        let mut sons = EntityList::new();
        let ident = self.ident()?;
        self.push(&mut sons, ident);

        let kind = match self.token_kind() {
            TKind::LPar => {
                self.list(
                    &mut sons,
                    TKind::LPar,
                    TKind::Comma,
                    TKind::RPar,
                    Self::attr_element,
                )?;
                AKind::AttributeElement
            }
            TKind::Op => {
                if self.display(self.token) == "=" {
                    self.next()?;
                    let expr = self.expr()?;
                    self.push(&mut sons, expr);
                } else {
                    return Err(self.unexpected_str("expected '=' or '('"));
                }
                AKind::AttributeAssign
            }
            _ => AKind::AttributeElement,
        };

        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(kind, sons, token)))
    }

    fn fun(&mut self) -> Result<Ast> {
        let token = self.token;
        let header = self.fun_header(false)?;
        let body = if self.token == TKind::Colon && !self.is_type_expr {
            self.stmt_block()?
        } else {
            Ast::reserved_value()
        };

        let sons = self.add_slice(&[header, body]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::Fun, sons, token)))
    }

    fn fun_header(&mut self, anonymous: bool) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let vis = if anonymous { Vis::None } else { self.vis()? };

        let mut sons = EntityList::new();

        let previous = self.is_type_expr;
        self.is_type_expr = true;
        let is_op = self.token_kind() == TKind::Op;
        let ident = match self.token_kind() {
            TKind::Ident | TKind::Op if !anonymous => self.ident_expr()?,
            _ => Ast::reserved_value(),
        };
        self.push(&mut sons, ident);
        self.is_type_expr = previous;

        if self.token == TKind::LPar {
            let parser = if self.is_type_expr {
                Self::expr
            } else {
                Self::fun_argument
            };
            self.list(&mut sons, TKind::LPar, TKind::Comma, TKind::RPar, parser)?;
        }

        let kind = if is_op {
            let arg_count = self.slice(sons)[1..]
                .iter()
                .fold(0, |acc, &i| acc + self.sons(i).len() - 1);
            match arg_count {
                1 => OpKind::Unary,
                2 => OpKind::Binary,
                _ => return Err(AError::new(
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

        let ret = if self.token == TKind::RArrow {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };
        self.push(&mut sons, ret);

        // call convention
        let call_conv = if self.token == TKind::Ident {
            self.ident()?
        } else {
            Ast::reserved_value()
        };
        self.push(&mut sons, call_conv);

        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::FunHeader(kind, vis), sons, token)))
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let token = self.token;
        let mutable = if token.kind() == TKind::Var {
            self.next()?;
            true
        } else {
            false
        };

        let mut sons = EntityList::new();
        self.list(
            &mut sons,
            TKind::None,
            TKind::Comma,
            TKind::Colon,
            Self::ident,
        )?;

        let expr = self.type_expr()?;
        self.push(&mut sons, expr);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::FunArgument(mutable), sons, token)))
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.token_kind() {
            TKind::Return => self.return_statement(),
            TKind::Var | TKind::Let => self.var_statement(false),
            TKind::Break => return self.break_statement(),
            TKind::Continue => return self.continue_statement(),
            _ => self.expr(),
        }
    }

    fn var_statement(&mut self, top_level: bool) -> Result<Ast> {
        let token = self.token;
        let mutable = token.kind() == TKind::Var;

        self.next()?;

        let vis = if top_level { self.vis()? } else { Vis::None };
        let kind = AKind::VarStatement(vis, mutable);
        let mut sons = EntityList::new();

        self.walk_block(|s| {
            let line = s.var_statement_line()?;
            s.push(&mut sons, line);
            Ok(())
        })?;

        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(kind, sons, token)))
    }

    fn var_statement_line(&mut self) -> Result<Ast> {
        let token = self.token;
        let mut ident_group = EntityList::new();
        self.list(
            &mut ident_group,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::ident,
        )?;
        let token = token.join_trimmed(self.token);

        let datatype = if self.token == TKind::Colon {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };

        let values = if self.display(self.token) == "=" {
            let token = self.token;
            let mut values = EntityList::new();
            self.next()?;
            self.list(
                &mut values,
                TKind::None,
                TKind::Comma,
                TKind::None,
                Self::expr,
            )?;
            let len = self.len(values);
            let ident_len = self.len(ident_group);
            if len == 1 {
                std::iter::repeat(self.get(ident_group, 0))
                    .take(ident_len - 1)
                    .for_each(|n| self.push(&mut values, n));
            } else if len != ident_len {
                return Err(self.unexpected_str(
                    "expected one value per identifier or one value for all identifiers",
                ));
            }
            let token = token.join_trimmed(self.token);
            self.add(AstEnt::new(AKind::Group, values, token))
        } else {
            Ast::reserved_value()
        };

        if datatype == Ast::reserved_value() && values == Ast::reserved_value() {
            return Err(self.unexpected_str("expected '=' or ':' type"));
        }

        let ident_group = self.add(AstEnt::new(AKind::Group, ident_group, token));
        let sons = self.add_slice(&[ident_group, datatype, values]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::VarAssign, sons, token)))
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;
        let ret_val = if let TKind::Indent(_) | TKind::Eof = self.token_kind() {
            Ast::reserved_value()
        } else {
            self.expr()?
        };

        let sons = self.add_slice(&[ret_val]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::Return, sons, token)))
    }

    fn type_expr(&mut self) -> Result<Ast> {
        self.is_type_expr = true;

        let result = self.simple_expr();

        self.is_type_expr = false;

        result
    }

    fn expr(&mut self) -> Result<Ast> {
        let expr = self.simple_expr()?;
        self.expr_low(expr)
    }

    fn expr_low(&mut self, previous: Ast) -> Result<Ast> {
        let mut result = previous;
        while self.token == TKind::Op {
            let token = self.token;
            let op = AstEnt::sonless(AKind::Ident, token);
            let pre = self.precedence(token);

            self.next()?;
            self.ignore_newlines()?;

            let mut next = self.simple_expr()?;

            if self.token == TKind::Op {
                let dif = pre - self.precedence(self.token);

                if dif > 0 {
                    next = self.expr_low(next)?;
                }
            }

            let token = self.token(previous).join(self.token(next));

            // this handles the '{op}=' sugar
            result = if pre == ASSIGN_PRECEDENCE
                && op.len() != 1
                && self.main_state.display(op.span()).chars().last().unwrap() == '='
            {
                let op_token =
                    Token::new(TKind::Op, op.span().slice(0..op.len() - 1), op.line_data());
                let operator = self.add(AstEnt::sonless(AKind::Ident, op_token));

                let eq_token = Token::new(
                    TKind::Op,
                    op.span().slice(op.len() - 1..op.len()),
                    token.line_data(),
                );
                let eq = self.add(AstEnt::sonless(AKind::Ident, eq_token));

                let sons = self.add_slice(&[operator, result, next]);
                let expr = self.add(AstEnt::new(AKind::Binary, sons, token));

                let sons = self.add_slice(&[eq, result, expr]);
                self.add(AstEnt::new(AKind::Binary, sons, token))
            } else {
                let op = self.add(op);
                let sons = self.add_slice(&[op, result, next]);
                self.add(AstEnt::new(AKind::Binary, sons, token))
            };
        }

        Ok(result)
    }

    fn precedence(&self, token: Token) -> i64 {
        precedence(self.main_state.display_token(token))
    }

    fn simple_expr(&mut self) -> Result<Ast> {
        self.simple_expr_low(false)
    }

    fn simple_expr_low(&mut self, nested: bool) -> Result<Ast> {
        let token = self.token;
        let mut ast = match self.token_kind() {
            TKind::Ident => self.ident_expr()?,
            TKind::Int(..)
            | TKind::Uint(..)
            | TKind::Bool(..)
            | TKind::Char
            | TKind::Float(..)
            | TKind::String => {
                self.next()?;
                self.add(AstEnt::sonless(AKind::Lit, token))
            }
            TKind::LPar => {
                self.next()?;
                let expr = self.expr()?;
                let result = if self.token_kind() == TKind::Comma {
                    let mut sons = self.add_slice(&[expr]);
                    self.next()?;
                    self.list(
                        &mut sons,
                        TKind::None,
                        TKind::Comma,
                        TKind::RPar,
                        Self::expr,
                    )?;
                    let token = token.join_trimmed(self.token);
                    self.add(AstEnt::new(AKind::Tuple, sons, token))
                } else {
                    self.expect_str(TKind::RPar, "expected ')'")?;
                    self.next()?;
                    expr
                };
                result
            }
            TKind::If => return self.if_expr(),
            TKind::For => return self.loop_expr(),
            TKind::Op => {
                let mut sons = EntityList::new();
                let kind = match self.main_state.display(token.span()) {
                    "&" => {
                        self.next()?;
                        let mutable = self.token_kind() == TKind::Var;
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
                        let ast = self.add(AstEnt::sonless(AKind::Ident, token));
                        self.push(&mut sons, ast);
                        self.next()?;
                        AKind::Ident
                    }
                };
                let ast = self.simple_expr()?;
                self.push(&mut sons, ast);
                let token = token.join_trimmed(self.token);
                return Ok(self.add(AstEnt::new(kind, sons, token)));
            }
            TKind::Pass => {
                self.next()?;
                return Ok(self.add(AstEnt::sonless(AKind::Pass, token)));
            }
            TKind::LBra => {
                let mut sons = EntityList::new();
                self.list(
                    &mut sons,
                    TKind::LBra,
                    TKind::Comma,
                    TKind::RBra,
                    Self::expr,
                )?;
                let token = token.join_trimmed(self.token);
                return Ok(self.add(AstEnt::new(AKind::Array, sons, token)));
            }
            TKind::Fun => return self.fun_header(true),
            _ => todo!("unmatched simple expr pattern {:?}", self.token),
        };

        if !nested && !self.is_type_expr {
            loop {
                let new_ast = match self.token_kind() {
                    TKind::Dot => {
                        self.next()?;
                        let expr = self.simple_expr_low(true)?;
                        let sons = self.add_slice(&[ast, expr]);
                        let token = token.join_trimmed(self.token);
                        AstEnt::new(AKind::Dot, sons, token)
                    }
                    TKind::LPar => {
                        let (kind, sons, _) = self.ent(ast).parts();
                        let (kind, mut sons) = if kind == AKind::Dot {
                            let slice = &[self.get(sons, 1), self.get(sons, 0)];
                            let new_sons = self.add_slice(slice);
                            self.clear_slice(sons);
                            (AKind::Call(true), new_sons)
                        } else {
                            (AKind::Call(false), self.add_slice(&[ast]))
                        };

                        self.list(
                            &mut sons,
                            TKind::LPar,
                            TKind::Comma,
                            TKind::RPar,
                            Self::expr,
                        )?;

                        let token = token.join_trimmed(self.token);
                        AstEnt::new(kind, sons, token)
                    }
                    TKind::LBra => {
                        self.next()?;
                        self.ignore_newlines()?;
                        let expr = self.expr()?;
                        self.ignore_newlines()?;
                        self.expect_str(TKind::RBra, "expected ']'")?;
                        self.next()?;

                        let sons = self.add_slice(&[ast, expr]);
                        let token = token.join_trimmed(self.token);
                        AstEnt::new(AKind::Index, sons, token)
                    }

                    _ => break,
                };

                ast = self.add(new_ast);
            }
        }

        Ok(ast)
    }

    fn continue_statement(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let label = self.optional_tag()?;
        let sons = self.add_slice(&[label]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::Continue, sons, token)))
    }

    fn break_statement(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let label = self.optional_tag()?;

        let ret = if let TKind::Indent(_) | TKind::Eof = self.token_kind() {
            Ast::reserved_value()
        } else {
            self.expr()?
        };

        let sons = self.add_slice(&[label, ret]);
        let token = token.join_trimmed(self.token);
        Ok(self.add(AstEnt::new(AKind::Break, sons, token)))
    }

    fn loop_expr(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;

        let label = self.optional_tag()?;
        let body = self.stmt_block()?;

        let sons = self.add_slice(&[label, body]);
        let token = token.join_trimmed(self.token);

        Ok(self.add(AstEnt::new(AKind::Loop, sons, token)))
    }

    fn optional_tag(&mut self) -> Result<Ast> {
        Ok(if self.token == TKind::Tag {
            let token = self.token;
            self.next()?;
            self.add(AstEnt::sonless(AKind::Ident, token))
        } else {
            Ast::reserved_value()
        })
    }

    fn ident_expr(&mut self) -> Result<Ast> {
        let token = self.token;
        let mut ast = self.ident()?;

        self.peek()?;
        if self.token == TKind::DoubleColon && self.peeked == TKind::Ident {
            self.next()?;
            let ident = self.ident()?;
            self.peek()?;
            let sons = if self.token == TKind::DoubleColon && self.peeked == TKind::Ident {
                self.next()?;
                let last_ident = self.ident()?;
                self.add_slice(&[ast, ident, last_ident])
            } else {
                self.add_slice(&[ast, ident])
            };
            let token = token.join_trimmed(self.token);
            ast = self.add(AstEnt::new(AKind::Path, sons, token));
        }

        let is_instantiation =
            self.is_type_expr && self.token == TKind::LBra || self.token == TKind::DoubleColon;

        if is_instantiation {
            if self.token == TKind::DoubleColon {
                self.next()?;
            }
            self.expect_str(
                TKind::LBra,
                "expected '[' as a start of generic instantiation",
            )?;
            let mut sons = self.add_slice(&[ast]);
            self.list(
                &mut sons,
                TKind::LBra,
                TKind::Comma,
                TKind::RBra,
                Self::expr,
            )?;

            let token = token.join_trimmed(self.token);
            ast = self.add(AstEnt::new(AKind::Instantiation, sons, token));
        }

        Ok(ast)
    }

    fn ident(&mut self) -> Result<Ast> {
        self.expect_str(TKind::Ident, "expected ident")?;
        let token = self.token;
        self.next()?;
        Ok(self.add(AstEnt::sonless(AKind::Ident, token)))
    }

    fn if_expr(&mut self) -> Result<Ast> {
        let token = self.token;
        self.next()?;
        let condition = self.expr()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.token_kind() {
            TKind::Else => {
                self.next()?;
                self.stmt_block()?
            }
            TKind::Elif => {
                let token = self.token;
                let branch = self.if_expr()?;
                let sons = self.add_slice(&[branch]);
                let token = token.join_trimmed(self.token);
                self.add(AstEnt::new(AKind::Elif, sons, token))
            }
            TKind::Indent(_) => {
                self.peek()?;
                match self.peeked_kind() {
                    TKind::Else => {
                        self.next()?;
                        self.next()?;
                        self.stmt_block()?
                    }
                    TKind::Elif => {
                        self.next()?;
                        let token = self.token;
                        let branch = self.if_expr()?;
                        let sons = self.add_slice(&[branch]);
                        let token = token.join_trimmed(self.token);
                        self.add(AstEnt::new(AKind::Elif, sons, token))
                    }
                    _ => Ast::reserved_value(),
                }
            }
            _ => Ast::reserved_value(),
        };

        let sons = self.add_slice(&[condition, then_block, else_block]);

        Ok(self.add(AstEnt::new(AKind::If, sons, token)))
    }

    fn vis(&mut self) -> Result<Vis> {
        Ok(match self.token_kind() {
            TKind::Pub => {
                self.next()?;
                Vis::Public
            }
            TKind::Priv => {
                self.next()?;
                Vis::Private
            }
            _ => Vis::None,
        })
    }

    fn walk_block<F: FnMut(&mut Self) -> Result>(&mut self, mut parser: F) -> Result {
        if let TKind::Indent(level) = self.token_kind() {
            if level > self.level + 1 {
                return Err(self.unexpected_str(
                    "too deep indentation, one indentation level is equal 2 spaces or one tab",
                ));
            }
            self.level += 1;
            while self.level_continues()? {
                parser(self)?;
            }
        } else {
            parser(self)?;
        }
        Ok(())
    }

    fn block<F: FnMut(&mut Self) -> Result<Ast>>(&mut self, mut parser: F) -> Result<Ast> {
        self.expect_str(TKind::Colon, "expected ':' as a start of block")?;
        let token = self.token;
        let mut sons = EntityList::new();
        self.next()?;
        self.walk_block(|s| {
            let expr = parser(s)?;
            s.push(&mut sons, expr);
            Ok(())
        })?;
        let token = token.join_trimmed(self.token);
        Ok(self.add(AstEnt::new(AKind::Group, sons, token)))
    }

    fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.token_kind(), TKind::Indent(_) | TKind::Eof) {
            return Err(self.unexpected_str("expected indentation"));
        }

        loop {
            self.peek()?;
            match self.peeked_kind() {
                TKind::Indent(_) => {
                    self.next()?;
                }
                TKind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.token_kind() {
            TKind::Indent(level) => {
                if level == self.level {
                    self.next()?;
                    Ok(true)
                } else if level < self.level {
                    self.level -= 1;
                    Ok(false)
                } else {
                    return Err(self.unexpected_str("unexpected indentation dive"));
                }
            }
            _ => unreachable!(),
        }
    }

    fn list<F: FnMut(&mut Self) -> Result<Ast>>(
        &mut self,
        sons: &mut EntityList<Ast>,
        start: TKind,
        separator: TKind,
        end: TKind,
        mut parser: F,
    ) -> Result {
        if start != TKind::None {
            self.expect(start.clone(), format!("expected {}", start))?;
            self.next()?;
            self.ignore_newlines()?;
        }

        if end != TKind::None && self.token == end {
            self.next()?;
            return Ok(());
        }

        let expr = parser(self)?;
        self.push(sons, expr);

        while self.token == separator {
            self.next()?;
            self.ignore_newlines()?;
            // trailing colon allowed
            if end != TKind::None && self.token == end {
                break;
            }
            let expr = parser(self)?;
            self.push(sons, expr);
        }

        if end != TKind::None {
            self.ignore_newlines()?;
            self.expect(end.clone(), format!("expected {}", end))?;
            self.next()?;
        }

        Ok(())
    }

    fn ignore_newlines(&mut self) -> Result {
        while let TKind::Indent(_) = self.token_kind() {
            self.next()?;
        }

        Ok(())
    }

    fn peek(&mut self) -> Result {
        let mut state = self.l_state.clone();
        let token = self
            .main_state
            .token(&mut state)
            .map_err(|err| AError::new(AEKind::LError(err), Token::default()))?;
        self.peeked = token;
        Ok(())
    }

    fn next(&mut self) -> Result {
        let token = self
            .main_state
            .token(&mut self.context.l_state)
            .map_err(|err| AError::new(AEKind::LError(err), Token::default()))?;
        self.token = token;
        Ok(())
    }

    fn expect_str(&self, kind: TKind, message: &str) -> Result {
        self.expect(kind, message.to_string())
    }

    fn expect(&self, kind: TKind, message: String) -> Result {
        if self.token_kind() == kind {
            Ok(())
        } else {
            Err(self.unexpected(message))
        }
    }

    fn token_kind(&self) -> TKind {
        self.token.kind()
    }

    fn peeked_kind(&self) -> TKind {
        self.peeked.kind()
    }

    fn unexpected_str(&self, message: &'static str) -> AError {
        self.unexpected(message.to_string())
    }

    fn unexpected(&self, message: String) -> AError {
        AError::new(AEKind::UnexpectedToken(message), self.token)
    }

    fn display(&self, token: Token) -> &str {
        self.main_state.display(token.span())
    }
}

#[derive(Debug, Clone, QuickSer)]
pub struct AState {
    pub l_main_state: LMainState,
}

crate::inherit!(AState, l_main_state, LMainState);

impl Default for AState {
    fn default() -> Self {
        Self {
            l_main_state: LMainState::default(),
        }
    }
}

impl AState {
    pub fn prepare_context(&mut self, source: Source, target: &mut AContext) {
        let mut l_state = LState::new(source);
        let token = self.token(&mut l_state).unwrap();

        target.clear(l_state, token);
    }

    pub fn attr_of(&self, manifest: &Manifest, name: &str) -> Option<Span> {
        manifest
            .attrs
            .iter()
            .find(|(a_name, _)| self.display(*a_name) == name)
            .map(|(_, value)| value.clone())
    }
}

#[cfg(debug_assertions)]
static COUNTER: AtomicU64 = AtomicU64::new(0);

#[cfg(debug_assertions)]
#[derive(Debug, Default, Clone, Copy, RealQuickSer)]
struct RelocSafety {
    id: u64,
}

#[cfg(debug_assertions)]
impl RelocSafety {
    fn new() -> Self {
        Self {
            id: 1 + COUNTER.fetch_add(1, Ordering::Relaxed),
        }
    }

    fn check(&mut self, other: &mut Self) -> bool {
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
        self.safety = RelocSafety::default();
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
    pub fn chain_son_ent(&self, ast: Ast, indexes: &[usize]) -> AstEnt {
        self.ent(self.chain_son(ast, indexes))
    }

    pub fn chain_son(&self, mut ast: Ast, indexes: &[usize]) -> Ast {
        let mut current = 0;
        while current < indexes.len() {
            let index = indexes[current];
            ast = self.son(ast, index);
            current += 1;
        }
        ast
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
        self.son_ent(ast, index).sons.len(&self.connections)
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
        self.ent(ast).sons.as_slice(&self.connections)
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
        debug_assert!(ctx.safety.check(&mut self.safety));
        debug_assert!(ctx.frontier.is_empty());

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

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct AContext {
    l_state: LState,
    peeked: Token,
    token: Token,
    is_type_expr: bool,
    level: u16,

    data: AstData,

    funs: Vec<(Ast, Ast, Ast)>,
    types: Vec<(Ast, Ast)>,
    globals: Vec<(Ast, Ast, Ast)>,

    attrib_stack: Vec<Ast>,
    attrib_frames: Vec<usize>,
    current_attributes: Vec<Ast>,
}

crate::inherit!(AContext, data, AstData);

impl AContext {
    pub fn clear(&mut self, l_state: LState, token: Token) {
        self.l_state = l_state;
        self.token = token;
        self.peeked = token;
        self.level = 0;

        self.data.clear();

        self.funs.clear();
        self.types.clear();
        self.globals.clear();

        self.attrib_stack.clear();
        self.attrib_frames.clear();
        self.current_attributes.clear();
    }

    pub fn add(&mut self, ast_ent: AstEnt) -> Ast {
        self.data.entities.push(ast_ent)
    }

    pub fn push(&mut self, target: &mut EntityList<Ast>, value: Ast) {
        target.push(value, &mut self.data.connections);
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

    pub fn add_slice(&mut self, slice: &[Ast]) -> EntityList<Ast> {
        EntityList::from_slice(slice, &mut self.data.connections)
    }

    fn clear_slice(&mut self, mut slice: EntityList<Ast>) {
        slice.clear(&mut self.data.connections);
    }

    fn create_attribute_slice(&mut self) -> EntityList<Ast> {
        let value = EntityList::from_slice(
            self.current_attributes.as_slice(),
            &mut self.data.connections,
        );
        self.current_attributes.clear();
        value
    }

    fn add_attributes(&mut self, sons: EntityList<Ast>, main_state: &AState) {
        for &ast in sons.as_slice(&self.data.connections) {
            let name = main_state.display(self.son_ent(ast, 0).token().span());
            if name == "push" {
                self.attrib_frames.push(self.attrib_stack.len());
                for &ast in &self.data.sons(ast)[1..] {
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
}

#[derive(Clone, Debug, Default)]
pub struct Import {
    pub nickname: Option<Span>,
    pub path: Span,
    pub token: Token,
}

#[derive(Clone, Debug, Default)]
pub struct Manifest {
    pub attrs: Vec<(Span, Span)>,
    pub deps: Vec<Dep>,
}

impl Manifest {
    pub fn clear(&mut self) {
        self.attrs.clear();
        self.deps.clear();
    }
}

#[derive(Clone, Debug, Copy, Default, RealQuickSer)]
pub struct Dep {
    pub path: Span,
    pub name: Span,
    pub version: Span,
    pub external: bool,
    pub token: Token,
}

pub const ASSIGN_PRECEDENCE: i64 = 15;

pub fn precedence(op: &str) -> i64 {
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

#[derive(Debug, Clone, Copy, Default, PartialEq, RealQuickSer)]
pub struct AstEnt {
    kind: AKind,
    sons: EntityList<Ast>,
    token: Token,
}

impl AstEnt {
    fn new(kind: AKind, sons: EntityList<Ast>, token: Token) -> Self {
        Self { kind, sons, token }
    }

    fn sonless(kind: AKind, token: Token) -> AstEnt {
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
    main_state: &'a AState,
    state: &'a AstData,
    ast: Ast,
}

impl<'a> AstDisplay<'a> {
    pub fn new(main_state: &'a AState, state: &'a AstData, ast: Ast) -> Self {
        Self {
            main_state,
            state,
            ast,
        }
    }

    fn log(&self, ast: Ast, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    FunHeader(OpKind, Vis),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, RealQuickSer)]
pub enum Vis {
    Public,
    None,
    Private,
}

impl Vis {
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (_, Vis::Public) | (Vis::Public, Vis::None) => Vis::Public,
            (_, Vis::Private) | (Vis::Private, Vis::None) => Vis::Private,
            _ => Vis::None,
        }
    }
}

impl Default for Vis {
    fn default() -> Self {
        Vis::Public
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpKind {
    Normal,
    Unary,
    Binary,
}

crate::def_displayer!(
    AErrorDisplay,
    AState,
    AError,
    |self, f| {
        AEKind::LError(error) => {
            writeln!(f, "{}", LErrorDisplay::new(self.state, error))?;
        },
        AEKind::UnexpectedToken(message) => {
            writeln!(f, "{}", message)?;
        },
    }
);

#[derive(Debug)]
pub struct AError {
    pub kind: AEKind,
    pub token: Token,
}

impl AError {
    pub fn new(kind: AEKind, token: Token) -> AError {
        AError { kind, token }
    }
}

#[derive(Debug)]
pub enum AEKind {
    LError(LError),
    UnexpectedToken(String),
}

impl Into<AError> for AEKind {
    fn into(self) -> AError {
        AError {
            kind: self,
            token: Token::default(),
        }
    }
}

pub fn test() {
    
    let mut a_main_state = AState::default();
    let source = SourceEnt::new(
        "text_code.mf".to_string(),
        crate::testing::TEST_CODE.to_string(),
        SystemTime::UNIX_EPOCH,
    );

    let source = a_main_state.add_source(source);
    let mut context = AContext::default();

    a_main_state.prepare_context(source, &mut context);
    let mut a_parser = AParser::new(&mut a_main_state, &mut context);
    a_parser.parse().unwrap();

    for &(global, attrs, header) in context.globals() {
        println!("===global===");
        print!("{}", AstDisplay::new(&a_main_state, &context, header));
        print!("{}", AstDisplay::new(&a_main_state, &context, attrs));
        print!("{}", AstDisplay::new(&a_main_state, &context, global));
    }

    for &(ty, attrs) in context.types() {
        println!("===type===");
        print!("{}", AstDisplay::new(&a_main_state, &context, attrs));
        print!("{}", AstDisplay::new(&a_main_state, &context, ty));
    }

    for &(fun, attrs, header) in context.funs() {
        println!("===fun===");
        print!("{}", AstDisplay::new(&a_main_state, &context, header));
        print!("{}", AstDisplay::new(&a_main_state, &context, attrs));
        print!("{}", AstDisplay::new(&a_main_state, &context, fun));
    }    
}
