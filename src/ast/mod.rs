use cranelift::{
    codegen::packed_option::ReservedValue,
    entity::{EntityList, ListPool, PrimaryMap},
};
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use crate::{
    entities::{Ast, Source},
    lexer::*,
};

use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
};

pub type Result<T = ()> = std::result::Result<T, AError>;

pub struct AParser<'a> {
    main_state: &'a mut AMainState,
    state: &'a mut AState,
    context: &'a mut AContext,
}

impl<'a> AParser<'a> {
    pub fn new(
        main_state: &'a mut AMainState,
        state: &'a mut AState,
        context: &'a mut AContext,
    ) -> Self {
        context.clear();
        Self {
            main_state,
            state,
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


                    manifest.attrs.push((name, self.token.span().slice(1..self.token.len() - 2)));

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
                let sons = self.state.add_slice(&self.context.current_attributes);
                self.context.current_attributes.clear();
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
                self.state
                    .types
                    .extend([item, attributes], &mut self.state.cons);
            }
            TKind::Fun => {
                let item = self.fun()?;
                self.state
                    .funs
                    .extend([item, attributes, impl_ast], &mut self.state.cons);
            }
            TKind::Var | TKind::Let => {
                let item = self.var_statement(true)?;
                self.state
                    .globals
                    .extend([item, attributes, impl_ast], &mut self.state.cons);
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

        for &ast in self.state.slice(sons) {
            let name = self.display(self.son_ent(ast, 0).token());
            if name == "push" {
                self.context
                    .attrib_frames
                    .push(self.context.attrib_stack.len());
                for &ast in &self.state.slice(self.sons(ast))[1..] {
                    self.context.attrib_stack.push(ast);
                }
            } else if name == "pop" {
                let len = self.context.attrib_frames.pop().unwrap();
                self.context.attrib_stack.truncate(len);
            } else {
                self.context.current_attributes.push(ast);
            }
        }

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
            },
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
                .fold(0, |acc, &i| acc + self.ast_len(i) - 1);
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
        self.list(&mut sons, TKind::None, TKind::Comma, TKind::Colon, Self::ident)?;

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
                return Err(
                    self.unexpected_str("expected one value per identifier or one value for all identifiers")
                );
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
                && self
                    .main_state
                    .display(op.span())
                    .chars()
                    .last()
                    .unwrap()
                    == '='
            {
                let op_token = Token::new(
                    TKind::Op,
                    op.span().slice(0..op.len() - 1),
                    op.line_data(),
                );
                let operator = self.add(AstEnt::sonless(AKind::Ident, op_token));
                
                let eq_token = Token::new(TKind::Op, op.span().slice(op.len() - 1..op.len()), token.line_data());
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
            },
            TKind::LPar => {
                self.next()?;
                let expr = self.expr()?;
                let result = if self.token_kind() == TKind::Comma {
                    let mut sons = self.add_slice(&[expr]);
                    self.next()?;
                    self.list(&mut sons, TKind::None, TKind::Comma, TKind::RPar, Self::expr)?;
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
                        let (kind, mut sons, _) = self.ent(ast).parts();
                        let (kind, mut sons) = if kind == AKind::Dot {
                            let slice = &[self.get(sons, 1), self.get(sons, 0)];
                            let new_sons = self.add_slice(slice);
                            sons.clear(&mut self.cons);
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
                        self.add(AstEnt::new(
                            AKind::Elif, 
                            sons, 
                            token,
                        ))
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
            s.state.push(&mut sons, expr);
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
            .lexer_for(&mut state)
            .next()
            .map_err(|err| AError::new(AEKind::LError(err), Token::default()))?;
        self.peeked = token;
        Ok(())
    }

    fn next(&mut self) -> Result {
        let token = self
            .main_state
            .lexer_for(&mut self.state.l_state)
            .next()
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

impl<'a> Deref for AParser<'a> {
    type Target = AState;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl<'a> DerefMut for AParser<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.state
    }
}

#[derive(Debug, Clone, QuickSer)]
pub struct AMainState {
    pub l_main_state: LMainState,
}

crate::inherit!(AMainState, l_main_state, LMainState);

impl Default for AMainState {
    fn default() -> Self {
        Self {
            l_main_state: LMainState::default(),
        }
    }
}

impl AMainState {
    pub fn a_state_for(&mut self, source: Source, target: &mut AState) {
        let mut l_state = LState::new(source);
        let mut lexer = self.lexer_for(&mut l_state);
        let token = lexer.next().unwrap();

        target.l_state = l_state;
        target.token = token;
        target.peeked = token;
        target.level = 0;
        target.asts.clear();
        target.cons.clear();

        target.funs = EntityList::new();
        target.types = EntityList::new();
        target.globals = EntityList::new();
    }

    pub fn attr_of(&self, manifest: &Manifest, name: &str) -> Option<Span> {
        manifest
            .attrs
            .iter()
            .find(|(a_name, _)| self.display(*a_name) == name)
            .map(|(_, value)| value.clone())
    }
}

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct AState {
    pub l_state: LState,
    peeked: Token,
    pub token: Token,
    is_type_expr: bool,
    level: u16,
    asts: PrimaryMap<Ast, AstEnt>,
    cons: ListPool<Ast>,

    funs: EntityList<Ast>,
    types: EntityList<Ast>,
    globals: EntityList<Ast>,
}

crate::inherit!(AState, l_state, LState);

impl AState {
    pub fn add(&mut self, ast_ent: AstEnt) -> Ast {
        self.asts.push(ast_ent)
    }

    pub fn kind(&self, ast: Ast) -> AKind {
        self.asts[ast].kind
    }
    
    pub fn sons(&self, ast: Ast) -> EntityList<Ast> {
        self.asts[ast].sons
    }

    pub fn token(&self, ast: Ast) -> Token {
        self.asts[ast].token
    }

    pub fn son(&self, ast: Ast, index: usize) -> Ast {
        self.son_optional(ast, index).unwrap()
    }

    pub fn son_ent(&self, ast: Ast, index: usize) -> &AstEnt {
        &self.asts[self.son(ast, index)]
    }

    pub fn son_optional(&self, ast: Ast, index: usize) -> Option<Ast> {
        self.sons(ast).get(index, &self.cons)
    }

    pub fn push(&mut self, target: &mut EntityList<Ast>, value: Ast) {
        target.push(value, &mut self.cons);
    }

    pub fn slice(&self, sons: EntityList<Ast>) -> &[Ast] {
        sons.as_slice(&self.cons)
    }

    pub fn len(&self, list: EntityList<Ast>) -> usize {
        list.len(&self.cons)
    }

    pub fn ast_len(&self, ast: Ast) -> usize {
        self.sons(ast).len(&self.cons)
    }

    pub fn is_empty(&self, ast: Ast) -> bool {
        self.asts[ast].sons.is_empty()
    }

    pub fn son_len(&self, ast: Ast, index: usize) -> usize {
        self.son_ent(ast, index).sons.len(&self.cons)
    }

    pub fn get(&self, sons: EntityList<Ast>, index: usize) -> Ast {
        sons.get(index, &self.cons).unwrap()
    }

    pub fn ent(&self, ast: Ast) -> AstEnt {
        self.asts[ast]
    }

    pub fn funs(&self) -> &[Ast] {
        self.funs.as_slice(&self.cons)
    }

    pub fn types(&self) -> &[Ast] {
        self.types.as_slice(&self.cons)
    }

    pub fn globals(&self) -> &[Ast] {
        self.globals.as_slice(&self.cons)
    }

    pub fn get_ent(&self, sons: EntityList<Ast>, index: usize) -> &AstEnt {
        &self.asts[self.get(sons, index)]
    }

    pub fn chain_son_ent(&self, ast: Ast, indexes: &[usize]) -> &AstEnt {
        &self.asts[self.chain_son(ast, indexes)]
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

    pub fn add_slice(&mut self, slice: &[Ast]) -> EntityList<Ast> {
        EntityList::from_slice(slice, &mut self.cons)
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
        Self {
            kind,
            sons,
            token,
        }
    }
    
    fn sonless(kind: AKind, token: Token, ) -> AstEnt {
        Self { kind, sons: EntityList::new(), token }
    }

    fn parts(&self) -> (AKind, EntityList<Ast>, Token) {
        (self.kind, self.sons, self.token)
    }

    fn kind(&self) -> AKind {
        self.kind
    }

    fn sons(&self) -> EntityList<Ast> {
        self.sons
    }

    fn span(&self) -> Span {
        self.token.span()
    }

    fn token(&self) -> Token {
        self.token
    }

    fn len(&self) -> usize {
        self.span().len()
    }

    fn line_data(&self) -> LineData {
        self.token.line_data()
    }
}

#[derive(Debug, Clone, Default)]
pub struct AContext {
    attrib_stack: Vec<Ast>,
    attrib_frames: Vec<usize>,
    current_attributes: Vec<Ast>,
}

impl AContext {
    fn clear(&mut self) {
        self.attrib_stack.clear();
        self.attrib_frames.clear();
        self.current_attributes.clear();
    }
}

pub struct AstDisplay<'a> {
    main_state: &'a AMainState,
    state: &'a AState,
    ast: Ast,
}

impl<'a> AstDisplay<'a> {
    pub fn new(main_state: &'a AMainState, state: &'a AState, ast: Ast) -> Self {
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
        if sons.len(&self.state.cons) > 0 {
            write!(f, ":\n")?;
            for &child in sons.as_slice(&self.state.cons) {
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
    AMainState,
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
    let mut a_main_state = AMainState::default();
    let source = SourceEnt::new(
        "text_code.mf".to_string(),
        crate::testing::TEST_CODE.to_string(),
    );

    let source = a_main_state.add_source(source);
    let mut context = AContext::default();
    let mut a_state = AState::default();

    a_main_state.a_state_for(source, &mut a_state);
    let mut a_parser = AParser::new(&mut a_main_state, &mut a_state, &mut context);
    a_parser.parse().unwrap();

    for i in (0..a_state.globals.len(&a_state.cons)).step_by(3) {
        if let [fun, attrs, header] = a_state.globals.as_slice(&a_state.cons)[i..i + 3] {
            println!("===global===");
            print!("{}", AstDisplay::new(&a_main_state, &a_state, header));
            print!("{}", AstDisplay::new(&a_main_state, &a_state, attrs));
            print!("{}", AstDisplay::new(&a_main_state, &a_state, fun));
        }
    }

    for i in (0..a_state.types.len(&a_state.cons)).step_by(2) {
        if let [fun, attrs] = a_state.types.as_slice(&a_state.cons)[i..i + 2] {
            println!("===type===");
            print!("{}", AstDisplay::new(&a_main_state, &a_state, attrs));
            print!("{}", AstDisplay::new(&a_main_state, &a_state, fun));
        }
    }

    for i in (0..a_state.funs.len(&a_state.cons)).step_by(3) {
        if let [fun, attrs, header] = a_state.funs.as_slice(&a_state.cons)[i..i + 3] {
            println!("===fun===");
            print!("{}", AstDisplay::new(&a_main_state, &a_state, header));
            print!("{}", AstDisplay::new(&a_main_state, &a_state, attrs));
            print!("{}", AstDisplay::new(&a_main_state, &a_state, fun));
        }
    }
}
