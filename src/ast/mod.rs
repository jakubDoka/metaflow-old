use cranelift::{
    codegen::packed_option::ReservedValue,
    entity::{EntityList, ListPool, PrimaryMap},
};
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use crate::{
    entities::{Ast, Source},
    lexer::*,
    util::sdbm::ID,
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
            match self.token.kind {
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
            let name = self.token.span;
            self.next()?;
            match self.token.kind {
                TKind::Op if self.token.span.hash == ID::new("=") => {
                    self.next()?;

                    if !matches!(self.token.kind, TKind::String(_)) {
                        return Err(self.unexpected_str("expected string literal"));
                    }

                    let mut value = self.token.span;
                    value.start += 1;
                    value.end -= 1;

                    manifest.attrs.push((name, value));

                    self.next()?;
                }
                TKind::Colon => match self.main_state.display(&name) {
                    "dependencies" => {
                        self.next()?;
                        self.walk_block(|s| {
                            let mut token = s.state.token;

                            s.expect_str(TKind::Ident, "expected dependency name")?;
                            let name = s.state.token.span;
                            s.next()?;

                            if !matches!(s.state.token.kind, TKind::String(_)) {
                                return Err(s.unexpected_str("expected string literal as repository link with version or local path"));
                            }
                            let mut path_and_version = s.state.token.span;
                            path_and_version.start += 1;
                            path_and_version.end -= 1;
                            s.next()?;

                            let (path_end, version_start) = s
                                .main_state
                                .display(&path_and_version)
                                .find('@')
                                .map(|i| (i, i + 1))
                                .unwrap_or((path_and_version.len(), path_and_version.len()));

                            let path = s.main_state.slice_span(&path_and_version, 0, path_end);

                            let version = s.main_state.slice_span(&path_and_version, version_start, path_and_version.len());

                            s.join_token(&mut token);

                            let external = s.main_state.display(&path).starts_with("github.com");

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
                            self.main_state.display(&name)
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
        while let TKind::Indent(_) = self.token.kind {
            self.next()?;
        }

        if self.token == TKind::Use {
            self.next()?;
            self.walk_block(|s| s.import_line(imports))?;
        }

        Ok(())
    }

    fn import_line(&mut self, imports: &mut Vec<Import>) -> Result {
        let mut token = self.token;

        let nickname = if self.token == TKind::Ident {
            let nickname = self.token.span;
            self.next()?;
            Some(nickname)
        } else {
            None
        };

        let path = if let TKind::String(_) = self.token.kind {
            let mut path = self.token.span;
            path.start += 1;
            path.end -= 1;
            path
        } else {
            return Err(self.unexpected_str("expected string literal as import path"));
        };

        self.next()?;
        self.join_token(&mut token);

        imports.push(Import {
            nickname,
            path,
            token,
        });

        Ok(())
    }

    pub fn parse(&mut self) -> Result {
        while self.token.kind != TKind::Eof {
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
        let mut ast_ent = self.ast_ent(AKind::Pass);

        self.next()?;

        let vis = self.vis()?;

        ast_ent.kind = AKind::Impl(vis);

        let generics = if self.token == TKind::LBra {
            let mut ast_ent = self.ast_ent(AKind::Group);
            self.list(
                &mut ast_ent,
                TKind::LBra,
                TKind::Comma,
                TKind::RBra,
                Self::ident,
            )?;
            self.add(ast_ent)
        } else {
            Ast::reserved_value()
        };

        self.push(&mut ast_ent.sons, generics);

        let expr = self.type_expr()?;
        self.push(&mut ast_ent.sons, expr);

        let impl_ast = self.add(ast_ent);

        self.expect_str(TKind::Colon, "expected ':' after 'impl' type")?;
        self.next()?;
        self.walk_block(|s| {
            s.top_item(
                impl_ast,
                "expected 'fun' | 'attr' | 'let' | 'var' | '##'",
            )
        })?;

        Ok(())
    }

    fn top_item(&mut self, impl_ast: Ast, message: &'static str) -> Result {
        let kind = self.token.kind;
        let collect_attributes =
            matches!(kind, 
                TKind::Union |
                TKind::Enum |
                TKind::Struct | 
                TKind::Fun |
                TKind::Var |
                TKind::Let
            );

        let attributes = if collect_attributes {
            self.context
                .current_attributes
                .extend_from_slice(&self.context.attrib_stack);
            if !self.context.current_attributes.is_empty() {
                let sons =
                    EntityList::from_slice(&self.context.current_attributes, &mut self.state.cons);
                self.context.current_attributes.clear();
                self.add(AstEnt::with_children(AKind::Group, Token::default(), sons))
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
                let ast = self.ast(AKind::Comment);
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
        let mut ast = self.ast_ent(AKind::Pass);
        self.next()?;

        let vis = self.vis()?;
        ast.kind = AKind::Enum(vis);

        let name = self.ident()?;
        self.push(&mut ast.sons, name);
        
        let variants = if self.token == TKind::Colon {
            self.block(Self::ident)?
        } else {
            Ast::reserved_value()
        };

        self.push(&mut ast.sons, variants);

        Ok(self.add(ast))
    }

    fn structure_declaration(&mut self, union: bool) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Pass);
        self.next()?;

        let vis = self.vis()?;
        ast_ent.kind = if union {
            AKind::Union(vis)
        } else { 
            AKind::Struct(vis)
        };

        let expr = self.type_expr()?;
        self.push(&mut ast_ent.sons, expr);

        let body = if self.token == TKind::Colon {
            self.block(Self::struct_field)?
        } else {
            Ast::reserved_value()
        };

        self.push(&mut ast_ent.sons, body);

        Ok(self.add(ast_ent))
    }

    fn struct_field(&mut self) -> Result<Ast> {
        let vis = self.vis()?;

        let embedded = if self.token == TKind::Embed {
            self.next()?;
            true
        } else {
            false
        };

        let mut ast_ent = self.ast_ent(AKind::StructField(vis, embedded));

        self.list(
            &mut ast_ent,
            TKind::None,
            TKind::Comma,
            TKind::Colon,
            Self::ident,
        )?;

        let expr = self.type_expr()?;
        self.push(&mut ast_ent.sons, expr);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn attr(&mut self) -> Result {
        let mut ast_ent = self.ast_ent(AKind::Attribute);
        self.next()?;

        self.list(
            &mut ast_ent,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::attr_element,
        )?;

        for &ast in self.state.slice(ast_ent.sons) {
            let hash = self.token(ast).span.hash;
            if hash == ID::new("push") {
                self.context
                    .attrib_frames
                    .push(self.context.attrib_stack.len());
                for &ast in &self.state.slice(self.sons(ast))[1..] {
                    self.context.attrib_stack.push(ast);
                }
            } else if hash == ID::new("pop") {
                let len = self.context.attrib_frames.pop().unwrap();
                self.context.attrib_stack.truncate(len);
            } else {
                self.context.current_attributes.push(ast);
            }
        }

        Ok(())
    }

    fn attr_element(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::AttributeElement);
        let ident = self.ident()?;
        self.push(&mut ast_ent.sons, ident);

        match self.token.kind {
            TKind::LPar => self.list(
                &mut ast_ent,
                TKind::LPar,
                TKind::Comma,
                TKind::RPar,
                Self::attr_element,
            )?,
            TKind::Op => {
                if self.token.span.hash == ID::new("=") {
                    ast_ent.kind = AKind::AttributeAssign;
                    self.next()?;
                    let expr = self.expr()?;
                    self.push(&mut ast_ent.sons, expr);
                } else {
                    return Err(self.unexpected_str("expected '=' or '('"));
                }
            }
            _ => (),
        }

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn fun(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Pass);
        let (header, visibility) = self.fun_header(false)?;
        self.push(&mut ast_ent.sons, header);
        ast_ent.kind = AKind::Fun(visibility);

        let body = if self.token == TKind::Colon && !self.is_type_expr {
            self.stmt_block()?
        } else {
            Ast::reserved_value()
        };

        self.push(&mut ast_ent.sons, body);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn fun_header(&mut self, anonymous: bool) -> Result<(Ast, Vis)> {
        let mut ast_ent = self.ast_ent(AKind::Pass);
        self.next()?;

        let visibility = if anonymous { Vis::None } else { self.vis()? };

        let previous = self.is_type_expr;
        self.is_type_expr = true;
        let is_op = self.token.kind == TKind::Op;
        let ident = match self.token.kind {
            TKind::Ident | TKind::Op if !anonymous => self.ident_expr()?,
            _ => Ast::reserved_value(),
        };
        self.push(&mut ast_ent.sons, ident);
        self.is_type_expr = previous;

        if self.token == TKind::LPar {
            let parser = if self.is_type_expr {
                Self::expr
            } else {
                Self::fun_argument
            };
            self.list(&mut ast_ent, TKind::LPar, TKind::Comma, TKind::RPar, parser)?;
        }

        let kind = if is_op {
            let arg_count = self.slice(ast_ent.sons)[1..]
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
                    ast_ent.token,
                )),
            }
        } else {
            OpKind::Normal
        };

        ast_ent.kind = AKind::FunHeader(kind);

        let ret = if self.token == TKind::RArrow {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };
        self.push(&mut ast_ent.sons, ret);

        // call convention
        let call_conv = if self.token == TKind::Ident {
            let call_conv = self.ast(AKind::Ident);
            self.next()?;
            call_conv
        } else {
            Ast::reserved_value()
        };
        self.push(&mut ast_ent.sons, call_conv);

        self.join_token(&mut ast_ent.token);

        Ok((self.add(ast_ent), visibility))
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let mutable = if self.token.kind == TKind::Var {
            self.next()?;
            true
        } else {
            false
        };
        let mut ast_ent = self.ast_ent(AKind::FunArgument(mutable));
        self.list(&mut ast_ent, TKind::None, TKind::Comma, TKind::Colon, |s| {
            s.expect_str(TKind::Ident, "expected ident")?;
            let ident = s.state.ast(AKind::Ident);
            s.next()?;
            Ok(ident)
        })?;

        let expr = self.type_expr()?;
        self.push(&mut ast_ent.sons, expr);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.token.kind {
            TKind::Return => self.return_statement(),
            TKind::Var | TKind::Let => self.var_statement(false),
            TKind::Break => return self.break_statement(),
            TKind::Continue => return self.continue_statement(),
            _ => self.expr(),
        }
    }

    fn var_statement(&mut self, top_level: bool) -> Result<Ast> {
        let mutable = self.token.kind == TKind::Var;
        let mut ast_ent = self.ast_ent(AKind::Pass);
        self.next()?;

        let vis = if top_level { self.vis()? } else { Vis::None };
        ast_ent.kind = AKind::VarStatement(vis, mutable);

        self.walk_block(|s| {
            let line = s.var_statement_line()?;
            s.state.push(&mut ast_ent.sons, line);
            Ok(())
        })?;

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn var_statement_line(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::VarAssign);
        let mut ident_group = self.ast_ent(AKind::Group);
        self.list(
            &mut ident_group,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::ident,
        )?;

        let datatype = if self.token == TKind::Colon {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::reserved_value()
        };

        let values = if self.token.span.hash == ID::new("=") {
            let mut values = self.ast_ent(AKind::Group);
            self.next()?;
            self.list(
                &mut values,
                TKind::None,
                TKind::Comma,
                TKind::None,
                Self::expr,
            )?;
            if values.sons.len(&self.cons) == 1 {
                std::iter::repeat(ident_group.sons.get(0, &self.cons).unwrap())
                    .take(ident_group.sons.len(&self.cons) - 1)
                    .for_each(|n| self.push(&mut values.sons, n));
            } else if values.sons.len(&self.cons) != ident_group.sons.len(&self.cons) {
                return Err(
                    self.unexpected_str("expected one value per ident or one value for all idents")
                );
            }
            self.add(values)
        } else {
            Ast::reserved_value()
        };

        if datatype == Ast::reserved_value() && values == Ast::reserved_value() {
            return Err(self.unexpected_str("expected '=' or ':' type"));
        }

        ast_ent.sons =
            EntityList::from_slice(&[self.add(ident_group), datatype, values], &mut self.cons);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn ident(&mut self) -> Result<Ast> {
        self.expect_str(TKind::Ident, "expected ident")?;
        let ast = self.ast(AKind::Ident);
        self.next()?;
        Ok(ast)
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::ReturnStatement);
        self.next()?;
        let ret_val = if let TKind::Indent(_) | TKind::Eof = self.token.kind {
            Ast::reserved_value()
        } else {
            self.expr()?
        };
        self.push(&mut ast_ent.sons, ret_val);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
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
            let op = self.ast_ent(AKind::Ident);
            let pre = precedence(self.main_state.display(&op.token.span));

            self.next()?;
            self.ignore_newlines()?;

            let mut next = self.simple_expr()?;

            if self.token == TKind::Op {
                let dif = pre - precedence(self.main_state.display(&self.token.span));

                if dif > 0 {
                    next = self.expr_low(next)?;
                }
            }

            let mut token = *self.token(previous);

            self.join_token_with(&mut token, self.token(next), false);

            // this handles the '{op}=' sugar
            result = if pre == ASSIGN_PRECEDENCE
                && op.token.span.len() != 1
                && self
                    .main_state
                    .display(&op.token.span)
                    .chars()
                    .last()
                    .unwrap()
                    == '='
            {
                let operator = AstEnt::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        self.main_state
                            .slice_span(&op.token.span, 0, op.token.span.len() - 1),
                    ),
                );
                let operator = self.add(operator);
                let eq = AstEnt::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        self.main_state.slice_span(
                            &op.token.span,
                            op.token.span.len() - 1,
                            op.token.span.len(),
                        ),
                    ),
                );
                let eq = self.add(eq);
                let expr = AstEnt::with_children(
                    AKind::BinaryOp,
                    token,
                    EntityList::from_slice(&[operator, result, next], &mut self.cons),
                );
                let expr = self.add(expr);

                let final_expr = AstEnt::with_children(
                    AKind::BinaryOp,
                    token,
                    EntityList::from_slice(&[eq, result.clone(), expr], &mut self.cons),
                );
                self.add(final_expr)
            } else {
                let expr = AstEnt::with_children(
                    AKind::BinaryOp,
                    token,
                    EntityList::from_slice(&[self.add(op), result, next], &mut self.cons),
                );

                self.add(expr)
            };
        }

        Ok(result)
    }

    fn simple_expr(&mut self) -> Result<Ast> {
        self.simple_expr_low(false)
    }

    fn simple_expr_low(&mut self, nested: bool) -> Result<Ast> {
        let mut ast = match self.token.kind {
            TKind::Ident => self.ident_expr()?,
            TKind::Int(..)
            | TKind::Uint(..)
            | TKind::Bool(..)
            | TKind::Char(..)
            | TKind::Float(..)
            | TKind::String(..) => self.ast(AKind::Lit),
            TKind::LPar => {
                let mut token = self.token;
                self.next()?;
                let expr = self.expr()?;
                let result = if self.token.kind == TKind::Comma {
                    let mut ast = self.ast_ent(AKind::Tuple);
                    self.push(&mut ast.sons, expr);
                    self.next()?;
                    self.list(
                        &mut ast,
                        TKind::None,
                        TKind::Comma,
                        TKind::RPar,
                        Self::expr,
                    )?;
                    self.add(ast)
                } else {
                    self.expect_str(TKind::RPar, "expected ')'")?;
                    self.next()?;
                    expr
                };
                self.join_token(&mut token);
                self.asts[result].token = token;
                result
            }
            TKind::If => return self.if_expr(),
            TKind::For => return self.loop_expr(),
            TKind::Op => {
                let mut ast_ent = self.ast_ent(AKind::UnaryOp);
                match self.main_state.display(&self.token.span) {
                    "&" => {
                        self.next()?;
                        let mutable = self.token.kind == TKind::Var;
                        if mutable {
                            self.next()?;
                        }
                        ast_ent.kind = AKind::Ref(mutable);
                    }
                    "*" => {
                        self.next()?;
                        ast_ent.kind = AKind::Deref;
                    }
                    _ => {
                        let ast = self.ast(AKind::Ident);
                        self.push(&mut ast_ent.sons, ast);
                        self.next()?;
                    }
                }
                let ast = self.simple_expr()?;
                self.push(&mut ast_ent.sons, ast);
                self.join_token(&mut ast_ent.token);
                return Ok(self.add(ast_ent));
            }
            TKind::Pass => {
                let ast = self.ast(AKind::Pass);
                self.next()?;
                return Ok(ast);
            }
            TKind::LBra => {
                let mut ast_ent = self.ast_ent(AKind::Array);
                self.list(
                    &mut ast_ent,
                    TKind::LBra,
                    TKind::Comma,
                    TKind::RBra,
                    Self::expr,
                )?;
                return Ok(self.add(ast_ent));
            }
            TKind::Fun => return Ok(self.fun_header(true)?.0),
            _ => todo!("unmatched simple expr pattern {:?}", self.token),
        };

        if self.kind(ast) == AKind::Lit {
            self.next()?;
        }

        if !nested && !self.is_type_expr {
            loop {
                let new_ast = match self.token.kind {
                    TKind::Dot => {
                        let mut new_ast = AstEnt::new(AKind::DotExpr, *self.token(ast));
                        self.push(&mut new_ast.sons, ast);
                        self.next()?;
                        let expr = self.simple_expr_low(true)?;
                        self.push(&mut new_ast.sons, expr);
                        new_ast
                    }
                    TKind::LPar => {
                        let AstEnt {
                            mut sons, token, ..
                        } = self.asts[ast];
                        let mut new_ast = AstEnt::new(AKind::Pass, token);
                        if self.kind(ast) == AKind::DotExpr {
                            new_ast.kind = AKind::Call(true);
                            new_ast.sons = EntityList::from_slice(
                                &[
                                    sons.get(1, &self.cons).unwrap(),
                                    sons.get(0, &self.cons).unwrap(),
                                ],
                                &mut self.cons,
                            );
                            sons.clear(&mut self.cons);
                        } else {
                            new_ast.kind = AKind::Call(false);
                            self.push(&mut new_ast.sons, ast);
                        }

                        self.list(
                            &mut new_ast,
                            TKind::LPar,
                            TKind::Comma,
                            TKind::RPar,
                            Self::expr,
                        )?;

                        new_ast
                    }
                    TKind::LBra => {
                        let AstEnt { token, .. } = self.asts[ast];
                        let mut new_ast = AstEnt::new(AKind::Index, token);
                        self.push(&mut new_ast.sons, ast);
                        self.next()?;
                        self.ignore_newlines()?;
                        let expr = self.expr()?;
                        self.push(&mut new_ast.sons, expr);
                        self.ignore_newlines()?;
                        self.expect_str(TKind::RBra, "expected ']'")?;
                        self.next()?;

                        new_ast
                    }

                    _ => break,
                };

                ast = self.add(new_ast);
            }
        }

        let mut ast_ent = self.asts[ast];
        if ast_ent.kind != AKind::Ident {
            self.join_token(&mut ast_ent.token);
        }
        self.asts[ast] = ast_ent;

        Ok(ast)
    }

    fn continue_statement(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Continue);
        self.next()?;

        let label = self.optional_tag()?;
        self.push(&mut ast_ent.sons, label);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn break_statement(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Break);
        self.next()?;

        let label = self.optional_tag()?;
        self.push(&mut ast_ent.sons, label);

        let ret = if let TKind::Indent(_) | TKind::Eof = self.token.kind {
            Ast::reserved_value()
        } else {
            self.expr()?
        };
        self.push(&mut ast_ent.sons, ret);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn loop_expr(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Loop);
        self.next()?;

        let label = self.optional_tag()?;
        self.push(&mut ast_ent.sons, label);

        let body = self.stmt_block()?;
        self.push(&mut ast_ent.sons, body);

        self.join_token(&mut ast_ent.token);

        Ok(self.add(ast_ent))
    }

    fn optional_tag(&mut self) -> Result<Ast> {
        Ok(if self.token == TKind::Tag {
            let ast = self.ast(AKind::Ident);
            self.next()?;
            ast
        } else {
            Ast::reserved_value()
        })
    }

    fn ident_expr(&mut self) -> Result<Ast> {
        let mut ast_ent = self.ast_ent(AKind::Ident);
        self.next()?;
        let mut ast = self.add(ast_ent);

        self.peek()?;
        if self.token == TKind::DoubleColon && self.peeked == TKind::Ident {
            let mut temp_ast = AstEnt::new(AKind::Path, ast_ent.token);
            self.push(&mut temp_ast.sons, ast);
            self.next()?;
            let ident = self.ident()?;
            self.push(&mut temp_ast.sons, ident);
            self.peek()?;
            if self.token == TKind::DoubleColon && self.peeked == TKind::Ident {
                self.next()?;
                let ident = self.ident()?;
                self.push(&mut temp_ast.sons, ident);
            }
            ast_ent = temp_ast;
            self.join_token(&mut ast_ent.token);
            ast = self.add(ast_ent);
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
            let mut temp_ast = AstEnt::new(AKind::Instantiation, ast_ent.token);
            self.push(&mut temp_ast.sons, ast);
            ast_ent = temp_ast;
            self.list(
                &mut ast_ent,
                TKind::LBra,
                TKind::Comma,
                TKind::RBra,
                Self::expr,
            )?;

            self.join_token(&mut ast_ent.token);
            ast = self.add(ast_ent);
        }

        Ok(ast)
    }

    fn if_expr(&mut self) -> Result<Ast> {
        let ast = self.ast(AKind::IfExpr);
        self.next()?;
        let condition = self.expr()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.token.kind {
            TKind::Else => {
                self.next()?;
                self.stmt_block()?
            }
            TKind::Elif => {
                // simplify later parsing
                let mut ast_ent = self.ast_ent(AKind::Group);
                let expr = self.if_expr()?;
                self.push(&mut ast_ent.sons, expr);
                self.add(ast_ent)
            }
            TKind::Indent(_) => {
                self.peek()?;
                match self.peeked.kind {
                    TKind::Else => {
                        self.next()?;
                        self.next()?;
                        let val = self.stmt_block()?;
                        val
                    }
                    TKind::Elif => {
                        self.next()?;
                        // simplify later parsing
                        let mut ast_ent = self.ast_ent(AKind::Group);
                        let expr = self.if_expr()?;
                        self.push(&mut ast_ent.sons, expr);
                        self.add(ast_ent)
                    }
                    _ => Ast::reserved_value(),
                }
            }
            _ => Ast::reserved_value(),
        };

        let mut ast_ent = self.asts[ast];
        ast_ent.sons = EntityList::from_slice(&[condition, then_block, else_block], &mut self.cons);

        self.join_token(&mut ast_ent.token);
        self.asts[ast] = ast_ent;

        Ok(ast)
    }

    fn vis(&mut self) -> Result<Vis> {
        Ok(match self.token.kind {
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
        if let TKind::Indent(level) = self.token.kind {
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
        let mut ast_ent = self.ast_ent(AKind::Group);
        self.next()?;
        self.walk_block(|s| {
            let expr = parser(s)?;
            s.state.push(&mut ast_ent.sons, expr);
            Ok(())
        })?;

        Ok(self.add(ast_ent))
    }

    fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.token.kind, TKind::Indent(_) | TKind::Eof) {
            return Err(self.unexpected_str("expected indentation"));
        }

        loop {
            self.peek()?;
            match self.peeked.kind {
                TKind::Indent(_) => {
                    self.next()?;
                }
                TKind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.token.kind {
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
        ast: &mut AstEnt,
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
        self.push(&mut ast.sons, expr);

        while self.token == separator {
            self.next()?;
            self.ignore_newlines()?;
            // trailing colon allowed
            if end != TKind::None && self.token == end {
                break;
            }
            let expr = parser(self)?;
            self.push(&mut ast.sons, expr);
        }

        if end != TKind::None {
            self.ignore_newlines()?;
            self.expect(end.clone(), format!("expected {}", end))?;
            self.next()?;
        }

        Ok(())
    }

    fn ignore_newlines(&mut self) -> Result {
        while let TKind::Indent(_) = self.token.kind {
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
        if self.token.kind == kind {
            Ok(())
        } else {
            Err(self.unexpected(message))
        }
    }

    fn unexpected_str(&self, message: &'static str) -> AError {
        self.unexpected(message.to_string())
    }

    fn unexpected(&self, message: String) -> AError {
        AError::new(AEKind::UnexpectedToken(message), self.token)
    }

    fn join_token(&self, token: &mut Token) {
        self.join_token_with(token, &self.token, true);
    }

    fn join_token_with(&self, token: &mut Token, other: &Token, trim: bool) {
        self.main_state
            .join_spans(&mut token.span, &other.span, trim);
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
            .find(|(a_name, _)| self.display(a_name) == name)
            .map(|(_, value)| value.clone())
    }
}

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct AState {
    pub l_state: LState,
    peeked: Token,
    pub token: Token,
    is_type_expr: bool,
    level: usize,
    asts: PrimaryMap<Ast, AstEnt>,
    cons: ListPool<Ast>,

    funs: EntityList<Ast>,
    types: EntityList<Ast>,
    globals: EntityList<Ast>,
}

crate::inherit!(AState, l_state, LState);

impl AState {
    pub fn ast(&mut self, kind: AKind) -> Ast {
        self.asts.push(AstEnt::new(kind, self.token))
    }

    pub fn add(&mut self, ast_ent: AstEnt) -> Ast {
        self.asts.push(ast_ent)
    }

    pub fn ast_ent(&mut self, kind: AKind) -> AstEnt {
        AstEnt::new(kind, self.token)
    }

    pub fn kind(&self, ast: Ast) -> AKind {
        self.asts[ast].kind
    }

    pub fn son_ent(&self, ast: Ast, index: usize) -> &AstEnt {
        &self.asts[self.son(ast, index)]
    }

    pub fn son(&self, ast: Ast, index: usize) -> Ast {
        self.son_optional(ast, index).unwrap()
    }

    pub fn son_optional(&self, ast: Ast, index: usize) -> Option<Ast> {
        self.sons(ast).get(index, &self.cons)
    }

    pub fn sons(&self, ast: Ast) -> EntityList<Ast> {
        self.asts[ast].sons
    }

    pub fn token(&self, ast: Ast) -> &Token {
        &self.asts[ast].token
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
        self.ast_len(ast) == 0
    }

    pub fn son_len(&self, ast: Ast, index: usize) -> usize {
        self.son_ent(ast, index).sons.len(&self.cons)
    }

    pub fn get(&self, sons: EntityList<Ast>, index: usize) -> Ast {
        sons.get(index, &self.cons).unwrap()
    }

    pub fn load(&self, ast: Ast) -> &AstEnt {
        &self.asts[ast]
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

    pub fn attr(&self, attrs: Ast, id: ID) -> Option<Ast> {
        if attrs.is_reserved_value() {
            return None;
        }
        let sons = self.sons(attrs);
        self.slice(sons)
            .iter()
            .find(|&&a| self.kind(a) != AKind::Comment && self.son_ent(a, 0).token.span.hash == id)
            .cloned()
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
    pub kind: AKind,
    pub sons: EntityList<Ast>,
    pub token: Token,
}

impl AstEnt {
    pub fn new(kind: AKind, token: Token) -> Self {
        Self {
            kind,
            sons: EntityList::new(),
            token,
        }
    }

    fn with_children(kind: AKind, token: Token, sons: EntityList<Ast>) -> AstEnt {
        Self { kind, sons, token }
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
        let AstEnt { kind, sons, token } = self.state.asts[ast];
        write!(f, "{:?} {:?}", kind, self.main_state.display(&token.span))?;
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

    Fun(Vis),
    Impl(Vis),
    FunHeader(OpKind),
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

    ReturnStatement,

    BinaryOp,
    UnaryOp,
    IfExpr,
    DotExpr,
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
            (Vis::None, Vis::None) => Vis::None,
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
    let source = SourceEnt {
        name: "text_code.mf".to_string(),
        content: crate::testing::TEST_CODE.to_string(),
        ..Default::default()
    };

    let source = a_main_state.sources.push(source);
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
