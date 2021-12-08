use crate::lexer::*;

use std::{
    fmt::{Display, Write},
    ops::{Deref, DerefMut},
};

pub type Result<T = ()> = std::result::Result<T, AstError>;

pub struct AstParser<'a> {
    state: &'a mut AstState,
    context: &'a mut AstContext,
}

impl<'a> AstParser<'a> {
    pub fn new(state: &'a mut AstState, context: &'a mut AstContext) -> Self {
        Self { state, context }
    }

    pub fn parse_manifest(&mut self) -> Result<Manifest> {
        let mut manifest = std::mem::take(&mut self.context.temp_manifest);
        manifest.clear();

        loop {
            match self.state.token.kind {
                TKind::Eof => break,
                TKind::Indent(_) => {
                    self.state.next();
                    continue;
                }
                TKind::Ident => (),
                _ => {
                    return Err(self.unexpected_str("every item in manifest starts with identifier"))
                }
            }
            let name = self.state.token.spam.raw();
            self.state.next();
            match self.state.token.kind {
                TKind::Op if self.state.token.spam.raw() == "=" => {
                    self.state.next();

                    if !matches!(self.state.token.kind, TKind::String(_)) {
                        return Err(self.unexpected_str("expected string literal"));
                    }

                    let value = self.state.token.spam.raw();
                    let value = &value[1..value.len() - 1];

                    manifest.attrs.push((name, value));

                    self.state.next();
                }
                TKind::Colon => match name {
                    "dependencies" => {
                        self.state.next();
                        self.walk_block(|s| {
                            let mut token = s.state.token.clone();

                            let external = if s.state.token == TKind::Extern {
                                s.state.next();
                                true
                            } else {
                                false
                            };

                            s.expect_str(TKind::Ident, "expected dependency name")?;
                            let name = s.state.token.spam.raw();
                            s.state.next();

                            if !matches!(s.state.token.kind, TKind::String(_)) {
                                return Err(s.unexpected_str("expected string literal as repository link with version or local path"));
                            }
                            let path_and_version = s.state.token.spam.raw();
                            let path_and_version = &path_and_version[1..path_and_version.len() - 1];
                            s.state.next();

                            let mut parts = path_and_version.splitn(2, '@');
                            let path = parts.next().unwrap_or("");
                            let version = parts.next().unwrap_or("main");

                            token.to_group(&s.state.token, true);

                            let dependency = Dep {
                                name,
                                path,
                                version,
                                external,
                                token
                            };

                            manifest.deps.push(dependency);
                            Ok(())
                        })?;
                    }
                    _ => {
                        return Err(
                            self.unexpected(format!("unexpected item in manifest '{}'", name))
                        )
                    }
                },
                _ => {
                    return Err(
                        self.unexpected_str("expected '=' or ':' after identifier in manifest")
                    )
                }
            }
        }

        Ok(manifest)
    }

    pub fn take_imports(&mut self) -> Result {
        while let TKind::Indent(_) = self.state.token.kind {
            self.state.next();
        }

        if self.state.token == TKind::Use {
            self.state.next();

            self.walk_block(|s| {
                if s.state.token == TKind::Extern {
                    s.state.next();
                    s.walk_block(|s| {
                        s.import_line(true)?;
                        Ok(())
                    })?;
                } else {
                    s.import_line(false)?;
                }
                Ok(())
            })?;
        }

        Ok(())
    }

    fn import_line(&mut self, external: bool) -> Result {
        let mut token = self.state.token.clone();

        let nickname = if self.state.token == TKind::Ident {
            let nickname = self.state.token.spam.raw();
            self.state.next();
            nickname
        } else {
            ""
        };

        let path = if let TKind::String(_) = self.state.token.kind {
            let path = self.state.token.spam.raw();
            &path[1..path.len() - 1]
        } else {
            return Err(self.unexpected_str("expected string literal as import path"));
        };

        token.to_group(&self.state.token, true);
        self.state.next();

        self.state.imports.push(Import {
            external,
            nickname,
            path,
            token,
        });

        Ok(())
    }

    pub fn parse(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Group);
        while self.state.token.kind != TKind::Eof {
            match self.state.token.kind {
                TKind::Fun => ast.push(self.fun()?),
                TKind::Attr => ast.push(self.attr()?),
                TKind::Struct => ast.push(self.struct_declaration()?),
                TKind::Indent(0) => self.state.next(),
                _ => {
                    return Err(self.unexpected_str("expected 'fun' or 'attr' or 'struct' or 'use'"))
                }
            }
        }
        Ok(ast)
    }

    fn struct_declaration(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        self.state.next();

        ast.kind = AKind::StructDeclaration(self.visibility());

        ast.push(self.type_expr()?);

        if self.state.token == TKind::Colon {
            ast.push(self.block(Self::struct_field)?);
        } else {
            ast.push(Ast::none());
        }

        Ok(ast)
    }

    fn struct_field(&mut self) -> Result<Ast> {
        if self.state.token.kind == TKind::Attr {
            return self.attr();
        }

        let vis = self.visibility();

        let embedded = if self.state.token == TKind::Embed {
            self.state.next();
            true
        } else {
            false
        };

        let mut ast = self.ast(AKind::StructField(vis, embedded));

        self.list(
            &mut ast,
            TKind::None,
            TKind::Comma,
            TKind::Colon,
            Self::ident,
        )?;

        ast.push(self.type_expr()?);

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn attr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Attribute);
        self.state.next();

        self.list(
            &mut ast,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::attr_element,
        )?;

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn attr_element(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::AttributeElement);
        ast.push(self.ident()?);

        match self.state.token.kind {
            TKind::LPar => self.list(
                &mut ast,
                TKind::LPar,
                TKind::Comma,
                TKind::RPar,
                Self::attr_element,
            )?,
            TKind::Op => match self.state.token.spam.deref() {
                "=" => {
                    ast.kind = AKind::AttributeAssign;
                    self.state.next();
                    ast.push(self.expr()?);
                }
                _ => return Err(self.unexpected_str("expected '=' or '('")),
            },
            _ => (),
        }

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn fun(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        let (header, visibility) = self.fun_header()?;
        ast.push(header);
        ast.kind = AKind::Fun(visibility);
        ast.push(if self.state.token == TKind::Colon {
            self.stmt_block()?
        } else {
            Ast::none()
        });

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn fun_header(&mut self) -> Result<(Ast, Vis)> {
        let mut ast = self.ast(AKind::FunHeader);
        self.state.next();

        let visibility = self.visibility();

        self.state.is_type_expr = true;
        ast.push(match self.state.token.kind {
            TKind::Ident | TKind::Op => self.ident_expr()?,
            _ => Ast::none(),
        });
        self.state.is_type_expr = false;

        if self.state.token == TKind::LPar {
            self.list(
                &mut ast,
                TKind::LPar,
                TKind::Comma,
                TKind::RPar,
                Self::fun_argument,
            )?;
        }

        ast.push(if self.state.token == TKind::RArrow {
            self.state.next();
            self.type_expr()?
        } else {
            Ast::none()
        });

        ast.token.to_group(&self.state.token, true);

        Ok((ast, visibility))
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let mutable = if self.state.token.kind == TKind::Var {
            self.state.next();
            true
        } else {
            false
        };
        let mut ast = self.ast(AKind::FunArgument(mutable));
        self.list(&mut ast, TKind::None, TKind::Comma, TKind::Colon, |s| {
            s.expect_str(TKind::Ident, "expected ident")?;
            let ident = s.ast(AKind::Ident);
            s.state.next();
            Ok(ident)
        })?;
        ast.push(self.type_expr()?);

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.state.token.kind {
            TKind::Return => self.return_statement(),
            TKind::Var | TKind::Let => self.var_statement(),
            TKind::Break => return self.break_statement(),
            TKind::Continue => return self.continue_statement(),
            _ => self.expr(),
        }
    }

    fn var_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::VarStatement(self.state.token.kind == TKind::Var));
        self.state.next();
        self.walk_block(|s| {
            ast.push(s.var_statement_line()?);
            Ok(())
        })?;

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn var_statement_line(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::VarAssign);
        let mut ident_group = self.ast(AKind::Group);
        self.list(
            &mut ident_group,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::ident,
        )?;

        let datatype = if self.state.token == TKind::Colon {
            self.state.next();
            self.type_expr()?
        } else {
            Ast::none()
        };

        let values = if self.state.token.spam.deref() == "=" {
            let mut values = self.ast(AKind::Group);
            self.state.next();
            self.list(
                &mut values,
                TKind::None,
                TKind::Comma,
                TKind::None,
                Self::expr,
            )?;
            if values.len() == 1 {
                std::iter::repeat(ident_group[0].clone())
                    .take(ident_group.len() - 1)
                    .for_each(|n| values.push(n));
            } else if values.len() != ident_group.len() {
                return Err(
                    self.unexpected_str("expected one value per ident or one value for all idents")
                );
            }
            values
        } else {
            Ast::none()
        };

        ast.children = vec![ident_group, datatype, values];

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn ident(&mut self) -> Result<Ast> {
        self.expect_str(TKind::Ident, "expected ident")?;
        let ast = self.ast(AKind::Ident);
        self.state.next();
        Ok(ast)
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::ReturnStatement);
        self.state.next();
        let ret_val = if let TKind::Indent(_) | TKind::Eof = self.state.token.kind {
            Ast::none()
        } else {
            self.expr()?
        };
        ast.push(ret_val);

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn type_expr(&mut self) -> Result<Ast> {
        self.state.is_type_expr = true;

        let result = self.simple_expr();

        self.state.is_type_expr = false;

        result
    }

    fn expr(&mut self) -> Result<Ast> {
        let expr = self.simple_expr()?;
        self.expr_low(expr)
    }

    fn expr_low(&mut self, previous: Ast) -> Result<Ast> {
        let mut result = previous;
        while self.state.token == TKind::Op {
            let op = self.state.token.clone();
            let pre = precedence(op.spam.deref());

            self.state.next();
            self.ignore_newlines();

            let mut next = self.simple_expr()?;

            if self.state.token == TKind::Op {
                let dif = pre - precedence(self.state.token.spam.deref());
                let is_or_or_and =
                    self.state.token.spam.deref() == "or" || self.state.token.spam.deref() == "and";

                if dif > 0 || is_or_or_and {
                    next = self.expr_low(next)?;
                }
            }

            let mut token = result.token.clone();
            token.to_group(&next.token, false);

            // this handles the '{op}=' sugar
            result = if pre == ASSIGN_PRECEDENCE
                && op.spam.len() != 1
                && op.spam.as_bytes().last().unwrap() == &b'='
            {
                let operator = Ast::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        op.spam.sub(0..op.spam.len() - 1),
                        op.line_data.clone(),
                    ),
                );
                let eq = Ast::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        op.spam.sub(op.spam.len() - 1..op.spam.len()),
                        op.line_data.clone(),
                    ),
                );

                Ast::with_children(
                    AKind::BinaryOp,
                    token.clone(),
                    vec![
                        eq,
                        result.clone(),
                        Ast::with_children(AKind::BinaryOp, token, vec![operator, result, next]),
                    ],
                )
            } else {
                Ast::with_children(
                    AKind::BinaryOp,
                    token,
                    vec![Ast::new(AKind::Ident, op), result, next],
                )
            };
        }

        Ok(result)
    }

    fn simple_expr(&mut self) -> Result<Ast> {
        self.simple_expr_low(false)
    }

    fn simple_expr_low(&mut self, nested: bool) -> Result<Ast> {
        let mut ast = match self.state.token.kind {
            TKind::Ident => self.ident_expr()?,
            TKind::Int(..)
            | TKind::Uint(..)
            | TKind::Bool(..)
            | TKind::Char(..)
            | TKind::Float(..)
            | TKind::String(..) => self.ast(AKind::Lit),
            TKind::LPar => {
                self.state.next();
                let expr = self.expr()?;
                self.expect_str(TKind::RPar, "expected ')'")?;
                self.state.next();
                expr
            }
            TKind::If => return self.if_expr(),
            TKind::Loop => return self.loop_expr(),
            TKind::Op => {
                let mut ast = self.ast(AKind::UnaryOp);
                match self.state.token.spam.deref() {
                    "&" => {
                        self.state.next();
                        let mutable = self.state.token.kind == TKind::Var;
                        ast.kind = AKind::Ref(mutable);
                        if mutable {
                            self.state.next();
                        }
                    }
                    "*" => {
                        self.state.next();
                        let mutable = self.state.token.kind == TKind::Var;
                        ast.kind = AKind::Deref(mutable);
                        self.state.next();
                    }
                    _ => {
                        ast.push(self.ast(AKind::Ident));
                        self.state.next();
                    }
                }
                ast.push(self.simple_expr()?);
                ast.token.to_group(&self.state.token, true);
                return Ok(ast);
            }
            TKind::Pass => {
                let ast = self.ast(AKind::Pass);
                self.state.next();
                return Ok(ast);
            }
            _ => todo!("unmatched simple expr pattern {:?}", self.state.token),
        };

        if ast.kind == AKind::Lit {
            self.state.next();
        }

        if !nested && !self.state.is_type_expr {
            loop {
                match self.state.token.kind {
                    TKind::Dot => {
                        let mut new_ast = Ast::new(AKind::DotExpr, ast.token.clone());
                        new_ast.push(ast);
                        self.state.next();
                        new_ast.push(self.simple_expr_low(true)?);
                        ast = new_ast;
                    }
                    TKind::LPar => {
                        let mut new_ast = Ast::new(AKind::None, ast.token.clone());
                        if ast.kind == AKind::DotExpr {
                            new_ast.kind = AKind::Call(true);
                            ast.drain(..).rev().for_each(|e| new_ast.push(e));
                        } else {
                            new_ast.kind = AKind::Call(false);
                            new_ast.push(ast);
                        }

                        self.list(
                            &mut new_ast,
                            TKind::LPar,
                            TKind::Comma,
                            TKind::RPar,
                            Self::expr,
                        )?;

                        ast = new_ast;
                    }
                    TKind::LBra => {
                        let mut new_ast = Ast::new(AKind::Index, ast.token.clone());
                        new_ast.push(ast);
                        self.state.next();
                        self.ignore_newlines();
                        new_ast.push(self.expr()?);
                        self.ignore_newlines();
                        self.expect_str(TKind::RBra, "expected ']'")?;
                        self.state.next();

                        ast = new_ast;
                    }

                    _ => break,
                }
            }
        }

        if ast.kind != AKind::Ident {
            ast.token.to_group(&self.state.token, true);
        }

        Ok(ast)
    }

    fn continue_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Continue);
        self.state.next();

        ast.push(self.optional_label());

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn break_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Break);
        self.state.next();

        ast.push(self.optional_label());

        ast.push(if let TKind::Indent(_) = self.state.token.kind {
            Ast::none()
        } else {
            self.expr()?
        });

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn loop_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Loop);
        self.state.next();

        ast.push(self.optional_label());

        ast.push(self.stmt_block()?);

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn optional_label(&mut self) -> Ast {
        if self.state.token == TKind::Label {
            let ast = self.ast(AKind::Ident);
            self.state.next();
            ast
        } else {
            Ast::none()
        }
    }

    fn ident_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Ident);
        self.state.next();

        self.state.peek();
        if self.state.token == TKind::DoubleColon && self.state.peeked == TKind::Ident {
            let mut temp_ast = Ast::new(AKind::ExplicitPackage, ast.token.clone());
            temp_ast.push(ast);
            self.state.next();
            temp_ast.push(self.ident()?);
            ast = temp_ast;
            ast.token.to_group(&self.state.token, true);
        }

        let is_instantiation = self.state.is_type_expr && self.state.token == TKind::LBra
            || self.state.token == TKind::DoubleColon;

        if is_instantiation {
            if self.state.token == TKind::DoubleColon {
                self.state.next();
            }
            self.expect_str(
                TKind::LBra,
                "expected '[' as a start of generic instantiation",
            )?;
            let mut temp_ast = Ast::new(AKind::Instantiation, ast.token.clone());
            temp_ast.push(ast);
            ast = temp_ast;
            self.list(&mut ast, TKind::LBra, TKind::Comma, TKind::RBra, Self::expr)?;

            ast.token.to_group(&self.state.token, true);
        }

        Ok(ast)
    }

    fn if_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::IfExpr);
        self.state.next();
        let condition = self.expr()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.state.token.kind {
            TKind::Else => {
                self.state.next();
                self.stmt_block()?
            }
            TKind::Elif => {
                // simplify later parsing
                let mut ast = self.ast(AKind::Group);
                ast.push(self.if_expr()?);
                ast
            }
            TKind::Indent(_) => {
                self.state.peek();
                match self.state.peeked.kind {
                    TKind::Else => {
                        self.state.next();
                        self.state.next();
                        let val = self.stmt_block()?;
                        val
                    }
                    TKind::Elif => {
                        self.state.next();
                        // simplify later parsing
                        let mut ast = self.ast(AKind::Group);
                        ast.push(self.if_expr()?);
                        ast
                    }
                    _ => Ast::none(),
                }
            }
            _ => Ast::none(),
        };

        ast.children = vec![condition, then_block, else_block];

        ast.token.to_group(&self.state.token, true);

        Ok(ast)
    }

    fn visibility(&mut self) -> Vis {
        match self.state.token.kind {
            TKind::Pub => {
                self.state.next();
                Vis::Public
            }
            TKind::Priv => {
                self.state.next();
                Vis::Private
            }
            _ => Vis::None,
        }
    }

    fn walk_block<F: FnMut(&mut Self) -> Result<()>>(&mut self, mut parser: F) -> Result<()> {
        if let TKind::Indent(level) = self.state.token.kind {
            if level > self.state.level + 1 {
                return Err(self.unexpected_str(
                    "too deep indentation, one indentation level is equal 2 spaces or one tab",
                ));
            }
            self.state.level += 1;
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
        let mut ast = self.ast(AKind::Group);
        self.state.next();
        self.walk_block(|s| {
            ast.push(parser(s)?);
            Ok(())
        })?;

        Ok(ast)
    }

    fn ignore_newlines(&mut self) {
        while let TKind::Indent(_) = self.state.token.kind {
            self.state.next();
        }
    }

    fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.state.token.kind, TKind::Indent(_) | TKind::Eof) {
            return Err(self.unexpected_str("expected indentation"));
        }

        loop {
            self.state.peek();
            match self.state.peeked.kind {
                TKind::Indent(_) => {
                    self.state.next();
                }
                TKind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.state.token.kind {
            TKind::Indent(level) => {
                if level == self.state.level {
                    self.state.next();
                    Ok(true)
                } else if level < self.state.level {
                    self.state.level -= 1;
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
        ast: &mut Ast,
        start: TKind,
        separator: TKind,
        end: TKind,
        mut parser: F,
    ) -> Result<()> {
        if start != TKind::None {
            self.expect(start.clone(), format!("expected {}", start))?;
            self.state.next();
            self.ignore_newlines();
        }

        if end != TKind::None && self.state.token == end {
            self.state.next();
            return Ok(());
        }

        ast.push(parser(self)?);

        while self.state.token == separator {
            self.state.next();
            self.ignore_newlines();
            ast.push(parser(self)?);
        }

        if end != TKind::None {
            self.ignore_newlines();
            self.expect(end.clone(), format!("expected {}", end))?;
            self.state.next();
        }

        Ok(())
    }

    fn ast(&mut self, kind: AKind) -> Ast {
        self.context.ast(kind, self.state.token.clone())
    }

    fn expect_str(&self, kind: TKind, message: &str) -> Result<()> {
        self.expect(kind, message.to_string())
    }

    fn expect(&self, kind: TKind, message: String) -> Result<()> {
        if self.state.token.kind == kind {
            Ok(())
        } else {
            Err(self.unexpected(message))
        }
    }

    fn unexpected_str(&self, message: &'static str) -> AstError {
        self.unexpected(message.to_string())
    }

    fn unexpected(&self, message: String) -> AstError {
        AstError::new(AEKind::UnexpectedToken(message), self.state.token.clone())
    }
}

#[derive(Debug, Clone, Default)]
pub struct AstContext {
    pub ast_pool: Vec<Ast>,
    pub temp_manifest: Manifest,
}

impl AstContext {
    pub fn new() -> AstContext {
        AstContext {
            ast_pool: Vec::new(),
            temp_manifest: Manifest::default(),
        }
    }

    pub fn recycle(&mut self, ast: Ast) {
        let mut i = self.ast_pool.len();
        self.ast_pool.push(ast);
        while i < self.ast_pool.len() {
            let mut ast = std::mem::take(&mut self.ast_pool[i]);
            ast.drain(..).for_each(|e| self.ast_pool.push(e));
            self.ast_pool[i] = ast;
            i += 1;
        }
    }

    pub fn ast(&mut self, kind: AKind, token: Token) -> Ast {
        if let Some(mut ast) = self.ast_pool.pop() {
            ast.kind = kind;
            ast.token = token;
            ast
        } else {
            Ast::new(kind, token)
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct AstState {
    lexer: Lexer,
    peeked: Token,
    token: Token,
    is_type_expr: bool,
    level: usize,
    pub imports: Vec<Import>,
}

impl AstState {
    pub fn new(mut lexer: Lexer) -> AstState {
        AstState {
            token: lexer.next().unwrap_or(Token::eof()),
            peeked: lexer.clone().next().unwrap_or(Token::eof()),
            lexer,
            is_type_expr: false,
            level: 0,
            imports: vec![],
        }
    }

    pub fn file_name(&self) -> &'static str {
        self.lexer.file_name()
    }

    fn peek(&mut self) {
        self.peeked = self.lexer.clone().next().unwrap_or(Token::eof());
    }

    fn next(&mut self) {
        self.token = self.lexer.next().unwrap_or(Token::eof());
    }
}

#[derive(Clone, Debug, Default)]
pub struct Import {
    pub external: bool,
    pub nickname: &'static str,
    pub path: &'static str,
    pub token: Token,
}

#[derive(Clone, Debug, Default)]
pub struct Manifest {
    pub attrs: Vec<(&'static str, &'static str)>,
    pub deps: Vec<Dep>,
}

impl Manifest {
    pub fn clear(&mut self) {
        self.attrs.clear();
        self.deps.clear();
    }
}

#[derive(Clone, Debug, Default)]
pub struct Dep {
    pub path: &'static str,
    pub name: &'static str,
    pub version: &'static str,
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

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Ast {
    pub kind: AKind,
    pub children: Vec<Ast>,
    pub token: Token,
}

impl Ast {
    pub fn new(kind: AKind, token: Token) -> Ast {
        Self::with_children(kind, token, vec![])
    }

    pub fn none() -> Ast {
        Self::new(AKind::None, Token::eof())
    }

    pub fn with_children(kind: AKind, token: Token, children: Vec<Ast>) -> Ast {
        Ast {
            kind,
            children,
            token,
        }
    }

    pub fn push(&mut self, ast: Ast) {
        self.children.push(ast);
    }

    fn log(&self, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::iter::repeat(())
            .take(level)
            .for_each(|_| f.write_char(' ').unwrap());
        write!(f, "{:?} {}", self.kind, self.token)?;
        if self.children.len() > 0 {
            write!(f, ":\n")?;
            for child in &self.children {
                child.log(level + 1, f)?;
            }
        } else {
            write!(f, "\n")?;
        }

        Ok(())
    }
}

impl std::fmt::Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.log(0, f)
    }
}

impl DerefMut for Ast {
    fn deref_mut(&mut self) -> &mut Vec<Ast> {
        &mut self.children
    }
}

impl Deref for Ast {
    type Target = Vec<Ast>;

    fn deref(&self) -> &Self::Target {
        &self.children
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AKind {
    UseStatement(bool),

    ExplicitPackage,

    Fun(Vis),
    FunHeader,
    FunArgument(bool),
    Call(bool), // true if dot syntax is used
    Index,

    StructDeclaration(Vis),
    StructField(Vis, bool),

    Attribute,
    AttributeElement,
    AttributeAssign,

    VarStatement(bool),
    VarAssign,

    ReturnStatement,

    BinaryOp,
    UnaryOp,
    IfExpr,
    DotExpr,
    Ref(bool),
    Deref(bool),

    Loop,
    Break,
    Continue,

    Pass,

    Group,

    Ident,
    Instantiation,
    Lit,

    None,
}

impl Default for AKind {
    fn default() -> Self {
        AKind::None
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Vis {
    Public,
    None,
    Private,
}

impl Default for Vis {
    fn default() -> Self {
        Vis::Public
    }
}

#[derive(Debug)]
pub struct AstError {
    pub kind: AEKind,
    pub token: Token,
}

impl AstError {
    pub fn new(kind: AEKind, token: Token) -> AstError {
        AstError { kind, token }
    }
}

impl Display for AstError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{}", TokenView::new(&self.token))?;
        match &self.kind {
            AEKind::UnexpectedToken(expected) => writeln!(f, "{}\n", expected),
            AEKind::UnexpectedEof => writeln!(f, "unexpected end of file\n"),
            AEKind::InvalidAttribute(name, hint) => {
                writeln!(f, "invalid attribute `{}`, hint: {}", name, hint)
            }
            AEKind::MissingAttribute(name, hint) => {
                writeln!(f, "missing attribute `{}`, hint: {}", name, hint)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum AEKind {
    UnexpectedToken(String),
    UnexpectedEof,
    MissingAttribute(&'static str, &'static str),
    InvalidAttribute(&'static str, &'static str),
}

impl Into<AstError> for AEKind {
    fn into(self) -> AstError {
        AstError {
            kind: self,
            token: Token::default(),
        }
    }
}

pub fn test() {
    let lexer = Lexer::new(
        "test_code.pmh".to_string(),
        crate::testing::TEST_CODE.to_string(),
    );

    let mut state = AstState::new(lexer);
    let mut context = AstContext::new();

    let mut parser = AstParser::new(&mut state, &mut context);

    let ast = parser.parse().unwrap();

    println!("{}", ast);

    context.recycle(ast);
}
