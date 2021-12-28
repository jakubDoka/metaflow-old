use meta_ser::{MetaQuickSer, MetaSer};
use traits::MetaQuickSer;

use crate::{lexer::*, util::sdbm::ID};

use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
};

pub type Result<T = ()> = std::result::Result<T, AError>;

pub struct AParser<'a> {
    main_state: &'a mut AMainState,
    state: &'a mut AState,
}

impl<'a> AParser<'a> {
    pub fn new(main_state: &'a mut AMainState, state: &'a mut AState) -> Self {
        Self { main_state, state }
    }

    pub fn parse_manifest(&mut self) -> Result<Manifest> {
        let mut manifest = Manifest::default();
        loop {
            match self.state.token.kind {
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
            let name = self.state.token.span;
            self.next()?;
            match self.state.token.kind {
                TKind::Op if self.state.token.span.hash == self.main_state.equal_sign => {
                    self.next()?;

                    if !matches!(self.state.token.kind, TKind::String(_)) {
                        return Err(self.unexpected_str("expected string literal"));
                    }

                    let mut value = self.state.token.span;
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
        while let TKind::Indent(_) = self.state.token.kind {
            self.next()?;
        }

        if self.state.token == TKind::Use {
            self.next()?;
            self.walk_block(|s| s.import_line(imports))?;
        }

        Ok(())
    }

    fn import_line(&mut self, imports: &mut Vec<Import>) -> Result {
        let mut token = self.state.token;

        let nickname = if self.state.token == TKind::Ident {
            let nickname = self.state.token.span;
            self.next()?;
            Some(nickname)
        } else {
            None
        };

        let path = if let TKind::String(_) = self.state.token.kind {
            let mut path = self.state.token.span;
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

    pub fn parse(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Group);
        while self.state.token.kind != TKind::Eof {
            match self.state.token.kind {
                TKind::Impl => ast.push(self.impl_block()?),
                TKind::Fun => ast.push(self.fun()?),
                TKind::Attr => ast.push(self.attr()?),
                TKind::Struct => ast.push(self.struct_declaration()?),
                TKind::Var | TKind::Let => ast.push(self.var_statement(true)?),
                TKind::Comment(_) => {
                    let ast = ast.push(self.ast(AKind::Comment));
                    self.next()?;
                    ast
                }
                TKind::Indent(_) => self.next()?,
                _ => {
                    return Err(self.unexpected_str(
                        "expected 'fun' or 'attr' or 'struct' or 'let' or 'var' or 'impl' or '##'",
                    ))
                }
            }
        }
        Ok(ast)
    }

    fn impl_block(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);

        self.next()?;

        let vis = self.vis()?;

        ast.kind = AKind::Impl(vis);

        ast.push(if self.state.token == TKind::LBra {
            let mut ast = self.ast(AKind::Group);
            self.list(
                &mut ast,
                TKind::LBra,
                TKind::Comma,
                TKind::RBra,
                Self::ident,
            )?;
            ast
        } else {
            Ast::none()
        });

        ast.push(self.type_expr()?);

        let mut body = self.ast(AKind::Group);
        self.expect_str(TKind::Colon, "expected ':' after 'impl' type")?;
        self.next()?;
        self.walk_block(|s| {
            match s.state.token.kind {
                TKind::Fun => body.push(s.fun()?),
                TKind::Attr => body.push(s.attr()?),
                TKind::Var | TKind::Let => body.push(s.var_statement(true)?),
                TKind::Comment(_) => {
                    let ast = ast.push(s.ast(AKind::Comment));
                    s.next()?;
                    ast
                }
                _ => {
                    return Err(
                        s.unexpected_str("expected 'fun' or 'attr' or 'let' or 'var' or '##'")
                    )
                }
            }
            Ok(())
        })?;
        ast.push(body);

        Ok(ast)
    }

    fn struct_declaration(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        self.next()?;

        ast.kind = AKind::StructDeclaration(self.vis()?);

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

        let vis = self.vis()?;

        let embedded = if self.state.token == TKind::Embed {
            self.next()?;
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

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn attr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Attribute);
        self.next()?;

        self.list(
            &mut ast,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::attr_element,
        )?;

        self.join_token(&mut ast.token);

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
            TKind::Op => {
                if self.state.token.span.hash == self.main_state.equal_sign {
                    ast.kind = AKind::AttributeAssign;
                    self.next()?;
                    ast.push(self.expr()?);
                } else {
                    return Err(self.unexpected_str("expected '=' or '('"));
                }
            }
            _ => (),
        }

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn fun(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        let (header, visibility) = self.fun_header(false)?;
        ast.push(header);
        ast.kind = AKind::Fun(visibility);

        ast.push(
            if self.state.token == TKind::Colon && !self.state.is_type_expr {
                self.stmt_block()?
            } else {
                Ast::none()
            },
        );

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn fun_header(&mut self, anonymous: bool) -> Result<(Ast, Vis)> {
        let mut ast = self.ast(AKind::None);
        self.next()?;

        let visibility = if anonymous { Vis::None } else { self.vis()? };

        let previous = self.state.is_type_expr;
        self.state.is_type_expr = true;
        let is_op = self.state.token.kind == TKind::Op;
        ast.push(match self.state.token.kind {
            TKind::Ident | TKind::Op if !anonymous => self.ident_expr()?,
            _ => Ast::none(),
        });
        self.state.is_type_expr = previous;

        if self.state.token == TKind::LPar {
            let parser = if self.state.is_type_expr {
                Self::expr
            } else {
                Self::fun_argument
            };
            self.list(&mut ast, TKind::LPar, TKind::Comma, TKind::RPar, parser)?;
        }

        let kind = if is_op {
            let arg_count = ast[1..].iter().fold(0, |acc, i| acc + i.len() - 1);
            match arg_count {
                1 => OpKind::Unary,
                2 => OpKind::Binary,
                _ => return Err(AError::new(
                    AEKind::UnexpectedToken(
                        "operator functions can have either 1 or 2 arguments, (unary and binary)"
                            .to_string(),
                    ),
                    ast.token,
                )),
            }
        } else {
            OpKind::Normal
        };

        ast.kind = AKind::FunHeader(kind);

        ast.push(if self.state.token == TKind::RArrow {
            self.next()?;
            self.type_expr()?
        } else {
            Ast::none()
        });

        // call convention
        if self.state.token == TKind::Ident {
            ast.push(self.ast(AKind::Ident));
            self.next()?;
        } else {
            ast.push(Ast::none());
        }

        self.join_token(&mut ast.token);

        Ok((ast, visibility))
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let mutable = if self.state.token.kind == TKind::Var {
            self.next()?;
            true
        } else {
            false
        };
        let mut ast = self.ast(AKind::FunArgument(mutable));
        self.list(&mut ast, TKind::None, TKind::Comma, TKind::Colon, |s| {
            s.expect_str(TKind::Ident, "expected ident")?;
            let ident = s.ast(AKind::Ident);
            s.next()?;
            Ok(ident)
        })?;
        ast.push(self.type_expr()?);

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.state.token.kind {
            TKind::Return => self.return_statement(),
            TKind::Var | TKind::Let => self.var_statement(false),
            TKind::Break => return self.break_statement(),
            TKind::Continue => return self.continue_statement(),
            _ => self.expr(),
        }
    }

    fn var_statement(&mut self, top_level: bool) -> Result<Ast> {
        let mutable = self.state.token.kind == TKind::Var;
        let mut ast = self.ast(AKind::None);
        self.next()?;

        let vis = if top_level { self.vis()? } else { Vis::None };
        ast.kind = AKind::VarStatement(vis, mutable);

        self.walk_block(|s| {
            ast.push(s.var_statement_line()?);
            Ok(())
        })?;

        self.join_token(&mut ast.token);

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
            self.next()?;
            self.type_expr()?
        } else {
            Ast::none()
        };

        let values = if self.state.token.span.hash == self.main_state.equal_sign {
            let mut values = self.ast(AKind::Group);
            self.next()?;
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

        if datatype.kind == AKind::None && values.kind == AKind::None {
            return Err(self.unexpected_str("expected '=' or ':' type"));
        }

        ast.children = vec![ident_group, datatype, values];

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn ident(&mut self) -> Result<Ast> {
        self.expect_str(TKind::Ident, "expected ident")?;
        let ast = self.ast(AKind::Ident);
        self.next()?;
        Ok(ast)
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::ReturnStatement);
        self.next()?;
        let ret_val = if let TKind::Indent(_) | TKind::Eof = self.state.token.kind {
            Ast::none()
        } else {
            self.expr()?
        };
        ast.push(ret_val);

        self.join_token(&mut ast.token);

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
            let op = self.state.token;
            let pre = precedence(self.main_state.display(&op.span));

            self.next()?;
            self.ignore_newlines()?;

            let mut next = self.simple_expr()?;

            if self.state.token == TKind::Op {
                let dif = pre - precedence(self.main_state.display(&self.state.token.span));

                if dif > 0 {
                    next = self.expr_low(next)?;
                }
            }

            let mut token = result.token;

            self.join_token_with(&mut token, &next.token, false);

            // this handles the '{op}=' sugar
            result = if pre == ASSIGN_PRECEDENCE
                && op.span.len() != 1
                && self.main_state.display(&op.span).chars().last().unwrap() == '='
            {
                let operator = Ast::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        self.main_state.slice_span(&op.span, 0, op.span.len() - 1),
                    ),
                );
                let eq = Ast::new(
                    AKind::Ident,
                    Token::new(
                        TKind::Op,
                        self.main_state
                            .slice_span(&op.span, op.span.len() - 1, op.span.len()),
                    ),
                );

                Ast::with_children(
                    AKind::BinaryOp,
                    token,
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
                let token = self.state.token;
                self.next()?;
                let mut expr = self.expr()?;
                self.expect_str(TKind::RPar, "expected ')'")?;
                self.next()?;
                expr.token = token;
                expr
            }
            TKind::If => return self.if_expr(),
            TKind::Loop => return self.loop_expr(),
            TKind::Op => {
                let mut ast = self.ast(AKind::UnaryOp);
                match self.main_state.display(&self.state.token.span) {
                    "&" => {
                        self.next()?;
                        ast.kind = AKind::Ref;
                    }
                    "*" => {
                        self.next()?;
                        ast.kind = AKind::Deref;
                    }
                    _ => {
                        ast.push(self.ast(AKind::Ident));
                        self.next()?;
                    }
                }
                ast.push(self.simple_expr()?);
                self.join_token(&mut ast.token);
                return Ok(ast);
            }
            TKind::Pass => {
                let ast = self.ast(AKind::Pass);
                self.next()?;
                return Ok(ast);
            }
            TKind::LBra => {
                let mut ast = self.ast(AKind::Array);
                self.list(&mut ast, TKind::LBra, TKind::Comma, TKind::RBra, Self::expr)?;
                return Ok(ast);
            }
            TKind::Fun => return Ok(self.fun_header(true)?.0),
            _ => todo!("unmatched simple expr pattern {:?}", self.state.token),
        };

        if ast.kind == AKind::Lit {
            self.next()?;
        }

        if !nested && !self.state.is_type_expr {
            loop {
                match self.state.token.kind {
                    TKind::Dot => {
                        let mut new_ast = Ast::new(AKind::DotExpr, ast.token);
                        new_ast.push(ast);
                        self.next()?;
                        new_ast.push(self.simple_expr_low(true)?);
                        ast = new_ast;
                    }
                    TKind::LPar => {
                        let mut new_ast = Ast::new(AKind::None, ast.token);
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
                        let mut new_ast = Ast::new(AKind::Index, ast.token);
                        new_ast.push(ast);
                        self.next()?;
                        self.ignore_newlines()?;
                        new_ast.push(self.expr()?);
                        self.ignore_newlines()?;
                        self.expect_str(TKind::RBra, "expected ']'")?;
                        self.next()?;

                        ast = new_ast;
                    }

                    _ => break,
                }
            }
        }

        if ast.kind != AKind::Ident {
            self.join_token(&mut ast.token);
        }

        Ok(ast)
    }

    fn continue_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Continue);
        self.next()?;

        ast.push(self.optional_label()?);

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn break_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Break);
        self.next()?;

        ast.push(self.optional_label()?);

        ast.push(if let TKind::Indent(_) = self.state.token.kind {
            Ast::none()
        } else {
            self.expr()?
        });

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn loop_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Loop);
        self.next()?;

        ast.push(self.optional_label()?);

        ast.push(self.stmt_block()?);

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn optional_label(&mut self) -> Result<Ast> {
        Ok(if self.state.token == TKind::Label {
            let ast = self.ast(AKind::Ident);
            self.next()?;
            ast
        } else {
            Ast::none()
        })
    }

    fn ident_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Ident);
        self.next()?;

        self.peek()?;
        if self.state.token == TKind::DoubleColon && self.state.peeked == TKind::Ident {
            let mut temp_ast = Ast::new(AKind::Path, ast.token);
            temp_ast.push(ast);
            self.next()?;
            temp_ast.push(self.ident()?);
            self.peek()?;
            if self.state.token == TKind::DoubleColon && self.state.peeked == TKind::Ident {
                self.next()?;
                temp_ast.push(self.ident()?);
            }
            ast = temp_ast;
            self.join_token(&mut ast.token);
        }

        let is_instantiation = self.state.is_type_expr && self.state.token == TKind::LBra
            || self.state.token == TKind::DoubleColon;

        if is_instantiation {
            if self.state.token == TKind::DoubleColon {
                self.next()?;
            }
            self.expect_str(
                TKind::LBra,
                "expected '[' as a start of generic instantiation",
            )?;
            let mut temp_ast = Ast::new(AKind::Instantiation, ast.token);
            temp_ast.push(ast);
            ast = temp_ast;
            self.list(&mut ast, TKind::LBra, TKind::Comma, TKind::RBra, Self::expr)?;

            self.join_token(&mut ast.token);
        }

        Ok(ast)
    }

    fn if_expr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::IfExpr);
        self.next()?;
        let condition = self.expr()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.state.token.kind {
            TKind::Else => {
                self.next()?;
                self.stmt_block()?
            }
            TKind::Elif => {
                // simplify later parsing
                let mut ast = self.ast(AKind::Group);
                ast.push(self.if_expr()?);
                ast
            }
            TKind::Indent(_) => {
                self.peek()?;
                match self.state.peeked.kind {
                    TKind::Else => {
                        self.next()?;
                        self.next()?;
                        let val = self.stmt_block()?;
                        val
                    }
                    TKind::Elif => {
                        self.next()?;
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

        self.join_token(&mut ast.token);

        Ok(ast)
    }

    fn vis(&mut self) -> Result<Vis> {
        Ok(match self.state.token.kind {
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
        self.next()?;
        self.walk_block(|s| {
            ast.push(parser(s)?);
            Ok(())
        })?;

        Ok(ast)
    }

    fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.state.token.kind, TKind::Indent(_) | TKind::Eof) {
            return Err(self.unexpected_str("expected indentation"));
        }

        loop {
            self.peek()?;
            match self.state.peeked.kind {
                TKind::Indent(_) => {
                    self.next()?;
                }
                TKind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.state.token.kind {
            TKind::Indent(level) => {
                if level == self.state.level {
                    self.next()?;
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
            self.next()?;
            self.ignore_newlines()?;
        }

        if end != TKind::None && self.state.token == end {
            self.next()?;
            return Ok(());
        }

        ast.push(parser(self)?);

        while self.state.token == separator {
            self.next()?;
            self.ignore_newlines()?;
            ast.push(parser(self)?);
        }

        if end != TKind::None {
            self.ignore_newlines()?;
            self.expect(end.clone(), format!("expected {}", end))?;
            self.next()?;
        }

        Ok(())
    }

    fn ignore_newlines(&mut self) -> Result {
        while let TKind::Indent(_) = self.state.token.kind {
            self.next()?;
        }

        Ok(())
    }

    fn peek(&mut self) -> Result {
        let mut state = self.state.l_state.clone();
        let token = self
            .main_state
            .lexer_for(&mut state)
            .next()
            .map_err(|err| AError::new(AEKind::LError(err), Token::default()))?;
        self.state.peeked = token;
        Ok(())
    }

    fn next(&mut self) -> Result {
        let token = self
            .main_state
            .lexer_for(&mut self.state.l_state)
            .next()
            .map_err(|err| AError::new(AEKind::LError(err), Token::default()))?;
        self.state.token = token;
        Ok(())
    }

    fn ast(&mut self, kind: AKind) -> Ast {
        Ast::new(kind, self.state.token)
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

    fn unexpected_str(&self, message: &'static str) -> AError {
        self.unexpected(message.to_string())
    }

    fn unexpected(&self, message: String) -> AError {
        AError::new(AEKind::UnexpectedToken(message), self.state.token)
    }

    fn join_token(&self, token: &mut Token) {
        self.join_token_with(token, &self.state.token, true);
    }

    fn join_token_with(&self, token: &mut Token, other: &Token, trim: bool) {
        self.main_state
            .join_spans(&mut token.span, &other.span, trim);
    }
}

#[derive(Debug, Clone, MetaSer)]
pub struct AMainState {
    pub l_main_state: LMainState,
    pub equal_sign: ID,
}

crate::inherit!(AMainState, l_main_state, LMainState);

impl Default for AMainState {
    fn default() -> Self {
        Self {
            l_main_state: LMainState::default(),
            equal_sign: ID::new("="),
        }
    }
}

impl AMainState {
    pub fn a_state_for(&mut self, source: Source) -> AState {
        let mut l_state = LState::new(source);
        let mut lexer = self.lexer_for(&mut l_state);
        let token = lexer.next().unwrap();

        AState {
            l_state,
            peeked: token,
            token,
            is_type_expr: false,
            level: 0,
        }
    }

    pub fn attr_of(&self, manifest: &Manifest, name: &str) -> Option<Span> {
        manifest
            .attrs
            .iter()
            .find(|(a_name, _)| self.display(a_name) == name)
            .map(|(_, value)| value.clone())
    }
}

#[derive(Debug, Clone, Default, Copy, MetaQuickSer)]
pub struct AState {
    pub l_state: LState,
    peeked: Token,
    pub token: Token,
    is_type_expr: bool,
    level: usize,
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

#[derive(Clone, Debug, Copy, Default)]
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

#[derive(Debug, Clone, Default, PartialEq, MetaSer)]
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
}

crate::inherit!(Ast, children, Vec<Ast>);

pub struct AstDisplay<'a> {
    state: &'a AMainState,
    ast: &'a Ast,
}

impl<'a> AstDisplay<'a> {
    pub fn new(state: &'a AMainState, ast: &'a Ast) -> Self {
        Self { state, ast }
    }

    fn log(&self, ast: &Ast, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::iter::repeat(())
            .take(level)
            .for_each(|_| f.write_char(' ').unwrap());
        write!(
            f,
            "{:?} {:?}",
            ast.kind,
            self.state.display(&ast.token.span)
        )?;
        if ast.children.len() > 0 {
            write!(f, ":\n")?;
            for child in &ast.children {
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

#[derive(Debug, Clone, Copy, PartialEq, MetaQuickSer)]
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

    StructDeclaration(Vis),
    StructField(Vis, bool),

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
    Ref,
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

    None,
}

impl Default for AKind {
    fn default() -> Self {
        AKind::None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, MetaQuickSer)]
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
    let source = a_main_state.sources.add(source);
    let mut a_state = a_main_state.a_state_for(source);

    let mut a_parser = AParser::new(&mut a_main_state, &mut a_state);
    let ast = a_parser.parse().unwrap();

    println!("{}", AstDisplay::new(&a_main_state, &ast));
}
