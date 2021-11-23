pub mod ast;
pub mod error;

use crate::{lexer::*, util::sdbm::ID};
pub use ast::*;
pub use error::*;

use std::ops::Deref;

pub type Result<T> = std::result::Result<T, AstError>;

pub struct AstParser {
    lexer: Lexer,
    peeked: Option<Token>,
    current_token: Token,
    level: usize,
}

impl AstParser {
    pub fn new(mut lexer: Lexer) -> AstParser {
        AstParser {
            current_token: lexer.next().unwrap_or(Token::eof()),
            lexer,
            peeked: None,
            level: 0,
        }
    }

    pub fn parse(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Group);
        while self.current_token.kind != TKind::Eof {
            match self.current_token.kind {
                TKind::Fun => ast.push(self.fun()?),
                TKind::Attr => ast.push(self.attr()?),
                TKind::Struct => ast.push(self.struct_declaration()?),
                TKind::Indent(0) => self.advance(),
                TKind::Use => ast.push(self.use_statement()?),
                _ => self.unexpected_str("expected 'fun' or 'attr' or 'struct' or 'use'")?,
            }
        }
        Ok(ast)
    }

    fn use_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        self.advance();

        let external = self.current_token == TKind::Extern;
        if external {
            self.advance();
        }

        let export = self.current_token == TKind::Pub;
        if export {
            self.advance();
        }

        ast.kind = AKind::UseStatement(external, export);

        if self.current_token == TKind::Ident {
            ast.push(self.ident()?); // alias
        } else {
            ast.push(Ast::none());
        }

        if !matches!(self.current_token.kind, TKind::String(_)) {
            self.unexpected_str("expected string literal")?;
        }

        ast.push(self.ast(AKind::Literal));
        self.advance();

        Ok(ast)
    }

    fn struct_declaration(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        self.advance();

        ast.kind = AKind::StructDeclaration(self.visibility());

        ast.push(self.ident_expression()?);

        ast.push(self.block(Self::struct_field)?);

        Ok(ast)
    }

    fn struct_field(&mut self) -> Result<Ast> {
        if self.current_token.kind == TKind::Attr {
            return self.attr();
        }

        let embedded = if self.current_token == TKind::Embed {
            self.advance();
            true
        } else {
            false
        };

        let mut ast = self.ast(AKind::StructField(embedded));

        self.list(
            &mut ast,
            TKind::None,
            TKind::Comma,
            TKind::Colon,
            Self::ident,
        )?;

        ast.push(self.expression()?);

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn attr(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Attribute);
        self.advance();

        self.list(
            &mut ast,
            TKind::None,
            TKind::Comma,
            TKind::None,
            Self::attr_element,
        )?;

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn attr_element(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::AttributeElement);
        self.advance();

        match self.current_token.kind {
            TKind::LPar => self.list(
                &mut ast,
                TKind::LPar,
                TKind::Comma,
                TKind::RPar,
                Self::attr_element,
            )?,
            TKind::Op => match self.current_token.spam.deref() {
                "=" => {
                    ast.kind = AKind::AttributeAssign;
                    self.advance();
                    ast.push(self.expression()?);
                }
                _ => self.unexpected_str("expected '=' or '('")?,
            },
            _ => (),
        }

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn fun(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::None);
        let (header, visibility) = self.fun_header()?;
        ast.push(header);
        ast.kind = AKind::Function(visibility);
        ast.push(if self.current_token == TKind::Colon {
            self.stmt_block()?
        } else {
            Ast::none()
        });

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn fun_header(&mut self) -> Result<(Ast, Visibility)> {
        let mut ast = self.ast(AKind::FunctionHeader);
        self.advance();

        let visibility = self.visibility();

        ast.push(match self.current_token.kind {
            TKind::Ident | TKind::Op => self.ast(AKind::Identifier),
            _ => Ast::none(),
        });
        self.advance();

        if self.current_token == TKind::LPar {
            self.list(
                &mut ast,
                TKind::LPar,
                TKind::Comma,
                TKind::RPar,
                Self::fun_argument,
            )?;
        }

        ast.push(if self.current_token == TKind::RArrow {
            self.advance();
            self.expression()?
        } else {
            Ast::none()
        });

        ast.token.to_group(&self.current_token, true);

        Ok((ast, visibility))
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let mutable = if self.current_token.kind == TKind::Var {
            self.advance();
            true
        } else {
            false
        };
        let mut ast = self.ast(AKind::FunctionArgument(mutable));
        self.list(&mut ast, TKind::None, TKind::Comma, TKind::Colon, |s| {
            s.expect_str(TKind::Ident, "expected identifier")?;
            let ident = s.ast(AKind::Identifier);
            s.advance();
            Ok(ident)
        })?;
        ast.push(self.expression()?);

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.current_token.kind {
            TKind::Return => self.return_statement(),
            TKind::Var | TKind::Let | TKind::Svar => self.var_statement(),
            _ => self.expression(),
        }
    }

    fn var_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::VarStatement(
            matches!(self.current_token.kind, TKind::Var | TKind::Svar),
            self.current_token.kind == TKind::Svar,
        ));
        self.advance();
        self.walk_block(|s| {
            ast.push(s.var_statement_line()?);
            Ok(())
        })?;

        ast.token.to_group(&self.current_token, true);

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

        let datatype = if self.current_token == TKind::Colon {
            self.advance();
            self.simple_expression()?
        } else {
            Ast::none()
        };

        let values = if self.current_token.spam.deref() == "=" {
            let mut values = self.ast(AKind::Group);
            self.advance();
            self.list(
                &mut values,
                TKind::None,
                TKind::Comma,
                TKind::None,
                Self::expression,
            )?;
            if values.len() == 1 {
                std::iter::repeat(ident_group[0].clone())
                    .take(ident_group.len() - 1)
                    .for_each(|n| values.push(n));
            } else if values.len() != ident_group.len() {
                self.unexpected_str(
                    "expected one value per identifier or one value for all identifiers",
                )?;
            }
            values
        } else {
            Ast::none()
        };

        if datatype.kind == AKind::None && values.kind == AKind::None {
            self.unexpected_str("expected ':' or '='")?;
        }

        ast.children = vec![ident_group, datatype, values];

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn ident(&mut self) -> Result<Ast> {
        self.expect_str(TKind::Ident, "expected identifier")?;
        let ast = self.ast(AKind::Identifier);
        self.advance();
        Ok(ast)
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::ReturnStatement);
        self.advance();
        let ret_val = if let TKind::Indent(_) = self.current_token.kind {
            Ast::none()
        } else {
            self.expression()?
        };
        ast.push(ret_val);

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn expression(&mut self) -> Result<Ast> {
        let expr = self.simple_expression()?;
        self.expression_low(expr)
    }

    fn expression_low(&mut self, previous: Ast) -> Result<Ast> {
        let mut result = previous;
        while self.current_token == TKind::Op {
            let op = self.current_token.clone();
            let pre = precedence(op.spam.deref());

            self.advance();
            self.ignore_newlines();

            let mut next = self.simple_expression()?;

            if self.current_token == TKind::Op {
                let dif = pre - precedence(self.current_token.spam.deref());
                let is_or_or_and = self.current_token.spam.deref() == "or"
                    || self.current_token.spam.deref() == "and";

                if dif > 0 || is_or_or_and {
                    next = self.expression_low(next)?;
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
                    AKind::Identifier,
                    Token::new(
                        TKind::Op,
                        op.spam.sub(0..op.spam.len() - 1),
                        op.line_data.clone(),
                    ),
                );
                let eq = Ast::new(
                    AKind::Identifier,
                    Token::new(
                        TKind::Op,
                        op.spam.sub(op.spam.len() - 1..op.spam.len()),
                        op.line_data.clone(),
                    ),
                );

                Ast::with_children(
                    AKind::BinaryOperation,
                    token.clone(),
                    vec![
                        eq,
                        result.clone(),
                        Ast::with_children(
                            AKind::BinaryOperation,
                            token,
                            vec![operator, result, next],
                        ),
                    ],
                )
            } else {
                Ast::with_children(
                    AKind::BinaryOperation,
                    token,
                    vec![Ast::new(AKind::Identifier, op), result, next],
                )
            };
        }

        Ok(result)
    }

    fn simple_expression(&mut self) -> Result<Ast> {
        self.simple_expression_low(false)
    }

    fn simple_expression_low(&mut self, nested: bool) -> Result<Ast> {
        let mut ast = match self.current_token.kind {
            TKind::Ident => self.ident_expression()?,
            TKind::Int(..)
            | TKind::Uint(..)
            | TKind::Bool(..)
            | TKind::Char(..)
            | TKind::Float(..)
            | TKind::String(..) => self.ast(AKind::Literal),
            TKind::LPar => {
                self.advance();
                let expr = self.expression()?;
                self.expect_str(TKind::RPar, "expected ')'")?;
                self.advance();
                expr
            }
            TKind::If => return self.if_expression(),
            TKind::Loop => return self.loop_expression(),
            TKind::Break => return self.break_expression(),
            TKind::Continue => return self.continue_expression(),
            TKind::Op | TKind::Var => {
                let mut ast = self.ast(AKind::UnaryOperation);
                ast.push(self.ast(AKind::Identifier));
                self.advance();
                ast.push(self.simple_expression()?);
                return Ok(ast);
            }
            _ => todo!(
                "unmatched simple expression pattern {:?}",
                self.current_token
            ),
        };

        if ast.kind == AKind::Literal {
            self.advance();
        }

        if !nested {
            loop {
                match self.current_token.kind {
                    TKind::Dot => {
                        let mut new_ast = Ast::new(AKind::DotExpr, ast.token.clone());
                        new_ast.push(ast);
                        self.advance();
                        new_ast.push(self.simple_expression_low(true)?);
                        ast = new_ast;
                    }
                    TKind::LPar => {
                        let mut new_ast = Ast::new(AKind::Call, ast.token.clone());
                        if ast.kind == AKind::DotExpr {
                            ast.drain(..).rev().for_each(|e| new_ast.push(e));
                        } else {
                            new_ast.push(ast);
                        }

                        self.list(
                            &mut new_ast,
                            TKind::LPar,
                            TKind::Comma,
                            TKind::RPar,
                            Self::expression,
                        )?;

                        ast = new_ast;
                    }
                    TKind::LBra => {
                        let mut new_ast = Ast::new(AKind::Index, ast.token.clone());
                        new_ast.push(ast);
                        self.advance();
                        self.ignore_newlines();
                        new_ast.push(self.expression()?);
                        self.ignore_newlines();
                        self.expect_str(TKind::RBra, "expected ']'")?;
                        self.advance();

                        ast = new_ast;
                    }

                    _ => break,
                }
            }
        }

        if ast.kind != AKind::Identifier {
            ast.token.to_group(&self.current_token, true);
        }

        Ok(ast)
    }

    fn continue_expression(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Break);
        self.advance();

        ast.push(self.optional_label());

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn break_expression(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Break);
        self.advance();

        ast.push(self.optional_label());

        ast.push(if let TKind::Indent(_) = self.current_token.kind {
            Ast::none()
        } else {
            self.expression()?
        });

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn loop_expression(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Loop);
        self.advance();

        ast.push(self.optional_label());

        ast.push(self.stmt_block()?);

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn optional_label(&mut self) -> Ast {
        if self.current_token == TKind::Label {
            let ast = self.ast(AKind::Identifier);
            self.advance();
            ast
        } else {
            Ast::none()
        }
    }

    fn ident_expression(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Identifier);
        self.advance();

        if self.current_token == TKind::DoubleColon {
            let mut temp_ast = Ast::new(AKind::ExplicitPackage, ast.token.clone());
            temp_ast.push(ast);
            self.advance();
            temp_ast.push(self.ident()?);
            ast = temp_ast;
            ast.token.to_group(&self.current_token, true);
        }

        if self.current_token == TKind::LCurly {
            let mut temp_ast = Ast::new(AKind::Instantiation, ast.token.clone());
            temp_ast.push(ast);
            ast = temp_ast;
            self.list(
                &mut ast,
                TKind::LCurly,
                TKind::Comma,
                TKind::RCurly,
                Self::expression,
            )?;

            ast.token.to_group(&self.current_token, true);
        }

        Ok(ast)
    }

    fn if_expression(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::IfExpression);
        self.advance();
        let condition = self.expression()?;
        let then_block = self.stmt_block()?;

        let else_block = match self.current_token.kind {
            TKind::Else => {
                self.advance();
                self.stmt_block()?
            }
            TKind::Elif => {
                // simplify later parsing
                let mut ast = self.ast(AKind::Group);
                ast.push(self.if_expression()?);
                ast
            }
            TKind::Indent(_) => match self.peek().kind {
                TKind::Else => {
                    self.advance();
                    self.advance();
                    let val = self.stmt_block()?;
                    val
                }
                TKind::Elif => {
                    self.advance();
                    // simplify later parsing
                    let mut ast = self.ast(AKind::Group);
                    ast.push(self.if_expression()?);
                    ast
                }
                _ => Ast::none(),
            },
            _ => Ast::none(),
        };

        ast.children = vec![condition, then_block, else_block];

        ast.token.to_group(&self.current_token, true);

        Ok(ast)
    }

    fn visibility(&mut self) -> Visibility {
        match self.current_token.kind {
            TKind::Pub => {
                self.advance();
                Visibility::Public
            }
            TKind::Priv => {
                self.advance();
                Visibility::FilePrivate
            }
            _ => Visibility::Private,
        }
    }

    fn walk_block<F: FnMut(&mut Self) -> Result<()>>(&mut self, mut parser: F) -> Result<()> {
        if let TKind::Indent(level) = self.current_token.kind {
            if level > self.level + 1 {
                self.unexpected_str(
                    "too deep indentation, one indentation level is equal 2 spaces of one tab",
                )?;
            }
            self.level += 1;
            while self.level_continues()? {
                if self.current_token == TKind::Pass {
                    self.advance();
                } else {
                    parser(self)?;
                }
            }
        } else {
            if self.current_token == TKind::Pass {
                self.advance();
            } else {
                parser(self)?;
            }
        }
        Ok(())
    }

    fn block<F: FnMut(&mut Self) -> Result<Ast>>(&mut self, mut parser: F) -> Result<Ast> {
        self.expect_str(TKind::Colon, "expected ':' as a start of block")?;
        let mut ast = self.ast(AKind::Group);
        self.advance();
        self.walk_block(|s| {
            ast.push(parser(s)?);
            Ok(())
        })?;

        Ok(ast)
    }

    fn ignore_newlines(&mut self) {
        while let TKind::Indent(_) = self.current_token.kind {
            self.advance();
        }
    }

    fn level_continues(&mut self) -> Result<bool> {
        if !matches!(self.current_token.kind, TKind::Indent(_) | TKind::Eof) {
            self.unexpected_str("expected indentation")?;
        }

        loop {
            match self.peek().kind {
                TKind::Indent(_) => {
                    self.advance();
                }
                TKind::Eof => return Ok(false),
                _ => break,
            }
        }

        match self.current_token.kind {
            TKind::Indent(level) => {
                if level == self.level {
                    self.advance();
                    Ok(true)
                } else if level < self.level {
                    self.level -= 1;
                    Ok(false)
                } else {
                    self.unexpected_str("unexpected indentation dive")?;
                    unreachable!();
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
            self.advance();
            self.ignore_newlines();
        }

        if end != TKind::None && self.current_token == end {
            self.advance();
            return Ok(());
        }

        ast.push(parser(self)?);

        while self.current_token == separator {
            self.advance();
            self.ignore_newlines();
            ast.push(parser(self)?);
        }

        if end != TKind::None {
            self.ignore_newlines();
            self.expect(end.clone(), format!("expected {}", end))?;
            self.advance();
        }

        Ok(())
    }

    fn peek(&mut self) -> Token {
        if self.peeked.is_none() {
            self.peeked = Some(self.lexer.next().unwrap_or(Token::eof()));
        }
        self.peeked.as_ref().unwrap().clone()
    }

    fn advance(&mut self) {
        if let Some(token) = self.peeked.clone() {
            self.current_token = token;
            self.peeked = None;
        } else {
            self.current_token = self.lexer.next().unwrap_or(Token::eof());
        }
    }

    fn ast(&self, kind: AKind) -> Ast {
        Ast::new(kind, self.current_token.clone())
    }

    fn expect_str(&self, kind: TKind, message: &str) -> Result<()> {
        self.expect(kind, message.to_string())
    }

    fn expect(&self, kind: TKind, message: String) -> Result<()> {
        if self.current_token.kind == kind {
            Ok(())
        } else {
            self.unexpected(message)
        }
    }

    fn unexpected_str(&self, message: &'static str) -> Result<()> {
        self.unexpected(message.to_string())
    }

    fn unexpected(&self, message: String) -> Result<()> {
        Err(AstError::new(
            AEKind::UnexpectedToken(message),
            self.current_token.clone(),
        ))
    }
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

pub fn test() {
    let lexer = Lexer::new(
        ID::new(),
        "test_code.pmh".to_string(),
        crate::testing::TEST_CODE.to_string(),
    );
    let mut parser = AstParser::new(lexer);

    let ast = parser.parse().unwrap();

    println!("{}", ast);
}
