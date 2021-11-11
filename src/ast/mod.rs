use std::{convert::TryInto, fmt::Write, iter::repeat, ops::{Deref, DerefMut}};

use crate::lexer::{Lexer, TKind, Token};

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
                TKind::Fun => {
                    ast.push(self.fun()?);
                }
                TKind::Indent(0) => self.advance(),
                _ => self.unexpected_str("expected 'fun'")?,
            }
        }
        Ok(ast)
    }

    fn fun(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::Function);
        ast.push(self.fun_header()?);
        ast.push(self.stmt_block()?);
        Ok(ast)
    }

    fn fun_header(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::FunctionHeader);
        self.advance();
        ast.push(match self.current_token.kind {
            TKind::Ident | TKind::Op => self.ast(AKind::Identifier),
            _ => self.empty_ast(),
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
            self.empty_ast()
        });

        Ok(ast)
    }

    fn fun_argument(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::FunctionArgument);
        self.list(&mut ast, TKind::None, TKind::Comma, TKind::Colon, |s| {
            s.expect_str(TKind::Ident, "expected identifier")?;
            let ident = s.ast(AKind::Identifier);
            s.advance();
            Ok(ident)
        })?;
        ast.push(self.expression()?);
        Ok(ast)
    }

    fn stmt_block(&mut self) -> Result<Ast> {
        self.block(Self::statement)
    }

    fn statement(&mut self) -> Result<Ast> {
        match self.current_token.kind {
            TKind::Return => self.return_statement(),
            _ => self.expression(),
        }
    }

    fn return_statement(&mut self) -> Result<Ast> {
        let mut ast = self.ast(AKind::ReturnStatement);
        self.advance();
        let ret_val = if let TKind::Indent(_) = self.current_token.kind {
            self.empty_ast()
        } else {
            self.expression()?
        };
        ast.push(ret_val);
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
            let pre = precedence(op.value.deref());
            
            self.advance();
            self.ignore_newlines();  
            
            let mut next = self.simple_expression()?;
            
            if self.current_token == TKind::Op {
                let dif = pre - precedence(self.current_token.value.deref());
                let is_or_or_and = self.current_token.value.deref() == "or" || self.current_token.value.deref() == "and";
    
                if dif > 0 || is_or_or_and {
                    next = self.expression_low(next)?;
                }
            }

            result = Ast::with_children(AKind::BinaryOperation, op.clone(), vec![Ast::new(AKind::Identifier, op), result, next]);
        }

        Ok(result)
    }        

    fn simple_expression(&mut self) -> Result<Ast> {        
        let result = match self.current_token.kind {
            TKind::Ident => self.ast(AKind::Identifier),
            TKind::Int(..) => self.ast(AKind::Literal),
            _ => todo!(),
        };
        self.advance();
        Ok(result)
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
                    self.advance();
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
            self.expect(start, format!("expected {}", start))?;
            self.advance();
        }

        if end != TKind::None && self.current_token == end {
            self.advance();
            return Ok(());
        }

        ast.push(parser(self)?);

        while self.current_token == separator {
            self.advance();
            ast.push(parser(self)?);
        }

        if end != TKind::None {
            self.expect(end, format!("expected {}", end))?;
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

    fn empty_ast(&mut self) -> Ast {
        self.ast(AKind::None)
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

#[derive(Debug, Clone, Default)]
pub struct Ast {
    pub kind: AKind,
    pub children: Vec<Ast>,
    pub token: Token,
}

impl Ast {
    pub fn new(kind: AKind, token: Token) -> Ast {
        Self::with_children(kind, token, vec![])
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
        repeat(' ')
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
    Function,
    FunctionHeader,
    FunctionArgument,

    ReturnStatement,

    BinaryOperation,

    Group,

    Identifier,
    Literal,

    None,
}

impl Default for AKind {
    fn default() -> Self {
        AKind::None
    }
}

#[derive(Debug)]
pub struct AstError {
    pub kind: AEKind,
    pub token: Option<Token>,
}

impl AstError {
    pub fn new(kind: AEKind, token: Token) -> AstError {
        AstError {
            kind,
            token: Some(token),
        }
    }
}

#[derive(Debug)]
pub enum AEKind {
    UnexpectedToken(String),
    UnexpectedEof,
}

impl Into<AstError> for AEKind {
    fn into(self) -> AstError {
        AstError {
            kind: self,
            token: None,
        }
    }
}

pub const ASSIGN_PRECEDENCE: i64 = 15;

pub fn precedence(op: &str) -> i64 {
    match op {
        "." => 2,
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
        "test_code.pmh".to_string(),
        crate::testing::TEST_CODE.to_string(),
    );
    let mut parser = AstParser::new(lexer);

    let ast = parser.parse().unwrap();

    println!("{}", ast);
}
