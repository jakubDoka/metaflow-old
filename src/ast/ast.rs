use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
};

use crate::lexer::*;

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
        std::iter::repeat(' ')
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
    Call,
    Index,

    StructDeclaration(Vis),
    StructField(bool),

    Attribute,
    AttributeElement,
    AttributeAssign,

    VarStatement(bool),
    VarAssign,

    ReturnStatement,

    BinaryOperation,
    UnaryOperation,
    IfExpression,
    DotExpr,

    Loop,
    Break,
    Continue,

    Group,

    Identifier,
    Instantiation,
    Literal,

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
    Private,
    FilePrivate,
}

impl Default for Vis {
    fn default() -> Self {
        Vis::Public
    }
}
