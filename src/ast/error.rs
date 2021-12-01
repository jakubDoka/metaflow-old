use std::fmt::Display;

use super::*;

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
        write!(f, "{}", TokenView::new(&self.token))?;
        match &self.kind {
            AEKind::UnexpectedToken(expected) => write!(f, "{}\n", expected),
            AEKind::UnexpectedEof => write!(f, "unexpected end of file\n"),
        }
    }
}


#[derive(Debug, Clone)]
pub enum AEKind {
    UnexpectedToken(String),
    UnexpectedEof,
}

impl Into<AstError> for AEKind {
    fn into(self) -> AstError {
        AstError {
            kind: self,
            token: Token::default(),
        }
    }
}
