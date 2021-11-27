use super::*;

#[derive(Debug)]
pub struct AstError {
    pub kind: AEKind,
    pub token: Token,
}

impl AstError {
    pub fn new(kind: AEKind, token: Token) -> AstError {
        AstError { kind, token: token }
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
