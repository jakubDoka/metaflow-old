use super::*;

#[derive(Debug)]
pub struct AstError {
    kind: AEKind,
    token: Option<Token>,
}

impl AstError {
    pub fn new(kind: AEKind, token: Token) -> AstError {
        AstError {
            kind,
            token: Some(token),
        }
    }

    pub fn kind(&self) -> &AEKind {
        &self.kind
    }

    pub fn token(&self) -> &Option<Token> {
        &self.token
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
            token: None,
        }
    }
}
