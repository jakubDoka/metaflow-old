use super::*;

#[derive(Debug)]
pub struct IrGenError {
    kind: IGEKind,
    token: Option<Token>,
}

impl IrGenError {
    pub fn new(kind: IGEKind, token: Token) -> Self {
        Self {
            kind,
            token: Some(token),
        }
    }

    pub fn kind(&self) -> &IGEKind {
        &self.kind
    }

    pub fn take_kind(&mut self) -> IGEKind {
        std::mem::replace(&mut self.kind, IGEKind::None)
    }

    pub fn token(&self) -> &Option<Token> {
        &self.token
    }
}

impl Into<IrGenError> for AstError {
    fn into(self) -> IrGenError {
        IrGenError {
            kind: IGEKind::AstError(self.kind().clone()),
            token: self.token().clone(),
        }
    }
}

#[derive(Debug)]
pub enum IGEKind {
    TypeMismatch(Cell<Datatype>, Cell<Datatype>),
    DuplicateType(Cell<Datatype>, Cell<Datatype>),
    DuplicateModule(Cell<Mod>, Cell<Mod>),
    DuplicateFunction(Cell<Fun>, Cell<Fun>),
    MissingAttrArgument(usize, usize),
    InvalidAmountOfArguments(usize, usize),
    InvalidInlineLevel,
    InvalidLinkage,
    InvalidCallConv,
    InvalidFieldAccess,
    FieldNotFound,
    AssignToImmutable,
    ExpectedValue,
    MissingValueInElseBranch,
    UnexpectedValueInThenBranch,
    UnexpectedValue,
    LoopHeaderNotFound,
    MissingElseBranch,
    FunctionNotFound,
    VariableNotFound,
    TypeNotFound,
    ModuleNotFound,
    CannotOpenFile(std::io::Error),
    AstError(AEKind),
    None,
}

impl Into<IrGenError> for IGEKind {
    fn into(self) -> IrGenError {
        IrGenError {
            kind: self,
            token: None,
        }
    }
}