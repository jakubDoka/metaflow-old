use super::*;

#[derive(Debug, Clone)]
pub struct Fun {
    id: FuncId,
    name: Spam,
    params: Vec<Var>,
    return_type: Option<Cell<Datatype>>,
    inline_level: InlineLevel,
    signature: Option<Signature>,
    body: Ast,
}

impl Fun {
    pub fn new(
        id: FuncId,
        name: Spam,
        params: Vec<Var>,
        return_type: Option<Cell<Datatype>>,
        inline_level: InlineLevel,
        signature: Option<Signature>,
        body: Ast,
    ) -> Self {
        Self {
            id,
            name,
            params,
            return_type,
            inline_level,
            signature,
            body,
        }
    }

    pub fn id(&self) -> FuncId {
        self.id
    }

    pub fn name(&self) -> &Spam {
        &self.name
    }

    pub fn params(&self) -> &Vec<Var> {
        &self.params
    }

    pub fn params_mut(&mut self) -> &mut Vec<Var> {
        &mut self.params
    }

    pub fn return_type(&self) -> Option<&Cell<Datatype>> {
        self.return_type.as_ref()
    }

    pub fn inline_level(&self) -> InlineLevel {
        self.inline_level.clone()
    }

    pub fn signature(&self) -> &Option<Signature> {
        &self.signature
    }

    pub fn signature_mut(&mut self) -> &mut Option<Signature> {
        &mut self.signature
    }

    pub fn body(&self) -> &Ast {
        &self.body
    }
}

#[derive(Debug, Clone)]
pub enum InlineLevel {
    Never,
    Auto,
    Always,
}

impl FromStr for InlineLevel {
    type Err = ();
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "never" => Ok(InlineLevel::Never),
            "auto" => Ok(InlineLevel::Auto),
            "always" => Ok(InlineLevel::Always),
            _ => Err(()),
        }
    }
}
