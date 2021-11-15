use super::*;

#[derive(Debug, Clone)]
pub struct Var {
    name: StrRef,
    value: Val,
}

impl Var {
    pub fn new(name: StrRef, value: Val) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> &StrRef {
        &self.name
    }

    pub fn value(&self) -> &Val {
        &self.value
    }

    pub fn set_kind(&mut self, kind: VKind) {
        self.value.set_kind(kind);
    }
}