use super::*;

#[derive(Debug, Clone)]
pub struct Var {
    name: Spam,
    value: Val,
}

impl Var {
    pub fn new(name: Spam, value: Val) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> &Spam {
        &self.name
    }

    pub fn value(&self) -> &Val {
        &self.value
    }

    pub fn set_kind(&mut self, kind: VKind) {
        self.value.set_kind(kind);
    }
}
