use super::module::*;
use super::*;

pub struct Context {
    modules: Vec<Cell<Mod>>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
        }
    }

    pub fn add_module(&mut self, module: Cell<Mod>) -> Result<()> {
        match self
            .modules
            .binary_search_by(|d| module.name().cmp(d.name()))
        {
            Ok(i) => Err(IGEKind::DuplicateModule(module.clone(), self.modules[i].clone()).into()),
            Err(i) => {
                self.modules.insert(i, module);
                Ok(())
            }
        }
    }

    pub fn find_module(&self, name: Token) -> Result<Cell<Mod>> {
        match self
            .modules
            .binary_search_by(|d| name.value().cmp(&d.name()))
        {
            Ok(i) => Ok(self.modules[i].clone()),
            Err(_) => Err(IrGenError::new(IGEKind::ModuleNotFound, name.clone())),
        }
    }

    pub fn modules(&self) -> &[Cell<Mod>] {
        &self.modules
    }
}
