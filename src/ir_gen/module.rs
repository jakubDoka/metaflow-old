use super::*;

#[derive(Debug, Clone)]
pub struct Mod {
    name: String,
    dependency: Vec<Cell<Mod>>,
    types: Vec<Cell<Datatype>>,
    functions: Vec<Cell<Fun>>,
}

impl Mod {
    pub fn new(name: String) -> Self {
        Self {
            name,
            dependency: vec![],
            types: vec![],
            functions: vec![],
        }
    }

    pub fn find_datatype(&self, name: &str) -> Option<Cell<Datatype>> {
        self.types
            .binary_search_by(|d| name.cmp(&d.name()))
            .ok()
            .map(|i| self.types[i].clone())
            .or_else(|| {
                for dep in self.dependency.iter().rev() {
                    if let Some(d) = dep.find_datatype(name) {
                        return Some(d);
                    }
                }
                None
            })
    }

    pub fn add_datatype(&mut self, datatype: Cell<Datatype>) -> Result<()> {
        match self
            .types
            .binary_search_by(|d| datatype.name().cmp(&d.name()))
        {
            Ok(i) => Err(IGEKind::DuplicateType(datatype.clone(), self.types[i].clone()).into()),
            Err(i) => {
                self.types.insert(i, datatype);
                Ok(())
            }
        }
    }

    pub fn has_function(&self, name: &str) -> bool {
        self.functions
            .binary_search_by(|d| name.cmp(d.name()))
            .is_ok()
    }

    pub fn add_function(&mut self, fun: Cell<Fun>) -> Result<()> {
        match self
            .functions
            .binary_search_by(|d| fun.name().cmp(d.name()))
        {
            Ok(i) => Err(IGEKind::DuplicateFunction(fun.clone(), self.functions[i].clone()).into()),
            Err(i) => {
                self.functions.insert(i, fun);
                Ok(())
            }
        }
    }

    pub fn find_function(&self, name: &Token) -> Option<Cell<Fun>> {
        self.functions
            .binary_search_by(|f| name.value().cmp(&f.name()))
            .ok()
            .map(|i| self.functions[i].clone())
            .or_else(|| {
                for dep in self.dependency.iter().rev() {
                    if let Some(d) = dep.find_function(name) {
                        return Some(d);
                    }
                }
                None
            })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn types(&self) -> &[Cell<Datatype>] {
        &self.types
    }

    pub fn types_mut(&mut self) -> &mut Vec<Cell<Datatype>> {
        &mut self.types
    }

    pub fn dependency(&self) -> &[Cell<Mod>] {
        &self.dependency
    }

    pub fn dependency_mut(&mut self) -> &mut Vec<Cell<Mod>> {
        &mut self.dependency
    }

    pub fn functions(&self) -> &[Cell<Fun>] {
        &self.functions
    }
}

macro_rules! builtin_repo {
    (types [$($name:ident: $lit:ident $bits:expr,)*]) => {
        pub struct BuiltinRepo {
            $($name: Cell<Datatype>,)*
        }

        impl BuiltinRepo {
            pub fn new() -> Self {
                Self {
                    $(
                        $name: Cell::new(Datatype::with_size(
                            stringify!($name).to_string(),
                            DKind::Builtin($lit),
                            $bits
                        )),
                    )*
                }
            }

            $(
                pub fn $name(&self) -> &Cell<Datatype> {
                    &self.$name
                }
            )*

            pub fn to_module(&self) -> Cell<Mod> {
                let mut module = Mod::new("builtin".to_string());
                $(
                    module.add_datatype(self.$name.clone()).unwrap();
                )*
                Cell::new(module)
            }
        }
    }
}

builtin_repo!(
    types [
        i8: I8 1,
        i16: I16 2,
        i32: I32 4,
        i64: I64 8,
        u8: I8 1,
        u16: I16 2,
        u32: I32 4,
        u64: I64 8,
        f32: F32 4,
        f64: F64 8,
        bool: B1 1,
    ]
);
