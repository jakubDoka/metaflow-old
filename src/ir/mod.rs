pub mod functions;
pub mod module_tree;
pub mod types;
pub mod attributes;
pub mod globals;

use cranelift_codegen::{isa::TargetIsa, settings};

use crate::{
    ast::{Ast, Visibility},
    lexer::{Spam, Token},
    util::{
        sdbm::ID,
        sym_table::{SymID, SymTable},
    },
};

use self::attributes::Attributes;

pub struct Program {
    pub isa: Box<dyn TargetIsa>,
    pub types: SymTable<Datatype, DatatypeEntity>,
    pub functions: SymTable<Function, FunctionEntity>,
    pub generic_functions: SymTable<Function, Vec<FunctionEntity>>,
    pub modules: SymTable<Mod, ModEntity>,
}

impl Default for Program {
    fn default() -> Self {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder().unwrap().finish(flags);
        Program {
            isa,
            types: SymTable::new(),
            functions: SymTable::new(),
            modules: SymTable::new(),
            generic_functions: SymTable::new(),
        }
    }
}

crate::sym_id!(Mod);

#[derive(Clone, Debug, Default)]
pub struct ModEntity {
    pub name: ID,
    pub id: ID,
    pub absolute_path: String,
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,

    pub ast: Ast,
    pub attributes: Attributes,

    pub is_external: bool,
}

crate::sym_id!(Function);

#[derive(Debug, Default, Clone)]
pub struct FunctionEntity {
    pub visibility: Visibility,
    pub name: ID,
    pub module: Mod,
    pub hint_token: Token,
    pub kind: FKind,
    pub ast: Ast,
}

#[derive(Debug, Clone)]
pub enum FKind {
    Unresolved,
    Generic,
    Normal(NormalFunction),
}

#[derive(Debug, Clone)]
pub struct NormalFunction {
    pub params: Vec<Val>,
    pub ret: Option<Datatype>,
}

crate::sym_id!(GlobalVal);

#[derive(Debug, Clone)]
pub struct GlobalValEntity {
    pub val: Val,
    pub ast: Ast,
}

#[derive(Debug, Clone)]
pub struct Val {
    pub name: ID,
    pub datatype: Datatype,
    pub mutable: bool,
    pub on_stack: bool,
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Unresolved
    }
}

crate::sym_id!(Datatype);

#[derive(Clone, Debug, PartialEq, Default)]
pub struct DatatypeEntity {
    pub visibility: Visibility,
    pub kind: DKind,
    pub name: ID,
    pub size: u32,
    pub ast: Ast,
    pub module: Mod,
    pub token_hint: Token,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DKind {
    Unresolved,
    Builtin,
    Generic,
    Pointer(Datatype),
    Structure(Structure),
}

impl Default for DKind {
    fn default() -> Self {
        DKind::Unresolved
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Structure {
    pub kind: SKind,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SKind {
    Struct,
    Union,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub visibility: Visibility,
    pub embedded: bool,
    pub offset: u32,
    pub name: Spam,
    pub datatype: Datatype,
}

pub fn test() {
    module_tree::test();
    types::test();
}
