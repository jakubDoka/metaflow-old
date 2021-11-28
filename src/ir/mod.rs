pub mod attributes;
pub mod functions;
pub mod globals;
pub mod module_tree;
pub mod types;

use std::ops::{Index, IndexMut};

use cranelift_codegen::{ir, ir::types::*, isa::TargetIsa, settings};

use crate::{
    ast::{Ast, Vis},
    lexer::{self, Spam, Token},
    util::{
        sdbm::{SdbmHashState, ID},
        sym_table::{SymID, SymTable, SymVec},
    },
};

use self::attributes::Attributes;

pub type CrValue = ir::Value;
pub type LTKind = lexer::TKind;
pub type CrType = ir::Type;

pub struct Program {
    pub builtin: Module,
    pub builtin_repo: BuiltinRepo,
    pub isa: Box<dyn TargetIsa>,
    pub types: SymTable<Type, TypeEnt>,
    pub functions: SymTable<Fun, FunEnt>,
    pub generic_functions: SymTable<Fun, Vec<FunEnt>>,
    pub modules: SymTable<Module, ModuleEnt>,
}

impl Program {
    pub fn walk_accessible_scopes<T, F: FnMut(ID, Module) -> Option<T>>(
        &self,
        module: Module,
        mut fun: F,
    ) -> Option<T> {
        if let Some(t) = fun(self.modules[module].id, module) {
            return Some(t);
        }

        self.modules[module]
            .dependency
            .iter()
            .rev()
            .map(|&(_, id)| fun(self.modules[id].id, id))
            .find(|t| t.is_some())
            .flatten()
    }

    pub fn build_builtin(&mut self) {
        let module_id = ID::new().add("builtin");

        let module = ModuleEnt {
            name: module_id,
            id: module_id,
            absolute_path: "".to_string(),
            dependency: Vec::new(),
            dependant: Vec::new(),
            ast: Ast::none(),
            attributes: Attributes::default(),
            is_external: true,
        };

        let (_, module) = self.modules.insert(module_id, module);
        self.builtin = module;

        self.builtin_repo = BuiltinRepo::new(self);

        let builtin_operations = [
            (
                "+ - * / == != >= <= > < ^ | & >> <<",
                &[
                    self.builtin_repo.i8,
                    self.builtin_repo.i16,
                    self.builtin_repo.i32,
                    self.builtin_repo.i64,
                    self.builtin_repo.u8,
                    self.builtin_repo.u16,
                    self.builtin_repo.u32,
                    self.builtin_repo.u64,
                ][..],
            ),
            (
                "+ - * / == != >= <= > <",
                &[self.builtin_repo.f32, self.builtin_repo.f64][..],
            ),
            ("&& || ^^", &[self.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_operations.iter() {
            for operation in operators.split(' ') {
                for &datatype in types.iter() {
                    let datatype_id = self.types.direct_to_id(datatype);
                    let return_type = if matches!(operation, "==" | "!=" | ">" | "<" | ">=" | "<=")
                    {
                        self.builtin_repo.bool
                    } else {
                        datatype
                    };
                    let binary_op = FunEnt {
                        visibility: Vis::Public,
                        name: ID::new()
                            .add(operation)
                            .combine(datatype_id)
                            .combine(datatype_id)
                            .combine(module_id),
                        module,
                        kind: FKind::Builtin(FunSignature {
                            args: vec![ValueEnt::temp(datatype), ValueEnt::temp(datatype)],
                            return_type: Some(return_type),
                        }),

                        token_hint: Default::default(),
                        body: Default::default(),
                        ast: AstRef::new(usize::MAX),
                        attribute_id: 0,
                    };
                    self.functions.insert(binary_op.name, binary_op);
                }
            }
        }
    }
}

crate::sym_id!(AstRef);

macro_rules! define_repo {
    ($($name:ident, $repr:ident, $size:expr),+,) => {
        #[derive(Clone, Debug)]
        pub struct BuiltinRepo {
            $(pub $name: Type,)+
        }

        impl BuiltinRepo {
            pub fn new(program: &mut Program) -> Self {


                let builtin_id = ID::new().add("builtin");

                $(
                    let id = ID::new().add(stringify!($name)).combine(builtin_id);
                    let type_ent = TypeEnt {
                        visibility: Vis::Public,
                        kind: TKind::Builtin($repr),
                        name: id,
                        size: $size,
                        align: $size.min(8),
                        module: program.builtin,

                        token_hint: Token::builtin(stringify!($name)),

                        params: Vec::new(),
                        ast: Ast::none(),
                        attribute_id: 0,
                    };
                    let (_, $name) = program.types.insert(id, type_ent);
                )+

                Self {
                    $($name),+
                }
            }
        }

    };
}

define_repo!(
    i8, I8, 1, i16, I16, 2, i32, I32, 4, i64, I64, 8, u8, I8, 1, u16, I16, 2, u32, I32, 4, u64,
    I64, 8, f32, F32, 4, f64, F64, 8, bool, B1, 1, auto, INVALID, 0,
);

impl Index<Type> for Program {
    type Output = TypeEnt;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index]
    }
}

impl IndexMut<Type> for Program {
    fn index_mut(&mut self, index: Type) -> &mut Self::Output {
        &mut self.types[index]
    }
}

impl Index<Fun> for Program {
    type Output = FunEnt;

    fn index(&self, index: Fun) -> &Self::Output {
        &self.functions[index]
    }
}

impl IndexMut<Fun> for Program {
    fn index_mut(&mut self, index: Fun) -> &mut Self::Output {
        &mut self.functions[index]
    }
}

impl Index<Module> for Program {
    type Output = ModuleEnt;

    fn index(&self, index: Module) -> &Self::Output {
        &self.modules[index]
    }
}

impl IndexMut<Module> for Program {
    fn index_mut(&mut self, index: Module) -> &mut Self::Output {
        &mut self.modules[index]
    }
}

impl Default for Program {
    fn default() -> Self {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder().unwrap().finish(flags);
        let mut program = Program {
            isa,
            builtin: Module::new(0),
            builtin_repo: unsafe { std::mem::zeroed() },
            types: SymTable::new(),
            functions: SymTable::new(),
            modules: SymTable::new(),
            generic_functions: SymTable::new(),
        };

        program.build_builtin();

        program
    }
}

crate::sym_id!(Module);

#[derive(Clone, Debug, Default)]
pub struct ModuleEnt {
    pub name: ID,
    pub id: ID,
    pub absolute_path: String,
    pub dependency: Vec<(ID, Module)>,
    pub dependant: Vec<Module>,

    pub ast: Ast,
    pub attributes: Attributes,

    pub is_external: bool,
}

crate::sym_id!(Fun);

#[derive(Debug, Clone)]
pub struct FunEnt {
    pub visibility: Vis,
    pub name: ID,
    pub module: Module,
    pub token_hint: Token,
    pub kind: FKind,
    pub body: FunBody,
    pub ast: AstRef,
    pub attribute_id: usize,
}

impl FunEnt {
    pub fn signature(&self) -> &FunSignature {
        match &self.kind {
            FKind::Normal(sig) => sig,
            FKind::Builtin(sig) => sig,
            _ => panic!("cannot access signature on {:?}", self.kind),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct FunBody {
    pub values: SymVec<Value, ValueEnt>,
    pub instructions: SymVec<Inst, InstEnt>,
    pub blocks: SymVec<Block, BlockEnt>,
}

impl FunBody {
    pub fn clear(&mut self) {
        self.values.clear();
        self.instructions.clear();
        self.blocks.clear();
    }
}

crate::sym_id!(Inst);

#[derive(Debug, Default, Clone)]
pub struct InstEnt {
    kind: IKind,
    value: Option<Value>,
    token_hint: Token,
    unresolved: usize,
}

impl InstEnt {
    pub fn new(kind: IKind, value: Option<Value>, token_hint: &Token) -> Self {
        Self {
            kind,
            value,
            token_hint: token_hint.clone(),
            unresolved: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub enum IKind {
    NoOp,
    Call(Fun, Vec<Value>),
    UnresolvedCall(ID, Vec<Value>),
    VarDecl(Value),
    ZeroValue,
    Literal(LTKind),
    Return(Option<Value>),
    Assign(Value),
    Jump(Block, Vec<Value>),
    JumpIfTrue(Value, Block, Vec<Value>),
}

impl IKind {
    pub fn is_closing(&self) -> bool {
        matches!(self, IKind::Jump(..) | IKind::Return(..))
    }
}

impl Default for IKind {
    fn default() -> Self {
        IKind::NoOp
    }
}

crate::sym_id!(Block);

#[derive(Debug, Default, Clone)]
pub struct BlockEnt {
    pub args: Vec<Value>,
    pub first_instruction: Option<Inst>,
    pub last_instruction: Option<Inst>,
}

#[derive(Debug, Clone)]
pub enum FKind {
    Unresolved,
    Builtin(FunSignature),
    Generic(GenericSignature),
    Normal(FunSignature),
}

#[derive(Debug, Clone)]
pub struct GenericSignature {
    pub params: Vec<ID>,
    pub elements: Vec<GenericElement>,
    pub return_index: usize,
    pub arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericElement {
    ScopeStart,
    ScopeEnd,
    Element(ID, Option<Type>),
    Parameter(usize),
    NextArgument(usize, usize),
    NextReturn(bool),
}

impl GenericElement {
    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (GenericElement::Element(id1, _), GenericElement::Element(id2, _)) => id1 == id2,
            _ => self == other,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct FunSignature {
    pub args: Vec<ValueEnt>,
    pub return_type: Option<Type>,
}

crate::sym_id!(GlobalValue);

#[derive(Debug, Clone)]
pub struct GlobalValueEnt {
    pub val: Value,
    pub ast: Ast,
}

crate::sym_id!(Value);

#[derive(Debug, Clone)]
pub struct ValueEnt {
    pub name: ID,
    pub datatype: Type,
    pub type_dependency: Option<TypeDep>,
    pub value: Option<CrValue>,
    pub mutable: bool,
    pub on_stack: bool,
}

impl ValueEnt {
    pub fn temp(datatype: Type) -> Self {
        Self {
            datatype,
            name: ID::new(),
            type_dependency: None,
            value: None,
            mutable: false,
            on_stack: false,
        }
    }
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Unresolved
    }
}

crate::sym_id!(TypeDep);

crate::sym_id!(Type);

#[derive(Clone, Debug, PartialEq)]
pub struct TypeEnt {
    pub visibility: Vis,
    pub params: Vec<Type>,
    pub kind: TKind,
    pub size: u32,
    pub align: u32,
    pub attribute_id: usize,
    pub ast: Ast,
    pub module: Module,
    pub name: ID,
    pub token_hint: Token,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TKind {
    Unresolved,
    Builtin(CrType),
    Generic,
    Pointer(Type),
    Structure(Structure),
}

impl Default for TKind {
    fn default() -> Self {
        TKind::Unresolved
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
    pub visibility: Vis,
    pub embedded: bool,
    pub offset: u32,
    pub name: Spam,
    pub datatype: Type,
}

pub fn test() {
    module_tree::test();
    types::test();
    functions::test();
}
