/*pub mod attributes;
pub mod functions;
pub mod globals;
pub mod module_tree;
pub mod types;

use std::ops::{Index, IndexMut};

use cranelift_codegen::{
    ir,
    ir::{types::*, Signature, StackSlot},
    isa::TargetIsa,
    settings,
};
use cranelift_frontend::Variable;
use cranelift_module::{FuncId, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::{
    ast::{Ast, Vis},
    lexer::{self, Token},
    util::{
        sdbm::{SdbmHashState, ID},
        storage::{LinkedList, List, SymID, Table},
    },
};

use self::attributes::Attributes;

pub type LTKind = lexer::TKind;

pub type CrValue = ir::Value;
pub type CrType = ir::Type;
pub type CrBlock = ir::Block;
pub type CrVar = Variable;

pub const TYPE_SALT: ID = ID(0xFACD184950);
pub const FUN_SALT: ID = ID(0x7485978ADC);
pub const MOD_SALT: ID = ID(0x85403875FF);

pub struct Program {
    pub builtin: Mod,
    pub builtin_repo: BuiltinRepo,
    pub object_module: ObjectModule,
    pub types: Table<Type, TypeEnt>,
    pub functions: Table<Fun, FunEnt>,
    pub generic_functions: Table<Fun, Vec<FunEnt>>,
    pub modules: Table<Mod, ModuleEnt>,
}

impl Program {
    pub fn new(object_module: ObjectModule) -> Self {
        let mut program = Program {
            object_module,
            builtin: Mod::new(0),
            builtin_repo: unsafe { std::mem::zeroed() },
            types: Table::new(),
            functions: Table::new(),
            modules: Table::new(),
            generic_functions: Table::new(),
        };

        program.build_builtin();

        program
    }

    pub fn attr_enabled(&self, fun: Fun, name: &str) -> bool {
        self.get_attr(fun, name).is_some()
    }

    pub fn get_attr(&self, fun: Fun, name: &str) -> Option<&Ast> {
        let module = self.functions[fun].module;
        let attr_id = self.functions[fun].attribute_id;
        self.modules[module].attributes.get_attr(attr_id, name)
    }

    pub fn walk_accessible_scopes<T, F: FnMut(ID, Mod) -> Option<T>>(
        &self,
        module: Mod,
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
        let module_id = MOD_SALT.add("builtin");

        let module = ModuleEnt {
            name: module_id,
            id: module_id,
            absolute_path: "".to_string(),
            dependency: vec![],
            dependant: vec![],
            ast: Ast::none(),
            attributes: Attributes::default(),
            is_external: true,
        };

        let (_, module) = self.modules.insert(module_id, module);
        self.builtin = module;

        self.builtin_repo = BuiltinRepo::new(self);

        let types = self.builtin_repo.type_list();

        for i in types {
            for j in types {
                if i == self.builtin_repo.auto || j == self.builtin_repo.auto {
                    continue;
                }
                let datatype_id = self.types.direct_to_id(j);
                let name = self.types[i].debug_name;
                let unary_op = FunEnt {
                    visibility: Vis::Public,
                    name: FUN_SALT.add(name).combine(datatype_id),
                    module,
                    kind: FKind::Builtin(FunSignature {
                        args: vec![ValueEnt::temp(j)],
                        return_type: Some(i),
                        struct_return: false,
                    }),
                    debug_name: name,
                    import: false,
                    token_hint: Default::default(),
                    body: Default::default(),
                    ast: AstRef::new(usize::MAX),
                    attribute_id: 0,
                    final_signature: None,
                    object_id: None,
                };
                assert!(self
                    .functions
                    .insert(unary_op.name.combine(module_id), unary_op)
                    .0
                    .is_none());
            }
        }

        let integer_types = &[
            self.builtin_repo.i8,
            self.builtin_repo.i16,
            self.builtin_repo.i32,
            self.builtin_repo.i64,
            self.builtin_repo.u8,
            self.builtin_repo.u16,
            self.builtin_repo.u32,
            self.builtin_repo.u64,
            self.builtin_repo.int,
            self.builtin_repo.uint,
        ][..];

        let builtin_unary_ops = [
            ("~ + ++ --", integer_types),
            (
                "- abs",
                &[
                    self.builtin_repo.i8,
                    self.builtin_repo.i16,
                    self.builtin_repo.i32,
                    self.builtin_repo.i64,
                    self.builtin_repo.f32,
                    self.builtin_repo.f64,
                    self.builtin_repo.int,
                ][..],
            ),
            ("!", &[self.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_unary_ops.iter() {
            for op in operators.split(' ') {
                for &datatype in types.iter() {
                    let datatype_id = self.types.direct_to_id(datatype);
                    let unary_op = FunEnt {
                        visibility: Vis::Public,
                        name: FUN_SALT.add(op).combine(datatype_id),
                        module,
                        kind: FKind::Builtin(FunSignature {
                            args: vec![ValueEnt::temp(datatype)],
                            return_type: Some(datatype),
                            struct_return: false,
                        }),
                        debug_name: op,
                        import: false,
                        token_hint: Default::default(),
                        body: Default::default(),
                        ast: AstRef::new(usize::MAX),
                        attribute_id: 0,
                        final_signature: None,
                        object_id: None,
                    };
                    assert!(self
                        .functions
                        .insert(unary_op.name.combine(module_id), unary_op)
                        .0
                        .is_none());
                }
            }
        }

        let builtin_bin_ops = [
            ("+ - * / == != >= <= > < ^ | & >> <<", integer_types),
            (
                "+ - * / == != >= <= > <",
                &[self.builtin_repo.f32, self.builtin_repo.f64][..],
            ),
            ("&& || ^ | &", &[self.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_bin_ops.iter() {
            for op in operators.split(' ') {
                for &datatype in types.iter() {
                    let datatype_id = self.types.direct_to_id(datatype);
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        self.builtin_repo.bool
                    } else {
                        datatype
                    };
                    let binary_op = FunEnt {
                        visibility: Vis::Public,
                        name: FUN_SALT.add(op).combine(datatype_id).combine(datatype_id),
                        module,
                        kind: FKind::Builtin(FunSignature {
                            args: vec![ValueEnt::temp(datatype), ValueEnt::temp(datatype)],
                            return_type: Some(return_type),
                            struct_return: false,
                        }),
                        debug_name: op,
                        import: false,
                        token_hint: Default::default(),
                        body: Default::default(),
                        ast: AstRef::new(usize::MAX),
                        attribute_id: 0,
                        final_signature: None,
                        object_id: None,
                    };
                    assert!(self
                        .functions
                        .insert(binary_op.name.combine(module_id), binary_op)
                        .0
                        .is_none());
                }
            }
        }
    }

    pub fn isa(&self) -> &dyn TargetIsa {
        self.object_module.isa()
    }
}

crate::sym_id!(AstRef);

macro_rules! define_repo {
    (
        $($name:ident, $repr:ident, $size:expr);+,
        $($pointer_type:ident)*
    ) => {
        #[derive(Clone, Debug)]
        pub struct BuiltinRepo {
            $(pub $name: Type,)+
            $(pub $pointer_type: Type,)+
        }

        impl BuiltinRepo {
            pub fn new(program: &mut Program) -> Self {


                let builtin_id = MOD_SALT.add("builtin");

                $(
                    let name = TYPE_SALT.add(stringify!($name));
                    let type_ent = TypeEnt {
                        visibility: Vis::Public,
                        kind: TKind::Builtin($repr),
                        name,
                        size: $size,
                        align: $size.min(8),
                        module: program.builtin,

                        token_hint: Token::builtin(stringify!($name)),

                        debug_name: stringify!($name),
                        params: vec![],
                        ast: Ast::none(),
                        attribute_id: 0,
                    };
                    let (_, $name) = program.types.insert(name.combine(builtin_id), type_ent);
                )+

                $(
                    let name = TYPE_SALT.add(stringify!($pointer_type));
                    let size = program.isa().pointer_bytes() as u32;
                    let type_ent = TypeEnt {
                        visibility: Vis::Public,
                        kind: TKind::Builtin(program.isa().pointer_type()),
                        name,
                        size,
                        align: size,
                        module: program.builtin,

                        token_hint: Token::builtin(stringify!($pointer_type)),

                        debug_name: stringify!($pointer_type),
                        params: vec![],
                        ast: Ast::none(),
                        attribute_id: 0,
                    };
                    let (_, $pointer_type) = program.types.insert(name.combine(builtin_id), type_ent);
                )+

                Self {
                    $($name,)+
                    $($pointer_type,)+
                }
            }

            pub fn type_list(&self) -> [Type; 14] {
                [
                    $(self.$name,)+
                    $(self.$pointer_type,)+
                ]
            }
        }
    };
}

define_repo!(
    i8, I8, 1;
    i16, I16, 2;
    i32, I32, 4;
    i64, I64, 8;
    u8, I8, 1;
    u16, I16, 2;
    u32, I32, 4;
    u64, I64, 8;
    f32, F32, 4;
    f64, F64, 8;
    bool, B1, 1;
    auto, INVALID, 0,
    int uint
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

impl Index<Mod> for Program {
    type Output = ModuleEnt;

    fn index(&self, index: Mod) -> &Self::Output {
        &self.modules[index]
    }
}

impl IndexMut<Mod> for Program {
    fn index_mut(&mut self, index: Mod) -> &mut Self::Output {
        &mut self.modules[index]
    }
}

impl Default for Program {
    fn default() -> Self {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder().unwrap().finish(flags);
        let builder =
            ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();
        let mut program = Program {
            object_module: ObjectModule::new(builder),
            builtin: Mod::new(0),
            builtin_repo: unsafe { std::mem::zeroed() },
            types: Table::new(),
            functions: Table::new(),
            modules: Table::new(),
            generic_functions: Table::new(),
        };

        program.build_builtin();

        program
    }
}

crate::sym_id!(Mod);

#[derive(Clone, Debug, Default)]
pub struct ModuleEnt {
    pub name: ID,
    pub id: ID,
    pub absolute_path: String,
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,

    pub ast: Ast,
    pub attributes: Attributes,

    pub is_external: bool,
}

crate::sym_id!(Fun);

#[derive(Debug, Clone)]
pub struct FunEnt {
    pub visibility: Vis,
    pub name: ID,
    pub module: Mod,
    pub token_hint: Token,
    pub kind: FKind,
    pub body: FunBody,
    pub ast: AstRef,
    pub debug_name: &'static str,
    pub import: bool,
    pub final_signature: Option<Signature>,
    pub object_id: Option<FuncId>,
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
    pub values: List<Value, ValueEnt>,
    pub insts: LinkedList<Inst, InstEnt>,
}

impl FunBody {
    pub fn clear(&mut self) {
        self.values.clear();
        self.insts.clear();
    }
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
    Pointer(bool),
    Element(Type, Option<Type>),
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
    pub struct_return: bool,
}

crate::sym_id!(Inst);

#[derive(Debug, Default, Clone)]
pub struct InstEnt {
    pub kind: IKind,
    pub value: Option<Value>,
    pub token_hint: Token,
    pub unresolved: usize,
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
    UnresolvedCall(ID, &'static str, bool, Vec<Value>),
    UnresolvedDot(Value, ID),
    VarDecl(Value),
    ZeroValue,
    Lit(LTKind),
    Return(Option<Value>),
    Assign(Value),
    Block(Block),
    BlockEnd(Inst),
    Jump(Inst, Vec<Value>),
    JumpIfTrue(Value, Inst, Vec<Value>),
    Offset(Value),
    Deref(Value),
    Ref(Value),
    Cast(Value),
}

impl IKind {
    pub fn is_closing(&self) -> bool {
        matches!(self, IKind::Jump(..) | IKind::Return(..))
    }

    pub fn block(&self) -> &Block {
        match self {
            IKind::Block(block) => block,
            _ => panic!("cannot access block on {:?}", self),
        }
    }

    pub fn block_mut(&mut self) -> &mut Block {
        match self {
            IKind::Block(block) => block,
            _ => panic!("cannot access block on {:?}", self),
        }
    }
}

impl Default for IKind {
    fn default() -> Self {
        IKind::NoOp
    }
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub block: Option<CrBlock>,
    pub args: Vec<Value>,
    pub end: Option<Inst>,
}

#[derive(Debug, Clone)]
pub struct Loop {
    name: ID,
    start_block: Inst,
    end_block: Inst,
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
    pub inst: Option<Inst>,
    pub type_dependency: Option<TypeDep>,
    pub value: FinalValue,
    pub offset: u32,
    pub mutable: bool,
    pub on_stack: bool,
}

impl ValueEnt {
    pub fn new(name: ID, datatype: Type, mutable: bool) -> Self {
        Self {
            name,
            datatype,
            mutable,

            type_dependency: None,
            inst: None,
            value: FinalValue::None,
            offset: 0,
            on_stack: false,
        }
    }

    pub fn temp(datatype: Type) -> Self {
        Self {
            name: ID(0),
            datatype,
            inst: None,
            type_dependency: None,
            value: FinalValue::None,
            offset: 0,
            mutable: false,
            on_stack: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalValue {
    None,
    Zero,
    Value(CrValue),
    Pointer(CrValue),
    Var(CrVar),
    StackSlot(StackSlot),
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
    pub module: Mod,
    pub name: ID,
    pub debug_name: &'static str,
    pub token_hint: Token,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TKind {
    Unresolved,
    Builtin(CrType),
    Generic,
    Pointer(Type, bool),
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
    pub name: ID,
    pub datatype: Type,
    pub token_hint: Token,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BTKind {
    Int,
    Uint,
    Float(u8),
    Bool,
}

impl BTKind {
    pub fn of(tp: Type) -> Self {
        match SymID::raw(&tp) {
            0..=3 | 12 => Self::Int,
            4..=7 | 13 => Self::Uint,
            8 => Self::Float(32),
            9 => Self::Float(64),
            10 => Self::Bool,
            _ => panic!("cannot get builtin type of {:?}", tp),
        }
    }
}

pub fn test() {
    module_tree::test();
    types::test();
    functions::test();
}
*/
