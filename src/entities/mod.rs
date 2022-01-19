use crate::{
    lexer::{TKind as LTKind, Token, Span},
    util::{sdbm::ID, Size}, ast::Vis,
};
use cranelift::{entity::packed_option::ReservedValue, codegen::{isa::{CallConv as CrCallConv, TargetIsa}}};
use cranelift::{
    codegen::{
        ir::{Block, GlobalValue, Inst, Value, types::*},
        packed_option::PackedOption,
    },
    entity::EntityList,
};
use quick_proc::{QuickDefault, RealQuickSer, QuickSer, QuickEnumGets};

pub const BUILTIN_MODULE: Mod = Mod(0);

crate::impl_entity!(Ast);
crate::impl_entity!(Fun);
crate::impl_entity!(Source);
crate::impl_entity!(Manifest);
crate::impl_entity!(Mod);
crate::impl_entity!(Ty);
crate::impl_entity!(Unused);

#[derive(Debug, Clone, QuickDefault, Copy, RealQuickSer)]
pub struct ValueEnt {
    #[default(Ty::reserved_value())]
    pub ty: Ty,
    pub inst: PackedOption<Inst>,
    pub offset: Size,
    pub mutable: bool,
    pub on_stack: bool,
}

impl ValueEnt {
    pub fn temp(ty: Ty) -> Self {
        Self {
            ty,
            ..Default::default()
        }
    }
}

#[derive(Debug, Default, Clone, Copy, RealQuickSer)]
pub struct InstEnt {
    pub kind: IKind,
    pub value: PackedOption<Value>,
    pub hint: Token,
    pub prev: PackedOption<Inst>,
    pub next: PackedOption<Inst>,
    pub block: PackedOption<Block>,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub enum IKind {
    NoOp,
    FunPointer(Fun),
    FunPointerCall(Value, EntityList<Value>),
    GlobalLoad(GlobalValue),
    Call(Fun, EntityList<Value>),
    UnresolvedDot(Value, ID),
    VarDecl(Value),
    Zeroed,
    Uninitialized,
    Lit(LTKind),
    Return(PackedOption<Value>),
    Assign(Value),
    Jump(Block, EntityList<Value>),
    JumpIfTrue(Value, Block, EntityList<Value>),
    Offset(Value),
    Deref(Value, bool),
    Ref(Value),
    Cast(Value),
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

#[derive(Debug, Clone, Copy, Default, RealQuickSer)]
pub struct BlockEnt {
    pub block: PackedOption<Block>,

    pub prev: PackedOption<Block>,
    pub next: PackedOption<Block>,

    pub args: EntityList<Value>,

    pub start: PackedOption<Inst>,
    pub end: PackedOption<Inst>,
}

#[derive(Debug, QuickDefault, Clone, Copy, RealQuickSer)]
pub struct FunBody {
    pub current_block: PackedOption<Block>,
    pub entry_block: PackedOption<Block>,
    pub last_block: PackedOption<Block>,
}

impl FunBody {
    pub fn clear(&mut self) {
        self.entry_block = PackedOption::default();
        self.last_block = PackedOption::default();
        self.current_block = PackedOption::default();
    }
}

#[derive(Debug, Clone, QuickSer, QuickDefault)]
pub struct TypeEnt {
    pub id: ID,
    #[default(Mod::reserved_value())]
    pub module: Mod,
    pub vis: Vis,
    pub params: EntityList<Ty>,
    pub kind: TKind,
    pub name: Span,
    pub hint: Token,
    #[default(Ast::reserved_value())]
    pub attrs: Ast,
    pub size: Size,
    pub align: Size,
}

impl TypeEnt {
    pub fn to_cr_type(&self, isa: &dyn TargetIsa) -> Type {
        match &self.kind {
            TKind::Pointer(..) | TKind::Array(..) | TKind::Structure(_) | TKind::FunPointer(_)  => {
                isa.pointer_type()
            }
            TKind::Enumeration(_) => I8, //temporary solution
            &TKind::Builtin(ty) => ty.0,
            TKind::Generic(_) | TKind::Constant(_) | TKind::Unresolved(_) => unreachable!(),
        }
    }

    pub fn on_stack(&self, ptr_ty: Type) -> bool {
        self.size.pick(ptr_ty == I32) > ptr_ty.bytes() as u32
    }
}

#[derive(Debug, Clone, QuickEnumGets, QuickSer)]
pub enum TKind {
    Builtin(CrTypeWr),
    Pointer(Ty, bool),
    Enumeration(Vec<ID>),
    Array(Ty, u32),
    FunPointer(Signature),
    Constant(TypeConst),
    Structure(SType),
    Generic(Ast),
    Unresolved(Ast),
}

crate::impl_wrapper!(CrTypeWr, Type);

impl Default for TKind {
    fn default() -> Self {
        TKind::Builtin(CrTypeWr(INVALID))
    }
}

#[derive(Debug, Clone, Copy, Default, RealQuickSer)]
pub struct Signature {
    pub call_conv: CallConv,
    pub args: EntityList<Ty>,
    pub ret: PackedOption<Ty>,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub enum TypeConst {
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),
    String(Span),
}

#[derive(Debug, Clone, QuickSer)]
pub struct SType {
    pub kind: SKind,
    pub fields: Vec<SField>,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct SField {
    pub embedded: bool,
    pub vis: Vis,
    pub id: ID,
    pub offset: Size,
    pub ty: Ty,
    pub hint: Token,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum SKind {
    Struct,
    Union,
    Tuple,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum CallConv {
    Fast,
    Cold,
    SystemV,
    WindowsFastcall,
    AppleAarch64,
    BaldrdashSystemV,
    BaldrdashWindows,
    Baldrdash2020,
    Probestack,
    WasmtimeSystemV,
    WasmtimeFastcall,
    WasmtimeAppleAarch64,
    Platform,
}

impl CallConv {
    pub fn from_str(s: &str) -> Option<Self> {
        Some(match s {
            "fast" => Self::Fast,
            "cold" => Self::Cold,
            "system_v" => Self::SystemV,
            "windows_fastcall" => Self::WindowsFastcall,
            "apple_aarch64" => Self::AppleAarch64,
            "baldrdash_system_v" => Self::BaldrdashSystemV,
            "baldrdash_windows" => Self::BaldrdashWindows,
            "baldrdash_2020" => Self::Baldrdash2020,
            "probestack" => Self::Probestack,
            "wasmtime_system_v" => Self::WasmtimeSystemV,
            "wasmtime_fastcall" => Self::WasmtimeFastcall,
            "wasmtime_apple_aarch64" => Self::WasmtimeAppleAarch64,
            "platform" => Self::Platform,
            _ => return None,
        })
    }

    pub fn to_cr_call_conv(&self, isa: &dyn TargetIsa) -> CrCallConv {
        match self {
            Self::Platform => isa.default_call_conv(),
            _ => unsafe { std::mem::transmute(*self) },
        }
    }
}

impl Default for CallConv {
    fn default() -> Self {
        Self::Fast
    }
}