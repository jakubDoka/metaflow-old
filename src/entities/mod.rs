use crate::{
    lexer::{token, Span, Token},
    util::{sdbm::ID, storage::TableId, Size},
};
use cranelift::{
    codegen::isa::{CallConv as CrCallConv, TargetIsa},
    entity::packed_option::ReservedValue,
    module::{DataId, Linkage},
};
use cranelift::{
    codegen::{
        ir::{types::*, Block, GlobalValue, Inst, Value},
        packed_option::PackedOption,
    },
    entity::EntityList,
};
use quick_proc::{QuickEnumGets, QuickSer, RealQuickSer};



crate::impl_entity!(
    Ast,
    Fun,
    Manifest,
    Mod,
    Ty,
    AnonString,
    Unused
);

#[derive(Debug, Clone, Copy, RealQuickSer, Default)]
pub struct AnonStringEnt {
    pub jit_id: PackedOption<DataId>,
    pub id: PackedOption<DataId>,
    pub data: Span,
    pub table_id: ID,
}

impl TableId for AnonStringEnt {
    fn id(&self) -> ID {
        self.table_id
    }
}

#[derive(Debug, Clone, Default, Copy, RealQuickSer)]
pub struct ValueEnt {
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
    Lit(token::Kind),
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

#[derive(Debug, Default, Clone, Copy, RealQuickSer)]
pub struct FunBody {
    pub dependant_functions: EntityList<Fun>,
    pub dependant_globals: EntityList<GlobalValue>,
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

#[derive(Debug, Clone, Default, Copy, RealQuickSer)]
pub struct GlobalEnt {
    pub id: ID,
    pub vis: Vis,
    pub mutable: bool,
    pub module: Mod,
    pub ty: Ty,
    pub hint: Token,
    pub ast: Ast,
    pub attrs: Ast,
    pub alias: Option<Span>,
    pub linkage: Linkage,
}

impl TableId for GlobalEnt {
    fn id(&self) -> ID {
        self.id
    }
}