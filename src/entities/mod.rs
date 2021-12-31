use cranelift::{codegen::{ir::{Inst, Value, Block, GlobalValue}, packed_option::PackedOption}, entity::EntityList};
use quick_proc::{RealQuickSer, QuickDefault};
use cranelift::entity::packed_option::ReservedValue;
use crate::{util::{sdbm::ID, Size}, lexer::{Token, TKind}};

crate::impl_entity!(Ast);
crate::impl_entity!(Fun);
crate::impl_entity!(Source);
crate::impl_entity!(Manifest);
crate::impl_entity!(Mod);
crate::impl_entity!(Ty);

#[derive(Debug, Clone, QuickDefault, Copy, RealQuickSer)]
pub struct ValueEnt {
    pub id: ID,
    #[default(Ty::reserved_value())]
    pub ty: Ty,
    #[default(Inst::reserved_value())]
    pub inst: Inst,
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
    Lit(TKind),
    Return(Option<Value>),
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