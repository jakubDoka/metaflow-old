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



impl TableId for GlobalEnt {
    fn id(&self) -> ID {
        self.id
    }
}