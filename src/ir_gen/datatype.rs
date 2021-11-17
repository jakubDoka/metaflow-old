use super::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Datatype {
    name: String,
    kind: DKind,
    size: Option<u32>,
}

impl Datatype {
    pub fn new(name: String, kind: DKind) -> Self {
        Self {
            name,
            kind,
            size: None,
        }
    }

    pub fn with_size(name: String, kind: DKind, size: u32) -> Self {
        Self {
            name,
            kind,
            size: Some(size),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kind(&self) -> &DKind {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut DKind {
        &mut self.kind
    }

    pub fn set_size(&mut self, size: u32) {
        self.size = Some(size);
    }

    pub fn size(&self) -> u32 {
        self.size.unwrap()
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self.kind, DKind::Pointer(..))
    }

    pub fn is_int(&self) -> bool {
        match &self.kind {
            DKind::Builtin(tp) => tp.is_int() && self.name.starts_with('i'),
            DKind::Pointer(..) => true,
            _ => false,
        }
    }

    pub fn is_uint(&self) -> bool {
        match &self.kind {
            DKind::Builtin(tp) => tp.is_int() && self.name.starts_with('u'),
            _ => false,
        }
    }

    pub fn is_float(&self) -> bool {
        match &self.kind {
            DKind::Builtin(tp) => tp.is_float(),
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        match &self.kind {
            DKind::Builtin(tp) => tp.is_bool(),
            _ => false,
        }
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self.kind, DKind::Builtin(_))
    }

    pub fn is_resolved(&self) -> bool {
        !matches!(self.kind, DKind::Unresolved(_))
    }

    pub fn is_on_stack(&self) -> bool {
        matches!(self.kind, DKind::Structure(_))
    }

    pub fn is_size_resolved(&self) -> bool {
        self.size.is_some()
    }

    pub fn ir_repr(&self, isa: &dyn TargetIsa) -> Type {
        match self.kind {
            DKind::Builtin(tp) => tp,
            DKind::Structure(_) => isa.pointer_type(),
            DKind::Pointer(..) => isa.pointer_type(),
            _ => todo!("unimplemented type kind {:?}", self.kind),
        }
    }

    pub fn default_value(&self, builder: &mut FunctionBuilder, isa: &dyn TargetIsa) -> Value {
        match self.kind {
            DKind::Builtin(tp) => match tp {
                I8 | I16 | I32 | I64 => builder.ins().iconst(tp, 0),
                F32 => builder.ins().f32const(0.0),
                F64 => builder.ins().f64const(0.0),
                B1 => builder.ins().bconst(B1, false),
                _ => panic!("unsupported builtin type"),
            },
            DKind::Pointer(..) => builder.ins().null(isa.pointer_type()),
            _ => todo!("not implemented for type kind {:?}", self.kind),
        }
    }

    pub fn set_kind(&mut self, kind: DKind) {
        self.kind = kind;
    }

    pub fn clear(&mut self) {
        self.kind = DKind::Cleared
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DKind {
    Builtin(Type),
    Pointer(Cell<Datatype>, bool),
    Alias(Cell<Datatype>),
    Structure(Structure),
    Enum(Enum),
    Unresolved(Ast),
    Cleared,
}
