use super::*;

#[derive(Debug, Clone)]
pub struct Val {
    kind: VKind,
    datatype: Cell<Datatype>,
}

impl Val {
    pub fn new(kind: VKind, datatype: Cell<Datatype>) -> Self {
        Self { kind, datatype }
    }

    pub fn new_stack(
        mutable: bool,
        datatype: &Cell<Datatype>,
        builder: &mut FunctionBuilder,
    ) -> Self {
        let slot = builder.create_stack_slot(StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: datatype.size(),
        });
        let value = builder.ins().stack_addr(I64, slot, 0);
        Self {
            kind: VKind::Address(value, mutable, 0),
            datatype: datatype.clone(),
        }
    }

    pub fn unresolved(datatype: Cell<Datatype>) -> Self {
        Self::new(VKind::Unresolved, datatype)
    }

    pub fn immutable(value: Value, datatype: Cell<Datatype>) -> Self {
        Self::new(VKind::Immutable(value), datatype)
    }

    pub fn mutable(value: Variable, datatype: Cell<Datatype>) -> Self {
        Self::new(VKind::Mutable(value), datatype)
    }

    pub fn address(value: Value, mutable: bool, datatype: Cell<Datatype>) -> Self {
        Self::new(VKind::Address(value, mutable, 0), datatype)
    }

    pub fn is_mutable(&self) -> bool {
        matches!(self.kind, VKind::Mutable(_) | VKind::Address(_, true, _))
    }

    pub fn take_address(&self) -> Value {
        match self.kind {
            VKind::Address(value, ..) => {
                value.clone()
            }
            _ => panic!("take_address on non-address"),
        }
    }

    pub fn deref(&self, builder: &mut FunctionBuilder, isa: &dyn TargetIsa) -> Self {
        match self.datatype.kind() {
            DKind::Pointer(datatype, mutable) => {
                let val = self.read(builder, isa);
                return Self::address(val, *mutable, datatype.clone());
            }
            _ => panic!("deref on non-pointer"),
        }
        
    }

    pub fn read(&self, builder: &mut FunctionBuilder, isa: &dyn TargetIsa) -> Value {
        match &self.kind {
            VKind::Immutable(value) => value.clone(),
            VKind::Mutable(variable) => builder.use_var(*variable),
            VKind::Address(value, _, offset) => {
                if self.datatype.is_on_stack() {
                    value.clone()
                } else {
                    builder.ins().load(
                        self.datatype.ir_repr(isa),
                        MemFlags::new(),
                        *value,
                        *offset as i32,
                    )
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn write(
        &self,
        value: &Val,
        token: &Token,
        builder: &mut FunctionBuilder,
        isa: &dyn TargetIsa,
    ) -> Result<()> {
        assert_type(token, &self.datatype, &value.datatype)?;

        let src_value = value.read(builder, isa);

        match &self.kind {
            VKind::Immutable(_) => {
                return Err(IrGenError::new(IGEKind::AssignToImmutable, token.clone()))
            }
            VKind::Mutable(variable) => builder.def_var(*variable, src_value),
            VKind::Address(dst_value, mutable, offset) => {
                if *mutable {
                    if value.datatype.is_on_stack() {
                        static_memmove(
                            *dst_value,
                            *offset,
                            src_value,
                            value.offset(),
                            self.datatype.size(),
                            builder,
                        );
                    } else {
                        builder
                            .ins()
                            .store(MemFlags::new(), src_value, *dst_value, *offset as i32);
                    }
                } else {
                    return Err(IrGenError::new(IGEKind::AssignToImmutable, token.clone()));
                }
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    pub fn set_mutability(&mut self, arg: bool) {
        match &mut self.kind {
            VKind::Address(_, mutable, _) => *mutable = arg,
            _ => panic!("set_mutability called on non-address"),
        }
    }

    pub fn add_offset(&mut self, offset: u32) {
        match &mut self.kind {
            VKind::Address(.., off) => *off += offset,
            _ => panic!("add_offset called on non-address"),
        }
    }

    pub fn offset(&self) -> u32 {
        match &self.kind {
            VKind::Address(_, _, off) => *off,
            _ => panic!("offset called on non-address"),
        }
    }

    pub fn datatype(&self) -> &Cell<Datatype> {
        &self.datatype
    }

    pub fn set_datatype(&mut self, datatype: Cell<Datatype>) {
        self.datatype = datatype;
    }

    pub fn kind(&self) -> &VKind {
        &self.kind
    }

    pub fn set_kind(&mut self, kind: VKind) {
        self.kind = kind;
    }

    pub fn is_addressable(&self) -> bool {
        matches!(self.kind, VKind::Address(..))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum VKind {
    Mutable(Variable),
    Immutable(Value),
    Address(Value, bool, u32),
    Unresolved,
}
