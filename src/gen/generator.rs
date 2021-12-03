use cranelift_codegen::{
    binemit::{NullStackMapSink, NullTrapSink},
    entity::EntityRef,
    ir::{
        condcodes::{FloatCC, IntCC},
        types::*,
        AbiParam, ArgumentPurpose, InstBuilder, MemFlags, Signature, StackSlot, StackSlotData,
        StackSlotKind,
    },
    isa::CallConv,
    Context,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use std::str::FromStr;

use crate::{
    ast::Ast,
    ir::{
        BTKind, CrBlock, CrType, CrValue, CrVar, FKind, FinalValue, Fun, IKind, Inst, LTKind,
        Program, TKind, Type, Value,
    },
    util::storage::SymID,
};

use super::{GEKind, GenError};

type Result<T = ()> = std::result::Result<T, GenError>;

pub struct Generator<'a> {
    program: &'a mut Program,
    context: &'a mut GeneratorContext,
}

impl<'a> Generator<'a> {
    pub fn new(program: &'a mut Program, context: &'a mut GeneratorContext) -> Self {
        Self { program, context }
    }

    pub fn generate(&mut self) -> Result {
        self.declare()?;

        self.make_bodies()?;

        Ok(())
    }

    fn make_bodies(&mut self) -> Result {
        let mut fun_ctx = FunctionBuilderContext::new();
        let mut ctx = Context::new();

        for fun in unsafe { self.program.functions.direct_ids() } {
            if !self.program.functions.is_direct_valid(fun) {
                continue;
            }

            if matches!(
                self.program[fun].kind,
                FKind::Generic(_) | FKind::Builtin(..)
            ) {
                continue;
            }

            let fun_id = self.program[fun].object_id.unwrap();
            ctx.func.signature = self.program[fun].final_signature.take().unwrap();
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fun_ctx);

            self.body(fun, &mut builder)?;

            builder.finalize();

            println!("{}", ctx.func.display());

            ctx.compute_cfg();
            ctx.compute_domtree();
            ctx.compute_loop_analysis();

            self.program
                .object_module
                .define_function(
                    fun_id,
                    &mut ctx,
                    &mut NullTrapSink::default(),
                    &mut NullStackMapSink {},
                )
                .unwrap();

            ctx.clear();
        }

        Ok(())
    }

    fn body(&mut self, fun: Fun, builder: &mut FunctionBuilder) -> Result {
        let entry_block = self.program[fun].body.insts.first().unwrap();
        let mut current = entry_block;

        let mut buffer = std::mem::take(&mut self.context.block_buffer);

        loop {
            let cr_block = builder.create_block();
            let block = self.program[fun].body.insts[current].kind.block_mut();
            block.block = Some(cr_block);
            let inst = block.end.unwrap();
            let args = std::mem::take(&mut block.args);
            for &arg in args.iter() {
                let value = builder.append_block_param(cr_block, self.repr_of_val(fun, arg));
                self.wrap_val(fun, arg, value);
            }

            let next = self.program[fun].body.insts.next(current).unwrap();

            buffer.push((next, cr_block));

            if let Some(next) = self.program[fun].body.insts.next(inst) {
                current = next;
            } else {
                break;
            }
        }

        for (block, cr_block) in buffer.drain(..) {
            builder.switch_to_block(cr_block);
            self.block(fun, block, builder)?;
        }

        self.context.block_buffer = buffer;

        builder.seal_all_blocks();

        Ok(())
    }

    fn block(&mut self, fun: Fun, mut current: Inst, builder: &mut FunctionBuilder) -> Result {
        let mut call_buffer = std::mem::take(&mut self.context.call_buffer);
        let mut arg_buffer = std::mem::take(&mut self.context.arg_buffer);
        loop {
            let inst = &self.program[fun].body.insts[current];
            let value = inst.value;

            match &inst.kind {
                IKind::Call(id, args) => {
                    let id = *id;
                    
                    let other = &self.program[id];
                    
                    arg_buffer.clear();
                    arg_buffer.extend(args);

                    if let FKind::Builtin(_, name) = other.kind {
                        
                        self.call_builtin(fun, name, &arg_buffer, value, builder);
                    } else {
                        let object_id = other.object_id.unwrap();
                        let sig = other.signature();
                        let struct_return = sig.struct_return;

                        if struct_return {
                            let datatype = sig.return_type.unwrap();
                            let size = self.program[datatype].size;
                            let last = arg_buffer[arg_buffer.len() - 1];
                            let data = StackSlotData::new(StackSlotKind::ExplicitSlot, size);
                            let slot = builder.create_stack_slot(data);
                            self.program[fun].body.values[last].value = FinalValue::StackSlot(slot);
                        }

                        let fun_ref = self
                            .program
                            .object_module
                            .declare_func_in_func(object_id, builder.func);

                        
                        call_buffer.clear();
                        call_buffer.extend(arg_buffer.iter().map(|&a| self.unwrap_val(fun, a, builder)));

                        let inst = builder.ins().call(fun_ref, &call_buffer);

                        if let Some(value) = value {
                            let val = builder.inst_results(inst)[0];
                            self.wrap_val(fun, value, val);
                        }
                    }
                }
                IKind::VarDecl(init) => {
                    let init = *init;
                    let value = value.unwrap();
                    let datatype = self.program[fun].body.values[value].datatype;
                    let size = self.program[datatype].size;
                    let size = size + 8 * ((size & 7) != 0) as u32 - (size & 7); // align
                    let val = &mut self.program[fun].body.values[value];
                    if val.on_stack {
                        let data = StackSlotData::new(StackSlotKind::ExplicitSlot, size);
                        let slot = builder.create_stack_slot(data);
                        val.value = FinalValue::StackSlot(slot);
                        self.assign_val(fun, value, init, builder)
                    } else if val.mutable {
                        let var = CrVar::new(value.raw());
                        val.value = FinalValue::Var(var);
                        builder.declare_var(var, self.repr_of(datatype));
                        self.assign_val(fun, value, init, builder)
                    } else {
                        let val = self.unwrap_val(fun, init, builder);
                        self.program[fun].body.values[value].value = FinalValue::Value(val);
                    }
                }
                IKind::ZeroValue => {
                    self.program[fun].body.values[value.unwrap()].value = FinalValue::Zero;
                }
                IKind::Lit(lit) => {
                    let value = value.unwrap();
                    let datatype = self.program[fun].body.values[value].datatype;
                    let repr = self.repr_of(datatype);
                    let lit = match lit {
                        LTKind::Int(val, _) => builder.ins().iconst(repr, *val),
                        LTKind::Uint(val, _) => builder.ins().iconst(repr, *val as i64),
                        LTKind::Float(val, _) => {
                            if repr == F32 {
                                builder.ins().f32const(*val as f32)
                            } else {
                                builder.ins().f64const(*val)
                            }
                        }
                        LTKind::Bool(val) => builder.ins().bconst(B1, *val),
                        LTKind::Char(val) => builder.ins().iconst(I32, *val as i64),
                        LTKind::String(_) => todo!(),
                        lit => todo!("{}", lit),
                    };
                    self.program[fun].body.values[value].value = FinalValue::Value(lit);
                }
                IKind::Return(value) => {
                    if let Some(value) = value {
                        let value = self.unwrap_val(fun, *value, builder);
                        builder.ins().return_(&[value]);
                    } else {
                        builder.ins().return_(&[]);
                    }
                }
                IKind::Assign(other) => {
                    let other = *other;
                    self.assign_val(fun, other, value.unwrap(), builder);
                }
                IKind::Jump(block, values) => {
                    let block = *block;
                    
                    call_buffer.clear();
                    call_buffer.extend(values.iter().map(|&a| self.unwrap_val(fun, a, builder)));
                    let block = self.unwrap_block(fun, block);
                    builder.ins().jump(block, &call_buffer);
                }
                IKind::JumpIfTrue(condition, block, values) => {
                    let condition = *condition;
                    let block = *block;
                    call_buffer.clear();
                    call_buffer.extend(values.iter().map(|&a| self.unwrap_val(fun, a, builder)));
                    let block = self.unwrap_block(fun, block);
                    let value = self.unwrap_val(fun, condition, builder);
                    builder.ins().brnz(value, block, &call_buffer);
                }
                IKind::Offset(other) | IKind::Deref(other) | IKind::Ref(other) => {
                    let other = *other;
                    self.pass(fun, other, value.unwrap())
                }
                IKind::Load(val) => {
                    let val = self.unwrap_val(fun, *val, builder);
                    self.wrap_val(fun, value.unwrap(), val);
                }
                IKind::BlockEnd(_) => break,
                value => unreachable!("{:?}", value),
            }

            current = self.program[fun].body.insts.next(current).unwrap();
        }

        self.context.call_buffer = call_buffer;
        self.context.arg_buffer = arg_buffer;

        Ok(())
    }

    fn call_builtin(
        &mut self,
        fun: Fun,
        name: &str,
        args: &[Value],
        target: Option<Value>,
        builder: &mut FunctionBuilder,
    ) {
        match args.len() {
            1 => {
                let val = &self.program[fun].body.values[args[0]];
                let datatype = val.datatype;
                let a = self.unwrap_val(fun, args[0], builder);
                let value = match BTKind::of(datatype) {
                    BTKind::Int | BTKind::Uint => match name {
                        "+" => a,
                        "-" => builder.ins().ineg(a),
                        "~" => builder.ins().bnot(a),
                        "++" | "--" => {
                            let value =
                                builder.ins().iadd_imm(a, if name == "++" { 1 } else { -1 });
                            if val.mutable {
                                self.assign_raw_val(fun, args[0], value, builder)
                            }
                            value
                        }
                        "abs" => builder.ins().iabs(a),
                        name => todo!("{}", name),
                    },
                    BTKind::Float(_) => match name {
                        "+" => a,
                        "-" => builder.ins().fneg(a),
                        "abs" => builder.ins().fabs(a),
                        todo => todo!("{}", todo),
                    },
                    BTKind::Bool => match name {
                        "!" => builder.ins().bnot(a),
                        name => todo!("{}", name),
                    },
                    BTKind::Ptr => todo!(),
                };

                self.wrap_val(fun, target.unwrap(), value)
            }
            2 => {
                let datatype = self.program[fun].body.values[args[0]].datatype;
                let a = self.unwrap_val(fun, args[0], builder);
                let b = self.unwrap_val(fun, args[1], builder);
                let kind = BTKind::of(datatype);
                let value = match kind {
                    BTKind::Int | BTKind::Uint => match (name, kind) {
                        ("+", _) => builder.ins().iadd(a, b),
                        ("-", _) => builder.ins().isub(a, b),
                        ("*", _) => builder.ins().imul(a, b),
                        ("<<", _) => builder.ins().ishl(a, b),

                        ("min", _) => builder.ins().imin(a, b),
                        ("max", _) => builder.ins().imax(a, b),

                        ("/", BTKind::Int) => builder.ins().sdiv(a, b),
                        ("%", BTKind::Int) => builder.ins().srem(a, b),
                        (">>", BTKind::Int) => builder.ins().sshr(a, b),

                        ("/", BTKind::Uint) => builder.ins().udiv(a, b),
                        ("%", BTKind::Uint) => builder.ins().urem(a, b),
                        (">>", BTKind::Uint) => builder.ins().ushr(a, b),

                        ("&", _) => builder.ins().band(a, b),
                        ("|", _) => builder.ins().bor(a, b),
                        ("^", _) => builder.ins().bxor(a, b),

                        ("==" | "!=" | ">=" | "<=" | "<" | ">", _) => {
                            let strategy = match (name, kind) {
                                ("==", _) => IntCC::Equal,
                                ("!=", _) => IntCC::NotEqual,
                                ("<", BTKind::Int) => IntCC::SignedLessThan,
                                ("<", BTKind::Uint) => IntCC::UnsignedLessThan,
                                (">", BTKind::Int) => IntCC::SignedGreaterThan,
                                (">", BTKind::Uint) => IntCC::UnsignedGreaterThan,
                                ("<=", BTKind::Int) => IntCC::SignedLessThanOrEqual,
                                ("<=", BTKind::Uint) => IntCC::UnsignedLessThanOrEqual,
                                (">=", BTKind::Int) => IntCC::SignedGreaterThanOrEqual,
                                (">=", BTKind::Uint) => IntCC::UnsignedGreaterThanOrEqual,
                                _ => unreachable!(),
                            };

                            builder.ins().icmp(strategy, a, b)
                        }

                        name => todo!("{:?}", name),
                    },
                    BTKind::Float(_) => match name {
                        "+" => builder.ins().fadd(a, b),
                        "-" => builder.ins().fsub(a, b),
                        "*" => builder.ins().fmul(a, b),
                        "/" => builder.ins().fdiv(a, b),

                        "max" => builder.ins().fmax(a, b),
                        "min" => builder.ins().fmin(a, b),

                        "==" | "!=" | ">=" | "<=" | "<" | ">" => {
                            let strategy = match name {
                                "==" => FloatCC::Equal,
                                "!=" => FloatCC::NotEqual,
                                "<" => FloatCC::LessThan,
                                ">" => FloatCC::GreaterThan,
                                "<=" => FloatCC::LessThanOrEqual,
                                ">=" => FloatCC::GreaterThanOrEqual,
                                _ => unreachable!(),
                            };

                            builder.ins().fcmp(strategy, a, b)
                        }

                        name => todo!("{:?}", name),
                    },
                    BTKind::Bool => match name {
                        "|" => builder.ins().bor(a, b),
                        "&" => builder.ins().band(a, b),
                        "^" => builder.ins().bxor(a, b),
                        name => todo!("{:?}", name),
                    },
                    BTKind::Ptr => todo!(),
                };
                self.wrap_val(fun, target.unwrap(), value)
            }
            len => todo!("{}", len),
        }
    }

    fn declare(&mut self) -> Result {
        let mut name_buffer = String::new();
        let mut signature = Signature::new(CallConv::Fast);

        let entrypoint = None;

        for fun in unsafe { self.program.functions.direct_ids() } {
            if !self.program.functions.is_direct_valid(fun) {
                continue;
            }

            if matches!(
                self.program[fun].kind,
                FKind::Generic(_) | FKind::Builtin(..)
            ) {
                continue;
            }

            let fun_id = self.program.functions.direct_to_id(fun).0;

            name_buffer.clear();

            let mut number = fun_id;
            while number > 0 {
                let mut digit = (number % 36) as u8;
                digit += (digit < 10) as u8 * b'0' + (digit >= 10) as u8 * (b'a' - 10);
                name_buffer.push(digit as char);
                number /= 36;
            }

            let (linkage, alias) = if let Some(attr) = self.program.get_attr(fun, "linkage") {
                assert_attr_len(attr, 1)?;

                let linkage = match attr[0].token.spam.raw() {
                    "import" => Linkage::Import,
                    "local" => Linkage::Local,
                    "export" => Linkage::Export,
                    "preemptible" => Linkage::Preemptible,
                    "hidden" => Linkage::Hidden,
                    _ => return Err(GenError::new(GEKind::InvalidLinkage, &attr.token)),
                };

                if attr.len() > 1 {
                    (linkage, attr[1].token.spam.raw())
                } else {
                    (linkage, &name_buffer[..])
                }
            } else {
                (Linkage::Export, &name_buffer[..])
            };

            let call_conv = if let Some(attr) = self.program.get_attr(fun, "call_conv") {
                assert_attr_len(attr, 1)?;
                let conv = attr[0].token.spam.raw();
                if conv == "platform" {
                    let triple = self.program.object_module.isa().triple();
                    CallConv::triple_default(triple)
                } else {
                    CallConv::from_str(conv)
                        .map_err(|_| GenError::new(GEKind::InvalidCallConv, &attr.token))?
                }
            } else {
                CallConv::Fast
            };

            signature.clear(call_conv);

            
            if let Some(return_type) = self.program[fun].signature().return_type {
                let repr = self.repr_of(return_type);

                let purpose = if self.on_stack(return_type) {
                    ArgumentPurpose::StructReturn
                } else {
                    ArgumentPurpose::Normal
                };

                signature.returns.push(AbiParam::special(repr, purpose));
            }

            let sig = self.program[fun].signature();

            for arg in sig.args.iter() {
                let repr = self.repr_of(arg.datatype);

                signature.params.push(AbiParam::new(repr));
            }

            if sig.struct_return {
                let last = signature.params.len() - 1;
                signature.params[last].purpose = ArgumentPurpose::StructReturn;
            }

            let alias = if let Some(attr) = self.program.get_attr(fun, "entry") {
                if let Some(entry) = entrypoint {
                    return Err(GenError::new(
                        GEKind::DuplicateEntrypoint(entry),
                        &attr.token,
                    ));
                }
                "WinMain"
            } else {
                alias
            };

            let id = self
                .program
                .object_module
                .declare_function(alias, linkage, &signature)
                .unwrap();

            self.program[fun].object_id = Some(id);
            self.program[fun].final_signature = Some(signature.clone());
        }

        Ok(())
    }

    fn assign_val(
        &mut self,
        fun: Fun,
        target: Value,
        source: Value,
        builder: &mut FunctionBuilder,
    ) {
        let target = &self.program[fun].body.values[target];
        let source_v = &self.program[fun].body.values[source];
        let datatype = source_v.datatype;

        debug_assert!(target.datatype == datatype);

        match target.value.clone() {
            FinalValue::StackSlot(slot) => {
                let size = self.program[datatype].size;
                match source_v.value {
                    FinalValue::Zero => static_stack_memset(slot, target.offset, 0, size, builder),
                    FinalValue::Value(value) => {
                        builder.ins().stack_store(value, slot, target.offset as i32);
                    }
                    FinalValue::Var(var) => {
                        let value = builder.use_var(var);
                        builder.ins().stack_store(value, slot, target.offset as i32);
                    }
                    FinalValue::StackSlot(other) => static_stack_memmove(
                        slot,
                        target.offset,
                        other,
                        source_v.offset,
                        size,
                        builder,
                    ),
                    FinalValue::Pointer(pointer) => {
                        let pt = self.program.isa().pointer_type();
                        let target_ptr = builder.ins().stack_addr(pt, slot, 0);
                        static_memmove(
                            target_ptr,
                            target.offset,
                            pointer,
                            source_v.offset,
                            size,
                            builder,
                        )
                    }
                    FinalValue::None => unreachable!(),
                }
            }
            FinalValue::Var(var) => {
                let value = self.unwrap_val(fun, source, builder);
                builder.def_var(var, value);
            }
            kind => unreachable!("{:?}", kind),
        };
    }

    fn assign_raw_val(
        &mut self,
        fun: Fun,
        target: Value,
        source: CrValue,
        builder: &mut FunctionBuilder,
    ) {
        let target = &self.program[fun].body.values[target];

        match target.value {
            FinalValue::StackSlot(slot) => {
                builder
                    .ins()
                    .stack_store(source, slot, target.offset as i32);
            }
            FinalValue::Pointer(pointer) => {
                builder
                    .ins()
                    .store(MemFlags::new(), source, pointer, target.offset as i32);
            }
            FinalValue::Var(var) => {
                builder.def_var(var, source);
            }
            _ => unreachable!(),
        };
    }

    fn unwrap_block(&mut self, fun: Fun, block: Inst) -> CrBlock {
        self.program[fun].body.insts[block]
            .kind
            .block()
            .block
            .unwrap()
    }

    #[inline]
    fn wrap_val(&mut self, fun: Fun, target: Value, value: CrValue) {
        self.program[fun].body.values[target].value = FinalValue::Value(value);
    }

    #[inline]
    fn wrap_slot(&mut self, fun: Fun, target: Value, value: StackSlot) {
        self.program[fun].body.values[target].value = FinalValue::StackSlot(value);
    }

    #[inline]
    fn unwrap_val(&self, fun: Fun, value: Value, builder: &mut FunctionBuilder) -> CrValue {
        let value = &self.program[fun].body.values[value];
        let datatype = value.datatype;
        match value.value {
            FinalValue::None => unreachable!(),
            FinalValue::Zero => {
                let repr = self.repr_of(datatype);
                match BTKind::of(datatype) {
                    BTKind::Int | BTKind::Uint => builder.ins().iconst(repr, 0),
                    BTKind::Float(32) => builder.ins().f32const(0.0),
                    BTKind::Float(64) => builder.ins().f64const(0.0),
                    BTKind::Bool => builder.ins().bconst(B1, false),
                    BTKind::Ptr => builder.ins().null(repr),
                    _ => unreachable!("{}", datatype),
                }
            }
            FinalValue::Value(value) => value,
            FinalValue::Var(var) => builder.use_var(var),
            FinalValue::Pointer(pointer) => {
                let wrapped_type = match self.program[datatype].kind {
                    TKind::Pointer(inner, _) => inner,
                    _ => unreachable!(),
                };
                if self.on_stack(wrapped_type) {
                    if value.offset != 0 {
                        let ptr_type = self.program.isa().pointer_type();
                        let offset = builder.ins().iconst(ptr_type, value.offset as i64);
                        builder.ins().iadd(pointer, offset)
                    } else {
                        pointer
                    }
                } else {
                    let repr = self.repr_of(wrapped_type);
                    let flags = MemFlags::new();
                    builder
                        .ins()
                        .load(repr, flags, pointer, value.offset as i32)
                }
            }
            FinalValue::StackSlot(slot) => {
                if self.on_stack(value.datatype) {
                    builder.ins().stack_addr(
                        self.program.object_module.isa().pointer_type(),
                        slot,
                        value.offset as i32,
                    )
                } else {
                    builder.ins().stack_load(
                        self.repr_of(value.datatype),
                        slot,
                        value.offset as i32,
                    )
                }
            }
        }
    }

    fn pass(&mut self, fun: Fun, from: Value, to: Value) {
        let other_value = self.program[fun].body.values[from].value.clone();
        self.program[fun].body.values[to].value = other_value;
    }

    #[inline]
    fn on_stack(&self, datatype: Type) -> bool {
        self.program[datatype].size > self.program.isa().pointer_bytes() as u32
    }

    #[inline]
    fn repr_of_val(&self, fun: Fun, value: Value) -> CrType {
        self.repr_of(self.program[fun].body.values[value].datatype)
    }

    #[inline]
    fn repr_of(&self, datatype: Type) -> CrType {
        match &self.program[datatype].kind {
            &TKind::Builtin(repr) => repr,
            TKind::Pointer(..) | TKind::Structure(..) => self.program.isa().pointer_type(),
            _ => unreachable!("{:?}", self.program[datatype].kind),
        }
    }
}

pub fn assert_attr_len(attr: &Ast, len: usize) -> Result {
    if attr.len() < len {
        Err(GenError::new(
            GEKind::TooShortAttribute(attr.len(), len),
            &attr.token,
        ))
    } else {
        Ok(())
    }
}

pub struct GeneratorContext {
    pub call_buffer: Vec<CrValue>,
    pub block_buffer: Vec<(Inst, CrBlock)>,
    pub arg_buffer: Vec<Value>,
}

impl Default for GeneratorContext {
    fn default() -> Self {
        Self {
            arg_buffer: vec![],
            call_buffer: vec![],
            block_buffer: vec![],
        }
    }
}

const MOVERS: &'static [CrType] = &[I8, I16, I32, I64];
const MOVER_SIZES: &'static [u32] = &[1, 2, 4, 8];
const MAX_MOVER_SIZE: u32 = 64;

fn find_best_mover(size: u32) -> (CrType, u32) {
    let size = size.min(MAX_MOVER_SIZE);
    MOVER_SIZES
        .iter()
        .rev()
        .position(|&s| s <= size)
        .map(|i| {
            (
                MOVERS[MOVERS.len() - i - 1],
                MOVER_SIZES[MOVER_SIZES.len() - i - 1],
            )
        })
        .unwrap()
}

fn static_memset(
    pointer: CrValue,
    pointer_offset: u32,
    value: i8,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    let (mover, _) = find_best_mover(size);

    let flags = MemFlags::new();

    let value = builder.ins().iconst(mover, value as i64);

    walk_mem(size, |_, offset| {
        builder
            .ins()
            .store(flags, value, pointer, (offset + pointer_offset) as i32);
    });
}

fn static_stack_memset(
    pointer: StackSlot,
    pointer_offset: u32,
    value: i8,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    let (mover, _) = find_best_mover(size);

    let value = builder.ins().iconst(mover, value as i64);

    walk_mem(size, |_, offset| {
        builder
            .ins()
            .stack_store(value, pointer, (offset + pointer_offset) as i32);
    });
}

fn static_memmove(
    dst_pointer: CrValue,
    dst_pointer_offset: u32,
    src_pointer: CrValue,
    src_pointer_offset: u32,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    let flags = MemFlags::new();

    walk_mem(size, |mover, offset| {
        let value = builder.ins().load(
            mover,
            flags,
            src_pointer,
            (offset + src_pointer_offset) as i32,
        );
        builder.ins().store(
            flags,
            value,
            dst_pointer,
            (offset + dst_pointer_offset) as i32,
        );
    });
}

fn static_stack_memmove(
    dst_pointer: StackSlot,
    dst_pointer_offset: u32,
    src_pointer: StackSlot,
    src_pointer_offset: u32,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    walk_mem(size, |mover, offset| {
        let value =
            builder
                .ins()
                .stack_load(mover, src_pointer, (offset + src_pointer_offset) as i32);
        builder
            .ins()
            .stack_store(value, dst_pointer, (offset + dst_pointer_offset) as i32);
    });
}

fn walk_mem<F: FnMut(CrType, u32)>(size: u32, mut fun: F) {
    let (mover, mover_size) = find_best_mover(size);

    let mut offset = 0u32;
    loop {
        fun(mover, offset);

        offset += mover_size;
        if offset + mover_size >= size {
            break;
        }
    }

    if size > offset {
        // overlap should not matter
        let offset = size - mover_size;
        fun(mover, offset);
    }
}
