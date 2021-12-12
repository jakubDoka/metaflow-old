use cranelift_codegen::{
    binemit::{NullStackMapSink, NullTrapSink},
    entity::EntityRef,
    ir::{
        condcodes::{FloatCC, IntCC},
        types::*,
        Block as CrBlock, InstBuilder, MemFlags, Signature, StackSlot, StackSlotData,
        StackSlotKind, Type as CrType, Value as CrValue,
    },
    isa::CallConv,
    Context,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable as CrVar};
use cranelift_module::{DataContext, FuncOrDataId, Linkage, Module};
use std::ops::{Deref, DerefMut};

use crate::{
    functions::{
        self, FContext, FKind, FParser, FState, FinalValue, IKind, Inst, Program, RFun,
        Value,
    },
    lexer::{TKind as LTKind, Token},
    module_tree::Mod,
    types::{self, TKind, Type, TypeDisplay},
    util::{sdbm::SdbmHash, storage::IndexPointer},
};

use super::{GEKind, GenError};

type Result<T = ()> = std::result::Result<T, GenError>;

pub const STRING_SALT: u64 = 0xDEADBEEF; // just a random number

pub struct Generator<'a> {
    program: &'a mut Program,
    state: &'a mut FState,
    context: &'a mut GContext,
}

impl<'a> Generator<'a> {
    pub fn new(program: &'a mut Program, state: &'a mut GState, context: &'a mut GContext) -> Self {
        Self {
            program,
            state,
            context,
        }
    }

    pub fn generate(&mut self, module: Mod) -> Result {
        FParser::new(self.program, self.state, self.context)
            .parse(module)
            .map_err(|err| GenError::new(GEKind::FunError(err), Token::default()))?;

        self.make_bodies()?;

        Ok(())
    }

    fn make_bodies(&mut self) -> Result {
        let mut fun_ctx = FunctionBuilderContext::new();
        let mut ctx = Context::new();

        let mut represented = std::mem::take(&mut self.state.represented);

        for fun in represented.drain(..) {
            //println!("{}", FunDisplay::new(&self.state, fun));

            let rid = self.state.funs[fun].kind.unwrap_represented();
            let fun_id = self.state.rfuns[rid].id;
            if self
                .program
                .module
                .declarations()
                .get_function_decl(fun_id)
                .linkage
                == Linkage::Import
            {
                continue;
            }

            ctx.func.signature = std::mem::replace(
                &mut self.state.rfuns[rid].ir_signature,
                Signature::new(CallConv::Fast),
            );
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fun_ctx);

            self.body(rid, &mut builder)?;

            self.state.rfuns[rid].body.clear();
            self.context.body_pool.push(std::mem::take(&mut self.state.rfuns[rid].body));

            builder.finalize();

            //println!("{}", ctx.func.display());

            ctx.compute_cfg();
            ctx.compute_domtree();
            ctx.compute_loop_analysis();

            self.program
                .module
                .define_function(
                    fun_id,
                    &mut ctx,
                    &mut NullTrapSink::default(),
                    &mut NullStackMapSink {},
                )
                .unwrap();

            ctx.clear();
        }

        self.state.represented = represented;

        Ok(())
    }

    fn body(&mut self, fun: RFun, builder: &mut FunctionBuilder) -> Result {
        let entry_block = self.state.rfuns[fun].body.insts.first().unwrap();
        let mut current = entry_block;

        let mut buffer = self.context.pool.get();

        loop {
            let cr_block = builder.create_block();
            let block = self.state.rfuns[fun].body.insts[current].kind.block_mut();
            block.block = Some(cr_block);
            let inst = block.end.unwrap();
            let args = std::mem::take(&mut block.args);
            for &arg in args.iter() {
                let value = builder.append_block_param(cr_block, self.repr_of_val(fun, arg));
                self.wrap_val(fun, arg, value);
            }

            let next = self.state.rfuns[fun].body.insts.next(current).unwrap();

            buffer.push((next, cr_block));

            debug_assert!(
                matches!(
                    self.state.rfuns[fun].body.insts[inst].kind,
                    IKind::BlockEnd(_)
                ),
                "next block is not a block"
            );

            if let Some(next) = self.state.rfuns[fun].body.insts.next(inst) {
                current = next;
            } else {
                break;
            }
        }

        for (block, cr_block) in buffer.drain(..) {
            builder.switch_to_block(cr_block);
            self.block(fun, block, builder)?;
        }

        builder.seal_all_blocks();

        Ok(())
    }

    fn block(&mut self, fun: RFun, mut current: Inst, builder: &mut FunctionBuilder) -> Result {
        let mut call_buffer = self.context.pool.get();
        let mut arg_buffer = self.context.pool.get();

        loop {
            let inst = &self.state.rfuns[fun].body.insts[current];
            let value = inst.value;

            match &inst.kind {
                IKind::Call(id, args) => {
                    let id = *id;

                    let other = &self.state.funs[id];

                    arg_buffer.clear();
                    arg_buffer.extend(args);

                    if let &FKind::Builtin(return_type) = &other.kind {
                        let name = other.name;
                        self.call_builtin(fun, name, return_type, &arg_buffer, value, builder);
                    } else {
                        let rid = other.kind.unwrap_represented();
                        let r_ent = &self.state.rfuns[rid];
                        let fun_id = r_ent.id;

                        let mut struct_return = false;

                        if let Some(ret_ty) = r_ent.signature.ret_ty {
                            if self.on_stack(ret_ty) {
                                let size = self.state.types[ret_ty].size;
                                let last = arg_buffer[arg_buffer.len() - 1];
                                let data = StackSlotData::new(StackSlotKind::ExplicitSlot, size);
                                let slot = builder.create_stack_slot(data);
                                self.state.rfuns[fun].body.values[last].value =
                                    FinalValue::StackSlot(slot);
                                self.state.rfuns[fun].body.values[value.unwrap()].value =
                                    FinalValue::StackSlot(slot);
                                struct_return = true;
                            }
                        }

                        let fun_ref = self
                            .program
                            .module
                            .declare_func_in_func(fun_id, builder.func);

                        call_buffer.clear();
                        call_buffer
                            .extend(arg_buffer.iter().map(|&a| self.unwrap_val(fun, a, builder)));

                        let inst = builder.ins().call(fun_ref, &call_buffer);

                        if !struct_return {
                            if let Some(value) = value {
                                let val = builder.inst_results(inst)[0];
                                self.wrap_val(fun, value, val);
                            }
                        }
                    }
                }
                IKind::VarDecl(init) => {
                    let init = *init;
                    let value = value.unwrap();
                    let ty = self.state.rfuns[fun].body.values[value].ty;
                    let size = self.state.types[ty].size;
                    let size = size + 8 * ((size & 7) != 0) as u32 - (size & 7); // align
                    let val = &mut self.state.rfuns[fun].body.values[value];
                    if val.on_stack {
                        let data = StackSlotData::new(StackSlotKind::ExplicitSlot, size);
                        let slot = builder.create_stack_slot(data);
                        val.value = FinalValue::StackSlot(slot);
                        self.assign_val(fun, value, init, builder)
                    } else if val.mutable {
                        let var = CrVar::new(value.raw());
                        val.value = FinalValue::Var(var);
                        builder.declare_var(var, self.repr(ty));
                        self.assign_val(fun, value, init, builder)
                    } else {
                        let val = self.unwrap_val(fun, init, builder);
                        self.state.rfuns[fun].body.values[value].value = FinalValue::Value(val);
                    }
                }
                IKind::ZeroValue => {
                    self.state.rfuns[fun].body.values[value.unwrap()].value = FinalValue::Zero;
                }
                IKind::Lit(lit) => {
                    let value = value.unwrap();
                    let ty = self.state.rfuns[fun].body.values[value].ty;
                    let repr = self.repr(ty);
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
                        LTKind::String(data) => {
                            let data = data.clone();
                            let id = data.deref().sdbm_hash(STRING_SALT);
                            let mut name_buffer = self.context.pool.get();
                            functions::write_base36(id, &mut name_buffer);
                            let name = unsafe { std::str::from_utf8_unchecked(&name_buffer) };
                            let data_id = if let Some(FuncOrDataId::Data(data_id)) =
                                self.program.module.get_name(name)
                            {
                                data_id
                            } else {
                                let data_id = self
                                    .program
                                    .module
                                    .declare_data(name, Linkage::Export, false, false)
                                    .unwrap();
                                let context = unsafe {
                                    std::mem::transmute::<_, &mut DataContext>(
                                        &mut self.context.data_context,
                                    )
                                };
                                context.define(data.deref().to_owned().into_boxed_slice());
                                self.program.module.define_data(data_id, context).unwrap();
                                context.clear();
                                data_id
                            };

                            let value = self
                                .program
                                .module
                                .declare_data_in_func(data_id, builder.func);
                            builder.ins().global_value(types::ptr_ty(), value)
                        }
                        lit => todo!("{}", lit),
                    };
                    self.state.rfuns[fun].body.values[value].value = FinalValue::Value(lit);
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
                IKind::Offset(other) => {
                    let other = *other;
                    self.pass(fun, other, value.unwrap())
                }
                IKind::Deref(other) => {
                    let value = value.unwrap();
                    let other = *other;
                    let val = self.unwrap_val(fun, other, builder);
                    if self.state.rfuns[fun].body.values[value].on_stack {
                        self.state.rfuns[fun].body.values[value].value = FinalValue::Pointer(val);
                    } else {
                        let repr = self.repr_of_val(fun, value);
                        let val = builder.ins().load(repr, MemFlags::new(), val, 0);
                        self.state.rfuns[fun].body.values[value].value = FinalValue::Value(val);
                    }
                }
                IKind::Ref(val) => {
                    let val = self.unwrap_val(fun, *val, builder);
                    self.wrap_val(fun, value.unwrap(), val);
                }
                IKind::Cast(other) => {
                    let other = *other;
                    let value = value.unwrap();
                    if self.state.rfuns[fun].body.values[value].on_stack {
                        self.pass(fun, other, value);
                    } else {
                        let target = self.repr_of_val(fun, value);
                        if self.repr_of_val(fun, other) != target {
                            let other_value = self.unwrap_val(fun, other, builder);
                            let val = builder.ins().bitcast(target, other_value);
                            self.wrap_val(fun, value, val);
                        } else {
                            self.pass(fun, other, value);
                        }
                    }
                }
                IKind::BlockEnd(_) => break,
                value => unreachable!("{:?}", value),
            }

            current = self.state.rfuns[fun].body.insts.next(current).unwrap();
        }

        Ok(())
    }

    fn call_builtin(
        &mut self,
        fun: RFun,
        name: &str,
        return_type: Option<Type>,
        args: &[Value],
        target: Option<Value>,
        builder: &mut FunctionBuilder,
    ) {
        match args.len() {
            1 => {
                let val = &self.state.rfuns[fun].body.values[args[0]];
                let ty = val.ty;
                let a = self.unwrap_val(fun, args[0], builder);
                let kind = BTKind::of(ty);
                let repr = self.repr(ty);

                let value = match kind {
                    BTKind::Int | BTKind::Uint => match (name, kind) {
                        ("+", _) => a,
                        ("-", BTKind::Int) => builder.ins().ineg(a),
                        ("~", _) => builder.ins().bnot(a),
                        ("++" | "--", _) => {
                            let value =
                                builder.ins().iadd_imm(a, if name == "++" { 1 } else { -1 });
                            if val.mutable {
                                self.assign_raw_val(fun, args[0], value, builder)
                            }
                            value
                        }
                        ("f32", BTKind::Int) => builder.ins().fcvt_from_sint(F32, a),
                        ("f64", BTKind::Int) => builder.ins().fcvt_from_sint(F64, a),
                        ("f32", BTKind::Uint) => builder.ins().fcvt_from_sint(F32, a),
                        ("f64", BTKind::Uint) => builder.ins().fcvt_from_sint(F64, a),

                        ("abs", BTKind::Int) => {
                            let condition = builder.ins().icmp_imm(IntCC::SignedGreaterThan, a, 0);
                            let neg = builder.ins().ineg(a);
                            builder.ins().select(condition, a, neg)
                        }
                        ("bool", _) => builder.ins().icmp_imm(IntCC::NotEqual, a, 0),
                        ("i8" | "i16" | "i32" | "i64" | "int", _) => {
                            let to = self.repr(return_type.unwrap());
                            match to.bytes().cmp(&repr.bytes()) {
                                std::cmp::Ordering::Less => builder.ins().ireduce(to, a),
                                std::cmp::Ordering::Equal => a,
                                std::cmp::Ordering::Greater => builder.ins().sextend(to, a),
                            }
                        }
                        ("u8" | "u16" | "u32" | "u64" | "uint", _) => {
                            let to = self.repr(return_type.unwrap());
                            match to.bytes().cmp(&repr.bytes()) {
                                std::cmp::Ordering::Less => builder.ins().ireduce(to, a),
                                std::cmp::Ordering::Equal => a,
                                std::cmp::Ordering::Greater => builder.ins().uextend(to, a),
                            }
                        }
                        name => todo!("{:?}", name),
                    },
                    BTKind::Float(bits) => {
                        let target = if bits == 32 { F32 } else { F64 };
                        match name {
                            "+" => a,
                            "-" => builder.ins().fneg(a),
                            "abs" => builder.ins().fabs(a),
                            "u8" | "u16" | "u32" | "u64" | "uint" | "ptr" => {
                                let to = self.repr(return_type.unwrap());
                                builder.ins().fcvt_to_uint(to, a)
                            }
                            "i8" | "i16" | "i32" | "i64" | "int" => {
                                let to = self.repr(return_type.unwrap());
                                builder.ins().fcvt_to_sint(to, a)
                            }
                            "f32" => {
                                if target != F32 {
                                    builder.ins().fpromote(target, a)
                                } else {
                                    a
                                }
                            }
                            "f64" => {
                                if target != F64 {
                                    builder.ins().fdemote(target, a)
                                } else {
                                    a
                                }
                            }
                            "bool" => {
                                let value = builder.ins().f32const(0.0);
                                builder.ins().fcmp(FloatCC::NotEqual, a, value)
                            }
                            todo => todo!("{}", todo),
                        }
                    }
                    BTKind::Bool => match name {
                        "!" => {
                            let value = builder.ins().bint(I8, a);
                            builder.ins().icmp_imm(IntCC::Equal, value, 0)
                        }
                        "i64" | "u64" => builder.ins().bint(I64, a),
                        "i32" | "u32" => builder.ins().bint(I32, a),
                        "i16" | "u16" => builder.ins().bint(I16, a),
                        "i8" | "u8" => builder.ins().bint(I8, a),
                        "uint" | "int" => builder.ins().bint(types::ptr_ty(), a),
                        "f32" => {
                            let value = builder.ins().bint(I32, a);
                            builder.ins().fcvt_from_uint(F32, value)
                        }
                        "f64" => {
                            let value = builder.ins().bint(I64, a);
                            builder.ins().fcvt_from_uint(F64, value)
                        }
                        "bool" => a,
                        name => todo!("{}", name),
                    },
                };

                self.wrap_val(fun, target.unwrap(), value)
            }
            2 => {
                let ty = self.state.rfuns[fun].body.values[args[0]].ty;
                let a = self.unwrap_val(fun, args[0], builder);
                let b = self.unwrap_val(fun, args[1], builder);
                let kind = BTKind::of(ty);
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
                        "==" | "!=" => {
                            let strategy = match name {
                                "==" => IntCC::Equal,
                                "!=" => IntCC::NotEqual,
                                _ => unreachable!(),
                            };

                            let a = builder.ins().bint(I8, a);
                            let b = builder.ins().bint(I8, b);

                            builder.ins().icmp(strategy, a, b)
                        }
                        name => todo!("{:?}", name),
                    },
                };
                self.wrap_val(fun, target.unwrap(), value)
            }
            len => todo!("{}", len),
        }
    }

    fn assign_val(
        &mut self,
        fun: RFun,
        target: Value,
        source: Value,
        builder: &mut FunctionBuilder,
    ) {
        let target = &self.state.rfuns[fun].body.values[target];
        let source_v = &self.state.rfuns[fun].body.values[source];
        let ty = source_v.ty;

        debug_assert!(
            target.ty == ty,
            "{} {} {:?} {:?}",
            TypeDisplay::new(&self.state, ty),
            TypeDisplay::new(&self.state, target.ty),
            self.state.rfuns[fun].body.insts[target.inst.unwrap()].kind,
            self.state.rfuns[fun].body.insts[source_v.inst.unwrap()].kind
        );

        match target.value.clone() {
            FinalValue::StackSlot(slot) => {
                let size = self.state.types[ty].size;
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
                        let pt = types::ptr_ty();
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
                let mut value = self.unwrap_val(fun, source, builder);
                let value_type = builder.func.dfg.value_type(value);
                let val = builder.use_var(var);
                let var_type = builder.func.dfg.value_type(val);
                if value_type != var_type {
                    let mut mask = 0;
                    for i in 0..value_type.bytes() {
                        mask |= 0xFF << (i * 8);
                    }
                    mask <<= target.offset * 8;
                    mask = !mask;
                    let mask_value = builder.ins().iconst(var_type, mask);
                    let target_val = builder.ins().band(val, mask_value);
                    let source_value = builder.ins().uextend(var_type, value);
                    let source_value = builder.ins().ishl_imm(source_value, target.offset as i64 * 8);
                    value = builder.ins().bor(target_val, source_value);
                }
                builder.def_var(var, value);
            }
            FinalValue::Pointer(pointer) => {
                if source_v.value == FinalValue::Zero {
                    static_memset(
                        pointer,
                        target.offset,
                        0,
                        self.state.types[ty].size,
                        builder,
                    );
                } else {
                    let value = self.unwrap_val(fun, source, builder);
                    if source_v.on_stack {
                        static_memmove(
                            pointer,
                            target.offset,
                            value,
                            source_v.offset,
                            self.state.types[ty].size,
                            builder,
                        );
                    } else {
                        builder
                            .ins()
                            .store(MemFlags::new(), value, pointer, target.offset as i32);
                    }
                }
            }
            kind => unreachable!("{:?}", kind),
        };
    }

    fn assign_raw_val(
        &mut self,
        fun: RFun,
        target: Value,
        source: CrValue,
        builder: &mut FunctionBuilder,
    ) {
        let target = &self.state.rfuns[fun].body.values[target];

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

    fn unwrap_block(&mut self, fun: RFun, block: Inst) -> CrBlock {
        self.state.rfuns[fun].body.insts[block]
            .kind
            .block()
            .block
            .unwrap()
    }

    #[inline]
    fn wrap_val(&mut self, fun: RFun, target: Value, value: CrValue) {
        self.state.rfuns[fun].body.values[target].value = FinalValue::Value(value);
    }

    #[inline]
    fn wrap_slot(&mut self, fun: RFun, target: Value, value: StackSlot) {
        self.state.rfuns[fun].body.values[target].value = FinalValue::StackSlot(value);
    }

    #[inline]
    fn unwrap_val(&self, fun: RFun, value: Value, builder: &mut FunctionBuilder) -> CrValue {
        let value = &self.state.rfuns[fun].body.values[value];
        let ty = value.ty;
        match value.value {
            FinalValue::None => unreachable!(),
            FinalValue::Zero => {
                let repr = self.repr(ty);
                match self.state.types[ty].kind {
                    TKind::Pointer(..) => builder.ins().null(repr),
                    TKind::Structure(..) => builder.ins().iconst(repr, 0),
                    _ => match BTKind::of(ty) {
                        BTKind::Int | BTKind::Uint => builder.ins().iconst(repr, 0),
                        BTKind::Float(32) => builder.ins().f32const(0.0),
                        BTKind::Float(64) => builder.ins().f64const(0.0),
                        BTKind::Bool => builder.ins().bconst(B1, false),
                        _ => unreachable!("{}", ty),
                    },
                }
            }
            FinalValue::Value(value) => value,
            FinalValue::Var(var) => {
                let repr = self.repr(ty);
                let mut val = builder.use_var(var);
                let value_type = builder.func.dfg.value_type(val);
                if repr != value_type {
                    val = builder.ins().ushr_imm(val, value.offset as i64 * 8);
                    val = builder.ins().ireduce(repr, val);
                }
                val
            }
            FinalValue::Pointer(pointer) => {
                let wrapped_type = match self.state.types[ty].kind {
                    TKind::Pointer(inner, ..) => inner,
                    _ => unreachable!(),
                };
                if self.on_stack(wrapped_type) {
                    if value.offset != 0 {
                        let ptr_type = types::ptr_ty();
                        let offset = builder.ins().iconst(ptr_type, value.offset as i64);
                        builder.ins().iadd(pointer, offset)
                    } else {
                        pointer
                    }
                } else {
                    let repr = self.repr(wrapped_type);
                    let flags = MemFlags::new();
                    builder
                        .ins()
                        .load(repr, flags, pointer, value.offset as i32)
                }
            }
            FinalValue::StackSlot(slot) => {
                if self.on_stack(value.ty) {
                    builder
                        .ins()
                        .stack_addr(types::ptr_ty(), slot, value.offset as i32)
                } else {
                    builder
                        .ins()
                        .stack_load(self.repr(value.ty), slot, value.offset as i32)
                }
            }
        }
    }

    fn pass(&mut self, fun: RFun, from: Value, to: Value) {
        let other_value = self.state.rfuns[fun].body.values[from].value.clone();
        self.state.rfuns[fun].body.values[to].value = other_value;
    }

    #[inline]
    fn repr_of_val(&self, fun: RFun, value: Value) -> CrType {
        self.repr(self.state.rfuns[fun].body.values[value].ty)
    }

    fn on_stack(&self, ty: Type) -> bool {
        self.state.types[ty].on_stack()
    }

    fn repr(&self, ty: Type) -> CrType {
        self.state.types[ty].repr()
    }

    pub fn is_zero(&self, fun: RFun, value: Value) -> bool {
        let inst = self.state.rfuns[fun].body.values[value].inst;
        if let Some(inst) = inst {
            let inst = &self.state.rfuns[fun].body.insts[inst];
            matches!(inst.kind, IKind::ZeroValue)
        } else {
            false
        }
    }
}

pub struct GState {
    pub f_state: FState,
}

crate::inherit!(GState, f_state, FState);

impl GState {
    pub fn new(f_state: FState) -> Self {
        Self { f_state }
    }
}

pub struct GContext {
    pub data_context: DataContext,
    pub f_context: FContext,
}

crate::inherit!(GContext, f_context, FContext);

impl GContext {
    pub fn new(f_context: FContext) -> Self {
        Self {
            data_context: DataContext::new(),
            f_context,
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BTKind {
    Int,
    Uint,
    Float(u8),
    Bool,
}

impl BTKind {
    pub fn of(tp: Type) -> Self {
        match IndexPointer::raw(&tp) {
            0..=3 | 11 => Self::Int,
            4..=7 | 12 => Self::Uint,
            8 => Self::Float(32),
            9 => Self::Float(64),
            10 => Self::Bool,
            _ => panic!("cannot get builtin type of {:?}", tp),
        }
    }
}
