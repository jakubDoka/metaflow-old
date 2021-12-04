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
use cranelift_module::{Linkage, Module, DataContext, FuncOrDataId};
use std::{str::FromStr, ops::Deref};

use crate::{
    ast::Ast,
    ir::{
        BTKind, CrBlock, CrType, CrValue, CrVar, FKind, FinalValue, Fun, IKind, Inst, LTKind,
        Program, TKind, Type, Value, types::TypePrinter,
    },
    util::{storage::SymID, sdbm::SdbmHash},
};

use super::{GEKind, GenError};

type Result<T = ()> = std::result::Result<T, GenError>;

pub const STRING_SALT: u64 = 0xDEADBEEF; // just a random number

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

            if self.program[fun].import {
                continue;
            }

            let fun_id = self.program[fun].object_id.unwrap();
            ctx.func.signature = self.program[fun].final_signature.take().unwrap();
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fun_ctx);

            self.body(fun, &mut builder)?;

            builder.finalize();

            //println!("{}", ctx.func.display());

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

            debug_assert!(
                matches!(self.program[fun].body.insts[inst].kind, IKind::BlockEnd(_)),
                "next block is not a block"
            );

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

                    if let FKind::Builtin(sig) = &other.kind {
                        let return_type = sig.return_type;
                        let name = self.program[id].debug_name;
                        self.call_builtin(fun, name, return_type, &arg_buffer, value, builder);
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
                            self.program[fun].body.values[value.unwrap()].value =
                                FinalValue::StackSlot(slot);
                        }

                        let fun_ref = self
                            .program
                            .object_module
                            .declare_func_in_func(object_id, builder.func);

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
                        LTKind::String(data) => {
                            let data = data.clone();
                            let id = data.deref().sdbm_hash(STRING_SALT);
                            let mut name_buffer = std::mem::take(&mut self.context.name_buffer);
                            name_buffer.clear();
                            write_base36(id, &mut name_buffer);
                            let data_id = if let Some(FuncOrDataId::Data(data_id)) = self.program.object_module.get_name(&name_buffer) {
                                data_id
                            } else {
                                let data_id = self.program.object_module.declare_data(&name_buffer, Linkage::Export, false, false).unwrap();
                                let context = unsafe {
                                    std::mem::transmute::<_, &mut DataContext>(&mut self.context.data_context)
                                };
                                context.define(data.deref().to_owned().into_boxed_slice());
                                self.program.object_module.define_data(data_id, context).unwrap();
                                context.clear();
                                data_id
                            };
                            
                            let value = self.program.object_module.declare_data_in_func(data_id, builder.func);
                            builder.ins().global_value(self.program.isa().pointer_type(), value)
                        },
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
                IKind::Offset(other) => {
                    let other = *other;
                    self.pass(fun, other, value.unwrap())
                }
                IKind::Deref(other) => {
                    let value = value.unwrap();
                    let other = *other;
                    let val = self.unwrap_val(fun, other, builder);
                    if self.program[fun].body.values[value].on_stack {
                        self.program[fun].body.values[value].value = FinalValue::Pointer(val);
                    } else {
                        let repr = self.repr_of_val(fun, value);
                        let val = builder.ins().load(repr, MemFlags::new(), val, 0);
                        self.program[fun].body.values[value].value = FinalValue::Value(val);
                    }
                }
                IKind::Ref(val) => {
                    let val = self.unwrap_val(fun, *val, builder);
                    self.wrap_val(fun, value.unwrap(), val);
                }
                IKind::Cast(other) => {
                    let other = *other;
                    let value = value.unwrap();
                    if self.program[fun].body.values[value].on_stack {
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
        return_type: Option<Type>,
        args: &[Value],
        target: Option<Value>,
        builder: &mut FunctionBuilder,
    ) {
        match args.len() {
            1 => {
                let val = &self.program[fun].body.values[args[0]];
                let datatype = val.datatype;
                let a = self.unwrap_val(fun, args[0], builder);
                let kind = BTKind::of(datatype);
                let repr = self.repr_of(datatype);

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
                            let to = self.repr_of(return_type.unwrap());
                            match to.bytes().cmp(&repr.bytes()) {
                                std::cmp::Ordering::Less => builder.ins().ireduce(to, a),
                                std::cmp::Ordering::Equal => a,
                                std::cmp::Ordering::Greater => builder.ins().sextend(to, a),
                            }
                        }
                        ("u8" | "u16" | "u32" | "u64" | "uint", _) => {
                            let to = self.repr_of(return_type.unwrap());
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
                                let to = self.repr_of(return_type.unwrap());
                                builder.ins().fcvt_to_uint(to, a)
                            }
                            "i8" | "i16" | "i32" | "i64" | "int" => {
                                let to = self.repr_of(return_type.unwrap());
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
                        "uint" | "int" => {
                            builder.ins().bint(self.program.isa().pointer_type(), a)
                        }
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

            write_base36(fun_id, &mut name_buffer);

            let (linkage, alias) = if let Some(attr) = self.program.get_attr(fun, "linkage") {
                assert_attr_len(attr, 1)?;

                let linkage = match attr[1].token.spam.raw() {
                    "import" => Linkage::Import,
                    "local" => Linkage::Local,
                    "export" => Linkage::Export,
                    "preemptible" => Linkage::Preemptible,
                    "hidden" => Linkage::Hidden,
                    _ => return Err(GenError::new(GEKind::InvalidLinkage, &attr.token)),
                };

                if attr.len() > 2 {
                    (linkage, attr[2].token.spam.raw())
                } else if linkage == Linkage::Import {
                    (linkage, self.program[fun].debug_name)
                } else {
                    (linkage, &name_buffer[..])
                }
            } else {
                (Linkage::Export, &name_buffer[..])
            };

            if linkage == Linkage::Import {
                self.program[fun].import = true;
            }

            let call_conv = if let Some(attr) = self.program.get_attr(fun, "call_conv") {
                assert_attr_len(attr, 1)?;
                let conv = attr[1].token.spam.raw();
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
                "main"
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

        let type_printer = TypePrinter::new(self.program);

        debug_assert!(
            target.datatype == datatype, 
            "{} {} {:?} {:?}", 
            type_printer.print(datatype), 
            type_printer.print(target.datatype),
            self.program[fun].body.insts[target.inst.unwrap()].kind,
            self.program[fun].body.insts[source_v.inst.unwrap()].kind

        );

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
            FinalValue::Pointer(pointer) => {
                if source_v.value == FinalValue::Zero {
                    static_memset(pointer, target.offset, 0, self.program[datatype].size, builder);
                } else  {
                    let value = self.unwrap_val(fun, source, builder);
                    if source_v.on_stack {
                        static_memmove(
                            pointer,
                            target.offset,
                            value,
                            source_v.offset,
                            self.program[datatype].size,
                            builder,
                        );
                    } else {
                        builder.ins().store(MemFlags::new(), value, pointer, target.offset as i32);
                    }
                } 
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

    pub fn is_zero(&self, fun: Fun, value: Value) -> bool {
        let inst = self.program[fun].body.values[value].inst;
        if let Some(inst) = inst {
            let inst = &self.program[fun].body.insts[inst];
            matches!(inst.kind, IKind::ZeroValue)
        } else {
            false
        }
    }
}

pub fn assert_attr_len(attr: &Ast, len: usize) -> Result {
    if attr.len() - 1 < len {
        Err(GenError::new(
            GEKind::TooShortAttribute(attr.len(), len),
            &attr.token,
        ))
    } else {
        Ok(())
    }
}

pub struct GeneratorContext {
    pub data_context: DataContext,
    pub call_buffer: Vec<CrValue>,
    pub block_buffer: Vec<(Inst, CrBlock)>,
    pub arg_buffer: Vec<Value>,
    pub name_buffer: String,
}

impl Default for GeneratorContext {
    fn default() -> Self {
        Self {
            data_context: DataContext::new(),
            arg_buffer: vec![],
            call_buffer: vec![],
            block_buffer: vec![],
            name_buffer: String::new(),
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

fn write_base36(mut number: u64, buffer: &mut String) {
    while number > 0 {
        let mut digit = (number % 36) as u8;
        digit += (digit < 10) as u8 * b'0' + (digit >= 10) as u8 * (b'a' - 10);
        buffer.push(digit as char);
        number /= 36;
    }
}