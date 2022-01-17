use cranelift::codegen::binemit::NullTrapSink;
use cranelift::codegen::ir::AbiParam;
use cranelift::frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift::module::{DataContext, DataId, FuncOrDataId, Linkage, Module, RelocRecord, ModuleDeclarations};
use cranelift::object::ObjectModule;
use cranelift::{
    codegen::{
        binemit::RelocSink,
        binemit::{Addend, CodeOffset, NullStackMapSink, Reloc, TrapSink},
        entity::EntityRef,
        ir::{
            condcodes::{FloatCC, IntCC},
            types::*,
            Block, ExternalName, FuncRef, GlobalValue, Inst, InstBuilder, MemFlags, SigRef,
            Signature as CrSignature, SourceLoc, StackSlot, StackSlotData, StackSlotKind, TrapCode,
            Type, Value,
        },
        isa::CallConv as CrCallConv,
        packed_option::{PackedOption, ReservedValue},
        Context,
    },
    entity::{SecondaryMap, SparseMap, SparseMapValue},
    module::FuncId,
};
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use std::ops::{Deref, DerefMut};

use crate::entities::{BlockEnt, BUILTIN_MODULE, TKind, CrTypeWr, TypeEnt};
use crate::{
    entities::{Fun, IKind, InstEnt, Mod, Ty, ValueEnt},
    functions::{FContext, FKind, FParser, FState, FunEnt, GlobalEnt},
    lexer::{Span, TKind as LTKind, Token},
    types::TypeDisplay,
    util::{
        sdbm::{SdbmHash, ID},
        storage::Map,
        write_radix, Size,
    },
};

use super::{GEKind, GError};

type Result<T = ()> = std::result::Result<T, GError>;

pub const STRING_SALT: u64 = 0xDEADBEEF; // just a random number

pub struct Generator<'a> {
    module: &'a mut ObjectModule,
    state: &'a mut GState,
    context: &'a mut GContext,
    s32: bool,
    jit: bool,
    ptr_ty: Type,
}

crate::inherit!(Generator<'_>, state, GState);

impl<'a> Generator<'a> {
    pub fn new(
        module: &'a mut ObjectModule,
        state: &'a mut GState,
        context: &'a mut GContext,
        jit: bool,
    ) -> Self {
        // TODO: move this to better place so we don't repeat it pointlessly
        let ptr_ty = module.isa().pointer_type();
        let int = state.builtin_repo.int;
        let uint = state.builtin_repo.uint;
        state.types[int].kind = TKind::Builtin(CrTypeWr(ptr_ty));
        state.types[uint].kind = TKind::Builtin(CrTypeWr(ptr_ty));

        Self {
            jit,
            s32: ptr_ty.bytes() == 4,
            ptr_ty,
            module,
            state,
            context,
        }
    }

    pub fn generate(&mut self, order: &[Mod]) -> Result {
        let mut declarations = std::mem::take(&mut self.state.bin_declarations);
        for &module in order {
            if self.modules[module].clean {
                continue;
            }
            
            // remove types
            if module != BUILTIN_MODULE {
                let mut types = std::mem::take(&mut self.modules[module].types);
                for ty in types.drain(..) {
                    let id = self.types[ty].id;
                    self.types.remove(id);
                }
                self.modules[module].types = types;
            }
            
            // remove functions
            let mut funs = std::mem::take(&mut self.modules[module].functions);
            for fun in funs.drain(..) {
                let id = self.funs[fun].id;
                self.funs.remove(id);
                declarations.remove_function(self.compiled_funs[fun].id);
            }
            self.modules[module].functions = funs;
    
            // remove globals
            let mut globals = std::mem::take(&mut self.modules[module].globals);
            for global in globals.drain(..) {
                let id = self.globals[global].id;
                self.globals.remove(id);
                declarations.remove_data(self.compiled_globals[global].id);
            }
            self.modules[module].globals = globals;

            // remove strings
            let mut strings = std::mem::take(&mut self.modules[module].strings);
            for (id, _) in strings.drain(..) {
                declarations.remove_data(id);
            }
            self.modules[module].strings = strings;
        }

        self.module.load_declarations(declarations);

        for &module in order.iter() {
            let module_ent = &mut self.modules[module];
            if module_ent.clean {
                let functions = std::mem::take(&mut module_ent.functions);
                let globals = std::mem::take(&mut module_ent.globals);
                let strings = std::mem::take(&mut module_ent.strings);

                self.load_funs(&functions);
                self.load_globals(&globals);
                self.load_strings(&strings);

                let module_ent = &mut self.modules[module];
                module_ent.functions = functions;
                module_ent.globals = globals;
                module_ent.strings = strings;
                continue;
            } else {
                module_ent.clean = true;
            }

            FParser::new(self.state, self.context, self.ptr_ty)
                .parse(module)
                .map_err(|err| GError::new(GEKind::FError(err), Token::default()))?;
            
            let mut represented = std::mem::take(&mut self.context.represented);
            self.declare_funs(&represented);
            
            let mut resolved_globals = std::mem::take(&mut self.context.resolved_globals);
            self.declare_and_define_globals(&resolved_globals);
            resolved_globals.clear();
            self.context.resolved_globals = resolved_globals;
            
            self.define_funs(&represented);
            represented.clear();
            self.context.represented = represented;
        }

        self.finalize(order);

        self.state.bin_declarations = self.module.take_declarations();

        Ok(())
    }

    pub fn load_strings(&mut self, strings: &[(DataId, Span)]) {
        for &(id, span) in strings {
            let data = self.state.display(&span);
            self.context.data_context.define(data.deref().as_bytes().to_owned().into_boxed_slice());
            self.module.define_data(id, &self.context.data_context).unwrap();
            self.context.data_context.clear();
        }
    }

    pub fn load_globals(&mut self, globals: &[GlobalValue]) {
        for &global in globals {
            let GlobalEnt { ty, linkage, .. } = self.globals[global];
            if linkage == Linkage::Import {
                continue;
            }
            let id = self.compiled_globals[global].id;
            self.context
                .data_context
                .define_zeroinit(self.types[ty].size.pick(self.s32) as usize);
            self.module.define_data(id, &self.context.data_context).unwrap();
            self.context.data_context.clear();
        }
    }

    pub fn load_funs(&mut self, functions: &[Fun]) {
        for &fun_id in functions {
            let FunEnt {
                linkage,
                body,
                kind,
                ..
            } = self.funs[fun_id];
            
            if linkage == Linkage::Import || kind != FKind::Represented || body.entry_block.is_none() {
                continue;
            }

            let data = std::mem::take(&mut self.compiled_funs[fun_id]);

            if self.jit {
                let jit_data = std::mem::take(self.jit_funs.get_mut(fun_id).unwrap());
                self.module.define_function_bytes(
                    data.id, 
                    &jit_data.bin.bytes, 
                    &jit_data.bin.relocs
                ).unwrap();
                self.jit_funs.insert(jit_data);
            } else {
                self.module.define_function_bytes(
                    data.id, 
                    &data.bin.bytes, 
                    &data.bin.relocs
                ).unwrap();
            }

            self.compiled_funs[fun_id] = data;
        }
    }

    pub fn finalize(&mut self, order: &[Mod]) {
        let mut context = Context::new();
        context.func.signature = CrSignature {
            params: vec![AbiParam::new(self.ptr_ty), AbiParam::new(self.ptr_ty)],
            returns: vec![AbiParam::new(self.ptr_ty)],
            call_conv: self.module.isa().default_call_conv(),
        };
        let mut f_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut f_context);
        let entry_block = builder.create_block();
        builder.switch_to_block(entry_block);
        builder.append_block_params_for_function_params(entry_block);
        let args = builder.block_params(entry_block);
        let (arg1, arg2) = (args[0], args[1]);
        
        let mut return_value = None;

        for &module in order {
            let module_ent = &self.modules[module];
            let id = self.compiled_funs[module_ent.entry_point.unwrap()].id;
            let func_id = self.module.declare_func_in_func(id, builder.func);
            let inst = builder.ins().call(func_id, &[arg1, arg2]);
            return_value = Some(builder.inst_results(inst)[0]);
        }

        let return_value = return_value
            .unwrap_or_else(|| builder.ins().iconst(self.ptr_ty, 0));

        builder.ins().return_(&[return_value]);

        builder.seal_block(entry_block);

        builder.finalize();

        let id = self.module.declare_function("main", Linkage::Export, &context.func.signature)
            .unwrap();
        
        self.module.define_function(
            id,
            &mut context,
            &mut NullTrapSink::default(),
            &mut NullStackMapSink {}
        ).unwrap();
    }

    fn declare_funs(&mut self, represented: &Vec<Fun>) {
        let mut signature = CrSignature::new(CrCallConv::Fast);
        let mut name = String::new();

        for &fun_id in represented {
            let FunEnt {
                id,
                sig,
                module,
                alias,
                linkage,
                kind,
                ..
            } = self.state.funs[fun_id];

            if kind != FKind::Represented {
                continue;
            }

            signature.clear(CrCallConv::Fast);
            sig.to_cr_signature(module, self.state, self.module.isa(), &mut signature);

            name.clear();
            write_radix(id.0, 16, &mut name);

            let final_name = if let Some(alias) = alias {
                self.state.display(&alias)
            } else {
                &name
            };

            if final_name == "main" {
                todo!();
            }

            let id = self
                .module
                .declare_function(final_name, linkage, &signature)
                .unwrap();

            self.compiled_funs[fun_id].id = id;
        }
    }

    fn declare_and_define_globals(&mut self, resolved: &[GlobalValue]) {
        let mut name = String::new();
        for &global in resolved {
            let GlobalEnt {
                id,
                module,
                ty,
                linkage,
                alias,
                attrs,
                mutable,
                ..
            } = self.globals[global];

            let tls = self.modules[module].attr(attrs, ID::new("tls")).is_some();

            name.clear();
            write_radix(id.0, 36, &mut name);

            let final_name = if let Some(alias) = alias {
                self.state.display(&alias)
            } else {
                &name
            };

            let id = self
                .module
                .declare_data(final_name, linkage, mutable, tls)
                .unwrap();
            
            self.compiled_globals[global].id = id;
            
            if linkage == Linkage::Import {
                continue;
            }


            self.context
                .data_context
                .define_zeroinit(self.types[ty].size.pick(self.s32) as usize);
            self.module.define_data(id, &self.context.data_context).unwrap();
            self.context.data_context.clear();
        }
    }

    fn define_funs(&mut self, represented: &[Fun]) {
        let mut reloc_sink = MetaRelocSink::new();
        let mut fun_ctx = FunctionBuilderContext::new();
        let mut ctx = Context::new();

        for &fun_id in represented {
            crate::test_println!("{}", crate::functions::FunDisplay::new(&self.state, fun_id));

            self.context.imported_funs.clear();
            self.context.imported_globals.clear();
            self.context.imported_signatures.clear();

            let FunEnt { sig, module, linkage, body, kind, .. } = self.state.funs[fun_id];

            if linkage == Linkage::Import || kind != FKind::Represented || body.entry_block.is_none() {
                continue;
            }

            sig.to_cr_signature(
                module,
                self.state,
                self.module.isa(),
                &mut ctx.func.signature,
            );

            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fun_ctx);

            self.body(fun_id, &mut builder);

            builder.finalize();

            crate::test_println!("{}", ctx.func.display());

            let mut bytes = vec![];

            ctx.compile_and_emit(
                self.module.isa(),
                &mut bytes,
                &mut reloc_sink,
                &mut MetaTrapSink {},
                &mut NullStackMapSink {},
            )
            .unwrap();

            let id = self.compiled_funs[fun_id].id;

            self.module
                .define_function_bytes(id, &bytes, &reloc_sink.relocs)
                .unwrap();

            if self.jit {
                self.jit_funs.insert(JFun {
                    id: fun_id,
                    bin: CompiledData {
                        bytes,
                        relocs: unsafe { std::mem::transmute(reloc_sink.relocs.clone()) },
                    },
                });
            } else {
                self.compiled_funs[fun_id] = CFun {
                    bin: CompiledData {
                        bytes,
                        relocs: unsafe { std::mem::transmute(reloc_sink.relocs.clone()) },
                    },
                    id,
                };
            }

            ctx.clear();
            reloc_sink.clear();
        }
    }

    fn body(&mut self, fun: Fun, builder: &mut FunctionBuilder) {
        let entry_block = self.funs[fun].body.entry_block;

        self.load_blocks(fun, None, builder);

        let mut arg_buffer = self.context.pool.get();
        let mut inline_stack = self.context.pool.get();
        inline_stack.push((
            fun,
            entry_block,
            Option::<Block>::None,
            Option::<Inst>::None,
        ));

        let mut bail = false;
        while let Some((fun, raw_block, return_block, raw_inst)) = inline_stack.last_mut() {
            let module = self.funs[*fun].module;
            if raw_block.is_none() {
                if let &mut Some(return_block) = return_block {
                    builder.switch_to_block(return_block)
                }
                inline_stack.pop().unwrap();
                if !inline_stack.is_empty() {
                    self.context.bail();
                }
                bail = true;
                continue;
            }

            let block = raw_block.unwrap();
            let BlockEnt {
                start,
                next,
                ..
            } = self.modules[module].blocks[block];
            let inst = if raw_inst.is_some() {
                let inst = raw_inst.unwrap();
                *raw_inst = None;
                self.modules[module].insts[inst].next.unwrap()
            } else {
                start.unwrap()
            };
            
            if !bail {
                builder.switch_to_block(self.context.block(block));
            }
            bail = false;

            let inst = self.block(module, inst, *return_block, true, builder);
            if let Some(inst) = inst {
                let module_ent = &self.state.modules[module];
                let inst_ent = &module_ent.insts[inst];
                let (fun, args) = match inst_ent.kind {
                    IKind::Call(id, args) => (id, args),
                    _ => unreachable!(),
                };
                let return_block = *return_block;
                if inline_stack.iter().any(|e| e.0 == fun) {
                    self.block(module, inst, return_block, false, builder);
                    inline_stack.last_mut().unwrap().1 = next;
                    continue;
                }
                let value = inst_ent.value;
                let entry_block = builder.create_block();
                arg_buffer.clear();
                arg_buffer.extend(
                    module_ent
                        .values(args)
                        .iter()
                        .map(|&a| self.unwrap_val(module, a, builder)),
                );
                builder.ins().jump(entry_block, arg_buffer.as_slice());
                let return_block = builder.create_block();
                if value.is_some() {
                    let value = value.unwrap();
                    let ty = module_ent.type_of_value(value);
                    let repr = self.types[ty].to_cr_type(self.module.isa());
                    let return_value = builder.append_block_param(return_block, repr);
                    self.context
                        .set_value(value, FinalValue::Value(return_value));
                }
                self.context.dive();
                self.load_blocks(fun, Some(entry_block), builder);
                let entry_block = self.funs[fun].body.entry_block;
                inline_stack.last_mut().unwrap().3 = Some(inst);
                inline_stack.push((
                    fun,
                    entry_block,
                    Some(return_block),
                    None,
                ));
            } else {
                *raw_block = next;
            }
        }

        builder.seal_all_blocks();
    }

    fn load_blocks(
        &mut self,
        fun_id: Fun,
        mut injected: Option<Block>,
        builder: &mut FunctionBuilder,
    ) {
        let FunEnt { module, body, .. } = self.state.funs[fun_id];
        let module_ent = &self.state.modules[module];

        let mut current = body.entry_block;
        while current.is_some() {
            let cur = current.unwrap();
            let block = injected.take().unwrap_or_else(|| builder.create_block());
            let block_ent = &module_ent.blocks[cur];
            let args = module_ent.block_args(cur);

            for &arg in args {
                let ty = module_ent.type_of_value(arg);
                let ty = self.types[ty].to_cr_type(self.module.isa());
                let value = builder.append_block_param(block, ty);
                self.context.set_value(arg, FinalValue::Value(value));
            }

            self.context.set_block(cur, block);
            current = block_ent.next;
        }
    }

    fn block(
        &mut self,
        module: Mod,
        from: Inst,
        return_block: Option<Block>,
        can_inline: bool,
        builder: &mut FunctionBuilder,
    ) -> Option<Inst> {
        let mut call_buffer = self.context.pool.get();
        let mut arg_buffer = self.context.pool.get();

        let mut current = PackedOption::from(from);

        while current.is_some() {
            let module_ent = &self.modules[module];
            let InstEnt {
                value, next, kind, ..
            } = module_ent.insts[current.unwrap()];

            match kind {
                IKind::Call(id, args) => {
                    let FunEnt {
                        module: other_module,
                        name,
                        sig,
                        kind,
                        inline,
                        ..
                    } = self.funs[id];

                    arg_buffer.clear();
                    arg_buffer.extend_from_slice(module_ent.values(args));

                    if let FKind::Builtin = kind {
                        let name = name.clone();
                        let return_type = sig.ret;
                        self.call_builtin(module, name, return_type, &arg_buffer, value, builder);
                    } else if other_module == Mod::new(0)
                        && matches!(self.state.display(&name), "sizeof")
                    {
                        self.call_generic_builtin(id, &arg_buffer, value, builder);
                    } else {
                        let inline = inline && can_inline;
                        let fun_id = self.compiled_funs[id].id;
                        let map_id = ID(fun_id.as_u32() as u64);

                        let mut struct_return = false;

                        if sig.ret.is_some() {
                            let ret_ty = sig.ret.unwrap();
                            if self.on_stack(ret_ty) {
                                let size = self.types[ret_ty].size;
                                let last = arg_buffer[arg_buffer.len() - 1];
                                let data = StackSlotData::new(
                                    StackSlotKind::ExplicitSlot,
                                    align(size.pick(self.s32)),
                                );
                                let slot = builder.create_stack_slot(data);
                                self.context.set_value(last, FinalValue::StackSlot(slot));
                                self.context
                                    .set_value(value.unwrap(), FinalValue::StackSlot(slot));
                                struct_return = true;
                            }
                        }

                        if inline {
                            return Some(current.unwrap());
                        } else {
                            let fun_ref =
                                if let Some(&fun_ref) = self.context.imported_funs.get(map_id) {
                                    fun_ref
                                } else {
                                    let fun_ref =
                                        self.module.declare_func_in_func(fun_id, builder.func);
                                    self.context.imported_funs.insert(map_id, fun_ref);
                                    fun_ref
                                };

                            call_buffer.clear();
                            call_buffer.extend(
                                arg_buffer
                                    .iter()
                                    .map(|&a| self.unwrap_val(module, a, builder)),
                            );

                            let inst = builder.ins().call(fun_ref, &call_buffer);

                            if !struct_return {
                                if value.is_some() {
                                    let val = builder.inst_results(inst)[0];
                                    self.context
                                        .set_value(value.unwrap(), FinalValue::Value(val));
                                }
                            }
                        }
                    }
                }
                IKind::VarDecl(init) => {
                    let value = value.unwrap();
                    let ValueEnt {
                        on_stack, mutable, ty, ..
                    } = module_ent.values[value];
                    let size = self.types[ty].size.pick(self.s32);
                    if on_stack || self.on_stack(ty) {
                        let data = StackSlotData::new(StackSlotKind::ExplicitSlot, align(size));
                        let slot = builder.create_stack_slot(data);
                        self.context.set_value(value, FinalValue::StackSlot(slot));
                        self.assign_val(module, value, init, builder)
                    } else if mutable {
                        let var = Variable::new(value.index());
                        self.context.set_value(value, FinalValue::Var(var));
                        builder.declare_var(var, self.repr(ty));
                        self.assign_val(module, value, init, builder);
                    } else {
                        let val = self.unwrap_val(module, init, builder);
                        self.context.set_value(value, FinalValue::Value(val));
                    }
                }
                IKind::Zeroed => {
                    self.context.set_value(value.unwrap(), FinalValue::Zero);
                }
                IKind::Uninitialized => {
                    let value = value.unwrap();
                    let ty = module_ent.type_of_value(value);
                    if self.on_stack(ty) {
                        let size = self.types[ty].size.pick(self.s32);
                        let data = StackSlotData::new(StackSlotKind::ExplicitSlot, align(size));
                        let slot = builder.create_stack_slot(data);
                        self.context.set_value(value, FinalValue::StackSlot(slot));
                    } else {
                        self.context.set_value(value, FinalValue::Zero);
                    }
                }
                IKind::Lit(lit) => {
                    let value = value.unwrap();
                    let ty = module_ent.type_of_value(value);
                    let repr = self.repr(ty);
                    let lit = match lit {
                        LTKind::Int(val, _) => builder.ins().iconst(repr, val),
                        LTKind::Uint(val, _) => builder.ins().iconst(repr, val as i64),
                        LTKind::Float(val, _) => {
                            if repr == F32 {
                                builder.ins().f32const(val as f32)
                            } else {
                                builder.ins().f64const(val)
                            }
                        }
                        LTKind::Bool(val) => builder.ins().bconst(B1, val),
                        LTKind::Char(val) => builder.ins().iconst(I32, val as i64),
                        LTKind::String(string) => {
                            let data = unsafe {
                                std::mem::transmute::<&[u8], &[u8]>(
                                    self.state.display(&string).as_bytes(),
                                )
                            };
                            let (data, new) = self.make_static_data(data, false, false);
                            if new { // we don't want duplicates
                                self.modules[module].strings.push((data, string));
                            }
                            let map_id = ID(data.as_u32() as u64);
                            let value = if let Some(&value) =
                                self.context.imported_globals.get(map_id)
                            {
                                value
                            } else {
                                let value = self.module.declare_data_in_func(data, builder.func);
                                self.context.imported_globals.insert(map_id, value);
                                value
                            };
                            builder.ins().global_value(repr, value)
                        }
                        lit => todo!("{:?}", lit),
                    };
                    self.context.set_value(value, FinalValue::Value(lit));
                }
                IKind::Return(value) => {
                    if let Some(return_block) = return_block {
                        if value.is_some() {
                            let value = self.unwrap_val(module, value.unwrap(), builder);
                            builder.ins().jump(return_block, &[value]);
                        } else {
                            builder.ins().jump(return_block, &[]);
                        }
                    } else {                        
                        if value.is_some() {
                            let value = self.unwrap_val(module, value.unwrap(), builder);
                            builder.ins().return_(&[value]);
                        } else {
                            builder.ins().return_(&[]);
                        }
                    }
                }
                IKind::Assign(other) => {
                    self.assign_val(module, other, value.unwrap(), builder);
                }
                IKind::Jump(block, values) => {
                    call_buffer.clear();
                    call_buffer.extend(
                        module_ent
                            .values(values)
                            .iter()
                            .map(|&a| self.unwrap_val(module, a, builder)),
                    );
                    let block = self.context.block(block);
                    builder.ins().jump(block, &call_buffer);
                }
                IKind::JumpIfTrue(condition, block, values) => {
                    call_buffer.clear();
                    call_buffer.extend(
                        module_ent
                            .values(values)
                            .iter()
                            .map(|&a| self.unwrap_val(module, a, builder)),
                    );
                    let block = self.context.block(block);
                    let value = self.unwrap_val(module, condition, builder);
                    builder.ins().brnz(value, block, &call_buffer);
                }
                IKind::Offset(other) => self.pass(other, value.unwrap()),
                IKind::Deref(other, assign) => {
                    let value = value.unwrap();
                    let val = self.unwrap_val_low(module, other, builder, assign);
                    self.context.set_value(value, FinalValue::Pointer(val));
                }
                IKind::Ref(val) => {
                    let val = self.unwrap_val_low(module, val, builder, true);
                    self.context
                        .set_value(value.unwrap(), FinalValue::Value(val));
                }
                IKind::Cast(other) => {
                    let value = value.unwrap();
                    let ValueEnt { on_stack, ty, .. } = module_ent.values[value];
                    if on_stack || self.on_stack(ty) {
                        self.pass(other, value);
                    } else {
                        let target = self.repr(ty);
                        let other_ty = self.repr(module_ent.values[other].ty);
                        if other_ty != target {
                            let other_value = self.unwrap_val(module, other, builder);
                            let val = builder.ins().bitcast(target, other_value);
                            self.context.set_value(value, FinalValue::Value(val));
                        } else {
                            self.pass(other, value);
                        }
                    }
                }
                IKind::GlobalLoad(global) => {
                    let id = self.compiled_globals[global].id;
                    let ty = self.globals[global].ty;
                    let map_id = ID(id.as_u32() as u64);

                    let data = if let Some(&data) = self.context.imported_globals.get(map_id) {
                        data
                    } else {
                        let data = self.module.declare_data_in_func(id, builder.func);
                        self.context.imported_globals.insert(map_id, data);
                        data
                    };
                    let val = builder.ins().global_value(self.repr(ty), data);
                    self.context
                        .set_value(value.unwrap(), FinalValue::Pointer(val))
                }
                IKind::FunPointer(id) => {
                    let fun_id = self.compiled_funs[id].id;
                    let map_id = ID(fun_id.as_u32() as u64);

                    let fun_ref = if let Some(&fun_ref) = self.context.imported_funs.get(map_id) {
                        fun_ref
                    } else {
                        let fun_ref = self.module.declare_func_in_func(fun_id, builder.func);
                        self.context.imported_funs.insert(map_id, fun_ref);
                        fun_ref
                    };

                    let pointer = builder.ins().func_addr(self.ptr_ty, fun_ref);

                    self.context
                        .set_value(value.unwrap(), FinalValue::Value(pointer));
                }
                IKind::FunPointerCall(pointer, args) => {
                    let pointer_type = module_ent.type_of_value(pointer);
                    let pointer = self.unwrap_val(module, pointer, builder);
                    call_buffer.clear();
                    call_buffer.extend(
                        module_ent
                            .values(args)
                            .iter()
                            .map(|&a| self.unwrap_val(module, a, builder)),
                    );

                    let mut struct_return = false;
                    if value.is_some() {
                        let value = value.unwrap();
                        let ret_ty = module_ent.type_of_value(value);
                        if self.on_stack(ret_ty) {
                            let size = self.types[ret_ty].size.pick(self.s32);
                            let last = arg_buffer[arg_buffer.len() - 1];
                            let data = StackSlotData::new(StackSlotKind::ExplicitSlot, align(size));
                            let slot = builder.create_stack_slot(data);
                            self.context.set_value(last, FinalValue::StackSlot(slot));
                            self.context.set_value(value, FinalValue::StackSlot(slot));
                            struct_return = true;
                        }
                    }

                    let TypeEnt {
                        id,
                        kind,
                        module: ptr_module,
                        ..
                    } = &self.types[pointer_type];
                    let id = *id;
                    let sig = if let Some(&sig) = self.context.imported_signatures.get(id) {
                        sig
                    } else {
                        let ptr_ty = kind.fun_pointer();
                        let mut sig = CrSignature::new(CrCallConv::Fast);
                        ptr_ty.to_cr_signature(
                            *ptr_module,
                            self.state,
                            self.module.isa(),
                            &mut sig,
                        );
                        let sig = builder.import_signature(sig);

                        self.context.imported_signatures.insert(id, sig);
                        sig
                    };

                    let call = builder.ins().call_indirect(sig, pointer, &call_buffer);
                    if !struct_return {
                        if value.is_some() {
                            self.context.set_value(
                                value.unwrap(),
                                FinalValue::Value(builder.inst_results(call)[0]),
                            );
                        }
                    }
                }
                value => unreachable!("{:?}", value),
            }

            current = next;
        }

        None
    }

    fn call_generic_builtin(
        &mut self,
        other: Fun,
        _args: &[Value],
        target: PackedOption<Value>,
        builder: &mut FunctionBuilder,
    ) {
        let FunEnt {
            name,
            module,
            params,
            ..
        } = self.state.funs[other];
        let module_ent = &self.modules[module];
        match self.state.display(&name) {
            "sizeof" => {
                let value = target.unwrap();
                let size = self.types[module_ent.type_slice(params)[0]]
                    .size
                    .pick(self.s32);
                let size = builder.ins().iconst(self.ptr_ty, size as i64);
                self.context.set_value(value, FinalValue::Value(size));
            }
            name => unreachable!("{}", name),
        }
    }

    fn call_builtin(
        &mut self,
        module: Mod,
        name: Span,
        return_type: PackedOption<Ty>,
        args: &[Value],
        target: PackedOption<Value>,
        builder: &mut FunctionBuilder,
    ) {
        let module_ent = &self.modules[module];
        let name = self.state.display(&name);
        match args.len() {
            1 => {
                let a = self.unwrap_val(module, args[0], builder);
                let val = &module_ent.values[args[0]];
                let ty = val.ty;
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
                                self.assign_raw_val(module, args[0], value, builder)
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
                        "uint" | "int" => builder.ins().bint(self.ptr_ty, a),
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

                self.context
                    .set_value(target.unwrap(), FinalValue::Value(value));
            }
            2 => {
                let ty = module_ent.type_of_value(args[0]);
                let a = self.unwrap_val(module, args[0], builder);
                let b = self.unwrap_val(module, args[1], builder);
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
                self.context
                    .set_value(target.unwrap(), FinalValue::Value(value));
            }
            len => todo!("{}", len),
        }
    }

    fn assign_val(
        &self,
        module: Mod,
        target_value: Value,
        source_value: Value,
        builder: &mut FunctionBuilder,
    ) {
        let module_ent = &self.modules[module];

        let target = module_ent.values[target_value];
        let final_target_value = self.context.value(target_value);
        let source = module_ent.values[source_value];
        let final_source_value = self.context.value(source_value);
        let ty = source.ty;

        debug_assert!(
            target.ty == ty,
            "{} {} {:?} {:?}",
            TypeDisplay::new(&self.state, ty),
            TypeDisplay::new(&self.state, target.ty),
            target,
            module_ent.insts[source.inst.unwrap()].kind
        );

        match final_target_value {
            FinalValue::StackSlot(slot) => {
                let size = self.types[ty].size.pick(self.s32);
                match final_source_value {
                    FinalValue::Zero => {
                        println!("{}", size);
                        static_stack_memset(slot, target.offset.pick(self.s32), 0, size, builder)
                    }
                    FinalValue::Value(value) => {
                        let value = if target.ty == self.state.builtin_repo.bool {
                            builder.ins().bint(I8, value)
                        } else {
                            value
                        };
                        builder
                            .ins()
                            .stack_store(value, slot, target.offset.pick(self.s32) as i32);
                    }
                    FinalValue::Var(var) => {
                        let value = builder.use_var(var);
                        let value = if target.ty == self.state.builtin_repo.bool {
                            builder.ins().bint(I8, value)
                        } else {
                            value
                        };
                        builder
                            .ins()
                            .stack_store(value, slot, target.offset.pick(self.s32) as i32);
                    }
                    FinalValue::StackSlot(other) => static_stack_memmove(
                        slot,
                        target.offset.pick(self.s32),
                        other,
                        source.offset.pick(self.s32),
                        size,
                        builder,
                    ),
                    FinalValue::Pointer(pointer) => {
                        let pt = self.ptr_ty;
                        let target_ptr = builder.ins().stack_addr(pt, slot, 0);
                        static_memmove(
                            target_ptr,
                            target.offset.pick(self.s32),
                            pointer,
                            source.offset.pick(self.s32),
                            size,
                            builder,
                        )
                    }
                    FinalValue::None => unreachable!(),
                }
            }
            FinalValue::Var(var) => {
                let mut value = self.unwrap_val(module, source_value, builder);
                let value_type = builder.func.dfg.value_type(value);
                let val = builder.use_var(var);
                let var_type = builder.func.dfg.value_type(val);
                if value_type != var_type {
                    let mut mask = 0i64;
                    for i in 0..value_type.bytes() {
                        mask |= 0xFF << (i * 8);
                    }
                    mask <<= target.offset.pick(self.s32) * 8;
                    mask = !mask;
                    let mask_value = builder.ins().iconst(var_type, mask);
                    let target_val = builder.ins().band(val, mask_value);
                    let source_value = builder.ins().uextend(var_type, value);
                    let source_value = builder
                        .ins()
                        .ishl_imm(source_value, target.offset.pick(self.s32) as i64 * 8);
                    value = builder.ins().bor(target_val, source_value);
                }
                builder.def_var(var, value);
            }
            FinalValue::Pointer(pointer) => {
                if final_source_value == FinalValue::Zero {
                    static_memset(
                        pointer,
                        target.offset.pick(self.s32),
                        0,
                        self.types[ty].size.pick(self.s32),
                        builder,
                    );
                } else {
                    let mut value = self.unwrap_val(module, source_value, builder);
                    if source.on_stack || self.on_stack(source.ty) {
                        static_memmove(
                            pointer,
                            target.offset.pick(self.s32),
                            value,
                            source.offset.pick(self.s32),
                            self.types[ty].size.pick(self.s32),
                            builder,
                        );
                    } else {
                        if target.ty == self.state.builtin_repo.bool {
                            value = builder.ins().bint(I8, value)
                        }
                        builder.ins().store(
                            MemFlags::new(),
                            value,
                            pointer,
                            target.offset.pick(self.s32) as i32,
                        );
                    }
                }
            }
            kind => {
                unreachable!("{:?} {:?}", kind, target_value)
            }
        };
    }

    fn assign_raw_val(
        &mut self,
        module: Mod,
        target: Value,
        mut source: Value,
        builder: &mut FunctionBuilder,
    ) {
        let target_value = self.context.value(target);
        let target = &self.modules[module].values[target];

        match target_value {
            FinalValue::StackSlot(slot) => {
                if target.ty == self.state.builtin_repo.bool {
                    source = builder.ins().bint(I8, source)
                }
                builder
                    .ins()
                    .stack_store(source, slot, target.offset.pick(self.s32) as i32);
            }
            FinalValue::Pointer(pointer) => {
                if target.ty == self.state.builtin_repo.bool {
                    source = builder.ins().bint(I8, source)
                }
                builder.ins().store(
                    MemFlags::new(),
                    source,
                    pointer,
                    target.offset.pick(self.s32) as i32,
                );
            }
            FinalValue::Var(var) => {
                builder.def_var(var, source);
            }
            _ => unreachable!(),
        };
    }

    fn unwrap_val(&self, module: Mod, value: Value, builder: &mut FunctionBuilder) -> Value {
        self.unwrap_val_low(module, value, builder, false)
    }

    fn unwrap_val_low(
        &self,
        module: Mod,
        value: Value,
        builder: &mut FunctionBuilder,
        assign: bool,
    ) -> Value {
        let module_ent = &self.modules[module];
        let value_value = self.context.value(value);
        let value = module_ent.values[value];
        let ty = value.ty;
        match value_value {
            FinalValue::None => unreachable!(),
            FinalValue::Zero => {
                let repr = self.repr(ty);
                match self.types[ty].kind {
                    TKind::Pointer(..) => builder.ins().null(repr),
                    TKind::Structure(..) => builder.ins().iconst(repr, 0),
                    _ => match BTKind::of(ty) {
                        BTKind::Int | BTKind::Uint => builder.ins().iconst(repr, 0),
                        BTKind::Float(32) => builder.ins().f32const(0.0),
                        BTKind::Float(64) => builder.ins().f64const(0.0),
                        BTKind::Bool => builder.ins().bconst(B1, false),
                        _ => unreachable!("{:?}", ty),
                    },
                }
            }
            FinalValue::Value(value) => value,
            FinalValue::Var(var) => {
                let repr = self.repr(ty);
                let mut val = builder.use_var(var);
                let value_type = builder.func.dfg.value_type(val);
                if repr != value_type {
                    val = builder
                        .ins()
                        .ushr_imm(val, value.offset.pick(self.s32) as i64 * 8);
                    val = builder.ins().ireduce(repr, val);
                }
                val
            }
            FinalValue::Pointer(pointer) => {
                if !assign && (!value.on_stack || !self.on_stack(value.ty)) {
                    let repr = self.repr(ty);
                    builder.ins().load(
                        repr,
                        MemFlags::new(),
                        pointer,
                        value.offset.pick(self.s32) as i32,
                    )
                } else if value.offset != Size::ZERO {
                    let ptr_type = self.ptr_ty;
                    let offset = builder
                        .ins()
                        .iconst(ptr_type, value.offset.pick(self.s32) as i64);
                    builder.ins().iadd(pointer, offset)
                } else {
                    pointer
                }
            }
            FinalValue::StackSlot(slot) => {
                if !assign && !self.on_stack(value.ty) {
                    if value.ty == self.state.builtin_repo.bool {
                        let value =
                            builder
                                .ins()
                                .stack_load(I8, slot, value.offset.pick(self.s32) as i32);
                        builder.ins().icmp_imm(IntCC::NotEqual, value, 0)
                    } else {
                        builder.ins().stack_load(
                            self.repr(value.ty),
                            slot,
                            value.offset.pick(self.s32) as i32,
                        )
                    }
                } else {
                    builder
                        .ins()
                        .stack_addr(self.ptr_ty, slot, value.offset.pick(self.s32) as i32)
                }
            }
        }
    }

    fn pass(&mut self, from: Value, to: Value) {
        let from = self.context.value(from);
        self.context.set_value(to, from);
    }

    fn on_stack(&self, ty: Ty) -> bool {
        self.types[ty].on_stack(self.ptr_ty)
    }

    fn repr(&self, ty: Ty) -> Type {
        self.types[ty].to_cr_type(self.module.isa())
    }

    pub fn make_static_data(&mut self, data: &[u8], mutable: bool, tls: bool) -> (DataId, bool) {
        let id = data.sdbm_hash().wrapping_add(STRING_SALT);
        let mut name = String::new();
        write_radix(id, 36, &mut name);
        if let Some(FuncOrDataId::Data(data_id)) = self.module.get_name(&name) {
            (data_id, false)
        } else {
            let data_id = self
                .module
                .declare_data(&name, Linkage::Export, mutable, tls)
                .unwrap();
            self.context.data_context.define(data.deref().to_owned().into_boxed_slice());
            self.module.define_data(data_id, &self.context.data_context).unwrap();
            self.context.data_context.clear();
            (data_id, true)
        }
    }
}

impl SdbmHash for &[u8] {
    fn bytes(&self) -> &[u8] {
        self
    }
}

#[derive(Default, QuickSer)]
pub struct GState {
    pub f_state: FState,
    pub compiled_funs: SecondaryMap<Fun, CFun>,
    pub compiled_globals: SecondaryMap<GlobalValue, CompiledGlobal>,
    pub jit_funs: SparseMap<Fun, JFun>,
    pub bin_declarations: ModuleDeclarations,
    pub jit_declarations: ModuleDeclarations,
}

crate::inherit!(GState, f_state, FState);

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct CompiledGlobal {
    pub id: DataId,
}

impl Default for CompiledGlobal {
    fn default() -> Self {
        Self {
            id: DataId::reserved_value(),
        }
    }
}

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct CFun {
    pub bin: CompiledData,
    #[default(FuncId::from_u32(0))]
    pub id: FuncId,
}

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct JFun {
    pub id: Fun,
    pub bin: CompiledData,
}

impl SparseMapValue<Fun> for JFun {
    fn key(&self) -> Fun {
        self.id
    }
}

#[derive(Clone, Default, QuickSer)]
pub struct CompiledData {
    pub bytes: Vec<u8>,
    pub relocs: Vec<RelocRecord>,
}

impl std::fmt::Debug for CompiledData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompiledData")
            .field("bytes", &self.bytes)
            .field("relocs", &"...")
            .finish()
    }
}

#[derive(QuickDefault)]
pub struct GContext {
    #[default(DataContext::new())]
    pub data_context: DataContext,
    pub f_context: FContext,
    pub imported_signatures: Map<SigRef>,
    pub imported_funs: Map<FuncRef>,
    pub imported_globals: Map<GlobalValue>,
    #[default(vec![Default::default()])]
    pub b_contexts: Vec<BContext>,
    pub current_b_context: usize,
}

crate::inherit!(GContext, f_context, FContext);

impl GContext {
    pub fn dive(&mut self) {
        self.current_b_context += 1;
        if self.current_b_context >= self.b_contexts.len() {
            self.b_contexts.push(BContext::default());
        }
    }

    pub fn bail(&mut self) {
        self.current_b_context -= 1;
    }

    pub fn block(&self, block: Block) -> Block {
        self.b_contexts[self.current_b_context].blocks[block]
    }

    pub fn set_block(&mut self, block: Block, new_block: Block) {
        self.b_contexts[self.current_b_context].blocks[block] = new_block;
    }

    pub fn value(&self, value: Value) -> FinalValue {
        self.b_contexts[self.current_b_context].values[value]
    }

    pub fn set_value(&mut self, value: Value, new_value: FinalValue) {
        self.b_contexts[self.current_b_context].values[value] = new_value;
    }
}

pub struct BContext {
    pub values: SecondaryMap<Value, FinalValue>,
    pub blocks: SecondaryMap<Block, Block>,
}

impl Default for BContext {
    fn default() -> Self {
        Self {
            values: SecondaryMap::new(),
            blocks: SecondaryMap::new(),
        }
    }
}

const MOVERS: &'static [Type] = &[I8, I16, I32, I64];
const MOVER_SIZES: &'static [u32] = &[1, 2, 4, 8];
const MAX_MOVER_SIZE: u32 = 64;

fn find_best_mover(size: u32) -> (Type, u32) {
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
    pointer: Value,
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
    dst_pointer: Value,
    dst_pointer_offset: u32,
    src_pointer: Value,
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

fn walk_mem<F: FnMut(Type, u32)>(size: u32, mut fun: F) {
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

pub struct MetaTrapSink {}

impl TrapSink for MetaTrapSink {
    fn trap(&mut self, _offset: CodeOffset, _loc: SourceLoc, _code: TrapCode) {
        //println!("{:?} {:?} {:?}", _offset, _loc, _code);
    }
}

pub struct MetaRelocSink {
    pub relocs: Vec<RelocRecord>,
}

impl MetaRelocSink {
    pub fn new() -> Self {
        Self { relocs: Vec::new() }
    }

    pub fn clear(&mut self) {
        self.relocs.clear();
    }
}

impl RelocSink for MetaRelocSink {
    fn reloc_external(
        &mut self,
        offset: CodeOffset,
        _source_loc: SourceLoc,
        reloc: Reloc,
        name: &ExternalName,
        addend: Addend,
    ) {
        self.relocs.push(RelocRecord {
            offset,
            reloc,
            name: name.clone(),
            addend,
        });
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum FinalValue {
    None,
    Zero,
    Value(Value),
    Pointer(Value),
    Var(Variable),
    StackSlot(StackSlot),
}

impl Default for FinalValue {
    fn default() -> Self {
        Self::None
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
    pub fn of(tp: Ty) -> Self {
        match EntityRef::index(tp) {
            0..=3 | 11 => Self::Int,
            4..=7 | 12 => Self::Uint,
            8 => Self::Float(32),
            9 => Self::Float(64),
            10 => Self::Bool,
            _ => panic!("cannot get builtin type of {:?}", tp),
        }
    }
}

fn align(size: u32) -> u32 {
    size + 8 * ((size & 7) != 0) as u32 - (size & 7)
}
