use core::panic;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use crate::ast::{AKind, Ast, AstDisplay, Vis};
use crate::collector::{Collector, Attrs, Item, Scope};
use crate::lexer::TKind as LTKind;
use crate::lexer::{Spam, Token, TokenDisplay};
use crate::module_tree::*;
use crate::types::Type;
use crate::types::*;
use crate::util::storage::{LinkedList, ReusableList, Table};
use crate::util::{
    sdbm::ID,
    storage::{IndexPointer, List},
};

use cranelift_codegen::ir::{
    AbiParam, ArgumentPurpose, Block as CrBlock, Signature, StackSlot, Value as CrValue,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_frontend::Variable as CrVar;
use cranelift_module::{DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

type Result<T = ()> = std::result::Result<T, FError>;
type ExprResult = Result<Option<Value>>;

// wales i made up btw
pub const FUN_SALT: ID = ID(0xDEADBEEF);
pub const GLOBAL_SALT: ID = ID(0x2849437252);
pub const GENERIC_FUN_SALT: ID = ID(0xFAEFACBD);

pub struct FParser<'a> {
    program: &'a mut Program,
    state: &'a mut FState,
    context: &'a mut FContext,
    collector: &'a mut Collector,
}

impl<'a> FParser<'a> {
    pub fn new(
        program: &'a mut Program,
        state: &'a mut FState,
        context: &'a mut FContext,
        collector: &'a mut Collector,
    ) -> Self {
        Self {
            program,
            state,
            context,
            collector,
        }
    }

    pub fn parse(&mut self, module: Mod) -> Result {
        TParser::new(self.state, self.context, self.collector)
            .parse(module)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))?;

        self.collect(module)?;

        self.translate_globals()?;

        self.translate()?;

        Ok(())
    }

    pub fn finalize(&mut self) -> Result {
        self.state.bstate = std::mem::take(&mut self.state.main_bstate);

        let value = self.state.bstate.vars.pop().unwrap();
        self.add_inst(InstEnt::new(
            IKind::Return(Some(value)),
            None,
            &Token::default(),
        ));

        self.declare_fun(self.state.main_fun)?;

        Ok(())
    }

    fn translate_globals(&mut self) -> Result {
        std::mem::swap(&mut self.state.bstate, &mut self.state.main_bstate);
        let mut unresolved = std::mem::take(&mut self.state.unresolved_globals);
        let fun = self.state.main_fun;
        let mut buffer = self.context.pool.get();

        for global in unresolved.drain(..) {
            let glob = &mut self.state.globals[global];
            let (ast, ty) = match &mut glob.kind {
                GKind::Normal(ast, ty) => (std::mem::take(ast), ty.clone()),
                _ => unreachable!(),
            };
            let attrs = glob.attrs.clone();
            let module = glob.module;

            write_base36(glob.id.0, &mut buffer);

            self.state.funs[fun].module = module;

            let ty = if ast.kind != AKind::None {
                let value = self.expr(fun, &ast)?;
                let ty = self.value(value).ty;
                let target = self.new_anonymous_value(ty, true);
                self.add_inst(InstEnt::new(
                    IKind::GlobalLoad(global),
                    Some(target),
                    &ast.token,
                ));

                self.add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

                ty
            } else {
                ty.unwrap()
            };

            let name = unsafe { std::str::from_utf8_unchecked(buffer.as_slice()) };

            let tls =
                self.collector.attr_id(&attrs, self.state.tls_hash).is_some() || 
                self.collector.attr_id(&attrs, self.state.thread_local_hash).is_some();

            let data_id = self
                .program
                .module
                .declare_data(name, Linkage::Export, true, tls)
                .unwrap();

            self.state.globals[global].kind = GKind::Represented(data_id, ty);

            self.state.resolved_globals.push(global);
        }

        std::mem::swap(&mut self.state.bstate, &mut self.state.main_bstate);
        self.state.unresolved_globals = unresolved;

        Ok(())
    }

    fn translate(&mut self) -> Result {
        while let Some(fun) = self.state.unresolved.pop() {
            self.state.bstate.body = self.context.body_pool.pop().unwrap_or_default();
            self.fun(fun)?;
            self.declare_fun(fun)?;
        }

        Ok(())
    }

    fn fun(&mut self, fun: Fun) -> Result {
        let fun_ent = &self.state.funs[fun];
        let param_len = fun_ent.params.len();

        let nid = fun_ent.kind.unwrap_normal();
        let n_ent_ast = self.state.nfuns[nid].ast;
        let ast = std::mem::take(&mut self.state.asts[n_ent_ast]);

        if ast[1].is_empty() {
            return Ok(());
        }

        let mut shadowed = self.context.pool.get();
        for i in 0..param_len {
            let (id, ty) = self.state.funs[fun].params[i];
            shadowed.push((id, self.state.types.link(id, ty)))
        }

        let entry_point = self.new_block();
        self.make_block_current(entry_point);

        let sig = &mut self.state.nfuns[nid].sig;
        let args = std::mem::take(&mut sig.args);
        let ret_ty = sig.ret_ty;
        let mut arg_buffer = self.context.pool.get();
        self.clear_vars();
        for arg in args.iter() {
            let var = self.state.bstate.body.values.add(arg.clone());
            self.state.bstate.vars.push(var);
            arg_buffer.push(var);
        }
        if let Some(ret_ty) = ret_ty {
            if self.ty(ret_ty).on_stack() {
                let ty = self.pointer_of(ret_ty);
                let value = self.new_anonymous_value(ty, false);
                arg_buffer.push(value);
            }
        }
        self.state.nfuns[nid].sig.args = args;
        self.inst_mut(entry_point).kind.block_mut().args = arg_buffer.clone();

        let value = self.block(fun, &ast[1])?;

        let n_ent = &self.state.nfuns[nid];

        if let (Some(value), Some(_), Some(ret_ty)) =
            (value, self.state.bstate.block, n_ent.sig.ret_ty)
        {
            let value_ty = self.value(value).ty;
            let token = &ast[1].last().unwrap().token;
            self.assert_type(value_ty, ret_ty, token)?;
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if let (Some(ret_ty), Some(_)) = (n_ent.sig.ret_ty, self.state.bstate.block) {
            let value = self.new_temp_value(ret_ty);
            let token = &ast[1].last().unwrap().token;
            self.add_inst(InstEnt::new(IKind::Zeroed, Some(value), token));
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if self.state.bstate.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Return(None),
                None,
                &ast[1].last().unwrap_or(&Ast::none()).token,
            ));
        }

        self.state.asts[n_ent_ast] = ast;

        for value_id in self.state.bstate.body.values.ids() {
            let ty = self.value(value_id).ty;
            let on_stack = self.ty(ty).on_stack();
            self.value_mut(value_id).on_stack = self.value(value_id).on_stack || on_stack;
        }

        for (id, shadow) in shadowed.drain(..) {
            self.state.types.remove_link(id, shadow);
        }

        Ok(())
    }

    fn declare_fun(&mut self, fun: Fun) -> Result {
        let fun_ent = &self.state.funs[fun];
        let disposable = fun_ent.params.is_empty();
        let n_ent = self.state.nfuns.remove(fun_ent.kind.unwrap_normal());
        let fun_id = fun_ent.id;
        let attrs = fun_ent.attrs.clone();
        let state = unsafe {
            std::mem::transmute::<&mut BodyState, &mut BodyState>(&mut self.state.main_bstate)
        };

        if disposable {
            let ast = self.state.asts.remove(n_ent.ast);
            self.context.recycle(ast);
        }

        let mut name_buffer = self.context.pool.get();

        write_base36(fun_id.0, &mut name_buffer);

        let name = unsafe { std::str::from_utf8_unchecked(&name_buffer[..]) };

        let (linkage, alias) = if let Some(attr) = self.collector.attr(&attrs, self.state.linkage_hash) {
            assert_attr_len(attr, 1)?;

            let linkage = match self.state.display(&attr[1].token.spam) {
                "import" => Linkage::Import,
                "local" => Linkage::Local,
                "export" => Linkage::Export,
                "preemptible" => Linkage::Preemptible,
                "hidden" => Linkage::Hidden,
                _ => return Err(FError::new(FEKind::InvalidLinkage, attr[1].token.clone())),
            };

            if attr.len() > 2 {
                (linkage, self.state.display(&attr[2].token.spam))
            } else if linkage == Linkage::Import {
                (linkage, self.state.display(&self.state.funs[fun].name))
            } else {
                (linkage, name)
            }
        } else {
            (Linkage::Export, name)
        };

        let call_conv = if let Some(attr) = self.collector.attr(&attrs, self.state.call_conv_hash) {
            assert_attr_len(attr, 1)?;
            let conv = self.state.display(&attr[1].token.spam);
            if conv == "platform" {
                let triple = self.program.module.isa().triple();
                CallConv::triple_default(triple)
            } else {
                CallConv::from_str(conv)
                    .map_err(|_| FError::new(FEKind::InvalidCallConv, attr[1].token.clone()))?
            }
        } else {
            CallConv::Fast
        };

        let mut signature =
            std::mem::replace(&mut self.context.signature, Signature::new(CallConv::Fast));
        signature.clear(call_conv);

        for arg in n_ent.sig.args.iter() {
            let repr = self.ty(arg.ty).repr();
            signature.params.push(AbiParam::new(repr));
        }

        if let Some(ret_ty) = n_ent.sig.ret_ty {
            let ret_ty = &self.ty(ret_ty);
            let repr = ret_ty.repr();

            let purpose = if ret_ty.on_stack() {
                signature
                    .params
                    .push(AbiParam::special(repr, ArgumentPurpose::StructReturn));
                ArgumentPurpose::StructReturn
            } else {
                ArgumentPurpose::Normal
            };

            signature.returns.push(AbiParam::special(repr, purpose));
        }

        if let Some(attr) = self.collector.attr(&attrs, self.state.entry_hash) {
            if !n_ent.sig.args.is_empty()
                && (
                    !n_ent.sig.args.len() != 2
                        || n_ent.sig.args[0].ty != self.state.builtin_repo.int
                        || self
                            .base_of(n_ent.sig.args[1].ty)
                            .map(|base| self.base_of(base))
                            .flatten()
                            .map(|base| base == self.state.builtin_repo.u8)
                            .unwrap_or(true)
                    // verify that it is a '& &u8'
                )
            {
                return Err(FError::new(
                    FEKind::InvalidEntrySignature,
                    attr[0].token.clone(),
                ));
            }

            let args = if n_ent.sig.args.len() == 2 {
                let args = state.body.insts.first().unwrap();
                state.body.insts[args].kind.block().args.clone()
            } else {
                vec![]
            };

            let token = attr[0].token.clone();

            if let Some(ret) = n_ent.sig.ret_ty {
                let return_value = state.body.values.add(ValueEnt::temp(ret));
                state.body.insts.push(InstEnt::new(
                    IKind::Call(fun, args),
                    Some(return_value),
                    &token,
                ));
                if ret == self.state.builtin_repo.int {
                    let result = state.vars.last().unwrap().clone();
                    state.body.insts.push(InstEnt::new(
                        IKind::Assign(result),
                        Some(return_value),
                        &token,
                    ));
                }
            } else {
                state
                    .body
                    .insts
                    .push(InstEnt::new(IKind::Call(fun, args), None, &token));
            }
        }

        let inline = if let Some(attr) = self.collector.attr(&attrs, self.state.inline_hash) {
            if self.state.bstate.body.recursive {
                return Err(FError::new(FEKind::RecursiveInline, attr.token.clone()));
            }
            true
        } else {
            false
        };

        let alias = if fun_id == ID(0) { "main" } else { alias };

        let id = self
            .program
            .module
            .declare_function(alias, linkage, &signature)
            .unwrap();

        let r_ent = RFunEnt {
            signature: n_ent.sig,
            ir_signature: signature.clone(),
            id,
            body: std::mem::take(&mut self.state.bstate.body),
            inline,
        };

        let f = self.state.rfuns.add(r_ent);
        self.state.funs[fun].kind = FKind::Represented(f);

        if !inline {
            self.state.represented.push(fun);
        }

        Ok(())
    }

    fn return_value(&mut self, fun: Fun, value: Value, token: &Token) -> Value {
        let ty = self.return_type_of(fun).unwrap();
        if self.ty(ty).on_stack() {
            let entry = self.state.bstate.body.insts.first().unwrap();
            let return_value = self.inst(entry).kind.block().args.last().unwrap().clone();

            let deref = self.new_temp_value(ty);
            self.add_inst(InstEnt::new(
                IKind::Deref(return_value, false),
                Some(deref),
                &token,
            ));
            self.add_inst(InstEnt::new(IKind::Assign(deref), Some(value), &token));
            return_value
        } else {
            value
        }
    }

    fn block(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        if ast.is_empty() {
            return Ok(None);
        }

        self.push_scope();

        for statement in ast[..ast.len() - 1].iter() {
            if self.state.bstate.block.is_none() {
                break;
            }
            self.statement(fun, statement)?;
        }

        let value = if self.state.bstate.block.is_some() {
            self.statement(fun, ast.last().unwrap())?
        } else {
            None
        };

        self.pop_scope();

        Ok(value)
    }

    fn statement(&mut self, fun: Fun, statement: &Ast) -> ExprResult {
        match statement.kind {
            AKind::VarStatement(..) => self.var_statement(fun, statement)?,
            AKind::ReturnStatement => self.return_statement(fun, statement)?,
            AKind::Break => self.break_statement(fun, statement)?,
            AKind::Continue => self.continue_statement(statement)?,
            _ => return self.expr_low(fun, statement),
        }

        Ok(None)
    }

    fn continue_statement(&mut self, ast: &Ast) -> Result {
        let loop_header = self.find_loop(&ast[0].token).map_err(|outside| {
            if outside {
                FError::new(FEKind::ContinueOutsideLoop, ast.token.clone())
            } else {
                FError::new(FEKind::WrongLabel, ast.token.clone())
            }
        })?;

        self.add_inst(InstEnt::new(
            IKind::Jump(loop_header.start_block, vec![]),
            None,
            &ast.token,
        ));

        Ok(())
    }

    fn break_statement(&mut self, fun: Fun, ast: &Ast) -> Result {
        let loop_header = self.find_loop(&ast[0].token).map_err(|outside| {
            if outside {
                FError::new(FEKind::BreakOutsideLoop, ast.token.clone())
            } else {
                FError::new(FEKind::WrongLabel, ast.token.clone())
            }
        })?;

        if ast[1].kind != AKind::None {
            let return_value = self.expr(fun, &ast[1])?;
            let current_value = self
                .inst(loop_header.end_block)
                .kind
                .block()
                .args
                .first()
                .cloned();
            if current_value.is_none() {
                let ty = self.value(return_value).ty;
                let value = self.new_temp_value(ty);
                self.inst_mut(loop_header.end_block)
                    .kind
                    .block_mut()
                    .args
                    .push(value);
            }

            self.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, vec![return_value]),
                None,
                &ast.token,
            ));
        } else {
            self.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, vec![]),
                None,
                &ast.token,
            ));
        }

        Ok(())
    }

    fn return_statement(&mut self, fun: Fun, ast: &Ast) -> Result {
        let ty = self.return_type_of(fun);

        let value = if ast[0].kind == AKind::None {
            if let Some(ty) = ty {
                let temp_value = self.new_temp_value(ty);
                self.add_inst(InstEnt::new(IKind::Zeroed, Some(temp_value), &ast.token));
                Some(self.return_value(fun, temp_value, &ast.token))
            } else {
                None
            }
        } else {
            let ty =
                ty.ok_or_else(|| FError::new(FEKind::UnexpectedReturnValue, ast[0].token.clone()))?;
            let value = self.expr(fun, &ast[0])?;
            let actual_type = self.value(value).ty;
            self.assert_type(actual_type, ty, &ast[0].token)?;
            Some(self.return_value(fun, value, &ast.token))
        };

        self.add_inst(InstEnt::new(IKind::Return(value), None, &ast.token));

        Ok(())
    }

    fn var_statement(&mut self, fun: Fun, statement: &Ast) -> Result {
        let mutable = statement.kind == AKind::VarStatement(Vis::None, true);
        let module = self.state.funs[fun].module;

        for var_line in statement.iter() {
            let ty = if var_line[1].kind == AKind::None {
                None
            } else {
                Some(self.parse_type(module, &var_line[1])?)
            };

            if var_line[2].kind == AKind::None {
                for name in var_line[0].iter() {
                    let ty = ty.unwrap();
                    let name = name.token.spam.hash;

                    let temp_value = self.state.bstate.body.values.add(ValueEnt::temp(ty));

                    self.add_inst(InstEnt::new(
                        IKind::Zeroed,
                        Some(temp_value),
                        &var_line.token,
                    ));

                    let var = self.add_variable(name, ty, mutable);

                    self.add_inst(InstEnt::new(
                        IKind::VarDecl(temp_value),
                        Some(var),
                        &var_line.token,
                    ));
                }
            } else {
                for (name, raw_value) in var_line[0].iter().zip(var_line[2].iter()) {
                    let name = name.token.spam.hash;
                    let value = self.expr(fun, raw_value)?;
                    let actual_datatype = self.value(value).ty;

                    if let Some(ty) = ty {
                        self.assert_type(actual_datatype, ty, &raw_value.token)?;
                    }

                    let var = self.add_variable(name, actual_datatype, mutable);

                    self.add_inst(InstEnt::new(
                        IKind::VarDecl(value),
                        Some(var),
                        &var_line.token,
                    ));
                }
            }
        }

        Ok(())
    }

    fn expr(&mut self, fun: Fun, ast: &Ast) -> Result<Value> {
        self.expr_low(fun, ast)?
            .ok_or_else(|| FError::new(FEKind::ExpectedValue, ast.token.clone()))
    }

    fn expr_low(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        match ast.kind {
            AKind::BinaryOp => self.binary_op(fun, ast),
            AKind::Lit => self.lit(ast),
            AKind::Ident => self.ident(fun, ast),
            AKind::Call(_) => self.call(fun, ast),
            AKind::IfExpr => self.if_expr(fun, ast),
            AKind::Loop => self.loop_expr(fun, ast),
            AKind::DotExpr => self.dot_expr(fun, ast),
            AKind::Deref => self.deref_expr(fun, ast),
            AKind::Ref => self.ref_expr(fun, ast),
            AKind::UnaryOp => self.unary_op(fun, ast),
            AKind::Pass => Ok(None),
            AKind::Array => self.array(fun, ast),
            AKind::Index => self.index(fun, ast),
            _ => todo!("unmatched expr ast {}", AstDisplay::new(self.state, &ast)),
        }
    }

    fn index(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let target = self.expr(fun, &ast[0])?;
        let index = self.expr(fun, &ast[1])?;
        let id = FUN_SALT.add(self.state.index_spam.hash);
        let args = &[target, index];
        let spam = self.state.index_spam.clone();
        let result = self
            .call_low(fun, id, &spam, true, &[], args, &ast.token)?
            .ok_or_else(|| FError::new(FEKind::ExpectedValue, ast.token.clone()))?;

        let result = self.deref_expr_low(result, &ast.token)?;

        Ok(Some(result))
    }

    fn array(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let mut values = self.context.pool.get();

        let mut element_ty = None;
        let length = ast.len();

        for raw_value in ast.iter() {
            let value = self.expr(fun, raw_value)?;
            if let Some(ty) = element_ty {
                self.assert_type(self.value(value).ty, ty, &raw_value.token)?;
            } else {
                element_ty = Some(self.value(value).ty);
            }
            values.push(value);
        }

        if element_ty.is_none() {
            return Err(FError::new(FEKind::EmptyArray, ast.token.clone()));
        }

        let element_ty = element_ty.unwrap();
        let element_size = self.ty(element_ty).size;

        let ty = self.array_of(element_ty, length);

        let result = self.new_anonymous_value(ty, true);
        self.add_inst(InstEnt::new(IKind::Uninitialized, Some(result), &ast.token));

        for (i, &value) in values.iter().enumerate() {
            let offset = self.new_anonymous_value(element_ty, false);
            self.value_mut(offset).offset = i as u32 * element_size;
            self.add_inst(InstEnt::new(
                IKind::Offset(result),
                Some(offset),
                &ast.token,
            ));
            self.add_inst(InstEnt::new(IKind::Assign(offset), Some(value), &ast.token));
        }

        Ok(Some(result))
    }

    fn ref_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let value = self.expr(fun, &ast[0])?;

        let reference = self.ref_expr_low(value, &ast.token);

        Ok(Some(reference))
    }

    fn ref_expr_low(&mut self, value: Value, token: &Token) -> Value {
        let ty = self.value(value).ty;
        let ty = self.pointer_of(ty);
        let reference = self.new_temp_value(ty);
        self.add_inst(InstEnt::new(IKind::Ref(value), Some(reference), token));

        // we need to allocate it since register cannot be referenced
        let mut current = reference;
        loop {
            let value = self.value_mut(current);
            if value.on_stack {
                break;
            }
            value.on_stack = true;

            if let Some(inst) = value.inst {
                match &self.inst(inst).kind {
                    IKind::Ref(value) | IKind::Offset(value) | IKind::Cast(value) => {
                        current = *value;
                        continue;
                    }
                    _ => (),
                }
            }

            break;
        }

        reference
    }

    fn deref_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let expr = self.expr(fun, &ast[0])?;

        let value = self.deref_expr_low(expr, &ast.token)?;

        Ok(Some(value))
    }

    fn deref_expr_low(&mut self, value: Value, token: &Token) -> Result<Value> {
        let ty = self.value(value).ty;
        let pointed = self.base_of_err(ty, token)?;

        let val = self.new_anonymous_value(pointed, true);
        self.add_inst(InstEnt::new(IKind::Deref(value, false), Some(val), token));

        Ok(val)
    }

    fn unary_op(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let name = FUN_SALT.add(ast[0].token.spam.hash);
        let value = self.expr(fun, &ast[1])?;

        let mut values = self.context.pool.get();
        values.push(value);
        self.call_low(
            fun,
            name,
            &ast[0].token.spam,
            false,
            &[],
            &values,
            &ast.token,
        )
    }

    fn dot_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let header = self.expr(fun, &ast[0])?;
        let mutable = self.value(header).mutable;
        let field = ast[1].token.spam.hash;

        let inst = self.add_inst(InstEnt::new(IKind::NoOp, None, &Token::default()));
        let value = self.new_anonymous_value(self.state.builtin_repo.bool, mutable);
        self.value_mut(value).inst = Some(inst);
        let ty = self.field_access(header, field, value, &ast.token)?;
        self.state.bstate.body.insts.remove(inst);
        self.value_mut(value).ty = ty;
        Ok(Some(value))
    }

    fn find_field(&mut self, ty: Type, field_id: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = self.context.pool.get();
        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            let sid = match &self.ty(frontier[i].2).kind {
                &TKind::Structure(sid) => sid,
                &TKind::Pointer(pointed) => match &self.ty(pointed).kind {
                    &TKind::Structure(sid) => sid,
                    _ => continue,
                },
                _ => continue,
            };
            for (j, field) in self.state.stypes[sid].fields.iter().enumerate() {
                if field.id == field_id {
                    path.push(j);
                    let mut k = i;
                    loop {
                        let (index, ptr, _) = frontier[k];
                        if index == usize::MAX {
                            break;
                        }
                        path.push(ptr);
                        k = index;
                    }
                    return true;
                }
                if field.embedded {
                    frontier.push((i, j, field.ty));
                }
            }
            i += 1;
        }

        false
    }

    fn loop_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let name = ast[0].token.spam.hash;

        let start_block = self.new_block();
        let end_block = self.new_block();

        let header = Loop {
            name,
            start_block,
            end_block,
        };

        self.add_inst(InstEnt::new(
            IKind::Jump(start_block, vec![]),
            None,
            &ast.token,
        ));

        self.state.bstate.loops.push(header);
        self.make_block_current(start_block);
        self.block(fun, &ast[1])?;
        self.state
            .bstate
            .loops
            .pop()
            .expect("expected previously pushed header");

        if self.state.bstate.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Jump(start_block, vec![]),
                None,
                &ast.token,
            ));
        }
        self.make_block_current(end_block);

        let value = if self.inst(end_block).kind.block().args.is_empty() {
            None
        } else {
            Some(self.inst(end_block).kind.block().args[0])
        };

        Ok(value)
    }

    fn if_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let cond_expr = &ast[0];
        let cond_val = self.expr(fun, cond_expr)?;
        let cond_type = self.value(cond_val).ty;

        let then_block = self.new_block();
        self.add_inst(InstEnt::new(
            IKind::JumpIfTrue(cond_val, then_block, vec![]),
            None,
            &cond_expr.token,
        ));

        self.assert_type(cond_type, self.state.builtin_repo.bool, &cond_expr.token)?;

        let merge_block = self.new_block();

        let else_branch = &ast[2];
        let else_block = if else_branch.kind == AKind::None {
            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![]),
                None,
                &else_branch.token,
            ));
            None
        } else {
            let some_block = self.new_block();
            self.add_inst(InstEnt::new(
                IKind::Jump(some_block, vec![]),
                None,
                &else_branch.token,
            ));
            Some(some_block)
        };

        self.make_block_current(then_block);

        let then_branch = &ast[1];

        let then_result = self.block(fun, then_branch)?;

        let mut result = None;
        let mut then_filled = false;
        if let Some(val) = then_result {
            if else_block.is_none() {
                return Err(FError::new(FEKind::MissingElseBranch, ast.token.clone()));
            }

            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![val]),
                None,
                &ast.token,
            ));

            let ty = self.value(val).ty;
            let value = self.new_temp_value(ty);
            self.inst_mut(merge_block).kind.block_mut().args.push(value);
            result = Some(value);
        } else if self.state.bstate.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![]),
                None,
                &ast.token,
            ));
        } else {
            then_filled = true;
        }

        if else_branch.kind == AKind::Group {
            let else_block = else_block.unwrap();
            self.make_block_current(else_block);
            let else_result = self.block(fun, else_branch)?;

            if let Some(val) = else_result {
                let value_token = &else_branch.last().unwrap().token;
                if result.is_some() {
                    self.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![val]),
                        None,
                        value_token,
                    ));
                } else if then_filled {
                    self.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![val]),
                        None,
                        value_token,
                    ));

                    let ty = self.value(val).ty;
                    let value = self.new_temp_value(ty);
                    self.inst_mut(merge_block).kind.block_mut().args.push(value);
                    result = Some(value);
                } else {
                    return Err(FError::new(FEKind::UnexpectedValue, ast.token.clone()));
                }
            } else {
                if self.state.bstate.block.is_some() {
                    if result.is_some() {
                        return Err(FError::new(FEKind::ExpectedValue, ast.token.clone()));
                    }
                    self.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![]),
                        None,
                        &ast.token,
                    ));
                }
            }
        }

        self.make_block_current(merge_block);

        Ok(result)
    }

    fn call(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let module = self.state.funs[fun].module;
        let mut generic_params = self.context.pool.get();
        let name = match ast[0].kind {
            AKind::Ident => (ast[0].token.spam.clone()),
            AKind::Instantiation => {
                for arg in ast[0][1..].iter() {
                    let id = self.parse_type(module, arg)?;
                    generic_params.push(id);
                }
                ast[0][0].token.spam.clone()
            }
            _ => unreachable!(),
        };

        let base_name = FUN_SALT.add(name.hash);

        let mut buffer = self.context.pool.get();
        for value in ast[1..].iter() {
            let value = self.expr(fun, value)?;
            buffer.push(value);
        }

        self.call_low(
            fun,
            base_name,
            &name,
            ast.kind == AKind::Call(true),
            &generic_params,
            &buffer,
            &ast.token,
        )
    }

    fn call_low(
        &mut self,
        fun: Fun,
        base_name: ID,
        name: &Spam,
        dot_call: bool,
        params: &[Type],
        values: &[Value],
        token: &Token,
    ) -> ExprResult {
        let mut values = values.to_vec();
        let module = self.state.funs[fun].module;

        let other_fun = self.smart_find_or_create(
            module,
            base_name,
            name,
            params,
            &mut values,
            dot_call,
            token,
        )?;
        let return_type = self.return_type_of(other_fun);

        self.state.bstate.body.recursive |= fun == other_fun;

        let value = return_type.map(|t| {
            let on_stack = self.ty(t).on_stack();
            let value = self.new_anonymous_value(t, on_stack);
            if on_stack {
                values.push(value);
            }
            value
        });

        self.add_inst(InstEnt::new(IKind::Call(other_fun, values), value, token));

        Ok(value)
    }

    fn return_type_of(&self, fun: Fun) -> Option<Type> {
        match &self.state.funs[fun].kind {
            &FKind::Normal(nid) => self.state.nfuns[nid].sig.ret_ty,
            &FKind::Builtin(ret_ty) => ret_ty,
            i => unreachable!("{:?}", i),
        }
    }

    fn ident(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        if ast.kind == AKind::Ident {
            let ident = &ast.token;
            let value = self
                .find_variable(ident.spam.hash)
                .or_else(|| self.find_constant_parameter(fun, ident));

            if value.is_some() {
                value
            } else {
                self.find_global(fun, None, ident)?
            }
        } else {
            self.find_global(fun, Some(&ast[0].token), &ast[1].token)?
        }
        .ok_or_else(|| FError::new(FEKind::UndefinedVariable, ast.token.clone()))
        .map(|var| Some(var))
    }

    fn find_global(
        &mut self,
        fun: Fun,
        scope: Option<&Token>,
        token: &Token,
    ) -> Result<Option<Value>> {
        let module = self.state.funs[fun].module;

        let mut found = None;

        if let Some(scope) = scope {
            let module = self.state.find_dep(module, scope).ok_or_else(|| {
                FError::new(
                    FEKind::TypeError(TError::new(TEKind::UnknownModule, scope.clone())),
                    Token::default(),
                )
            })?;
            let id = GLOBAL_SALT
                .add(token.spam.hash)
                .add(self.state.modules[module].id);
            found = self.state.globals.index(id).map(|v| v.clone());
        } else {
            let mut buffer = self.context.pool.get();
            self.state.collect_scopes(module, &mut buffer);
            for (_, module_id) in buffer.drain(..) {
                let id = GLOBAL_SALT.add(token.spam.hash).add(module_id);
                if let Some(&value) = self.state.globals.index(id) {
                    if let Some(found) = found {
                        return Err(FError::new(
                            FEKind::AmbiguousGlobal(found, value),
                            token.clone(),
                        ));
                    }
                    found = Some(value);
                    break;
                }
            }
        }

        let found = if let Some(found) = found {
            found
        } else {
            return Ok(None);
        };

        let ty = match self.state.globals[found].kind {
            GKind::Represented(_, ty) => ty,
            _ => unreachable!(),
        };

        let value = self.new_anonymous_value(ty, self.state.globals[found].mutable);
        self.add_inst(InstEnt::new(IKind::GlobalLoad(found), Some(value), token));

        Ok(Some(value))
    }

    fn find_constant_parameter(&mut self, fun: Fun, token: &Token) -> Option<Value> {
        let name = TYPE_SALT
            .add(token.spam.hash)
            .add(self.state.modules[self.state.funs[fun].module].id);
        if let Some(&(_, ty)) = self.state.funs[fun]
            .params
            .iter()
            .find(|&(p, _)| *p == name)
        {
            let ty = &self.ty(ty).kind;
            match ty {
                TKind::Const(t) => {
                    let (kind, ty) = match t.clone() {
                        TypeConst::Bool(val) => (LTKind::Bool(val), self.state.builtin_repo.bool),
                        TypeConst::Int(val) => (LTKind::Int(val, 0), self.state.builtin_repo.int),
                        TypeConst::Float(val) => {
                            (LTKind::Float(val, 64), self.state.builtin_repo.f64)
                        }
                        TypeConst::Char(val) => (LTKind::Char(val), self.state.builtin_repo.u32),
                        TypeConst::String(val) => (
                            LTKind::String(val),
                            self.pointer_of(self.state.builtin_repo.u8),
                        ),
                    };

                    let value = self.new_temp_value(ty);
                    self.add_inst(InstEnt::new(IKind::Lit(kind), Some(value), token));
                    Some(value)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn lit(&mut self, ast: &Ast) -> ExprResult {
        let ty = match ast.token.kind {
            LTKind::Int(_, base) => match base {
                8 => self.state.builtin_repo.i8,
                16 => self.state.builtin_repo.i16,
                32 => self.state.builtin_repo.i32,
                64 => self.state.builtin_repo.i64,
                _ => self.state.builtin_repo.int,
            },
            LTKind::Uint(_, base) => match base {
                8 => self.state.builtin_repo.u8,
                16 => self.state.builtin_repo.u16,
                32 => self.state.builtin_repo.u32,
                64 => self.state.builtin_repo.u64,
                _ => self.state.builtin_repo.uint,
            },
            LTKind::Float(_, base) => match base {
                32 => self.state.builtin_repo.f32,
                _ => self.state.builtin_repo.f64,
            },
            LTKind::Bool(_) => self.state.builtin_repo.bool,
            LTKind::Char(_) => self.state.builtin_repo.i32,
            LTKind::String(_) => self.pointer_of(self.state.builtin_repo.u8),
            _ => unreachable!("{}", AstDisplay::new(self.state, ast)),
        };

        let value = self.new_temp_value(ty);

        self.add_inst(InstEnt::new(
            IKind::Lit(ast.token.kind.clone()),
            Some(value),
            &ast.token,
        ));

        Ok(Some(value))
    }

    fn binary_op(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        match self.state.display(&ast[0].token.spam) {
            "=" => return self.assignment(fun, ast),
            "as" => return self.bit_cast(fun, ast),
            _ => (),
        }

        let left = self.expr(fun, &ast[1])?;
        let right = self.expr(fun, &ast[2])?;

        let base_id = FUN_SALT.add(ast[0].token.spam.hash);

        let mut buffer = self.context.pool.get();
        buffer.extend(&[left, right]);

        self.call_low(
            fun,
            base_id,
            &ast[0].token.spam,
            false,
            &[],
            &buffer,
            &ast.token,
        )
    }

    fn bit_cast(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let module = self.state.funs[fun].module;
        let target = self.expr(fun, &ast[1])?;
        let ty = self.parse_type(module, &ast[2])?;

        let original_datatype = self.value(target).ty;
        let original_size = self.ty(original_datatype).size;
        let datatype_size = self.ty(ty).size;

        if original_size != datatype_size {
            return Err(FError::new(
                FEKind::InvalidBitCast(original_size, datatype_size),
                ast.token.clone(),
            ));
        }

        let value = self.new_anonymous_value(ty, self.value(target).mutable);
        self.add_inst(InstEnt::new(IKind::Cast(target), Some(value), &ast.token));

        Ok(Some(value))
    }

    fn field_access(
        &mut self,
        mut header: Value,
        field: ID,
        value: Value,
        token: &Token,
    ) -> Result<Type> {
        let mutable = self.value(header).mutable;
        let header_datatype = self.value(header).ty;
        let mut path = vec![];
        if !self.find_field(header_datatype, field, &mut path) {
            return Err(FError::new(
                FEKind::UnknownField(header_datatype),
                token.clone(),
            ));
        }

        let mut offset = 0;
        let mut current_type = header_datatype;
        for &i in path.iter().rev() {
            match &self.ty(current_type).kind {
                &TKind::Structure(sid) => {
                    let field = &self.state.stypes[sid].fields[i];
                    offset += field.offset;
                    current_type = field.ty;
                }
                &TKind::Pointer(pointed) => {
                    let value = self.new_anonymous_value(current_type, mutable);
                    self.value_mut(value).offset = offset;
                    self.add_inst(InstEnt::new(IKind::Offset(header), Some(value), &token));

                    match &self.ty(pointed).kind {
                        &TKind::Structure(sid) => {
                            let field = &self.state.stypes[sid].fields[i];
                            offset = field.offset;
                            current_type = field.ty;
                            let loaded = self.new_anonymous_value(pointed, mutable);
                            self.add_inst(InstEnt::new(
                                IKind::Deref(value, false),
                                Some(loaded),
                                &token,
                            ));
                            header = loaded;
                            self.value_mut(loaded).offset = offset;
                        }
                        _ => unreachable!(),
                    }
                }
                _ => todo!("{:?}", self.ty(current_type)),
            }
        }

        let inst = self.add_inst(InstEnt::new(IKind::Offset(header), Some(value), token));

        let val = self.value_mut(value);
        val.inst = Some(inst);
        val.offset = offset;
        val.ty = current_type;

        Ok(current_type)
    }

    fn inst_of(&mut self, value: Value) -> Inst {
        // if inst is none then this is function parameter and its safe to put it
        // at the beginning of the entry block
        self.value(value)
            .inst
            .unwrap_or(self.state.bstate.body.insts.first().unwrap())
    }

    pub fn add_variable(&mut self, name: ID, ty: Type, mutable: bool) -> Value {
        let val = self.new_value(name, ty, mutable);
        self.state.bstate.vars.push(val);
        val
    }

    fn assignment(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let target = self.expr(fun, &ast[1])?;
        let value = self.expr(fun, &ast[2])?;
        let target_datatype = self.value(target).ty;
        let value_datatype = self.value(value).ty;

        if !self.value(target).mutable {
            return Err(FError::new(FEKind::AssignToImmutable, ast.token.clone()));
        }

        match &mut self.inst_mut(self.value(target).inst.unwrap()).kind {
            IKind::Deref(_, assign) => *assign = true,
            _ => (),
        }

        self.assert_type(value_datatype, target_datatype, &ast.token)?;

        self.add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

        Ok(Some(value))
    }

    fn smart_find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &Spam,
        params: &[Type],
        args: &mut [Value],
        dot_expr: bool,
        token: &Token,
    ) -> Result<Fun> {
        let mut types = self.context.pool.get();
        types.clear();
        types.extend(args.iter().map(|&v| self.value(v).ty));

        let result = if dot_expr {
            let first_mutable = self.value(args[0]).mutable;
            let (fun, id, kind) =
                self.dot_find_or_create(module, base, name, params, &mut types, &token)?;
            if id.0 != 0 {
                let value = self.new_anonymous_value(self.state.builtin_repo.bool, first_mutable);
                self.field_access(args[0], id, value, &token)?;
                args[0] = value;
            }
            match kind {
                DotInstr::None => (),
                DotInstr::Deref => args[0] = self.deref_expr_low(args[0], &token)?,
                DotInstr::Ref => args[0] = self.ref_expr_low(args[0], &token),
            }
            Ok(fun)
        } else {
            self.find_or_create(module, base, name, params, &types, &token)
        };

        result
    }

    #[inline]
    fn new_temp_value(&mut self, ty: Type) -> Value {
        self.new_anonymous_value(ty, false)
    }

    #[inline]
    fn new_anonymous_value(&mut self, ty: Type, mutable: bool) -> Value {
        self.new_value(ID(0), ty, mutable)
    }

    #[inline]
    fn new_value(&mut self, name: ID, ty: Type, mutable: bool) -> Value {
        let value = ValueEnt::new(name, ty, mutable);
        self.state.bstate.body.values.add(value)
    }

    pub fn add_inst(&mut self, inst: InstEnt) -> Inst {
        debug_assert!(self.state.bstate.block.is_some(), "no block to add inst to");
        let closing = inst.kind.is_closing();
        let value = inst.value;
        let inst = self.state.bstate.body.insts.push(inst);
        if let Some(value) = value {
            self.value_mut(value).inst = Some(inst);
        }
        if closing {
            self.close_block();
        }
        inst
    }

    pub fn add_inst_above(&mut self, inst: InstEnt, at: Inst) -> Inst {
        debug_assert!(!inst.kind.is_closing(), "cannot insert closing instruction");
        let value = inst.value;
        let inst = self.state.bstate.body.insts.insert_before(at, inst);
        if let Some(value) = value {
            self.value_mut(value).inst = Some(inst);
        }
        inst
    }

    pub fn new_block(&mut self) -> Inst {
        self.state.bstate.body.insts.add_hidden(InstEnt::new(
            IKind::Block(Default::default()),
            None,
            &Token::default(),
        ))
    }

    pub fn make_block_current(&mut self, block: Inst) {
        debug_assert!(
            self.state.bstate.block.is_none(),
            "current block is not closed"
        );
        self.state.bstate.body.insts.show_as_last(block);
        self.state.bstate.block = Some(block);
    }

    pub fn close_block(&mut self) {
        debug_assert!(self.state.bstate.block.is_some(), "no block to close");
        let block = self.state.bstate.block.unwrap();
        let inst = self.state.bstate.body.insts.push(InstEnt::new(
            IKind::BlockEnd(block),
            None,
            &Token::default(),
        ));
        self.inst_mut(block).kind.block_mut().end = Some(inst);
        self.state.bstate.block = None;
    }

    fn dot_find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &Spam,
        params: &[Type],
        values: &mut [Type],
        token: &Token,
    ) -> Result<(Fun, ID, DotInstr)> {
        let mut frontier = self.context.pool.get();
        frontier.push((values[0], ID(0)));

        let mut final_err = None;

        macro_rules! unwrap {
            ($expr:expr, $id:expr, $type:ident) => {
                match $expr {
                    Ok(expr) => return Ok((expr, $id, DotInstr::$type)),
                    #[allow(unused_assignments)]
                    Err(err) => {
                        if let FError {
                            kind: FEKind::FunctionNotFound(..),
                            ..
                        } = err
                        {
                            final_err = Some(err);
                        } else {
                            return Err(err);
                        }
                    }
                }
            };
        }

        let mut i = 0;
        while i < frontier.len() {
            let (ty, id) = frontier[i];
            values[0] = ty;
            unwrap!(
                self.find_or_create(module, base, name, params, values, token),
                id,
                None
            );
            if self.is_pointer(ty) {
                values[0] = self.base_of(ty).unwrap();
                unwrap!(
                    self.find_or_create(module, base, name, params, values, token),
                    id,
                    Deref
                );
            } else {
                values[0] = self.pointer_of(ty);
                unwrap!(
                    self.find_or_create(module, base, name, params, values, token),
                    id,
                    Ref
                );
            }

            match &self.ty(ty).kind {
                &TKind::Structure(id) => {
                    for field in self.state.stypes[id].fields.iter().filter(|f| f.embedded) {
                        frontier.push((field.ty, field.id));
                    }
                }
                &TKind::Pointer(pointed) => match &self.ty(pointed).kind {
                    &TKind::Structure(id) => {
                        for field in self.state.stypes[id].fields.iter().filter(|f| f.embedded) {
                            frontier.push((field.ty, field.id));
                        }
                    }
                    _ => (),
                },
                _ => (),
            }

            i += 1;
        }

        Err(final_err.unwrap())
    }

    fn find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &Spam,
        params: &[Type],
        values: &[Type],
        token: &Token,
    ) -> Result<Fun> {
        let mut specific_id = values
            .iter()
            .fold(base, |base, &val| base.add(self.ty(val).id));

        if values.len() == 0 {
            for &ty in params {
                specific_id = specific_id.add(self.ty(ty).id);
            }
        }

        let mut buffer = self.context.pool.get();
        self.state.collect_scopes(module, &mut buffer);

        let (_, module_id) = buffer[0];

        if let Some(fun) =
            self.find_or_create_low(specific_id, module_id, base, module, params, values, token)?
        {
            return Ok(fun);
        }

        let mut found = None;

        for (module, module_id) in buffer.drain(1..) {
            if let Some(fun) = self.find_or_create_low(
                specific_id,
                module_id,
                base,
                module,
                params,
                values,
                token,
            )? {
                if let Some(found) = found {
                    return Err(FError::new(
                        FEKind::AmbiguousFunction(fun, found),
                        token.clone(),
                    ));
                }
                found = Some(fun);
            }
        }

        found.ok_or_else(|| {
            FError::new(
                FEKind::FunctionNotFound(name.clone(), values.to_vec()),
                token.clone(),
            )
        })
    }

    fn find_or_create_low(
        &mut self,
        specific_id: ID,
        module_id: ID,
        base: ID,
        module: Mod,
        params: &[Type],
        values: &[Type],
        token: &Token,
    ) -> Result<Option<Fun>> {
        if let Some(&fun) = self.state.funs.index(specific_id.add(module_id)) {
            return Ok(Some(fun));
        }

        let mut g_fun = self
            .state
            .funs
            .index(base.add(GENERIC_FUN_SALT).add(module_id))
            .cloned();

        let mut found = None;

        while let Some(fun) = g_fun {
            let g = match self.state.funs[fun].kind {
                FKind::Generic(g) => g,
                _ => unreachable!("{:?}", self.state.funs[fun].kind),
            };
            if let Some(fun) = self.create(module, fun, g, params, values)? {
                if let Some(found) = found {
                    return Err(FError::new(
                        FEKind::AmbiguousFunction(fun, found),
                        token.clone(),
                    ));
                }
                found = Some(fun);
            }
            g_fun = self.state.gfuns[g].next;
        }

        Ok(found)
    }

    fn create(
        &mut self,
        module: Mod,
        fun: Fun,
        g: GFun,
        explicit_params: &[Type],
        values: &[Type],
    ) -> Result<Option<Fun>> {
        let g_ent = &self.state.gfuns[g];
        let g_ent_len = g_ent.signature.elements.len();

        let mut arg_buffer = self.context.pool.get();
        let mut stack = self.context.pool.get();
        let mut params = self.context.pool.get();
        params.resize(g_ent.signature.params.len(), None);
        for (exp, param) in explicit_params.iter().zip(params.iter_mut()) {
            *param = Some(exp.clone());
        }

        // perform pattern matching
        let mut i = 0;
        let mut j = 0;
        while i < g_ent_len {
            let g_ent = &self.state.gfuns[g];
            let (amount, length) = match g_ent.signature.elements[i] {
                GenericElement::NextArgument(amount, length) => (amount, length),
                _ => unreachable!("{:?}", g_ent.signature.elements[i]),
            };

            for _ in 0..amount {
                self.load_arg_from_datatype(values[j], &mut arg_buffer, &mut stack);
                let g_ent = &self.state.gfuns[g];
                let arg = &g_ent.signature.elements[i + 1..i + 1 + length];
                {
                    let mut i = 0;
                    let mut j = 0;
                    while i + j < arg.len() + arg_buffer.len() {
                        let a = arg[i].clone();
                        let b = arg_buffer[j].clone();
                        if !a.compare(&b) {
                            match a {
                                GenericElement::Parameter(i) => match b {
                                    GenericElement::Element(_, Some(ty))
                                    | GenericElement::Array(Some(ty)) => {
                                        if let Some(inferred_ty) = params[i] {
                                            if ty != inferred_ty {
                                                return Ok(None);
                                            }
                                        } else {
                                            params[i] = Some(ty);
                                        }
                                        if let GenericElement::Array(_) = b {
                                            j += 2;
                                        } else if let Some(&GenericElement::ScopeStart) =
                                            arg_buffer.get(j + 1)
                                        {
                                            loop {
                                                if let Some(&GenericElement::ScopeEnd) =
                                                    arg_buffer.get(j)
                                                {
                                                    break;
                                                }
                                                j += 1;
                                            }
                                        }
                                    }
                                    _ => return Ok(None),
                                },
                                _ => return Ok(None),
                            }
                        }
                        j += 1;
                        i += 1;
                    }
                }
                arg_buffer.clear();
                j += 1;
            }
            i += length + 1;
        }

        let fun_ent = &self.state.funs[fun];
        let g_ent = &self.state.gfuns[g];
        let fun_module_id = self.state.modules[fun_ent.module].id;
        let mut id = FUN_SALT.add(fun_ent.name.hash);
        let vis = fun_ent.vis;
        let name = fun_ent.name.clone();
        let hint = fun_ent.hint.clone();
        let attrs = fun_ent.attrs.clone();
        let scope = fun_ent.scope;
        let ast_id = g_ent.ast;

        let mut shadowed = self.context.pool.get();
        let mut final_params = self.context.pool.get();

        for i in 0..params.len() {
            if let Some(ty) = params[i] {
                let id = self.state.gfuns[g].signature.params[i].add(fun_module_id);
                shadowed.push((id, self.state.types.link(id, ty)));
                final_params.push((id, ty));
            } else {
                return Ok(None);
            }
        }

        let ast = std::mem::take(&mut self.state.asts[ast_id]);
        let signature = self.parse_signature(module, &ast[0], &mut id)?;
        if signature.args.len() == 0 {
            for final_param in final_params.iter() {
                let tid = self.ty(final_param.1).id;
                id = id.add(tid);
            }
        }
        id = id.add(self.state.modules[module].id);
        self.state.asts[ast_id] = ast;

        for (id, ty) in shadowed.drain(..) {
            self.state.types.remove_link(id, ty);
        }

        if let Some(&fun) = self.state.funs.index(id) {
            return Ok(Some(fun));
        }

        let n_ent = NFunEnt {
            sig: signature,
            ast: ast_id,
        };

        let kind = FKind::Normal(self.state.nfuns.add(n_ent));

        let new_fun_ent = FunEnt {
            vis,
            id,
            module,
            hint,
            params: final_params.clone(),
            name,
            attrs,
            kind,
            scope,
        };

        let (shadowed, id) = self.state.funs.insert(id, new_fun_ent);
        debug_assert!(shadowed.is_none());

        self.state.unresolved.push(id);

        Ok(Some(id))
    }

    fn assert_type(&self, actual: Type, expected: Type, token: &Token) -> Result {
        if actual == expected {
            Ok(())
        } else {
            Err(FError::new(
                FEKind::TypeMismatch(actual, expected),
                token.clone(),
            ))
        }
    }

    fn collect(&mut self, module: Mod) -> Result {
        let module_id = self.state.modules[module].id;

        let mut globals = std::mem::take(&mut self.collector.globals);
        for Item { attrs, ast, scope } in globals.drain(..) {
            self.collect_global_var(ast, module, module_id, attrs, scope)?
        }
        self.collector.globals = globals;
        
        let mut functions = std::mem::take(&mut self.collector.functions);
        for Item { attrs, ast, scope } in functions.drain(..) {
            self.collect_fun(ast, module, module_id, attrs, scope)?
        }
        self.collector.functions = functions;

        Ok(())
    }

    fn collect_global_var(
        &mut self,
        mut ast: Ast,
        module: Mod,
        module_id: ID,
        attrs: Attrs,
        scope: Option<Scope>,
    ) -> Result {
        let scope_id = if let Some(scope) = scope {
            let scope = std::mem::take(&mut self.collector.scopes[scope]);    
            if scope.params.len() > 0 {
                return Err(FError::new(
                    FEKind::VarInsideGenericScope(scope.ty.token.clone()),
                    ast.token.clone(),
                ));
            }
            let ty = self.parse_type(module, &scope.ty)?; 
            self.ty(ty).id
        } else {
            ID(0)
        };

        let (vis, mutable) = match ast.kind {
            AKind::VarStatement(vis, mutable) => (vis, mutable),
            _ => unreachable!(),
        };

        for var_line in ast.iter_mut() {
            let ty = if var_line[1].kind != AKind::None {
                Some(self.parse_type(module, &var_line[1])?)
            } else {
                None
            };

            let mut values = std::mem::take(&mut var_line[2]);

            for (name, value) in var_line[0]
                .iter()
                .zip(values.drain(..).chain(std::iter::repeat(Ast::none())))
            {
                let hint = name.token.clone();
                let id = GLOBAL_SALT
                    .add(hint.spam.hash)
                    .add(scope_id)
                    .add(module_id);

                let g_ent = GlobalEnt {
                    vis,
                    mutable,
                    id,
                    module,
                    kind: GKind::Normal(value, ty),
                    hint,
                    attrs: attrs.clone(),
                    scope,
                };

                let (shadowed, id) = self.state.globals.insert(id, g_ent);

                if let Some(shadowed) = shadowed {
                    return Err(FError::new(
                        FEKind::RedefinedGlobal(shadowed.hint.clone()),
                        name.token.clone(),
                    ));
                }

                self.state.unresolved_globals.push(id);
            }
        }

        Ok(())
    }

    fn collect_fun(
        &mut self,
        ast: Ast,
        module: Mod,
        module_id: ID,
        attrs: Attrs,
        scope: Option<Scope>,
    ) -> Result {
        let vis = match ast.kind {
            AKind::Fun(vis) => vis,
            _ => unreachable!(),
        };

        let header = &ast[0];
        let hint = header.token.clone();
        let name = &header[0];
        let (name, mut id, kind, unresolved) = if name.kind == AKind::Ident {
            let mut fun_id = FUN_SALT.add(name.token.spam.hash);

            let signature = self.parse_signature(module, header, &mut fun_id)?;

            let name = name.token.spam.clone();

            let ast = self.state.asts.add(ast);
            let n_ent = NFunEnt {
                sig: signature,
                ast,
            };

            let n = self.state.nfuns.add(n_ent);
            (name, fun_id, FKind::Normal(n), true)
        } else if name.kind == AKind::Instantiation {
            let nm = &name[0];
            if nm.kind != AKind::Ident {
                return Err(FError::new(FEKind::InvalidFunctionHeader, nm.token.clone()));
            }

            let id = FUN_SALT.add(nm.token.spam.hash).add(GENERIC_FUN_SALT);

            let mut params = self.context.pool.get();
            for param in name[1..].iter() {
                let ty = TYPE_SALT.add(param.token.spam.hash);
                params.push(ty);
            }

            let mut arg_count = 0;
            let mut args = self.context.pool.get();
            for arg_section in &header[1..header.len() - 1] {
                let amount = arg_section.len() - 1;
                let idx = args.len();
                args.push(GenericElement::NextArgument(amount, 0));
                self.load_arg(module, &arg_section[amount], &params, &mut args)?;
                let additional = args.len() - idx - 1;
                args[idx] = GenericElement::NextArgument(amount, additional);
                arg_count += amount;
            }

            let signature = GenericSignature {
                params: params.clone(),
                elements: args.clone(),
                arg_count,
            };

            let nm = nm.token.spam.clone();

            let g_ent = GFunEnt {
                signature,
                ast: self.state.asts.add(ast),
                next: None,
            };

            let g = self.state.gfuns.add(g_ent);

            (nm, id, FKind::Generic(g), false)
        } else {
            return Err(FError::new(
                FEKind::InvalidFunctionHeader,
                name.token.clone(),
            ));
        };

        id = id.add(module_id);

        let fun_ent = FunEnt {
            vis,
            id,
            module,
            hint,
            params: vec![],
            kind,
            name,
            attrs,
            scope,
        };

        let (shadowed, id) = self.state.funs.insert(id, fun_ent);

        if let Some(shadowed) = shadowed {
            if unresolved {
                return Err(FError::new(
                    FEKind::Redefinition(shadowed.hint),
                    self.state.funs[id].hint.clone(),
                ));
            }

            // In the end generic funs with same module and name create a linked list
            // of which head is accessible from table.
            let gid = self.state.funs[id].kind.unwrap_generic();

            let id = self.state.funs.add_hidden(shadowed);
            self.state.gfuns[gid].next = Some(id);
        }

        if unresolved {
            self.state.unresolved.push(id);
        }

        Ok(())
    }

    fn parse_signature(
        &mut self,
        module: Mod,
        header: &Ast,
        fun_id: &mut ID,
    ) -> Result<FunSignature> {
        let mut args = self.context.pool.get();
        args.clear();

        for arg_section in &header[1..header.len() - 1] {
            let ty = self.parse_type(module, &arg_section[arg_section.len() - 1])?;
            for arg in arg_section[0..arg_section.len() - 1].iter() {
                let id = arg.token.spam.hash;
                *fun_id = fun_id.add(self.ty(ty).id);
                let val_ent = ValueEnt {
                    id,
                    ty,

                    ..ValueEnt::default()
                };
                args.push(val_ent);
            }
        }

        let raw_ret_ty = &header[header.len() - 1];
        let ret_ty = if raw_ret_ty.kind != AKind::None {
            Some(self.parse_type(module, raw_ret_ty)?)
        } else {
            None
        };

        Ok(FunSignature {
            args: args.clone(),
            ret_ty,
        })
    }

    fn load_arg(
        &mut self,
        module: Mod,
        ast: &Ast,
        params: &[ID],
        buffer: &mut Vec<GenericElement>,
    ) -> Result {
        let mut stack = self.context.pool.get();
        stack.push((ast, false));

        while let Some((ast, done)) = stack.last_mut() {
            if *done {
                if ast.kind == AKind::Instantiation {
                    buffer.push(GenericElement::ScopeEnd);
                }
                stack.pop();
                continue;
            }
            *done = true;
            let ast = *ast;
            match &ast.kind {
                AKind::Ident => {
                    let id = TYPE_SALT.add(ast.token.spam.hash);
                    if let Some(index) = params.iter().position(|&p| p == id) {
                        buffer.push(GenericElement::Parameter(index));
                    } else {
                        let ty = self.parse_type(module, ast)?;
                        buffer.push(GenericElement::Element(ty, None));
                    }
                }
                AKind::Instantiation => {
                    self.load_arg(module, &ast[0], params, buffer)?;
                    buffer.push(GenericElement::ScopeStart);
                    stack.extend(ast[1..].iter().map(|a| (a, false)));
                }
                &AKind::Ref => {
                    buffer.push(GenericElement::Pointer);

                    stack.push((&ast[0], false));
                }
                AKind::Array => {
                    buffer.push(GenericElement::Array(None));
                    stack.push((&ast[0], false));
                    stack.push((&ast[1], false));
                }
                AKind::Lit => {
                    let ty = self.parse_type(module, ast)?;
                    buffer.push(GenericElement::Element(ty, None));
                }
                _ => todo!("{}", AstDisplay::new(self.state, ast)),
            }
        }

        Ok(())
    }

    fn load_arg_from_datatype(
        &mut self,
        ty: Type,
        arg_buffer: &mut Vec<GenericElement>,
        stack: &mut Vec<(Type, bool)>,
    ) {
        stack.push((ty, false));

        while let Some((ty, done)) = stack.last_mut() {
            let ty = *ty;
            let ty_ent = &self.ty(ty);

            if *done {
                if !ty_ent.params.is_empty() {
                    arg_buffer.push(GenericElement::ScopeEnd);
                }
                stack.pop();
                continue;
            }

            *done = true;

            if ty_ent.params.is_empty() {
                if let TKind::Pointer(pointed) = ty_ent.kind {
                    arg_buffer.push(GenericElement::Pointer);
                    stack.push((pointed, false));
                } else if let TKind::Array(element, size) = ty_ent.kind {
                    arg_buffer.push(GenericElement::Array(Some(ty)));
                    stack.push((element, false));
                    let size = self.constant_of(TypeConst::Int(size as i64));
                    stack.push((size, false));
                } else {
                    arg_buffer.push(GenericElement::Element(ty, Some(ty)));
                }
                continue;
            }

            arg_buffer.push(GenericElement::Element(ty_ent.params[0], Some(ty)));

            arg_buffer.push(GenericElement::ScopeStart);
            stack.extend(ty_ent.params[1..].iter().map(|p| (*p, false)));
        }
    }

    fn find_loop(&self, token: &Token) -> std::result::Result<Loop, bool> {
        if token.spam.range.len() == 0 {
            return self.state.bstate.loops.last().cloned().ok_or(true);
        }

        let name = token.spam.hash;

        self.state
            .bstate
            .loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.state.bstate.loops.is_empty())
    }

    fn base_of_err(&mut self, ty: Type, token: &Token) -> Result<Type> {
        self.base_of(ty)
            .ok_or_else(|| FError::new(FEKind::NonPointerDereference, token.clone()))
    }

    fn base_of(&self, ty: Type) -> Option<Type> {
        match self.ty(ty).kind {
            TKind::Pointer(pointed) => Some(pointed),
            _ => None,
        }
    }

    fn parse_type(&mut self, module: Mod, ast: &Ast) -> Result<Type> {
        TParser::new(self.state, self.context, self.collector)
            .parse_type(module, ast)
            .map(|t| t.1)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))
    }

    fn pointer_of(&mut self, ty: Type) -> Type {
        TParser::new(self.state, self.context, self.collector).pointer_of(ty)
    }

    fn constant_of(&mut self, constant: TypeConst) -> Type {
        TParser::new(self.state, self.context, self.collector).constant_of(constant)
    }

    #[inline]
    pub fn is_pointer(&self, ty: Type) -> bool {
        matches!(self.ty(ty).kind, TKind::Pointer(..))
    }

    #[inline]
    fn pass_mutability(&mut self, from: Value, to: Value) {
        self.value_mut(to).mutable = self.value(from).mutable;
    }

    fn push_scope(&mut self) {
        self.state.bstate.frames.push(self.state.bstate.vars.len());
    }

    fn pop_scope(&mut self) {
        let idx = self.state.bstate.frames.pop().unwrap();
        self.state.bstate.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Value> {
        self.state
            .bstate
            .vars
            .iter()
            .rev()
            .find(|&&v| self.value(v).id == id)
            .cloned()
    }

    fn ty(&self, ty: Type) -> &TypeEnt {
        &self.state.types[ty]
    }

    fn inst(&self, inst: Inst) -> &InstEnt {
        &self.state.bstate.body.insts[inst]
    }

    fn inst_mut(&mut self, inst: Inst) -> &mut InstEnt {
        &mut self.state.bstate.body.insts[inst]
    }

    fn value(&self, value: Value) -> &ValueEnt {
        &self.state.bstate.body.values[value]
    }

    fn value_mut(&mut self, value: Value) -> &mut ValueEnt {
        &mut self.state.bstate.body.values[value]
    }

    fn array_of(&mut self, ty: Type, length: usize) -> Type {
        TParser::new(self.state, self.context, self.collector).array_of(ty, length)
    }

    fn clear_vars(&mut self) {
        self.state.bstate.vars.clear();
    }
}

crate::def_displayer!(
    FErrorDisplay,
    FState,
    FError,
    |self, f| {
        &FEKind::DuplicateEntrypoint(other) => {
            let other = self.state.funs[other].hint.clone();
            writeln!(
                f,
                "entrypoint already defined here:\n{}",
                TokenDisplay::new(self.state, &other)
            )?;
        },
        FEKind::TooShortAttribute(actual, expected) => {
            writeln!(
                f,
                "too short attribute, expected {} but got {}",
                expected, actual
            )?;
        },
        FEKind::InvalidCallConv => {
            writeln!(
                f,
                "Invalid call convention, list of valid call conventions:"
            )?;
            for cc in [
                "platform - picks call convention based of target platform",
                "fast",
                "cold - then its unlikely this gets called",
                "system_v",
                "windows_fastcall",
                "apple_aarch64",
                "baldrdash_system_v",
                "baldrdash_windows",
                "baldrdash_2020",
                "probestack",
                "wasmtime_system_v",
                "wasmtime_fastcall",
                "wasmtime_apple_aarch64",
            ] {
                writeln!(f, "  {}", cc)?;
            }
        },
        FEKind::InvalidLinkage => {
            writeln!(f, "Invalid linkage, valid linkages are:")?;
            for cc in ["import", "local", "export", "preemptible", "hidden"] {
                writeln!(f, "  {}", cc)?;
            }
        },
        FEKind::TypeError(error) => {
            writeln!(f, "{}", TErrorDisplay::new(self.state, &error))?;
        },
        FEKind::Redefinition(other) => {
            writeln!(f, "redefinition of\n{}", TokenDisplay::new(self.state, &other))?;
        },
        FEKind::InvalidBitCast(actual, expected) => {
            writeln!(
                f,
                "invalid bit-cast, expected type of size {} but got {}",
                expected, actual
            )?;
        },
        FEKind::AssignToImmutable => {
            writeln!(f, "cannot assign to immutable value")?;
        },
        FEKind::ExpectedValue => {
            writeln!(f, "expected this expression to have a value")?;
        },
        &FEKind::TypeMismatch(actual, expected) => {
            writeln!(
                f,
                "type mismatch, expected '{}' but got '{}'",
                TypeDisplay::new(&self.state, expected),
                TypeDisplay::new(&self.state, actual)
            )?;
        },
        FEKind::FunctionNotFound(name, arguments) => {
            writeln!(
                f,
                "function {}({}) does not exist within current scope",
                self.state.display(name),
                arguments
                    .iter()
                    .map(|t| format!("{}", TypeDisplay::new(&self.state, *t)))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        },
        FEKind::UnexpectedValue => {
            writeln!(
                f,
                "value not expected here, consider adding 'pass' after expression"
            )?;
        },
        FEKind::UnexpectedReturnValue => {
            writeln!(f, "return value not expected, if you want to return something, add '-> <type>' after '()' in signature")?;
        },
        FEKind::UnexpectedAuto => {
            writeln!(f, "'auto' not allowed here")?;
        },
        FEKind::UndefinedVariable => {
            writeln!(f, "cannot find variable in current scope")?;
        },
        FEKind::UnresolvedType => {
            writeln!(
                f,
                "type of this expression cannot be inferred, consider annotating the type"
            )?;
        },
        &FEKind::UnknownField(ty) => {
            writeln!(
                f,
                "unknown field for type '{}', type has this fields (embedded included):",
                TypeDisplay::new(&self.state, ty)
            )?;
            let mut frontier = vec![(ty, Spam::default(), true)];
            let mut i = 0;
            while i < frontier.len() {
                let (ty, _, embedded) = frontier[i];
                if !embedded {
                    continue;
                }
                match self.state.types[ty].kind {
                    TKind::Structure(sty) => {
                        for f in self.state.stypes[sty].fields.iter() {
                            frontier.push((f.ty, f.hint.spam.clone(), f.embedded));
                        }
                    },
                    _ => (),
                }
                i += 1;
            }

            for (ty, name, _) in frontier {
                writeln!(f, "  {}: {}", self.state.display(&name), TypeDisplay::new(&self.state, ty))?;
            }
        },
        FEKind::MutableRefOfImmutable => {
            writeln!(f, "cannot take mutable reference of immutable value")?;
        },
        FEKind::MissingElseBranch => {
            writeln!(f, "expected 'else' branch since 'if' branch returns value, consider adding 'pass' after last expression if this is intended")?;
        },
        FEKind::ContinueOutsideLoop => {
            writeln!(f, "cannot use 'continue' outside of loop")?;
        },
        FEKind::BreakOutsideLoop => {
            writeln!(f, "cannot use 'break' outside of loop")?;
        },
        FEKind::WrongLabel => {
            writeln!(f, "parent loop with this label does not exist")?;
        },
        FEKind::NonPointerDereference => {
            writeln!(f, "cannot dereference non-pointer type")?;
        },
        FEKind::InvalidFunctionHeader => {
            writeln!(f, "invalid function header, syntax for header is:\n  ident | op [ '[' ident {{ ',' ident }} ']' ]")?;
        },
        &FEKind::AmbiguousFunction(a, b) => {
            let a = self.state.funs[a].hint.clone();
            let b = self.state.funs[b].hint.clone();
            writeln!(
                f,
                "ambiguous function call, matches\n{}\nand\n{}",
                TokenDisplay::new(self.state, &a),
                TokenDisplay::new(self.state, &b)
            )?;
        },
        FEKind::EmptyArray => {
            writeln!(
                f,
                "cannot create empty array from '[]' syntax as type of element is unknown"
            )?;
        },
        FEKind::RedefinedGlobal(other) => {
            writeln!(
                f,
                "redefinition of global variable\n{}\n",
                TokenDisplay::new(self.state, &other)
            )?;
        },
        &FEKind::AmbiguousGlobal(a, b) => {
            let a = self.state.globals[a].hint.clone();
            let b = self.state.globals[b].hint.clone();
            writeln!(
                f,
                "ambiguous global variable, matches\n{}\nand\n{}",
                TokenDisplay::new(self.state, &a),
                TokenDisplay::new(self.state, &b)
            )?;
        },
        FEKind::InvalidEntrySignature => {
            writeln!(f, "invalid entry point signature, expected 'fun (int, & &u8)' or 'fun ()'")?;
        },
        FEKind::RecursiveInline => {
            writeln!(f, "cannot inline recursive function")?;
        },
        FEKind::VarInsideGenericScope(scope) => {
            writeln!(
                f,
                "cannot declare global inside generic scope\n{}",
                TokenDisplay::new(self.state, scope)
            )?;
        },
    }
);

#[derive(Debug)]
pub struct FError {
    pub kind: FEKind,
    pub token: Token,
}

impl FError {
    pub fn new(kind: FEKind, token: Token) -> Self {
        FError { kind, token }
    }
}

#[derive(Debug)]
pub enum FEKind {
    VarInsideGenericScope(Token),
    RecursiveInline,
    InvalidEntrySignature,
    EmptyArray,
    RedefinedGlobal(Token),
    DuplicateEntrypoint(Fun),
    TooShortAttribute(usize, usize),
    InvalidLinkage,
    InvalidCallConv,
    TypeError(TError),
    Redefinition(Token),
    InvalidBitCast(u32, u32),
    AssignToImmutable,
    ExpectedValue,
    TypeMismatch(Type, Type),
    FunctionNotFound(Spam, Vec<Type>),
    UnexpectedValue,
    UnexpectedReturnValue,
    UnexpectedAuto,
    UndefinedVariable,
    UnresolvedType,
    UnknownField(Type),
    MutableRefOfImmutable,
    MissingElseBranch,
    ContinueOutsideLoop,
    BreakOutsideLoop,
    WrongLabel,
    NonPointerDereference,
    InvalidFunctionHeader,
    AmbiguousFunction(Fun, Fun),
    AmbiguousGlobal(Global, Global),
}

pub enum DotInstr {
    None,
    Deref,
    Ref,
}

crate::index_pointer!(Fun);

#[derive(Debug, Clone, Default)]
pub struct FunEnt {
    pub vis: Vis,
    pub id: ID,
    pub module: Mod,
    pub hint: Token,
    pub params: Vec<(ID, Type)>,
    pub kind: FKind,
    pub name: Spam,
    pub attrs: Attrs,
    pub scope: Option<Scope>,
}

#[derive(Debug, Default, Clone)]
pub struct FunBody {
    pub values: List<Value, ValueEnt>,
    pub insts: LinkedList<Inst, InstEnt>,
    pub recursive: bool,
}

impl FunBody {
    pub fn clear(&mut self) {
        self.values.clear();
        self.insts.clear();
    }
}

#[derive(Debug, Clone)]
pub enum FKind {
    Builtin(Option<Type>),
    Generic(GFun),
    Normal(NFun),
    Represented(RFun),
    Compiled(CFun),
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Builtin(None)
    }
}

impl FKind {
    pub fn unwrap_generic(&self) -> GFun {
        match self {
            FKind::Generic(g) => *g,
            _ => panic!("{:?}", self),
        }
    }

    pub fn unwrap_normal(&self) -> NFun {
        match self {
            FKind::Normal(n) => *n,
            _ => panic!("{:?}", self),
        }
    }

    pub fn unwrap_represented(&self) -> RFun {
        match self {
            FKind::Represented(r) => *r,
            _ => panic!("{:?}", self),
        }
    }

    pub fn unwrap_compiled(&self) -> CFun {
        match self {
            FKind::Compiled(c) => *c,
            _ => panic!("{:?}", self),
        }
    }
}

crate::index_pointer!(NFun);

#[derive(Default)]
pub struct NFunEnt {
    pub sig: FunSignature,
    pub ast: GAst,
}

crate::index_pointer!(GFun);

pub struct GFunEnt {
    pub signature: GenericSignature,
    pub ast: GAst,
    pub next: Option<Fun>,
}

crate::index_pointer!(RFun);

pub struct RFunEnt {
    pub signature: FunSignature,
    pub ir_signature: Signature,
    pub id: FuncId,
    pub body: FunBody,
    pub inline: bool,
}

crate::index_pointer!(CFun);

#[derive(Debug, Clone)]
pub struct GenericSignature {
    pub params: Vec<ID>,
    pub elements: Vec<GenericElement>,
    pub arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericElement {
    ScopeStart,
    ScopeEnd,
    Pointer,
    Array(Option<Type>),
    ArraySize(u32),
    Element(Type, Option<Type>),
    Parameter(usize),
    NextArgument(usize, usize), // amount of arguments, amount of elements for representation
}

impl GenericElement {
    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (GenericElement::Element(id1, _), GenericElement::Element(id2, _)) => id1 == id2,
            (GenericElement::Array(_), GenericElement::Array(_)) => true,
            _ => self == other,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct FunSignature {
    pub args: Vec<ValueEnt>,
    pub ret_ty: Option<Type>,
}

crate::index_pointer!(Inst);

#[derive(Debug, Default, Clone)]
pub struct InstEnt {
    pub kind: IKind,
    pub value: Option<Value>,
    pub hint: Token,
    pub unresolved: usize,
}

impl InstEnt {
    pub fn new(kind: IKind, value: Option<Value>, hint: &Token) -> Self {
        Self {
            kind,
            value,
            hint: hint.clone(),
            unresolved: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub enum IKind {
    NoOp,
    GlobalLoad(Global),
    Call(Fun, Vec<Value>),
    UnresolvedCall(ID, &'static str, bool, Vec<Value>),
    UnresolvedDot(Value, ID),
    VarDecl(Value),
    Zeroed,
    Uninitialized,
    Lit(LTKind),
    Return(Option<Value>),
    Assign(Value),
    Block(Block),
    BlockEnd(Inst),
    Jump(Inst, Vec<Value>),
    JumpIfTrue(Value, Inst, Vec<Value>),
    Offset(Value),
    Deref(Value, bool),
    Ref(Value),
    Cast(Value),
}

impl IKind {
    pub fn is_closing(&self) -> bool {
        matches!(self, IKind::Jump(..) | IKind::Return(..))
    }

    pub fn block(&self) -> &Block {
        match self {
            IKind::Block(block) => block,
            _ => panic!("cannot access block on {:?}", self),
        }
    }

    pub fn block_mut(&mut self) -> &mut Block {
        match self {
            IKind::Block(block) => block,
            _ => panic!("cannot access block on {:?}", self),
        }
    }
}

impl Default for IKind {
    fn default() -> Self {
        IKind::NoOp
    }
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub block: Option<CrBlock>,
    pub args: Vec<Value>,
    pub end: Option<Inst>,
}

#[derive(Debug, Clone)]
pub struct Loop {
    name: ID,
    start_block: Inst,
    end_block: Inst,
}

crate::index_pointer!(Value);

#[derive(Debug, Clone, Default)]
pub struct ValueEnt {
    pub id: ID,
    pub ty: Type,
    pub inst: Option<Inst>,
    pub value: FinalValue,
    pub offset: u32,
    pub mutable: bool,
    pub on_stack: bool,
}

impl ValueEnt {
    pub fn new(name: ID, ty: Type, mutable: bool) -> Self {
        Self {
            id: name,
            ty,
            mutable,

            inst: None,
            value: FinalValue::None,
            offset: 0,
            on_stack: false,
        }
    }

    pub fn temp(ty: Type) -> Self {
        Self {
            id: ID(0),
            ty,
            inst: None,
            value: FinalValue::None,
            offset: 0,
            mutable: false,
            on_stack: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalValue {
    None,
    Zero,
    Value(CrValue),
    Pointer(CrValue),
    Var(CrVar),
    StackSlot(StackSlot),
}

impl Default for FinalValue {
    fn default() -> Self {
        FinalValue::None
    }
}

pub struct Program {
    pub module: ObjectModule,
}

impl Program {
    pub fn new(module: ObjectModule) -> Self {
        unsafe {
            POINTER_TYPE = module.isa().pointer_type();
        }
        Self { module }
    }
}

impl Default for Program {
    fn default() -> Self {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder().unwrap().finish(flags);
        let builder =
            ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();
        Self::new(ObjectModule::new(builder))
    }
}

crate::index_pointer!(Global);

pub struct GlobalEnt {
    pub id: ID,
    pub vis: Vis,
    pub module: Mod,
    pub mutable: bool,
    pub kind: GKind,
    pub hint: Token,
    pub attrs: Attrs,
    pub scope: Option<Scope>,
}

pub enum GKind {
    Normal(Ast, Option<Type>),
    Represented(DataId, Type),
}

#[derive(Default)]
pub struct BodyState {
    pub vars: Vec<Value>,
    pub loops: Vec<Loop>,
    pub frames: Vec<usize>,
    pub body: FunBody,
    pub block: Option<Inst>,
}

pub struct FState {
    pub t_state: TState,

    pub funs: Table<Fun, FunEnt>,
    pub nfuns: ReusableList<NFun, NFunEnt>,
    pub gfuns: List<GFun, GFunEnt>,
    pub rfuns: List<RFun, RFunEnt>,

    pub globals: Table<Global, GlobalEnt>,

    pub bstate: BodyState,
    pub main_bstate: BodyState,
    pub main_fun: Fun,

    pub unresolved_globals: Vec<Global>,
    pub resolved_globals: Vec<Global>,
    pub unresolved: Vec<Fun>,
    pub represented: Vec<Fun>,
    pub index_spam: Spam,

    pub linkage_hash: ID,
    pub entry_hash: ID,
    pub call_conv_hash: ID,
    pub inline_hash: ID,
    pub tls_hash: ID,
    pub thread_local_hash: ID,
}

crate::inherit!(FState, t_state, TState);

impl Default for FState {
    fn default() -> Self {
        let mut state = Self {
            t_state: TState::default(),
            funs: Table::new(),
            nfuns: ReusableList::new(),
            gfuns: List::new(),
            rfuns: List::new(),
            unresolved: Vec::new(),
            represented: Vec::new(),
            index_spam: Spam::default(),
            globals: Table::new(),
            bstate: BodyState::default(),
            main_bstate: BodyState::default(),
            unresolved_globals: Vec::new(),
            main_fun: Fun::default(),
            resolved_globals: Vec::new(),

            linkage_hash: ID::new("linkage"),
            entry_hash: ID::new("entry"),
            call_conv_hash: ID::new("call_conv"),
            inline_hash: ID::new("inline"),
            tls_hash: ID::new("tls"),
            thread_local_hash: ID::new("thread_local"),
        };

        let count = state
            .main_bstate
            .body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));
        let args = state
            .main_bstate
            .body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));

        let entry_point = state.main_bstate.body.insts.push(InstEnt::new(
            IKind::Block(Block {
                block: None,
                args: vec![count, args],
                end: None,
            }),
            None,
            &Token::default(),
        ));

        let zero_value = state
            .main_bstate
            .body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));
        state.main_bstate.body.insts.push(InstEnt::new(
            IKind::Zeroed,
            Some(zero_value),
            &Token::default(),
        ));
        let value =
            state
                .main_bstate
                .body
                .values
                .add(ValueEnt::new(ID(0), state.builtin_repo.int, true));
        state.main_bstate.body.insts.push(InstEnt::new(
            IKind::VarDecl(zero_value),
            Some(value),
            &Token::default(),
        ));

        state.main_bstate.vars.push(value);

        state.main_bstate.block = Some(entry_point);

        let n_fun = NFunEnt {
            sig: FunSignature {
                args: vec![
                    ValueEnt::new(ID(0), state.builtin_repo.int, true), //arg count
                    ValueEnt::new(ID(0), state.builtin_repo.int, true), //args
                ],
                ret_ty: Some(state.builtin_repo.int),
            },
            ast: GAst::default(),
        };

        let n = state.nfuns.add(n_fun);

        let main_fun = FunEnt {
            id: ID(0),
            vis: Vis::Public,
            module: Mod::default(),
            kind: FKind::Normal(n),
            hint: Token::default(),
            attrs: Attrs::default(),
            params: Vec::new(),
            name: state.builtin_spam("main"),
            scope: None,
        };

        state.main_fun = state.funs.add_hidden(main_fun);

        let spam = state.builtin_spam("__index__");

        state.index_spam = spam;

        let module_id = state.modules[state.builtin_module].id;

        let types = state.builtin_repo.type_list();

        fn create_builtin_fun(
            state: &mut FState,
            module: ID,
            name: Spam,
            args: &[Type],
            ret_ty: Option<Type>,
        ) {
            let mut id = FUN_SALT.add(name.hash);
            for &arg in args {
                id = id.add(state.types[arg].id);
            }
            id = id.add(module);
            let fun_ent = FunEnt {
                id,
                name,
                vis: Vis::Public,
                module: state.builtin_module,
                hint: Token::default(),
                params: vec![],
                kind: FKind::Builtin(ret_ty),
                attrs: Attrs::default(),
                scope: None,
            };
            assert!(state.funs.insert(id, fun_ent).0.is_none());
        }

        for i in types {
            for j in types {
                let name = state.types[i].name.clone();
                create_builtin_fun(&mut state, module_id, name, &[j], Some(i));
            }
        }

        let integer_types = &[
            state.builtin_repo.i8,
            state.builtin_repo.i16,
            state.builtin_repo.i32,
            state.builtin_repo.i64,
            state.builtin_repo.u8,
            state.builtin_repo.u16,
            state.builtin_repo.u32,
            state.builtin_repo.u64,
            state.builtin_repo.int,
            state.builtin_repo.uint,
        ][..];

        let builtin_unary_ops = [
            ("~ + ++ --", integer_types),
            (
                "- abs",
                &[
                    state.builtin_repo.i8,
                    state.builtin_repo.i16,
                    state.builtin_repo.i32,
                    state.builtin_repo.i64,
                    state.builtin_repo.f32,
                    state.builtin_repo.f64,
                    state.builtin_repo.int,
                ][..],
            ),
            ("!", &[state.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_unary_ops.iter() {
            for op in operators.split(' ') {
                let op = state.builtin_spam(op);
                for &datatype in types.iter() {
                    create_builtin_fun(
                        &mut state,
                        module_id,
                        op.clone(),
                        &[datatype],
                        Some(datatype),
                    );
                }
            }
        }

        let builtin_bin_ops = [
            ("+ - * / == != >= <= > < ^ | & >> <<", integer_types),
            (
                "+ - * / == != >= <= > <",
                &[state.builtin_repo.f32, state.builtin_repo.f64][..],
            ),
            ("&& || ^ | &", &[state.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_bin_ops.iter() {
            for op in operators.split(' ') {
                let op_spam = state.builtin_spam(op);
                for &ty in types.iter() {
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        state.builtin_repo.bool
                    } else {
                        ty
                    };

                    create_builtin_fun(
                        &mut state,
                        module_id,
                        op_spam.clone(),
                        &[ty, ty],
                        Some(return_type),
                    );
                }
            }
        }

        state
    }
}

pub struct FContext {
    pub t_context: TContext,
    pub body_pool: Vec<FunBody>,
    pub signature: Signature,
}

crate::inherit!(FContext, t_context, TContext);

impl Default for FContext {
    fn default() -> Self {
        Self {
            t_context: TContext::default(),
            body_pool: Vec::new(),
            signature: Signature::new(CallConv::Fast),
        }
    }
}

pub fn write_base36(mut number: u64, buffer: &mut Vec<u8>) {
    while number > 0 {
        let mut digit = (number % 36) as u8;
        digit += (digit < 10) as u8 * b'0' + (digit >= 10) as u8 * (b'a' - 10);
        buffer.push(digit);
        number /= 36;
    }
}

pub fn assert_attr_len(attr: &Ast, len: usize) -> Result {
    if attr.len() - 1 < len {
        Err(FError::new(
            FEKind::TooShortAttribute(attr.len(), len),
            attr.token.clone(),
        ))
    } else {
        Ok(())
    }
}

pub struct FunDisplay<'a> {
    pub state: &'a FState,
    pub fun: Fun,
}

impl<'a> FunDisplay<'a> {
    pub fn new(state: &'a FState, fun: Fun) -> Self {
        Self { state, fun }
    }
}

impl std::fmt::Display for FunDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let fun = &self.state.funs[self.fun];
        let rid = match fun.kind {
            FKind::Represented(rid) => rid,
            _ => unreachable!(),
        };

        let r_ent = &self.state.rfuns[rid];

        writeln!(f, "{}", self.state.display(&fun.hint.spam))?;
        writeln!(f)?;

        for (i, inst) in r_ent.body.insts.iter() {
            match &inst.kind {
                IKind::Block(block) => {
                    writeln!(f, "  {}{:?}", i, block.args)?;
                }
                IKind::BlockEnd(_) => {
                    writeln!(f)?;
                }
                _ => {
                    if let Some(value) = inst.value {
                        let ty = TypeDisplay::new(&self.state, r_ent.body.values[value].ty);
                        writeln!(
                            f,
                            "    {:?}: {} = {:?} |{}",
                            value,
                            ty,
                            inst.kind,
                            self.state.display(&inst.hint.spam)
                        )?;
                    } else {
                        writeln!(
                            f,
                            "    {:?} |{}",
                            inst.kind,
                            self.state.display(&inst.hint.spam)
                        )?;
                    }
                }
            }
        }

        Ok(())
    }
}

pub fn test() {
    /*let mut program = Program::default();

    let mut state = FState::default();
    let mut context = FContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/functions/test_project")
        .unwrap();

    for &module in std::mem::take(&mut state.module_order).iter().rev() {
        FParser::new(&mut program, &mut state, &mut context)
            .parse(module)
            .map_err(|e| println!("{}", FErrorDisplay::new(&state, &e)))
            .unwrap();
    }*/
}
