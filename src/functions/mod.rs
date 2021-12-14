use core::panic;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use crate::ast::{AKind, Ast, Vis};
use crate::lexer::Token;
use crate::lexer::{TKind as LTKind, TokenView};
use crate::module_tree::*;
use crate::types::Type;
use crate::types::*;
use crate::util::storage::{LinkedList, ReusableList, Table};
use crate::util::{
    sdbm::{SdbmHashState, ID},
    storage::{IndexPointer, List},
};

use cranelift_codegen::ir::{
    AbiParam, ArgumentPurpose, Block as CrBlock, Signature, StackSlot, Value as CrValue,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_frontend::Variable as CrVar;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

type Result<T = ()> = std::result::Result<T, FError>;
type ExprResult = Result<Option<Value>>;

pub const FUN_SALT: ID = ID(0xDEADBEEF);
pub const GENERIC_FUN_SALT: ID = ID(0xFAEFACBD);

pub struct FParser<'a> {
    program: &'a mut Program,
    state: &'a mut FState,
    context: &'a mut FContext,
}

impl<'a> FParser<'a> {
    pub fn new(program: &'a mut Program, state: &'a mut FState, context: &'a mut FContext) -> Self {
        Self {
            program,
            state,
            context,
        }
    }

    pub fn parse(mut self, module: Mod) -> Result {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .parse(module)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))?;

        self.collect(module)?;

        self.translate()?;

        Ok(())
    }

    fn translate(&mut self) -> Result {
        
        while let Some(fun) = self.state.unresolved.pop() {
            self.state.body = self.context.body_pool.pop().unwrap_or_default();
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
        self.state.vars.clear();
        for arg in args.iter() {
            let var = self.state.body.values.add(arg.clone());
            self.state.vars.push(var);
            arg_buffer.push(var);
        }
        if let Some(ret_ty) = ret_ty {
            if self.state.types[ret_ty].on_stack() {
                let ty = self.pointer_of(ret_ty);
                let value = self.new_anonymous_value(ty, false);
                arg_buffer.push(value);
            }
        }
        self.state.nfuns[nid].sig.args = args;
        self.state.body.insts[entry_point].kind.block_mut().args = arg_buffer.clone();

        let value = self.block(fun, &ast[1])?;

        let n_ent = &self.state.nfuns[nid];

        if let (Some(value), Some(_), Some(ret_ty)) = (value, self.state.block, n_ent.sig.ret_ty) {
            let value_ty = self.state.body.values[value].ty;
            let token = &ast[1].last().unwrap().token;
            self.assert_type(value_ty, ret_ty, token)?;
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if let (Some(ret_ty), Some(_)) = (n_ent.sig.ret_ty, self.state.block) {
            let value = self.new_temp_value(ret_ty);
            let token = &ast[1].last().unwrap().token;
            self.add_inst(InstEnt::new(IKind::Zeroed, Some(value), token));
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if self.state.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Return(None),
                None,
                &ast[1].last().unwrap_or(&Ast::none()).token,
            ));
        }

        self.state.asts[n_ent_ast] = ast;

        for value_id in self.state.body.values.ids() {
            let ty = self.state.body.values[value_id].ty;
            let on_stack = self.state.types[ty].on_stack();
            self.state.body.values[value_id].on_stack =
                self.state.body.values[value_id].on_stack || on_stack;
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
        let attr_id = fun_ent.attr_id;

        if disposable {
            let ast = self.state.asts.remove(n_ent.ast);
            self.context.recycle(ast);
        }

        let mut name_buffer = self.context.pool.get();
        
        write_base36(fun_id.0, &mut name_buffer);
        
        let name = unsafe { std::str::from_utf8_unchecked(&name_buffer[..]) };
        let attributes = &self.state.modules[self.state.funs[fun].module].attributes;

        let (linkage, alias) =
            if let Some(attr) = attributes.get_attr(attr_id, "linkage") {
                assert_attr_len(attr, 1)?;

                let linkage = match attr[1].token.spam.raw() {
                    "import" => Linkage::Import,
                    "local" => Linkage::Local,
                    "export" => Linkage::Export,
                    "preemptible" => Linkage::Preemptible,
                    "hidden" => Linkage::Hidden,
                    _ => return Err(FError::new(FEKind::InvalidLinkage, attr.token.clone())),
                };

                if attr.len() > 2 {
                    (linkage, attr[2].token.spam.raw())
                } else if linkage == Linkage::Import {
                    (linkage, self.state.funs[fun].name)
                } else {
                    (linkage, name)
                }
            } else {
                (Linkage::Export, name)
            };

        let call_conv = if let Some(attr) = attributes.get_attr(attr_id, "call_conv") {
            assert_attr_len(attr, 1)?;
            let conv = attr[1].token.spam.raw();
            if conv == "platform" {
                let triple = self.program.module.isa().triple();
                CallConv::triple_default(triple)
            } else {
                CallConv::from_str(conv)
                    .map_err(|_| FError::new(FEKind::InvalidCallConv, attr.token.clone()))?
            }
        } else {
            CallConv::Fast
        };

        let mut signature =
            std::mem::replace(&mut self.context.signature, Signature::new(CallConv::Fast));
        signature.clear(call_conv);

        for arg in n_ent.sig.args.iter() {
            let repr = self.state.types[arg.ty].repr();
            signature.params.push(AbiParam::new(repr));
        }

        if let Some(ret_ty) = n_ent.sig.ret_ty {
            let ret_ty = &self.state.types[ret_ty];
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

        let alias = if let Some(attr) = attributes.get_attr(attr_id, "entry") {
            if let Some(entry) = self.state.entry_point {
                return Err(FError::new(
                    FEKind::DuplicateEntrypoint(entry),
                    attr.token.clone(),
                ));
            } else {
                self.state.entry_point = Some(fun);
            }
            "main"
        } else {
            alias
        };

        let id = self
            .program
            .module
            .declare_function(alias, linkage, &signature)
            .unwrap();

        let r_ent = RFunEnt {
            signature: n_ent.sig,
            ir_signature: signature.clone(),
            id,
            body: std::mem::take(&mut self.state.body),
        };

        let f = self.state.rfuns.add(r_ent);
        self.state.funs[fun].kind = FKind::Represented(f);

        self.state.represented.push(fun);

        Ok(())
    }

    fn return_value(&mut self, fun: Fun, value: Value, token: &Token) -> Value {
        let ty = self.return_type_of(fun).unwrap();
        if self.state.types[ty].on_stack() {
            let entry = self.state.body.insts.first().unwrap();
            let return_value = self.state.body.insts[entry]
                .kind
                .block()
                .args
                .last()
                .unwrap()
                .clone();

            let deref = self.new_temp_value(ty);
            self.add_inst(InstEnt::new(
                IKind::Deref(return_value),
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
            if self.state.block.is_none() {
                break;
            }
            self.statement(fun, statement)?;
        }

        let value = if self.state.block.is_some() {
            self.statement(fun, ast.last().unwrap())?
        } else {
            None
        };

        self.pop_scope();

        Ok(value)
    }

    fn statement(&mut self, fun: Fun, statement: &Ast) -> ExprResult {
        match statement.kind {
            AKind::VarStatement(_) => self.var_statement(fun, statement)?,
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
            let current_value = self.state.body.insts[loop_header.end_block]
                .kind
                .block()
                .args
                .first()
                .cloned();
            if current_value.is_none() {
                let ty = self.state.body.values[return_value].ty;
                let value = self.new_temp_value(ty);
                self.state.body.insts[loop_header.end_block]
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
            let actual_type = self.state.body.values[value].ty;
            self.assert_type(actual_type, ty, &ast[0].token)?;
            Some(self.return_value(fun, value, &ast.token))
        };

        self.add_inst(InstEnt::new(IKind::Return(value), None, &ast.token));

        Ok(())
    }

    fn var_statement(&mut self, fun: Fun, statement: &Ast) -> Result {
        let mutable = statement.kind == AKind::VarStatement(true);
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
                    let name = ID(0).add(name.token.spam.deref());

                    let temp_value = self.state.body.values.add(ValueEnt::temp(ty));

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
                    let name = ID(0).add(name.token.spam.deref());
                    let value = self.expr(fun, raw_value)?;
                    let actual_datatype = self.state.body.values[value].ty;

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
            _ => todo!("unmatched expr ast {}", ast),
        }
    }

    fn index(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let target = self.expr(fun, &ast[0])?;
        let index = self.expr(fun, &ast[1])?;
        let id = FUN_SALT.add("__index__");
        let args = &[target, index];
        let result = self.call_low(fun, id, "__index__", true, &[], args, &ast.token)?
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
                self.assert_type(self.state.body.values[value].ty, ty, &raw_value.token)?;
            } else {
                element_ty = Some(self.state.body.values[value].ty);
            }
            values.push(value);
        }

        if element_ty.is_none() {
            return Err(FError::new(FEKind::EmptyArray, ast.token.clone()));
        }

        let element_ty = element_ty.unwrap();
        let element_size = self.state.types[element_ty].size;

        let ty = self.array_of(element_ty, length);

        let result = self.new_anonymous_value(ty, true);
        self.add_inst(InstEnt::new(
            IKind::Uninitialized,
            Some(result),
            &ast.token,
        ));

        for (i, &value) in values.iter().enumerate() {
            let offset = self.new_anonymous_value(element_ty, false);
            self.state.body.values[offset].offset = i as u32 * element_size;
            self.add_inst(InstEnt::new(
                IKind::Offset(result),
                Some(offset),
                &ast.token,
            ));
            self.add_inst(InstEnt::new(
                IKind::Assign(offset),
                Some(value),
                &ast.token,
            ));
        }

        Ok(Some(result))
    }

    fn ref_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let value = self.expr(fun, &ast[0])?;

        let reference = self.ref_expr_low(value, &ast.token);

        Ok(Some(reference))
    }

    fn ref_expr_low(&mut self, value: Value, token: &Token) -> Value {
        let ty = self.state.body.values[value].ty;
        let ty = self.pointer_of(ty);
        let reference = self.new_temp_value(ty);
        self.add_inst(
            InstEnt::new(IKind::Ref(value), Some(reference), token),
        );

        // we need to allocate it since register cannot be referenced
        let mut current = reference;
        loop {
            let value = &mut self.state.body.values[current];
            if value.on_stack {
                break;
            }
            value.on_stack = true;

            if let Some(inst) = value.inst {
                match &self.state.body.insts[inst].kind {
                    IKind::Offset(value) => {
                        current = *value;
                        continue;
                    }
                    IKind::Cast(value) => {
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
        let ty = self.state.body.values[value].ty;
        let pointed = self.base_of_err(ty, token)?;

        let val = self.new_anonymous_value(pointed, true);
        self.add_inst(InstEnt::new(IKind::Deref(value), Some(val), token));

        Ok(val)
    }

    fn unary_op(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let name = FUN_SALT.add(ast[0].token.spam.deref());
        let value = self.expr(fun, &ast[1])?;

        let mut values = self.context.pool.get();
        values.push(value);
        self.call_low(
            fun,
            name,
            ast[0].token.spam.raw(),
            false,
            &[],
            &values,
            &ast.token,
        )
    }

    fn dot_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let header = self.expr(fun, &ast[0])?;
        let mutable = self.state.body.values[header].mutable;
        let field = ID(0).add(ast[1].token.spam.deref());

        let inst = self.add_inst(InstEnt::new(IKind::NoOp, None, &Token::default()));
        let value = self.new_anonymous_value(self.state.builtin_repo.bool, mutable);
        self.state.body.values[value].inst = Some(inst);
        let ty = self.field_access(header, field, value, &ast.token)?;
        self.state.body.insts.remove(inst);
        self.state.body.values[value].ty = ty;
        Ok(Some(value))
    }

    fn find_field(&mut self, ty: Type, field_id: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = self.context.pool.get();
        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            let sid = match &self.state.types[frontier[i].2].kind {
                &TKind::Structure(sid) => sid,
                &TKind::Pointer(pointed) => match &self.state.types[pointed].kind {
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
        let name = ID(0).add(ast[0].token.spam.deref());

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

        self.state.loops.push(header);
        self.make_block_current(start_block);
        self.block(fun, &ast[1])?;
        self.state
            .loops
            .pop()
            .expect("expected previously pushed header");

        if self.state.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Jump(start_block, vec![]),
                None,
                &ast.token,
            ));
        }
        self.make_block_current(end_block);

        let value = if self.state.body.insts[end_block]
            .kind
            .block()
            .args
            .is_empty()
        {
            None
        } else {
            Some(self.state.body.insts[end_block].kind.block().args[0])
        };

        Ok(value)
    }

    fn if_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let cond_expr = &ast[0];
        let cond_val = self.expr(fun, cond_expr)?;
        let cond_type = self.state.body.values[cond_val].ty;

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

            let ty = self.state.body.values[val].ty;
            let value = self.new_temp_value(ty);
            self.state.body.insts[merge_block]
                .kind
                .block_mut()
                .args
                .push(value);
            result = Some(value);
        } else if self.state.block.is_some() {
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

                    let ty = self.state.body.values[val].ty;
                    let value = self.new_temp_value(ty);
                    self.state.body.insts[merge_block]
                        .kind
                        .block_mut()
                        .args
                        .push(value);
                    result = Some(value);
                } else {
                    return Err(FError::new(FEKind::UnexpectedValue, ast.token.clone()));
                }
            } else {
                if self.state.block.is_some() {
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
        let (base_name, name) = match ast[0].kind {
            AKind::Ident => (
                FUN_SALT.add(ast[0].token.spam.deref()),
                ast[0].token.spam.raw(),
            ),
            AKind::Instantiation => {
                for arg in ast[0][1..].iter() {
                    let id = self.parse_type(module, arg)?;
                    generic_params.push(id);
                }
                (
                    FUN_SALT.add(ast[0][0].token.spam.deref()),
                    ast[0][0].token.spam.raw(),
                )
            }
            _ => unreachable!(),
        };

        let mut buffer = self.context.pool.get();
        for value in ast[1..].iter() {
            let value = self.expr(fun, value)?;
            buffer.push(value);
        }

        self.call_low(
            fun,
            base_name,
            name,
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
        name: &'static str,
        dot_call: bool,
        params: &[Type],
        values: &[Value],
        token: &Token,
    ) -> ExprResult {
        let mut values = values.to_vec();
        let module = self.state.funs[fun].module;
        
        let fun =
            self.smart_find_or_create(module, base_name, name, params, &mut values, dot_call, token)?;
        let return_type = self.return_type_of(fun);

        let value = return_type.map(|t| {
            let on_stack = self.state.types[t].on_stack();
            let value = self.new_anonymous_value(t, on_stack);
            if on_stack {
                values.push(value);
            }
            value
        });

        self.add_inst(InstEnt::new(IKind::Call(fun, values), value, token));

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
        let name = ID(0).add(ast.token.spam.raw());
        self.find_variable(name)
            .or_else(|| {
                let name = TYPE_SALT
                    .add(ast.token.spam.raw())
                    .combine(self.state.modules[self.state.funs[fun].module].id);
                if let Some(&(_, ty)) = self
                    .state
                    .funs[fun]
                    .params
                    .iter()
                    .find(|&(p, _)| *p == name)
                {
                    let ty = &self.state.types[ty].kind;
                    match ty {
                        TKind::Const(t) => {
                            let (kind, ty) = match t.clone() {
                                TypeConst::Bool(val) => (LTKind::Bool(val), self.state.builtin_repo.bool),
                                TypeConst::Int(val) => (LTKind::Int(val, 0), self.state.builtin_repo.int),
                                TypeConst::Float(val) => (LTKind::Float(val, 64), self.state.builtin_repo.f64),
                                TypeConst::Char(val) => (LTKind::Char(val), self.state.builtin_repo.u32),
                                TypeConst::String(val) => (LTKind::String(val), self.pointer_of(self.state.builtin_repo.u8)),
                            };
                            
                            let value = self.new_temp_value(ty);
                            self.add_inst(InstEnt::new(
                                IKind::Lit(kind),
                                Some(value),
                                &ast.token,
                            ));
                            Some(value)
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .ok_or_else(|| FError::new(FEKind::UndefinedVariable, ast.token.clone()))
            .map(|var| Some(var))
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
            _ => unreachable!("{}", ast),
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
        match ast[0].token.spam.deref() {
            "=" => return self.assignment(fun, ast),
            "as" => return self.bit_cast(fun, ast),
            _ => (),
        }

        let left = self.expr(fun, &ast[1])?;
        let right = self.expr(fun, &ast[2])?;

        let base_id = FUN_SALT.add(ast[0].token.spam.deref());

        let mut buffer = self.context.pool.get();
        buffer.extend(&[left, right]);

        self.call_low(
            fun,
            base_id,
            ast[0].token.spam.raw(),
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

        let original_datatype = self.state.body.values[target].ty;
        let original_size = self.state.types[original_datatype].size;
        let datatype_size = self.state.types[ty].size;

        if original_size != datatype_size {
            return Err(FError::new(
                FEKind::InvalidBitCast(original_size, datatype_size),
                ast.token.clone(),
            ));
        }

        let value = self.new_anonymous_value(ty, self.state.body.values[target].mutable);
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
        let mutable = self.state.body.values[header].mutable;
        let header_datatype = self.state.body.values[header].ty;
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
            match &self.state.types[current_type].kind {
                &TKind::Structure(sid) => {
                    let field = &self.state.stypes[sid].fields[i];
                    offset += field.offset;
                    current_type = field.ty;
                }
                &TKind::Pointer(pointed) => {
                    let value = self.new_anonymous_value(current_type, mutable);
                    self.state.body.values[value].offset = offset;
                    self.add_inst(InstEnt::new(IKind::Offset(header), Some(value), &token));
                    

                    match &self.state.types[pointed].kind {
                        &TKind::Structure(sid) => {
                            let field = &self.state.stypes[sid].fields[i];
                            offset = field.offset;
                            current_type = field.ty;
                            let loaded = self.new_anonymous_value(pointed, mutable);
                            self.add_inst(InstEnt::new(IKind::Deref(value), Some(loaded), &token));
                            header = loaded;
                            self.state.body.values[loaded].offset = offset;
                        }
                        _ => unreachable!(),
                    }
                }
                _ => todo!("{:?}", self.state.types[current_type]),
            }
        }

        let inst = self.add_inst(InstEnt::new(IKind::Offset(header), Some(value), token));

        let val = &mut self.state.body.values[value];
        val.inst = Some(inst);
        val.offset = offset;
        val.ty = current_type;

        Ok(current_type)
    }

    fn inst_of(&mut self, value: Value) -> Inst {
        // if inst is none then this is function parameter and its safe to put it
        // at the beginning of the entry block
        self.state.body.values[value]
            .inst
            .unwrap_or(self.state.body.insts.first().unwrap())
    }

    pub fn add_variable(&mut self, name: ID, ty: Type, mutable: bool) -> Value {
        let val = self.new_value(name, ty, mutable);
        self.state.vars.push(val);
        val
    }

    fn assignment(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let target = self.expr(fun, &ast[1])?;
        let value = self.expr(fun, &ast[2])?;
        let target_datatype = self.state.body.values[target].ty;
        let value_datatype = self.state.body.values[value].ty;

        if !self.state.body.values[target].mutable {
            return Err(FError::new(FEKind::AssignToImmutable, ast.token.clone()));
        }

        
        self.assert_type(value_datatype, target_datatype, &ast.token)?;

        self.add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

        Ok(Some(value))
    }

    fn smart_find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &str,
        params: &[Type],
        args: &mut [Value],
        dot_expr: bool,
        token: &Token,
    ) -> Result<Fun> {
        let mut types = self.context.pool.get();
        types.clear();
        types.extend(args.iter().map(|&v| self.state.body.values[v].ty));

        let result = if dot_expr {
            let first_mutable = self.state.body.values[args[0]].mutable;
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
        self.state.body.values.add(value)
    }

    pub fn add_inst(&mut self, inst: InstEnt) -> Inst {
        debug_assert!(self.state.block.is_some(), "no block to add inst to");
        let closing = inst.kind.is_closing();
        let value = inst.value;
        let inst = self.state.body.insts.push(inst);
        if let Some(value) = value {
            self.state.body.values[value].inst = Some(inst);
        }
        if closing {
            self.close_block();
        }
        inst
    }

    pub fn add_inst_above(&mut self, inst: InstEnt, at: Inst) -> Inst {
        debug_assert!(!inst.kind.is_closing(), "cannot insert closing instruction");
        let value = inst.value;
        let inst = self.state.body.insts.insert_before(at, inst);
        if let Some(value) = value {
            self.state.body.values[value].inst = Some(inst);
        }
        inst
    }

    pub fn new_block(&mut self) -> Inst {
        self.state.body.insts.add_hidden(InstEnt::new(
            IKind::Block(Default::default()),
            None,
            &Token::default(),
        ))
    }

    pub fn make_block_current(&mut self, block: Inst) {
        debug_assert!(self.state.block.is_none(), "current block is not closed");
        self.state.body.insts.show_as_last(block);
        self.state.block = Some(block);
    }

    pub fn close_block(&mut self) {
        debug_assert!(self.state.block.is_some(), "no block to close");
        let block = self.state.block.unwrap();
        let inst = self.state.body.insts.push(InstEnt::new(
            IKind::BlockEnd(block),
            None,
            &Token::default(),
        ));
        self.state.body.insts[block].kind.block_mut().end = Some(inst);
        self.state.block = None;
    }

    fn dot_find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &str,
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

            match &self.state.types[ty].kind {
                &TKind::Structure(id) => {
                    for field in self.state.stypes[id].fields.iter().filter(|f| f.embedded) {
                        frontier.push((field.ty, field.id));
                    }
                }
                &TKind::Pointer(pointed) => match &self.state.types[pointed].kind {
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
        name: &str,
        params: &[Type],
        values: &[Type],
        token: &Token,
    ) -> Result<Fun> {
        let mut specific_id = values
            .iter()
            .fold(base, |base, &val| base.combine(self.state.types[val].id));
        
        if values.len() == 0 {
            for &ty in params {
                specific_id = specific_id.combine(self.state.types[ty].id);
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
            if let Some(fun) =
                self.find_or_create_low(specific_id, module_id, base, module, params, values, token)?
            {
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
                FEKind::FunctionNotFound(name.to_string(), values.to_vec()),
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
        if let Some(&fun) = self.state.funs.index(specific_id.combine(module_id)) {
            return Ok(Some(fun));
        }

        let mut g_fun = self
            .state
            .funs
            .index(base.combine(GENERIC_FUN_SALT).combine(module_id))
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

    fn create(&mut self, module: Mod, fun: Fun, g: GFun, explicit_params: &[Type], values: &[Type]) -> Result<Option<Fun>> {
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
        while i <  g_ent_len {
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
                                GenericElement::Parameter(i) => {
                                    match b {
                                        GenericElement::Element(_, Some(ty)) | GenericElement::Array(Some(ty)) => {
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
                                    }
                                }
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
        let mut id = FUN_SALT.add(fun_ent.name);
        let vis = fun_ent.vis;
        let name = fun_ent.name;
        let hint = fun_ent.hint.clone();
        let attr_id = fun_ent.attr_id;
        let ast_id = g_ent.ast;

        let mut shadowed = self.context.pool.get();
        let mut final_params = self.context.pool.get();

        for i in 0..params.len() {
            if let Some(ty) = params[i] {
                let id = self.state.gfuns[g].signature.params[i].combine(fun_module_id);
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
                let tid = self.state.types[final_param.1].id;
                id = id.combine(tid);
            }
        }
        id = id.combine(self.state.modules[module].id);
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
            attr_id,
            kind,
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
        let mut ast = std::mem::take(&mut self.state.parsed_ast);

        for (attr_id, a) in ast.iter_mut().enumerate() {
            match &a.kind {
                &AKind::Fun(vis) => {
                    self.collect_fun(std::mem::take(a), module, module_id, vis, attr_id)?
                }
                _ => (),
            }
        }

        Ok(())
    }

    fn collect_fun(
        &mut self,
        ast: Ast,
        module: Mod,
        module_id: ID,
        vis: Vis,
        attr_id: usize,
    ) -> Result {
        let header = &ast[0];
        let hint = header.token.clone();
        let name = &header[0];
        let (name, mut id, kind, unresolved) = if name.kind == AKind::Ident {
            let name = name.token.spam.raw();
            let mut fun_id = FUN_SALT.add(name);

            let signature = self.parse_signature(module, header, &mut fun_id)?;

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
            let nm = nm.token.spam.raw();

            let mut params = self.context.pool.get();
            for param in name[1..].iter() {
                let ty = TYPE_SALT.add(param.token.spam.raw());
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

            let g_ent = GFunEnt {
                signature,
                ast: self.state.asts.add(ast),
                next: None,
            };

            let g = self.state.gfuns.add(g_ent);

            let id = FUN_SALT.add(nm).combine(GENERIC_FUN_SALT);

            (nm, id, FKind::Generic(g), false)
        } else {
            return Err(FError::new(
                FEKind::InvalidFunctionHeader,
                name.token.clone(),
            ));
        };

        id = id.combine(module_id);

        let fun_ent = FunEnt {
            vis,
            id,
            module,
            hint,
            params: vec![],
            kind,
            name,
            attr_id,
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
                let id = ID(0).add(arg.token.spam.raw());
                *fun_id = fun_id.combine(self.state.types[ty].id);
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
                    let id = TYPE_SALT.add(ast.token.spam.raw());
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
                _ => todo!("{}", ast),
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
            let ty_ent = &self.state.types[ty];

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
        if token.spam.is_empty() {
            return self.state.loops.last().cloned().ok_or(true);
        }

        let name = ID(0).add(token.spam.deref());

        self.state
            .loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.state.loops.is_empty())
    }

    fn base_of_err(&mut self, ty: Type, token: &Token) -> Result<Type> {
        self.base_of(ty)
            .ok_or_else(|| FError::new(FEKind::NonPointerDereference, token.clone()))
    }

    fn base_of(&mut self, ty: Type) -> Option<Type> {
        match self.state.types[ty].kind {
            TKind::Pointer(pointed) => Some(pointed),
            _ => None,
        }
    }

    fn parse_type(&mut self, module: Mod, ast: &Ast) -> Result<Type> {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .parse_type(module, ast)
            .map(|t| t.1)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))
    }

    fn pointer_of(&mut self, ty: Type) -> Type {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context).pointer_of(ty)
    }

    fn constant_of(&mut self, constant: TypeConst) -> Type {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .constant_of(constant)
    }

    #[inline]
    pub fn is_pointer(&self, ty: Type) -> bool {
        matches!(self.state.types[ty].kind, TKind::Pointer(..))
    }

    #[inline]
    fn pass_mutability(&mut self, from: Value, to: Value) {
        self.state.body.values[to].mutable = self.state.body.values[from].mutable;
    }

    fn push_scope(&mut self) {
        self.state.frames.push(self.state.vars.len());
    }

    fn pop_scope(&mut self) {
        let idx = self.state.frames.pop().unwrap();
        self.state.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Value> {
        self.state
            .vars
            .iter()
            .rev()
            .find(|&&v| self.state.body.values[v].id == id)
            .cloned()
    }

    fn array_of(&mut self, ty: Type, length: usize) -> Type {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .array_of(ty, length)
    }
}

pub struct FEDisplay<'a> {
    state: &'a FState,
    error: &'a FError,
}

impl<'a> FEDisplay<'a> {
    pub fn new(state: &'a FState, error: &'a FError) -> Self {
        Self { state, error }
    }
}

impl<'a> std::fmt::Display for FEDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.error.token.kind != LTKind::None {
            writeln!(f, "{}", TokenView::new(&self.error.token))?;
        }

        match &self.error.kind {
            &FEKind::DuplicateEntrypoint(other) => {
                let other = self.state.funs[other].hint.clone();
                writeln!(
                    f,
                    "entrypoint already defined here:\n{}",
                    TokenView::new(&other)
                )?;
            }
            FEKind::TooShortAttribute(actual, expected) => {
                writeln!(
                    f,
                    "too short attribute, expected {} but got {}",
                    expected, actual
                )?;
            }
            FEKind::InvalidCallConv => {
                writeln!(f, "{}", TokenView::new(&self.error.token))?;
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
            }
            FEKind::InvalidLinkage => {
                writeln!(f, "{}", TokenView::new(&self.error.token))?;
                writeln!(f, "Invalid linkage, valid linkages are:")?;
                for cc in ["import", "local", "export", "preemptible", "hidden"] {
                    writeln!(f, "  {}", cc)?;
                }
            }
            FEKind::TypeError(error) => {
                writeln!(f, "{}", TEDisplay::new(self.state, &error))?;
            }
            FEKind::Redefinition(other) => {
                writeln!(f, "redefinition of\n{}", TokenView::new(&other))?;
            }
            FEKind::InvalidBitCast(actual, expected) => {
                writeln!(
                    f,
                    "invalid bit-cast, expected type of size {} but got {}",
                    expected, actual
                )?;
            }
            FEKind::AssignToImmutable => {
                writeln!(f, "cannot assign to immutable value")?;
            }
            FEKind::ExpectedValue => {
                writeln!(f, "expected this expression to have a value")?;
            }
            &FEKind::TypeMismatch(actual, expected) => {
                writeln!(
                    f,
                    "type mismatch, expected '{}' but got '{}'",
                    TypeDisplay::new(&self.state, expected),
                    TypeDisplay::new(&self.state, actual)
                )?;
            }
            FEKind::FunctionNotFound(name, arguments) => {
                writeln!(
                    f,
                    "function {}({}) does not exist within current scope",
                    name,
                    arguments
                        .iter()
                        .map(|t| format!("{}", TypeDisplay::new(&self.state, *t)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
            FEKind::UnexpectedValue => {
                writeln!(
                    f,
                    "value not expected here, consider adding 'pass' after expression"
                )?;
            }
            FEKind::UnexpectedReturnValue => {
                writeln!(f, "return value not expected, if you want to return something, add '-> <type>' after '()' in signature")?;
            }
            FEKind::UnexpectedAuto => {
                writeln!(f, "'auto' not allowed here")?;
            }
            FEKind::UndefinedVariable => {
                writeln!(f, "cannot find variable in current scope")?;
            }
            FEKind::UnresolvedType => {
                writeln!(
                    f,
                    "type of this expression cannot be inferred, consider annotating the type"
                )?;
            }
            &FEKind::UnknownField(ty) => {
                writeln!(
                    f,
                    "unknown field for type '{}', type has this fields (embedded included):",
                    TypeDisplay::new(&self.state, ty)
                )?;
                let mut frontier = vec![(ty, "", true)];
                let mut i = 0;
                while i < frontier.len() {
                    let (ty, _, embedded) = frontier[i];
                    if !embedded {
                        continue;
                    }
                    match self.state.types[ty].kind {
                        TKind::Structure(sty) => {
                            for f in self.state.stypes[sty].fields.iter() {
                                frontier.push((f.ty, f.hint.spam.raw(), f.embedded));
                            }
                        }
                        _ => (),
                    }
                    i += 1;
                }

                for (ty, name, _) in frontier {
                    writeln!(f, "  {}: {}", name, TypeDisplay::new(&self.state, ty))?;
                }
            }
            FEKind::MutableRefOfImmutable => {
                writeln!(f, "cannot take mutable reference of immutable value")?;
            }
            FEKind::MissingElseBranch => {
                writeln!(f, "expected 'else' branch since 'if' branch returns value, consider adding 'pass' after last expression if this is intended")?;
            }
            FEKind::ContinueOutsideLoop => {
                writeln!(f, "cannot use 'continue' outside of loop")?;
            }
            FEKind::BreakOutsideLoop => {
                writeln!(f, "cannot use 'break' outside of loop")?;
            }
            FEKind::WrongLabel => {
                writeln!(f, "parent loop with this label does not exist")?;
            }
            FEKind::NonPointerDereference => {
                writeln!(f, "cannot dereference non-pointer type")?;
            }
            FEKind::InvalidFunctionHeader => {
                writeln!(f, "invalid function header, syntax for header is:\n  ident | op [ '[' ident {{ ',' ident }} ']' ]")?;
            }
            &FEKind::AmbiguousFunction(a, b) => {
                let a = self.state.funs[a].hint.clone();
                let b = self.state.funs[b].hint.clone();
                writeln!(
                    f,
                    "ambiguous function call, matches\n{}\nand\n{}",
                    TokenView::new(&a),
                    TokenView::new(&b)
                )?;
            }
            FEKind::EmptyArray => {
                writeln!(f, "cannot create empty array from '[]' syntax as type of element is unknown")?;
            },
        }

        Ok(())
    }
}

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
    EmptyArray,
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
    FunctionNotFound(String, Vec<Type>),
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
    pub name: &'static str,
    pub attr_id: usize,
}

#[derive(Debug, Default, Clone)]
pub struct FunBody {
    pub values: List<Value, ValueEnt>,
    pub insts: LinkedList<Inst, InstEnt>,
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
    Deref(Value),
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

pub struct FState {
    pub t_state: TState,
    pub funs: Table<Fun, FunEnt>,
    pub nfuns: ReusableList<NFun, NFunEnt>,
    pub gfuns: List<GFun, GFunEnt>,
    pub rfuns: List<RFun, RFunEnt>,

    pub loops: Vec<Loop>,

    pub entry_point: Option<Fun>,
    pub vars: Vec<Value>,
    pub frames: Vec<usize>,
    pub body: FunBody,
    pub block: Option<Inst>,
    pub unresolved: Vec<Fun>,

    pub represented: Vec<Fun>,
}

crate::inherit!(FState, t_state, TState);

impl FState {
    pub fn new(t_state: TState) -> Self {
        let mut state = Self {
            t_state,
            funs: Table::new(),
            nfuns: ReusableList::new(),
            gfuns: List::new(),
            rfuns: List::new(),
            loops: Vec::new(),
            body: FunBody::default(),
            block: None,
            unresolved: Vec::new(),
            vars: Vec::new(),
            entry_point: None,
            represented: Vec::new(),
            frames: Vec::new(),
        };

        let module_id = state.modules[state.builtin_module].id;

        let types = state.builtin_repo.type_list();

        fn create_builtin_fun(
            state: &mut FState,
            module: ID,
            name: &'static str,
            args: &[Type],
            ret_ty: Option<Type>,
        ) {
            let mut id = FUN_SALT.add(name);
            for &arg in args {
                id = id.combine(state.types[arg].id);
            }
            id = id.combine(module);
            let fun_ent = FunEnt {
                id,
                name,
                vis: Vis::Public,
                module: state.builtin_module,
                hint: Token::builtin(name),
                params: vec![],
                kind: FKind::Builtin(ret_ty),
                attr_id: 0,
            };
            assert!(state.funs.insert(id, fun_ent).0.is_none());
        }

        for i in types {
            for j in types {
                let name = state.types[i].name;
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
                for &datatype in types.iter() {
                    create_builtin_fun(&mut state, module_id, op, &[datatype], Some(datatype));
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
                for &ty in types.iter() {
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        state.builtin_repo.bool
                    } else {
                        ty
                    };

                    create_builtin_fun(&mut state, module_id, op, &[ty, ty], Some(return_type));
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

impl FContext {
    pub fn new(t_context: TContext) -> Self {
        Self {
            t_context,
            body_pool: Vec::new(),
            signature: Signature::new(CallConv::Fast),
        }
    }
}

crate::inherit!(FContext, t_context, TContext);

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

        writeln!(f, "{}", fun.hint.spam.deref())?;
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
                            inst.hint.spam.deref()
                        )?;
                    } else {
                        writeln!(f, "    {:?} |{}", inst.kind, inst.hint.spam.deref())?;
                    }
                }
            }
        }

        Ok(())
    }
}

pub fn test() {
    let mut program = Program::default();

    let mut state = MTState::default();
    let mut context = MTContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/functions/test_project")
        .unwrap();

    let state = TState::new(state);
    let context = TContext::new(context);
    let mut state = FState::new(state);
    let mut context = FContext::new(context);

    for i in (0..state.module_order.len()).rev() {
        let module = state.module_order[i];
        FParser::new(&mut program, &mut state, &mut context)
            .parse(module)
            .unwrap();
    }

    for (i, fun) in state.funs.iter().enumerate() {
        match fun.kind {
            FKind::Represented(_) => (),
            _ => continue,
        };

        println!("{}", FunDisplay::new(&state, Fun::new(i)));
    }
}