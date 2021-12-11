use core::panic;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use crate::ast::{AKind, Ast, Vis};
use crate::lexer::TKind as LTKind;
use crate::lexer::{Token};
use crate::{module_tree::*};
use crate::types::Type;
use crate::types::*;
use crate::util::storage::{LinkedList, ReusableList, Table};
use crate::util::{
    sdbm::{SdbmHashState, ID},
    storage::{IndexPointer, List},
};

use cranelift_codegen::ir::{Block as CrBlock, Signature, StackSlot, Value as CrValue, ArgumentPurpose, AbiParam};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_frontend::Variable as CrVar;
use cranelift_module::{FuncId, Module, Linkage};
use cranelift_object::{ObjectModule, ObjectBuilder};

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
        Self { program, state, context }
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
        for arg in args.iter() {
            let var = self.state.body.values.add(arg.clone());
            self.state.vars.push(Some(var));
            arg_buffer.push(var);
        }
        if let Some(ret_ty) = ret_ty {
            if self.state.types[ret_ty].on_stack() {
                let ty = self.pointer_of(ret_ty, true, false);
                let value = self.new_anonymous_value(ty, false);
                arg_buffer.push(value);
            }
        }
        self.state.nfuns[nid].sig.args = args;
        self.state.body.insts[entry_point].kind.block_mut().args = arg_buffer.clone();
        
        if ast[1].is_empty() {
            return Ok(());
        }

        let value = self.block(fun, &ast[1])?;

        let n_ent = &self.state.nfuns[nid];

        if let (Some(value), Some(_), Some(ret_ty)) =
            (value, self.state.block, n_ent.sig.ret_ty)
        {
            let value_ty = self.state.body.values[value].ty;
            let token = &ast[1].last().unwrap().token;
            if self.is_auto(value_ty) {
                self.infer(fun, value, ret_ty)?;
            } else {
                self.assert_type(value_ty, ret_ty, token)?;
            }
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if let (Some(ret_ty), Some(_)) =
            (n_ent.sig.ret_ty, self.state.block)
        {
            let value = self.new_temp_value(ret_ty);
            let token = &ast[1].last().unwrap().token;
            self.add_inst(InstEnt::new(IKind::ZeroValue, Some(value), token));
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
            self.state.body.values[value_id].on_stack = self.state.body.values[value_id].on_stack || on_stack;
        }

        let mut frontier = self.context.pool.get();
        let mut unresolved = std::mem::take(&mut self.state.unresolved_funs);
        for inst in unresolved.drain(..) {
            match &self.state.body.insts[inst].kind {
                IKind::UnresolvedCall(..) => {
                    self.infer_call(fun, inst, &mut frontier)?;
                }
                _ => (),
            }

            for (value, ty) in frontier.drain(..) {
                self.infer(fun, value, ty)?;
            }
        }
        self.state.unresolved_funs = unresolved;

        for (id, dep) in self.context.deps.iter() {
            if dep.len() > 0 {
                let inst = self
                    .state
                    .body
                    .insts
                    .iter()
                    .find(|(_, inst)| {
                        inst.value.is_some()
                            && self.state.body.values[inst.value.unwrap()].type_dependency == Some(id)
                    })
                    .unwrap()
                    .0
                    .clone();

                return Err(FError::new(
                    FEKind::UnresolvedType,
                    self.state.body.insts[inst].hint.clone(),
                ));
            }
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

        let (linkage, alias) = if let Some(attr) = self.state.attributes.get_attr(attr_id, "linkage") {
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

        let call_conv = if let Some(attr) = self.state.attributes.get_attr(attr_id, "call_conv") {
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

        let mut signature = std::mem::replace(&mut self.context.signature, Signature::new(CallConv::Fast));
        signature.clear(call_conv);

        for arg in n_ent.sig.args.iter() {
            let repr = self.state.types[arg.ty].repr();
            signature.params.push(AbiParam::new(repr));
        }

        if let Some(ret_ty) = n_ent.sig.ret_ty {
            let ret_ty = &self.state.types[ret_ty];
            let repr = ret_ty.repr();

            let purpose = if ret_ty.on_stack() {
                signature.params.push(AbiParam::special(repr, ArgumentPurpose::StructReturn));
                ArgumentPurpose::StructReturn
            } else {
                ArgumentPurpose::Normal
            };

            signature.returns.push(AbiParam::special(repr, purpose));
        }

        
        let alias = if let Some(attr) = self.state.attributes.get_attr(attr_id, "entry") {
            println!("{}", attr_id);
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
            let return_value = self.state.body.insts[entry].kind.block().args.last().unwrap().clone();

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
            if let Some(current_value) = current_value {
                self.may_infer(fun, return_value, current_value, &ast[1].token)?;
            } else {
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
                self.add_inst(InstEnt::new(IKind::ZeroValue, Some(temp_value), &ast.token));
                Some(self.return_value(fun, temp_value, &ast.token))
            } else {
                None
            }
        } else {
            let ty = ty
                .ok_or_else(|| FError::new(FEKind::UnexpectedReturnValue, ast[0].token.clone()))?;
            let value = self.expr(fun, &ast[0])?;
            let actual_type = self.state.body.values[value].ty;
            if self.is_auto(actual_type) {
                self.infer(fun, value, ty)?;
            } else {
                self.assert_type(actual_type, ty, &ast[0].token)?;
            }

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
                self.auto()
            } else {
                match self.parse_type(module, &var_line[1]) {
                    Ok(ty) => ty,
                    Err(FError {
                        kind: FEKind::TypeError(
                            TError {
                                kind: TEKind::WrongInstantiationArgAmount(0, _),
                                ..
                            }
                        ),
                        ..
                    }) => self.auto(),
                    Err(err) => return Err(err),
                }
            };

            if var_line[2].kind == AKind::None {
                for name in var_line[0].iter() {
                    let name = ID(0).add(name.token.spam.deref());

                    let temp_value = self
                        .state
                        .body
                        .values
                        .add(ValueEnt::temp(ty));

                    let inst = self.add_inst(InstEnt::new(
                        IKind::ZeroValue,
                        Some(temp_value),
                        &var_line.token,
                    ));

                    let var = self.add_variable(name, ty, mutable);

                    if self.is_auto(ty) {
                        self.add_type_dependency(var, inst);
                    }

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
                    let mut actual_datatype = self.state.body.values[value].ty;

                    let unresolved = if self.is_auto(ty) {
                        self.is_auto(actual_datatype)
                    } else {
                        if self.is_auto(actual_datatype) {
                            actual_datatype = ty;
                            self.infer(fun, value, ty)?;
                        } else {
                            self.assert_type(actual_datatype, ty, &raw_value.token)?;
                        }
                        false
                    };

                    let var = self.add_variable(name, actual_datatype, mutable);

                    let inst = self.add_inst(InstEnt::new(
                        IKind::VarDecl(value),
                        Some(var),
                        &var_line.token,
                    ));

                    if unresolved {
                        self.add_type_dependency(value, inst);
                    }
                }
            }
        }

        Ok(())
    }

    fn expr(&mut self, fun: Fun, ast: &Ast) -> Result<Value> {
        self.expr_low(fun, ast)?.ok_or_else(|| FError::new(FEKind::ExpectedValue, ast.token.clone()))
    }

    fn expr_low(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        match ast.kind {
            AKind::BinaryOp => self.binary_op(fun, ast),
            AKind::Lit => self.lit(ast),
            AKind::Ident => self.ident(ast),
            AKind::Call(_) => self.call(fun, ast),
            AKind::IfExpr => self.if_expr(fun, ast),
            AKind::Loop => self.loop_expr(fun, ast),
            AKind::DotExpr => self.dot_expr(fun, ast),
            AKind::Deref(_) => self.deref_expr(fun, ast),
            AKind::Ref(_) => self.ref_expr(fun, ast),
            AKind::UnaryOp => self.unary_op(fun, ast),
            AKind::Pass => Ok(None),
            _ => todo!("unmatched expr ast {}", ast),
        }
    }

    fn ref_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let mutable = ast.kind == AKind::Ref(true);
        let value = self.expr(fun, &ast[0])?;

        if !self.state.body.values[value].mutable && mutable {
            return Err(FError::new(FEKind::MutableRefOfImmutable, ast.token.clone()));
        }

        let reference = self.ref_expr_low(value, mutable, &ast.token);

        Ok(Some(reference))
    }

    fn ref_expr_low(&mut self, value: Value, mutable: bool, token: &Token) -> Value {
        let ty = self.state.body.values[value].ty;
        let inst = self.inst_of(value);
        let unresolved = self.is_auto(ty);
        let ty = self.pointer_of(ty, mutable, false);
        let reference = self.new_temp_value(ty);
        let inst = self.add_inst_under(
            InstEnt::new(IKind::Ref(value), Some(reference), token),
            inst,
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

        if unresolved {
            self.add_type_dependency(value, inst);
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
        let inst = self.inst_of(value);
        let (pointed, mutable, _) = self.base_of_err(ty, token)?;

        let val = self.new_anonymous_value(pointed, mutable);
        self.state.body.values[val].mutable = mutable;
        let inst = self
            .add_inst_under(InstEnt::new(IKind::Deref(value), Some(val), token), inst);

        if self.is_auto(pointed) {
            self.add_type_dependency(value, inst);
        }

        Ok(val)
    }

    fn unary_op(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let name = FUN_SALT.add(ast[0].token.spam.deref());
        let value = self.expr(fun, &ast[1])?;

        let mut values = self.context.pool.get();
        values.push(value);
        self.call_low(fun, name, ast[0].token.spam.raw(), false, &values, &ast.token)
    }

    fn dot_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let header = self.expr(fun, &ast[0])?;
        let mutable = self.state.body.values[header].mutable;
        let field = ID(0).add(ast[1].token.spam.deref());
        let ty = self.state.body.values[header].ty;
        if self.is_auto(ty) {
            let value = self.new_anonymous_value(self.auto(), mutable);
            self.pass_mutability(header, value);
            let inst = self.add_inst(InstEnt::new(
                IKind::UnresolvedDot(header, field),
                Some(value),
                &ast.token,
            ));
            self.add_type_dependency(header, inst);
            Ok(Some(value))
        } else {
            // bool is a placeholder
            let value = self.new_anonymous_value(self.state.builtin_repo.bool, mutable);
            let ty = self.field_access(header, field, value, &ast.token)?;
            self.state.body.values[value].ty = ty;
            Ok(Some(value))
        }
    }

    fn find_field(&mut self, ty: Type, field_id: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = self.context.pool.get();
        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            match &self.state.types[frontier[i].2].kind {
                &TKind::Structure(sid) => {
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
                }
                _ => (),
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

        let value = if self.state.body.insts[end_block].kind.block().args.is_empty() {
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

        if self.is_auto(cond_type) {
            self.infer(fun, cond_val, self.state.builtin_repo.bool)?;
        } else {
            self.assert_type(cond_type, self.state.builtin_repo.bool, &cond_expr.token)?;
        }

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

        /*if let Some((_, loop_block, ..)) = self.loop_headers.last() {
            if loop_block.to_owned() != builder.state.block().unwrap() {
                builder.seal_current_block();
            }
        } else {
            builder.seal_current_block();
        }*/

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
            self.state.body.insts[merge_block].kind.block_mut().args.push(value);
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
                if let Some(result) = result {
                    self.may_infer(fun, val, result, &value_token)?;
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
                    self.state.body.insts[merge_block].kind.block_mut().args.push(value);
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
                generic_params.resize(ast[0].len() - 1, None);
                for (i, arg) in ast[0][1..].iter().enumerate() {
                    let id = self.parse_type(module, arg)?;
                    generic_params[i] = Some(id);
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

        self.call_low(fun, base_name, name, ast.kind == AKind::Call(true), &buffer, &ast.token)
    }

    fn call_low(
        &mut self,
        fun: Fun,
        base_name: ID,
        name: &'static str,
        dot_call: bool,
        values: &[Value],
        token: &Token,
    ) -> ExprResult {
        let mut values = values.to_vec();
        let module = self.state.funs[fun].module; 
        let mut unresolved = self.context.pool.get();
        unresolved.extend(values.iter().filter(|&&v| self.is_auto(self.state.body.values[v].ty)));

        let value = if unresolved.len() > 0 {
            let value = self.auto();
            let value = self.new_temp_value(value);
            let inst = self.add_inst(InstEnt::new(
                IKind::UnresolvedCall(base_name, name, dot_call, values),
                Some(value),
                token,
            ));
            unresolved
                .drain(..)
                .for_each(|v| self.add_type_dependency(v, inst));
            self.state.unresolved_funs.push(inst);
            Some(value)
        } else {
            let fun =
                self.smart_find_or_create(module, base_name, name, &mut values, dot_call, token)?;
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
            value
        };

        Ok(value)
    }

    fn return_type_of(&self, fun: Fun) -> Option<Type> {
        match &self.state.funs[fun].kind {
            &FKind::Normal(nid) => self.state.nfuns[nid].sig.ret_ty,
            &FKind::Builtin(ret_ty) => ret_ty,
            i => unreachable!("{:?}", i),
        } 
    }

    fn ident(&mut self, ast: &Ast) -> ExprResult {
        let name = ID(0).add(ast.token.spam.deref());
        self.find_variable(name)
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
            LTKind::String(_) => self.pointer_of(self.state.builtin_repo.u8, false, false),
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

        self.call_low(fun, base_id, ast[0].token.spam.raw(), false, &buffer, &ast.token)
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

    fn may_infer(&mut self, fun: Fun, a: Value, b: Value, token: &Token) -> Result<bool> {
        let a_type = self.state.body.values[a].ty;
        let b_type = self.state.body.values[b].ty;
        Ok(if self.is_auto(a_type) {
            if !self.is_auto(b_type) {
                self.infer(fun, a, b_type)?;
                true
            } else {
                false
            }
        } else {
            if self.is_auto(b_type) {
                self.infer(fun, b, a_type)?;
            } else {
                self.assert_type(a_type, b_type, token)?;
            }
            true
        })
    }

    fn infer(&mut self, fun: Fun, value: Value, ty: Type) -> Result<()> {
        let mut frontier = self.context.pool.get();
        frontier.clear();
        frontier.push((value, ty));

        while let Some((value, ty)) = frontier.pop() {
            let val = &mut self.state.body.values[value];
            val.ty = ty;
            let dependency_id = if let Some(dep) = val.type_dependency {
                val.type_dependency = None;
                dep
            } else {
                continue;
            };

            if let Some(inst) = val.inst {
                match self.state.body.insts[inst].kind {
                    IKind::Ref(value) => match self.state.types[ty].kind {
                        TKind::Pointer(inner, ..) => {
                            frontier.push((value, inner));
                        }
                        _ => unreachable!(),
                    },
                    IKind::Deref(value) => {
                        let (_, mutable, nullable) = self.base_of(self.state.body.values[value].ty).unwrap();
                        
                        frontier.push((value, self.pointer_of(ty, mutable, nullable)));
                    }
                    IKind::VarDecl(value) => {
                        frontier.push((value, ty));
                    }
                    _ => (),
                }
            }

            let mut dependencies = std::mem::take(&mut self.context.deps[dependency_id]);
            for dep in dependencies.drain(..).skip(1)
            /* first is null marker */
            {
                let inst = &mut self.state.body.insts[dep];
                inst.unresolved -= 1;
                if inst.unresolved != 0 {
                    continue;
                }

                let token = inst.hint.clone();
                match &mut inst.kind {
                    IKind::VarDecl(_) => {
                        let value = inst.value.unwrap();
                        frontier.push((value, ty));
                    }
                    IKind::UnresolvedCall(..) => {
                        self.infer_call(fun, dep, &mut frontier)?;
                    }
                    IKind::ZeroValue => {
                        let value = inst.value.unwrap();
                        self.state.body.values[value].ty = ty;
                    }
                    IKind::Assign(val) => {
                        let mut val = *val;
                        if value == val {
                            val = inst.value.unwrap();
                        }

                        frontier.push((val, ty));
                    }
                    IKind::UnresolvedDot(header, field) => {
                        let header = *header;
                        let field = *field;

                        let value = inst.value.unwrap();
                        self.state.body.insts.remove(dep);
                        let ty = self.field_access(header, field, value, &token)?;
                        frontier.push((value, ty));
                    }
                    IKind::Ref(value) => {
                        let val = inst.value.unwrap();
                        let value = *value;
                        let value_datatype = self.state.body.values[value].ty;
                        let (_, mutable, nullable) = self.base_of(self.state.body.values[val].ty).unwrap();
                        let ty = self.pointer_of(value_datatype, mutable, nullable);
                        frontier.push((val, ty));
                    }
                    IKind::Deref(value) => {
                        let value = *value;
                        let val = inst.value.unwrap();
                        let value_datatype = self.state.body.values[value].ty;
                        let ty = self.base_of(value_datatype).unwrap().0;
                        frontier.push((val, ty));
                    }
                    IKind::NoOp | IKind::Call(..) => (),
                    _ => todo!("{:?}", inst),
                }
            }

            self.context.deps[dependency_id] = dependencies;
        }

        Ok(())
    }

    fn infer_call(&mut self, fun: Fun, inst: Inst, frontier: &mut Vec<(Value, Type)>) -> Result {
        let module = self.state.funs[fun].module;
        let (name, dot_expr, base_id, mut args) = match std::mem::take(&mut self.state.body.insts[inst].kind)
        {
            IKind::UnresolvedCall(base_id, name, dot_expr, args) => (name, dot_expr, base_id, args),
            _ => unreachable!(),
        };

        let token = self.state.body.insts[inst].hint.clone();

        let fun = self.smart_find_or_create(module, base_id, name, &mut args, dot_expr, &token)?;
        

        if self.state.body.insts[inst].unresolved != 0 {
            let mut types = self.context.pool.get();    
            let nid = self.state.funs[fun].kind.unwrap_normal();
            types.extend(
                self
                    .state
                    .nfuns[nid]
                    .sig
                    .args
                    .iter()
                    .map(|arg| arg.ty),
            );
            for (&ty, &value) in types.iter().zip(args.iter()) {
                if self.is_auto(self.state.body.values[value].ty) {
                    frontier.push((value, ty));
                }
            }
        }

        let value = self.state.body.insts[inst].value;
        let ty = self.return_type_of(fun);

        if let (Some(value), Some(ty)) = (value, ty) {
            if self.state.types[ty].on_stack() {
                self.state.body.values[value].mutable = true;
                args.push(value);
            }
            frontier.push((value, ty));
        } else if let Some(dependency) = self.state.body.values[value.unwrap()].type_dependency {
            if self.context.deps[dependency].len() > 1 {
                return Err(FError::new(FEKind::ExpectedValue, token.clone()));
            }
            self.context.deps[dependency].clear();
            self.state.body.insts[inst].value = None;
        }

        self.state.body.insts[inst].kind = IKind::Call(fun, args);

        Ok(())
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
            return Err(FError::new(FEKind::UnknownField(header_datatype), token.clone()));
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
                TKind::Pointer(pointed, _, _) => {
                    let pointed = *pointed;
                    let prev_inst = self.inst_of(header);
                    let value = self.new_anonymous_value(current_type, mutable);
                    self.state.body.values[value].offset = offset;
                    let prev_inst = self.add_inst_under(
                        InstEnt::new(IKind::Offset(header), Some(value), &token),
                        prev_inst,
                    );
                    let loaded = self.new_anonymous_value(pointed, mutable);
                    self.add_inst_under(
                        InstEnt::new(IKind::Deref(value), Some(loaded), &token),
                        prev_inst,
                    );
                    offset = 0;
                    current_type = pointed;
                    header = loaded;
                }
                _ => todo!("{:?}", self.state.types[current_type]),
            }
        }

        let inst = self.inst_of(header);
        let inst = self.add_inst_under(
            InstEnt::new(IKind::Offset(header), Some(value), token),
            inst,
        );

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
        self.state.vars.push(Some(val));
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

        let unresolved = if self.is_auto(target_datatype) {
            if !self.is_auto(value_datatype) {
                self.infer(fun, target, value_datatype)?;
                false
            } else {
                true
            }
        } else {
            if self.is_auto(value_datatype) {
                self.infer(fun, value, target_datatype)?;
            } else {
                self.assert_type(value_datatype, target_datatype, &ast.token)?;
            }
            false
        };

        let inst =
            self.add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

        if unresolved {
            self.add_type_dependency(value, inst);
            self.add_type_dependency(target, inst);
        }

        Ok(Some(value))
    }

    fn smart_find_or_create(
        &mut self,
        module: Mod,
        base: ID,
        name: &str,
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
                self.dot_find_or_create(module, base, name, &mut types, first_mutable, &token)?;
            if id.0 != 0 {
                let value = self.new_anonymous_value(self.state.builtin_repo.bool, first_mutable);
                self.field_access(args[0], id, value, &token)?;
                args[0] = value;
            }
            match kind {
                DotInstr::None => (),
                DotInstr::Deref => args[0] = self.deref_expr_low(args[0], &token)?,
                DotInstr::Ref => args[0] = self.ref_expr_low(args[0], false, &token),
                DotInstr::MutRef => args[0] = self.ref_expr_low(args[0], true, &token),
            }
            Ok(fun)
        } else {
            self.find_or_create(module, base, name, &types, &token)
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
        let mut value = ValueEnt::new(name, ty, mutable);
        if self.is_auto(ty) {
            let dep = self.new_type_dependency();
            value.type_dependency = Some(dep);
        }
        self.state.body.values.add(value)
    }

    fn new_type_dependency(&mut self) -> TypeDep {
        let mut vec = self.context.dep_pool.pop().unwrap_or_default();
        vec.push(Inst::new(0));
        self.context.deps.add(vec)
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

    pub fn add_inst_under(&mut self, inst: InstEnt, under: Inst) -> Inst {
        debug_assert!(!inst.kind.is_closing(), "cannot insert closing instruction");
        let value = inst.value;
        let inst = self.state.body.insts.insert(under, inst);
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
        values: &mut [Type],
        first_mutable: bool,
        token: &Token,
    ) -> Result<(Fun, ID, DotInstr)> {
        let mut frontier = self.context.pool.get();
        frontier.push((values[0], ID(0), first_mutable));

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
            let (ty, id, first_mutable) = frontier[i];
            values[0] = ty;
            unwrap!(
                self.find_or_create(module, base, name, values, token),
                id,
                None
            );
            if self.is_pointer(ty) {
                values[0] = self.base_of(ty).unwrap().0;
                unwrap!(
                    self.find_or_create(module, base, name, values, token),
                    id,
                    Deref
                );
            } else {
                if first_mutable {
                    values[0] = self.pointer_of(ty, true, false);
                    unwrap!(
                        self.find_or_create(module, base, name, values, token),
                        id,
                        MutRef
                    );

                    values[0] = self.pointer_of(ty, true, true);
                    unwrap!(
                        self.find_or_create(module, base, name, values, token),
                        id,
                        MutRef
                    );
                }

                values[0] = self.pointer_of(ty, false, false);
                unwrap!(self.find_or_create(module, base, name, values, token), id, Ref);
                
                values[0] = self.pointer_of(ty, false, true);
                unwrap!(self.find_or_create(module, base, name, values, token), id, Ref);
            }

            match &self.state.types[ty].kind {
                &TKind::Structure(id) => {
                    for field in self.state.stypes[id].fields.iter().filter(|f| f.embedded) {
                        frontier.push((field.ty, field.id, first_mutable));
                    }
                }
                &TKind::Pointer(pointed, mutable, _) => {
                    match &self.state.types[pointed].kind {
                        &TKind::Structure(id) => {
                            for field in self.state.stypes[id].fields.iter().filter(|f| f.embedded) {
                                frontier.push((field.ty, field.id, mutable));
                            }
                        }
                        _ => (),
                    }
                }
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
        values: &[Type],
        token: &Token,
    ) -> Result<Fun> {
        let specific_id = values.iter().fold(base, |base, &val| {
            base.combine(self.state.types[val].id)
        });

        let mut buffer = self.context.pool.get();
        self.state.collect_scopes(module, &mut buffer);

        let (_, module_id) = buffer[0]; 

        if let Some(fun) = self.find_or_create_low(specific_id, module_id, base, module, values, token)? {
            return Ok(fun);
        }

        let mut found = None;

        for (module, module_id) in buffer.drain(1..) {
            if let Some(fun) = self.find_or_create_low(specific_id, module_id, base, module, values, token)? {
                if let Some(found) = found {
                    return Err(FError::new(FEKind::AmbiguousFunction(fun, found), token.clone()));
                }
                found = Some(fun);
            }
        }

        found.ok_or_else(|| FError::new(
            FEKind::FunctionNotFound(name.to_string(), values.to_vec()),
            token.clone(),
        ))
    }

    fn find_or_create_low(&mut self, specific_id: ID, module_id: ID, base: ID, module: Mod, values: &[Type], token: &Token) -> Result<Option<Fun>> {
        if let Some(&fun) = self.state.funs.index(specific_id.combine(module_id)) {
            return Ok(Some(fun));
        }

        let mut g_fun = self.state.funs.index(base
                .combine(GENERIC_FUN_SALT)
                .combine(module_id))
            .cloned();

        let mut found = None;

        while let Some(fun) = g_fun {
            let g = match self.state.funs[fun].kind {
                FKind::Generic(g) => g,
                _ => unreachable!("{:?}", self.state.funs[fun].kind),
            };
            if let Some(fun) = self.create(module, fun, g, values)? {
                if let Some(found) = found {
                    return Err(FError::new(FEKind::AmbiguousFunction(fun, found), token.clone()));
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
        values: &[Type],
    ) -> Result<Option<Fun>> {
        let fun_ent = &self.state.funs[fun];
        let g_ent = &self.state.gfuns[g];

        let mut arg_buffer = self.context.pool.get();
        let mut stack = self.context.pool.get();
        let mut params = self.context.pool.get();
        params.resize(g_ent.signature.params.len(), None);

        // perform pattern matching
        let mut i = 0;
        let mut j = 0;
        while i < g_ent.signature.elements.len() {
            let (amount, length) = match g_ent.signature.elements[i] {
                GenericElement::NextArgument(amount, length) => (amount, length),
                GenericElement::NextReturn(_) => break,
                _ => unreachable!("{:?}", g_ent.signature.elements[i]),
            };

            let arg = &g_ent.signature.elements[i + 1..i + 1 + length];

            for _ in 0..amount {
                self.load_arg_from_datatype(values[j], &mut arg_buffer, &mut stack);
                {
                    let mut i = 0;
                    let mut j = 0;
                    while i + j < arg.len() + arg_buffer.len() {
                        let a = arg[i].clone();
                        let b = arg_buffer[j].clone();
                        if !a.compare(&b) {
                            match a {
                                GenericElement::Parameter(i) => {
                                    if let GenericElement::Element(_, Some(ty)) = b {
                                        if let Some(inferred_ty) = params[i] {
                                            if ty != inferred_ty {
                                                return Ok(None);
                                            }
                                        } else {
                                            params[i] = Some(ty);
                                        }
                                        if let Some(&GenericElement::ScopeStart) =
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
                                }
                                GenericElement::Element(..) => {
                                    if let GenericElement::Element(_, Some(ty)) = b {
                                        if !self.is_auto(ty) {
                                            return Ok(None);
                                        }
                                        if let Some(&GenericElement::ScopeStart) =
                                            arg.get(i + 1)
                                        {
                                            loop {
                                                if let Some(&GenericElement::ScopeEnd) =
                                                    arg.get(i)
                                                {
                                                    break;
                                                }
                                                i += 1;
                                            }
                                        }
                                    } else {
                                        return Ok(None)
                                    }
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

    fn add_type_dependency(&mut self, value: Value, inst: Inst) {
        self.state.body.insts[inst].unresolved += 1;
        let dependency_id = self.state.body.values[value].type_dependency.unwrap();
        self.context.deps[dependency_id].push(inst);
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
                return Err(FError::new(
                    FEKind::InvalidFunctionHeader,
                    nm.token.clone(),
                ));
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

            let return_index = args.len();

            let has_return = header[header.len() - 1].kind != AKind::None;

            args.push(GenericElement::NextReturn(has_return));

            if has_return {
                self.load_arg(module, &header[header.len() - 1], &params, &mut args)?;
            }

            let signature = GenericSignature {
                params: params.clone(),
                elements: args.clone(),
                return_index,
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

    fn parse_signature(&mut self, module: Mod, header: &Ast, fun_id: &mut ID) -> Result<FunSignature> {
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
                &AKind::Ref(mutable) | &AKind::Deref(mutable) => {
                    buffer.push(GenericElement::Pointer(
                        mutable,
                        ast.kind == AKind::Deref(mutable),
                    ));

                    stack.push((&ast[0], false));
                }
                _ => todo!("{}", ast),
            }
        }

        Ok(())
    }

    fn load_arg_from_datatype(
        &self,
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
                if let TKind::Pointer(pointed, mutable, nullable) = ty_ent.kind {
                    arg_buffer.push(GenericElement::Pointer(mutable, nullable));
                    stack.push((pointed, false));
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

    #[inline]
    fn auto(&self) -> Type {
        self.state.builtin_repo.auto
    }

    #[inline]
    fn is_auto(&self, ty: Type) -> bool {
        self.state.builtin_repo.auto == ty
            || matches!(self.state.types[ty].kind, TKind::Generic(..))
            || matches!(self.state.types[ty].kind, TKind::Pointer(pointed, ..) if self.is_auto(pointed))
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

    fn base_of_err(&mut self, ty: Type, token: &Token) -> Result<(Type, bool, bool)> {
        self.base_of(ty)
            .ok_or_else(|| FError::new(FEKind::NonPointerDereference, token.clone()))
    }

    fn base_of(&mut self, ty: Type) -> Option<(Type, bool, bool)> {
        match self.state.types[ty].kind {
            TKind::Pointer(pointed, mutable, nullable) => Some((pointed, mutable, nullable)),
            _ => None,
        }
    }

    fn parse_type(&mut self, module: Mod, ast: &Ast) -> Result<Type> {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .parse_type(module, ast)
            .map(|t| t.1)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))
    }

    fn pointer_of(&mut self, ty: Type, mutable: bool, nullable: bool) -> Type {
        TParser::new(&mut self.state.t_state, &mut self.context.t_context)
            .pointer_of(ty, mutable, nullable)
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
        self.state.vars.push(None)
    }

    fn pop_scope(&mut self) {
        let idx = self.state.vars.len() - 1 - self
            .state
            .vars
            .iter()
            .rev()
            .position(|i| i.is_none())
            .unwrap();
        self.state.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Value> {
        self
            .state
            .vars
            .iter()
            .rev()
            .filter_map(|&v| v)
            .find(|&v| self.state.body.values[v].id == id)
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
    MutRef,
}

crate::index_pointer!(Fun);

#[derive(Debug, Clone)]
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
    pub return_index: usize,
    pub arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericElement {
    ScopeStart,
    ScopeEnd,
    Pointer(bool, bool),
    Element(Type, Option<Type>),
    Parameter(usize),
    NextArgument(usize, usize),
    NextReturn(bool),
}

impl GenericElement {
    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (GenericElement::Element(id1, _), GenericElement::Element(id2, _)) => id1 == id2,
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
    ZeroValue,
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
    pub type_dependency: Option<TypeDep>,
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

            type_dependency: None,
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
            type_dependency: None,
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

crate::index_pointer!(TypeDep);

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
    pub vars: Vec<Option<Value>>,
    pub body: FunBody,
    pub block: Option<Inst>,
    pub unresolved_funs: Vec<Inst>,
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
            unresolved_funs: Vec::new(),
            entry_point: None,
            represented: Vec::new(),
        };

        let module_id = state.modules[state.builtin_module].id;

        let types = state.builtin_repo.type_list();

        fn create_builtin_fun(state: &mut FState, module: ID, name: &'static str, args: &[Type], ret_ty: Option<Type>) {
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
            assert!(state
                .funs
                .insert(id, fun_ent)
                .0
                .is_none());
        }

        for i in types {
            for j in types {
                if i == state.builtin_repo.auto || j == state.builtin_repo.auto {
                    continue;
                }
                let name = state.types[i].name;
                create_builtin_fun(
                    &mut state,
                    module_id,
                    name,
                    &[j],
                    Some(i),
                );
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
                    create_builtin_fun(
                        &mut state,
                        module_id,
                        op,
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
                for &ty in types.iter() {
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        state.builtin_repo.bool
                    } else {
                        ty
                    };

                    create_builtin_fun(
                        &mut state,
                        module_id,
                        op,
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
    pub deps: List<TypeDep, Vec<Inst>>,
    pub dep_pool: Vec<Vec<Inst>>,
    pub signature: Signature,
}

impl FContext {
    pub fn new(t_context: TContext) -> Self {
        Self {
            t_context,
            body_pool: Vec::new(),
            deps: List::new(),
            dep_pool: Vec::new(),
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

    for i in 0..state.module_order.len() {
        let module = state.module_order[i];
        FParser::new(&mut program, &mut state, &mut context)
            .parse(module)
            .unwrap();
    }

    for fun in state.funs.iter() {
        let rid = match fun.kind {
            FKind::Represented(rid) => rid,
            _ => continue,
        };

        let r_ent = &state.rfuns[rid];

        println!("{}", fun.hint.spam.deref());
        println!();

        for (i, inst) in r_ent.body.insts.iter() {
            match &inst.kind {
                IKind::Block(block) => {
                    println!("  {}{:?}", i, block.args);
                }
                IKind::BlockEnd(_) => {
                    println!();
                }
                _ => {
                    if let Some(value) = inst.value {
                        let ty = TypeDisplay::new(&state, r_ent.body.values[value].ty);
                        println!(
                            "    {:?}: {} = {:?} |{}",
                            value,
                            ty,
                            inst.kind,
                            inst.hint.spam.deref()
                        );
                    } else {
                        println!("    {:?} |{}", inst.kind, inst.hint.spam.deref());
                    }
                }
            }
        }
    }
}
