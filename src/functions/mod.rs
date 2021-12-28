use core::panic;
use std::ops::{Deref, DerefMut};

use crate::ast::{AKind, AParser, Ast, AstDisplay, OpKind, Vis};
use crate::collector::{Attrs, Collector, Item, Scope};
use crate::lexer::TKind as LTKind;
use crate::lexer::{Span, Token, TokenDisplay};
use crate::module_tree::*;
use crate::types::Type;
use crate::types::*;
use crate::util::storage::{LinkedList, Table, ImSlicePool, Range};
use crate::util::Size;
use crate::util::{
    sdbm::ID,
    storage::{IndexPointer, List},
};

use cranelift_codegen::ir::types::I64;
use cranelift_codegen::ir::{types::Type as CrType, Block as CrBlock, StackSlot, Value as CrValue};

use cranelift_frontend::Variable as CrVar;
use cranelift_module::{DataId, FuncId, Linkage, RelocRecord};
use meta_ser::{CustomDefault, EnumGetters, MetaSer, MetaQuickSer};
use traits::MetaSer;
use traits::MetaQuickSer;

type Result<T = ()> = std::result::Result<T, FError>;
type ExprResult = Result<Option<Value>>;

// wales i made up btw
pub const FUN_SALT: ID = ID(0xDEADBEEF);
pub const UNARY_SALT: ID = ID(0xFADACAFE);
pub const BINARY_SALT: ID = ID(0xBEEFDEAD);
pub const GLOBAL_SALT: ID = ID(0x2849437252);

pub struct FParser<'a> {
    state: &'a mut FState,
    context: &'a mut FContext,
    collector: &'a mut Collector,
    ptr_ty: CrType,
}

impl<'a> FParser<'a> {
    pub fn new(
        state: &'a mut FState,
        context: &'a mut FContext,
        collector: &'a mut Collector,
        ptr_ty: CrType,
    ) -> Self {
        Self {
            state,
            context,
            collector,
            ptr_ty,
        }
    }

    pub fn parse(&mut self, module: Mod) -> Result {
        TParser::new(self.state, self.context, self.collector)
            .parse(module)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))?;

        self.collect(module)?;

        self.translate()?;

        Ok(())
    }

    pub fn finalize(&mut self) -> Result {
        self.with_main_function(|s| {
            let value = s.state.main_fun_data.return_value;
            s.add_inst(InstEnt::new(
                IKind::Return(Some(value)),
                None,
                &Token::default(),
            ));

            Ok(())
        })?;

        self.context.represented.push(self.state.main_fun_data.id);

        Ok(())
    }

    fn translate(&mut self) -> Result {
        while let Some(fun) = self.context.unresolved.pop() {
            self.translate_fun(fun)?;
        }

        Ok(())
    }

    fn translate_fun(&mut self, fun: Fun) -> Result {
        let fun_ent = &self.fun(fun);
        let param_len = fun_ent.params.len();
        let scope = fun_ent.scope;
        let module = fun_ent.module;

        let n_ent_ast = fun_ent.kind.normal().ast;
        let ast = std::mem::take(&mut self.state.asts[n_ent_ast]);

        if ast[1].is_empty() {
            self.state.asts[n_ent_ast] = ast;
            self.finalize_fun(fun);
            return Ok(());
        }

        let mut shadowed = self.context.pool.get();
        for i in 0..param_len {
            let (id, ty) = self.fun(fun).params[i];
            shadowed.push((id, self.state.types.link(id, ty)))
        }

        if let Some(scope) = scope {
            let ty = unsafe { std::mem::transmute::<&Ast, &Ast>(&self.collector.scopes[scope].ty) };
            let ty = self.parse_type(module, ty)?;
            let id = TYPE_SALT
                .add(ID::new("Self"))
                .add(self.state.modules[module].id);

            shadowed.push((id, self.state.types.link(id, ty)));
        }

        let entry_point = self.new_block();
        self.make_block_current(entry_point);

        let sig = &mut self.fun_mut(fun).kind.normal_mut().sig;
        let args = std::mem::take(&mut sig.args);
        let ret = sig.ret;
        let mut arg_buffer = self.context.pool.get();
        self.clear_vars();

        let header = &ast[0];
        let mut i = 0;
        for arg_group in header[1..header.len() - 2].iter() {
            for arg in arg_group[..arg_group.len() - 1].iter() {
                let var = self.new_value(arg.token.span.hash, args[i], false);
                self.context.vars.push(var);
                arg_buffer.push(var);
                i += 1;
            }
        }
        if let Some(ret) = ret {
            if self.ty(ret).on_stack(self.ptr_ty) {
                let ty = self.pointer_of(ret);
                let value = self.new_anonymous_value(ty, false);
                arg_buffer.push(value);
            }
        }
        self.fun_mut(fun).kind.normal_mut().sig.args = args;
        let args = self.make_value_slice(&arg_buffer);
        self.inst_mut(entry_point).kind.block_mut().args = args;

        let value = self.block(fun, &ast[1])?;

        if let (Some(value), Some(_), Some(ret)) = (value, self.context.block, ret) {
            let value_ty = self.value(value).ty;
            let token = &ast[1].last().unwrap().token;
            self.assert_type(value_ty, ret, token)?;
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if let (Some(ret), Some(_)) = (ret, self.context.block) {
            let value = self.new_temp_value(ret);
            let token = &ast[1].last().unwrap().token;
            self.add_inst(InstEnt::new(IKind::Zeroed, Some(value), token));
            let value = self.return_value(fun, value, token);
            self.add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if self.context.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Return(None),
                None,
                &ast[1].last().unwrap_or(&Ast::none()).token,
            ));
        }

        self.state.asts[n_ent_ast] = ast;

        for value_id in self.context.body.values.ids() {
            let ty = self.value(value_id).ty;
            let on_stack = self.ty(ty).on_stack(self.ptr_ty);
            self.value_mut(value_id).on_stack = self.value(value_id).on_stack || on_stack;
        }

        for (id, shadow) in shadowed.drain(..) {
            self.state.types.remove_link(id, shadow);
        }

        self.finalize_fun(fun);

        Ok(())
    }

    fn finalize_fun(&mut self, fun: Fun) {
        let normal = std::mem::take(&mut self.fun_mut(fun).kind).into_normal();

        let represented = RFun {
            sig: normal.sig,
            body: std::mem::take(&mut self.context.body),
            compiled: None,
        };

        self.fun_mut(fun).kind = FKind::Represented(represented);

        self.context.represented.push(fun);
    }

    fn return_value(&mut self, fun: Fun, value: Value, token: &Token) -> Value {
        let ty = self.signature_of(fun).ret.unwrap();
        if self.ty(ty).on_stack(self.ptr_ty) {
            let entry = self.context.body.insts.first().unwrap();
            let args = self.value_slice(self.inst(entry).kind.block().args);
            let return_value = args[args.len() - 1];

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
            if self.context.block.is_none() {
                break;
            }
            self.statement(fun, statement)?;
        }

        let value = if self.context.block.is_some() {
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
                FError::new(FEKind::ContinueOutsideLoop, ast.token)
            } else {
                FError::new(FEKind::WrongLabel, ast.token)
            }
        })?;

        self.add_inst(InstEnt::new(
            IKind::Jump(loop_header.start_block, ValueSlice::empty()),
            None,
            &ast.token,
        ));

        Ok(())
    }

    fn break_statement(&mut self, fun: Fun, ast: &Ast) -> Result {
        let loop_header = self.find_loop(&ast[0].token).map_err(|outside| {
            if outside {
                FError::new(FEKind::BreakOutsideLoop, ast.token)
            } else {
                FError::new(FEKind::WrongLabel, ast.token)
            }
        })?;

        if ast[1].kind != AKind::None {
            let return_value = self.expr(fun, &ast[1])?;
            let args = self
                .inst(loop_header.end_block)
                .kind
                .block()
                .args;
            let current_value = self.value_slice(args).first();
            if current_value.is_none() {
                let ty = self.value(return_value).ty;
                let value = self.new_temp_value(ty);
                let args = self.make_value_slice(&[value]);
                self.inst_mut(loop_header.end_block)
                    .kind
                    .block_mut()
                    .args = args;
            }

            let args = self.make_value_slice(&[return_value]);
            self.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, args),
                None,
                &ast.token,
            ));
        } else {
            self.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, ValueSlice::empty()),
                None,
                &ast.token,
            ));
        }

        Ok(())
    }

    fn return_statement(&mut self, fun: Fun, ast: &Ast) -> Result {
        let ty = self.signature_of(fun).ret;

        let value = if ast[0].kind == AKind::None {
            if let Some(ty) = ty {
                let temp_value = self.new_temp_value(ty);
                self.add_inst(InstEnt::new(IKind::Zeroed, Some(temp_value), &ast.token));
                Some(self.return_value(fun, temp_value, &ast.token))
            } else {
                None
            }
        } else {
            let ty = ty.ok_or_else(|| FError::new(FEKind::UnexpectedReturnValue, ast[0].token))?;
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
        let module = self.fun(fun).module;

        for var_line in statement.iter() {
            let ty = if var_line[1].kind == AKind::None {
                None
            } else {
                Some(self.parse_type(module, &var_line[1])?)
            };

            if var_line[2].kind == AKind::None {
                for name in var_line[0].iter() {
                    let ty = ty.unwrap();
                    let name = name.token.span.hash;

                    let temp_value = self.context.body.values.add(ValueEnt::temp(ty));

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
                    let name = name.token.span.hash;
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
            .ok_or_else(|| FError::new(FEKind::ExpectedValue, ast.token))
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
        let args = &[target, index];
        let span = self.state.index_span;
        let result = self
            .call_low(fun, None, None, FUN_SALT, &span, &[], args, &ast.token)?
            .ok_or_else(|| FError::new(FEKind::ExpectedValue, ast.token))?;

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
            return Err(FError::new(FEKind::EmptyArray, ast.token));
        }

        let element_ty = element_ty.unwrap();
        let element_size = self.ty(element_ty).size;

        let ty = self.array_of(element_ty, length);

        let result = self.new_anonymous_value(ty, true);
        self.add_inst(InstEnt::new(IKind::Uninitialized, Some(result), &ast.token));

        for (i, &value) in values.iter().enumerate() {
            let offset = self.new_anonymous_value(element_ty, false);
            self.value_mut(offset).offset = element_size.mul(Size::new(i as u32, i as u32));
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
        let value = self.expr(fun, &ast[1])?;

        let mut values = self.context.pool.get();
        values.push(value);
        self.call_low(
            fun,
            None,
            None,
            UNARY_SALT,
            &ast[0].token.span,
            &[],
            &values,
            &ast.token,
        )
    }

    fn dot_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let module = self.fun(fun).module;
        let header = self.expr(fun, &ast[0])?;
        let mutable = self.value(header).mutable;
        let field = ast[1].token.span.hash;

        let inst = self.add_inst(InstEnt::new(IKind::NoOp, None, &Token::default()));
        let value = self.new_anonymous_value(self.state.builtin_repo.bool, mutable);
        self.value_mut(value).inst = Some(inst);
        let ty = self.field_access(header, field, value, &ast.token, module)?;
        self.context.body.insts.remove(inst);
        self.value_mut(value).ty = ty;
        Ok(Some(value))
    }

    fn find_field(&mut self, ty: Type, field_id: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = self.context.pool.get();
        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            let stype = match &self.ty(frontier[i].2).kind {
                TKind::Structure(stype) => stype,
                &TKind::Pointer(pointed) => match &self.ty(pointed).kind {
                    TKind::Structure(stype) => stype,
                    _ => continue,
                },
                _ => continue,
            };
            for (j, field) in stype.fields.iter().enumerate() {
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
        let name = ast[0].token.span.hash;

        let start_block = self.new_block();
        let end_block = self.new_block();

        let header = Loop {
            name,
            start_block,
            end_block,
        };

        self.add_inst(InstEnt::new(
            IKind::Jump(start_block, ValueSlice::empty()),
            None,
            &ast.token,
        ));

        self.context.loops.push(header);
        self.make_block_current(start_block);
        self.block(fun, &ast[1])?;
        self.context
            .loops
            .pop()
            .expect("expected previously pushed header");

        if self.context.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Jump(start_block, ValueSlice::empty()),
                None,
                &ast.token,
            ));
        }
        self.make_block_current(end_block);

        let value = if self.inst(end_block).kind.block().args.len() == 0 {
            None
        } else {
            let args = self.inst(end_block).kind.block().args;
            Some(self.value_slice(args)[0])
        };

        Ok(value)
    }

    fn if_expr(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let cond_expr = &ast[0];
        let cond_val = self.expr(fun, cond_expr)?;
        let cond_type = self.value(cond_val).ty;

        let then_block = self.new_block();
        self.add_inst(InstEnt::new(
            IKind::JumpIfTrue(cond_val, then_block, ValueSlice::empty()),
            None,
            &cond_expr.token,
        ));

        self.assert_type(cond_type, self.state.builtin_repo.bool, &cond_expr.token)?;

        let merge_block = self.new_block();

        let else_branch = &ast[2];
        let else_block = if else_branch.kind == AKind::None {
            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, ValueSlice::empty()),
                None,
                &else_branch.token,
            ));
            None
        } else {
            let some_block = self.new_block();
            self.add_inst(InstEnt::new(
                IKind::Jump(some_block, ValueSlice::empty()),
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
                return Err(FError::new(FEKind::MissingElseBranch, ast.token));
            }

            let args = self.make_value_slice(&[val]);
            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, args),
                None,
                &ast.token,
            ));

            let ty = self.value(val).ty;
            let value = self.new_temp_value(ty);
            let args = self.make_value_slice(&[value]);
            self.inst_mut(merge_block).kind.block_mut().args = args;
            result = Some(value);
        } else if self.context.block.is_some() {
            self.add_inst(InstEnt::new(
                IKind::Jump(merge_block, ValueSlice::empty()),
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
                let args = self.make_value_slice(&[val]);
                self.add_inst(InstEnt::new(
                    IKind::Jump(merge_block, args),
                    None,
                    value_token,
                ));
                if result.is_some() {
                    
                } else if then_filled {
                    let ty = self.value(val).ty;
                    let value = self.new_temp_value(ty);
                    let args = self.make_value_slice(&[value]);
                    self.inst_mut(merge_block).kind.block_mut().args = args;
                    result = Some(value);
                } else {
                    return Err(FError::new(FEKind::UnexpectedValue, ast.token));
                }
            } else {
                if self.context.block.is_some() {
                    if result.is_some() {
                        return Err(FError::new(FEKind::ExpectedValue, ast.token));
                    }
                    self.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, ValueSlice::empty()),
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
        let mut values = self.context.pool.get();
        for value in ast[1..].iter() {
            let value = self.expr(fun, value)?;
            values.push(value);
        }

        let module = self.fun(fun).module;
        let mut generic_params = self.context.pool.get();
        let name = match ast[0].kind {
            AKind::Ident | AKind::Path => &ast[0],
            AKind::Deref => {
                let pointer = self.expr(fun, &ast[0][0])?;
                let ty = self.value(pointer).ty;

                let fp = match &self.ty(ty).kind {
                    TKind::FunPointer(fp) => fp,
                    _ => {
                        return Err(FError::new(FEKind::ExpectedFunctionPointer, ast.token));
                    }
                };

                let ret = fp.ret;

                let mismatched = fp.args.len() != values.len()
                    || fp
                        .args
                        .iter()
                        .zip(values.iter())
                        .any(|(&param, &value)| self.value(value).ty != param);

                if mismatched {
                    return Err(FError::new(
                        FEKind::FunPointerArgMismatch(
                            ty,
                            values.iter().map(|&v| self.value(v).ty).collect(),
                        ),
                        ast.token,
                    ));
                }

                let do_stacktrace = self.state.do_stacktrace;

                if do_stacktrace {
                    self.gen_frame_push(&ast.token);
                }

                let value = ret.map(|ty| self.new_temp_value(ty));
                let args = self.make_value_slice(&values);
                self.add_inst(InstEnt::new(
                    IKind::FunPointerCall(pointer, args),
                    value,
                    &ast.token,
                ));

                if do_stacktrace {
                    self.gen_frame_pop(&ast.token);
                }

                return Ok(value);
            }
            AKind::Instantiation => {
                for arg in ast[0][1..].iter() {
                    let id = self.parse_type(module, arg)?;
                    generic_params.push(id);
                }
                &ast[0][0]
            }
            _ => unreachable!(),
        };

        let (module, caller, name) = self.parse_ident(module, name)?;

        let caller = if ast.kind == AKind::Call(true) {
            None
        } else {
            Some(caller)
        };

        let result = self.call_low(
            fun,
            module,
            caller,
            FUN_SALT,
            &name.span,
            &generic_params,
            &values,
            &ast.token,
        );

        result
    }

    fn call_low(
        &mut self,
        fun: Fun,
        target: Option<Mod>,
        caller: Option<Option<Type>>,
        salt: ID,
        name: &Span,
        params: &[Type],
        original_values: &[Value],
        token: &Token,
    ) -> ExprResult {
        let mut values = self.context.pool.get();
        values.extend(original_values.iter().cloned());
        let mut types = self.context.pool.get();
        types.extend(values.iter().map(|&v| self.value(v).ty));
        let module = self.fun(fun).module;

        let id = salt.add(name.hash);

        let mut module_buffer = self.context.pool.get();

        let (result, field, final_type) = if let Some(caller) = caller {
            let caller = caller.map(|caller| self.ty(caller).id).unwrap_or(ID(0));
            let id = id.add(caller);
            (
                self.find_item(module, id, target, &mut module_buffer),
                None,
                None,
            )
        } else {
            let v = *original_values.first().unwrap();
            let ty = self.value(v).ty;

            let mut result = (Ok(None), None, None);
            let mut fields = self.context.pool.get();
            let mut i = 0;
            fields.push((None, ty));
            while i < fields.len() {
                let (field, ty) = fields[i];
                let ty = self.base_of(ty).unwrap_or(ty);
                let ty_id = self.ty(self.ty(ty).base().unwrap_or(ty)).id;
                module_buffer.clear();
                let pre_result = self.find_item(module, id.add(ty_id), target, &mut module_buffer);
                match pre_result {
                    Ok(Some(_)) => {
                        result = (pre_result, field, Some(ty));
                        break;
                    }
                    Err(_) if i == 0 => {
                        result = (pre_result, None, Some(ty));
                        break;
                    }
                    _ => (),
                }
                match &self.ty(ty).kind {
                    TKind::Structure(stype) => {
                        fields.extend(
                            stype
                                .fields
                                .iter()
                                .filter(|f| f.embedded)
                                .map(|f| (Some(f.id), f.ty)),
                        );
                    }
                    _ => (),
                }
                i += 1;
            }
            result
        };

        if let Some(ty) = final_type {
            types[0] = ty;
        }

        let (_, other_fun) = result
            .map_err(|(a, b)| FError::new(FEKind::AmbiguousFunction(a, b), *token))?
            .ok_or_else(|| {
                FError::new(
                    FEKind::FunctionNotFound(name.clone(), types.to_vec()),
                    *token,
                )
            })?;

        let other_fun = if let FKind::Generic(_) = self.fun(other_fun).kind {
            if caller.is_none() {
                let result = self.create(other_fun, params, &types)?;
                types[0] = self.pointer_of(types[0]);
                if result.is_some() {
                    result
                } else {
                    self.create(other_fun, params, &types)?
                }
            } else {
                self.create(other_fun, params, &types)?
            }
            .ok_or_else(|| {
                FError::new(
                    FEKind::GenericMismatch(name.clone(), types.to_vec()),
                    *token,
                )
            })?
        } else {
            other_fun
        };

        let return_type = self.signature_of(other_fun).ret;

        let value = return_type.map(|t| {
            let on_stack = self.ty(t).on_stack(self.ptr_ty);
            let value = self.new_anonymous_value(t, on_stack);
            if on_stack {
                values.push(value);
            }
            value
        });

        if caller.is_none() {
            if let Some(field) = field {
                let temp = self.new_temp_value(self.state.builtin_repo.bool);
                self.field_access(values[0], field, temp, token, module)?;
                values[0] = temp;
            }

            let first_arg_ty = self.signature_of(other_fun).args[0];

            let first_real_arg_ty = self.value(values[0]).ty;

            if first_real_arg_ty != first_arg_ty {
                if self.base_of(first_real_arg_ty) == Some(first_arg_ty) {
                    values[0] = self.deref_expr_low(values[0], token)?;
                } else {
                    values[0] = self.ref_expr_low(values[0], token);
                }
                debug_assert!(self.value(values[0]).ty == first_arg_ty);
            }
        }

        let sig = self.signature_of(other_fun);
        let mismatched = sig.args.len() != types.len()
            || sig
                .args
                .iter()
                .zip(values.iter())
                .any(|(&a, &b)| a != self.value(b).ty);

        if mismatched {
            types[0] = self.value(values[0]).ty;
            return Err(FError::new(
                FEKind::FunArgMismatch(other_fun, types.to_vec()),
                *token,
            ));
        }

        let do_stacktrace = self.state.do_stacktrace
            && !self.fun(fun).untraced
            && !matches!(self.fun(other_fun).kind, FKind::Builtin(..));
        if do_stacktrace {
            self.gen_frame_push(&token);
        }

        if !self.state.can_access(
            self.fun(fun).module,
            self.fun(other_fun).module,
            self.fun(other_fun).vis,
        ) {
            return Err(FError::new(FEKind::VisibilityViolation, *token));
        }

        let args = self.make_value_slice(&values);

        self.add_inst(InstEnt::new(
            IKind::Call(other_fun, args),
            value,
            token,
        ));

        if do_stacktrace {
            self.gen_frame_pop(&token);
        }

        Ok(value)
    }

    fn gen_frame_pop(&mut self, token: &Token) {
        let pop = FUN_SALT
            .add(ID::new("pop_frame"))
            .add(ID(0))
            .add(self.state.modules[self.state.builtin_module].id);
        let pop = self.state.funs.index(pop).unwrap().clone();
        self.add_inst(InstEnt::new(IKind::Call(pop, ValueSlice::empty()), None, &token));
    }

    fn gen_frame_push(&mut self, token: &Token) {
        let push = FUN_SALT
            .add(ID::new("push_frame"))
            .add(ID(0))
            .add(self.state.modules[self.state.builtin_module].id);
        let push = self.state.funs.index(push).unwrap().clone();
        let line = self.new_temp_value(self.state.builtin_repo.int);
        self.add_inst(InstEnt::new(
            IKind::Lit(LTKind::Int(token.span.line as i64, 0)),
            Some(line),
            token,
        ));
        let column = self.new_temp_value(self.state.builtin_repo.int);
        self.add_inst(InstEnt::new(
            IKind::Lit(LTKind::Int(token.span.column as i64, 0)),
            Some(column),
            token,
        ));
        let file_name = &self.state.sources[token.span.source].name;
        let mut final_file_name = String::with_capacity(file_name.len() + 1);
        final_file_name.push_str(file_name);
        final_file_name.push('\x00');
        let span = self.state.builtin_span(&final_file_name);
        let ptr = self.pointer_of(self.state.builtin_repo.u8);
        let file_name = self.new_temp_value(ptr);
        self.add_inst(InstEnt::new(
            IKind::Lit(LTKind::String(span)),
            Some(file_name),
            token,
        ));

        let args = self.make_value_slice(&[line, column, file_name]);
        self.add_inst(InstEnt::new(
            IKind::Call(push, args),
            None,
            token,
        ));
    }

    fn ident(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let module = self.fun(fun).module;
        let (target, caller, name) = self.parse_ident(module, ast)?;
        let can_be_local = target.is_none() && caller.is_none();
        let caller = caller.map(|c| self.ty(c).id).unwrap_or(ID(0));

        let result = (|| {
            if can_be_local {
                if let Some(var) = self.find_variable(name.span.hash) {
                    return Ok(Some(var));
                }
                if let Some(var) = self.find_constant_parameter(fun, &name) {
                    return Ok(Some(var));
                }
            }

            if let Some(global) = self.find_global(fun, target, caller, &name)? {
                return Ok(Some(global));
            }

            if let Some(local) = self.find_function_pointer(fun, target, caller, &name)? {
                return Ok(Some(local));
            }

            Ok(None)
        })()?
        .ok_or_else(|| FError::new(FEKind::UndefinedVariable, ast.token))?;

        Ok(Some(result))
    }

    fn parse_ident(
        &mut self,
        module: Mod,
        name: &Ast,
    ) -> Result<(Option<Mod>, Option<Type>, Token)> {
        if name.kind == AKind::Ident {
            Ok((None, None, name.token))
        } else {
            match &name[..] {
                [module_name, caller_name, name] => {
                    let dep = self
                        .state
                        .find_dep(module, &module_name.token)
                        .ok_or_else(|| FError::new(FEKind::UnknownModule, module_name.token))?;
                    let caller = self.parse_type(dep, caller_name)?;

                    Ok((Some(dep), Some(caller), name.token))
                }
                [something, name] => {
                    if let Some(dep) = self.state.find_dep(module, &something.token) {
                        Ok((Some(dep), None, name.token))
                    } else {
                        let caller = self.parse_type(module, something)?;
                        Ok((None, Some(caller), name.token))
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    fn find_function_pointer(
        &mut self,
        fun: Fun,
        target: Option<Mod>,
        caller: ID,
        ident: &Token,
    ) -> ExprResult {
        let mut module_buffer = self.context.pool.get();
        let module = self.fun(fun).module;
        let id = FUN_SALT.add(ident.span.hash).add(caller);
        Ok(
            match self
                .find_item(module, id, target, &mut module_buffer)
                .map_err(|(a, b)| FError::new(FEKind::AmbiguousFunction(a, b), ident.clone()))?
            {
                Some((other_module, f)) => {
                    if !self
                        .state
                        .can_access(module, other_module, self.state.funs[f].vis)
                    {
                        return Err(FError::new(FEKind::VisibilityViolation, ident.clone()));
                    }
                    let ty = self.function_type_of(module, f);
                    let value = self.new_temp_value(ty);
                    self.add_inst(InstEnt::new(IKind::FunPointer(f), Some(value), ident));
                    Some(value)
                }
                None => None,
            },
        )
    }

    fn find_global(
        &mut self,
        fun: Fun,
        target: Option<Mod>,
        caller: ID,
        name: &Token,
    ) -> ExprResult {
        let module = self.fun(fun).module;

        let id = GLOBAL_SALT.add(name.span.hash).add(caller);

        let mut module_buffer = self.context.pool.get();
        let global = self
            .find_item(module, id, target, &mut module_buffer)
            .map_err(|(a, b)| FError::new(FEKind::AmbiguousGlobal(a, b), name.clone()))?;

        let found = if let Some((other_module, found)) = global {
            if !self
                .state
                .can_access(module, other_module, self.state.globals[found].vis)
            {
                return Err(FError::new(FEKind::GlobalVisibilityViolation, name.clone()));
            }
            found
        } else {
            return Ok(None);
        };

        let ty = self.state.globals[found].ty;

        let value = self.new_anonymous_value(ty, self.state.globals[found].mutable);
        self.add_inst(InstEnt::new(IKind::GlobalLoad(found), Some(value), name));

        Ok(Some(value))
    }

    fn find_constant_parameter(&mut self, fun: Fun, token: &Token) -> Option<Value> {
        let name = TYPE_SALT
            .add(token.span.hash)
            .add(self.state.modules[self.fun(fun).module].id);
        if let Some(&(_, ty)) = self.fun(fun).params.iter().find(|&(p, _)| *p == name) {
            let ty = &self.ty(ty).kind;
            match ty {
                TKind::Constant(t) => {
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
            LTKind::Char(_) => self.state.builtin_repo.u32,
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
        match self.state.display(&ast[0].token.span) {
            "=" => return self.assignment(fun, ast),
            "as" => return self.bit_cast(fun, ast),
            _ => (),
        }

        let left = self.expr(fun, &ast[1])?;
        let right = self.expr(fun, &ast[2])?;

        let mut buffer = self.context.pool.get();
        buffer.extend(&[left, right]);

        self.call_low(
            fun,
            None,
            None,
            BINARY_SALT,
            &ast[0].token.span,
            &[],
            &buffer,
            &ast.token,
        )
    }

    fn bit_cast(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let module = self.fun(fun).module;
        let target = self.expr(fun, &ast[1])?;
        let ty = self.parse_type(module, &ast[2])?;

        let original_datatype = self.value(target).ty;
        let original_size = self.ty(original_datatype).size;
        let datatype_size = self.ty(ty).size;

        if original_size != datatype_size {
            return Err(FError::new(
                FEKind::InvalidBitCast(original_size, datatype_size),
                ast.token,
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
        module: Mod,
    ) -> Result<Type> {
        let mutable = self.value(header).mutable || self.base_of(self.value(header).ty).is_some();
        let header_datatype = self.value(header).ty;
        let mut path = vec![];
        if !self.find_field(header_datatype, field, &mut path) {
            return Err(FError::new(FEKind::UnknownField(header_datatype), *token));
        }

        let mut offset = Size::ZERO;
        let mut current_type = header_datatype;
        for &i in path.iter().rev() {
            let ty = self.ty(current_type);
            match &ty.kind {
                TKind::Structure(stype) => {
                    let field = &stype.fields[i];
                    if !self.state.can_access(module, ty.module, field.vis) {
                        return Err(FError::new(FEKind::FieldVisibilityViolation, *token));
                    }
                    offset = offset.add(field.offset);
                    current_type = field.ty;
                }
                &TKind::Pointer(pointed) => {
                    let value = self.new_anonymous_value(current_type, mutable);
                    self.value_mut(value).offset = offset;
                    self.add_inst(InstEnt::new(IKind::Offset(header), Some(value), token));
                    let ty = self.ty(pointed);
                    match &ty.kind {
                        TKind::Structure(stype) => {
                            let field = &stype.fields[i];
                            if !self.state.can_access(module, ty.module, field.vis) {
                                return Err(FError::new(FEKind::FieldVisibilityViolation, *token));
                            }
                            offset = field.offset;
                            current_type = field.ty;
                            let loaded = self.new_anonymous_value(pointed, mutable);
                            self.add_inst(InstEnt::new(
                                IKind::Deref(value, false),
                                Some(loaded),
                                token,
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
        val.mutable = mutable;
        val.offset = offset;
        val.ty = current_type;

        Ok(current_type)
    }

    pub fn add_variable(&mut self, name: ID, ty: Type, mutable: bool) -> Value {
        let val = self.new_value(name, ty, mutable);
        self.context.vars.push(val);
        val
    }

    fn assignment(&mut self, fun: Fun, ast: &Ast) -> ExprResult {
        let target = self.expr(fun, &ast[1])?;
        let value = self.expr(fun, &ast[2])?;
        let target_datatype = self.value(target).ty;
        let value_datatype = self.value(value).ty;

        if !self.value(target).mutable {
            return Err(FError::new(FEKind::AssignToImmutable, ast.token));
        }

        match &mut self.inst_mut(self.value(target).inst.unwrap()).kind {
            IKind::Deref(_, assign) => *assign = true,
            _ => (),
        }

        self.assert_type(value_datatype, target_datatype, &ast.token)?;

        self.add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

        Ok(Some(value))
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
        self.context.body.values.add(value)
    }

    pub fn add_inst(&mut self, inst: InstEnt) -> Inst {
        debug_assert!(self.context.block.is_some(), "no block to add inst to");
        let closing = inst.kind.is_closing();
        let value = inst.value;
        let inst = self.context.body.insts.push(inst);
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
        let inst = self.context.body.insts.insert_before(at, inst);
        if let Some(value) = value {
            self.value_mut(value).inst = Some(inst);
        }
        inst
    }

    pub fn new_block(&mut self) -> Inst {
        self.context.body.insts.add_hidden(InstEnt::new(
            IKind::Block(Default::default()),
            None,
            &Token::default(),
        ))
    }

    pub fn make_block_current(&mut self, block: Inst) {
        debug_assert!(
            self.context.block.is_none(),
            "current block is not closed"
        );
        self.context.body.insts.show_as_last(block);
        self.context.block = Some(block);
    }

    pub fn close_block(&mut self) {
        debug_assert!(self.context.block.is_some(), "no block to close");
        let block = self.context.block.unwrap();
        let inst = self.context.body.insts.push(InstEnt::new(
            IKind::BlockEnd(block),
            None,
            &Token::default(),
        ));
        self.inst_mut(block).kind.block_mut().end = Some(inst);
        self.context.block = None;
    }

    fn create(
        &mut self,
        fun: Fun,
        explicit_params: &[Type],
        values: &[Type],
    ) -> Result<Option<Fun>> {
        let g_ent = self.state.funs[fun].kind.generic_mut();
        let g_ent_len = g_ent.signature.elements.len();
        let elements = std::mem::take(&mut g_ent.signature.elements);

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
        let ok = 'o: loop {
            if i >= g_ent_len {
                break true;
            }
            let (amount, length) = match elements[i] {
                GenericElement::NextArgument(amount, length) => (amount, length),
                _ => unreachable!("{:?}", elements[i]),
            };

            for _ in 0..amount {
                self.load_arg_from_datatype(values[j], &mut arg_buffer, &mut stack);
                let arg = &elements[i + 1..i + 1 + length];
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
                                                break 'o false;
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
                                    _ => break 'o false,
                                },
                                _ => break 'o false,
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
        };

        let fun_ent = self.fun_mut(fun);

        if !ok {
            fun_ent.kind.generic_mut().signature.elements = elements;
            return Ok(None);
        }

        let &mut FunEnt {
            module,
            untraced,
            vis,
            scope,
            inline,
            attrs,
            hint,
            name,
            linkage,
            ..
        } = fun_ent;
        let g_ent = fun_ent.kind.generic_mut();
        g_ent.signature.elements = elements;
        let call_conv = g_ent.call_conv;
        let g_params = std::mem::take(&mut g_ent.signature.params);
        let mut id = FUN_SALT.add(fun_ent.name.hash);
        let ast_id = g_ent.ast;
        let fun_module_id = self.state.modules[module].id;

        let mut shadowed = self.context.pool.get();
        let mut final_params = self.context.pool.get();
        for i in 0..params.len() {
            if let Some(ty) = params[i] {
                let id = TYPE_SALT.add(g_params[i]).add(fun_module_id);
                shadowed.push((id, self.state.types.link(id, ty)));
                final_params.push((id, ty));
            } else {
                return Ok(None);
            }
        }

        self.fun_mut(fun).kind.generic_mut().signature.params = g_params;

        if let Some(scope) = scope {
            let ty = unsafe { std::mem::transmute::<&Ast, &Ast>(&self.collector.scopes[scope].ty) };
            let ty = self.parse_type(module, ty)?;
            let id = TYPE_SALT.add(ID::new("Self")).add(fun_module_id);
            shadowed.push((id, self.state.types.link(id, ty)));
        }

        let ast = std::mem::take(&mut self.state.asts[ast_id]);
        let mut signature = self.parse_signature(module, &ast[0])?;
        for final_param in final_params.iter() {
            id = id.add(self.ty(final_param.1).id);
        }
        id = id.add(self.state.modules[module].id);
        self.state.asts[ast_id] = ast;
        signature.call_conv = call_conv;

        for (id, ty) in shadowed.drain(..) {
            self.state.types.remove_link(id, ty);
        }

        if let Some(&fun) = self.state.funs.index(id) {
            return Ok(Some(fun));
        }

        let n_ent = NFun {
            sig: signature,
            ast: ast_id,
        };

        let kind = FKind::Normal(n_ent);

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
            untraced,
            inline,
            linkage,
            alias: None,
        };

        let (shadowed, id) = self.state.funs.insert(id, new_fun_ent);
        debug_assert!(shadowed.is_none());
        self.state.modules[module].items.push(ModItem::Fun(id));

        self.context.unresolved.push(id);

        Ok(Some(id))
    }

    fn assert_type(&self, actual: Type, expected: Type, token: &Token) -> Result {
        if actual == expected {
            Ok(())
        } else {
            Err(FError::new(FEKind::TypeMismatch(actual, expected), *token))
        }
    }

    fn collect(&mut self, module: Mod) -> Result {
        let module_id = self.state.modules[module].id;

        let mut functions = std::mem::take(&mut self.collector.functions);
        for Item { attrs, ast, scope } in functions.drain(..) {
            self.collect_fun(ast, module, module_id, attrs, scope)?
        }
        self.collector.functions = functions;

        self.with_main_function(|s| {
            let mut globals = std::mem::take(&mut s.collector.globals);
            for Item { attrs, ast, scope } in globals.drain(..) {
                s.collect_global_var(ast, module, module_id, attrs, scope)?
            }
            s.collector.globals = globals;

            for i in 0..s.context.entry_points.len() {
                let entry_point = s.context.entry_points[i];
                s.add_entry(entry_point)?;                
            }

            s.context.entry_points.clear();

            Ok(())
        })?;

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
        let scope_id = if let Some(scope_id) = scope {
            let scope_ent = std::mem::take(&mut self.collector.scopes[scope_id]);
            if scope_ent.params.len() > 0 {
                return Err(FError::new(
                    FEKind::VarInsideGenericScope(scope_ent.ty.token),
                    ast.token,
                ));
            }
            let ty = match scope_ent.ty.kind {
                AKind::Ident => self.parse_type(module, &scope_ent.ty)?,
                AKind::Instantiation => self.parse_type(module, &scope_ent.ty[0])?,
                AKind::Array => self.state.builtin_repo.array,
                _ => unreachable!(),
            };
            self.collector.scopes[scope_id] = scope_ent;
            self.ty(ty).id
        } else {
            ID(0)
        };

        let (vis, mutable) = match ast.kind {
            AKind::VarStatement(vis, mutable) => (vis, mutable),
            _ => unreachable!(),
        };

        let (linkage, alias) = self.resolve_linkage(attrs)?;
        let fun = self.state.main_fun_data.id;
        self.fun_mut(fun).module = module;

        for var_line in ast.iter_mut() {
            let ty = if var_line[1].kind != AKind::None {
                Some(self.parse_type(module, &var_line[1])?)
            } else {
                None
            };

            let mut values = std::mem::take(&mut var_line[2]);

            for (name, ast) in var_line[0]
                .iter()
                .zip(values.drain(..).chain(std::iter::repeat(Ast::none())))
            {
                let hint = name.token;
                let id = GLOBAL_SALT.add(hint.span.hash).add(scope_id).add(module_id);
    
                let (shadowed, global) = self.state.globals.insert(id, GlobalEnt::default());
                if let Some(shadowed) = shadowed {
                    return Err(FError::new(
                        FEKind::RedefinedGlobal(shadowed.hint.clone()),
                        name.token,
                    ));
                }
                self.state.modules[module].items.push(ModItem::Global(global));

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

                let g_ent = GlobalEnt {
                    vis,
                    mutable,
                    id,
                    module,
                    ty,
                    ast,
                    data_id: None,
                    hint,
                    attrs,
                    scope,
                    linkage: LinkageWr(linkage),
                    alias,
                };

                self.state.globals[global] = g_ent;

                self.context.resolved_globals.push(global);
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
        let mut shadowed = None;

        let (caller, generic) = if let Some(scope_id) = scope {
            let raw_ty = std::mem::take(&mut self.collector.scopes[scope_id].ty);
            let generic = self.collector.scopes[scope_id].params.len() > 0;
            let ty = match raw_ty.kind {
                AKind::Ident => self.parse_type(module, &raw_ty)?,
                AKind::Instantiation => self.parse_type(module, &raw_ty[0])?,
                AKind::Array => self.state.builtin_repo.array,
                _ => unreachable!(),
            };

            if !generic {
                let ty = self.parse_type(module, &raw_ty)?;
                let id = TYPE_SALT.add(ID::new("Self")).add(module_id);
                shadowed = Some((id, self.state.types.link(id, ty)));
            };

            self.collector.scopes[scope_id].ty = raw_ty;
            (self.ty(ty).id, generic)
        } else {
            (ID(0), false)
        };

        let vis = match ast.kind {
            AKind::Fun(vis) => vis,
            _ => unreachable!(),
        };

        let salt = match ast[0].kind {
            AKind::FunHeader(op_kind) => match op_kind {
                OpKind::Normal => FUN_SALT,
                OpKind::Binary => BINARY_SALT,
                OpKind::Unary => UNARY_SALT,
            },
            _ => unreachable!(),
        };

        let header = &ast[0];

        let call_conv = if let Some(attr) = self
            .collector
            .attr(&attrs, ID::new("call_conv"))
            .or_else(|| {
                if header[header.len() - 1].kind == AKind::Ident {
                    Some(&header[header.len() - 1])
                } else {
                    None
                }
            }) {
            let str = self
                .state
                .display(&attr.get(1).unwrap_or(&attr[0]).token.span);
            CallConv::from_str(str)
                .ok_or_else(|| FError::new(FEKind::InvalidCallConv, attr.token))?
        } else {
            CallConv::Fast
        };

        let entry = self.collector.attr(&attrs, ID::new("entry")).is_some();

        let (linkage, mut alias) = self.resolve_linkage(attrs)?;

        let hint = header.token;
        let name = &header[0];
        let (name, mut id, kind, unresolved) = if name.kind == AKind::Ident && !generic {
            let mut signature = self.parse_signature(module, header)?;
            signature.call_conv = call_conv;

            let fun_id = salt.add(name.token.span.hash).add(caller);

            let name = name.token.span;

            if linkage == Linkage::Import && alias.is_none() {
                alias = Some(name);
            }

            let ast = self.state.asts.add(ast);
            let n_ent = NFun {
                sig: signature,
                ast,
            };

            (name, fun_id, FKind::Normal(n_ent), true)
        } else if name.kind == AKind::Instantiation || generic {
            let nm = if name.kind == AKind::Instantiation {
                &name[0]
            } else {
                name
            };

            if nm.kind != AKind::Ident {
                return Err(FError::new(FEKind::InvalidFunctionHeader, nm.token));
            }

            let mut params = self.context.pool.get();
            if name.kind == AKind::Instantiation {
                for param in name[1..].iter() {
                    params.push(param.token.span.hash);
                }
            }

            if let Some(scope_id) = scope {
                params.extend(self.collector.scopes[scope_id].params.iter());
            }

            let mut arg_count = 0;
            let mut args = self.context.pool.get();
            for arg_section in &header[1..header.len() - 2] {
                let amount = arg_section.len() - 1;
                let idx = args.len();
                args.push(GenericElement::NextArgument(amount, 0));
                self.load_arg(module, scope, &arg_section[amount], &params, &mut args)?;
                let additional = args.len() - idx - 1;
                args[idx] = GenericElement::NextArgument(amount, additional);
                arg_count += amount;
            }

            let id = salt.add(nm.token.span.hash).add(caller);

            let signature = GenericSignature {
                params: params.clone(),
                elements: args.clone(),
                arg_count,
            };

            let nm = nm.token.span;

            let g_ent = GFun {
                call_conv,
                signature,
                ast: self.state.asts.add(ast),
            };

            (nm, id, FKind::Generic(g_ent), false)
        } else {
            return Err(FError::new(FEKind::InvalidFunctionHeader, name.token));
        };

        if let Some((id, shadowed)) = shadowed {
            self.state.types.remove_link(id, shadowed);
        }

        id = id.add(module_id);

        let fun_ent = FunEnt {
            vis,
            id,
            module,
            hint: hint.clone(),
            params: vec![],
            kind,
            name,
            untraced: self.collector.attr(&attrs, ID::new("untraced")).is_some(),
            inline: self.collector.attr(&attrs, ID::new("inline")).is_some(),
            attrs,
            scope,
            linkage: LinkageWr(linkage),
            alias,
        };

        let (shadowed, id) = self.state.funs.insert(id, fun_ent);
        if let Some(shadowed) = shadowed {
            return Err(FError::new(
                FEKind::Redefinition(shadowed.hint.clone()),
                hint,
            ));
        }
        self.state.modules[module].items.push(ModItem::Fun(id));

        if unresolved {
            if entry {
                self.context.entry_points.push(id);
            }
            self.context.unresolved.push(id);
        }

        Ok(())
    }

    fn add_entry(&mut self, id: Fun) -> Result {
        let signature = self.signature_of(id);

        let ret = match signature.args.as_slice() {
            &[] => {
                let value = signature.ret.map(|ty| self.new_temp_value(ty));
                self.add_inst(InstEnt::new(
                    IKind::Call(id, ValueSlice::empty()),
                    value,
                    &self.fun(id).hint,
                ));
                value
            }
            &[count, args] => {
                let value = signature.ret.map(|ty| self.new_temp_value(ty));
                let temp_ptr = self.pointer_of(self.state.builtin_repo.int);
                if count != self.state.builtin_repo.int || args != self.pointer_of(temp_ptr) {
                    return Err(FError::new(
                        FEKind::InvalidEntrySignature,
                        self.fun(id).hint,
                    ));
                }
                let args = self.make_value_slice(&[
                    self.state.main_fun_data.arg1, 
                    self.state.main_fun_data.arg2
                ]);
                self.add_inst(InstEnt::new(
                    IKind::Call(id, args),
                    value,
                    &self.fun(id).hint,
                ));
                value
            }
            _ => {
                return Err(FError::new(
                    FEKind::InvalidEntrySignature,
                    self.fun(id).hint,
                ));
            }
        };

        if let Some(ret) = ret {
            let value = self.state.main_fun_data.return_value;
            self.add_inst(InstEnt::new(
                IKind::Assign(value),
                Some(ret),
                &self.fun(id).hint,
            ));
        }

        Ok(())
    }

    fn make_value_slice(&mut self, values: &[Value]) -> ValueSlice {
        self.context.body.slices.add(values)
    }

    fn parse_signature(&mut self, module: Mod, header: &Ast) -> Result<Signature> {
        let mut args = self.context.pool.get();

        for arg_section in &header[1..header.len() - 2] {
            let ty = self.parse_type(module, &arg_section[arg_section.len() - 1])?;
            for _ in 0..arg_section.len() - 1 {
                args.push(ty);
            }
        }

        let raw_ret_ty = &header[header.len() - 2];
        let ret = if raw_ret_ty.kind != AKind::None {
            Some(self.parse_type(module, raw_ret_ty)?)
        } else {
            None
        };

        Ok(Signature {
            call_conv: CallConv::Fast,
            args: args.clone(),
            ret,
        })
    }

    fn load_arg(
        &mut self,
        module: Mod,
        scope: Option<Scope>,
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
                    if ast.token.span.hash == ID::new("Self") && scope.is_some() {
                        let ast = unsafe {
                            std::mem::transmute::<&Ast, &Ast>(
                                &self.collector.scopes[scope.unwrap()].ty,
                            )
                        };
                        stack.push((ast, false));
                    } else {
                        let id = ast.token.span.hash;
                        if let Some(index) = params.iter().position(|&p| p == id) {
                            buffer.push(GenericElement::Parameter(index));
                        } else {
                            let ty = self.parse_type(module, ast)?;
                            buffer.push(GenericElement::Element(ty, None));
                        }
                    }
                }
                AKind::Instantiation => {
                    let ty = self.parse_type(module, &ast[0])?;
                    buffer.push(GenericElement::Element(ty, None));
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
        if token.span.len() == 0 {
            return self.context.loops.last().cloned().ok_or(true);
        }

        let name = token.span.hash;

        self.context
            .loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.context.loops.is_empty())
    }

    fn base_of_err(&mut self, ty: Type, token: &Token) -> Result<Type> {
        self.base_of(ty)
            .ok_or_else(|| FError::new(FEKind::NonPointerDereference, *token))
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
        self.state.pointer_of(ty)
    }

    fn constant_of(&mut self, constant: TypeConst) -> Type {
        self.state.constant_of(constant)
    }

    #[inline]
    pub fn is_pointer(&self, ty: Type) -> bool {
        matches!(self.ty(ty).kind, TKind::Pointer(..))
    }

    fn push_scope(&mut self) {
        self.context.frames.push(self.context.vars.len());
    }

    fn pop_scope(&mut self) {
        let idx = self.context.frames.pop().unwrap();
        self.context.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Value> {
        self
            .context
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
        &self.context.body.insts[inst]
    }

    fn inst_mut(&mut self, inst: Inst) -> &mut InstEnt {
        &mut self.context.body.insts[inst]
    }

    fn value(&self, value: Value) -> &ValueEnt {
        &self.context.body.values[value]
    }

    fn value_mut(&mut self, value: Value) -> &mut ValueEnt {
        &mut self.context.body.values[value]
    }

    fn array_of(&mut self, ty: Type, length: usize) -> Type {
        self.state.array_of(ty, length)
    }

    fn function_type_of(&mut self, module: Mod, fun: Fun) -> Type {
        let sig = self.signature_of(fun).clone();
        self.state.function_type_of(module, sig)
    }

    fn clear_vars(&mut self) {
        self.context.vars.clear();
    }

    fn fun(&self, fun: Fun) -> &FunEnt {
        &self.state.funs[fun]
    }

    fn fun_mut(&mut self, fun: Fun) -> &mut FunEnt {
        &mut self.state.funs[fun]
    }

    fn signature_of(&self, fun: Fun) -> &Signature {
        match &self.fun(fun).kind {
            FKind::Normal(n) => &n.sig,
            FKind::Represented(r) => &r.sig,
            FKind::Builtin(s) => s,
            _ => todo!(),
        }
    }

    fn resolve_linkage(&self, attrs: Attrs) -> Result<(Linkage, Option<Span>)> {
        if let Some(attr) = self.collector.attr(&attrs, ID::new("linkage")) {
            assert_attr_len(attr, 1)?;
            let linkage = match self.state.display(&attr[1].token.span) {
                "import" => Linkage::Import,
                "export" => Linkage::Export,
                "hidden" => Linkage::Hidden,
                "preemptible" => Linkage::Preemptible,
                "local" => Linkage::Local,
                _ => unreachable!(),
            };

            Ok((linkage, attr.get(2).map(|a| a.token.span)))
        } else {
            Ok((Linkage::Export, None))
        }
    }

    fn with_main_function<F: FnMut(&mut Self) -> Result>(&mut self, mut fun: F) -> Result {
        let prev_vars = std::mem::take(&mut self.context.vars);
        let prev_frames = std::mem::take(&mut self.context.frames);
        let prev_loops = std::mem::take(&mut self.context.loops);
        std::mem::swap(
            &mut self.context.body, 
            &mut self.state.funs[self.state.main_fun_data.id].kind.represented_mut().body,
        );
        std::mem::swap(
            &mut self.context.block, 
            &mut self.state.main_fun_data.current_block
        );

        fun(self)?;

        self.context.vars = prev_vars;
        self.context.frames = prev_frames;
        self.context.loops = prev_loops;
        std::mem::swap(
            &mut self.context.body, 
            &mut self.state.funs[self.state.main_fun_data.id].kind.represented_mut().body,
        );
        std::mem::swap(
            &mut self.context.block, 
            &mut self.state.main_fun_data.current_block
        );

        Ok(())
    }

    fn value_slice(&self, args: ValueSlice) -> &[Value] {
        &self.context.body.slices[args]
    }
}

impl<'a> ItemSearch<Fun> for FParser<'a> {
    fn find(&self, id: ID) -> Option<Fun> {
        self.state.funs.index(id).cloned()
    }

    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        self.state.collect_scopes(module, buffer)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.state.modules[module].id
    }
}

impl<'a> ItemSearch<Global> for FParser<'a> {
    fn find(&self, id: ID) -> Option<Global> {
        self.state.globals.index(id).cloned()
    }

    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        self.state.collect_scopes(module, buffer)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.state.modules[module].id
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
            crate::types::call_conv_error(f)?;
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
                "invalid bit-cast, expected type of size {:?} but got {:?}",
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
                "'{}({})' does not exist within current scope",
                self.state.display(name),
                arguments
                    .iter()
                    .map(|t| format!("{}", TypeDisplay::new(&self.state, *t)))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        },
        FEKind::GenericMismatch(name, arguments) => {
            writeln!(
                f,
                "'{}({})' does not match the generic signature",
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
            let mut frontier = vec![(ty, Span::default(), true)];
            let mut i = 0;
            while i < frontier.len() {
                let (ty, _, embedded) = frontier[i];
                if !embedded {
                    continue;
                }
                match &self.state.types[ty].kind {
                    TKind::Structure(stype) => {
                        for f in stype.fields.iter() {
                            frontier.push((f.ty, f.hint.span, f.embedded));
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
        FEKind::UnknownModule => {
            writeln!(f, "unknown module")?;
        },
        FEKind::InvalidDotCall => {
            writeln!(f, "call cannot have explicit caller type and be a dot call")?;
        },
        FEKind::VisibilityViolation => {
            writeln!(f, "function visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
        },
        FEKind::FieldVisibilityViolation => {
            writeln!(f, "field visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
        },
        FEKind::GlobalVisibilityViolation => {
            writeln!(f, "global variable visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
        },
        FEKind::FunArgMismatch(fun, arguments) => {
            let sig = match &self.state.funs[*fun].kind {
                FKind::Normal(n) => &n.sig,
                FKind::Represented(r) => &r.sig,
                FKind::Builtin(s) => s,
                _ => unreachable!(),
            };
            writeln!(
                f,
                "function argument types are '({})' but you provided '({})'",
                sig.args.iter().map(|&a| format!("{}", TypeDisplay::new(&self.state, a))).collect::<Vec<_>>().join(", "),
                arguments.iter().map(|&a| format!("{}", TypeDisplay::new(&self.state, a))).collect::<Vec<_>>().join(", ")
            )?;
        },
        FEKind::FunPointerArgMismatch(ty, arguments) => {
            writeln!(
                f,
                "function pointer argument types are '({})' but you provided '({})'",
                self.state.types[*ty].kind.fun_pointer().args.iter().map(|&a| format!("{}", TypeDisplay::new(&self.state, a))).collect::<Vec<_>>().join(", "),
                arguments.iter().map(|&a| format!("{}", TypeDisplay::new(&self.state, a))).collect::<Vec<_>>().join(", ")
            )?;
        },
        FEKind::ExpectedFunctionPointer => {
            writeln!(f, "only dereferenced function pointer can be called")?;
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
    FunPointerArgMismatch(Type, Vec<Type>),
    ExpectedFunctionPointer,
    FunArgMismatch(Fun, Vec<Type>),
    GlobalVisibilityViolation,
    FieldVisibilityViolation,
    VisibilityViolation,
    InvalidDotCall,
    UnknownModule,
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
    InvalidBitCast(Size, Size),
    AssignToImmutable,
    ExpectedValue,
    TypeMismatch(Type, Type),
    FunctionNotFound(Span, Vec<Type>),
    GenericMismatch(Span, Vec<Type>),
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

#[derive(Debug, Clone, CustomDefault, MetaSer)]
pub struct FunEnt {
    pub id: ID,
    pub module: Mod,
    pub hint: Token,
    pub params: Vec<(ID, Type)>,
    pub kind: FKind,
    pub name: Span,
    pub attrs: Attrs,
    pub scope: Option<Scope>,
    pub alias: Option<Span>,
    pub vis: Vis,
    #[default(LinkageWr(Linkage::Export))]
    pub linkage: LinkageWr,
    pub untraced: bool,
    pub inline: bool,
}

crate::impl_wrapper!(LinkageWr, Linkage);

type ValueSlice = Range<Value>;

#[derive(Debug, Default, Clone, MetaSer)]
pub struct FunBody {
    pub values: List<Value, ValueEnt>,
    pub insts: LinkedList<Inst, InstEnt>,
    pub slices: ImSlicePool<Value, Value>
}

impl FunBody {
    pub fn clear(&mut self) {
        self.values.clear();
        self.insts.clear();
    }
}

#[derive(Debug, Clone, EnumGetters, MetaSer)]
pub enum FKind {
    Default,
    Builtin(Signature),
    Generic(GFun),
    Normal(NFun),
    Represented(RFun),
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Default
    }
}

#[derive(Debug, Clone, Default, MetaSer)]
pub struct NFun {
    pub sig: Signature,
    pub ast: GAst,
}

#[derive(Debug, Clone, Default, MetaSer)]
pub struct GFun {
    pub call_conv: CallConv,
    pub signature: GenericSignature,
    pub ast: GAst,
}

#[derive(Debug, Clone, MetaSer)]
pub struct RFun {
    pub sig: Signature,
    pub body: FunBody,
    pub compiled: Option<CFun>,
}

impl RFun {
    pub fn value(&self, value: Value) -> &ValueEnt {
        &self.body.values[value]
    }

    pub fn value_mut(&mut self, value: Value) -> &mut ValueEnt {
        &mut self.body.values[value]
    }

    pub fn inst(&self, inst: Inst) -> &InstEnt {
        &self.body.insts[inst]
    }

    pub fn inst_mut(&mut self, inst: Inst) -> &mut InstEnt {
        &mut self.body.insts[inst]
    }

    pub fn slice(&self, slice: ValueSlice) -> &[Value] {
        &self.body.slices[slice]
    }

    pub fn slice_mut(&mut self, slice: ValueSlice) -> &mut [Value] {
        &mut self.body.slices[slice]
    }
}

#[derive(Debug, Clone, CustomDefault, MetaSer)]
pub struct CFun {
    pub bin: CompiledData,
    pub jit: CompiledData,
    #[default(FuncIdWr(FuncId::from_u32(0)))]
    pub id: FuncIdWr,
}

crate::impl_wrapper!(FuncIdWr, FuncId);

#[derive(Clone, Default, MetaSer)]
pub struct CompiledData {
    pub bytes: Vec<u8>,
    pub relocs: Vec<RelocRecordWr>,
}

#[derive(Clone)]
pub struct RelocRecordWr(RelocRecord);

impl MetaSer for RelocRecordWr {
    traits::gen_quick_copy!();
}

impl std::fmt::Debug for CompiledData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompiledData")
            .field("bytes", &self.bytes)
            .field("relocs", &"...")
            .finish()
    }
}

#[derive(Debug, Clone, Default, MetaSer)]
pub struct GenericSignature {
    pub params: Vec<ID>,
    pub elements: Vec<GenericElement>,
    pub arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, MetaQuickSer)]
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

crate::index_pointer!(Inst);

#[derive(Debug, Default, Clone, Copy, MetaQuickSer)]
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

#[derive(Debug, Clone, Copy, MetaQuickSer)]
pub enum IKind {
    NoOp,
    FunPointer(Fun),
    FunPointerCall(Value, ValueSlice),
    GlobalLoad(Global),
    Call(Fun, ValueSlice),
    UnresolvedDot(Value, ID),
    VarDecl(Value),
    Zeroed,
    Uninitialized,
    Lit(LTKind),
    Return(Option<Value>),
    Assign(Value),
    Block(Block),
    BlockEnd(Inst),
    Jump(Inst, ValueSlice),
    JumpIfTrue(Value, Inst, ValueSlice),
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

#[derive(Debug, Clone, Copy, Default, MetaQuickSer)]
pub struct Block {
    pub block: Option<CrBlockWr>,
    pub args: ValueSlice,
    pub end: Option<Inst>,
}

crate::impl_wrapper!(CrBlockWr, CrBlock);

#[derive(Debug, Clone)]
pub struct Loop {
    name: ID,
    start_block: Inst,
    end_block: Inst,
}

crate::index_pointer!(Value);

#[derive(Debug, Clone, Default, MetaSer)]
pub struct ValueEnt {
    pub id: ID,
    pub ty: Type,
    pub inst: Option<Inst>,
    pub value: FinalValue,
    pub offset: Size,
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
            offset: Size::ZERO,
            on_stack: false,
        }
    }

    pub fn temp(ty: Type) -> Self {
        Self {
            id: ID(0),
            ty,
            inst: None,
            value: FinalValue::None,
            offset: Size::ZERO,
            mutable: false,
            on_stack: false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, MetaQuickSer)]
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

crate::index_pointer!(Global);

#[derive(Debug, Clone, CustomDefault, MetaSer)]
pub struct GlobalEnt {
    pub id: ID,
    pub vis: Vis,
    pub mutable: bool,
    pub module: Mod,
    pub ast: Ast,
    pub data_id: Option<DataIdWr>,   
    pub ty: Type,
    pub hint: Token,
    pub attrs: Attrs,
    pub scope: Option<Scope>,
    #[default(LinkageWr(Linkage::Export))]
    pub linkage: LinkageWr,
    pub alias: Option<Span>,

}

crate::impl_wrapper!(DataIdWr, DataId);

#[derive(Debug, Clone, Copy, Default, MetaQuickSer)]
pub struct MainFunData {
    id: Fun,
    arg1: Value,
    arg2: Value,
    return_value: Value,
    current_block: Option<Inst>,
}

#[derive(MetaSer)]
pub struct FState {
    pub t_state: TState,
    pub funs: Table<Fun, FunEnt>,
    pub globals: Table<Global, GlobalEnt>,
    pub main_fun_data: MainFunData,
    pub index_span: Span,
    pub do_stacktrace: bool,
}

crate::inherit!(FState, t_state, TState);

impl Default for FState {
    fn default() -> Self {
        let mut state = Self {
            t_state: TState::default(),
            funs: Table::new(),
            index_span: Span::default(),
            globals: Table::new(),
            main_fun_data: MainFunData::default(),

            do_stacktrace: false,
        };

        let mut body = FunBody::default();

        let arg1 = body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));
        let arg2 = body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));

        let args = body.slices.add(&[arg1, arg2]);

        let entry_point = body.insts.push(InstEnt::new(
            IKind::Block(Block {
                block: None,
                args,
                end: None,
            }),
            None,
            &Token::default(),
        ));

        let zero_value = body
            .values
            .add(ValueEnt::temp(state.builtin_repo.int));
        body.insts.push(InstEnt::new(
            IKind::Zeroed,
            Some(zero_value),
            &Token::default(),
        ));
        let return_value =
            body
                .values
                .add(ValueEnt::new(ID(0), state.builtin_repo.int, true));
        body.insts.push(InstEnt::new(
            IKind::VarDecl(zero_value),
            Some(return_value),
            &Token::default(),
        ));

        let r_fun = RFun {
            sig: Signature {
                call_conv: CallConv::Platform,
                args: vec![
                    state.builtin_repo.int, //arg count
                    state.builtin_repo.int, //args
                ],
                ret: Some(state.builtin_repo.int),
            },
            body,
            compiled: None,
        };

        let name = state.builtin_span("main");

        let main_fun = FunEnt {
            vis: Vis::Public,
            kind: FKind::Represented(r_fun),
            name,
            alias: Some(name),

            ..Default::default()
        };

        let id = state.funs.add_hidden(main_fun);

        state.main_fun_data = MainFunData {
            id,
            arg1,
            arg2,
            return_value,
            current_block: Some(entry_point),
        };

        let span = state.builtin_span("__index__");

        state.index_span = span;

        let module_id = state.modules[state.builtin_module].id;

        let types = state.builtin_repo.type_list();

        fn create_builtin_fun(
            state: &mut FState,
            module: ID,
            salt: ID,
            name: Span,
            args: &[Type],
            ret: Option<Type>,
        ) {
            let id = salt.add(name.hash).add(state.types[args[0]].id).add(module);
            let sig = Signature {
                call_conv: CallConv::Fast,
                args: args.to_vec(),
                ret,
            };

            let fun_ent = FunEnt {
                id,
                name,
                vis: Vis::Public,
                module: state.builtin_module,
                kind: FKind::Builtin(sig),

                ..Default::default()
            };
            assert!(state.funs.insert(id, fun_ent).0.is_none());
        }

        for i in types {
            for j in types {
                let name = state.types[i].name.clone();
                create_builtin_fun(&mut state, module_id, FUN_SALT, name, &[j], Some(i));
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
                let op = state.builtin_span(op);
                for &datatype in types.iter() {
                    create_builtin_fun(
                        &mut state,
                        module_id,
                        UNARY_SALT,
                        op.clone(),
                        &[datatype],
                        Some(datatype),
                    );
                }
            }
        }

        let builtin_bin_ops = [
            ("+ - * / % == != >= <= > < ^ | & >> <<", integer_types),
            (
                "+ - * / == != >= <= > <",
                &[state.builtin_repo.f32, state.builtin_repo.f64][..],
            ),
            ("&& || ^ | &", &[state.builtin_repo.bool][..]),
        ];

        for &(operators, types) in builtin_bin_ops.iter() {
            for op in operators.split(' ') {
                let op_span = state.builtin_span(op);
                for &ty in types.iter() {
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        state.builtin_repo.bool
                    } else {
                        ty
                    };
                    create_builtin_fun(
                        &mut state,
                        module_id,
                        BINARY_SALT,
                        op_span,
                        &[ty, ty],
                        Some(return_type),
                    );
                }
            }
        }

        state
    }
}

#[derive(Default)]
pub struct FContext {
    pub t_context: TContext,
    pub vars: Vec<Value>,
    pub loops: Vec<Loop>,
    pub frames: Vec<usize>,
    pub body: FunBody,
    pub block: Option<Inst>,
    pub unresolved_globals: Vec<Global>,
    pub resolved_globals: Vec<Global>,
    pub unresolved: Vec<Fun>,
    pub entry_points: Vec<Fun>,
    pub represented: Vec<Fun>,
}

crate::inherit!(FContext, t_context, TContext);

pub fn assert_attr_len(attr: &Ast, len: usize) -> Result {
    if attr.len() - 1 < len {
        Err(FError::new(
            FEKind::TooShortAttribute(attr.len(), len),
            attr.token,
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
        let r_ent = fun.kind.represented();

        writeln!(f, "{}", self.state.display(&fun.hint.span))?;
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
                            self.state.display(&inst.hint.span)
                        )?;
                    } else {
                        writeln!(
                            f,
                            "    {:?} |{}",
                            inst.kind,
                            self.state.display(&inst.hint.span)
                        )?;
                    }
                }
            }
        }

        Ok(())
    }
}

pub fn test() {
    let mut state = FState::default();
    let mut context = FContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/functions/test_project")
        .unwrap();

    let mut collector = Collector::default();

    for module in std::mem::take(&mut state.module_order).drain(..).rev() {
        let mut ast = std::mem::take(&mut state.modules[module].ast);

        let mut ast = AParser::new(&mut state, &mut ast)
            .parse()
            .map_err(|err| TError::new(TEKind::AError(err), Token::default()))
            .unwrap();

        collector.parse(&mut state, &mut ast, Vis::None);

        FParser::new(&mut state, &mut context, &mut collector, I64)
            .parse(module)
            .map_err(|e| println!("{}", FErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }
}
