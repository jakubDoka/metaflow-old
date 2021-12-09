use core::panic;
use std::fmt::Display;
use std::ops::{Deref, DerefMut, Index, IndexMut};

use crate::ast::{AKind, Ast, Vis};
use crate::lexer::{Token, TokenView};
use crate::util::storage::{LockedList, LinkedList, ReusableList};
use crate::util::{
    sdbm::{SdbmHashState, ID},
    storage::{List, IndexPointer},
};
use crate::types::Type;
use crate::types::*;
use crate::module_tree::*;
use crate::lexer::TKind as LTKind;

use cranelift_codegen::ir::{
    Value as CrValue, 
    Block as CrBlock, 
    StackSlot, Signature,
};
use cranelift_frontend::Variable as CrVar;
use cranelift_module::FuncId;

type Result<T = ()> = std::result::Result<T, FunError>;
type ExprResult = Result<Option<Value>>;

pub struct FParser<'a> {
    state: &'a mut FState,
    context: &'a mut FContext,
}

impl<'a> FParser<'a> {
    pub fn new(state: &'a mut FState, context: &'a mut FContext) -> Self {
        Self { state, context }
    }

    /*pub fn resolve(mut self) -> Result {
        self.collect()?;

        self.translate()?;

        Ok(())
    }

    fn translate(&mut self) -> Result {
        for function in unsafe { self.state.functions.direct_ids() } {
            if !self.state.functions.is_direct_valid(function) {
                continue;
            }
            if !matches!(self.state.functions[function].kind, FKind::Normal(_)) {
                continue;
            }
            self.function(function)?;
            self.context.deref_mut().clear();
        }

        Ok(())
    }

    fn function(&mut self, function: Fun) -> Result {
        let fun = &mut self.state.functions[function];

        let signature = match &mut fun.kind {
            FKind::Normal(signature) => FunSignature {
                args: std::mem::take(&mut signature.args),
                return_type: signature.return_type.clone(),
                struct_return: signature.struct_return,
            },
            _ => unreachable!(),
        };

        let module = fun.module;
        {
            // SAFETY: as long as context lives ast is valid, scope ensures
            // it does not escape
            let ast = unsafe { self.context.function_ast.get(self.state[function].ast) };
            self.function_low(module, ast, &signature)?;
        }

        let fun = &mut self.state.functions[function];
        fun.kind = FKind::Normal(signature);
        fun.body = self.context.function_body.clone();

        Ok(())
    }

    fn function_low(&mut self, module: Mod, ast: &Ast, signature: &FunSignature) -> Result {
        debug_assert!(self.context.current_block.is_none());
        self.context.current_module = Some(module);
        self.context.return_type = signature.return_type;
        let entry_point = self.context.new_block();
        self.context.make_block_current(entry_point);

        signature.args.iter().for_each(|param| {
            let var = self.context.function_body.values.add(param.clone());
            self.context[entry_point].kind.block_mut().args.push(var);
            self.context.variables.push(Some(var));
        });

        if signature.struct_return {
            self.context.struct_return = Some(self.context.variables.pop().unwrap().unwrap());
        }

        if ast[1].is_empty() {
            return Ok(());
        }

        let value = self.block(&ast[1])?;

        if let (Some(value), Some(_), Some(return_type)) =
            (value, self.context.current_block, signature.return_type)
        {
            let value_type = self.context[value].ty;
            let token = &ast[1].last().unwrap().token;
            if self.is_auto(value_type) {
                self.infer(value, return_type)?;
            } else {
                self.assert_type(value_type, return_type, token)?;
            }
            let value = self.return_value(value, token);
            self.context
                .add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if let (Some(return_type), Some(_)) =
            (signature.return_type, self.context.current_block)
        {
            let value = self.new_temp_value(return_type);
            let token = &ast[1].last().unwrap().token;
            self.context
                .add_inst(InstEnt::new(IKind::ZeroValue, Some(value), token));
            let value = self.return_value(value, token);
            self.context
                .add_inst(InstEnt::new(IKind::Return(Some(value)), None, token));
        } else if self.context.current_block.is_some() {
            self.context.add_inst(InstEnt::new(
                IKind::Return(None),
                None,
                &ast[1].last().unwrap_or(&Ast::none()).token,
            ));
        }

        for value_id in self.context.function_body.values.ids() {
            let ty = self.context[value_id].ty;
            let on_stack =
                self.state.types[ty].size > self.state.isa().pointer_bytes() as u32;
            self.context[value_id].on_stack = self.context[value_id].on_stack || on_stack;
        }

        let mut frontier = std::mem::take(&mut self.context.second_graph_frontier);
        let mut unresolved = std::mem::take(&mut self.context.unresolved_functions);
        for inst in unresolved.drain(..) {
            match &self.context[inst].kind {
                IKind::UnresolvedCall(..) => {
                    self.infer_call(inst, &mut frontier)?;
                }
                _ => (),
            }

            for (value, ty) in frontier.drain(..) {
                self.infer(value, ty)?;
            }
        }
        self.context.second_graph_frontier = frontier;

        for (id, dep) in self.context.type_graph.iter() {
            if dep.len() > 0 {
                let inst = self
                    .context
                    .function_body
                    .insts
                    .iter()
                    .find(|(_, inst)| {
                        inst.value.is_some()
                            && self.context[inst.value.unwrap()].type_dependency == Some(id)
                    })
                    .unwrap()
                    .0
                    .clone();

                return Err(FunError::new(
                    FEKind::UnresolvedType,
                    &self.context[inst].token_hint,
                ));
            }
        }

        Ok(())
    }

    fn return_value(&mut self, value: Value, token: &Token) -> Value {
        if let Some(struct_return) = self.context.struct_return {
            let deref = self.new_temp_value(self.context.return_type.unwrap());
            self.context.add_inst(InstEnt::new(
                IKind::Deref(struct_return),
                Some(deref),
                &token,
            ));
            self.context
                .add_inst(InstEnt::new(IKind::Assign(deref), Some(value), &token));
            struct_return
        } else {
            value
        }
    }

    fn block(&mut self, ast: &Ast) -> ExprResult {
        if ast.is_empty() {
            return Ok(None);
        }

        self.context.push_scope();

        for statement in ast[..ast.len() - 1].iter() {
            if self.context.current_block.is_none() {
                break;
            }
            self.statement(statement)?;
        }

        let value = if self.context.current_block.is_some() {
            self.statement(ast.last().unwrap())?
        } else {
            None
        };

        self.context.pop_scope();

        Ok(value)
    }

    fn statement(&mut self, statement: &Ast) -> ExprResult {
        match statement.kind {
            AKind::VarStatement(_) => self.var_statement(statement)?,
            AKind::ReturnStatement => self.return_statement(statement)?,
            AKind::Break => self.break_statement(statement)?,
            AKind::Continue => self.continue_statement(statement)?,
            _ => return self.expr_low(statement),
        }

        Ok(None)
    }

    fn continue_statement(&mut self, ast: &Ast) -> Result {
        let loop_header = self.find_loop(&ast[0].token).map_err(|outside| {
            if outside {
                FunError::new(FEKind::ContinueOutsideLoop, &ast.token)
            } else {
                FunError::new(FEKind::WrongLabel, &ast.token)
            }
        })?;

        self.context.add_inst(InstEnt::new(
            IKind::Jump(loop_header.start_block, vec![]),
            None,
            &ast.token,
        ));

        Ok(())
    }

    fn break_statement(&mut self, ast: &Ast) -> Result {
        let loop_header = self.find_loop(&ast[0].token).map_err(|outside| {
            if outside {
                FunError::new(FEKind::BreakOutsideLoop, &ast.token)
            } else {
                FunError::new(FEKind::WrongLabel, &ast.token)
            }
        })?;

        if ast[1].kind != AKind::None {
            let return_value = self.expr(&ast[1])?;
            let current_value = self.context[loop_header.end_block]
                .kind
                .block()
                .args
                .first()
                .cloned();
            if let Some(current_value) = current_value {
                self.may_infer(return_value, current_value, &ast[1].token)?;
            } else {
                let ty = self.context[return_value].ty;
                let value = self.new_temp_value(ty);
                self.context[loop_header.end_block]
                    .kind
                    .block_mut()
                    .args
                    .push(value);
            }

            self.context.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, vec![return_value]),
                None,
                &ast.token,
            ));
        } else {
            self.context.add_inst(InstEnt::new(
                IKind::Jump(loop_header.end_block, vec![]),
                None,
                &ast.token,
            ));
        }

        Ok(())
    }

    fn return_statement(&mut self, ast: &Ast) -> Result {
        let ty = self.context.return_type;

        let value = if ast[0].kind == AKind::None {
            if let Some(ty) = ty {
                let temp_value = self.new_temp_value(ty);
                self.context
                    .add_inst(InstEnt::new(IKind::ZeroValue, Some(temp_value), &ast.token));
                Some(self.return_value(temp_value, &ast.token))
            } else {
                None
            }
        } else {
            let ty = ty
                .ok_or_else(|| FunError::new(FEKind::UnexpectedReturnValue, &ast[0].token))?;
            let value = self.expr(&ast[0])?;
            let actual_type = self.context[value].ty;
            if self.is_auto(actual_type) {
                self.infer(value, ty)?;
            } else {
                self.assert_type(actual_type, ty, &ast[0].token)?;
            }

            Some(self.return_value(value, &ast.token))
        };

        self.context
            .add_inst(InstEnt::new(IKind::Return(value), None, &ast.token));

        Ok(())
    }

    fn var_statement(&mut self, statement: &Ast) -> Result {
        let mutable = statement.kind == AKind::VarStatement(true);

        for var_line in statement.iter() {
            let ty = if var_line[1].kind == AKind::None {
                self.auto()
            } else {
                match self.resolve_type(&var_line[1]) {
                    Ok(ty) => ty,
                    Err(FunError {
                        kind: FEKind::TypeError(TEKind::WrongInstantiationArgAmount(0, _)),
                        ..
                    }) => self.auto(),
                    Err(err) => return Err(err),
                }
            };

            if var_line[2].kind == AKind::None {
                for name in var_line[0].iter() {
                    let name = ID(0).add(name.token.spam.deref());

                    let temp_value = self
                        .context
                        .function_body
                        .values
                        .add(ValueEnt::temp(ty));

                    let inst = self.context.add_inst(InstEnt::new(
                        IKind::ZeroValue,
                        Some(temp_value),
                        &var_line.token,
                    ));

                    let var = self.add_variable(name, ty, mutable);

                    if self.is_auto(ty) {
                        self.add_type_dependency(var, inst);
                    }

                    self.context.add_inst(InstEnt::new(
                        IKind::VarDecl(temp_value),
                        Some(var),
                        &var_line.token,
                    ));
                }
            } else {
                for (name, raw_value) in var_line[0].iter().zip(var_line[2].iter()) {
                    let name = ID(0).add(name.token.spam.deref());
                    let value = self.expr(raw_value)?;
                    let mut actual_datatype = self.context[value].ty;

                    let unresolved = if self.is_auto(ty) {
                        self.is_auto(actual_datatype)
                    } else {
                        if self.is_auto(actual_datatype) {
                            actual_datatype = ty;
                            self.infer(value, ty)?;
                        } else {
                            self.assert_type(actual_datatype, ty, &raw_value.token)?;
                        }
                        false
                    };

                    let var = self.add_variable(name, actual_datatype, mutable);

                    let inst = self.context.add_inst(InstEnt::new(
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

    fn expr(&mut self, ast: &Ast) -> Result<Value> {
        self.expr_low(ast)?.ok_or_else(|| panic!("")) //FunError::new(FEKind::ExpectedValue, &ast.token))
    }

    fn expr_low(&mut self, ast: &Ast) -> ExprResult {
        match ast.kind {
            AKind::BinaryOp => self.binary_op(ast),
            AKind::Lit => self.lit(ast),
            AKind::Ident => self.ident(ast),
            AKind::Call(_) => self.call(ast),
            AKind::IfExpr => self.if_expr(ast),
            AKind::Loop => self.loop_expr(ast),
            AKind::DotExpr => self.dot_expr(ast),
            AKind::Deref => self.deref_expr(ast),
            AKind::Ref(_) => self.ref_expr(ast),
            AKind::UnaryOp => self.unary_op(ast),
            AKind::Pass => Ok(None),
            _ => todo!("unmatched expr ast {}", ast),
        }
    }

    fn ref_expr(&mut self, ast: &Ast) -> ExprResult {
        let mutable = ast.kind == AKind::Ref(true);
        let value = self.expr(&ast[0])?;

        if !self.context[value].mutable && mutable {
            return Err(FunError::new(FEKind::MutableRefOfImmutable, &ast.token));
        }

        let reference = self.ref_expr_low(value, mutable, &ast.token);

        Ok(Some(reference))
    }

    fn ref_expr_low(&mut self, value: Value, mutable: bool, token: &Token) -> Value {
        let ty = self.context[value].ty;
        let inst = self.inst_of(value);
        let unresolved = self.is_auto(ty);
        let ty = self.pointer_of(ty, mutable);
        let reference = self.new_temp_value(ty);
        let inst = self.context.add_inst_under(
            InstEnt::new(IKind::Ref(value), Some(reference), token),
            inst,
        );

        // we need to allocate it since register cannot be referenced
        let mut current = reference;
        loop {
            let value = &mut self.context[current];
            if value.on_stack {
                break;
            }
            value.on_stack = true;

            if let Some(inst) = value.inst {
                match &self.context[inst].kind {
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

    fn deref_expr(&mut self, ast: &Ast) -> ExprResult {
        let expr = self.expr(&ast[0])?;

        let value = self.deref_expr_low(expr, &ast.token)?;

        Ok(Some(value))
    }

    fn deref_expr_low(&mut self, value: Value, token: &Token) -> Result<Value> {
        let ty = self.context[value].ty;
        let inst = self.inst_of(value);
        let (pointed, mutable) = self.base_of_err(ty, token)?;

        let val = self.new_anonymous_value(pointed, mutable);
        self.context[val].mutable = mutable;
        let inst = self
            .context
            .add_inst_under(InstEnt::new(IKind::Deref(value), Some(val), token), inst);

        if self.is_auto(pointed) {
            self.add_type_dependency(value, inst);
        }

        Ok(val)
    }

    fn unary_op(&mut self, ast: &Ast) -> ExprResult {
        let name = FUN_SALT.add(ast[0].token.spam.deref());
        let value = self.expr(&ast[1])?;

        self.context.call_value_buffer.push(value);
        self.call_low(name, ast[0].token.spam.raw(), false, &ast.token)
    }

    fn dot_expr(&mut self, ast: &Ast) -> ExprResult {
        let header = self.expr(&ast[0])?;
        let mutable = self.context[header].mutable;
        let field = ID(0).add(ast[1].token.spam.deref());
        let ty = self.context[header].ty;
        if self.is_auto(ty) {
            let value = self.new_anonymous_value(self.auto(), mutable);
            self.pass_mutability(header, value);
            let inst = self.context.add_inst(InstEnt::new(
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
            self.context[value].ty = ty;
            Ok(Some(value))
        }
    }

    fn find_field(&mut self, ty: Type, field_name: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = std::mem::take(&mut self.context.type_frontier);
        frontier.clear();

        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            match &self.state[frontier[i].2].kind {
                TKind::Structure(structure) => {
                    for (j, field) in structure.fields.iter().enumerate() {
                        if field.name == field_name {
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

        self.context.type_frontier = frontier;

        false
    }

    fn loop_expr(&mut self, ast: &Ast) -> ExprResult {
        let name = ID(0).add(ast[0].token.spam.deref());

        let start_block = self.context.new_block();
        let end_block = self.context.new_block();

        let header = Loop {
            name,
            start_block,
            end_block,
        };

        self.context.add_inst(InstEnt::new(
            IKind::Jump(start_block, vec![]),
            None,
            &ast.token,
        ));

        self.context.loops.push(header);
        self.context.make_block_current(start_block);
        self.block(&ast[1])?;
        self.context
            .loops
            .pop()
            .expect("expected previously pushed header");

        if self.context.current_block.is_some() {
            self.context.add_inst(InstEnt::new(
                IKind::Jump(start_block, vec![]),
                None,
                &ast.token,
            ));
        }
        self.context.make_block_current(end_block);

        let value = if self.context[end_block].kind.block().args.is_empty() {
            None
        } else {
            Some(self.context[end_block].kind.block().args[0])
        };

        Ok(value)
    }

    fn if_expr(&mut self, ast: &Ast) -> ExprResult {
        let cond_expr = &ast[0];
        let cond_val = self.expr(cond_expr)?;
        let cond_type = self.context[cond_val].ty;

        let then_block = self.context.new_block();
        self.context.add_inst(InstEnt::new(
            IKind::JumpIfTrue(cond_val, then_block, vec![]),
            None,
            &cond_expr.token,
        ));

        if self.is_auto(cond_type) {
            self.infer(cond_val, self.state.builtin_repo.bool)?;
        } else {
            self.assert_type(cond_type, self.state.builtin_repo.bool, &cond_expr.token)?;
        }

        let merge_block = self.context.new_block();

        let else_branch = &ast[2];
        let else_block = if else_branch.kind == AKind::None {
            self.context.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![]),
                None,
                &else_branch.token,
            ));
            None
        } else {
            let some_block = self.context.new_block();
            self.context.add_inst(InstEnt::new(
                IKind::Jump(some_block, vec![]),
                None,
                &else_branch.token,
            ));
            Some(some_block)
        };

        /*if let Some((_, loop_block, ..)) = self.loop_headers.last() {
            if loop_block.to_owned() != builder.current_block().unwrap() {
                builder.seal_current_block();
            }
        } else {
            builder.seal_current_block();
        }*/

        self.context.make_block_current(then_block);

        let then_branch = &ast[1];

        let then_result = self.block(then_branch)?;

        let mut result = None;
        let mut then_filled = false;
        if let Some(val) = then_result {
            if else_block.is_none() {
                return Err(FunError::new(FEKind::MissingElseBranch, &ast.token));
            }

            self.context.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![val]),
                None,
                &ast.token,
            ));

            let ty = self.context[val].ty;
            let value = self.new_temp_value(ty);
            self.context[merge_block].kind.block_mut().args.push(value);
            result = Some(value);
        } else if self.context.current_block.is_some() {
            self.context.add_inst(InstEnt::new(
                IKind::Jump(merge_block, vec![]),
                None,
                &ast.token,
            ));
        } else {
            then_filled = true;
        }

        if else_branch.kind == AKind::Group {
            let else_block = else_block.unwrap();
            self.context.make_block_current(else_block);
            let else_result = self.block(else_branch)?;

            if let Some(val) = else_result {
                let value_token = &else_branch.last().unwrap().token;
                if let Some(result) = result {
                    self.may_infer(val, result, &value_token)?;
                    self.context.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![val]),
                        None,
                        value_token,
                    ));
                } else if then_filled {
                    self.context.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![val]),
                        None,
                        value_token,
                    ));

                    let ty = self.context[val].ty;
                    let value = self.new_temp_value(ty);
                    self.context[merge_block].kind.block_mut().args.push(value);
                    result = Some(value);
                } else {
                    return Err(FunError::new(FEKind::UnexpectedValue, &ast.token));
                }
            } else {
                if self.context.current_block.is_some() {
                    if result.is_some() {
                        return Err(FunError::new(FEKind::ExpectedValue, &ast.token));
                    }
                    self.context.add_inst(InstEnt::new(
                        IKind::Jump(merge_block, vec![]),
                        None,
                        &ast.token,
                    ));
                }
            }
        }

        self.context.make_block_current(merge_block);

        Ok(result)
    }

    fn call(&mut self, ast: &Ast) -> ExprResult {
        let (base_name, name) = match ast[0].kind {
            AKind::Ident => (
                FUN_SALT.add(ast[0].token.spam.deref()),
                ast[0].token.spam.raw(),
            ),
            AKind::Instantiation => {
                self.context.generic.inferred.resize(ast[0].len() - 1, None);
                for (i, arg) in ast[0][1..].iter().enumerate() {
                    let id = self.resolve_type(arg)?;
                    self.context.generic.inferred[i] = Some(id);
                }
                (
                    FUN_SALT.add(ast[0][0].token.spam.deref()),
                    ast[0][0].token.spam.raw(),
                )
            }
            _ => unreachable!(),
        };
        for value in ast[1..].iter() {
            let value = self.expr(value)?;
            self.context.call_value_buffer.push(value);
        }

        self.call_low(base_name, name, ast.kind == AKind::Call(true), &ast.token)
    }

    fn call_low(
        &mut self,
        base_name: ID,
        name: &'static str,
        dot_call: bool,
        token: &Token,
    ) -> ExprResult {
        let mut values = self.context.call_value_buffer.clone();
        let mut unresolved = std::mem::take(&mut self.context.call_value_buffer);
        unresolved.retain(|f| self.is_auto(self.context[*f].ty));

        let value = if unresolved.len() > 0 {
            let value = self.auto();
            let value = self.new_temp_value(value);
            let inst = self.context.add_inst(InstEnt::new(
                IKind::UnresolvedCall(base_name, name, dot_call, values),
                Some(value),
                token,
            ));
            unresolved
                .drain(..)
                .for_each(|v| self.add_type_dependency(v, inst));
            self.context.unresolved_functions.push(inst);
            self.context.call_value_buffer = unresolved;
            Some(value)
        } else {
            self.context.call_value_buffer = unresolved;
            let fun =
                self.smart_find_or_instantiate(base_name, name, &mut values, dot_call, token)?;
            let sig = self.state[fun].signature();
            let struct_return = sig.struct_return;
            let return_type = sig.return_type;

            let value = return_type.map(|t| {
                let value = self.new_anonymous_value(t, struct_return);
                if struct_return {
                    values.push(value);
                }
                value
            });

            self.context
                .add_inst(InstEnt::new(IKind::Call(fun, values), value, token));
            value
        };

        self.context.call_value_buffer.clear();

        Ok(value)
    }

    fn ident(&mut self, ast: &Ast) -> ExprResult {
        let name = ID(0).add(ast.token.spam.deref());
        self.context
            .find_variable(name)
            .ok_or_else(|| FunError::new(FEKind::UndefinedVariable, &ast.token))
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
            LTKind::String(_) => self.pointer_of(self.state.builtin_repo.u8, false),
            _ => unreachable!("{}", ast),
        };

        let value = self.new_temp_value(ty);

        self.context.add_inst(InstEnt::new(
            IKind::Lit(ast.token.kind.clone()),
            Some(value),
            &ast.token,
        ));

        Ok(Some(value))
    }

    fn binary_op(&mut self, ast: &Ast) -> ExprResult {
        match ast[0].token.spam.deref() {
            "=" => return self.assignment(ast),
            "as" => return self.bit_cast(ast),
            _ => (),
        }

        let left = self.expr(&ast[1])?;
        let right = self.expr(&ast[2])?;

        let base_id = FUN_SALT.add(ast[0].token.spam.deref());

        self.context.call_value_buffer.extend(&[left, right]);

        self.call_low(base_id, ast[0].token.spam.raw(), false, &ast.token)
    }

    fn bit_cast(&mut self, ast: &Ast) -> ExprResult {
        let target = self.expr(&ast[1])?;
        let ty = self.resolve_type(&ast[2])?;

        let original_datatype = self.context[target].ty;
        let original_size = self.state[original_datatype].size;
        let datatype_size = self.state[ty].size;

        if original_size != datatype_size {
            return Err(FunError::new(
                FEKind::InvalidBitCast(original_size, datatype_size),
                &ast.token,
            ));
        }

        let value = self.new_anonymous_value(ty, self.context[target].mutable);
        self.context
            .add_inst(InstEnt::new(IKind::Cast(target), Some(value), &ast.token));

        Ok(Some(value))
    }

    fn may_infer(&mut self, a: Value, b: Value, token: &Token) -> Result<bool> {
        let a_type = self.context[a].ty;
        let b_type = self.context[b].ty;
        Ok(if self.is_auto(a_type) {
            if !self.is_auto(b_type) {
                self.infer(a, b_type)?;
                true
            } else {
                false
            }
        } else {
            if self.is_auto(b_type) {
                self.infer(b, a_type)?;
            } else {
                self.assert_type(a_type, b_type, token)?;
            }
            true
        })
    }

    fn infer(&mut self, value: Value, ty: Type) -> Result<()> {
        let mut frontier = std::mem::take(&mut self.context.graph_frontier);
        frontier.clear();
        frontier.push((value, ty));

        while let Some((value, ty)) = frontier.pop() {
            let val = &mut self.context[value];
            val.ty = ty;
            let dependency_id = if let Some(dep) = val.type_dependency {
                val.type_dependency = None;
                dep
            } else {
                continue;
            };

            if let Some(inst) = val.inst {
                match self.context[inst].kind {
                    IKind::Ref(value) => match self.state[ty].kind {
                        TKind::Pointer(inner, _) => {
                            frontier.push((value, inner));
                        }
                        _ => unreachable!(),
                    },
                    IKind::Deref(value) => {
                        let mutable = matches!(
                            self.state[self.context[value].ty].kind,
                            TKind::Pointer(_, true)
                        );
                        frontier.push((value, self.pointer_of(ty, mutable)));
                    }
                    IKind::VarDecl(value) => {
                        frontier.push((value, ty));
                    }
                    _ => (),
                }
            }

            let mut dependencies = std::mem::take(&mut self.context[dependency_id]);
            for dep in dependencies.drain(..).skip(1)
            /* first is null marker */
            {
                let inst = &mut self.context[dep];
                inst.unresolved -= 1;
                if inst.unresolved != 0 {
                    continue;
                }

                let token = inst.token_hint.clone();
                match &mut inst.kind {
                    IKind::VarDecl(_) => {
                        let value = inst.value.unwrap();
                        frontier.push((value, ty));
                    }
                    IKind::UnresolvedCall(..) => {
                        self.infer_call(dep, &mut frontier)?;
                    }
                    IKind::ZeroValue => {
                        let value = inst.value.unwrap();
                        self.context[value].ty = ty;
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
                        self.context.function_body.insts.remove(dep);
                        let ty = self.field_access(header, field, value, &token)?;
                        frontier.push((value, ty));
                    }
                    IKind::Ref(value) => {
                        let val = inst.value.unwrap();
                        let value = *value;
                        let value_datatype = self.context[value].ty;
                        let mutable =
                            matches!(self.state[value_datatype].kind, TKind::Pointer(_, true));
                        let ty = self.pointer_of(value_datatype, mutable);
                        frontier.push((val, ty));
                    }
                    IKind::Deref(value) => {
                        let value = *value;
                        let val = inst.value.unwrap();
                        let value_datatype = self.context[value].ty;
                        let ty = match self.state[value_datatype].kind {
                            TKind::Pointer(inner, _) => inner,
                            _ => unreachable!(),
                        };
                        frontier.push((val, ty));
                    }
                    IKind::NoOp | IKind::Call(..) => (),
                    _ => todo!("{:?}", inst),
                }
            }

            self.context[dependency_id] = dependencies;
        }

        self.context.graph_frontier = frontier;

        Ok(())
    }

    fn infer_call(&mut self, inst: Inst, frontier: &mut Vec<(Value, Type)>) -> Result {
        let (name, dot_expr, base_id, mut args) = match std::mem::take(&mut self.context[inst].kind)
        {
            IKind::UnresolvedCall(base_id, name, dot_expr, args) => (name, dot_expr, base_id, args),
            _ => unreachable!(),
        };

        let token = self.context[inst].token_hint.clone();

        let fun = self.smart_find_or_instantiate(base_id, name, &mut args, dot_expr, &token)?;

        if self.context[inst].unresolved != 0 {
            let mut types = std::mem::take(&mut self.context.type_buffer);
            types.clear();
            types.extend(
                self.state[fun]
                    .signature()
                    .args
                    .iter()
                    .map(|arg| arg.ty),
            );
            for (&ty, &value) in types.iter().zip(args.iter()) {
                if self.is_auto(self.context[value].ty) {
                    frontier.push((value, ty));
                }
            }
            self.context.type_buffer = types;
        }

        let value = self.context[inst].value;
        let sig = self.state[fun].signature();
        let struct_return = sig.struct_return;
        let ty = sig.return_type;

        if let (Some(value), Some(ty)) = (value, ty) {
            if struct_return {
                self.context[value].mutable = true;
                args.push(value);
            }
            frontier.push((value, ty));
        } else if let Some(dependency) = self.context[value.unwrap()].type_dependency {
            if self.context[dependency].len() > 1 {
                return Err(FunError::new(FEKind::ExpectedValue, &token));
            }
            self.context[dependency].clear();
            self.context[inst].value = None;
        }

        self.context[inst].kind = IKind::Call(fun, args);

        Ok(())
    }

    fn field_access(
        &mut self,
        mut header: Value,
        field: ID,
        value: Value,
        token: &Token,
    ) -> Result<Type> {
        let mutable = self.context[header].mutable;
        let header_datatype = self.context[header].ty;
        let mut path = vec![];
        if !self.find_field(header_datatype, field, &mut path) {
            return Err(FunError::new(FEKind::UnknownField(header_datatype), token));
        }

        let mut offset = 0;
        let mut current_type = header_datatype;
        for &i in path.iter().rev() {
            match &self.state[current_type].kind {
                TKind::Structure(structure) => {
                    let field = &structure.fields[i];
                    offset += field.offset;
                    current_type = field.ty;
                }
                TKind::Pointer(pointed, _) => {
                    let pointed = *pointed;
                    let prev_inst = self.inst_of(header);
                    let value = self.new_anonymous_value(current_type, mutable);
                    self.context[value].offset = offset;
                    let prev_inst = self.context.add_inst_under(
                        InstEnt::new(IKind::Offset(header), Some(value), &token),
                        prev_inst,
                    );
                    let loaded = self.new_anonymous_value(pointed, mutable);
                    self.context[loaded].mutable = mutable;
                    self.context.add_inst_under(
                        InstEnt::new(IKind::Deref(value), Some(loaded), &token),
                        prev_inst,
                    );
                    offset = 0;
                    current_type = pointed;
                    header = loaded;
                }
                _ => todo!("{:?}", self.state[current_type]),
            }
        }

        let inst = self.inst_of(header);
        let inst = self.context.add_inst_under(
            InstEnt::new(IKind::Offset(header), Some(value), token),
            inst,
        );

        let val = &mut self.context[value];
        val.inst = Some(inst);
        val.offset = offset;
        val.ty = current_type;

        Ok(current_type)
    }

    fn inst_of(&mut self, value: Value) -> Inst {
        // if inst is none then this is function parameter and its safe to put it
        // at the beginning of the entry block
        self.context[value]
            .inst
            .unwrap_or(self.context.function_body.insts.first().unwrap())
    }

    pub fn add_variable(&mut self, name: ID, ty: Type, mutable: bool) -> Value {
        let val = self.new_value(name, ty, mutable);
        self.context.variables.push(Some(val));
        val
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
            let dep = self.context.new_type_dependency();
            value.type_dependency = Some(dep);
        }
        self.context.function_body.values.add(value)
    }

    fn assignment(&mut self, ast: &Ast) -> ExprResult {
        let target = self.expr(&ast[1])?;
        let value = self.expr(&ast[2])?;
        let target_datatype = self.context[target].ty;
        let value_datatype = self.context[value].ty;

        if !self.context[target].mutable {
            return Err(FunError::new(FEKind::AssignToImmutable, &ast.token));
        }

        let unresolved = if self.is_auto(target_datatype) {
            if !self.is_auto(value_datatype) {
                self.infer(target, value_datatype)?;
                false
            } else {
                true
            }
        } else {
            if self.is_auto(value_datatype) {
                self.infer(value, target_datatype)?;
            } else {
                self.assert_type(value_datatype, target_datatype, &ast.token)?;
            }
            false
        };

        let inst =
            self.context
                .add_inst(InstEnt::new(IKind::Assign(target), Some(value), &ast.token));

        if unresolved {
            self.add_type_dependency(value, inst);
            self.add_type_dependency(target, inst);
        }

        Ok(Some(value))
    }

    fn smart_find_or_instantiate(
        &mut self,
        base: ID,
        name: &str,
        args: &mut [Value],
        dot_expr: bool,
        token: &Token,
    ) -> Result<Fun> {
        let mut types = std::mem::take(&mut self.context.type_buffer);
        types.clear();
        types.extend(args.iter().map(|v| self.context[*v].ty));

        let result = if dot_expr {
            let first_mutable = self.context[args[0]].mutable;
            assert!(self.context.current_module.is_some());
            let (fun, id, kind) =
                self.dot_find_or_instantiate(base, name, &mut types, first_mutable, &token)?;
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
            self.find_or_instantiate(base, name, &types, &token)
        };

        self.context.type_buffer = types;

        result
    }

    fn dot_find_or_instantiate(
        &mut self,
        base: ID,
        name: &str,
        values: &mut [Type],
        first_mutable: bool,
        token: &Token,
    ) -> Result<(Fun, ID, DotInstr)> {
        let mut frontier = std::mem::take(&mut self.context.embed_frontier);
        frontier.clear();
        frontier.push((values[0], ID(0)));

        let mut final_err = None;

        macro_rules! unwrap {
            ($expr:expr, $id:expr, $type:ident) => {
                match $expr {
                    Ok(expr) => return Ok((expr, $id, DotInstr::$type)),
                    #[allow(unused_assignments)]
                    Err(err) => {
                        if let FunError {
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
                self.find_or_instantiate(base, name, values, token),
                id,
                None
            );
            if self.is_pointer(ty) {
                values[0] = self.base_of(ty).unwrap().0;
                unwrap!(
                    self.find_or_instantiate(base, name, values, token),
                    id,
                    Deref
                );
            } else {
                if first_mutable {
                    values[0] = self.pointer_of(ty, true);
                    unwrap!(
                        self.find_or_instantiate(base, name, values, token),
                        id,
                        MutRef
                    );
                }

                values[0] = self.pointer_of(ty, false);
                assert!(self.context.current_module.is_some());
                unwrap!(self.find_or_instantiate(base, name, values, token), id, Ref);
            }

            match &self.state[ty].kind {
                TKind::Structure(structure) => {
                    for field in structure.fields.iter().filter(|f| f.embedded) {
                        frontier.push((field.ty, field.name));
                    }
                }
                _ => (),
            }

            i += 1;
        }

        Err(final_err.unwrap())
    }

    fn find_or_instantiate(
        &mut self,
        base: ID,
        name: &str,
        values: &[Type],
        token: &Token,
    ) -> Result<Fun> {
        let specific_id = values.iter().fold(base, |base, &val| {
            base.combine(self.state.types.direct_to_id(val))
        });
        assert!(self.context.current_module.is_some());
        if let Some((_, fun)) = self.find_by_name(self.context.current_module.unwrap(), specific_id)
        {
            return Ok(fun);
        }

        if let Some((module, functions)) = self.find_generic_by_name(base) {
            let len = self.state.generic_functions[functions].len();
            for fun in 0..len {
                if let Some(fun) = self.instantiate(module, functions, fun, values)? {
                    return Ok(fun);
                }
            }
        }

        Err(FunError::new(
            FEKind::FunctionNotFound(name.to_string(), values.to_vec()),
            token,
        ))
    }

    fn instantiate(
        &mut self,
        module: Mod,
        functions: Fun,
        index: usize,
        values: &[Type],
    ) -> Result<Option<Fun>> {
        let mut generic = std::mem::take(&mut self.context.generic);

        let fun = &self.state.generic_functions[functions][index];

        let signature = match &fun.kind {
            FKind::Generic(signature) => signature,
            _ => unreachable!("{:?}", fun.kind),
        };

        if signature.arg_count != values.len() {
            return Ok(None);
        }

        generic.inferred.resize(signature.params.len(), None);

        let mut i = 0;
        let mut n = 0;
        while i < signature.return_index {
            let (count, length) = if let GenericElement::NextArgument(count, length) =
                signature.elements[i].clone()
            {
                (count, length)
            } else {
                unreachable!("{:?}", signature.elements[i]);
            };

            for j in 0..count {
                let ty = values[n + j];
                generic.arg_buffer.clear();
                self.load_arg_from_datatype(ty, &mut generic);
                let pattern = &signature.elements[i + 1..i + length + 1];

                for (real, pat) in generic.arg_buffer.iter().zip(pattern) {
                    if !real.compare(pat) {
                        match pat {
                            GenericElement::Parameter(param) => match real {
                                GenericElement::Element(_, id) => {
                                    if let Some(already) = generic.inferred[*param] {
                                        if Some(already) != *id {
                                            return Ok(None);
                                        }
                                    } else if !self.is_auto(id.unwrap()) {
                                        generic.inferred[*param] = *id;
                                    }
                                }
                                _ => return Ok(None),
                            },
                            GenericElement::Element(..) => match real {
                                GenericElement::Element(_, id) => {
                                    if id.unwrap() != self.state.builtin_repo.auto {
                                        return Ok(None);
                                    }
                                }
                                _ => return Ok(None),
                            },
                            _ => return Ok(None),
                        }
                    }
                }
            }

            i += length + 1;
            n += 1;
        }

        generic.param_buffer.clear();
        generic.param_buffer.extend(&signature.params);

        let module_id = self.state[module].id;

        let old_len = self.context.type_resolver_context.shadowed_types.len();
        let old_id_len = self.context.type_resolver_context.instance_id_buffer.len();

        for (&name, &ty) in generic.param_buffer.iter().zip(generic.inferred.iter()) {
            let ty = match ty {
                Some(id) => id,
                None => return Ok(None),
            };
            let id = name.combine(module_id);
            if let Some(shadowed) = self.state.types.link(id, ty) {
                self.context
                    .type_resolver_context
                    .shadowed_types
                    .push(shadowed);
            } else {
                self.context
                    .type_resolver_context
                    .instance_id_buffer
                    .push(id);
            }
        }

        generic.inferred.clear();

        self.context.generic = generic;

        let old_dependency_len = if Some(module) != self.context.current_module {
            let current = self.context.current_module.unwrap();
            // SAFETY: the current module and targeted are not the same at this point
            let (target_module, source_module) = unsafe {
                (
                    std::mem::transmute::<_, &mut ModuleEnt>(&mut self.state[module]),
                    &self.state[current],
                )
            };
            let len = target_module.dependency.len();
            target_module
                .dependency
                .extend(source_module.dependency.iter());
            len
        } else {
            self.state[module].dependency.len()
        };

        let fun = &self.state.generic_functions[functions][index];
        let (ast_ref, name, debug_name, vis, attr_id) = (
            fun.ast,
            fun.name,
            fun.debug_name,
            fun.visibility,
            fun.attribute_id,
        );
        let fun = {
            // SAFETY: the function_ast has same live-time as self ans scope ensures
            // the reference does not escape
            let ast = unsafe { self.context.function_ast.get(ast_ref) };
            let id = self.id_of_ast_signature(module, name, &ast[0])?;
            if let Some(fun) = self.state.functions.id_to_direct(id) {
                fun
            } else {
                self.context.dive();
                let fun = self.collect_normal_function(
                    module, ast_ref, ast, name, debug_name, vis, attr_id,
                )?;
                self.function(fun)?;
                self.context.bail();
                fun
            }
        };
        self.state[module].dependency.truncate(old_dependency_len);

        for i in old_id_len..self.context.type_resolver_context.instance_id_buffer.len() {
            self.state.types.remove_link(
                self.context.type_resolver_context.instance_id_buffer[i],
                None,
            );
        }
        self.context
            .type_resolver_context
            .instance_id_buffer
            .truncate(old_id_len);

        for i in old_len..self.context.type_resolver_context.shadowed_types.len() {
            let direct_id = self.context.type_resolver_context.shadowed_types[i];
            let id = self.state.types.direct_to_id(direct_id);
            self.state.types.remove_link(id, Some(direct_id));
        }
        self.context
            .type_resolver_context
            .shadowed_types
            .truncate(old_len);

        Ok(Some(fun))
    }

    fn find_by_name(&mut self, module: Mod, name: ID) -> Option<(Mod, Fun)> {
        self.state.walk_accessible_scopes(module, |id, module| {
            self.state
                .functions
                .id_to_direct(name.combine(id))
                .map(|fun| (module, fun))
        })
    }

    fn find_generic_by_name(&mut self, name: ID) -> Option<(Mod, Fun)> {
        self.state
            .walk_accessible_scopes(self.context.current_module.unwrap(), |id, module| {
                self.state
                    .generic_functions
                    .id_to_direct(name.combine(id))
                    .map(|fun| (module, fun))
            })
    }

    fn assert_type(&self, actual: Type, expected: Type, token: &Token) -> Result {
        if actual == expected {
            Ok(())
        } else {
            Err(FunError::new(FEKind::TypeMismatch(actual, expected), token))
        }
    }

    fn add_type_dependency(&mut self, value: Value, inst: Inst) {
        self.context[inst].unresolved += 1;
        let dependency_id = self.context[value].type_dependency.unwrap();
        self.context[dependency_id].push(inst);
    }

    fn collect(&mut self) -> Result {
        let mut collected_ast = List::new();

        for module in unsafe { self.state.modules.direct_ids() } {
            if !self.state.modules.is_direct_valid(module) {
                continue;
            }

            self.context.current_module = Some(module);

            let mut ast = std::mem::take(&mut self.state.modules[module].ast);
            for (i, a) in ast.iter_mut().enumerate() {
                match a.kind.clone() {
                    AKind::Fun(visibility) => {
                        let a_ref = collected_ast.add(std::mem::take(a));
                        let a = &collected_ast[a_ref];
                        let header = &a[0];
                        match header[0].kind {
                            AKind::Ident => {
                                let debug_name = header[0].token.spam.raw();
                                let name = FUN_SALT.add(debug_name);
                                self.collect_normal_function(
                                    module, a_ref, a, name, debug_name, visibility, i,
                                )?;
                            }
                            AKind::Instantiation => {
                                self.collect_generic_function(module, a_ref, a, visibility, i)?;
                            }
                            _ => unreachable!("{}", a),
                        }
                    }
                    _ => (),
                }
            }
            self.state.modules[module].ast = ast;
        }

        self.context.function_ast = LockedList::new(collected_ast);

        Ok(())
    }

    fn collect_generic_function(
        &mut self,
        module: Mod,
        a_ref: AstRef,
        a: &Ast,
        visibility: Vis,
        attribute_id: usize,
    ) -> Result<Fun> {
        let debug_name = a[0][0][0].token.spam.raw();
        let name = FUN_SALT.add(debug_name);

        let signature = self.generic_signature(&a[0])?;

        let function = FunEnt {
            visibility,
            name,
            module,
            token_hint: a[0].token.clone(),
            kind: FKind::Generic(signature),
            ast: a_ref,
            attribute_id,
            debug_name,
            import: false,
            body: Default::default(),
            final_signature: None,
            object_id: None,
        };

        let name = name.combine(self.state.modules.direct_to_id(module));

        self.state
            .generic_functions
            .get_mut_or(name, vec![])
            .push(function);

        Ok(self.state.generic_functions.id_to_direct(name).unwrap())
    }

    fn id_of_ast_signature(&mut self, module: Mod, base_name: ID, ast: &Ast) -> Result<ID> {
        let mut name = base_name;
        for param_line in &ast[1..ast.len() - 1] {
            let raw_datatype = param_line.last().unwrap();
            let ty = self.resolve_type_low(module, raw_datatype)?;
            for _ in 0..param_line.len() - 1 {
                name = name.combine(self.state.types.direct_to_id(ty));
            }
        }

        Ok(name.combine(self.state.modules.direct_to_id(module)))
    }

    fn collect_normal_function(
        &mut self,
        module: Mod,
        a_ref: AstRef,
        a: &Ast,
        mut name: ID,
        debug_name: &'static str,
        visibility: Vis,
        attribute_id: usize,
    ) -> Result<Fun> {
        let mut args = vec![];
        let header = &a[0];
        for param_line in &header[1..header.len() - 1] {
            let raw_datatype = param_line.last().unwrap();
            let ty = self.resolve_type_low(module, raw_datatype)?;
            if self.is_auto(ty) {
                return Err(FunError::new(FEKind::UnexpectedAuto, &raw_datatype.token));
            }
            for param in param_line[0..param_line.len() - 1].iter() {
                name = name.combine(self.state.types.direct_to_id(ty));
                let name = ID(0).add(param.token.spam.deref());
                let mutable = param_line.kind == AKind::FunArgument(true);
                args.push(ValueEnt::new(name, ty, mutable));
            }
        }

        let raw_return_type = header.last().unwrap();
        let (return_type, struct_return) = if raw_return_type.kind == AKind::None {
            (None, false)
        } else {
            let return_type = self.resolve_type_low(module, raw_return_type)?;
            if self.is_auto(return_type) {
                return Err(FunError::new(
                    FEKind::UnexpectedAuto,
                    &raw_return_type.token,
                ));
            }
            let struct_return =
                self.state[return_type].size > self.state.isa().pointer_bytes() as u32;
            if struct_return {
                args.push(ValueEnt::new(
                    ID(0),
                    self.pointer_of(return_type, true),
                    false,
                ));
            }
            (Some(return_type), struct_return)
        };

        let function_signature = FunSignature {
            args,
            return_type,
            struct_return,
        };

        let token_hint = header.token.clone();

        let function = FunEnt {
            visibility,
            name,
            module,
            token_hint: token_hint.clone(),
            kind: FKind::Normal(function_signature),
            attribute_id,
            ast: a_ref,
            debug_name,
            import: false,
            body: Default::default(),
            final_signature: None,
            object_id: None,
        };

        name = name.combine(self.state.modules.direct_to_id(module));
        let id = match self.state.functions.insert(name, function) {
            (Some(function), _) => {
                return Err(FunError::new(
                    FEKind::Redefinition(function.token_hint),
                    &token_hint,
                ));
            }
            (_, id) => id,
        };

        Ok(id)
    }

    fn generic_signature(&mut self, ast: &Ast) -> Result<GenericSignature> {
        self.context.generic.param_buffer.clear();
        for ident in &ast[0][1..] {
            self.context
                .generic
                .param_buffer
                .push(TYPE_SALT.add(ident.token.spam.deref()))
        }

        let mut arg_count = 0;
        self.context.generic.arg_buffer.clear();
        for args in &ast[1..ast.len() - 1] {
            let amount = args.len() - 1;
            let idx = self.context.generic.arg_buffer.len();
            self.context
                .generic
                .arg_buffer
                .push(GenericElement::NextArgument(amount, 0));
            self.load_arg(&args[args.len() - 1])?;
            let additional = self.context.generic.arg_buffer.len() - idx - 1;
            self.context.generic.arg_buffer[idx] = GenericElement::NextArgument(amount, additional);
            arg_count += amount;
        }

        let return_index = self.context.generic.arg_buffer.len();

        let has_return = ast[ast.len() - 1].kind != AKind::None;

        self.context
            .generic
            .arg_buffer
            .push(GenericElement::NextReturn(has_return));

        if has_return {
            self.load_arg(&ast[ast.len() - 1])?;
        }

        Ok(GenericSignature {
            params: self.context.generic.param_buffer.clone(),
            elements: self.context.generic.arg_buffer.clone(),
            return_index,
            arg_count,
        })
    }

    fn load_arg_from_datatype(&self, ty: Type, generic: &mut GenericFunContext) {
        let dt = &self.state[ty];

        if dt.params.is_empty() {
            if let TKind::Pointer(pointed, mutable) = dt.kind {
                generic.arg_buffer.push(GenericElement::Pointer(mutable));
                self.load_arg_from_datatype(pointed, generic);
            } else {
                generic
                    .arg_buffer
                    .push(GenericElement::Element(ty, Some(ty)));
            }
            return;
        }

        generic
            .arg_buffer
            .push(GenericElement::Element(dt.params[0], Some(ty)));

        generic.arg_buffer.push(GenericElement::ScopeStart);
        for &param in &dt.params[1..] {
            self.load_arg_from_datatype(param, generic)
        }
        generic.arg_buffer.push(GenericElement::ScopeEnd);
    }

    fn load_arg(&mut self, ast: &Ast) -> Result {
        match &ast.kind {
            AKind::Ident => {
                let id = TYPE_SALT.add(ast.token.spam.deref());
                if let Some(index) = self
                    .context
                    .generic
                    .param_buffer
                    .iter()
                    .position(|&p| p == id)
                {
                    self.context
                        .generic
                        .arg_buffer
                        .push(GenericElement::Parameter(index));
                } else {
                    let ty = self.find_type(&ast.token)?;
                    self.context
                        .generic
                        .arg_buffer
                        .push(GenericElement::Element(ty, None));
                }
            }
            AKind::Instantiation => {
                self.load_arg(&ast[0])?;
                self.context
                    .generic
                    .arg_buffer
                    .push(GenericElement::ScopeStart);
                for a in ast[1..].iter() {
                    self.load_arg(a)?;
                }
                self.context
                    .generic
                    .arg_buffer
                    .push(GenericElement::ScopeEnd);
            }
            &AKind::Ref(mutable) => {
                self.context
                    .generic
                    .arg_buffer
                    .push(GenericElement::Pointer(mutable));

                self.load_arg(&ast[0])?;
            }
            _ => todo!("{}", ast),
        }

        Ok(())
    }

    */
    
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

        self
            .state
            .loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.state.loops.is_empty())
    }

    fn base_of_err(&mut self, ty: Type, token: &Token) -> Result<(Type, bool, bool)> {
        self.base_of(ty)
            .ok_or_else(|| FunError::new(FEKind::NonPointerDereference, token))
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
            .map_err(Into::into)
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
        self.context.body.values[to].mutable = self.context.body.values[from].mutable;
    }
}

#[derive(Debug)]
pub struct FunError {
    pub kind: FEKind,
    pub token: Token,
    pub message: String,
}

impl FunError {
    pub fn new(kind: FEKind, token: &Token) -> Self {
        FunError {
            kind,
            token: token.clone(),
            message: String::new(),
        }
    }
}

#[derive(Debug)]
pub enum FEKind {
    TypeError(TEKind),
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
}

impl Into<FunError> for TypeError {
    fn into(self) -> FunError {
        FunError {
            kind: FEKind::TypeError(self.kind),
            token: self.token,
            message: String::new(),
        }
    }
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
    pub visibility: Vis,
    pub id: ID,
    pub module: Mod,
    pub hint: Token,
    pub kind: FKind,
    pub name: &'static str,
    pub attribute_id: usize,
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
    Builtin(BFun),
    Generic(GFun),
    Normal(NFun),
    Represented(RFun),
}

crate::index_pointer!(NFun);

pub struct NFunEnt {
    pub signature: FunSignature,
    pub ast: GAst,
}

crate::index_pointer!(BFun);

pub struct BFunEnt {
    pub signature: FunSignature,
}

crate::index_pointer!(GFun);

pub struct GFunEnt {
    pub signature: GenericSignature,
    pub ast: GAst,
}

crate::index_pointer!(RFun);

pub struct RFunEnt {
    pub signature: Signature,
    pub object_id: FuncId,
    pub body: FunBody,
}   

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
    Pointer(bool),
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
    pub return_type: Option<Type>,
    pub struct_return: bool,
}

crate::index_pointer!(Inst);

#[derive(Debug, Default, Clone)]
pub struct InstEnt {
    pub kind: IKind,
    pub value: Option<Value>,
    pub token_hint: Token,
    pub unresolved: usize,
}

impl InstEnt {
    pub fn new(kind: IKind, value: Option<Value>, token_hint: &Token) -> Self {
        Self {
            kind,
            value,
            token_hint: token_hint.clone(),
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

#[derive(Debug, Clone)]
pub struct ValueEnt {
    pub name: ID,
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
            name,
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
            name: ID(0),
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

crate::index_pointer!(TypeDep);

pub struct FState {
    pub t_state: TState,
    pub funs: List<Fun, FunEnt>,
    pub nfuns: ReusableList<NFun, NFunEnt>,
    pub gfuns: ReusableList<GFun, GFunEnt>,
    pub bfuns: ReusableList<BFun, BFunEnt>,
    pub rfuns: ReusableList<RFun, RFunEnt>,

    pub loops: Vec<Loop>,
}

crate::inherit!(FState, t_state, TState);

pub struct FContext {
    pub t_context: TContext,
    pub body: FunBody,
}

crate::inherit!(FContext, t_context, TContext);

/*pub fn test() {
    let mut state = FState::default();
    let builder = ModuleTreeBuilder::new(&mut state);
    builder.build("src/ir/tests/module_tree/root").unwrap();

    let mut ctx = TypeResolverContext::default();

    TypeResolver::new(&mut state, &mut ctx).resolve().unwrap();

    let mut ctx = FunResolverContext::default();

    FunResolver::new(&mut state, &mut ctx)
        .resolve()
        .map_err(|e| {
            println!("{}", FunErrorDisplay::new(&state, &e));
            e
        })
        .unwrap();

    for fun in unsafe { state.functions.direct_ids() } {
        if !state.functions.is_direct_valid(fun)
            || !matches!(state.functions[fun].kind, FKind::Normal(_))
        {
            continue;
        }

        let fun = &state.functions[fun];

        println!("{}", fun.token_hint.spam.deref());
        println!();

        for (i, inst) in fun.body.insts.iter() {
            match &inst.kind {
                IKind::Block(block) => {
                    println!("  {}{:?}", i, block.args);
                }
                IKind::BlockEnd(_) => {
                    println!();
                }
                _ => {
                    if let Some(value) = inst.value {
                        let ty =
                            TypePrinter::new(&state).print(fun.body.values[value].ty);
                        println!(
                            "    {:?}: {} = {:?} |{}",
                            value,
                            ty,
                            inst.kind,
                            inst.token_hint.spam.deref()
                        );
                    } else {
                        println!("    {:?} |{}", inst.kind, inst.token_hint.spam.deref());
                    }
                }
            }
        }
    }
}*/
