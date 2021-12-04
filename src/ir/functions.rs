use core::panic;
use std::fmt::Display;
use std::ops::{Deref, DerefMut, Index, IndexMut};

use crate::ast::{AKind, Ast, Vis};
use crate::ir::types::TypePrinter;
use crate::ir::{
    FKind, Fun, FunBody, FunEnt, Inst, LTKind, Mod, ModuleEnt, Type, TypeDep, Value, ValueEnt,
};
use crate::lexer::{Token, TokenView};
use crate::util::storage::LockedList;
use crate::util::{
    sdbm::{SdbmHashState, ID},
    storage::{List, SymID},
};

use super::module_tree::ModuleTreeBuilder;
use super::types::{TEKind, TypeError, TypeResolver, TypeResolverContext};
use super::{
    AstRef, FunSignature, GenericElement, GenericSignature, IKind, InstEnt, Loop, Program, TKind,
    FUN_SALT, TYPE_SALT,
};

type Result<T = ()> = std::result::Result<T, FunError>;
type ExprResult = Result<Option<Value>>;

pub struct FunResolver<'a> {
    program: &'a mut Program,
    context: &'a mut FunResolverContext,
}

impl<'a> FunResolver<'a> {
    pub fn new(program: &'a mut Program, context: &'a mut FunResolverContext) -> Self {
        FunResolver { program, context }
    }

    pub fn resolve(mut self) -> Result {
        self.collect()?;

        self.translate()?;

        Ok(())
    }

    fn translate(&mut self) -> Result {
        for function in unsafe { self.program.functions.direct_ids() } {
            if !self.program.functions.is_direct_valid(function) {
                continue;
            }
            if !matches!(self.program.functions[function].kind, FKind::Normal(_)) {
                continue;
            }
            self.function(function)?;
            self.context.deref_mut().clear();
        }

        Ok(())
    }

    fn function(&mut self, function: Fun) -> Result {
        let fun = &mut self.program.functions[function];

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
            let ast = unsafe { self.context.function_ast.get(self.program[function].ast) };
            self.function_low(module, ast, &signature)?;
        }

        let fun = &mut self.program.functions[function];
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

        let value = self.block(&ast[1])?;

        if let (Some(value), Some(_), Some(return_type)) =
            (value, self.context.current_block, signature.return_type)
        {
            let value_type = self.context[value].datatype;
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
            let datatype = self.context[value_id].datatype;
            let on_stack =
                self.program.types[datatype].size > self.program.isa().pointer_bytes() as u32;
            self.context[value_id].on_stack = self.context[value_id].on_stack || on_stack;
        }

        assert!(self.context.current_module == Some(module));

        let mut frontier = std::mem::take(&mut self.context.second_graph_frontier);
        let mut unresolved = std::mem::take(&mut self.context.unresolved_functions);
        for inst in unresolved.drain(..) {
            match &self.context[inst].kind {
                IKind::UnresolvedCall(..) => {
                    self.infer_call(inst, &mut frontier)?;
                }
                _ => (),
            }

            for (value, datatype) in frontier.drain(..) {
                self.infer(value, datatype)?;
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
                let datatype = self.context[return_value].datatype;
                let value = self.new_temp_value(datatype);
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
        let datatype = self.context.return_type;

        let value = if ast[0].kind == AKind::None {
            if let Some(datatype) = datatype {
                let temp_value = self.new_temp_value(datatype);
                self.context
                    .add_inst(InstEnt::new(IKind::ZeroValue, Some(temp_value), &ast.token));
                Some(self.return_value(temp_value, &ast.token))
            } else {
                None
            }
        } else {
            let datatype = datatype
                .ok_or_else(|| FunError::new(FEKind::UnexpectedReturnValue, &ast[0].token))?;
            let value = self.expr(&ast[0])?;
            let actual_type = self.context[value].datatype;
            if self.is_auto(actual_type) {
                self.infer(value, datatype)?;
            } else {
                self.assert_type(actual_type, datatype, &ast[0].token)?;
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
            let datatype = if var_line[1].kind == AKind::None {
                self.auto()
            } else {
                match self.resolve_type(&var_line[1]) {
                    Ok(datatype) => datatype,
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
                        .add(ValueEnt::temp(datatype));

                    let inst = self.context.add_inst(InstEnt::new(
                        IKind::ZeroValue,
                        Some(temp_value),
                        &var_line.token,
                    ));

                    let var = self.add_variable(name, datatype, mutable);

                    if self.is_auto(datatype) {
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
                    let mut actual_datatype = self.context[value].datatype;

                    let unresolved = if self.is_auto(datatype) {
                        self.is_auto(actual_datatype)
                    } else {
                        if self.is_auto(actual_datatype) {
                            actual_datatype = datatype;
                            self.infer(value, datatype)?;
                        } else {
                            self.assert_type(actual_datatype, datatype, &raw_value.token)?;
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
        let datatype = self.context[value].datatype;
        let inst = self.inst_of(value);
        let unresolved = self.is_auto(datatype);
        let datatype = self.pointer_of(datatype, mutable);
        let reference = self.new_temp_value(datatype);
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
        let datatype = self.context[value].datatype;
        let inst = self.inst_of(value);
        let (pointed, mutable) = self.base_of_err(datatype, token)?;

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
        let datatype = self.context[header].datatype;
        if self.is_auto(datatype) {
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
            let value = self.new_anonymous_value(self.program.builtin_repo.bool, mutable);
            let datatype = self.field_access(header, field, value, &ast.token)?;
            self.context[value].datatype = datatype;
            Ok(Some(value))
        }
    }

    fn find_field(&mut self, datatype: Type, field_name: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = std::mem::take(&mut self.context.type_frontier);
        frontier.clear();

        frontier.push((usize::MAX, 0, datatype));

        let mut i = 0;
        while i < frontier.len() {
            match &self.program[frontier[i].2].kind {
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
                            frontier.push((i, j, field.datatype));
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
        let cond_type = self.context[cond_val].datatype;

        let then_block = self.context.new_block();
        self.context.add_inst(InstEnt::new(
            IKind::JumpIfTrue(cond_val, then_block, vec![]),
            None,
            &cond_expr.token,
        ));

        if self.is_auto(cond_type) {
            self.infer(cond_val, self.program.builtin_repo.bool)?;
        } else {
            self.assert_type(cond_type, self.program.builtin_repo.bool, &cond_expr.token)?;
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

            let datatype = self.context[val].datatype;
            let value = self.new_temp_value(datatype);
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

                    let datatype = self.context[val].datatype;
                    let value = self.new_temp_value(datatype);
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
        unresolved.retain(|f| self.is_auto(self.context[*f].datatype));

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
            let sig = self.program[fun].signature();
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
        let datatype = match ast.token.kind {
            LTKind::Int(_, base) => match base {
                8 => self.program.builtin_repo.i8,
                16 => self.program.builtin_repo.i16,
                32 => self.program.builtin_repo.i32,
                64 => self.program.builtin_repo.i64,
                _ => self.program.builtin_repo.int,
            },
            LTKind::Uint(_, base) => match base {
                8 => self.program.builtin_repo.u8,
                16 => self.program.builtin_repo.u16,
                32 => self.program.builtin_repo.u32,
                64 => self.program.builtin_repo.u64,
                _ => self.program.builtin_repo.uint,
            },
            LTKind::Float(_, base) => match base {
                32 => self.program.builtin_repo.f32,
                _ => self.program.builtin_repo.f64,
            },
            LTKind::Bool(_) => self.program.builtin_repo.bool,
            LTKind::Char(_) => self.program.builtin_repo.i32,
            LTKind::String(_) => self.pointer_of(self.program.builtin_repo.u8, false),
            _ => unreachable!("{}", ast),
        };

        let value = self.new_temp_value(datatype);

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
        let datatype = self.resolve_type(&ast[2])?;

        let original_datatype = self.context[target].datatype;
        let original_size = self.program[original_datatype].size;
        let datatype_size = self.program[datatype].size;

        if original_size != datatype_size {
            return Err(FunError::new(
                FEKind::InvalidBitCast(original_size, datatype_size),
                &ast.token,
            ));
        }

        let value = self.new_anonymous_value(datatype, self.context[target].mutable);
        self.context
            .add_inst(InstEnt::new(IKind::Cast(target), Some(value), &ast.token));

        Ok(Some(value))
    }

    fn may_infer(&mut self, a: Value, b: Value, token: &Token) -> Result<bool> {
        let a_type = self.context[a].datatype;
        let b_type = self.context[b].datatype;
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

    fn infer(&mut self, value: Value, datatype: Type) -> Result<()> {
        let mut frontier = std::mem::take(&mut self.context.graph_frontier);
        frontier.clear();
        frontier.push((value, datatype));

        while let Some((value, datatype)) = frontier.pop() {
            let val = &mut self.context[value];
            val.datatype = datatype;
            let dependency_id = if let Some(dep) = val.type_dependency {
                val.type_dependency = None;
                dep
            } else {
                continue;
            };

            if let Some(inst) = val.inst {
                match self.context[inst].kind {
                    IKind::Ref(value) => match self.program[datatype].kind {
                        TKind::Pointer(inner, _) => {
                            frontier.push((value, inner));
                        }
                        _ => unreachable!(),
                    },
                    IKind::Deref(value) => {
                        let mutable = matches!(
                            self.program[self.context[value].datatype].kind,
                            TKind::Pointer(_, true)
                        );
                        frontier.push((value, self.pointer_of(datatype, mutable)));
                    }
                    IKind::VarDecl(value) => {
                        frontier.push((value, datatype));
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
                        frontier.push((value, datatype));
                    }
                    IKind::UnresolvedCall(..) => {
                        self.infer_call(dep, &mut frontier)?;
                    }
                    IKind::ZeroValue => {
                        let value = inst.value.unwrap();
                        self.context[value].datatype = datatype;
                    }
                    IKind::Assign(val) => {
                        let mut val = *val;
                        if value == val {
                            val = inst.value.unwrap();
                        }

                        frontier.push((val, datatype));
                    }
                    IKind::UnresolvedDot(header, field) => {
                        let header = *header;
                        let field = *field;

                        let value = inst.value.unwrap();
                        self.context.function_body.insts.remove(dep);
                        let datatype = self.field_access(header, field, value, &token)?;
                        frontier.push((value, datatype));
                    }
                    IKind::Ref(value) => {
                        let val = inst.value.unwrap();
                        let value = *value;
                        let value_datatype = self.context[value].datatype;
                        let mutable =
                            matches!(self.program[value_datatype].kind, TKind::Pointer(_, true));
                        let datatype = self.pointer_of(value_datatype, mutable);
                        frontier.push((val, datatype));
                    }
                    IKind::Deref(value) => {
                        let value = *value;
                        let val = inst.value.unwrap();
                        let value_datatype = self.context[value].datatype;
                        let datatype = match self.program[value_datatype].kind {
                            TKind::Pointer(inner, _) => inner,
                            _ => unreachable!(),
                        };
                        frontier.push((val, datatype));
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
                self.program[fun]
                    .signature()
                    .args
                    .iter()
                    .map(|arg| arg.datatype),
            );
            for (&datatype, &value) in types.iter().zip(args.iter()) {
                if self.is_auto(self.context[value].datatype) {
                    frontier.push((value, datatype));
                }
            }
            self.context.type_buffer = types;
        }

        let value = self.context[inst].value;
        let sig = self.program[fun].signature();
        let struct_return = sig.struct_return;
        let datatype = sig.return_type;

        if let (Some(value), Some(datatype)) = (value, datatype) {
            if struct_return {
                self.context[value].mutable = true;
                args.push(value);
            }
            frontier.push((value, datatype));
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
        let header_datatype = self.context[header].datatype;
        let mut path = vec![];
        if !self.find_field(header_datatype, field, &mut path) {
            return Err(FunError::new(FEKind::UnknownField(header_datatype), token));
        }

        let mut offset = 0;
        let mut current_type = header_datatype;
        for &i in path.iter().rev() {
            match &self.program[current_type].kind {
                TKind::Structure(structure) => {
                    let field = &structure.fields[i];
                    offset += field.offset;
                    current_type = field.datatype;
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
                _ => todo!("{:?}", self.program[current_type]),
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
        val.datatype = current_type;

        Ok(current_type)
    }

    fn inst_of(&mut self, value: Value) -> Inst {
        // if inst is none then this is function parameter and its safe to put it
        // at the beginning of the entry block
        self.context[value]
            .inst
            .unwrap_or(self.context.function_body.insts.first().unwrap())
    }

    pub fn add_variable(&mut self, name: ID, datatype: Type, mutable: bool) -> Value {
        let val = self.new_value(name, datatype, mutable);
        self.context.variables.push(Some(val));
        val
    }

    #[inline]
    fn new_temp_value(&mut self, datatype: Type) -> Value {
        self.new_anonymous_value(datatype, false)
    }

    #[inline]
    fn new_anonymous_value(&mut self, datatype: Type, mutable: bool) -> Value {
        self.new_value(ID(0), datatype, mutable)
    }

    #[inline]
    fn new_value(&mut self, name: ID, datatype: Type, mutable: bool) -> Value {
        let mut value = ValueEnt::new(name, datatype, mutable);
        if self.is_auto(datatype) {
            let dep = self.context.new_type_dependency();
            value.type_dependency = Some(dep);
        }
        self.context.function_body.values.add(value)
    }

    fn assignment(&mut self, ast: &Ast) -> ExprResult {
        let target = self.expr(&ast[1])?;
        let value = self.expr(&ast[2])?;
        let target_datatype = self.context[target].datatype;
        let value_datatype = self.context[value].datatype;

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
        types.extend(args.iter().map(|v| self.context[*v].datatype));

        let result = if dot_expr {
            let first_mutable = self.context[args[0]].mutable;
            assert!(self.context.current_module.is_some());
            let (fun, id, kind) =
                self.dot_find_or_instantiate(base, name, &mut types, first_mutable, &token)?;
            if id.0 != 0 {
                let value = self.new_anonymous_value(self.program.builtin_repo.bool, first_mutable);
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
            let (datatype, id) = frontier[i];
            values[0] = datatype;
            unwrap!(
                self.find_or_instantiate(base, name, values, token),
                id,
                None
            );
            if self.is_pointer(datatype) {
                values[0] = self.base_of(datatype).unwrap().0;
                unwrap!(
                    self.find_or_instantiate(base, name, values, token),
                    id,
                    Deref
                );
            } else {
                if first_mutable {
                    values[0] = self.pointer_of(datatype, true);
                    unwrap!(
                        self.find_or_instantiate(base, name, values, token),
                        id,
                        MutRef
                    );
                }

                values[0] = self.pointer_of(datatype, false);
                assert!(self.context.current_module.is_some());
                unwrap!(self.find_or_instantiate(base, name, values, token), id, Ref);
            }

            match &self.program[datatype].kind {
                TKind::Structure(structure) => {
                    for field in structure.fields.iter().filter(|f| f.embedded) {
                        frontier.push((field.datatype, field.name));
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
            base.combine(self.program.types.direct_to_id(val))
        });
        assert!(self.context.current_module.is_some());
        if let Some((_, fun)) = self.find_by_name(self.context.current_module.unwrap(), specific_id)
        {
            return Ok(fun);
        }

        if let Some((module, functions)) = self.find_generic_by_name(base) {
            let len = self.program.generic_functions[functions].len();
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

        let fun = &self.program.generic_functions[functions][index];

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
                let datatype = values[n + j];
                generic.arg_buffer.clear();
                self.load_arg_from_datatype(datatype, &mut generic);
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
                                    if id.unwrap() != self.program.builtin_repo.auto {
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

        let module_id = self.program[module].id;

        let old_len = self.context.type_resolver_context.shadowed_types.len();
        let old_id_len = self.context.type_resolver_context.instance_id_buffer.len();

        for (&name, &datatype) in generic.param_buffer.iter().zip(generic.inferred.iter()) {
            let datatype = match datatype {
                Some(id) => id,
                None => return Ok(None),
            };
            let id = name.combine(module_id);
            if let Some(shadowed) = self.program.types.redirect(id, datatype) {
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
                    std::mem::transmute::<_, &mut ModuleEnt>(&mut self.program[module]),
                    &self.program[current],
                )
            };
            let len = target_module.dependency.len();
            target_module
                .dependency
                .extend(source_module.dependency.iter());
            len
        } else {
            self.program[module].dependency.len()
        };

        let fun = &self.program.generic_functions[functions][index];
        let (ast_ref, name, debug_name, vis, attr_id) = (fun.ast, fun.name, fun.debug_name, fun.visibility, fun.attribute_id);
        let fun = {
            // SAFETY: the function_ast has same live-time as self ans scope ensures
            // the reference does not escape
            let ast = unsafe { self.context.function_ast.get(ast_ref) };
            let id = self.id_of_ast_signature(module, name, &ast[0])?;
            if let Some(fun) = self.program.functions.id_to_direct(id) {
                fun
            } else {
                self.context.dive();
                let fun = self.collect_normal_function(module, ast_ref, ast, name, debug_name, vis, attr_id)?;
                self.function(fun)?;
                self.context.bail();
                fun
            }
        };
        self.program[module].dependency.truncate(old_dependency_len);

        for i in old_id_len..self.context.type_resolver_context.instance_id_buffer.len() {
            self.program.types.remove_redirect(
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
            let id = self.program.types.direct_to_id(direct_id);
            self.program.types.remove_redirect(id, Some(direct_id));
        }
        self.context
            .type_resolver_context
            .shadowed_types
            .truncate(old_len);

        Ok(Some(fun))
    }

    fn find_by_name(&mut self, module: Mod, name: ID) -> Option<(Mod, Fun)> {
        self.program.walk_accessible_scopes(module, |id, module| {
            self.program
                .functions
                .id_to_direct(name.combine(id))
                .map(|fun| (module, fun))
        })
    }

    fn find_generic_by_name(&mut self, name: ID) -> Option<(Mod, Fun)> {
        self.program
            .walk_accessible_scopes(self.context.current_module.unwrap(), |id, module| {
                self.program
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

        for module in unsafe { self.program.modules.direct_ids() } {
            if !self.program.modules.is_direct_valid(module) {
                continue;
            }

            self.context.current_module = Some(module);

            let mut ast = std::mem::take(&mut self.program.modules[module].ast);
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
            self.program.modules[module].ast = ast;
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

        let name = name.combine(self.program.modules.direct_to_id(module));

        self.program
            .generic_functions
            .get_mut_or(name, vec![])
            .push(function);

        Ok(self.program.generic_functions.id_to_direct(name).unwrap())
    }

    fn id_of_ast_signature(&mut self, module: Mod, base_name: ID, ast: &Ast) -> Result<ID> {
        let mut name = base_name;
        for param_line in &ast[1..ast.len() - 1] {
            let raw_datatype = param_line.last().unwrap();
            let datatype = self.resolve_type_low(module, raw_datatype)?;
            for _ in 0..param_line.len() - 1 {
                name = name.combine(self.program.types.direct_to_id(datatype));
            }
        }

        Ok(name.combine(self.program.modules.direct_to_id(module)))
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
            let datatype = self.resolve_type_low(module, raw_datatype)?;
            if self.is_auto(datatype) {
                return Err(FunError::new(FEKind::UnexpectedAuto, &raw_datatype.token));
            }
            for param in param_line[0..param_line.len() - 1].iter() {
                name = name.combine(self.program.types.direct_to_id(datatype));
                let name = ID(0).add(param.token.spam.deref());
                let mutable = param_line.kind == AKind::FunArgument(true);
                args.push(ValueEnt::new(name, datatype, mutable));
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
                self.program[return_type].size > self.program.isa().pointer_bytes() as u32;
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

        name = name.combine(self.program.modules.direct_to_id(module));
        let id = match self.program.functions.insert(name, function) {
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

    fn load_arg_from_datatype(&self, datatype: Type, generic: &mut GenericFunContext) {
        let dt = &self.program[datatype];

        if dt.params.is_empty() {
            if let TKind::Pointer(pointed, mutable) = dt.kind {
                generic.arg_buffer.push(GenericElement::Pointer(mutable));
                self.load_arg_from_datatype(pointed, generic);
            } else {
                generic
                    .arg_buffer
                    .push(GenericElement::Element(datatype, Some(datatype)));
            }
            return;
        }

        generic
            .arg_buffer
            .push(GenericElement::Element(dt.params[0], Some(datatype)));

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
                    let datatype = self.find_type(&ast.token)?;
                    self.context
                        .generic
                        .arg_buffer
                        .push(GenericElement::Element(datatype, None));
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

    fn resolve_type(&mut self, ast: &Ast) -> Result<Type> {
        self.resolve_type_low(self.context.current_module.unwrap(), ast)
    }

    fn resolve_type_low(&mut self, module: Mod, ast: &Ast) -> Result<Type> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .resolve_immediate(module, ast)
            .map_err(Into::into)
    }

    fn find_type(&mut self, token: &Token) -> Result<Type> {
        self.find_type_low(self.context.current_module.unwrap(), token)
    }

    fn find_type_low(&mut self, module: Mod, token: &Token) -> Result<Type> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .find_by_token(module, token)
            .map(|(_, t)| t)
            .map_err(Into::into)
    }

    #[inline]
    fn auto(&self) -> Type {
        self.program.builtin_repo.auto
    }

    #[inline]
    fn is_auto(&self, datatype: Type) -> bool {
        self.program.builtin_repo.auto == datatype
            || self.program[datatype].kind == TKind::Generic
            || matches!(self.program[datatype].kind, TKind::Pointer(pointed, _) if self.is_auto(pointed))
    }

    fn find_loop(&self, token: &Token) -> std::result::Result<Loop, bool> {
        if token.spam.is_empty() {
            return self.context.loops.last().cloned().ok_or(true);
        }

        let name = ID(0).add(token.spam.deref());

        self.context
            .loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.context.loops.is_empty())
    }

    fn base_of_err(&mut self, datatype: Type, token: &Token) -> Result<(Type, bool)> {
        self.base_of(datatype)
            .ok_or_else(|| FunError::new(FEKind::NonPointerDereference, token))
    }

    fn base_of(&mut self, datatype: Type) -> Option<(Type, bool)> {
        match self.program[datatype].kind {
            TKind::Pointer(pointed, mutable) => Some((pointed, mutable)),
            _ => None,
        }
    }

    fn pointer_of(&mut self, datatype: Type, mutable: bool) -> Type {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .pointer_to(datatype, mutable)
    }

    #[inline]
    pub fn is_pointer(&self, datatype: Type) -> bool {
        matches!(self.program[datatype].kind, TKind::Pointer(_, _))
    }

    #[inline]
    fn pass_mutability(&mut self, from: Value, to: Value) {
        self.context[to].mutable = self.context[from].mutable;
    }
}

#[derive(Debug)]
pub struct FunResolverContext {
    pub generic: GenericFunContext,
    pub function_ast: LockedList<AstRef, Ast>,
    pub type_resolver_context: TypeResolverContext,
    pub function_context_pool: Vec<FunContext>,
    pub current_context: usize,
}

impl FunResolverContext {
    pub fn dive(&mut self) {
        self.current_context += 1;
        if self.current_context >= self.function_context_pool.len() {
            self.function_context_pool.push(Default::default());
        } else {
            self.function_context_pool[self.current_context].clear();
        }
    }

    pub fn bail(&mut self) {
        self.current_context -= 1;
    }

    pub fn clear(&mut self) {
        self.type_resolver_context.clear();
        self.current_context = 0;
    }
}

impl Default for FunResolverContext {
    fn default() -> Self {
        FunResolverContext {
            function_ast: LockedList::default(),
            generic: Default::default(),
            type_resolver_context: Default::default(),
            function_context_pool: vec![Default::default()],
            current_context: 0,
        }
    }
}

impl Deref for FunResolverContext {
    type Target = FunContext;

    fn deref(&self) -> &Self::Target {
        &self.function_context_pool[self.current_context]
    }
}

impl DerefMut for FunResolverContext {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.function_context_pool[self.current_context]
    }
}

#[derive(Default, Debug)]
pub struct GenericFunContext {
    pub arg_buffer: Vec<GenericElement>,
    pub param_buffer: Vec<ID>,
    pub inferred: Vec<Option<Type>>,
}

#[derive(Debug, Default)]
pub struct FunContext {
    pub return_type: Option<Type>,
    pub struct_return: Option<Value>,
    pub current_module: Option<Mod>,
    pub current_block: Option<Inst>,
    pub variables: Vec<Option<Value>>,
    pub loops: Vec<Loop>,
    pub type_graph: List<TypeDep, Vec<Inst>>,
    pub unresolved_functions: Vec<Inst>,
    pub type_graph_pool: Vec<Vec<Inst>>,
    pub function_body: FunBody,
    pub embed_frontier: Vec<(Type, ID)>,
    pub graph_frontier: Vec<(Value, Type)>,
    pub second_graph_frontier: Vec<(Value, Type)>,
    pub call_value_buffer: Vec<Value>,
    pub type_frontier: Vec<(usize, usize, Type)>,
    pub type_buffer: Vec<Type>,
}

impl FunContext {
    pub fn find_variable(&mut self, name: ID) -> Option<Value> {
        self.variables
            .iter()
            .rev()
            .filter(|v| v.is_some())
            .map(|v| v.unwrap())
            .find(|v| self.function_body.values[*v].name == name)
    }

    pub fn push_scope(&mut self) {
        self.variables.push(None);
    }

    pub fn pop_scope(&mut self) {
        let idx = self.variables.len()
            - 1
            - self
                .variables
                .iter()
                .rev()
                .position(|v| v.is_none())
                .expect("no scope to pop");

        self.variables.truncate(idx);
    }

    pub fn clear(&mut self) {
        self.current_module = None;
        self.current_block = None;
        self.struct_return = None;
        self.variables.clear();
        self.function_body.clear();

        while let Some(garbage) = self.type_graph.pop() {
            self.type_graph_pool.push(garbage);
        }
    }

    pub fn add_inst(&mut self, inst: InstEnt) -> Inst {
        debug_assert!(self.current_block.is_some(), "no block to add inst to");
        let closing = inst.kind.is_closing();
        let value = inst.value;
        let inst = self.function_body.insts.push(inst);
        if let Some(value) = value {
            self[value].inst = Some(inst);
        }
        if closing {
            self.close_block();
        }
        inst
    }

    pub fn add_inst_under(&mut self, inst: InstEnt, under: Inst) -> Inst {
        debug_assert!(!inst.kind.is_closing(), "cannot insert closing instruction");
        let value = inst.value;
        let inst = self.function_body.insts.insert(under, inst);
        if let Some(value) = value {
            self[value].inst = Some(inst);
        }
        inst
    }

    pub fn new_block(&mut self) -> Inst {
        self.function_body.insts.add_hidden(InstEnt::new(
            IKind::Block(Default::default()),
            None,
            &Token::default(),
        ))
    }

    pub fn make_block_current(&mut self, block: Inst) {
        debug_assert!(self.current_block.is_none(), "current block is not closed");
        self.function_body.insts.show_as_last(block);
        self.current_block = Some(block);
    }

    pub fn close_block(&mut self) {
        debug_assert!(self.current_block.is_some(), "no block to close");
        let block = self.current_block.unwrap();
        let inst = self.function_body.insts.push(InstEnt::new(
            IKind::BlockEnd(block),
            None,
            &Token::default(),
        ));
        self[block].kind.block_mut().end = Some(inst);
        self.current_block = None;
    }

    pub fn new_type_dependency(&mut self) -> TypeDep {
        let mut value = self.type_graph_pool.pop().unwrap_or_default();
        value.push(Inst::new(usize::MAX));
        let value = self.type_graph.add(value);
        value
    }

    pub fn remove_inst(&mut self, inst: Inst) {
        let inst_value = &mut self[inst];
        match &inst_value.kind {
            &IKind::Deref(value) | &IKind::Ref(value) => {
                let value = &mut self[value];
                if let Some(dep) = value.type_dependency {
                    let idx = self[dep].iter().position(|v| *v == inst).unwrap();
                    self[dep].remove(idx);
                } else {
                    unreachable!()
                }
            }
            _ => todo!("{:?}", inst_value.kind),
        }

        self.function_body.insts.remove(inst);
    }
}

impl Index<Value> for FunContext {
    type Output = ValueEnt;

    fn index(&self, val: Value) -> &Self::Output {
        &self.function_body.values[val]
    }
}

impl IndexMut<Value> for FunContext {
    fn index_mut(&mut self, val: Value) -> &mut Self::Output {
        &mut self.function_body.values[val]
    }
}

impl Index<TypeDep> for FunContext {
    type Output = Vec<Inst>;

    fn index(&self, val: TypeDep) -> &Self::Output {
        &self.type_graph[val]
    }
}

impl IndexMut<TypeDep> for FunContext {
    fn index_mut(&mut self, val: TypeDep) -> &mut Self::Output {
        &mut self.type_graph[val]
    }
}

impl Index<Inst> for FunContext {
    type Output = InstEnt;

    fn index(&self, val: Inst) -> &Self::Output {
        &self.function_body.insts[val]
    }
}

impl IndexMut<Inst> for FunContext {
    fn index_mut(&mut self, val: Inst) -> &mut Self::Output {
        &mut self.function_body.insts[val]
    }
}

pub struct FunErrorDisplay<'a> {
    program: &'a Program,
    error: &'a FunError,
}

impl<'a> FunErrorDisplay<'a> {
    pub fn new(program: &'a Program, error: &'a FunError) -> Self {
        Self { program, error }
    }
}

impl<'a> Display for FunErrorDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !matches!(&self.error.kind, FEKind::TypeError(_)) {
            writeln!(f, "{}", TokenView::new(&self.error.token))?;
        }
        match &self.error.kind {
            FEKind::AssignToImmutable => writeln!(f, "cannot assign to immutable value"),
            FEKind::TypeError(kind) => {
                writeln!(f, "{}", TypeError::new(kind.clone(), &self.error.token))
            }
            FEKind::Redefinition(other) => {
                writeln!(f, "redefines the")?;
                writeln!(f, "{}", TokenView::new(other))
            }
            FEKind::ExpectedValue => writeln!(f, "expected this expression to return a value"),
            &FEKind::TypeMismatch(actual, supposed) => {
                let type_printer = TypePrinter::new(self.program);
                write!(
                    f,
                    "type mismatch, found '{}' which does not match the '{}'",
                    type_printer.print(actual),
                    type_printer.print(supposed)
                )
            }
            FEKind::FunctionNotFound(name, arguments) => {
                let type_printer = TypePrinter::new(self.program);
                let argument_string = arguments
                    .iter()
                    .map(|&t| type_printer.print(t))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(
                    f,
                    "function with signature '{}({})' not found",
                    name, argument_string
                )
            }
            FEKind::UnexpectedValue => writeln!(
                f,
                "expression that returns value is not allowed here, use 'discard' <expr> syntax"
            ),
            FEKind::UnexpectedReturnValue => writeln!(
                f,
                "function does not return value this return with value is invalid"
            ),
            FEKind::UnexpectedAuto => writeln!(f, "inference cannot be used here"),
            FEKind::UndefinedVariable => {
                writeln!(f, "variable is not defined in the current scope")
            }
            FEKind::UnresolvedType => writeln!(
                f,
                "type of this expression cannot be inferred, try to add some annotations"
            ),
            &FEKind::UnknownField(datatype) => {
                let type_printer = TypePrinter::new(self.program);
                writeln!(
                    f,
                    "'{}' does not have a this field",
                    type_printer.print(datatype)
                )
            }
            FEKind::MutableRefOfImmutable => {
                writeln!(f, "cannot take mutable reference of immutable value")
            }
            FEKind::MissingElseBranch => writeln!(
                f,
                "missing else branch, it is expected as if branch returns value"
            ),
            FEKind::ContinueOutsideLoop => {
                writeln!(f, "continue statement is not allowed outside of a loop")
            }
            FEKind::BreakOutsideLoop => {
                writeln!(f, "break statement is not allowed outside of a loop")
            }
            FEKind::WrongLabel => writeln!(f, "label is not defined in the current scope"),
            FEKind::NonPointerDereference => writeln!(f, "cannot dereference non-pointer value"),
            FEKind::InvalidBitCast(actual, supposed) => writeln!(
                f,
                "'as' requires operand to be of same size as target ({} as {})",
                actual, supposed
            ),
        }
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

pub fn test() {
    let mut program = Program::default();
    let builder = ModuleTreeBuilder::new(&mut program);
    builder.build("src/ir/tests/module_tree/root").unwrap();

    let mut ctx = TypeResolverContext::default();

    TypeResolver::new(&mut program, &mut ctx).resolve().unwrap();

    let mut ctx = FunResolverContext::default();

    FunResolver::new(&mut program, &mut ctx)
        .resolve()
        .map_err(|e| {
            println!("{}", FunErrorDisplay::new(&program, &e));
            e
        })
        .unwrap();

    for fun in unsafe { program.functions.direct_ids() } {
        if !program.functions.is_direct_valid(fun)
            || !matches!(program.functions[fun].kind, FKind::Normal(_))
        {
            continue;
        }

        let fun = &program.functions[fun];

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
                        let datatype =
                            TypePrinter::new(&program).print(fun.body.values[value].datatype);
                        println!(
                            "    {:?}: {} = {:?} |{}",
                            value,
                            datatype,
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
}
