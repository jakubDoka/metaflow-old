use std::ops::{Deref, DerefMut, Index, IndexMut};

use crate::ast::{AKind, Ast, Vis};
use crate::ir::{
    Block, FKind, Fun, FunBody, FunEnt, Inst, LTKind, Module, ModuleEnt, Type, TypeDep, Value,
    ValueEnt,
};
use crate::lexer::Token;
use crate::util::sym_table::LockedSymVec;
use crate::util::{
    sdbm::{SdbmHashState, ID},
    sym_table::{SymID, SymVec},
};

use super::module_tree::ModuleTreeBuilder;
use super::types::{TEKind, TypeError, TypeResolver, TypeResolverContext};
use super::{
    AstRef, BlockEnt, FunSignature, GenericElement, GenericSignature, IKind, InstEnt, Program,
    TKind,
};

type Result<T = ()> = std::result::Result<T, FunError>;

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
        }

        Ok(())
    }

    fn function(&mut self, function: Fun) -> Result {
        let fun = &mut self.program.functions[function];

        let signature = match &mut fun.kind {
            FKind::Normal(signature) => std::mem::take(signature),
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
        self.context.function_body.clear();

        Ok(())
    }

    fn function_low(&mut self, module: Module, ast: &Ast, signature: &FunSignature) -> Result {
        self.context.current_instruction = None;
        self.context.current_module = Some(module);
        self.context.return_type = signature.return_type;
        let entry_point = self.context.new_block();
        self.context.make_block_current(entry_point);

        signature.args.iter().for_each(|param| {
            let var = self.context.function_body.values.add(param.clone());
            self.context[entry_point].args.push(var);
            self.context.variables.push(Some(var));
        });

        let value = self.block(&ast[1])?;

        if let (Some(value), Some(_), Some(return_type)) =
            (value, self.context.current_block, signature.return_type)
        {
            let value_type = self.context[value].datatype;
            if self.is_auto(value_type) {
                self.infer(value, return_type)?;
            }
            self.context.add_instruction(InstEnt::new(
                IKind::Return(Some(value)),
                None,
                &ast[1].last().unwrap().token,
            ));
        } else if let (Some(return_type), Some(_)) =
            (signature.return_type, self.context.current_block)
        {
            let temp = self.new_value(return_type);
            self.context.add_instruction(InstEnt::new(
                IKind::ZeroValue,
                Some(temp),
                &ast[1].last().unwrap().token,
            ));
            self.context.add_instruction(InstEnt::new(
                IKind::Return(Some(temp)),
                None,
                &ast[1].last().unwrap().token,
            ));
        } else if self.context.current_block.is_some() {
            self.context.add_instruction(InstEnt::new(
                IKind::Return(None),
                None,
                &ast[1].last().unwrap().token,
            ));
        }

        for (id, dep) in self.context.type_graph.iter() {
            if dep.len() > 0 {
                return Err(FunError::new(FEKind::UnresolvedType(id), &Token::default()));
            }
        }

        Ok(())
    }

    fn block(&mut self, ast: &Ast) -> Result<Option<Value>> {
        if ast.is_empty() {
            return Ok(None);
        }

        self.context.push_scope();

        for statement in ast[..ast.len() - 1].iter() {
            self.statement(statement)?;
        }

        let value = self.statement(ast.last().unwrap());

        self.context.pop_scope();

        value
    }

    fn statement(&mut self, statement: &Ast) -> Result<Option<Value>> {
        match statement.kind {
            AKind::VarStatement(_) => self.var_statement(statement)?,
            AKind::ReturnStatement => self.return_statement(statement)?,
            AKind::Loop => todo!(),
            AKind::Break => todo!(),
            AKind::Continue => todo!(),
            _ => return self.expression_low(statement),
        }

        Ok(None)
    }

    fn return_statement(&mut self, ast: &Ast) -> Result {
        let datatype = self.context.return_type;

        let value = if ast[0].kind == AKind::None {
            if let Some(datatype) = datatype {
                let temp_value = self.new_value(datatype);

                self.context.add_instruction(InstEnt::new(
                    IKind::ZeroValue,
                    Some(temp_value),
                    &Token::default(),
                ));
                Some(temp_value)
            } else {
                None
            }
        } else {
            let datatype = datatype
                .ok_or_else(|| FunError::new(FEKind::UnexpectedReturnValue, &ast[0].token))?;
            let value = self.expression(&ast[0])?;
            let actual_type = self.context[value].datatype;
            if self.is_auto(actual_type) {
                self.infer(value, datatype)?;
            } else {
                self.assert_type(actual_type, datatype, &ast[0].token)?;
            }

            Some(value)
        };

        self.context
            .add_instruction(InstEnt::new(IKind::Return(value), None, &ast.token));

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
                    let name = ID::new().add(name.token.spam.deref());

                    let temp_value = self
                        .context
                        .function_body
                        .values
                        .add(ValueEnt::temp(datatype));

                    let unresolved = self.is_auto(datatype);

                    let inst = self.context.add_instruction(InstEnt::new(
                        IKind::ZeroValue,
                        Some(temp_value),
                        &Token::default(),
                    ));

                    let dep = if unresolved {
                        Some(self.context.new_type_dependency())
                    } else {
                        None
                    };

                    let var = ValueEnt {
                        name,
                        datatype,
                        mutable,
                        type_dependency: dep,
                        value: None,
                        on_stack: false,
                    };

                    let var = self.context.add_variable(var);

                    if unresolved {
                        self.add_type_dependency(var, inst);
                    }

                    self.context.add_instruction(InstEnt::new(
                        IKind::VarDecl(temp_value),
                        Some(var),
                        &var_line.token,
                    ));
                }
            } else {
                for (name, raw_value) in var_line[0].iter().zip(var_line[2].iter()) {
                    let name = ID::new().add(name.token.spam.deref());
                    let value = self.expression(raw_value)?;
                    let actual_datatype = self.context[value].datatype;

                    if !self.is_auto(datatype) {
                        if self.is_auto(actual_datatype) {
                            self.infer(value, datatype)?;
                        } else {
                            self.assert_type(actual_datatype, datatype, &raw_value.token)?;
                        }
                    }

                    let unresolved = self.is_auto(actual_datatype);

                    let dep = if unresolved {
                        Some(self.context.new_type_dependency())
                    } else {
                        None
                    };

                    let var = ValueEnt {
                        name,
                        datatype: actual_datatype,
                        mutable,

                        type_dependency: dep,

                        value: None,
                        on_stack: false,
                    };

                    let var = self.context.add_variable(var);

                    let inst = self.context.add_instruction(InstEnt::new(
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

    fn expression(&mut self, ast: &Ast) -> Result<Value> {
        self.expression_low(ast)?
            .ok_or_else(|| FunError::new(FEKind::ExpectedValue, &ast.token))
    }

    fn expression_low(&mut self, ast: &Ast) -> Result<Option<Value>> {
        match ast.kind {
            AKind::BinaryOperation => self.binary_operation(ast),
            AKind::Literal => self.literal(ast),
            AKind::Identifier => self.identifier(ast),
            AKind::Call => self.call(ast),
            AKind::IfExpression => self.if_expression(ast),
            _ => todo!("unmatched expression ast {}", ast),
        }
    }

    fn if_expression(&mut self, ast: &Ast) -> Result<Option<Value>> {
        let cond_expr = &ast[0];
        let cond_val = self.expression(cond_expr)?;
        let cond_type = self.context[cond_val].datatype;

        let then_block = self.context.new_block();
        self.context.add_instruction(InstEnt::new(
            IKind::JumpIfTrue(cond_val, then_block, Vec::new()),
            None,
            &cond_expr.token,
        ));

        if self.is_auto(cond_type) {
            self.infer(cond_val, self.program.builtin_repo.bool)?;
        } else {
            self.assert_type(cond_type, self.program.builtin_repo.bool, &cond_expr.token)?;
        }

        let mut merge_block = None;

        let else_branch = &ast[2];
        let some_block = self.context.new_block();
        let else_block = if else_branch.kind == AKind::None {
            self.context.add_instruction(InstEnt::new(
                IKind::Jump(some_block, Vec::new()),
                None,
                &else_branch.token,
            ));
            merge_block = Some(some_block);
            None
        } else {
            self.context.add_instruction(InstEnt::new(
                IKind::Jump(some_block, Vec::new()),
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
            if merge_block.is_some() {
                return Err(FunError::new(FEKind::MissingElseBranch, &ast.token));
            }

            let block = self.context.new_block();
            self.context.add_instruction(InstEnt::new(
                IKind::Jump(block, vec![val]),
                None,
                &Token::default(),
            ));

            let datatype = self.context[val].datatype;
            let value = self.new_value(datatype);
            self.context[block].args.push(value);
            result = Some(value);
            merge_block = Some(block);
        } else if self.context.current_block.is_some() {
            let block = merge_block.unwrap_or_else(|| self.context.new_block());
            self.context.add_instruction(InstEnt::new(
                IKind::Jump(block, Vec::new()),
                None,
                &Token::default(),
            ));
            merge_block = Some(block);
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
                    let merge_block = merge_block.unwrap();
                    self.may_infer(val, result, &value_token)?;
                    self.context.add_instruction(InstEnt::new(
                        IKind::Jump(merge_block, vec![val]),
                        None,
                        value_token,
                    ));
                    self.context.make_block_current(merge_block);
                } else if then_filled {
                    let block = self.context.new_block();

                    self.context.add_instruction(InstEnt::new(
                        IKind::Jump(block, vec![val]),
                        None,
                        value_token,
                    ));

                    let datatype = self.context[val].datatype;
                    let value = self.new_value(datatype);
                    self.context[block].args.push(value);
                    result = Some(value);
                    self.context.make_block_current(block);
                } else {
                    return Err(FunError::new(FEKind::UnexpectedValue, &ast.token));
                }
            } else {
                let block = merge_block.unwrap_or_else(|| self.context.new_block());
                if self.context.current_block.is_some() {
                    if result.is_some() {
                        return Err(FunError::new(FEKind::ExpectedValue, &ast.token));
                    }
                    self.context.add_instruction(InstEnt::new(
                        IKind::Jump(block, Vec::new()),
                        None,
                        &Token::default(),
                    ));
                }
                self.context.make_block_current(block);
            }
        }

        Ok(result)
    }

    fn call(&mut self, ast: &Ast) -> Result<Option<Value>> {
        let base_name = ID::new().add(ast[0].token.spam.deref()); // TODO: check if this is generic instantiation
        for value in ast[1..].iter() {
            let value = self.expression(value)?;
            self.context.call_value_buffer.push(value);
        }

        self.call_low(base_name, &ast.token)
    }

    fn call_low(&mut self, base_name: ID, token: &Token) -> Result<Option<Value>> {
        let inst = self
            .context
            .add_instruction(InstEnt::new(IKind::NoOp, None, token));

        let mut unresolved = false;
        for i in 0..self.context.call_value_buffer.len() {
            let value = self.context.call_value_buffer[i];
            if self.is_auto(self.context[value].datatype) {
                // two arguments can be of same value but that only
                // means we subtract twice later on
                self.add_type_dependency(value, inst);
                unresolved = true;
            }
        }

        let value = if unresolved {
            self.context[inst].kind =
                IKind::UnresolvedCall(base_name, self.context.call_value_buffer.clone());
            let value = self.new_auto_value();
            self.context[inst].value = Some(value);
            Some(value)
        } else {
            let mut name = base_name;
            for &value in self.context.call_value_buffer.iter() {
                name = name.combine(
                    self.program
                        .types
                        .direct_to_id(self.context[value].datatype),
                );
            }
            let (_, fun) = self
                .find_by_name(name)
                .ok_or_else(|| FunError::new(FEKind::NotFound, token))?;
            self.context[inst].kind = IKind::Call(fun, self.context.call_value_buffer.clone());
            if let Some(return_type) = self.program[fun].signature().return_type {
                let value = self.new_value(return_type);
                self.context[inst].value = Some(value);
                Some(value)
            } else {
                None
            }
        };

        self.context.call_value_buffer.clear();

        Ok(value)
    }

    fn identifier(&mut self, ast: &Ast) -> Result<Option<Value>> {
        let name = ID::new().add(ast.token.spam.deref());
        self.context
            .find_variable(name)
            .ok_or_else(|| FunError::new(FEKind::UndefinedVariable, &ast.token))
            .map(|var| Some(var))
    }

    fn literal(&mut self, ast: &Ast) -> Result<Option<Value>> {
        let datatype = match ast.token.kind {
            LTKind::Int(_, base) => match base {
                1 => self.program.builtin_repo.i8,
                2 => self.program.builtin_repo.i16,
                4 => self.program.builtin_repo.i32,
                _ => self.program.builtin_repo.i64,
            },
            LTKind::Uint(_, base) => match base {
                1 => self.program.builtin_repo.u8,
                2 => self.program.builtin_repo.u16,
                4 => self.program.builtin_repo.u32,
                _ => self.program.builtin_repo.u64,
            },
            LTKind::Float(_, base) => match base {
                4 => self.program.builtin_repo.f32,
                _ => self.program.builtin_repo.f64,
            },
            LTKind::Bool(_) => self.program.builtin_repo.bool,
            LTKind::Char(_) => self.program.builtin_repo.i32,

            _ => unreachable!("{}", ast),
        };

        let value = self.new_value(datatype);

        self.context.add_instruction(InstEnt::new(
            IKind::Literal(ast.token.kind.clone()),
            Some(value),
            &ast.token,
        ));

        Ok(Some(value))
    }

    fn binary_operation(&mut self, ast: &Ast) -> Result<Option<Value>> {
        if ast[0].token.spam.deref() == "=" {
            return Ok(self.assignment(ast)?);
        }

        let left = self.expression(&ast[1])?;
        let right = self.expression(&ast[2])?;

        let base_id = ID::new().add(ast[0].token.spam.deref());

        self.context.call_value_buffer.extend(&[left, right]);

        self.call_low(base_id, &ast.token)
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
                dep
            } else {
                continue;
            };
            let mut dependencies = std::mem::take(&mut self.context[dependency_id]);
            for dep in dependencies.drain(..).skip(1)
            /* first is null marker */
            {
                let inst = &mut self.context[dep];
                inst.unresolved -= 1;
                if inst.unresolved != 0 {
                    continue;
                }

                match &mut inst.kind {
                    IKind::VarDecl(_) => {
                        let value = inst.value.unwrap();
                        frontier.push((value, datatype));
                    }
                    IKind::UnresolvedCall(base_id, args) => {
                        let args = std::mem::take(args);
                        let token = inst.token_hint.clone();
                        let base_id = *base_id;

                        let fun = self.find_or_instantiate(base_id, args.as_slice(), &token)?;

                        let inst = &mut self.context[dep];
                        inst.kind = IKind::Call(fun, args);
                        let value = inst.value;
                        let datatype = self.program[fun].signature().return_type;

                        if let (Some(value), Some(datatype)) = (value, datatype) {
                            frontier.push((value, datatype));
                        } else if self.context[value.unwrap()].type_dependency.is_some() {
                            return Err(FunError::new(FEKind::ExpectedValue, &token));
                        }
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
                    _ => todo!("{:?}", inst),
                }
            }

            self.context[dependency_id] = dependencies;
        }

        self.context.graph_frontier = frontier;

        Ok(())
    }

    fn new_auto_value(&mut self) -> Value {
        self.new_value(self.auto())
    }

    fn new_value(&mut self, datatype: Type) -> Value {
        let value = ValueEnt::temp(datatype);
        let value = self.context.function_body.values.add(value);
        if self.is_auto(datatype) {
            let dep = self.context.new_type_dependency();
            self.context[value].type_dependency = Some(dep);
        }
        value
    }

    fn assignment(&mut self, ast: &Ast) -> Result<Option<Value>> {
        let target = self.expression(&ast[1])?;
        let value = self.expression(&ast[2])?;
        let target_datatype = self.context[target].datatype;
        let value_datatype = self.context[value].datatype;

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

        let inst = self.context.add_instruction(InstEnt::new(
            IKind::Assign(target),
            Some(value),
            &ast.token,
        ));

        if unresolved {
            self.add_type_dependency(value, inst);
            self.add_type_dependency(target, inst);
        }

        Ok(Some(value))
    }

    fn find_or_instantiate(&mut self, base: ID, values: &[Value], token: &Token) -> Result<Fun> {
        let specific_id = values.iter().fold(base, |base, &val| {
            base.combine(self.program.types.direct_to_id(self.context[val].datatype))
        });

        if let Some((_, fun)) = self.find_by_name(specific_id) {
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

        Err(FunError::new(FEKind::NotFound, token))
    }

    fn instantiate(
        &mut self,
        module: Module,
        functions: Fun,
        index: usize,
        values: &[Value],
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
                let datatype = self.context[values[n + j]].datatype;
                generic.arg_buffer.clear();
                self.load_arg_from_datatype(datatype, &mut generic);
                let pattern = &signature.elements[i + 1..i + length + 1];

                for (real, pattern) in generic.arg_buffer.iter().zip(pattern) {
                    if real != pattern {
                        match pattern {
                            GenericElement::Parameter(param) => match real {
                                GenericElement::Element(_, id) => {
                                    generic.inferred[*param] = *id;
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
            0
        };

        let fun = &self.program.generic_functions[functions][index];
        let (ast_ref, name, vis, attr_id) = (fun.ast, fun.name, fun.visibility, fun.attribute_id);
        let fun = {
            // SAFETY: the function_ast has same live-time as self ans scope ensures
            // the reference does not escape
            let ast = unsafe { self.context.function_ast.get(ast_ref) };
            self.context.dive();
            let fun = self.collect_normal_function(module, ast_ref, ast, name, vis, attr_id)?;
            self.function(fun)?;
            self.context.bail();
            fun
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

    fn find_by_name(&mut self, name: ID) -> Option<(Module, Fun)> {
        self.program
            .walk_accessible_scopes(self.context.current_module.unwrap(), |id, module| {
                self.program
                    .functions
                    .id_to_direct(name.combine(id))
                    .map(|fun| (module, fun))
            })
    }

    fn find_generic_by_name(&mut self, name: ID) -> Option<(Module, Fun)> {
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
        let mut collected_ast = SymVec::new();

        for module in unsafe { self.program.modules.direct_ids() } {
            if !self.program.modules.is_direct_valid(module) {
                continue;
            }

            let mut ast = std::mem::take(&mut self.program.modules[module].ast);
            for (i, a) in ast.iter_mut().enumerate() {
                match a.kind.clone() {
                    AKind::Fun(visibility) => {
                        let a_ref = collected_ast.add(std::mem::take(a));
                        let a = &collected_ast[a_ref];
                        let header = &a[0];
                        match header[0].kind {
                            AKind::Identifier => {
                                let name = ID::new().add(header[0].token.spam.deref());
                                self.collect_normal_function(
                                    module, a_ref, a, name, visibility, i,
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

        self.context.function_ast = LockedSymVec::new(collected_ast);

        Ok(())
    }

    fn collect_generic_function(
        &mut self,
        module: Module,
        a_ref: AstRef,
        a: &Ast,
        visibility: Vis,
        attribute_id: usize,
    ) -> Result<Fun> {
        let name = ID::new()
            .add(a[0][0][0].token.spam.deref())
            .combine(self.program.modules.direct_to_id(module));

        let signature = self.generic_signature(&a[0])?;

        let function = FunEnt {
            visibility,
            name,
            module,
            token_hint: a[0].token.clone(),
            kind: FKind::Generic(signature),
            ast: a_ref,
            attribute_id,
            body: Default::default(),
        };

        self.program
            .generic_functions
            .get_mut_or(name, Vec::new())
            .push(function);

        Ok(self.program.generic_functions.id_to_direct(name).unwrap())
    }

    fn collect_normal_function(
        &mut self,
        module: Module,
        a_ref: AstRef,
        a: &Ast,
        mut name: ID,
        visibility: Vis,
        attribute_id: usize,
    ) -> Result<Fun> {
        let mut args = Vec::new();
        let header = &a[0];
        for param_line in &header[1..header.len() - 1] {
            let datatype = param_line.last().unwrap();
            let datatype = self.resolve_type_low(module, datatype)?;
            name = name.combine(self.program.types.direct_to_id(datatype));
            for param in param_line[0..param_line.len() - 1].iter() {
                let name = ID::new().add(param.token.spam.deref());
                let mutable = param_line.kind == AKind::FunArgument(true);
                args.push(ValueEnt {
                    name,
                    datatype,
                    mutable,
                    type_dependency: None,
                    value: None,
                    on_stack: false,
                });
            }
        }

        name = name.combine(self.program.modules.direct_to_id(module));
        let return_type = header.last().unwrap();
        let return_type = if return_type.kind == AKind::None {
            None
        } else {
            Some(self.resolve_type_low(module, return_type)?)
        };

        let function_signature = FunSignature { args, return_type };

        let token_hint = header.token.clone();

        let function = FunEnt {
            visibility,
            name,
            module,
            token_hint: token_hint.clone(),
            kind: FKind::Normal(function_signature),
            attribute_id,
            ast: a_ref,
            body: Default::default(),
        };

        let id = match self.program.functions.insert(name, function) {
            (Some(function), _) => {
                return Err(FunError::new(
                    FEKind::Duplicate(function.token_hint),
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
                .push(ID::new().add(ident.token.spam.deref()))
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
        let id = self.program.types.direct_to_id(datatype);

        if dt.params.is_empty() {
            generic
                .arg_buffer
                .push(GenericElement::Element(id, Some(datatype)));
            return;
        }

        generic.arg_buffer.push(GenericElement::Element(
            self.program.types.direct_to_id(dt.params[0]),
            Some(datatype),
        ));

        for &param in &dt.params[1..] {
            self.load_arg_from_datatype(param, generic)
        }
    }

    fn load_arg(&mut self, ast: &Ast) -> Result {
        match &ast.kind {
            AKind::Identifier => {
                let id = ID::new().add(ast.token.spam.deref());
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
                    let datatype = self.program.types.direct_to_id(datatype);
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
            _ => todo!("{}", ast),
        }

        Ok(())
    }

    fn resolve_type(&mut self, ast: &Ast) -> Result<Type> {
        self.resolve_type_low(self.context.current_module.unwrap(), ast)
    }

    fn resolve_type_low(&mut self, module: Module, ast: &Ast) -> Result<Type> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .resolve_immediate(module, ast)
            .map_err(Into::into)
    }

    fn find_type(&mut self, token: &Token) -> Result<Type> {
        self.find_type_low(self.context.current_module.unwrap(), token)
    }

    fn find_type_low(&mut self, module: Module, token: &Token) -> Result<Type> {
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
        self.program.builtin_repo.auto == datatype || self.program[datatype].kind == TKind::Generic
    }
}

#[derive(Debug)]
pub struct FunResolverContext {
    pub generic: GenericFunContext,
    pub call_value_buffer: Vec<Value>,
    pub function_ast: LockedSymVec<AstRef, Ast>,
    pub graph_frontier: Vec<(Value, Type)>,
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
            function_ast: LockedSymVec::default(),
            call_value_buffer: Vec::new(),
            generic: Default::default(),
            graph_frontier: vec![],
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
    pub current_module: Option<Module>,
    pub current_block: Option<Block>,
    pub current_instruction: Option<Inst>,
    pub variables: Vec<Option<Value>>,
    pub type_graph: SymVec<TypeDep, Vec<Inst>>,
    pub unresolved_functions: Vec<Fun>,
    pub type_graph_pool: Vec<Vec<Inst>>,
    pub function_body: FunBody,
}

impl FunContext {
    pub fn add_variable(&mut self, val: ValueEnt) -> Value {
        let val = self.function_body.values.add(val);
        self.variables.push(Some(val));
        val
    }

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
        self.variables.clear();
        self.function_body.clear();

        while let Some(garbage) = self.type_graph.pop() {
            self.type_graph_pool.push(garbage);
        }
    }

    pub fn add_instruction(&mut self, instruction: InstEnt) -> Inst {
        debug_assert!(
            self.current_block.is_some(),
            "no block to add instruction to"
        );
        let closing = instruction.kind.is_closing();
        let inst = self.function_body.instructions.add(instruction);
        self.current_instruction = Some(inst);
        if closing {
            self.close_block();
        }
        inst
    }

    pub fn new_block(&mut self) -> Block {
        self.function_body.blocks.add(Default::default())
    }

    pub fn make_block_current(&mut self, block: Block) {
        self.function_body.blocks[block].first_instruction =
            self.current_instruction.map(|i| Inst::new(i.raw() + 1));
        self.current_block = Some(block);
    }

    pub fn close_block(&mut self) {
        if let Some(block) = self.current_block {
            self.function_body.blocks[block].last_instruction = self.current_instruction;
            self.current_block = None;
        } else {
            panic!("no block to close");
        }
    }

    pub fn new_type_dependency(&mut self) -> TypeDep {
        let mut value = self.type_graph_pool.pop().unwrap_or_default();
        value.push(Inst::new(0));
        let value = self.type_graph.add(value);
        value
    }
}

impl Index<Block> for FunContext {
    type Output = BlockEnt;

    fn index(&self, val: Block) -> &Self::Output {
        &self.function_body.blocks[val]
    }
}

impl IndexMut<Block> for FunContext {
    fn index_mut(&mut self, val: Block) -> &mut Self::Output {
        &mut self.function_body.blocks[val]
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
        &self.function_body.instructions[val]
    }
}

impl IndexMut<Inst> for FunContext {
    fn index_mut(&mut self, val: Inst) -> &mut Self::Output {
        &mut self.function_body.instructions[val]
    }
}

#[derive(Debug)]
pub struct FunError {
    pub kind: FEKind,
    pub token: Token,
}

impl FunError {
    pub fn new(kind: FEKind, token: &Token) -> Self {
        FunError {
            kind,
            token: token.clone(),
        }
    }
}

#[derive(Debug)]
pub enum FEKind {
    TypeError(TEKind),
    Duplicate(Token),
    ExpectedValue,
    TypeMismatch(Type, Type),
    NotFound,
    UnexpectedValue,
    UnexpectedReturnValue,
    UndefinedVariable,
    UnresolvedType(TypeDep),
    MissingElseBranch,
}

impl Into<FunError> for TypeError {
    fn into(self) -> FunError {
        FunError {
            kind: FEKind::TypeError(self.kind),
            token: self.token,
        }
    }
}

pub fn test() {
    let builder = ModuleTreeBuilder::default();
    let mut program = builder.build("src/ir/tests/module_tree/root").unwrap();

    let mut ctx = TypeResolverContext::default();

    TypeResolver::new(&mut program, &mut ctx).resolve().unwrap();

    let mut ctx = FunResolverContext::default();

    FunResolver::new(&mut program, &mut ctx).resolve().unwrap();

    for fun in unsafe { program.functions.direct_ids() } {
        if !program.functions.is_direct_valid(fun)
            || !matches!(program.functions[fun].kind, FKind::Normal(_))
        {
            continue;
        }

        let fun = &program.functions[fun];

        println!("{}", fun.token_hint.spam.deref());

        for (id, block) in fun.body.blocks.iter() {
            println!("  {}{:?}:", id, block.args);
            for inst in (block.first_instruction.map(|i| i.raw()).unwrap_or(0)
                ..=block.last_instruction.unwrap().raw())
                .map(|i| &fun.body.instructions[Inst::new(i)])
            {
                if let Some(value) = inst.value {
                    println!(
                        "    {:?}: {} = {:?} |{}",
                        value,
                        program[fun.body.values[value].datatype]
                            .token_hint
                            .spam
                            .deref(),
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
