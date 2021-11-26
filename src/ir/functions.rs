use std::ops::{Deref, DerefMut, Index, IndexMut};

use crate::ast::{AKind, Ast};
use crate::ir::{
    Chunk, FKind, Fun, FunBody, FunEnt, Inst, LTKind, Module, Type, TypeDep, Value, ValueEnt,
};
use crate::lexer::Token;
use crate::util::{
    sdbm::{SdbmHashState, ID},
    sym_table::{SymID, SymVec},
};

use super::module_tree::ModuleTreeBuilder;
use super::types::{TEKind, TypeError, TypeResolver, TypeResolverContext};
use super::{FunSignature, IKind, InstEnt, Program};

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
            self.translate_function(function)?;
        }

        Ok(())
    }

    fn translate_function(&mut self, function: Fun) -> Result {
        let fun = &mut self.program.functions[function];

        let signature = match &mut fun.kind {
            FKind::Normal(signature) => std::mem::take(signature),
            _ => unreachable!(),
        };

        let ast = std::mem::take(&mut fun.ast);

        let module = fun.module;

        self.translate_function_low(module, &ast, &signature)?;

        let fun = &mut self.program.functions[function];
        fun.kind = FKind::Normal(signature);
        fun.ast = ast;
        fun.body = self.context.function_body.clone();
        self.context.function_body.clear();

        Ok(())
    }

    fn translate_function_low(
        &mut self,
        module: Module,
        ast: &Ast,
        signature: &FunSignature,
    ) -> Result {
        self.context.current_module = module;
        self.context.return_type = signature.return_type;
        let entry_point = self.context.new_chunk();
        self.context.make_chunk_current(entry_point);

        signature.params.iter().for_each(|param| {
            let var = self.context.function_body.values.add(param.clone());
            self.context.variables.push(var);
        });

        self.translate_block(&ast[1])?;

        for (id, dep) in self.context.type_graph.iter() {
            if dep.len() > 0 {
                return Err(FunError::new(FEKind::UnresolvedType(id), &Token::default()));
            }
        }

        Ok(())
    }

    fn translate_block(&mut self, ast: &Ast) -> Result<Value> {
        if ast.is_empty() {
            return Ok(Value::NULL);
        }

        self.start_scope();

        for statement in ast[..ast.len() - 1].iter() {
            self.translate_statement(statement)?;
        }

        let value = self.translate_statement(ast.last().unwrap());

        self.pop_scope();

        value
    }

    fn translate_statement(&mut self, statement: &Ast) -> Result<Value> {
        match statement.kind {
            AKind::VarStatement(_) => self.translate_var_statement(statement)?,
            AKind::ReturnStatement => self.translate_return_statement(statement)?,
            AKind::IfExpression => todo!(),
            AKind::Loop => todo!(),
            AKind::Break => todo!(),
            AKind::Continue => todo!(),
            _ => return self.translate_expression(statement),
        }

        Ok(Value::NULL)
    }

    fn translate_return_statement(&mut self, ast: &Ast) -> Result {
        let datatype = self.context.return_type;

        let value = if ast[0].kind == AKind::None {
            if datatype.is_null() {
                Value::NULL
            } else {
                let temp_value = self.new_value(datatype);

                self.context.add_instruction(InstEnt::new(
                    IKind::ZeroValue,
                    temp_value,
                    &Token::default(),
                    0,
                ));
                temp_value
            }
        } else {
            if datatype.is_null() {
                return Err(FunError::new(FEKind::UnexpectedReturnValue, &ast[0].token));
            }
            let value = self.translate_expression(&ast[0])?;
            let actual_type = self.context[value].datatype;
            if self.is_auto(actual_type) {
                self.infer(value, datatype)?;
            } else {
                self.assert_type(actual_type, datatype, &ast[0])?;
            }

            value
        };

        self.context
            .add_instruction(InstEnt::new(IKind::Return, value, &ast[0].token, 0));

        Ok(())
    }

    fn translate_var_statement(&mut self, statement: &Ast) -> Result {
        let mutable = statement.kind == AKind::VarStatement(true);

        for var_line in statement.iter() {
            let datatype = if var_line[1].kind == AKind::None {
                self.auto()
            } else {
                self.resolve_datatype(&var_line[1])?
            };

            if var_line[2].kind == AKind::None {
                for name in var_line[0].iter() {
                    let name = ID::new().add(name.token.spam.deref());

                    let temp_value = self
                        .context
                        .function_body
                        .values
                        .add(ValueEnt::temp(datatype));

                    let unresolved = self.is_auto(datatype) as usize;

                    let inst = self.context.add_instruction(InstEnt::new(
                        IKind::ZeroValue,
                        temp_value,
                        &Token::default(),
                        unresolved,
                    ));

                    let dep = if unresolved == 0 {
                        TypeDep::NULL
                    } else {
                        let dep = self.context.new_type_dependency();
                        self.context[dep].push(inst);
                        dep
                    };

                    let var = ValueEnt {
                        name,
                        datatype,
                        mutable,
                        type_dependency: dep,
                        ..Default::default()
                    };

                    let var = self.context.add_variable(var);

                    self.context.add_instruction(InstEnt::new(
                        IKind::VarDecl(temp_value),
                        var,
                        &var_line.token,
                        unresolved,
                    ));
                }
            } else {
                for (name, raw_value) in var_line[0].iter().zip(var_line[2].iter()) {
                    let name = ID::new().add(name.token.spam.deref());
                    let value = self.translate_expression_unwrap(raw_value)?;
                    let actual_datatype = self.context[value].datatype;

                    if !self.is_auto(datatype) {
                        if self.is_auto(actual_datatype) {
                            self.infer(value, datatype)?;
                        } else {
                            self.assert_type(actual_datatype, datatype, raw_value)?;
                        }
                    }

                    let unresolved = actual_datatype.is_null() as usize;

                    let dep = if unresolved == 0 {
                        TypeDep::NULL
                    } else {
                        self.context.new_type_dependency()
                    };

                    let var = ValueEnt {
                        name,
                        datatype: actual_datatype,
                        mutable,

                        type_dependency: dep,

                        ..Default::default()
                    };

                    let var = self.context.add_variable(var);

                    let inst = self.context.add_instruction(InstEnt::new(
                        IKind::VarDecl(value),
                        var,
                        &var_line.token,
                        unresolved,
                    ));

                    if unresolved != 0 {
                        self.add_type_dependency(value, inst);
                    }
                }
            }
        }

        Ok(())
    }

    fn translate_expression_unwrap(&mut self, ast: &Ast) -> Result<Value> {
        let value = self.translate_expression(ast)?;
        if value.is_null() {
            Err(FunError::new(FEKind::ExpectedValueue, &ast.token))
        } else {
            Ok(value)
        }
    }

    fn translate_expression(&mut self, ast: &Ast) -> Result<Value> {
        match ast.kind {
            AKind::BinaryOperation => self.translate_binary_operation(ast),
            AKind::Literal => self.translate_literal(ast),
            AKind::Identifier => self.translate_identifier(ast),
            _ => todo!("unmatched expression ast {}", ast),
        }
    }

    fn translate_identifier(&mut self, ast: &Ast) -> Result<Value> {
        let name = ID::new().add(ast.token.spam.deref());
        self.context
            .find_variable(name)
            .ok_or_else(|| FunError::new(FEKind::UndefinedVariable, &ast.token))
    }

    fn translate_literal(&mut self, ast: &Ast) -> Result<Value> {
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
            value,
            &ast.token,
            0,
        ));

        Ok(value)
    }

    fn translate_binary_operation(&mut self, ast: &Ast) -> Result<Value> {
        if ast[0].token.spam.deref() == "=" {
            return Ok(self.translate_assignment(ast)?);
        }

        let left = self.translate_expression_unwrap(&ast[1])?;
        let right = self.translate_expression_unwrap(&ast[2])?;

        let base_id = ID::new().add(ast[0].token.spam.deref());

        let left_datatype = self.context[left].datatype;
        let right_datatype = self.context[right].datatype;

        let unresolved =
            self.is_auto(left_datatype) as usize + self.is_auto(right_datatype) as usize;
        if unresolved > 0 {
            let value = self.new_auto_value();

            let inst = self.context.add_instruction(InstEnt::new(
                IKind::UnresolvedCall(base_id, vec![left, right]),
                value,
                &ast.token,
                unresolved,
            ));

            if self.is_auto(left_datatype) {
                self.add_type_dependency(left, inst);
            }

            if self.is_auto(right_datatype) {
                self.add_type_dependency(right, inst);
            }

            Ok(value)
        } else {
            let specific_id = base_id
                .combine(self.program.types.direct_to_id(left_datatype))
                .combine(self.program.types.direct_to_id(right_datatype));

            let function = self.find_or_instantiate(base_id, specific_id, &ast.token)?;

            let ret_type = self.program[function].signature().return_type;

            let return_type = if ret_type.is_null() {
                Value::NULL
            } else {
                self.new_value(ret_type)
            };

            self.context.add_instruction(InstEnt::new(
                IKind::Call(function, vec![left, right]),
                return_type,
                &ast.token,
                0,
            ));

            Ok(return_type)
        }
    }

    fn infer(&mut self, value: Value, datatype: Type) -> Result<()> {
        let val = &mut self.context[value];
        val.datatype = datatype;
        let dependency_id = val.type_dependency;
        let mut dependencies = std::mem::take(&mut self.context[dependency_id]);
        for dep in dependencies.drain(..) {
            let inst = &mut self.context[dep];
            inst.unresolved -= 1;
            if inst.unresolved != 0 {
                continue;
            }

            match &mut inst.kind {
                IKind::VarDecl(_) => {
                    let value = inst.value;
                    self.infer(value, datatype)?;
                }
                IKind::UnresolvedCall(base_id, args) => {
                    let args = std::mem::take(args);
                    let mut id = *base_id;
                    for arg in &args {
                        id = id
                            .combine(self.program.types.direct_to_id(self.context[*arg].datatype));
                    }

                    let (_, fun) = self.find_by_name(id).ok_or_else(|| {
                        FunError::new(FEKind::NotFound, &self.context[dep].token_hint)
                    })?;

                    let inst = &mut self.context[dep];
                    inst.kind = IKind::Call(fun, args);
                    let value = inst.value;
                    let datatype = self.program[fun].signature().return_type;

                    self.infer(value, datatype)?;
                }
                IKind::ZeroValue => {
                    let value = inst.value;
                    self.context[value].datatype = datatype;
                }
                IKind::Assign(val) => {
                    let val = *val;
                    if value == val {
                        let other_id = inst.value;
                        self.infer(other_id, datatype)?;
                    } else {
                        self.infer(val, datatype)?;
                    }
                }
                _ => todo!("{:?}", inst),
            }
        }

        self.context[dependency_id] = dependencies;

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
            self.context[value].type_dependency = dep;
        }
        value
    }

    fn translate_assignment(&mut self, ast: &Ast) -> Result<Value> {
        let target = self.translate_expression_unwrap(&ast[1])?;
        let value = self.translate_expression_unwrap(&ast[2])?;
        let target_datatype = self.context[target].datatype;
        let value_datatype = self.context[value].datatype;

        let unresolved = if self.is_auto(target_datatype) {
            if !self.is_auto(value_datatype) {
                self.infer(target, value_datatype)?;
                0
            } else {
                2
            }
        } else {
            if self.is_auto(value_datatype) {
                self.infer(value, target_datatype)?;
            } else {
                self.assert_type(value_datatype, target_datatype, ast)?;
            }
            0
        };

        let inst = self.context.add_instruction(InstEnt::new(
            IKind::Assign(target),
            value,
            &ast.token,
            unresolved,
        ));

        if unresolved == 2 {
            self.add_type_dependency(value, inst);
            self.add_type_dependency(target, inst);
        }

        Ok(value)
    }

    fn find_or_instantiate(&mut self, base: ID, specific_id: ID, token: &Token) -> Result<Fun> {
        if let Some((_, fun)) = self.find_by_name(specific_id) {
            return Ok(fun);
        }

        if let Some(_fun) = self.find_generic_by_name(base) {
            todo!();
        }

        Err(FunError::new(FEKind::NotFound, token))
    }

    fn find_by_name(&mut self, name: ID) -> Option<(Module, Fun)> {
        self.program
            .walk_accessible_scopes(self.context.current_module, |id, module| {
                self.program
                    .functions
                    .id_to_direct(name.combine(id))
                    .map(|fun| (module, fun))
            })
    }

    fn find_generic_by_name(&mut self, name: ID) -> Option<(Module, Fun)> {
        self.program
            .walk_accessible_scopes(self.context.current_module, |id, module| {
                self.program
                    .generic_functions
                    .id_to_direct(name.combine(id))
                    .map(|fun| (module, fun))
            })
    }

    fn assert_type(&self, actual: Type, expected: Type, ast: &Ast) -> Result {
        if actual == expected {
            Ok(())
        } else {
            Err(FunError::new(
                FEKind::TypeMismatch(actual, expected),
                &ast.token,
            ))
        }
    }

    fn add_type_dependency(&mut self, value: Value, inst: Inst) {
        let dependency_id = self.context[value].type_dependency;
        self.context[dependency_id].push(inst);
    }

    fn start_scope(&mut self) {
        self.context.variables.push(Value::NULL);
    }

    fn pop_scope(&mut self) {
        let i = self.context.variables.len()
            - 1
            - self
                .context
                .variables
                .iter()
                .rev()
                .position(|v| v.is_null())
                .unwrap();
        self.context.variables.truncate(i);
    }

    fn collect(&mut self) -> Result {
        for module in unsafe { self.program.modules.direct_ids() } {
            if !self.program.modules.is_direct_valid(module) {
                continue;
            }

            let mut ast = std::mem::take(&mut self.program.modules[module].ast);
            for (i, a) in ast.iter_mut().enumerate() {
                match a.kind.clone() {
                    AKind::Fun(visibility) => {
                        let header = &a[0];
                        match header[0].kind {
                            AKind::Identifier => {
                                let mut name = ID::new().add(header.token.spam.deref());
                                let mut params = Vec::new();
                                for param_line in &a[1..a.len() - 1] {
                                    let datatype = param_line.last().unwrap();
                                    let datatype = self.resolve_datatype_low(module, datatype)?;
                                    name = name.combine(self.program.types.direct_to_id(datatype));
                                    for param in param_line[0..param_line.len() - 1].iter() {
                                        let name = ID::new().add(param.token.spam.deref());
                                        let mutable = param_line.kind == AKind::FunArgument(true);
                                        params.push(ValueEnt {
                                            name,
                                            datatype,
                                            mutable,

                                            ..Default::default()
                                        });
                                    }
                                }
                                name = name.combine(self.program.modules.direct_to_id(module));
                                let return_type = header.last().unwrap();
                                let return_type = if return_type.kind == AKind::None {
                                    Type::NULL
                                } else {
                                    self.resolve_datatype_low(module, return_type)?
                                };

                                let function_signature = FunSignature {
                                    params,
                                    return_type,
                                };

                                let token_hint = header.token.clone();

                                let function = FunEnt {
                                    visibility,
                                    name,
                                    module,
                                    hint_token: token_hint.clone(),
                                    kind: FKind::Normal(function_signature),
                                    ast: std::mem::take(a),
                                    attribute_id: i,

                                    ..Default::default()
                                };

                                if let (Some(function), _) =
                                    self.program.functions.insert(name, function)
                                {
                                    return Err(FunError::new(
                                        FEKind::Duplicate(function.hint_token),
                                        &token_hint,
                                    ));
                                }
                            }
                            AKind::Instantiation => {
                                let name = ID::new()
                                    .add(header[0].token.spam.deref())
                                    .combine(self.program.modules.direct_to_id(module));

                                let function = FunEnt {
                                    visibility,
                                    name,
                                    module,
                                    hint_token: header.token.clone(),
                                    kind: FKind::Generic,
                                    ast: std::mem::take(a),
                                    attribute_id: i,

                                    ..Default::default()
                                };

                                self.program
                                    .generic_functions
                                    .get_mut_or_default(name)
                                    .push(function);
                            }
                            _ => unreachable!("{}", a),
                        }
                    }
                    _ => (),
                }
            }
            self.program.modules[module].ast = ast;
        }

        Ok(())
    }

    fn resolve_datatype(&mut self, ast: &Ast) -> Result<Type> {
        self.resolve_datatype_low(self.context.current_module, ast)
    }

    fn resolve_datatype_low(&mut self, module: Module, ast: &Ast) -> Result<Type> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .resolve_immediate(module, ast)
            .map_err(Into::into)
    }

    #[inline]
    fn auto(&self) -> Type {
        self.program.builtin_repo.auto
    }

    #[inline]
    fn is_auto(&self, datatype: Type) -> bool {
        self.program.builtin_repo.auto == datatype
    }
}

#[derive(Debug)]
pub struct FunResolverContext {
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

#[derive(Debug, Default)]
pub struct FunContext {
    pub return_type: Type,
    pub current_module: Module,
    pub current_chunk: Chunk,
    pub current_instruction: Inst,
    pub variables: Vec<Value>,
    pub type_graph: SymVec<TypeDep, Vec<Inst>>,
    pub type_graph_pool: Vec<Vec<Inst>>,
    pub function_body: FunBody,
}

impl FunContext {
    pub fn add_variable(&mut self, val: ValueEnt) -> Value {
        let val = self.function_body.values.add(val);
        self.variables.push(val);
        val
    }

    pub fn find_variable(&mut self, name: ID) -> Option<Value> {
        self.variables
            .iter()
            .rev()
            .find(|&&val| self.function_body.values[val].name == name)
            .cloned()
    }

    pub fn clear(&mut self) {
        self.current_module = Module::NULL;
        self.current_chunk = Chunk::NULL;
        self.variables.clear();
        self.function_body.clear();

        while let Some(garbage) = self.type_graph.pop() {
            self.type_graph_pool.push(garbage);
        }
    }

    pub fn add_instruction(&mut self, instruction: InstEnt) -> Inst {
        debug_assert!(
            !self.current_chunk.is_null(),
            "no chunk to add instruction to"
        );
        self.function_body.instructions.add(instruction)
    }

    pub fn new_chunk(&mut self) -> Chunk {
        self.function_body.chunks.add(Default::default())
    }

    pub fn make_chunk_current(&mut self, chunk: Chunk) {
        self.function_body.chunks[chunk].first_instruction = if self.current_instruction.is_null() {
            Inst::new(0)
        } else {
            self.current_instruction
        };
        self.current_chunk = chunk;
    }

    pub fn close_chunk(&mut self) {
        debug_assert!(!self.current_chunk.is_null(), "no chunk to close");
        self.function_body.chunks[self.current_chunk].last_instruction = self.current_instruction;
        self.current_chunk = Chunk::NULL;
    }

    pub fn new_type_dependency(&mut self) -> TypeDep {
        let value = self.type_graph_pool.pop().unwrap_or_default();
        let value = self.type_graph.add(value);
        value
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
    ExpectedValueue,
    TypeMismatch(Type, Type),
    NotFound,
    UnexpectedReturnValue,
    UndefinedVariable,
    UnresolvedType(TypeDep),
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
}
