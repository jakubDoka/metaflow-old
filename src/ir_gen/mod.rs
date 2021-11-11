pub mod gen;

use cranelift_codegen::{
    ir::{
        condcodes::{FloatCC, IntCC},
        types::*,
        AbiParam, ExternalName, Function, InstBuilder, Signature, Type, Value,
    },
    isa::CallConv,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Linkage;
use std::{cell::RefCell, ops::Deref, rc::Rc, str::FromStr};

use crate::{
    ast::{AEKind, AKind, Ast, AstError, AstParser},
    lexer::{Lexer, StrRef, TKind, Token},
};

type CraneContext = cranelift_codegen::Context;
type Result<T> = std::result::Result<T, IrGenError>;

pub struct Generator {
    builtin_repo: BuiltinRepo,
    builtin_module: Mod,
    context: Context,
    current_module: Mod,
    function_builder_context: Option<FunctionBuilderContext>,
    variables: Vec<Option<Var>>,
    variable_counter: u32,
    module_id_counter: u32,
    global_attributes: Vec<Ast>,
    pushed_attributes: Vec<Ast>,
}

impl Generator {
    fn new() -> Self {
        let builtin_repo = BuiltinRepo::new();
        let builtin_module = builtin_repo.to_module();
        Self {
            current_module: builtin_module.clone(), // just an place holder
            builtin_repo,
            builtin_module,
            context: Context::new(),
            function_builder_context: Some(FunctionBuilderContext::new()),
            variables: Vec::new(),
            variable_counter: 0,
            module_id_counter: 0,
            global_attributes: Vec::new(),
            pushed_attributes: Vec::new(),
        }
    }

    fn generate(mut self, root_file_name: &str) -> Result<Context> {
        self.generate_module(root_file_name.to_string())?;

        Ok(self.context)
    }

    fn generate_module(&mut self, module_path: String) -> Result<Mod> {
        let mut ast = self.load_ast(module_path)?;

        self.module_id_counter += 1; // the 0 is for builtin module
        self.current_module = Mod::new(
            ast.token.line_data.file_name.to_string(),
            self.module_id_counter,
        );
        self.current_module
            .borrow_mut()
            .dependency
            .push(self.builtin_module.clone());
        for mut item in ast.drain(..) {
            match item.kind {
                AKind::Function => {
                    self.function(&item)?;
                    self.pushed_attributes.clear();
                }
                AKind::Attribute => match item[0].token.value.deref() {
                    "push" => {
                        self.global_attributes.push(Ast::none());
                        item.drain(..)
                            .for_each(|item| self.global_attributes.push(item));
                    }
                    "pop" => {
                        self.global_attributes.drain(
                            self.global_attributes
                                .iter()
                                .rev()
                                .position(|e| e.kind == AKind::None)
                                .unwrap()..,
                        );
                    }
                    _ => {
                        item.drain(..)
                            .for_each(|item| self.pushed_attributes.push(item));
                    }
                },
                _ => todo!(),
            }
        }

        self.context.add_module(self.current_module.clone())?;

        Ok(self.current_module.clone())
    }

    fn function(&mut self, ast: &Ast) -> Result<()> {
        self.variable_counter = 0;
        self.variables.clear();
        let mut function_builder_context =
            std::mem::take(&mut self.function_builder_context).unwrap();

        let signature_ast = &ast[0];
        let (signature, mut fun_signature) =
            self.create_signature(signature_ast)?;

        let mut function = Function::with_name_signature(fun_signature.id.clone(), signature);
        let mut builder = FunctionBuilder::new(&mut function, &mut function_builder_context);
        let fun = if ast[1].len() > 0 {
            let entry_point = builder.create_block();
            builder.append_block_params_for_function_params(entry_point);
            for (param, sig_param) in builder
                .block_params(entry_point)
                .iter()
                .zip(fun_signature.params.iter_mut())
            {
                sig_param.access = VarAccess::Immutable(param.clone());
            }

            self.variables
                .extend(fun_signature.params.iter().map(|i| Some(i.clone())));
            let fun = Fun::new(fun_signature);
            self.current_module.borrow_mut().add_function(fun.clone())?;

            builder.switch_to_block(entry_point);
            self.generate_function_body(&ast[1], &mut builder)?;
            builder.seal_current_block();
            fun
        } else {
            let entry_point = builder.create_block();
            builder.append_block_params_for_function_params(entry_point);
            builder.switch_to_block(entry_point);
            if let Some(ret) = fun_signature.ret.as_ref() {
                let val = ret.borrow().default_value(&mut builder);
                builder.ins().return_(&[val]);
            }
            builder.seal_current_block();
            let fun = Fun::new(fun_signature);
            self.current_module.borrow_mut().add_function(fun.clone())?;
            fun
        };

        builder.finalize();

        fun.borrow_mut().function = Some(function);

        self.function_builder_context = Some(function_builder_context);

        Ok(())
    }

    fn generate_function_body(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        self.statement_list(ast, builder)?;
        Ok(())
    }

    fn statement_list(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<Option<(Value, Datatype)>> {
        for stmt in ast[0..ast.len() - 1].iter() {
            self.statement(stmt, builder)?;
        }

        if let Some(last) = ast.last() {
            return self.statement(last, builder);
        }

        Ok(None)
    }

    fn statement(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<Option<(Value, Datatype)>> {
        match ast.kind {
            AKind::ReturnStatement => {
                self.return_statement(ast, builder)?;
            }
            AKind::IfExpression => {
                self.if_expression(ast, builder)?;
            }
            _ => {
                return Ok(Some(self.expression(ast, builder)?));
            }
        }

        Ok(None)
    }

    fn return_statement(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        let ret_expr = &ast[0];

        let ret_value = self.expression(ret_expr, builder)?;

        builder.ins().return_(&[ret_value.0]);

        Ok(())
    }

    fn expression(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<(Value, Datatype)> {
        match ast.kind {
            AKind::Literal => self.literal(ast, builder),
            AKind::BinaryOperation => self.binary_operation(ast, builder),
            AKind::IfExpression => self
                .if_expression(ast, builder)?
                .ok_or_else(|| IrGenError::new(IGEKind::ExpectedValue, ast.token.clone())),
            _ => todo!("unmatched expression {}", ast),
        }
    }

    fn literal(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<(Value, Datatype)> {
        match ast.token.kind {
            TKind::Int(value, bits) => {
                let datatype = match bits {
                    8 => self.builtin_repo.i8.clone(),
                    16 => self.builtin_repo.i16.clone(),
                    32 => self.builtin_repo.i32.clone(),
                    64 => self.builtin_repo.i64.clone(),
                    _ => unreachable!(),
                };
                let value = builder
                    .ins()
                    .iconst(datatype.borrow().get_ir_repr(), value as i64);
                Ok((value, datatype))
            }
            TKind::Bool(value) => {
                let datatype = self.builtin_repo.bool.clone();
                let value = builder.ins().bconst(datatype.borrow().get_ir_repr(), value);
                Ok((value, datatype))
            }
            _ => todo!(),
        }
    }

    fn if_expression(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<Option<(Value, Datatype)>> {
        let cond_expr = &ast[0];
        let (cond_value, cond_type) = self.expression(cond_expr, builder)?;

        self.assert_type(cond_expr, &cond_type, &self.builtin_repo.bool)?;

        let then_block = builder.create_block();
        builder.ins().brnz(cond_value, then_block, &[]);

        let merge_block = builder.create_block();

        let else_branch = &ast[2];
        let else_block = if else_branch.kind == AKind::None {
            builder.ins().jump(merge_block, &[]);
            None
        } else {
            let else_block = builder.create_block();
            builder.ins().jump(else_block, &[]);
            Some(else_block)
        };

        builder.seal_current_block();

        let then_branch = &ast[1];

        builder.switch_to_block(then_block);
        let then_result = self.statement_list(then_branch, builder)?;

        let mut result = None;
        if let Some((value, datatype)) = then_result {
            let val = builder.append_block_param(merge_block, datatype.borrow().get_ir_repr());
            result = Some((val, datatype));
            builder.ins().jump(merge_block, &[value]);
        } else if !builder.is_filled() {
            builder.ins().jump(merge_block, &[]);
        }

        builder.seal_current_block();

        match else_branch.kind {
            AKind::None => {
                if result.is_some() {
                    return Err(IrGenError::new(
                        IGEKind::MissingElseBranch,
                        ast.token.clone(),
                    ));
                }
                builder.switch_to_block(merge_block);
            }
            AKind::IfExpression | AKind::Group => {
                let else_block = else_block.unwrap();

                builder.switch_to_block(else_block);
                let else_result = match else_branch.kind {
                    AKind::IfExpression => self.if_expression(else_branch, builder)?,
                    AKind::Group => self.statement_list(else_branch, builder)?,
                    _ => unreachable!(),
                };

                if let Some((value, datatype)) = else_result {
                    if let Some((_, other_datatype)) = result.as_ref() {
                        self.assert_type(ast, &datatype, &other_datatype)?;
                    } else {
                        return Err(IrGenError::new(
                            IGEKind::UnexpectedValueInThenBranch,
                            ast.token.clone(),
                        ));
                    }
                    builder.ins().jump(merge_block, &[value]);
                } else {
                    if result.is_some() {
                        return Err(IrGenError::new(
                            IGEKind::MissingValueInElseBranch,
                            ast.token.clone(),
                        ));
                    }
                    if !builder.is_filled() {
                        builder.ins().jump(merge_block, &[]);
                    }
                }

                builder.seal_current_block();
            }
            _ => unreachable!(),
        }

        builder.switch_to_block(merge_block);

        Ok(result)
    }

    fn binary_operation(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<(Value, Datatype)> {
        let (left_val, left_type) = self.expression(&ast[1], builder)?;
        let (right_val, right_type) = self.expression(&ast[2], builder)?;

        if left_type == right_type {
            let op = ast[0].token.value.deref();
            let value = match left_type.borrow().name.as_str() {
                "i8" | "i16" | "i32" | "i64" => match op {
                    "+" => builder.ins().iadd(left_val, right_val),
                    "-" => builder.ins().isub(left_val, right_val),
                    "*" => builder.ins().imul(left_val, right_val),
                    "/" => builder.ins().sdiv(left_val, right_val),
                    "%" => builder.ins().srem(left_val, right_val),
                    "&" => builder.ins().band(left_val, right_val),
                    "|" => builder.ins().bor(left_val, right_val),
                    "^" => builder.ins().bxor(left_val, right_val),
                    "<<" => builder.ins().ishl(left_val, right_val),
                    ">>" => builder.ins().sshr(left_val, right_val),
                    "max" => builder.ins().imax(left_val, right_val),
                    "min" => builder.ins().imin(left_val, right_val),

                    "==" | "!=" | "<" | ">" | ">=" | "<=" => {
                        let op = match op {
                            "==" => IntCC::Equal,
                            "!=" => IntCC::NotEqual,
                            "<" => IntCC::SignedLessThan,
                            ">" => IntCC::SignedGreaterThan,
                            ">=" => IntCC::SignedGreaterThanOrEqual,
                            "<=" => IntCC::SignedLessThanOrEqual,
                            _ => unreachable!(),
                        };

                        let val = builder.ins().icmp(op, left_val, right_val);
                        return Ok((val, self.builtin_repo.bool.clone()));
                    }

                    _ => todo!(),
                },
                "u8" | "u16" | "u32" | "u64" => match op {
                    "+" => builder.ins().iadd(left_val, right_val),
                    "-" => builder.ins().isub(left_val, right_val),
                    "*" => builder.ins().imul(left_val, right_val),
                    "/" => builder.ins().udiv(left_val, right_val),
                    "%" => builder.ins().urem(left_val, right_val),
                    "&" => builder.ins().band(left_val, right_val),
                    "|" => builder.ins().bor(left_val, right_val),
                    "^" => builder.ins().bxor(left_val, right_val),
                    "<<" => builder.ins().ishl(left_val, right_val),
                    ">>" => builder.ins().ushr(left_val, right_val),
                    "max" => builder.ins().umax(left_val, right_val),
                    "min" => builder.ins().umin(left_val, right_val),

                    "==" | "!=" | "<" | ">" | ">=" | "<=" => {
                        let op = match op {
                            "==" => IntCC::Equal,
                            "!=" => IntCC::NotEqual,
                            "<" => IntCC::UnsignedLessThan,
                            ">" => IntCC::UnsignedGreaterThan,
                            ">=" => IntCC::UnsignedGreaterThanOrEqual,
                            "<=" => IntCC::UnsignedLessThanOrEqual,
                            _ => unreachable!(),
                        };

                        let val = builder.ins().icmp(op, left_val, right_val);
                        return Ok((val, self.builtin_repo.bool.clone()));
                    }

                    _ => todo!(),
                },
                "f32" | "f64" => match op {
                    "+" => builder.ins().fadd(left_val, right_val),
                    "-" => builder.ins().fsub(left_val, right_val),
                    "*" => builder.ins().fmul(left_val, right_val),
                    "/" => builder.ins().fdiv(left_val, right_val),
                    "max" => builder.ins().fmax(left_val, right_val),
                    "min" => builder.ins().fmin(left_val, right_val),

                    "==" | "=!" | "<" | ">" | ">=" | "<=" => {
                        let op = match op {
                            "==" => FloatCC::Equal,
                            "!=" => FloatCC::NotEqual,
                            "<" => FloatCC::LessThan,
                            ">" => FloatCC::GreaterThan,
                            ">=" => FloatCC::GreaterThanOrEqual,
                            "<=" => FloatCC::LessThanOrEqual,
                            _ => unreachable!(),
                        };

                        let val = builder.ins().fcmp(op, left_val, right_val);
                        return Ok((val, self.builtin_repo.bool.clone()));
                    }

                    "bool" => match op {
                        "&" => builder.ins().band(left_val, right_val),
                        "|" => builder.ins().bor(left_val, right_val),
                        "||" => todo!(),
                        "&&" => todo!(),
                        _ => todo!(),
                    },

                    _ => todo!(),
                },
                _ => todo!(),
            };
            Ok((value, right_type))
        } else {
            todo!()
        }
    }

    fn create_signature(&self, header: &Ast) -> Result<(Signature, FunSignature)> {
        let mut signature = Signature::new(CallConv::Fast);
        let mut fun_params = Vec::new();
        for args in header[1..header.len() - 1].iter() {
            let datatype = self.find_datatype(&args.last().unwrap().token)?;
            for arg in args[0..args.len() - 1].iter() {
                fun_params.push(Var::new(
                    arg.token.value.clone(),
                    VarAccess::Unresolved,
                    datatype.clone(),
                ));
                signature
                    .params
                    .push(AbiParam::new(datatype.borrow().get_ir_repr()));
            }
        }
        let return_type = header.last().unwrap();
        let return_type = if return_type.kind != AKind::None {
            let datatype = self.find_datatype(&return_type.token)?.clone();
            signature
                .returns
                .push(AbiParam::new(datatype.borrow().get_ir_repr()));
            Some(datatype)
        } else {
            None
        };
        let name = header.first().unwrap();
        let name = if name.kind != AKind::None {
            name.token.value.clone()
        } else {
            StrRef::empty()
        };

        let linkage = if let Some(attr) = self.find_attribute("linkage") {
            match attr[0].token.value.deref() {
                "local" => Linkage::Local,
                "hidden" => Linkage::Hidden,
                "import" => Linkage::Import,
                "export" => Linkage::Export,
                "preemptible" => Linkage::Preemptible,
                _ => return Err(IrGenError::new(IGEKind::InvalidLinkage, attr.token.clone())),
            }
        } else {
            Linkage::Export
        };

        let cc = if let Some(attr) = self.find_attribute("call_conv") {
            CallConv::from_str(attr[0].token.value.deref())
                .map_err(|_| IrGenError::new(IGEKind::InvalidCallConv, attr.token.clone()))?
        } else {
            CallConv::Fast
        };

        let fun_signature = FunSignature::new(
            self.current_module.borrow_mut().new_fun_name(),
            name,
            fun_params,
            return_type,
            cc,
            linkage,
        );

        signature.call_conv = cc;

        Ok((signature, fun_signature))
    }

    fn assert_type(&self, ast: &Ast, actual: &Datatype, expected: &Datatype) -> Result<()> {
        if actual != expected {
            Err(IrGenError::new(
                IGEKind::TypeMismatch(actual.clone(), expected.clone()),
                ast.token.clone(),
            ))
        } else {
            Ok(())
        }
    }

    fn find_datatype(&self, token: &Token) -> Result<Datatype> {
        self.current_module
            .borrow()
            .find_datatype(&token.value)
            .ok_or_else(|| IrGenError::new(IGEKind::TypeNotFound, token.clone()))
    }

    fn find_function(&self, token: &Token) -> Result<Fun> {
        self.current_module
            .borrow()
            .find_function(token)
            .ok_or_else(|| IrGenError::new(IGEKind::FunctionNotFound, token.clone()))
    }

    fn find_variable(&self, token: &Token) -> Result<Var> {
        self.variables
            .iter()
            .rev()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
            .find(|var| &var.name == &token.value)
            .map(|var| var.clone())
            .ok_or_else(|| IrGenError::new(IGEKind::VariableNotFound, token.clone()))
    }

    fn make_variable(&mut self) -> Variable {
        let var = Variable::with_u32(self.variable_counter);
        self.variable_counter += 1;
        var
    }

    fn load_ast(&mut self, file_name: String) -> Result<Ast> {
        let bytes =
            std::fs::read_to_string(&file_name).map_err(|e| IGEKind::CannotOpenFile(e).into())?;
        AstParser::new(Lexer::new(file_name, bytes))
            .parse()
            .map_err(Into::into)
    }

    fn has_attribute(&self, name: &str) -> bool {
        self.find_attribute(name).is_some()
    }

    fn find_attribute(&self, name: &str) -> Option<&Ast> {
        self.global_attributes
            .iter()
            .rev()
            .find(|a| a.token.value.deref() == name)
            .or(self
                .pushed_attributes
                .iter()
                .rev()
                .find(|a| a.token.value.deref() == name))
    }
}

pub struct Context {
    modules: Vec<Mod>,
}

impl Context {
    fn new() -> Self {
        Self {
            modules: Vec::new(),
        }
    }

    fn add_module(&mut self, module: Mod) -> Result<()> {
        match self
            .modules
            .binary_search_by(|d| module.borrow().name.cmp(&d.borrow().name))
        {
            Ok(i) => Err(IGEKind::DuplicateModule(module.clone(), self.modules[i].clone()).into()),
            Err(i) => {
                self.modules.insert(i, module);
                Ok(())
            }
        }
    }

    fn find_module(&self, name: Token) -> Result<Mod> {
        match self
            .modules
            .binary_search_by(|d| name.value.cmp(&d.borrow().name))
        {
            Ok(i) => Ok(self.modules[i].clone()),
            Err(_) => Err(IrGenError::new(IGEKind::ModuleNotFound, name.clone())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Mod {
    inner: Rc<RefCell<ModuleStruct>>,
}

impl Mod {
    fn new(name: String, id: u32) -> Self {
        Self {
            inner: Rc::new(RefCell::new(ModuleStruct::new(name, id))),
        }
    }
}

impl Deref for Mod {
    type Target = RefCell<ModuleStruct>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug, Clone)]
pub struct ModuleStruct {
    name: String,
    dependency: Vec<Mod>,
    types: Vec<Datatype>,
    functions: Vec<Fun>,
    function_id_counter: u32,
    id: u32,
}

impl ModuleStruct {
    fn new(name: String, id: u32) -> Self {
        Self {
            name,
            dependency: vec![],
            types: vec![],
            functions: vec![],
            function_id_counter: 0,
            id,
        }
    }

    fn find_datatype(&self, name: &str) -> Option<Datatype> {
        self.types
            .binary_search_by(|d| name.cmp(&d.borrow().name))
            .ok()
            .map(|i| self.types[i].clone())
            .or_else(|| {
                for dep in self.dependency.iter().rev() {
                    if let Some(d) = dep.borrow().find_datatype(name) {
                        return Some(d);
                    }
                }
                None
            })
    }

    fn add_datatype(&mut self, datatype: Datatype) -> Result<()> {
        match self
            .types
            .binary_search_by(|d| datatype.borrow().name.cmp(&d.borrow().name))
        {
            Ok(i) => Err(IGEKind::DuplicateType(datatype.clone(), self.types[i].clone()).into()),
            Err(i) => {
                self.types.insert(i, datatype);
                Ok(())
            }
        }
    }

    fn add_function(&mut self, fun: Fun) -> Result<()> {
        match self
            .functions
            .binary_search_by(|d| fun.borrow().signature.name.cmp(&d.borrow().signature.name))
        {
            Ok(i) => Err(IGEKind::DuplicateFunction(fun.clone(), self.functions[i].clone()).into()),
            Err(i) => {
                self.functions.insert(i, fun);
                Ok(())
            }
        }
    }

    fn find_function(&self, name: &Token) -> Option<Fun> {
        self.functions
            .binary_search_by(|f| name.value.cmp(&f.borrow().signature.name))
            .ok()
            .map(|i| self.functions[i].clone())
            .or_else(|| {
                for dep in self.dependency.iter().rev() {
                    if let Some(d) = dep.borrow().find_function(name) {
                        return Some(d);
                    }
                }
                None
            })
    }

    fn new_fun_name(&mut self) -> ExternalName {
        let name = ExternalName::user(self.id, self.function_id_counter);
        self.function_id_counter += 1;
        name
    }
}

macro_rules! builtin_repo {
    (types [$($name:ident: $lit:ident $bits:expr,)*]) => {
        pub struct BuiltinRepo {
            $($name: Datatype,)*
        }

        impl BuiltinRepo {
            fn new() -> Self {
                Self {
                    $(
                        $name: Datatype::with_size(
                            stringify!($name).to_string(),
                            DKind::Builtin($lit),
                            $bits
                        ),
                    )*
                }
            }

            fn to_module(&self) -> Mod {
                let module = Mod::new("builtin".to_string(), 0);
                $(
                    module.borrow_mut().add_datatype(self.$name.clone()).unwrap();
                )*
                module
            }
        }
    }
}

builtin_repo!(
    types [
        i8: I8 8,
        i16: I16 16,
        i32: I32 32,
        i64: I64 64,
        u8: I8 8,
        u16: I16 16,
        u32: I32 32,
        u64: I64 64,
        f32: F32 32,
        f64: F64 64,
        bool: B1 1,
    ]
);

#[derive(Debug, Clone)]
pub struct Fun {
    inner: Rc<RefCell<FunStruct>>,
}

impl Fun {
    fn new(signature: FunSignature) -> Self {
        Self {
            inner: Rc::new(RefCell::new(FunStruct::new(signature))),
        }
    }
}

impl Deref for Fun {
    type Target = RefCell<FunStruct>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug, Clone)]
pub struct FunStruct {
    signature: FunSignature,
    function: Option<Function>,
}

impl FunStruct {
    fn new(signature: FunSignature) -> Self {
        Self {
            signature,
            function: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunSignature {
    id: ExternalName,
    name: StrRef,
    params: Vec<Var>,
    ret: Option<Datatype>,
    cc: CallConv,
    linkage: Linkage,
}

impl FunSignature {
    fn new(
        id: ExternalName,
        name: StrRef,
        params: Vec<Var>,
        ret: Option<Datatype>,
        cc: CallConv,
        linkage: Linkage,
    ) -> Self {
        Self {
            id,
            name,
            params,
            ret,
            cc,
            linkage,
        }
    }

    fn to_signature(&self) -> Signature {
        Signature {
            call_conv: self.cc,
            params: self
                .params
                .iter()
                .map(|v| AbiParam::new(v.datatype.borrow().get_ir_repr()))
                .collect(),
            returns: if let Some(ret) = &self.ret {
                vec![AbiParam::new(ret.borrow().get_ir_repr())]
            } else {
                vec![]
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Datatype {
    inner: Rc<RefCell<DatatypeStruct>>,
}

impl Datatype {
    fn new(name: String, kind: DKind) -> Self {
        Self::with_size(name, kind, 0)
    }

    fn with_size(name: String, kind: DKind, size: usize) -> Self {
        Self {
            inner: Rc::new(RefCell::new(DatatypeStruct::with_size(name, kind, size))),
        }
    }
}

impl Deref for Datatype {
    type Target = RefCell<DatatypeStruct>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug, Clone)]
pub struct Var {
    name: StrRef,
    access: VarAccess,
    datatype: Datatype,
}

impl Var {
    fn new(name: StrRef, access: VarAccess, datatype: Datatype) -> Self {
        Self {
            datatype,
            name,
            access,
        }
    }
}

#[derive(Debug, Clone)]
pub enum VarAccess {
    Mutable(Variable),
    Immutable(Value),
    Unresolved,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DatatypeStruct {
    name: String,
    kind: DKind,
    size: usize,
}

impl DatatypeStruct {
    fn new(name: String, kind: DKind) -> Self {
        Self::with_size(name, kind, 0)
    }

    fn with_size(name: String, kind: DKind, size: usize) -> Self {
        Self { name, kind, size }
    }

    fn get_ir_repr(&self) -> Type {
        match self.kind {
            DKind::Builtin(tp) => tp,
            DKind::Pointer(_) => todo!(),
            DKind::Alias(_) => todo!(),
            DKind::Structure(_) => todo!(),
            DKind::Enum(_) => todo!(),
        }
    }

    fn default_value(&self, builder: &mut FunctionBuilder) -> Value {
        match self.kind {
            DKind::Builtin(tp) => match tp {
                I8 => builder.ins().iconst(I8, 0),
                I16 => builder.ins().iconst(I16, 0),
                I32 => builder.ins().iconst(I32, 0),
                I64 => builder.ins().iconst(I64, 0),
                F32 => builder.ins().f32const(0.0),
                F64 => builder.ins().f64const(0.0),
                B1 => builder.ins().bconst(B1, false),
                _ => panic!("unsupported builtin type"),
            },
            DKind::Pointer(_) => todo!(),
            DKind::Alias(_) => todo!(),
            DKind::Structure(_) => todo!(),
            DKind::Enum(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DKind {
    Builtin(Type),
    Pointer(Datatype),
    Alias(Datatype),
    Structure(Structure),
    Enum(Enum),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Structure {}

#[derive(Debug, Clone, PartialEq)]
pub enum Enum {}

#[derive(Debug)]
pub struct IrGenError {
    kind: IGEKind,
    token: Option<Token>,
}

impl IrGenError {
    fn new(kind: IGEKind, token: Token) -> Self {
        Self {
            kind,
            token: Some(token),
        }
    }
}

impl Into<IrGenError> for AstError {
    fn into(self) -> IrGenError {
        IrGenError {
            kind: IGEKind::AstError(self.kind),
            token: self.token,
        }
    }
}

#[derive(Debug)]
pub enum IGEKind {
    TypeMismatch(Datatype, Datatype),
    DuplicateType(Datatype, Datatype),
    DuplicateModule(Mod, Mod),
    DuplicateFunction(Fun, Fun),
    InvalidLinkage,
    InvalidCallConv,
    ExpectedValue,
    MissingValueInElseBranch,
    UnexpectedValueInThenBranch,
    MissingElseBranch,
    FunctionNotFound,
    VariableNotFound,
    TypeNotFound,
    ModuleNotFound,
    CannotOpenFile(std::io::Error),
    AstError(AEKind),
}

impl Into<IrGenError> for IGEKind {
    fn into(self) -> IrGenError {
        IrGenError {
            kind: self,
            token: None,
        }
    }
}

impl<'a> SealCurrentBlock for FunctionBuilder<'a> {
    fn seal_current_block(&mut self) {
        self.seal_block(self.current_block().unwrap());
    }
}

trait SealCurrentBlock {
    fn seal_current_block(&mut self);
}

pub fn test() {
    let context = Generator::new().generate("src/test_code.pmt").unwrap();
    for module in context.modules.iter() {
        for fun in module.borrow().functions.iter() {
            println!("{}", fun.borrow().function.as_ref().unwrap().display());
        }
    }
}
