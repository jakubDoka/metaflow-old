use cranelift_codegen::{ir::{AbiParam, ExternalName, Function, InstBuilder, Signature, Type, Value, condcodes::{FloatCC, IntCC}, types::*}, isa::CallConv};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use std::{cell::RefCell, ops::Deref, rc::Rc};

use crate::{
    ast::{AEKind, AKind, Ast, AstError, AstParser},
    lexer::{Lexer, StrRef, TKind, Token},
};

type CraneContext = cranelift_codegen::Context;
type Result<T> = std::result::Result<T, GenError>;

struct Generator {
    builtin_repo: BuiltinRepo,
    builtin_module: Mod,
    context: Context,
    current_module: Mod,
    function_builder_context: Option<FunctionBuilderContext>,
    variables: Vec<Option<Var>>,
    variable_counter: u32,
    module_id_counter: u32,
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
        }
    }

    fn generate(mut self, root_file_name: &str) -> Result<Context> {
        self.generate_module(root_file_name.to_string())?;

        Ok(self.context)
    }

    fn generate_module(&mut self, module_path: String) -> Result<Mod> {
        let ast = self.load_ast(module_path)?;

        self.module_id_counter += 1; // the 0 is for builtin module
        self.current_module = Mod::new(
            ast.token.line_data.file_name.to_string(),
            self.module_id_counter,
        );
        self.current_module
            .borrow_mut()
            .dependency
            .push(self.builtin_module.clone());
        for item in ast.children.iter() {
            match item.kind {
                AKind::Function => {
                    self.function(item)?;
                }
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
            self.create_signature(signature_ast, CallConv::Fast)?;

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
            builder.seal_block(entry_point);
            fun
        } else {
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
        for stmt in ast.iter() {
            match stmt.kind {
                AKind::ReturnStatement => {
                    self.return_statement(stmt, builder)?;
                }
                _ => todo!(),
            }
        }

        Ok(())
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
            AKind::Literal => match ast.token.kind {
                TKind::Int(value, bits) => {
                    let datatype = match bits {
                        8 => self.builtin_repo.i8.clone(),
                        16 => self.builtin_repo.i16.clone(),
                        32 => self.builtin_repo.i32.clone(),
                        64 => self.builtin_repo.i64.clone(),
                        _ => unreachable!(),
                    };
                    let value = builder.ins().iconst(datatype.borrow().get_ir_repr(), value as i64);
                    Ok((
                        value,
                        datatype,
                    ))
                }
                _ => todo!(),
            },
            AKind::BinaryOperation => self.binary_operation(ast, builder),
            _ => todo!(),
        }
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
                }
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
                }
                _ => todo!(),
            };
            Ok((value, right_type))
        } else {
            todo!()
        }
    }

    fn create_signature(&self, header: &Ast, cc: CallConv) -> Result<(Signature, FunSignature)> {
        let mut signature = Signature::new(cc);
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

        Ok((
            signature,
            FunSignature::new(
                self.current_module.borrow_mut().new_fun_name(),
                name,
                fun_params,
                return_type,
                cc,
            ),
        ))
    }

    fn find_datatype(&self, token: &Token) -> Result<Datatype> {
        self.current_module
            .borrow()
            .find_datatype(&token.value)
            .ok_or_else(|| GenError::new(GEKind::TypeNotFound, token.clone()))
    }

    fn find_function(&self, token: &Token) -> Result<Fun> {
        self.current_module
            .borrow()
            .find_function(token)
            .ok_or_else(|| GenError::new(GEKind::FunctionNotFound, token.clone()))
    }

    fn find_variable(&self, token: &Token) -> Result<Var> {
        self.variables
            .iter()
            .rev()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
            .find(|var| &var.name == &token.value)
            .map(|var| var.clone())
            .ok_or_else(|| GenError::new(GEKind::VariableNotFound, token.clone()))
    }

    fn make_variable(&mut self) -> Variable {
        let var = Variable::with_u32(self.variable_counter);
        self.variable_counter += 1;
        var
    }

    fn load_ast(&mut self, file_name: String) -> Result<Ast> {
        let bytes =
            std::fs::read_to_string(&file_name).map_err(|e| GEKind::CannotOpenFile(e).into())?;
        AstParser::new(Lexer::new(file_name, bytes))
            .parse()
            .map_err(Into::into)
    }
}

struct Context {
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
            Ok(i) => Err(GEKind::DuplicateModule(module.clone(), self.modules[i].clone()).into()),
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
            Err(_) => Err(GenError::new(GEKind::ModuleNotFound, name.clone())),
        }
    }
}

#[derive(Debug, Clone)]
struct Mod {
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
struct ModuleStruct {
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
            Ok(i) => Err(GEKind::DuplicateType(datatype.clone(), self.types[i].clone()).into()),
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
            Ok(i) => Err(GEKind::DuplicateFunction(fun.clone(), self.functions[i].clone()).into()),
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
        struct BuiltinRepo {
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
struct Fun {
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
struct FunStruct {
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
struct FunSignature {
    id: ExternalName,
    name: StrRef,
    params: Vec<Var>,
    ret: Option<Datatype>,
    cc: CallConv,
}

impl FunSignature {
    fn new(
        id: ExternalName,
        name: StrRef,
        params: Vec<Var>,
        ret: Option<Datatype>,
        cc: CallConv,
    ) -> Self {
        Self {
            id,
            name,
            params,
            ret,
            cc,
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
struct Datatype {
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
struct Var {
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
enum VarAccess {
    Mutable(Variable),
    Immutable(Value),
    Unresolved,
}

#[derive(Debug, Clone, PartialEq)]
struct DatatypeStruct {
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
}

#[derive(Debug, Clone, PartialEq)]
enum DKind {
    Builtin(Type),
    Pointer(Datatype),
    Alias(Datatype),
    Structure(Structure),
    Enum(Enum),
}

#[derive(Debug, Clone, PartialEq)]
enum Structure {}

#[derive(Debug, Clone, PartialEq)]
enum Enum {}

#[derive(Debug)]
struct GenError {
    kind: GEKind,
    cause: Option<Token>,
}

impl GenError {
    fn new(kind: GEKind, cause: Token) -> Self {
        Self {
            kind,
            cause: Some(cause),
        }
    }
}

impl Into<GenError> for AstError {
    fn into(self) -> GenError {
        GenError {
            kind: GEKind::AstError(self.kind),
            cause: self.token,
        }
    }
}

#[derive(Debug)]
enum GEKind {
    DuplicateType(Datatype, Datatype),
    DuplicateModule(Mod, Mod),
    DuplicateFunction(Fun, Fun),
    FunctionNotFound,
    VariableNotFound,
    TypeNotFound,
    ModuleNotFound,
    CannotOpenFile(std::io::Error),
    AstError(AEKind),
}

impl Into<GenError> for GEKind {
    fn into(self) -> GenError {
        GenError {
            kind: self,
            cause: None,
        }
    }
}

pub fn test() {
    let context = Generator::new().generate("src/test_code.pmt").unwrap();
    for module in context.modules.iter() {
        for fun in module.borrow().functions.iter() {
            println!("{}", fun.borrow().function.as_ref().unwrap().display());
        }
    }
}
