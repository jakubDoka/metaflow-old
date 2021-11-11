use std::{
    cell::RefCell,
    ops::Deref,
    rc::Rc,
    str::FromStr,
};
use cranelift_codegen::{binemit::{NullRelocSink, NullStackMapSink, NullTrapSink}, ir::{types::*, AbiParam, ExternalName, Function, Signature, Type, Value, InstBuilder}, isa::{self, CallConv}, settings::{self, Configurable}};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use target_lexicon::triple;
use crate::{
    ast::{AEKind, AKind, Ast, AstError, AstParser},
    lexer::{Lexer, StrRef, Token},
};

pub type CraneContext = cranelift_codegen::Context;
pub type Result<T> = std::result::Result<T, GenError>;

pub struct Generator {
    builtin_module: Mod,
    context: Context,
    current_module: Mod,
    function_builder_context: Option<FunctionBuilderContext>,
    variables: Vec<Option<Var>>,
    variable_counter: u32,
    module_id_counter: u32,
}

impl Generator {
    pub fn new() -> Self {
        let builtin = Mod::builtin();
        Self {
            builtin_module: builtin.clone(),
            context: Context::new(),
            current_module: builtin, // just an place holder
            function_builder_context: Some(FunctionBuilderContext::new()),
            variables: Vec::new(),
            variable_counter: 0,
            module_id_counter: 0,
        }
    }

    pub fn generate(mut self, root_file_name: &str) -> Result<Context> {
        self.generate_module(root_file_name.to_string())?;

        Ok(self.context)
    }

    pub fn generate_module(&mut self, module_path: String) -> Result<Mod> {
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

    pub fn function(&mut self, ast: &Ast) -> Result<()> {
        self.variable_counter = 0;
        self.variables.clear();
        let mut function_builder_context =
            std::mem::take(&mut self.function_builder_context).unwrap();

        let signature_ast = &ast[0];
        let (signature, mut fun_signature) =
            self.create_signature(signature_ast, CallConv::WindowsFastcall)?;

        let mut function = Function::with_name_signature(fun_signature.id.clone(), signature);
        let mut builder = FunctionBuilder::new(&mut function, &mut function_builder_context);
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
        self.current_module
            .borrow_mut()
            .add_function(fun.clone())?;

        builder.switch_to_block(entry_point);
        builder.seal_block(entry_point);
        let val = builder.ins().iconst(I32, 1);
        builder.ins().return_(&[val]);
        builder.finalize();

        fun.borrow_mut().function = Some(function);

        self.function_builder_context = Some(function_builder_context);

        Ok(())
    }

    pub fn create_signature(
        &self,
        header: &Ast,
        cc: CallConv,
    ) -> Result<(Signature, FunSignature)> {
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

    pub fn find_datatype(&self, token: &Token) -> Result<Datatype> {
        self.current_module
            .borrow()
            .find_datatype(&token.value)
            .ok_or_else(|| GenError::new(GEKind::TypeNotFound, token.clone()))
    }

    pub fn find_function(&self, token: &Token) -> Result<Fun> {
        self.current_module
            .borrow()
            .find_function(token)
            .ok_or_else(|| GenError::new(GEKind::FunctionNotFound, token.clone()))
    }

    pub fn find_variable(&self, token: &Token) -> Result<Var> {
        self.variables
            .iter()
            .rev()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
            .find(|var| &var.name == &token.value)
            .map(|var| var.clone())
            .ok_or_else(|| GenError::new(GEKind::VariableNotFound, token.clone()))
    }

    pub fn make_variable(&mut self) -> Variable {
        let var = Variable::with_u32(self.variable_counter);
        self.variable_counter += 1;
        var
    }

    pub fn load_ast(&mut self, file_name: String) -> Result<Ast> {
        let bytes =
            std::fs::read_to_string(&file_name).map_err(|e| GEKind::CannotOpenFile(e).into())?;
        AstParser::new(Lexer::new(file_name, bytes))
            .parse()
            .map_err(Into::into)
    }
}

pub struct Context {
    modules: Vec<Mod>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
        }
    }

    pub fn add_module(&mut self, module: Mod) -> Result<()> {
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

    pub fn find_module(&self, name: Token) -> Result<Mod> {
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
pub struct Mod {
    inner: Rc<RefCell<ModuleStruct>>,
}

impl Mod {
    pub fn new(name: String, id: u32) -> Self {
        Self {
            inner: Rc::new(RefCell::new(ModuleStruct::new(name, id))),
        }
    }

    pub fn builtin() -> Self {
        Self {
            inner: Rc::new(RefCell::new(ModuleStruct::builtin())),
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
    pub name: String,
    pub dependency: Vec<Mod>,
    pub types: Vec<Datatype>,
    pub functions: Vec<Fun>,
    pub function_id_counter: u32,
    pub id: u32,
}

impl ModuleStruct {
    pub fn new(name: String, id: u32) -> Self {
        Self {
            name,
            dependency: vec![],
            types: vec![],
            functions: vec![],
            function_id_counter: 0,
            id,
        }
    }

    pub fn builtin() -> Self {
        macro_rules! builtin {
            ($($name:ident, $short:ident, $bits:expr);+ $(;)?) => {
                vec![$(
                    Datatype::with_size(
                        concat!(stringify!($short)).to_string().to_lowercase(),
                        DKind::Builtin($name),
                        $bits,
                    ),
                )*]
            };
        }

        let builtin = builtin!(
            I8, i8, 8;
            I16, i16, 16;
            I32, i32, 32;
            I64, i64, 64;
            I8, u8, 8;
            I16, u16, 16;
            I32, u32, 32;
            I64, u64, 64;
            F32, f32, 32;
            F64, f64, 64;
        );

        let mut module = Self::new("builtin".to_string(), 0);
        for datatype in builtin {
            module.add_datatype(datatype).unwrap();
        }
        module
    }

    pub fn find_datatype(&self, name: &str) -> Option<Datatype> {
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

    pub fn add_datatype(&mut self, datatype: Datatype) -> Result<()> {
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

    pub fn add_function(&mut self, fun: Fun) -> Result<()> {
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

    pub fn find_function(&self, name: &Token) -> Option<Fun> {
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

    pub fn new_fun_name(&mut self) -> ExternalName {
        let name = ExternalName::user(self.id, self.function_id_counter);
        self.function_id_counter += 1;
        name
    }
}

#[derive(Debug, Clone)]
pub struct Fun {
    inner: Rc<RefCell<FunStruct>>,
}

impl Fun {
    pub fn new(signature: FunSignature) -> Self {
        Self {
            inner: Rc::new(RefCell::new(FunStruct::new(signature))),
        }
    }
}

impl Deref for Fun {
    type Target = Rc<RefCell<FunStruct>>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug, Clone)]
pub struct FunStruct {
    pub signature: FunSignature,
    pub function: Option<Function>,
}

impl FunStruct {
    pub fn new(signature: FunSignature) -> Self {
        Self {
            signature,
            function: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunSignature {
    pub id: ExternalName,
    pub name: StrRef,
    pub params: Vec<Var>,
    pub ret: Option<Datatype>,
    pub cc: CallConv,
}

impl FunSignature {
    pub fn new(
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

#[derive(Debug, Clone)]
pub struct Datatype {
    inner: Rc<RefCell<DatatypeStruct>>,
}

impl Datatype {
    pub fn new(name: String, kind: DKind) -> Self {
        Self::with_size(name, kind, 0)
    }

    pub fn with_size(name: String, kind: DKind, size: usize) -> Self {
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
    pub name: StrRef,
    pub access: VarAccess,
    pub datatype: Datatype,
}

impl Var {
    pub fn new(name: StrRef, access: VarAccess, datatype: Datatype) -> Self {
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

#[derive(Debug, Clone)]
pub struct DatatypeStruct {
    pub name: String,
    pub kind: DKind,
    pub size: usize,
}

impl DatatypeStruct {
    pub fn new(name: String, kind: DKind) -> Self {
        Self::with_size(name, kind, 0)
    }

    pub fn with_size(name: String, kind: DKind, size: usize) -> Self {
        Self { name, kind, size }
    }

    pub fn get_ir_repr(&self) -> Type {
        match self.kind {
            DKind::Builtin(tp) => tp,
            DKind::Pointer(_) => todo!(),
            DKind::Alias(_) => todo!(),
            DKind::Structure(_) => todo!(),
            DKind::Enum(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum DKind {
    Builtin(Type),
    Pointer(Datatype),
    Alias(Datatype),
    Structure(Structure),
    Enum(Enum),
}

#[derive(Debug, Clone)]
pub enum Structure {}

#[derive(Debug, Clone)]
pub enum Enum {}

#[derive(Debug)]
pub struct GenError {
    pub kind: GEKind,
    pub cause: Option<Token>,
}

impl GenError {
    pub fn new(kind: GEKind, cause: Token) -> Self {
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
pub enum GEKind {
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
