pub mod cell;
pub mod context;
pub mod datatype;
pub mod error;
pub mod field;
pub mod fun;
pub mod gen;
pub mod module;
pub mod structure;
pub mod val;
pub mod var;

pub use cell::*;
pub use context::*;
pub use datatype::*;
pub use error::*;
pub use field::*;
pub use fun::*;
pub use module::*;
pub use structure::*;
pub use val::*;
pub use var::*;

use cranelift_codegen::{
    binemit::{NullStackMapSink, NullTrapSink},
    entity::EntityRef,
    ir::{
        condcodes::{FloatCC, IntCC},
        types::*,
        AbiParam, Block, ExternalName, FuncRef, Function, InstBuilder, MemFlags, Signature,
        StackSlotData, StackSlotKind, Type, Value,
    },
    isa::{CallConv, TargetIsa},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataContext, DataId, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use std::{ops::Deref, str::FromStr};

use crate::{
    ast::{AEKind, AKind, Ast, AstError, AstParser},
    lexer::{Lexer, StrRef, TKind, Token},
};

type CraneContext = cranelift_codegen::Context;
type Result<T> = std::result::Result<T, IrGenError>;
type ExprResult = Result<Option<Val>>;
type LoopHeader = (StrRef, Block, Block, Option<Option<Val>>);

pub struct Generator {
    builtin_repo: BuiltinRepo,
    builtin_module: Cell<Mod>,
    context: Context,
    data_context: DataContext,
    current_module: Cell<Mod>,
    current_signature: Option<Cell<Fun>>,
    variables: Vec<Option<Var>>,
    loop_headers: Vec<LoopHeader>,
    variable_counter: usize,
    string_counter: usize,
    global_attributes: Vec<Ast>,
    pushed_attributes: Vec<Ast>,
    imported_functions: Vec<(StrRef, FuncRef)>,
    call_buffer: Vec<Value>,
    object_module: ObjectModule,
    seen_structures: Vec<Cell<Datatype>>,

    datatype_pool: Pool<Datatype>,
}

impl Generator {
    fn new(object_module: ObjectModule) -> Self {
        let builtin_repo = BuiltinRepo::new(object_module.isa());
        let builtin_module = builtin_repo.to_module();
        Self {
            current_module: builtin_module.clone(), // just an place holder
            builtin_repo,
            builtin_module,
            current_signature: None,
            context: Context::new(),
            data_context: DataContext::new(),
            variables: Vec::new(),
            loop_headers: Vec::new(),
            variable_counter: 0,
            string_counter: 0,
            global_attributes: Vec::new(),
            pushed_attributes: Vec::new(),
            imported_functions: Vec::new(),
            call_buffer: Vec::new(),
            object_module,
            seen_structures: Vec::new(),

            datatype_pool: Pool::new(),
        }
    }

    fn generate(mut self, root_file_name: &str) -> Result<ObjectModule> {
        self.generate_module(root_file_name.to_string())?;

        self.generate_functions()?;

        // get rid of cyclic references
        self.context
            .modules_mut()
            .iter_mut()
            .map(|m| m.types_mut().iter_mut())
            .flatten()
            .for_each(|t| t.clear());

        Ok(self.object_module)
    }

    fn generate_struct(&mut self, ast: Ast) -> Result<DKind> {
        let mut fields = Vec::new();
        for raw_fields in ast[1].iter() {
            match raw_fields.kind() {
                AKind::StructField(embedded) => {
                    let datatype = self.find_datatype(raw_fields.last().unwrap())?;
                    for field in raw_fields[0..raw_fields.len() - 1].iter() {
                        fields.push(Field::new(
                            embedded,
                            0,
                            field.token().value().clone(),
                            datatype.clone(),
                        ));
                    }
                }
                _ => todo!("unsupported inner struct construct {:?}", raw_fields),
            }
        }

        Ok(DKind::Structure(Structure::new(false, fields)))
    }

    fn generate_functions(&mut self) -> Result<()> {
        let mut codegen_ctx = cranelift_codegen::Context::new();
        let mut function_context = FunctionBuilderContext::new();
        let ctx = std::mem::replace(&mut self.context, Context::new());
        for mut f in ctx
            .modules()
            .iter()
            .map(|m| m.functions().iter())
            .flatten()
            .map(Clone::clone)
        {
            if let AKind::None = f.body().kind() {
                continue;
            }
            self.variables.clear();
            self.imported_functions.clear();
            self.variable_counter = 0;
            let mut function = Function::with_name_signature(
                ExternalName::default(),
                std::mem::take(f.signature_mut()).unwrap(),
            );
            let mut builder = FunctionBuilder::new(&mut function, &mut function_context);
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let params = builder.block_params(entry_block);

            let skip = f
                .return_type()
                .map(|t| {
                    if t.is_on_stack() {
                        self.variables.push(Some(Var::new(
                            StrRef::empty(),
                            Val::address(params[0], true, t.clone()),
                        )));
                        1
                    } else {
                        0
                    }
                })
                .unwrap_or(0);

            for (value, var) in params.iter().skip(skip).zip(f.params_mut().iter_mut()) {
                var.set_kind(if var.value().datatype().is_on_stack() {
                    VKind::Address(*value, false, 0)
                } else {
                    VKind::Immutable(*value)
                });
                self.variables.push(Some(var.clone()));
            }
            self.current_signature = Some(f.clone());
            self.generate_function_body(f.body(), &mut builder)?;
            builder.seal_current_block();
            builder.finalize();

            codegen_ctx.func = function;
            codegen_ctx.compute_cfg();
            codegen_ctx.compute_domtree();
            self.object_module
                .define_function(
                    f.id(),
                    &mut codegen_ctx,
                    &mut NullTrapSink::default(),
                    &mut NullStackMapSink {},
                )
                .unwrap();
        }

        Ok(())
    }

    fn generate_module(&mut self, module_path: String) -> Result<Cell<Mod>> {
        let mut ast = self.load_ast(module_path)?;

        self.current_module = Cell::new(Mod::new(ast.token().line_data().file_name().to_string()));
        self.current_module
            .dependency_mut()
            .push(self.builtin_module.clone());

        for item in ast.iter_mut() {
            match &item.kind() {
                AKind::StructDeclaration => {
                    self.struct_declaration(std::mem::take(item))?;
                    self.pushed_attributes.clear();
                }
                _ => (),
            }
        }

        self.resolve_types()?;

        for mut item in ast.drain(..) {
            match item.kind() {
                AKind::Function => {
                    self.function(item)?;
                    self.pushed_attributes.clear();
                }

                AKind::Attribute => match item[0].token().value().deref() {
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
                                .position(|e| e.kind() == AKind::None)
                                .unwrap()..,
                        );
                    }
                    _ => {
                        item.drain(..)
                            .for_each(|item| self.pushed_attributes.push(item));
                    }
                },
                AKind::None => (),
                _ => todo!("unmatched top level expression {:?}", item),
            }
        }

        self.context.add_module(self.current_module.clone())?;

        Ok(self.current_module.clone())
    }

    fn resolve_types(&mut self) -> Result<()> {
        let mut current_module = self.current_module.clone();
        for datatype in current_module
            .types_mut()
            .iter_mut()
            .filter(|d| !d.is_resolved())
        {
            let ast = if let DKind::Unresolved(ast) =
                std::mem::replace(datatype.kind_mut(), DKind::Unresolved(Ast::none()))
            {
                ast
            } else {
                unreachable!();
            };

            let kind = match ast.kind() {
                AKind::StructDeclaration => self.generate_struct(ast)?,
                _ => todo!("unmatched datatype type {:?}", ast),
            };

            datatype.set_kind(kind);
        }

        for mut datatype in current_module.types_mut() {
            self.determinate_size(&mut datatype)?;
        }

        Ok(())
    }

    fn determinate_size(&mut self, datatype: &mut Datatype) -> Result<()> {
        if datatype.is_size_resolved() {
            return Ok(());
        }

        let mut size = 0;

        match datatype.kind_mut() {
            DKind::Structure(structure) => {
                if structure.union() {
                    for field in structure.fields_mut() {
                        self.determinate_size(field.datatype_mut())?;
                        size = size.max(field.datatype().size());
                    }
                } else {
                    for field in structure.fields_mut() {
                        self.determinate_size(field.datatype_mut())?;
                        field.set_offset(size);
                        size += field.datatype().size();
                    }
                }
            }
            _ => todo!("unmatched datatype type {:?}", datatype.kind()),
        }

        datatype.set_size(size);

        Ok(())
    }

    fn struct_declaration(&mut self, ast: Ast) -> Result<()> {
        let name = ast[0].token().value().clone().to_string();

        let datatype = self.datatype_pool
            .wrap(Datatype::new(name, DKind::Unresolved(ast)));

        self.current_module
            .add_datatype(datatype)?;

        Ok(())
    }

    fn function(&mut self, ast: Ast) -> Result<()> {
        let fun = self.create_signature(ast)?;
        self.current_module.add_function(fun)?;
        Ok(())
    }

    fn generate_function_body(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        self.statement_list(ast, builder, false)?;
        Ok(())
    }

    fn statement_list(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
        is_scope: bool,
    ) -> ExprResult {
        if is_scope {
            self.start_scope();
        }
        for stmt in ast[0..ast.len() - 1].iter() {
            self.statement(stmt, builder)?;
        }

        if let Some(last) = ast.last() {
            return self.statement(last, builder);
        }
        if is_scope {
            self.end_scope();
        }
        Ok(None)
    }

    fn start_scope(&mut self) {
        self.variables.push(None);
    }

    fn end_scope(&mut self) {
        let new_len = self.variables.len()
            - 1
            - self
                .variables
                .iter()
                .rev()
                .position(|e| e.is_none())
                .unwrap();

        self.variables.truncate(new_len);
    }

    fn statement(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        match ast.kind() {
            AKind::ReturnStatement => self.return_statement(ast, builder)?,
            AKind::VarStatement(_) => self.var_statement(ast, builder)?,
            AKind::Break => self.break_statement(ast, builder)?,

            AKind::IfExpression => return self.if_expression(ast, builder),
            AKind::Call => return self.call_expression(ast, builder),
            AKind::Loop => return self.loop_expression(ast, builder),
            _ => {
                return Ok(Some(self.expression(ast, builder)?));
            }
        }

        Ok(None)
    }

    fn break_statement(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        let mut header = self.find_loop_header(&ast[0].token())?;
        let loop_exit_block = header.2;
        if let Some(val) = header.3 {
            if let Some(val) = val {
                if ast[1].kind() == AKind::None {
                    return Err(IrGenError::new(IGEKind::ExpectedValue, ast.token().clone()));
                }
                let value = self.expression(&ast[1], builder)?;
                if value.datatype().is_on_stack() {
                    val.write(&value, &ast.token(), builder, self.isa())?;
                    builder.ins().jump(loop_exit_block.clone(), &[]);
                } else {
                    let value = value.read(builder, self.isa());
                    builder.ins().jump(loop_exit_block.clone(), &[value]);
                }
            } else {
                if ast[1].kind() != AKind::None {
                    return Err(IrGenError::new(
                        IGEKind::UnexpectedValue,
                        ast.token().clone(),
                    ));
                }
                builder.ins().jump(loop_exit_block.clone(), &[]);
            }
        } else {
            header.3 = if ast[1].kind() == AKind::None {
                builder.ins().jump(loop_exit_block.clone(), &[]);
                Some(None)
            } else {
                let value = self.expression(&ast[1], builder)?;
                let val = Val::new_stack(false, &value.datatype(), builder);
                if value.datatype().is_on_stack() {
                    val.write(&value, &ast.token(), builder, self.isa())?;
                    builder.ins().jump(loop_exit_block.clone(), &[]);
                } else {
                    let value = value.read(builder, self.isa());
                    builder.ins().jump(loop_exit_block.clone(), &[value]);
                }
                Some(Some(val))
            };
            self.update_loop_header(header);
        }
        Ok(())
    }

    fn find_loop_header(&mut self, name: &Token) -> Result<LoopHeader> {
        self.loop_headers
            .iter()
            .rev()
            .find(|(header_name, ..)| header_name.deref() == name.value().deref())
            .map(|h| h.clone())
            .ok_or_else(|| IrGenError::new(IGEKind::LoopHeaderNotFound, name.clone()))
    }

    fn update_loop_header(&mut self, header: LoopHeader) {
        self.loop_headers
            .iter_mut()
            .find(|(header_name, ..)| header_name.deref() == header.0.deref())
            .map(|h| *h = header);
    }

    fn return_statement(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        let ret_expr = &ast[0];

        let ret_value = self.expression(ret_expr, builder)?;

        if let Ok(ret_stack) = self.find_variable(&Token::eof()) {
            ret_stack
                .value()
                .write(&ret_value, &ast.token(), builder, self.isa())?;
            let value = ret_stack.value().read(builder, self.isa());
            builder.ins().return_(&[value]);
        } else {
            let value = ret_value.read(builder, self.isa());
            builder.ins().return_(&[value]);
        }

        Ok(())
    }

    fn expression(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<Val> {
        match ast.kind() {
            AKind::Literal => return self.literal(ast, builder),
            AKind::Identifier => {
                let var = self.find_variable(&ast.token())?;
                return Ok(var.value().clone());
            }
            AKind::DotExpr => return self.dot_expr(ast, builder),
            AKind::BinaryOperation => self.binary_operation(ast, builder)?,
            AKind::UnaryOperation => self.unary_operation(ast, builder)?,
            AKind::IfExpression => self.if_expression(ast, builder)?,
            AKind::Call => self.call_expression(&ast, builder)?,
            AKind::Loop => self.loop_expression(ast, builder)?,
            _ => todo!("unmatched expression {}", ast),
        }
        .ok_or_else(|| {
            panic!(
                "{:?}",
                IrGenError::new(IGEKind::ExpectedValue, ast.token().clone())
            )
        })
    }

    fn unary_operation(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        let op = ast[0].token().value().deref();
        let value = self.expression(&ast[1], builder)?;
        let datatype = value.datatype();
        let red_value = value.read(builder, self.isa());
        match op {
            "*" => {
                match datatype.kind() {
                    DKind::Pointer(base, mutable) => {
                        let val = value.read(builder, self.isa());
                        return Ok(Some(Val::address(val, *mutable, base.clone())));
                    }
                    _ => (),
                }
            }
            "&" => {
                let ptr_datatype = self.pointer_of(value.is_mutable(), &datatype);
                if datatype.is_on_stack() {
                    return Ok(Some(Val::immutable(red_value, ptr_datatype)));
                } else {
                    return Err(IrGenError::new(IGEKind::CannotTakeAddressOfRegister, ast.token().clone()));
                }
            }
            
            "!" | "~" => {
                if datatype.is_builtin() {
                    if datatype.is_bool() {
                        let f = builder.ins().bconst(B1, false);
                        let t = builder.ins().bconst(B1, true);
                        return Ok(Some(Val::immutable(
                            builder.ins().select(red_value, f, t),
                            datatype.clone(),
                        )));
                    }
                    return Ok(Some(Val::immutable(
                        builder.ins().bnot(red_value),
                        datatype.clone(),
                    )));
                }
            }
            "-" => {
                if datatype.is_int() {
                    return Ok(Some(Val::immutable(
                        builder.ins().ineg(red_value),
                        datatype.clone(),
                    )));
                } else if datatype.is_float() {
                    return Ok(Some(Val::immutable(
                        builder.ins().fneg(red_value),
                        datatype.clone(),
                    )));
                }
            }
            "++" | "--" => {
                let val = if op == "++" { 1 } else { -1 };
                if datatype.is_int() || datatype.is_uint() {
                    return Ok(Some(Val::immutable(
                        builder.ins().iadd_imm(red_value, val),
                        datatype.clone(),
                    )));
                }
            }
            "abs" => {
                if datatype.is_float() {
                    return Ok(Some(Val::immutable(
                        builder.ins().fabs(red_value),
                        datatype.clone(),
                    )));
                } else if datatype.is_int() {
                    let cond = builder
                        .ins()
                        .icmp_imm(IntCC::SignedGreaterThan, red_value, 0);
                    let inverted = builder.ins().ineg(red_value);
                    return Ok(Some(Val::immutable(
                        builder.ins().select(cond, red_value, inverted),
                        datatype.clone(),
                    )));
                }
            }
            _ => (),
        }

        todo!("dispatch custom unary op ({})", op)
    }

    fn loop_expression(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        let loop_block = builder.create_block();
        let loop_exit_block = builder.create_block();

        self.loop_headers.push((
            ast[0].token().value().clone(),
            loop_block,
            loop_exit_block,
            None,
        ));

        builder.ins().jump(loop_block, &[]);
        builder.seal_current_block();
        builder.switch_to_block(loop_block);
        self.statement_list(&ast[1], builder, true)?;
        builder.ins().jump(loop_block, &[]);
        builder.seal_block(loop_block);
        builder.seal_current_block();

        builder.switch_to_block(loop_exit_block);

        Ok(
            if let Some((.., Some(Some(val)))) = self.loop_headers.pop() {
                if val.datatype().is_on_stack() {
                    Some(val)
                } else {
                    let value = builder
                        .append_block_param(loop_exit_block, val.datatype().ir_repr(self.isa()));
                    Some(Val::immutable(value, val.datatype().clone()))
                }
            } else {
                None
            },
        )
    }

    fn var_statement(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<()> {
        for var in ast.iter() {
            let (identifiers, datatype, values) = (&var[0], &var[1], &var[2]);

            let mut datatype = if let AKind::None = datatype.kind() {
                None
            } else {
                Some(self.find_datatype(datatype)?)
            };

            for (i, name) in identifiers
                .iter()
                .map(|i| i.token().value().clone())
                .enumerate()
            {
                let value = if values.kind() != AKind::None {
                    let mut value = self.expression(&values[i], builder)?;
                    if let Some(datatype) = datatype.as_ref() {
                        assert_type(&values[i].token(), &value.datatype(), datatype)?;
                    } else {
                        datatype = Some(value.datatype().clone());
                    }

                    if ast.kind() == AKind::VarStatement(true) {
                        if value.datatype().is_on_stack() {
                            value.set_mutability(true);
                        } else {
                            let variable = Variable::new(self.variable_counter);
                            self.variable_counter += 1;

                            builder.declare_var(variable, value.datatype().ir_repr(self.isa()));
                            let val = value.read(builder, self.isa());
                            value.set_kind(VKind::Mutable(variable));
                            builder.def_var(variable, val);
                        }
                    }

                    value
                } else {
                    let datatype = datatype.as_ref().unwrap();
                    if datatype.is_on_stack() {
                        let val = Val::new_stack(
                            ast.kind() == AKind::VarStatement(true),
                            datatype,
                            builder,
                        );
                        static_memset(
                            val.read(builder, self.isa()),
                            0,
                            0,
                            datatype.size(),
                            builder,
                        );
                        val
                    } else {
                        let default_value = datatype.default_value(builder, self.isa());
                        if ast.kind() == AKind::VarStatement(true) {
                            let var = Variable::new(self.variable_counter);
                            self.variable_counter += 1;
                            builder.declare_var(var, datatype.ir_repr(self.isa()));
                            builder.def_var(var, default_value);
                            Val::mutable(var, datatype.clone())
                        } else {
                            Val::immutable(default_value, datatype.clone())
                        }
                    }
                };
                self.variables.push(Some(Var::new(name, value)));
            }
        }

        Ok(())
    }

    fn call_expression(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        if let Some(result) = self.builtin_call(ast, builder)? {
            return Ok(result);
        }

        let fun = self.find_function(&ast[0].token())?;

        let fun_ref = self
            .imported_functions
            .iter()
            .find(|(id, _)| id.deref() == fun.name().deref())
            .map(|(_, fun_ref)| *fun_ref)
            .unwrap_or_else(|| {
                let fun_ref = self
                    .object_module
                    .declare_func_in_func(fun.id(), builder.func);
                self.imported_functions.push((fun.name().clone(), fun_ref));
                fun_ref
            });

        if fun.params().len() != ast.len() - 1 {
            return Err(IrGenError::new(
                IGEKind::InvalidAmountOfArguments(fun.params().len(), ast.len() - 1),
                ast.token().clone(),
            ));
        }

        let return_value = if let Some(return_type) = fun.return_type() {
            if return_type.is_on_stack() {
                let value = Val::new_stack(false, return_type, builder);
                self.call_buffer.push(value.read(builder, self.isa()));
                Some(value)
            } else {
                None
            }
        } else {
            None
        };

        for (i, e) in ast[1..].iter().enumerate() {
            let value = self.expression(e, builder)?;
            assert_type(
                &e.token(),
                &value.datatype(),
                &fun.params()[i].value().datatype(),
            )?;
            self.call_buffer.push(value.read(builder, self.isa()));
        }

        let vals = builder.ins().call(fun_ref, &self.call_buffer);
        self.call_buffer.clear();

        if let Some(return_type) = fun.return_type() {
            if return_type.is_on_stack() {
                Ok(return_value)
            } else {
                Ok(Some(Val::immutable(
                    builder.inst_results(vals)[0],
                    return_type.clone(),
                )))
            }
        } else {
            Ok(None)
        }
    }

    fn builtin_call(
        &mut self,
        ast: &Ast,
        builder: &mut FunctionBuilder,
    ) -> Result<Option<Option<Val>>> {
        let name = ast[0].token().value().deref();
        match name {
            "sizeof" => {
                assert_arg_count(ast, 1)?;
                let size = self.find_datatype(&ast[1])?.size();
                let size = builder.ins().iconst(I64, size as i64);
                Ok(Some(Some(Val::immutable(
                    size,
                    self.builtin_repo.i64().clone(),
                ))))
            }
            _ => Ok(None),
        }
    }

    fn literal(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<Val> {
        match ast.token().kind() {
            TKind::Int(value, bits) => {
                let datatype = match bits {
                    8 => self.builtin_repo.i8(),
                    16 => self.builtin_repo.i16(),
                    32 => self.builtin_repo.i32(),
                    _ => self.builtin_repo.i64(),
                }
                .clone();
                let value = builder
                    .ins()
                    .iconst(datatype.ir_repr(self.isa()), value as i64);
                Ok(Val::immutable(value, datatype))
            }
            TKind::Uint(value, bits) => {
                let datatype = match bits {
                    8 => self.builtin_repo.u8(),
                    16 => self.builtin_repo.u16(),
                    32 => self.builtin_repo.u32(),
                    _ => self.builtin_repo.u64(),
                }
                .clone();
                let value = builder
                    .ins()
                    .iconst(datatype.ir_repr(self.isa()), value as i64);
                Ok(Val::immutable(value, datatype))
            }
            TKind::Float(value, bits) => {
                if bits == 32 {
                    let value = builder.ins().f32const(value as f32);
                    Ok(Val::immutable(value, self.builtin_repo.f32().clone()))
                } else {
                    let value = builder.ins().f64const(value);
                    Ok(Val::immutable(value, self.builtin_repo.f64().clone()))
                }
            }
            TKind::Bool(value) => {
                let datatype = self.builtin_repo.bool().clone();
                let value = builder.ins().bconst(datatype.ir_repr(self.isa()), value);
                Ok(Val::immutable(value, datatype))
            }
            TKind::Char(value) => {
                let datatype = self.builtin_repo.i32().clone();
                let value = builder
                    .ins()
                    .iconst(datatype.ir_repr(self.isa()), value as i64);
                Ok(Val::immutable(value, datatype))
            }
            TKind::String(value) => {
                let id = self.create_static_data(
                    "",
                    DataContentOption::Data(&value),
                    Linkage::Export,
                    false,
                    false,
                )?;
                let data = self.object_module.declare_data_in_func(id, builder.func);
                let val = builder.ins().global_value(self.isa().pointer_type(), data);
                let datatype = self.builtin_repo.string().clone();
                let new_stack = Val::new_stack(false, &datatype, builder);
                let addr = new_stack.read(builder, self.isa());
                let len = builder.ins().iconst(I32, value.len() as i64);
                builder.ins().store(MemFlags::new(), len, addr, 0);
                builder.ins().store(MemFlags::new(), len, addr, 4);
                builder.ins().store(MemFlags::new(), val, addr, 8);
                Ok(new_stack)
            }
            _ => todo!("unmatched literal token {:?}", ast.token()),
        }
    }

    fn if_expression(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        let cond_expr = &ast[0];
        let cond_val = self.expression(cond_expr, builder)?;

        assert_type(
            &cond_expr.token(),
            &cond_val.datatype(),
            self.builtin_repo.bool(),
        )?;

        let then_block = builder.create_block();
        let value = cond_val.read(builder, self.isa());
        builder.ins().brnz(value, then_block, &[]);

        let mut merge_block = None;

        let else_branch = &ast[2];
        let else_block = if else_branch.kind() == AKind::None {
            let block = builder.create_block();
            builder.ins().jump(block, &[]);
            merge_block = Some(block);
            None
        } else {
            let else_block = builder.create_block();
            builder.ins().jump(else_block, &[]);
            Some(else_block)
        };

        if let Some((_, loop_block, ..)) = self.loop_headers.last() {
            if loop_block.to_owned() != builder.current_block().unwrap() {
                builder.seal_current_block();
            }
        } else {
            builder.seal_current_block();
        }

        let then_branch = &ast[1];

        builder.switch_to_block(then_block);
        let then_result = self.statement_list(then_branch, builder, true)?;

        let mut result = None;
        let mut then_filled = false;
        if let Some(val) = then_result {
            if merge_block.is_some() {
                return Err(IrGenError::new(
                    IGEKind::MissingElseBranch,
                    ast.token().clone(),
                ));
            }
            let block = builder.create_block();
            if val.datatype().is_on_stack() {
                let value = Val::new_stack(false, &val.datatype(), builder);
                value.write(
                    &val,
                    &then_branch.last().unwrap().token(),
                    builder,
                    self.isa(),
                )?;
                builder.ins().jump(block, &[]);
                result = Some(value);
            } else {
                let value = builder.append_block_param(block, val.datatype().ir_repr(self.isa()));
                let v = val.read(builder, self.isa());
                result = Some(Val::immutable(value, val.datatype().clone()));
                builder.ins().jump(block, &[v]);
                merge_block = Some(block);
            }
        } else if !builder.is_filled() {
            let block = merge_block.unwrap_or_else(|| builder.create_block());
            builder.ins().jump(block, &[]);
            merge_block = Some(block);
        } else {
            then_filled = true;
        }

        builder.seal_current_block();

        if else_branch.kind() == AKind::Group {
            let else_block = else_block.unwrap();

            builder.switch_to_block(else_block);
            let else_result = self.statement_list(else_branch, builder, true)?;

            if let Some(val) = else_result {
                let value_token = &else_branch.last().unwrap().token();
                if let Some(result) = result.as_ref() {
                    let merge_block = merge_block.unwrap();
                    if val.datatype().is_on_stack() {
                        result.write(&val, value_token, builder, self.isa())?;
                        builder.ins().jump(merge_block, &[]);
                    } else {
                        assert_type(value_token, &val.datatype(), &result.datatype())?;
                        let value = val.read(builder, self.isa());
                        builder.ins().jump(merge_block, &[value]);
                    }
                } else if then_filled {
                    let block = builder.create_block();
                    if val.datatype().is_on_stack() {
                        let value = Val::new_stack(false, &val.datatype(), builder);
                        value.write(&val, value_token, builder, self.isa())?;
                        builder.ins().jump(block, &[]);
                        result = Some(value);
                    } else {
                        let value =
                            builder.append_block_param(block, val.datatype().ir_repr(self.isa()));
                        let v = val.read(builder, self.isa());
                        builder.ins().jump(block, &[v]);
                        result = Some(Val::immutable(value, val.datatype().clone()));
                        merge_block = Some(block);
                    }
                } else {
                    return Err(IrGenError::new(
                        IGEKind::UnexpectedValueInThenBranch,
                        ast.token().clone(),
                    ));
                }
            } else {
                if result.is_some() {
                    return Err(IrGenError::new(
                        IGEKind::MissingValueInElseBranch,
                        ast.token().clone(),
                    ));
                }
                if !builder.is_filled() {
                    let block = merge_block.unwrap_or_else(|| builder.create_block());
                    builder.ins().jump(block, &[]);
                    merge_block = Some(block);
                }
            }

            if merge_block.is_some() {
                builder.seal_current_block();
            }
        }

        if let Some(block) = merge_block {
            builder.switch_to_block(block);
        }

        Ok(result)
    }

    fn binary_operation(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> ExprResult {
        let op = ast[0].token().value().deref();

        match op {
            "=" => return Ok(Some(self.assign(ast, builder)?)),
            "as" => return Ok(Some(self.convert(ast, builder)?)),
            _ => (),
        }

        let left = self.expression(&ast[1], builder)?;
        let right = self.expression(&ast[2], builder)?;

        let left_val = left.read(builder, self.isa());
        let right_val = right.read(builder, self.isa());

        let left_ir = left.datatype().ir_repr(self.isa());

        if left.datatype() == right.datatype() {
            let value = if left_ir.is_int() {
                let signed = left.datatype().is_int();
                match op {
                    "+" => builder.ins().iadd(left_val, right_val),
                    "-" => builder.ins().isub(left_val, right_val),
                    "*" => builder.ins().imul(left_val, right_val),
                    "/" => {
                        if signed {
                            builder.ins().sdiv(left_val, right_val)
                        } else {
                            builder.ins().udiv(left_val, right_val)
                        }
                    }
                    "%" => {
                        if signed {
                            builder.ins().srem(left_val, right_val)
                        } else {
                            builder.ins().urem(left_val, right_val)
                        }
                    }
                    "&" => builder.ins().band(left_val, right_val),
                    "|" => builder.ins().bor(left_val, right_val),
                    "^" => builder.ins().bxor(left_val, right_val),
                    "<<" => builder.ins().ishl(left_val, right_val),
                    ">>" => {
                        if signed {
                            builder.ins().sshr(left_val, right_val)
                        } else {
                            builder.ins().ushr(left_val, right_val)
                        }
                    }
                    "max" => builder.ins().imax(left_val, right_val),
                    "min" => builder.ins().imin(left_val, right_val),

                    "==" | "!=" | "<" | ">" | ">=" | "<=" => {
                        let op = if signed {
                            match op {
                                "==" => IntCC::Equal,
                                "!=" => IntCC::NotEqual,
                                "<" => IntCC::SignedLessThan,
                                ">" => IntCC::SignedGreaterThan,
                                ">=" => IntCC::SignedGreaterThanOrEqual,
                                "<=" => IntCC::SignedLessThanOrEqual,
                                _ => unreachable!(),
                            }
                        } else {
                            match op {
                                "==" => IntCC::Equal,
                                "!=" => IntCC::NotEqual,
                                "<" => IntCC::UnsignedLessThan,
                                ">" => IntCC::UnsignedGreaterThan,
                                ">=" => IntCC::UnsignedGreaterThanOrEqual,
                                "<=" => IntCC::UnsignedLessThanOrEqual,
                                _ => unreachable!(),
                            }
                        };

                        let val = builder.ins().icmp(op, left_val, right_val);
                        return Ok(Some(Val::immutable(val, self.builtin_repo.bool().clone())));
                    }

                    _ => todo!("unsupported int operator {}", op),
                }
            } else if left_ir.is_float() {
                match op {
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
                        return Ok(Some(Val::immutable(val, self.builtin_repo.bool().clone())));
                    }
                    _ => todo!("unsupported float operation {}", op),
                }
            } else if left_ir.is_bool() {
                match op {
                    "&" => builder.ins().band(left_val, right_val),
                    "|" => builder.ins().bor(left_val, right_val),
                    "||" => todo!("unsupported ||"),
                    "&&" => todo!("unsupported &&"),
                    _ => todo!("unsupported bool operation {}", op),
                }
            } else {
                unreachable!();
            };
            Ok(Some(Val::immutable(value, right.datatype().clone())))
        } else {
            todo!(
                "non-matching type of binary operation {} {} {}",
                left.datatype().name(),
                op,
                right.datatype().name()
            )
        }
    }

    fn convert(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<Val> {
        let target_datatype = self.find_datatype(&ast[2])?;
        let value = self.expression(&ast[1], builder)?;
        let source_datatype = value.datatype();
        if &target_datatype == source_datatype {
            // TODO: emit warming
            return Ok(value);
        }

        let extend = target_datatype.size() > source_datatype.size();
        let reduce = target_datatype.size() < source_datatype.size();
        let target_ir = target_datatype.ir_repr(self.isa());
        let red_value = value.read(builder, self.isa());
        let cannot_convert = Err(IrGenError::cannot_convert(&ast.token(), &source_datatype, &target_datatype));

        let ret = if target_datatype.is_float() {
            if source_datatype.is_float() {
                if extend {
                    builder.ins().fpromote(target_ir, red_value)
                } else if reduce {
                    builder.ins().fdemote(target_ir, red_value)
                } else {
                    red_value
                }
            } else if source_datatype.is_int() {
                builder.ins().fcvt_from_sint(target_ir, red_value)
            } else if source_datatype.is_uint() {
                builder.ins().fcvt_from_uint(target_ir, red_value)
            } else if source_datatype.is_bool() {
                let val = builder.ins().bint(I64, red_value);
                builder.ins().fcvt_from_sint(target_ir, val)
            } else {
                return cannot_convert;
            }
        } else if target_datatype.is_int() {
            if source_datatype.is_float() {
                builder.ins().fcvt_to_sint(target_ir, red_value)
            } else if source_datatype.is_int() {
                if extend {
                    builder.ins().sextend(target_ir, red_value)
                } else if reduce {
                    builder.ins().ireduce(target_ir, red_value)
                } else {
                    red_value
                }
            } else if source_datatype.is_uint() {
                if extend {
                    builder.ins().uextend(target_ir, red_value)
                } else if reduce {
                    builder.ins().ireduce(target_ir, red_value)
                } else {
                    red_value
                }
            } else if source_datatype.is_bool() {
                builder.ins().bint(target_ir, red_value)
            } else {
                return cannot_convert;
            }
        } else if target_datatype.is_uint() {
            if source_datatype.is_float() {
                builder.ins().fcvt_to_uint(target_ir, red_value)
            } else if source_datatype.is_int() {
                if extend {
                    builder.ins().uextend(target_ir, red_value)
                } else if reduce {
                    builder.ins().ireduce(target_ir, red_value)
                } else {
                    red_value
                }
            } else if source_datatype.is_uint() {
                if extend {
                    builder.ins().uextend(target_ir, red_value)
                } else if reduce {
                    builder.ins().ireduce(target_ir, red_value)
                } else {
                    red_value
                }
            } else if source_datatype.is_bool() {
                builder.ins().bint(target_ir, red_value)
            } else {
                return cannot_convert;
            }
        } else if target_datatype.is_bool() {
            if source_datatype.is_float() {
                let zero = source_datatype.default_value(builder, self.isa());
                builder.ins().fcmp(FloatCC::NotEqual, red_value, zero)
            } else if source_datatype.is_int() || source_datatype.is_uint() {
                let zero = source_datatype.default_value(builder, self.isa());
                builder.ins().icmp(IntCC::NotEqual, red_value, zero)
            } else {
                return cannot_convert;
            }
        } else {
            return cannot_convert;
        };

        Ok(Val::immutable(ret, target_datatype.clone()))
    }

    fn assign(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<Val> {
        let val = self.expression(&ast[2], builder)?;

        let var = match ast[1].kind() {
            AKind::Identifier => self.find_variable(&ast[1].token())?.value().clone(),
            AKind::DotExpr => self.dot_expr(&ast[1], builder)?,
            _ => todo!("unsupported assignment target"),
        };

        var.write(&val, &ast.token(), builder, self.isa())?;

        Ok(val)
    }

    fn dot_expr(&mut self, ast: &Ast, builder: &mut FunctionBuilder) -> Result<Val> {
        let mut header = self.expression(&ast[0], builder)?;

        if !header.datatype().is_on_stack() {
            return Err(IrGenError::new(
                IGEKind::InvalidFieldAccess,
                ast.token().clone(),
            ));
        }

        let field = match &header.datatype().kind() {
            DKind::Structure(structure) => structure
                .load_field(&ast[1].token())
                .ok_or_else(|| IrGenError::new(IGEKind::FieldNotFound, ast.token().clone()))?,
            _ => unreachable!(),
        };

        header.add_offset(field.offset());
        header.set_datatype(field.datatype().clone());

        Ok(header)
    }

    fn create_signature(&mut self, mut ast: Ast) -> Result<Cell<Fun>> {
        let header = &ast[0];
        let mut signature = Signature::new(CallConv::Fast);
        let mut fun_params = Vec::new();

        let return_type = header.last().unwrap();
        let return_type = if return_type.kind() != AKind::None {
            let datatype = self.find_datatype(return_type)?.clone();
            if datatype.is_on_stack() {
                signature
                    .params
                    .push(AbiParam::new(datatype.ir_repr(self.isa())));
            }
            signature
                .returns
                .push(AbiParam::new(datatype.ir_repr(self.isa())));
            Some(datatype)
        } else {
            None
        };

        for args in header[1..header.len() - 1].iter() {
            let datatype = self.find_datatype(args.last().unwrap())?;
            for arg in args[0..args.len() - 1].iter() {
                fun_params.push(Var::new(
                    arg.token().value().clone(),
                    Val::unresolved(datatype.clone()),
                ));
                signature
                    .params
                    .push(AbiParam::new(datatype.ir_repr(self.isa())));
            }
        }

        let name = header.first().unwrap();
        let name = if name.kind() != AKind::None {
            name.token().value().clone()
        } else {
            StrRef::empty()
        };

        let linkage = if let Some(attr) = self.find_attribute("linkage") {
            self.assert_atr_len(attr, 1)?;
            match attr[0].token().value().deref() {
                "local" => Linkage::Local,
                "hidden" => Linkage::Hidden,
                "import" => Linkage::Import,
                "export" => Linkage::Export,
                "preemptible" => Linkage::Preemptible,
                _ => {
                    return Err(IrGenError::new(
                        IGEKind::InvalidLinkage,
                        attr.token().clone(),
                    ))
                }
            }
        } else {
            Linkage::Export
        };

        let call_conv = if let Some(attr) = self.find_attribute("call_conv") {
            self.assert_atr_len(attr, 1)?;
            CallConv::from_str(attr[0].token().value().deref())
                .map_err(|_| IrGenError::new(IGEKind::InvalidCallConv, attr.token().clone()))?
        } else {
            CallConv::Fast
        };

        signature.call_conv = call_conv;

        let inline_level = if let Some(attr) = self.find_attribute("inline") {
            self.assert_atr_len(attr, 1)?;
            InlineLevel::from_str(attr[0].token().value().deref())
                .map_err(|_| IrGenError::new(IGEKind::InvalidInlineLevel, attr.token().clone()))?
        } else {
            InlineLevel::Never
        };

        signature.call_conv = call_conv;

        let fun = Fun::new(
            self.object_module
                .declare_function(name.deref(), linkage, &signature)
                .unwrap(),
            name,
            fun_params,
            return_type,
            inline_level,
            Some(signature),
            ast.remove(1),
        );

        Ok(Cell::new(fun))
    }

    fn create_static_data(
        &mut self,
        name: &str,
        content: DataContentOption,
        linkage: Linkage,
        mutable: bool,
        tls: bool,
    ) -> Result<DataId> {
        let id = self
            .object_module
            .declare_data(name, linkage, mutable, tls)
            .unwrap();

        if linkage != Linkage::Import {
            match content {
                DataContentOption::Data(content) => {
                    self.data_context
                        .define(content.to_vec().into_boxed_slice());
                }
                DataContentOption::ZeroMem(size) => {
                    self.data_context.define_zeroinit(size);
                }
                _ => panic!("not imported data has to have a form"),
            }

            self.object_module
                .define_data(id, &self.data_context)
                .unwrap();

            self.data_context.clear();
        } else if content != DataContentOption::None {
            panic!("imported data cannot have a form");
        }

        Ok(id)
    }

    fn isa(&self) -> &dyn TargetIsa {
        self.object_module.isa()
    }

    fn pointer_of(&mut self, mutable: bool, datatype: &Cell<Datatype>) -> Cell<Datatype> {
        let datatype = Datatype::with_size(
            format!("ptr {}", datatype.name()),
            DKind::Pointer(datatype.clone(), mutable),
            self.isa().pointer_type().bytes(),
        );

        self.datatype_pool.wrap(datatype)
    } 

    fn find_datatype(&mut self, ast: &Ast) -> Result<Cell<Datatype>> {
        let is_pointer = ast.kind() == AKind::UnaryOperation && ast.token().value().deref() == "&";
        let token = if is_pointer {
            ast[1].token()
        } else {
            ast.token()
        };
        let datatype = self.current_module
            .find_datatype(token.value())
            .map(|d| d.0)
            .ok_or_else(|| IrGenError::new(IGEKind::TypeNotFound, token.clone()))?;
        Ok(if is_pointer {
            self.pointer_of(false, &datatype)
        } else {
            datatype
        })
    }

    fn find_function(&self, token: &Token) -> Result<Cell<Fun>> {
        self.current_module
            .find_function(token)
            .map(|f| f.0)
            .ok_or_else(|| IrGenError::new(IGEKind::FunctionNotFound, token.clone()))
    }

    fn find_variable(&self, token: &Token) -> Result<&Var> {
        self.variables
            .iter()
            .rev()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
            .find(|var| var.name().deref() == token.value().deref())
            .ok_or_else(|| IrGenError::new(IGEKind::VariableNotFound, token.clone()))
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
            .find(|a| a.token().value().deref() == name)
            .or(self
                .pushed_attributes
                .iter()
                .rev()
                .find(|a| a.token().value().deref() == name))
    }

    fn assert_atr_len(&self, attr: &Ast, expected: usize) -> Result<()> {
        if attr.len() < expected {
            Err(IrGenError::new(
                IGEKind::MissingAttrArgument(attr.len(), expected),
                attr.token().clone(),
            ))
        } else {
            Ok(())
        }
    }
}

fn assert_arg_count(ast: &Ast, expected: usize) -> Result<()> {
    if ast.len() - 1 < expected {
        Err(IrGenError::new(
            IGEKind::InvalidAmountOfArguments(ast.len(), expected),
            ast.token().clone(),
        ))
    } else {
        Ok(())
    }
}

fn assert_type(token: &Token, actual: &Cell<Datatype>, expected: &Cell<Datatype>) -> Result<()> {
    if actual != expected {
        Err(IrGenError::new(
            IGEKind::TypeMismatch(actual.clone(), expected.clone()),
            token.clone(),
        ))
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Enum {}

impl<'a> SealCurrentBlock for FunctionBuilder<'a> {
    fn seal_current_block(&mut self) {
        self.seal_block(self.current_block().unwrap());
    }
}

trait SealCurrentBlock {
    fn seal_current_block(&mut self);
}

const MOVERS: &'static [Type] = &[I8, I16, I32, I64];
const MOVER_SIZES: &'static [u32] = &[1, 2, 4, 8];
const MAX_MOVER_SIZE: u32 = 64;

fn find_best_mover(size: u32) -> (Type, u32) {
    let size = size.min(MAX_MOVER_SIZE);
    MOVER_SIZES
        .iter()
        .rev()
        .position(|&s| s <= size)
        .map(|i| {
            (
                MOVERS[MOVERS.len() - i - 1],
                MOVER_SIZES[MOVER_SIZES.len() - i - 1],
            )
        })
        .unwrap()
}

fn static_memset(
    pointer: Value,
    pointer_offset: u32,
    value: i8,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    let (mover, mover_size) = find_best_mover(size);

    let flags = MemFlags::new();

    let value = builder.ins().iconst(mover, value as i64);

    let mut offset = 0;
    loop {
        builder
            .ins()
            .store(flags, value, pointer, (offset + pointer_offset) as i32);
        offset += mover_size;
        if offset + mover_size >= size {
            break;
        }
    }

    if size > offset {
        // overlap should not matter
        let offset = size - mover_size;
        builder
            .ins()
            .store(flags, value, pointer, (offset + pointer_offset) as i32);
    }
}

fn static_memmove(
    dst_pointer: Value,
    dst_pointer_offset: u32,
    src_pointer: Value,
    src_pointer_offset: u32,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    let (mover, mover_size) = find_best_mover(size);

    let flags = MemFlags::new();

    let mut offset = 0;
    loop {
        let value = builder.ins().load(
            mover,
            flags,
            src_pointer,
            (offset + src_pointer_offset) as i32,
        );
        builder.ins().store(
            flags,
            value,
            dst_pointer,
            (offset + dst_pointer_offset) as i32,
        );
        offset += mover_size;
        if offset + mover_size > size {
            break;
        }
    }

    if size > offset {
        // overlap should not matter
        let offset = size - mover_size;
        let value = builder.ins().load(
            mover,
            flags,
            src_pointer,
            (offset + src_pointer_offset) as i32,
        );
        builder.ins().store(
            flags,
            value,
            dst_pointer,
            (offset + dst_pointer_offset) as i32,
        );
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DataContentOption<'a> {
    None,
    Data(&'a [u8]),
    ZeroMem(usize),
}
