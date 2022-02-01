use std::ops::{Deref, DerefMut};

use crate::ast::{AstDisplay, AstEnt, OpKind, Vis, Ast, CallConv};
use crate::incr::IncrementalData;
use crate::lexer::{Span, Token, self, token, ErrorDisplayState, DisplayError};
use crate::modules::Mod;
use crate::types::{Ty, Signature, self, ALL_BUILTIN_TYPES, I8_TY, I16_TY, I32_TY, I64_TY, U8_TY, U16_TY, U32_TY, U64_TY, INT_TY, UINT_TY, F64_TY, F32_TY, BOOL_TY};
use crate::util::sdbm::ID;
use crate::util::Size;

use cranelift::codegen::ir::types::I64;
use cranelift::codegen::ir::{GlobalValue, Value};
use cranelift::codegen::packed_option::{PackedOption, ReservedValue};
use cranelift::entity::{EntityList, EntitySet, ListPool, SparseMap, SparseMapValue, PoolMap};
use cranelift::module::Linkage;
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

type Result<T = ()> = std::result::Result<T, Error>;
type ExprResult = Result<Option<Local>>;

#[derive(Default)]
pub struct Ctx {
    ctx: types::Ctx,

    vars: Vec<(ID, Value)>,
    loops: Vec<Loop>,
    frames: Vec<usize>,
    labels: Vec<(ID, EntityList<Command>, Option<Section>)>,
    label_insts: ListPool<Command>,

    in_assign: bool,
    in_var_ref: bool,

    unresolved_globals: Vec<Global>,
    resolved_globals: Vec<Global>,
    unresolved: Vec<Fun>,
    entry_points: Vec<Fun>,

    entry_point_data: MainFunData,

    funs: PoolMap<Fun, FunEnt>,
    generic_funs: SparseMap<Fun, GFun>,
    globals: PoolMap<Global, GlobalEnt>,

    do_stacktrace: bool,
}

impl Ctx {
    /*pub fn parse(&mut self, module: Mod) -> Result {
        TParser::new(self.state, self.context)
            .parse(module)
            .map_err(|err| FError::new(error::Kind::TypeError(err), Token::default()))?;

        self.module = module;

        self.init_module(module);
        self.collect(module)?;
        self.translate()?;
        self.finalize_module(module);

        Ok(())
    }

    pub fn finalize_module(&mut self, module: Mod) {
        let MainFunData {
            id, return_value, ..
        } = self.context.entry_point_data;
        let mut body = self.funs[id].body;
        self.modules[module].add_return_stmt(Some(return_value), Token::default(), &mut body);
        self.funs[id].body = body;
        //self.context.entry_points.push(id);
    }

    pub fn init_module(&mut self, module: Mod) {
        let int = self.builtin_repo.int;
        let module_ent = &mut self.modules[module];
        let args = module_ent.add_type_slice(&[int, int]);
        let ret = PackedOption::from(int);
        let sig = Signature {
            call_conv: CallConv::Fast,
            args,
            ret,
        };
        let id = FUN_SALT.add(ID::new("--entry--")).add(module_ent.id);
        let fnu_ent = FunEnt {
            id,
            sig,
            module,
            kind: FKind::Represented,
            untraced: true,
            inline: true,

            ..Default::default()
        };
        let (shadow, id) = self.add_fun(module, fnu_ent);
        debug_assert!(shadow.is_none());
        let module_ent = &mut self.modules[module];
        module_ent.entry_point = PackedOption::from(id);
        let mut body = FunBody::default();
        let block = module_ent.new_block(&mut body);
        module_ent.select_block(block, &mut body);
        let arg1 = module_ent.add_temp_value(int);
        let arg2 = module_ent.add_temp_value(int);
        module_ent.push_block_arg(block, arg1);
        module_ent.push_block_arg(block, arg2);
        let init = module_ent.add_zero_value(int, &mut body);
        let return_value = module_ent.add_value(int, true);
        module_ent.add_var_decl(init, return_value, Token::default(), &mut body);
        let data = MainFunData {
            id,
            arg1,
            arg2,
            return_value,
        };
        self.context.entry_point_data = data;
        self.funs[id].body = body;
    }

    fn translate(&mut self) -> Result {
        while let Some(fun) = self.context.unresolved.pop() {
            self.translate_fun(fun)?;
        }

        Ok(())
    }

    fn translate_fun(&mut self, fun: Fun) -> Result {
        let mut shadowed = self.context.pool.get();
        let FunEnt {
            module,
            scope,
            ast,
            params,
            sig,
            base_fun,
            mut body,
            ..
        } = self.funs[fun];
        let module_ent = &self.modules[module];
        let header = module_ent.son(ast, 0);
        let ast_body = module_ent.son(ast, 1);
        let header_len = module_ent.ast_len(header);

        if module_ent.son(ast, 1).is_reserved_value() {
            self.finalize_fun(fun, body);
            return Ok(());
        }

        if !params.is_empty() {
            let param_len = module_ent.type_slice(params).len();
            for i in 0..param_len {
                let module_ent = &self.modules[module];
                let ty = module_ent.type_slice(params)[i];
                let id = self.generic_funs.get(base_fun.unwrap()).unwrap().sig.params[i];
                let id = TYPE_SALT.add(id).add(module_ent.id);
                shadowed.push((id, self.state.types.link(id, ty)))
            }
        }

        if !scope.is_reserved_value() {
            let ty = self.modules[module].son(scope, 1);
            let ty = self.parse_type(module, ty)?;
            let id = TYPE_SALT
                .add(ID::new("Self"))
                .add(self.state.modules[module].id);

            shadowed.push((id, self.state.types.link(id, ty)));
        }

        let module_ent = &mut self.modules[module];
        let entry_point = module_ent.new_block(&mut body);
        module_ent.select_block(entry_point, &mut body);

        self.context.vars.clear();

        // create arguments for signature
        let mut i = 0;
        for arg_group in 1..header_len - 2 {
            let module_ent = &mut self.modules[module];
            let &AstEnt { sons, kind, token } = module_ent.son_ent(header, arg_group);
            let arg_sons_len = module_ent.len(sons);
            for arg in 0..arg_sons_len - 1 {
                let module_ent = &mut self.modules[module];
                let id = module_ent.get_ent(sons, arg).token.span.hash;
                let ty = module_ent.type_slice(sig.args)[i];
                let var = module_ent.add_temp_value(ty);
                module_ent.push_block_arg(entry_point, var);
                let var = if kind == AKind::FunArgument(true) {
                    let carrier = module_ent.add_value(ty, true);
                    module_ent.add_var_decl(var, carrier, token, &mut body);
                    carrier
                } else {
                    var
                };
                self.context.vars.push((id, var));
                i += 1;
            }
        }

        // check if return value is too big and allocate additional argument for struct pointer
        // if thats the case
        let has_ret = sig.ret.is_some();
        if has_ret {
            let ty = sig.ret.unwrap();
            let ty_ent = &self.types[ty];
            if ty_ent.on_stack(self.ptr_ty) {
                let ty = self.pointer_of(ty, true);
                let module_ent = &mut self.modules[module];
                let value = module_ent.add_temp_value(ty);
                module_ent.push_block_arg(entry_point, value);
            }
        }

        let (value, hint) = self.block(fun, ast_body, &mut body)?;

        let closed = body.current_block.is_some();

        let module_ent = &mut self.modules[module];
        match (value, closed, has_ret) {
            (Some(value), true, true) => {
                let ret_ty = sig.ret.unwrap();
                let value_ty = module_ent.type_of_value(value);
                assert_type(value_ty, ret_ty, &hint)?;
                self.gen_return(fun, Some(value), hint, &mut body);
            }
            (_, true, true) => {
                let zero_value = module_ent.add_zero_value(sig.ret.unwrap(), &mut body);
                self.gen_return(fun, Some(zero_value), Token::default(), &mut body);
            }
            (_, true, _) => self.gen_return(fun, None, Token::default(), &mut body),
            _ => (),
        }

        for (id, shadow) in shadowed.drain(..) {
            self.state.types.remove_link(id, shadow);
        }

        self.finalize_fun(fun, body);

        Ok(())
    }

    fn finalize_fun(&mut self, fun: Fun, body: FunBody) {
        self.funs[fun].body = body;
        self.funs[fun].kind = FKind::Represented;
    }

    fn gen_return(&mut self, fun: Fun, value: Option<Value>, token: Token, body: &mut FunBody) {
        let module = self.funs[fun].module;

        let value = if let Some(value) = value {
            // if type is no stack we have to load current value into provided stack pointer from caller
            let ty = self.modules[module].type_of_value(value);
            if self.types[ty].on_stack(self.ptr_ty) {
                let module_ent = &mut self.modules[module];
                let entry_block = body.entry_block.unwrap();
                let struct_ptr = module_ent.last_arg_of_block(entry_block).unwrap();
                let deref = module_ent.add_value(ty, true);
                module_ent.add_inst(IKind::Deref(struct_ptr, false), deref, token, body);
                module_ent.add_inst(IKind::Assign(deref), value, token, body);
                Some(struct_ptr)
            } else {
                Some(value)
            }
        } else {
            None
        };

        self.modules[module].add_return_stmt(value, token, body);
    }

    fn block(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result<(Option<Value>, Token)> {
        if ast.is_reserved_value() {
            return Ok((None, Token::default()));
        }

        self.context.push_scope();

        let module = self.funs[fun].module;
        let module_ent = &self.modules[module];
        let sons = module_ent.sons(ast);
        let sons_len = module_ent.len(sons);

        // block can be treated as expression so we take result from the loop, if any
        let mut result = None;
        let mut token = Token::default();
        for i in 0..sons_len {
            if body.current_block.is_none() {
                self.context.pop_scope();
                return Ok((None, token));
            }
            let module_ent = &self.modules[module];
            let stmt = module_ent.get(sons, i);
            token = *module_ent.token(stmt);
            match module_ent.kind(stmt) {
                AKind::VarStatement(..) => self.var_statement(fun, stmt, body)?,
                AKind::ReturnStatement => self.return_statement(fun, stmt, body)?,
                AKind::Break => self.break_statement(fun, stmt, body)?,
                AKind::Continue => self.continue_statement(fun, stmt, body)?,
                _ => result = self.expr_low(fun, stmt, body)?,
            };
        }

        self.context.pop_scope();

        Ok((result, token))
    }

    fn continue_statement(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result {
        let module = self.funs[fun].module;
        let module_ent = &mut self.state.modules[module];
        let label = module_ent.son(ast, 0);
        let label = if label.is_reserved_value() {
            Token::default()
        } else {
            *module_ent.token(label)
        };
        let token = *module_ent.token(ast);
        let loop_header = self.context.find_loop(&label).map_err(|outside| {
            if outside {
                FError::new(error::Kind::ContinueOutsideLoop, token)
            } else {
                FError::new(error::Kind::WrongLabel, token)
            }
        })?;

        module_ent.add_valueless_inst(
            IKind::Jump(loop_header.start_block, EntityList::new()),
            token,
            body,
        );

        Ok(())
    }

    fn break_statement(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result {
        let module = self.funs[fun].module;
        let module_ent = &mut self.state.modules[module];
        let label = module_ent.son(ast, 0);
        let label = if label.is_reserved_value() {
            Token::default()
        } else {
            *module_ent.token(label)
        };
        let token = *module_ent.token(ast);

        let loop_header = self.context.find_loop(&label).map_err(|outside| {
            if outside {
                FError::new(error::Kind::BreakOutsideLoop, token)
            } else {
                FError::new(error::Kind::WrongLabel, token)
            }
        })?;

        let return_value_ast = module_ent.son(ast, 1);

        if return_value_ast != Ast::reserved_value() {
            let return_value = self.expr(fun, return_value_ast, body)?;
            let module_ent = &mut self.state.modules[module];
            let current_return_value = module_ent.last_arg_of_block(loop_header.end_block);
            if let Some(current_return_value) = current_return_value {
                let token = module_ent.token(return_value_ast);
                let return_ty = module_ent.type_of_value(return_value);
                let current_return_ty = module_ent.type_of_value(current_return_value);
                assert_type(current_return_ty, return_ty, token)?;
            } else {
                let ty = module_ent.type_of_value(return_value);
                let value = module_ent.add_temp_value(ty);
                module_ent.push_block_arg(loop_header.end_block, value);
            }

            let args = module_ent.add_values(&[return_value]);
            module_ent.add_valueless_inst(IKind::Jump(loop_header.end_block, args), token, body);
        } else {
            self.state.modules[module].add_valueless_inst(
                IKind::Jump(loop_header.end_block, EntityList::new()),
                token,
                body,
            );
        }

        Ok(())
    }

    fn return_statement(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result {
        let fun_ent = &self.funs[fun];
        let module = fun_ent.module;
        let ty = fun_ent.sig.ret;
        let module_ent = &mut self.state.modules[module];
        let token = *module_ent.token(ast);
        let return_value_ast = module_ent.son(ast, 0);

        if return_value_ast.is_reserved_value() {
            let value = if ty.is_some() {
                Some(module_ent.add_zero_value(ty.unwrap(), body))
            } else {
                None
            };
            self.gen_return(fun, value, token, body);
        } else {
            let token = *module_ent.token(return_value_ast);
            if ty.is_none() {
                return Err(FError::new(error::Kind::UnexpectedReturnValue, token));
            }
            let value = self.expr(fun, return_value_ast, body)?;
            let module_ent = &mut self.state.modules[module];
            let actual_type = module_ent.type_of_value(value);
            assert_type(actual_type, ty.unwrap(), &token)?;
            self.gen_return(fun, Some(value), token, body)
        };

        Ok(())
    }

    fn var_statement(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { kind, sons, .. } = module_ent.load(ast);
        let mutable = kind == AKind::VarStatement(Vis::None, true);
        let sons_len = module_ent.len(sons);

        for i in 0..sons_len {
            let module_ent = &self.state.modules[module];
            let var_line = module_ent.get(sons, i);
            let name_group = module_ent.son(var_line, 0);
            let ty = module_ent.son(var_line, 1);
            let value_group = module_ent.son(var_line, 2);
            let ty = if ty.is_reserved_value() {
                None
            } else {
                Some(self.parse_type(module, ty)?)
            };

            let module_ent = &mut self.state.modules[module];
            let sons = module_ent.sons(name_group);
            let sons_len = module_ent.len(sons);
            if value_group.is_reserved_value() {
                // in this case we just assign zero values to all variables
                for i in 0..sons_len {
                    let ty = ty.unwrap();
                    let token = *module_ent.token(module_ent.get(sons, i));
                    let zero_value = module_ent.add_zero_value(ty, body);

                    let var = module_ent.add_value(ty, mutable);
                    self.context.vars.push((token.span.hash, var));
                    module_ent.add_var_decl(zero_value, var, token, body)
                }
            } else {
                let values = module_ent.sons(value_group);
                // ast parser takes care of the one value multiple variables case
                // all missing values are pushed as pointer to the first one
                for i in 0..sons_len {
                    let module_ent = &self.state.modules[module];
                    let name_token = *module_ent.token(module_ent.get(sons, i));
                    let raw_value = module_ent.get(values, i);
                    let value_token = *module_ent.token(raw_value);
                    let value = self.expr(fun, raw_value, body)?;

                    let module_ent = &mut self.state.modules[module];
                    let actual_datatype = module_ent.type_of_value(value);

                    // consistency check
                    if let Some(ty) = ty {
                        assert_type(actual_datatype, ty, &value_token)?;
                    }

                    let var = module_ent.add_value(actual_datatype, mutable);
                    self.context.vars.push((name_token.span.hash, var));
                    module_ent.add_var_decl(value, var, name_token, body);
                }
            }
        }

        Ok(())
    }

    fn expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> Result<Value> {
        // common case is that we expect a value out of the expression though
        // mode specific errors may be useful (TODO)
        self.expr_low(fun, ast, body)?.ok_or_else(|| {
            let module = self.funs[fun].module;
            let module_ent = &self.state.modules[module];
            let token = *module_ent.token(ast);
            FError::new(error::Kind::ExpectedValue, token)
        })
    }

    fn expr_low(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let kind = module_ent.kind(ast);
        match kind {
            AKind::BinaryOp => self.binary_op(fun, ast, body),
            AKind::Lit => self.lit(fun, ast, body),
            AKind::Ident => self.ident(fun, ast, body),
            AKind::Call(_) => self.call(fun, ast, body),
            AKind::IfExpr => self.if_expr(fun, ast, body),
            AKind::Loop => self.loop_expr(fun, ast, body),
            AKind::DotExpr => self.dot_expr(fun, ast, body),
            AKind::Deref => self.deref_expr(fun, ast, body),
            AKind::Ref(mutable) => self.ref_expr(fun, ast, mutable, body),
            AKind::UnaryOp => self.unary_op(fun, ast, body),
            AKind::Pass => Ok(None),
            AKind::Array => self.array(fun, ast, body),
            AKind::Index => self.index(fun, ast, body),
            _ => todo!(
                "unmatched expr ast {}",
                AstDisplay::new(self.state, &module_ent.a_state, ast)
            ),
        }
    }

    fn index(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { token, sons, .. } = module_ent.load(ast);
        let target = module_ent.get(sons, 0);
        let index = module_ent.get(sons, 1);
        let target = self.expr(fun, target, body)?;
        let index = self.expr(fun, index, body)?;
        let args = &[target, index];
        let span = if self.context.in_var_ref {
            self.state.index_var_span
        } else {
            self.state.index_span
        };
        let result = self
            .call_low(fun, None, None, FUN_SALT, span, &[], args, token, body)?
            .ok_or_else(|| FError::new(error::Kind::ExpectedValue, token))?;

        Ok(Some(self.deref_expr_low(fun, result, token, body)?))
    }

    fn array(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let mut values = self.context.pool.get();
        let mut element_ty = None;
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let length = module_ent.len(sons);

        for i in 0..length {
            let module_ent = &self.state.modules[module];
            let raw_value = module_ent.get(sons, i);
            let token = *module_ent.token(raw_value);
            let value = self.expr(fun, raw_value, body)?;
            let module_ent = &self.state.modules[module];
            let ty = module_ent.type_of_value(value);
            if let Some(real_ty) = element_ty {
                assert_type(ty, real_ty, &token)?;
            } else {
                element_ty = Some(ty);
            }
            values.push((value, token));
        }

        if element_ty.is_none() {
            return Err(FError::new(error::Kind::EmptyArray, token));
        }

        let element_ty = element_ty.unwrap();
        let element_size = self.types[element_ty].size;

        let ty = self.state.array_of(self.module, element_ty, length);
        let module_ent = &mut self.state.modules[module];

        let temp = module_ent.add_temp_value(ty);
        module_ent.add_inst(IKind::Uninitialized, temp, token, body);
        let result = module_ent.add_value(ty, true);
        module_ent.add_var_decl(temp, result, token, body);

        for (i, &(value, token)) in values.iter().enumerate() {
            let offset = element_size.mul(Size::new(i as u32, i as u32));
            let offset = module_ent.offset_value(result, element_ty, offset, token, body);
            module_ent.assign(offset, value, token, body);
        }

        Ok(Some(result))
    }

    fn ref_expr(&mut self, fun: Fun, ast: Ast, mutable: bool, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let value = module_ent.get(sons, 0);

        let prev_in_var_ref = self.context.in_var_ref;
        let prev_in_assign = self.context.in_assign;
        self.context.in_assign = true;
        self.context.in_var_ref = mutable;
        let value = self.expr(fun, value, body)?;
        self.context.in_assign = prev_in_assign;
        self.context.in_var_ref = prev_in_var_ref;

        self.ref_expr_low(fun, value, token, mutable, body)
            .map(|v| Some(v))
    }

    fn ref_expr_low(
        &mut self,
        fun: Fun,
        value: Value,
        token: Token,
        mutable: bool,
        body: &mut FunBody,
    ) -> Result<Value> {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let ValueEnt {
            ty,
            mutable: prev_mutable,
            ..
        } = module_ent.values[value];

        if !prev_mutable && mutable {
            return Err(FError::new(error::Kind::MutableToImmutable, token));
        }

        let ty = self.pointer_of(ty, mutable);
        let module_ent = &mut self.state.modules[module];
        let reference = module_ent.reference(ty, value, token, body);

        // we need to allocate it since register cannot be referenced
        let mut current = reference;
        loop {
            let value = module_ent.load_value_mut(current);
            if value.on_stack {
                break;
            }
            value.on_stack = true;

            if value.inst.is_some() {
                let inst = value.inst.unwrap();
                match module_ent.inst_kind(inst) {
                    IKind::Ref(value) | IKind::Offset(value) | IKind::Cast(value) => {
                        current = value;
                        continue;
                    }
                    _ => (),
                }
            }

            break;
        }

        Ok(reference)
    }

    fn deref_expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { token, sons, .. } = module_ent.load(ast);
        let value = module_ent.get(sons, 0);
        let expr = self.expr(fun, value, body)?;

        let value = self.deref_expr_low(fun, expr, token, body)?;

        Ok(Some(value))
    }

    fn deref_expr_low(
        &mut self,
        fun: Fun,
        target: Value,
        token: Token,
        body: &mut FunBody,
    ) -> Result<Value> {
        let in_assign = self.context.in_assign;
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let ty = module_ent.type_of_value(target);
        let pointed = self.pointer_base(ty, token)?;
        let mutable = self.pointer_mutability(ty);

        let module_ent = &mut self.state.modules[module];
        let value = module_ent.add_value(pointed, mutable);
        module_ent.add_inst(IKind::Deref(target, in_assign), value, token, body);

        Ok(value)
    }

    fn unary_op(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let expr = module_ent.get(sons, 1);
        let op = module_ent.get(sons, 0);
        let op = module_ent.token(op).span;
        let value = self.expr(fun, expr, body)?;

        self.call_low(fun, None, None, UNARY_SALT, op, &[], &[value], token, body)
    }

    fn dot_expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let header = module_ent.get(sons, 0);
        let field = module_ent.get(sons, 1);
        let header = self.expr(fun, header, body)?;
        let module_ent = &mut self.state.modules[module];
        let field = *module_ent.token(field);

        Ok(Some(self.field_access(
            fun,
            header,
            field.span.hash,
            token,
            body,
        )?))
    }

    fn find_field(&mut self, ty: Ty, field_id: ID, path: &mut Vec<usize>) -> bool {
        let mut frontier = self.context.pool.get();
        frontier.push((usize::MAX, 0, ty));

        let mut i = 0;
        while i < frontier.len() {
            let stype = match &self.types[frontier[i].2].kind {
                TKind::Structure(stype) => stype,
                &TKind::Pointer(pointed, _) => match &self.types[pointed].kind {
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

    fn loop_expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &mut self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let label = module_ent.get(sons, 0);
        let name = if label.is_reserved_value() {
            ID(0)
        } else {
            module_ent.token(label).span.hash
        };

        let start_block = module_ent.new_block(body);
        let end_block = module_ent.new_block(body);

        let header = Loop {
            name,
            start_block,
            end_block,
        };

        module_ent.add_valueless_inst(IKind::Jump(start_block, EntityList::new()), token, body);

        self.context.loops.push(header);
        module_ent.select_block(start_block, body);
        let block_ast = module_ent.get(sons, 1);
        self.block(fun, block_ast, body)?;
        self.context
            .loops
            .pop()
            .expect("expected previously pushed header");

        let module_ent = &mut self.state.modules[module];
        if body.current_block.is_some() {
            module_ent.add_valueless_inst(IKind::Jump(start_block, EntityList::new()), token, body);
        }
        module_ent.select_block(end_block, body);

        Ok(module_ent.last_arg_of_block(end_block))
    }

    fn if_expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let bool_type = self.state.builtin_repo.bool;
        let module_ent = &mut self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let cond_ast = module_ent.get(sons, 0);
        let cond_ast_token = *module_ent.token(cond_ast);
        let cond_val = self.expr(fun, cond_ast, body)?;
        let module_ent = &mut self.state.modules[module];
        let cond_type = module_ent.type_of_value(cond_val);

        assert_type(cond_type, bool_type, &cond_ast_token)?;

        let then_block = module_ent.new_block(body);
        module_ent.add_valueless_inst(
            IKind::JumpIfTrue(cond_val, then_block, EntityList::new()),
            cond_ast_token,
            body,
        );

        let merge_block = module_ent.new_block(body);

        let else_branch_ast = module_ent.get(sons, 2);
        let (else_block, jump_to, else_branch_token) = if else_branch_ast.is_reserved_value() {
            (None, merge_block, Token::default())
        } else {
            let some_block = module_ent.new_block(body);
            (
                Some(some_block),
                some_block,
                *module_ent.token(else_branch_ast),
            )
        };

        module_ent.add_valueless_inst(
            IKind::Jump(jump_to, EntityList::new()),
            else_branch_token,
            body,
        );

        module_ent.select_block(then_block, body);

        let then_branch = module_ent.get(sons, 1);

        let (then_result, _) = self.block(fun, then_branch, body)?;

        let module_ent = &mut self.state.modules[module];
        let mut result = None;
        let mut jump_inst = None;
        let mut then_filled = false;
        if let (Some(val), Some(_)) = (then_result, else_block) {
            let args = module_ent.add_values(&[val]);
            jump_inst =
                Some(module_ent.add_valueless_inst(IKind::Jump(merge_block, args), token, body));
            let ty = module_ent.type_of_value(val);
            let value = module_ent.add_temp_value(ty);
            let args = module_ent.add_values(&[value]);
            module_ent.set_block_args(merge_block, args);
            result = Some(value);
        } else if body.current_block.is_some() {
            module_ent.add_valueless_inst(IKind::Jump(merge_block, EntityList::new()), token, body);
        } else {
            then_filled = true;
        }

        if !else_branch_ast.is_reserved_value() {
            let else_block = else_block.unwrap();
            module_ent.select_block(else_block, body);
            let (else_result, hint) = self.block(fun, else_branch_ast, body)?;
            let module_ent = &mut self.state.modules[module];
            if let Some(value) = else_result {
                let args = module_ent.add_values(&[value]);
                module_ent.add_valueless_inst(IKind::Jump(merge_block, args), hint, body);
                if result.is_some() {
                    // do nothing
                } else if then_filled {
                    let ty = module_ent.type_of_value(value);
                    let value = module_ent.add_temp_value(ty);
                    module_ent.push_block_arg(merge_block, value);
                    result = Some(value);
                } else {
                    return Err(FError::new(error::Kind::UnexpectedValue, token));
                }
            } else {
                if body.current_block.is_some() {
                    if let Some(jump_inst) = jump_inst {
                        module_ent.insts[jump_inst].kind =
                            IKind::Jump(merge_block, EntityList::new());
                        module_ent.set_block_args(merge_block, EntityList::new());
                    }
                    if result.is_some() {
                        return Err(FError::new(error::Kind::ExpectedValue, token));
                    }
                    module_ent.add_valueless_inst(
                        IKind::Jump(merge_block, EntityList::new()),
                        token,
                        body,
                    );
                }
            }
        }

        self.modules[module].select_block(merge_block, body);

        Ok(result)
    }

    fn call(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let mut values = self.context.pool.get();
        let mut types = self.context.pool.get();
        let do_stacktrace = self.state.do_stacktrace;
        let module = self.funs[fun].module;
        let module_ent = &self.modules[module];
        let &AstEnt { sons, token, kind } = module_ent.load(ast);
        let dot_call = kind == AKind::Call(true);
        let sons_len = module_ent.len(sons);
        let caller = module_ent.get(sons, 0);
        let caller_kind = module_ent.kind(caller);
        for i in 1..sons_len {
            let value = self.modules[module].get(sons, i);
            let value = self.expr(fun, value, body)?;
            values.push(value);
            types.push(self.modules[module].type_of_value(value));
        }

        let mut generic_params = self.context.pool.get();
        let module_ent = &mut self.modules[module];
        let name = match caller_kind {
            AKind::Ident | AKind::Path => caller,
            AKind::Deref => {
                let pointer_ast = module_ent.son(caller, 0);
                let pointer_ast_token = *module_ent.token(pointer_ast);
                let pointer = self.expr(fun, pointer_ast, body)?;
                let module_ent = &self.state.modules[module];
                let ty = module_ent.type_of_value(pointer);

                let (mismatched, ret) = {
                    let fp_module = self.types[ty].module;
                    let fp = match self.types[ty].kind {
                        TKind::FunPointer(fp) => fp,
                        _ => {
                            return Err(FError::new(
                                error::Kind::ExpectedFunctionPointer,
                                pointer_ast_token,
                            ));
                        }
                    };

                    (
                        self.modules[fp_module].verify_args(&self.types, &types, fp.args),
                        fp.ret,
                    )
                };

                if mismatched {
                    return Err(FError::new(
                        error::Kind::FunPointerArgMismatch(
                            ty,
                            values
                                .iter()
                                .map(|&v| module_ent.type_of_value(v))
                                .collect(),
                        ),
                        token,
                    ));
                }

                if do_stacktrace {
                    self.gen_frame_push(fun, token, body);
                }

                let module_ent = &mut self.state.modules[module];

                let args = module_ent.add_values(&values);
                let value = if ret.is_none() {
                    module_ent.add_valueless_inst(
                        IKind::FunPointerCall(pointer, args),
                        token,
                        body,
                    );
                    None
                } else {
                    let value = module_ent.add_temp_value(ret.unwrap());
                    module_ent.add_inst(IKind::FunPointerCall(pointer, args), value, token, body);
                    Some(value)
                };

                if do_stacktrace {
                    self.gen_frame_pop(fun, token, body);
                }

                return Ok(value);
            }
            AKind::Instantiation => {
                let len = module_ent.ast_len(caller);
                for i in 1..len {
                    let param = self.modules[module].son(caller, i);
                    let ty = self.parse_type(module, param)?;
                    generic_params.push(ty);
                }
                self.modules[module].son(caller, 0)
            }
            _ => unreachable!(),
        };

        let (module, caller, name) = self.parse_ident(module, name)?;

        let caller = if dot_call { None } else { Some(caller) };

        self.call_low(
            fun,
            module,
            caller,
            FUN_SALT,
            name.span,
            &generic_params,
            &values,
            token,
            body,
        )
    }

    fn call_low(
        &mut self,
        fun: Fun,
        target: Option<Mod>,
        caller: Option<Option<Ty>>,
        salt: ID,
        name: Span,
        params: &[Ty],
        original_values: &[Value],
        token: Token,
        body: &mut FunBody,
    ) -> ExprResult {
        let mut module_buffer = self.context.pool.get();
        let mut values = self.context.pool.get();
        let mut types = self.context.pool.get();
        let module = self.funs[fun].module;
        let module_ent = &self.modules[module];
        values.extend_from_slice(original_values);
        types.extend(values.iter().map(|&v| module_ent.type_of_value(v)));

        let id = salt.add(name.hash);

        let (result, field, final_type) = if let Some(caller) = caller {
            let caller = caller.map(|caller| self.types[caller].id).unwrap_or(ID(0));
            let id = id.add(caller);
            (
                self.find_item(module, id, target, &mut module_buffer),
                None,
                None,
            )
        } else {
            let v = original_values[0];
            let ty = module_ent.type_of_value(v);

            let mut result = (Ok(None), None, None);
            let mut fields = self.context.pool.get();
            let mut i = 0;
            fields.push((None, ty));
            while i < fields.len() {
                let (field, ty) = fields[i];
                let ty = self.t_state.pointer_base(ty).unwrap_or(ty);
                let base_ty = self.t_state.base_of(ty);
                let ty_id = self.types[base_ty].id;
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
                match &self.types[ty].kind {
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

        let other_fun = result
            .map_err(|(a, b)| FError::new(error::Kind::AmbiguousFunction(a, b), token))?
            .ok_or_else(|| {
                FError::new(
                    error::Kind::FunctionNotFound(name.clone(), types.to_vec()),
                    token,
                )
            })?;

        let other_fun = if let FKind::Generic = self.funs[other_fun].kind {
            if caller.is_none() {
                let g_fun = self.generic_funs.get(other_fun).unwrap();
                // figure out whether receiver is pointer
                let (pointer, mutable) = match g_fun.sig.elements[1] {
                    GenericElement::Pointer(mutable) => (true, mutable),
                    _ => (false, false),
                };
                let (other_pointer, other_mutable) = match &self.types[types[0]].kind {
                    &TKind::Pointer(_, mutable) => (true, mutable),
                    _ => (false, false),
                };

                match (pointer, other_pointer) {
                    (true, false) => {
                        types[0] = self.pointer_of(types[0], mutable);
                        self.create(other_fun, params, &types)?
                    }
                    (false, true) => {
                        types[0] = self.t_state.pointer_base(types[0]).unwrap();
                        self.create(other_fun, params, &types)?
                    }
                    (true, true) if mutable && !other_mutable => None,
                    _ => self.create(other_fun, params, &types)?,
                }
            } else {
                self.create(other_fun, params, &types)?
            }
            .ok_or_else(|| {
                FError::new(error::Kind::GenericMismatch(name.clone(), types.to_vec()), token)
            })?
        } else {
            other_fun
        };

        let FunEnt {
            kind: other_kind,
            module: other_module,
            untraced,
            sig:
                Signature {
                    args: sig_args,
                    ret,
                    ..
                },
            vis,
            ..
        } = self.funs[other_fun];

        let value = if ret.is_some() {
            let ret = ret.unwrap();
            let on_stack = self.types[ret].on_stack(self.ptr_ty);
            let value = self.modules[module].add_value(ret, on_stack);
            if on_stack {
                values.push(value);
            }
            Some(value)
        } else {
            None
        };

        let mut changed = caller.is_none();
        if changed {
            if let Some(field) = field {
                values[0] = self.field_access(fun, values[0], field, token, body)?;
            }

            let first_arg_ty = self.modules[other_module].type_slice(sig_args)[0];
            let first_real_arg_ty = self.modules[module].type_of_value(values[0]);

            if first_real_arg_ty != first_arg_ty {
                if self.t_state.pointer_base(first_real_arg_ty) == Some(first_arg_ty) {
                    values[0] = self.deref_expr_low(fun, values[0], token, body)?;
                } else if self.t_state.pointer_base(first_arg_ty) == Some(first_real_arg_ty) {
                    let mutable = self.pointer_mutability(first_arg_ty);
                    values[0] = self.ref_expr_low(fun, values[0], token, mutable, body)?;
                } else {
                    // adjust mutability if '&var' instead of '&' is passed
                    let mutability_mismatch = matches!(
                        (
                            &self.types[first_real_arg_ty].kind,
                            &self.types[first_arg_ty].kind
                        ),
                        (&TKind::Pointer(_, a), &TKind::Pointer(_, b)) if a != b && b && !a
                    );
                    if mutability_mismatch {
                        types[0] = first_arg_ty; // just overwrite to so it matches later check
                    }
                    changed = false;
                }

                debug_assert!(
                    self.modules[module].type_of_value(values[0]) == first_arg_ty || !changed,
                    "{}({:?}) != {}({:?})",
                    TypeDisplay::new(self.state, self.modules[module].type_of_value(values[0])),
                    self.modules[module].type_of_value(values[0]),
                    TypeDisplay::new(self.state, first_arg_ty),
                    first_arg_ty,
                );
            }
        }

        if changed {
            types[0] = self.modules[module].type_of_value(values[0]);
        }

        let mismatched = self.modules[other_module].verify_args(&self.types, &types, sig_args);

        if mismatched {
            return Err(FError::new(
                error::Kind::FunArgMismatch(other_fun, types.to_vec()),
                token,
            ));
        }

        let do_stacktrace =
            self.state.do_stacktrace && !untraced && !matches!(other_kind, FKind::Builtin);

        if do_stacktrace {
            self.gen_frame_push(fun, token, body);
        }

        if !self.state.can_access(module, other_module, vis) {
            return Err(FError::new(error::Kind::VisibilityViolation, token));
        }

        let module_ent = &mut self.modules[module];
        let args = module_ent.add_values(&values);

        if let Some(value) = value {
            module_ent.add_inst(IKind::Call(other_fun, args), value, token, body);
        } else {
            module_ent.add_valueless_inst(IKind::Call(other_fun, args), token, body);
        }

        module_ent.add_dependant_function(other_fun, body);

        if do_stacktrace {
            self.gen_frame_pop(fun, token, body);
        }

        Ok(value)
    }

    fn gen_frame_pop(&mut self, fun: Fun, token: Token, body: &mut FunBody) {
        let module = self.funs[fun].module;
        let pop = self.state.funs.index(self.pop_fun_hahs).unwrap().clone();
        self.modules[module].add_valueless_call(pop, &[], token, body);
    }

    fn gen_frame_push(&mut self, fun: Fun, token: Token, body: &mut FunBody) {
        let push = self.state.funs.index(self.push_fun_hash).unwrap().clone();
        let int = self.state.builtin_repo.int;
        let u8 = self.state.builtin_repo.u8;
        let module = self.funs[fun].module;
        let module_ent = &mut self.modules[module];

        // line argument
        let line = module_ent.add_temp_value(int);
        module_ent.add_inst(
            IKind::Lit(LTKind::Int(token.span.line as i64, 0)),
            line,
            token,
            body,
        );

        // column argument
        let column = module_ent.add_temp_value(int);
        module_ent.add_inst(
            IKind::Lit(LTKind::Int(token.span.column as i64, 0)),
            column,
            token,
            body,
        );

        // file name argument
        let file_name = &self.state.sources[token.span.source].name;
        let mut final_file_name = String::with_capacity(file_name.len() + 1);
        final_file_name.push_str(file_name);
        final_file_name.push('\x00');
        let span = self.state.builtin_span(&final_file_name);
        let ptr = self.pointer_of(u8, false);
        let module_ent = &mut self.modules[module];
        let file_name = module_ent.add_temp_value(ptr);
        module_ent.add_inst(IKind::Lit(LTKind::String(span)), file_name, token, body);

        module_ent.add_valueless_call(push, &[line, column, file_name], token, body);
    }

    fn ident(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let (target, caller, name) = self.parse_ident(module, ast)?;
        let can_be_local = target.is_none() && caller.is_none();
        let caller = caller.map(|c| self.types[c].id).unwrap_or(ID(0));
        let token = *self.modules[module].token(ast);

        let result = (|| {
            if can_be_local {
                if let Some(var) = self
                    .context
                    .find_variable(name.span.hash)
                    .or_else(|| self.find_constant_parameter(fun, name, body))
                {
                    return Ok(Some(var));
                }
            }

            if let Some(global) = self.find_global(fun, target, caller, name, body)? {
                return Ok(Some(global));
            }

            if let Some(pointer) = self.find_function_pointer(fun, target, caller, name, body)? {
                return Ok(Some(pointer));
            }

            Ok(None)
        })()?
        .ok_or_else(|| FError::new(error::Kind::UndefinedVariable, token))?;

        Ok(Some(result))
    }

    fn parse_ident(&mut self, module: Mod, ast: Ast) -> Result<(Option<Mod>, Option<Ty>, Token)> {
        let module_ent = &self.modules[module];
        let &AstEnt { kind, sons, token } = module_ent.load(ast);
        if kind == AKind::Ident {
            Ok((None, None, token))
        } else {
            match module_ent.slice(sons) {
                &[module_name, caller_name, name] => {
                    let module_name_token = *module_ent.token(module_name);
                    let name_token = *module_ent.token(name);
                    let dep = self
                        .find_dep(module, &module_name_token)
                        .ok_or_else(|| FError::new(error::Kind::UnknownModule, module_name_token))?;
                    let caller = self.parse_type(dep, caller_name)?;
                    let caller = self.t_state.base_of(caller);
                    Ok((Some(dep), Some(caller), name_token))
                }
                &[package_or_caller, name] => {
                    let package_or_caller_token = *module_ent.token(package_or_caller);
                    let name_token = *module_ent.token(name);
                    if let Some(dep) = self.find_dep(module, &package_or_caller_token) {
                        Ok((Some(dep), None, name_token))
                    } else {
                        let caller = self.parse_type(module, package_or_caller)?;
                        let caller = self.t_state.base_of(caller);
                        Ok((None, Some(caller), name_token))
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
        ident: Token,
        body: &mut FunBody,
    ) -> ExprResult {
        let mut module_buffer = self.context.pool.get();
        let module = self.funs[fun].module;
        let id = FUN_SALT.add(ident.span.hash).add(caller);
        Ok(
            match self
                .find_item(module, id, target, &mut module_buffer)
                .map_err(|(a, b)| FError::new(error::Kind::AmbiguousFunction(a, b), ident))?
            {
                Some(f) => {
                    let FunEnt {
                        vis,
                        sig,
                        module: other_module,
                        ..
                    } = self.funs[f];
                    if !self.state.can_access(module, other_module, vis) {
                        return Err(FError::new(error::Kind::VisibilityViolation, ident));
                    }
                    // we store the pointers in the module function comes from,
                    // this makes it more likely we will reuse already instantiated
                    // pointers, it also means we don't have to reallocate signature
                    // to modules pool
                    let ty = self.state.function_type_of(self.module, other_module, sig);
                    let module_ent = &mut self.modules[module];
                    let value = module_ent.add_temp_value(ty);
                    module_ent.add_inst(IKind::FunPointer(f), value, ident, body);
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
        name: Token,
        body: &mut FunBody,
    ) -> ExprResult {
        let module = self.funs[fun].module;

        let id = GLOBAL_SALT.add(name.span.hash).add(caller);

        let mut module_buffer = self.context.pool.get();
        let global = self
            .find_item(module, id, target, &mut module_buffer)
            .map_err(|(a, b)| FError::new(error::Kind::AmbiguousGlobal(a, b), name))?;

        let found = if let Some(found) = global {
            let GlobalEnt { vis, module, .. } = self.globals[found];
            if !self.state.can_access(module, module, vis) {
                return Err(FError::new(error::Kind::GlobalVisibilityViolation, name));
            }
            found
        } else {
            return Ok(None);
        };

        let GlobalEnt { ty, mutable, .. } = self.state.globals[found];
        let module_ent = &mut self.modules[module];
        let value = module_ent.add_value(ty, mutable);
        module_ent.add_inst(IKind::GlobalLoad(found), value, name, body);
        module_ent.add_dependant_global(found, body);

        Ok(Some(value))
    }

    fn find_constant_parameter(
        &mut self,
        fun: Fun,
        token: Token,
        body: &mut FunBody,
    ) -> Option<Value> {
        let FunEnt {
            module,
            params,
            base_fun,
            ..
        } = self.funs[fun];
        if base_fun.is_none() {
            return None;
        }
        let module_ent = &self.modules[module];
        let name = TYPE_SALT.add(token.span.hash).add(module_ent.id);
        let sig_params = &self.generic_funs.get(base_fun.unwrap()).unwrap().sig.params;
        let ty = sig_params
            .iter()
            .position(|&e| {
                let hash = TYPE_SALT.add(e).add(module_ent.id);
                hash == name
            })
            .map(|i| module_ent.type_slice(params)[i]);
        if let Some(ty) = ty {
            match &self.types[ty].kind {
                &TKind::Constant(t) => {
                    let repo = self.state.builtin_repo;
                    let (kind, ty) = match t {
                        TypeConst::Bool(val) => (LTKind::Bool(val), repo.bool),
                        TypeConst::Int(val) => (LTKind::Int(val, 0), repo.int),
                        TypeConst::Float(val) => (LTKind::Float(val, 64), repo.f64),
                        TypeConst::Char(val) => (LTKind::Char(val), repo.u32),
                        TypeConst::String(val) => {
                            (LTKind::String(val), self.pointer_of(repo.u8, false))
                        }
                    };

                    let module_ent = &mut self.modules[module];
                    let value = module_ent.add_temp_value(ty);
                    module_ent.add_inst(IKind::Lit(kind), value, token, body);
                    Some(value)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn lit(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.modules[module];
        let token = *module_ent.token(ast);
        let repo = self.state.builtin_repo;
        let ty = match token.kind {
            LTKind::Int(_, base) => match base {
                8 => repo.i8,
                16 => repo.i16,
                32 => repo.i32,
                64 => repo.i64,
                _ => repo.int,
            },
            LTKind::Uint(_, base) => match base {
                8 => repo.u8,
                16 => repo.u16,
                32 => repo.u32,
                64 => repo.u64,
                _ => repo.uint,
            },
            LTKind::Float(_, base) => match base {
                32 => repo.f32,
                _ => repo.f64,
            },
            LTKind::Bool(_) => repo.bool,
            LTKind::Char(_) => repo.u32,
            LTKind::String(_) => self.pointer_of(repo.u8, false),
            _ => unreachable!(
                "{}",
                AstDisplay::new(self.state, &self.modules[module].a_state, ast)
            ),
        };

        let module_ent = &mut self.modules[module];
        let value = module_ent.add_temp_value(ty);

        module_ent.add_inst(IKind::Lit(token.kind.clone()), value, token, body);

        Ok(Some(value))
    }

    fn binary_op(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &mut self.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let op = module_ent.get_ent(sons, 0).token;

        if op.span.hash == ID::new("=") {
            return self.assignment(fun, ast, body);
        } else if op.span.hash == ID::new("as") {
            return self.bit_cast(fun, ast, body);
        }

        let left = module_ent.get(sons, 1);
        let right = module_ent.get(sons, 2);

        let left = self.expr(fun, left, body)?;
        let right = self.expr(fun, right, body)?;

        self.call_low(
            fun,
            None,
            None,
            BINARY_SALT,
            op.span,
            &[],
            &[left, right],
            token,
            body,
        )
    }

    fn bit_cast(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &mut self.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let target = module_ent.get(sons, 1);
        let ty = module_ent.get(sons, 2);
        let target = self.expr(fun, target, body)?;
        let ty = self.parse_type(module, ty)?;

        let original_datatype = self.modules[module].type_of_value(target);
        let original_size = self.types[original_datatype].size;
        let datatype_size = self.types[ty].size;

        if original_size != datatype_size {
            return Err(FError::new(
                error::Kind::InvalidBitCast(original_size, datatype_size),
                token,
            ));
        }

        Ok(Some(self.modules[module].cast(target, ty, token, body)))
    }

    fn field_access(
        &mut self,
        fun: Fun,
        mut header: Value,
        field: ID,
        token: Token,
        body: &mut FunBody,
    ) -> Result<Value> {
        let in_assign = self.context.in_assign;
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let ty = module_ent.type_of_value(header);
        let mut mutable = module_ent.is_mutable(header) || self.t_state.pointer_mutability(ty);
        let mut path = self.context.pool.get();
        let success = self.find_field(ty, field, &mut path);
        if !success {
            return Err(FError::new(error::Kind::UnknownField(ty), token));
        };

        let mut offset = Size::ZERO;
        let mut current_type = ty;
        for &i in path.iter().rev() {
            let ty = &self.types[current_type];
            match &ty.kind {
                TKind::Structure(stype) => {
                    let s_field = &stype.fields[i];
                    if !self.state.can_access(module, ty.module, s_field.vis) {
                        return Err(FError::new(error::Kind::FieldVisibilityViolation, token));
                    }
                    offset = offset.add(s_field.offset);
                    current_type = s_field.ty;
                }
                &TKind::Pointer(pointed, p_mutable) => {
                    mutable &= p_mutable;
                    let value =
                        self.modules[module].offset_value(header, pointed, offset, token, body);
                    let ty = &self.types[pointed];
                    match &ty.kind {
                        TKind::Structure(stype) => {
                            let s_field = &stype.fields[i];
                            if !self.state.can_access(module, ty.module, s_field.vis) {
                                return Err(FError::new(error::Kind::FieldVisibilityViolation, token));
                            }
                            offset = s_field.offset;
                            current_type = s_field.ty;
                            let module_ent = &mut self.modules[module];
                            let loaded = module_ent.add_value_ent(ValueEnt {
                                ty: current_type,
                                mutable,
                                offset,

                                ..Default::default()
                            });
                            module_ent.add_inst(
                                IKind::Deref(value, in_assign),
                                loaded,
                                token,
                                body,
                            );
                            header = loaded;
                        }
                        _ => unreachable!(),
                    }
                }
                _ => todo!("{}", TypeDisplay::new(self.state, current_type)),
            }
        }

        Ok(self.modules[module].offset_value(header, current_type, offset, token, body))
    }

    fn assignment(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &mut self.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let target = module_ent.get(sons, 1);
        let value = module_ent.get(sons, 2);

        let prev_in_var_ref = self.context.in_var_ref;
        let prev_in_assign = self.context.in_assign;
        self.context.in_assign = true;
        self.context.in_var_ref = true;
        let target = self.expr(fun, target, body)?;
        self.context.in_assign = prev_in_assign;
        self.context.in_var_ref = prev_in_var_ref;

        let value = self.expr(fun, value, body)?;

        let module_ent = &mut self.modules[module];
        let target_datatype = module_ent.type_of_value(target);
        let value_datatype = module_ent.type_of_value(value);
        let mutable = module_ent.is_mutable(target);
        if !mutable {
            return Err(FError::new(error::Kind::AssignToImmutable, token));
        }

        assert_type(value_datatype, target_datatype, &token)?;
        module_ent.assign(target, value, token, body);
        Ok(Some(value))
    }

    fn create(&mut self, fun: Fun, explicit_params: &[Ty], values: &[Ty]) -> Result<Option<Fun>> {
        let mut arg_buffer = self.context.pool.get();
        let mut stack = self.context.pool.get();
        let mut params = self.context.pool.get();
        let mut g_params = self.context.pool.get();

        let g_ent = self.generic_funs.get_mut(fun).unwrap();
        g_params.extend_from_slice(&g_ent.sig.params);
        let g_ent_len = g_ent.sig.elements.len();
        let call_conv = g_ent.call_conv;
        let elements = std::mem::take(&mut g_ent.sig.elements);

        params.resize(g_ent.sig.params.len(), None);
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

        self.generic_funs.get_mut(fun).unwrap().sig.elements = elements;

        if !ok {
            return Ok(None);
        }

        let FunEnt {
            module,
            untraced,
            vis,
            scope,
            inline,
            attrs,
            hint,
            name,
            linkage,
            ast,
            ..
        } = self.funs[fun];
        let mut id = FUN_SALT.add(name.hash);
        let fun_module_id = self.state.modules[module].id;

        let mut shadowed = self.context.pool.get();
        let mut final_params = EntityList::new();
        for i in 0..params.len() {
            if let Some(ty) = params[i] {
                id = id.add(self.types[ty].id);
                let id = TYPE_SALT.add(g_params[i]).add(fun_module_id);
                shadowed.push((id, self.state.types.link(id, ty)));
                self.modules[module].push_type(&mut final_params, ty);
            } else {
                return Ok(None);
            }
        }
        id = id.add(self.state.modules[module].id);

        if let Some(fun) = self.state.find_computed(self.module, id) {
            self.modules[module].clear_types(&mut final_params);
            return Ok(Some(fun));
        }

        if !scope.is_reserved_value() {
            let ty = self.modules[module].son(scope, 1);
            let ty = self.parse_type(module, ty)?;
            let id = TYPE_SALT.add(ID::new("Self")).add(fun_module_id);
            shadowed.push((id, self.state.types.link(id, ty)));
        }

        let header = self.modules[module].son(ast, 0);
        let mut sig = self.parse_signature(module, header)?;
        sig.call_conv = call_conv;

        for (id, ty) in shadowed.drain(..) {
            self.state.types.remove_link(id, ty);
        }

        let new_fun_ent = FunEnt {
            vis,
            id,
            module,
            hint,
            name,
            attrs,
            scope,
            untraced,
            inline,
            linkage,
            sig,
            ast,

            base_fun: PackedOption::from(fun),
            params: final_params,
            kind: FKind::Normal,
            alias: None,
            body: FunBody::default(),
        };

        let (shadowed, id) = self.state.add_fun(self.module, new_fun_ent);
        debug_assert!(shadowed.is_none());

        self.context.unresolved.push(id);

        Ok(Some(id))
    }

    fn collect(&mut self, module: Mod) -> Result {
        let module_ent = &self.modules[module];
        let funs_len = module_ent.funs().len();
        let globals_len = module_ent.globals().len();
        let mut scope_state = (
            Ast::reserved_value(),
            Ast::reserved_value(),
            ID(0),
            None,
            Vis::None,
        );

        for i in (0..funs_len).step_by(3) {
            let funs = self.modules[module].funs();
            let (ast, attrs, scope) = (funs[i], funs[i + 1], funs[i + 2]);
            self.parse_scope(module, scope, &mut scope_state)?;
            self.collect_fun(
                module,
                ast,
                attrs,
                scope,
                scope_state.2,
                scope_state.1,
                scope_state.4,
            )?
        }

        let main_fun_id = self.context.entry_point_data.id;

        let mut body = self.funs[main_fun_id].body;

        for i in (0..globals_len).step_by(3) {
            let globals = self.modules[module].globals();
            let (ast, attrs, scope) = (globals[i], globals[i + 1], globals[i + 2]);
            self.parse_scope(module, scope, &mut scope_state)?;
            self.collect_global_var(module, ast, attrs, scope_state.2, &mut body, scope_state.4)?
        }

        if let Some((id, ty)) = scope_state.3 {
            self.state.types.remove_link(id, ty);
        }

        for i in 0..self.context.entry_points.len() {
            let entry_point = self.context.entry_points[i];
            self.add_entry(entry_point, &mut body)?;
        }

        self.funs[main_fun_id].body = body;

        Ok(())
    }

    fn parse_scope(
        &mut self,
        module: Mod,
        ast: Ast,
        (previous, generics, id, shadow, vis): &mut (Ast, Ast, ID, Option<(ID, Option<Ty>)>, Vis),
    ) -> Result {
        if ast == *previous {
            return Ok(());
        }
        *previous = ast;
        *generics = Ast::reserved_value();
        *id = ID(0);
        if let Some((id, ty)) = *shadow {
            self.state.types.remove_link(id, ty);
            *shadow = None;
        }
        if ast.is_reserved_value() {
            return Ok(());
        }

        let module_ent = &self.modules[module];
        let &AstEnt { sons, kind, .. } = module_ent.load(ast);
        let generic_ast = module_ent.get(sons, 0);
        let ty = module_ent.get(sons, 1);
        let ty_kind = module_ent.kind(ty);
        let module_id = module_ent.id;

        *vis = match kind {
            AKind::Impl(vis) => vis,
            _ => unreachable!(),
        };

        *generics = generic_ast;

        let ty = match ty_kind {
            AKind::Ident | AKind::Instantiation if generic_ast.is_reserved_value() => {
                self.parse_type(module, ty)?
            }

            AKind::Instantiation => {
                let base = module_ent.son(ty, 0);
                self.parse_type(module, base)?
            }
            AKind::Array => self.builtin_repo.array,
            kind => unreachable!("{:?}", kind),
        };

        *id = self.types[self.t_state.base_of(ty)].id;
        let id = TYPE_SALT.add(ID::new("Self")).add(module_id);
        *shadow = Some((id, self.types.link(id, ty)));

        Ok(())
    }

    fn collect_global_var(
        &mut self,
        module: Mod,
        ast: Ast,
        attrs: Ast,
        scope: ID,
        body: &mut FunBody,
        vis: Vis,
    ) -> Result {
        let fun = self.context.entry_point_data.id;
        let module_ent = &self.modules[module];
        let module_id = module_ent.id;
        let &AstEnt { kind, sons, .. } = module_ent.load(ast);
        let ast_len = module_ent.len(sons);
        let (vis, mutable) = match kind {
            AKind::VarStatement(a_vis, mutable) => (vis.join(a_vis), mutable),
            _ => unreachable!(),
        };

        let (linkage, alias) = self.resolve_linkage(module, attrs)?;

        for i in 0..ast_len {
            let module_ent = &self.modules[module];
            let var_line = module_ent.get(sons, i);
            let ident_group = module_ent.son(var_line, 0);
            let ident_group_len = module_ent.ast_len(ident_group);
            let ty = module_ent.son(var_line, 1);
            let value_group = module_ent.son(var_line, 2);
            let ty = if ty.is_reserved_value() {
                None
            } else {
                Some(self.parse_type(module, ty)?)
            };

            for i in 0..ident_group_len {
                let hint = self.modules[module].son_ent(ident_group, i).token;
                let id = GLOBAL_SALT.add(hint.span.hash).add(scope).add(module_id);

                let (shadowed, global) = self.state.globals.insert(id, GlobalEnt::default());
                if let Some(shadowed) = shadowed {
                    return Err(FError::new(
                        error::Kind::RedefinedGlobal(shadowed.hint.clone()),
                        hint,
                    ));
                }

                let ty = if !value_group.is_reserved_value() {
                    let value = self.modules[module].son(value_group, i);
                    let value = self.expr(fun, value, body)?;
                    self.modules[module].assign_global(global, value, body)
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
                    hint,
                    attrs,
                    linkage,
                    alias,
                };

                self.state.globals[global] = g_ent;

                self.modules[module].add_global(global);

                self.context.resolved_globals.push(global);
            }
        }

        Ok(())
    }

    fn collect_fun(
        &mut self,
        module: Mod,
        ast: Ast,
        attrs: Ast,
        scope: Ast,
        scope_id: ID,
        generics: Ast,
        vis: Vis,
    ) -> Result {
        let module_ent = &self.modules[module];
        let module_id = module_ent.id;
        let &AstEnt { kind, sons, .. } = module_ent.load(ast);
        let vis = match kind {
            AKind::Fun(a_vis) => vis.join(a_vis),
            _ => unreachable!(),
        };
        let header = module_ent.get(sons, 0);
        let header_ent = *module_ent.load(header);
        let header_len = module_ent.len(header_ent.sons);

        let salt = match header_ent.kind {
            AKind::FunHeader(op_kind) => match op_kind {
                OpKind::Normal => FUN_SALT,
                OpKind::Binary => BINARY_SALT,
                OpKind::Unary => UNARY_SALT,
            },
            _ => unreachable!(),
        };

        let maybe_call_conv = module_ent.get(header_ent.sons, header_len - 1);
        let call_conv = if let Some(attr) =
            module_ent.attr(attrs, ID::new("call_conv")).or_else(|| {
                if maybe_call_conv.is_reserved_value() {
                    None
                } else {
                    Some(maybe_call_conv)
                }
            }) {
            let final_attr = module_ent
                .a_state
                .son_optional(attr, 1)
                .unwrap_or(module_ent.son(attr, 0));
            let token = *module_ent.token(final_attr);
            let str = self.state.display(&token.span);
            CallConv::from_str(str).ok_or_else(|| FError::new(error::Kind::InvalidCallConv, token))?
        } else {
            CallConv::Fast
        };

        let entry = module_ent.attr(attrs, ID::new("entry")).is_some();

        let (linkage, mut alias) = self.resolve_linkage(module, attrs)?;

        let hint = header_ent.token;
        let name_ent = *self.modules[module].get_ent(header_ent.sons, 0);
        let (name, mut id, sig, kind, unresolved) =
            if name_ent.kind == AKind::Ident && generics.is_reserved_value() {
                let mut sig = self.parse_signature(module, header)?;
                sig.call_conv = call_conv;

                let name = name_ent.token.span;
                let fun_id = salt.add(name.hash).add(scope_id);

                if linkage == Linkage::Import && alias.is_none() {
                    alias = Some(name);
                }

                (name, fun_id, Ok(sig), FKind::Normal, true)
            } else if name_ent.kind == AKind::Instantiation || !generics.is_reserved_value() {
                let mut args = self.context.pool.get();
                let mut params = self.context.pool.get();
                let module_ent = &self.modules[module];
                let name = if name_ent.kind == AKind::Instantiation {
                    *module_ent.get_ent(name_ent.sons, 0)
                } else {
                    name_ent
                };

                if name.kind != AKind::Ident {
                    return Err(FError::new(error::Kind::InvalidFunctionHeader, name.token));
                }

                if name_ent.kind == AKind::Instantiation {
                    params.extend(
                        module_ent.slice(name_ent.sons)[1..]
                            .iter()
                            .map(|&ast| module_ent.token(ast).span.hash),
                    );
                }

                if !generics.is_reserved_value() {
                    let sons = module_ent.sons(generics);
                    params.extend(
                        module_ent
                            .slice(sons)
                            .iter()
                            .map(|&ast| module_ent.token(ast).span.hash),
                    );
                }

                let mut arg_count = 0;
                for i in 1..header_len - 2 {
                    let module_ent = &self.modules[module];
                    let arg_section = module_ent.get(header_ent.sons, i);
                    let amount = module_ent.ast_len(arg_section) - 1;
                    let ty = module_ent.son(arg_section, amount);
                    let idx = args.len();
                    args.push(GenericElement::NextArgument(amount, 0));
                    self.load_arg(module, scope, ty, &params, &mut args)?;
                    let additional = args.len() - idx - 1;
                    args[idx] = GenericElement::NextArgument(amount, additional);
                    arg_count += amount;
                }

                let id = salt.add(name.token.span.hash).add(scope_id);

                let sig = GenericSignature {
                    params: params.clone(),
                    elements: args.clone(),
                    arg_count,
                };

                let nm = name.token.span;

                (nm, id, Err(sig), FKind::Generic, false)
            } else {
                return Err(FError::new(error::Kind::InvalidFunctionHeader, name_ent.token));
            };

        id = id.add(module_id);

        let module_ent = &self.modules[module];
        let fun_ent = FunEnt {
            vis,
            id,
            module,
            hint,
            kind,
            name,
            untraced: module_ent.attr(attrs, ID::new("untraced")).is_some(),
            inline: module_ent.attr(attrs, ID::new("inline")).is_some(),
            attrs,
            scope,
            linkage,
            alias,
            sig: sig.as_ref().map(|&s| s).unwrap_or_default(),
            ast,

            ..Default::default()
        };
        let (shadowed, id) = self.add_fun(module, fun_ent);
        if let Some(shadowed) = shadowed {
            return Err(FError::new(
                error::Kind::Redefinition(shadowed.hint.clone()),
                hint,
            ));
        }

        if let Err(sig) = sig {
            self.generic_funs.insert(GFun { id, sig, call_conv });
        }

        if unresolved {
            if entry {
                self.context.entry_points.push(id);
            }
            self.context.unresolved.push(id);
        }

        Ok(())
    }

    fn add_entry(&mut self, id: Fun, body: &mut FunBody) -> Result {
        let MainFunData {
            arg1,
            arg2,
            return_value,
            ..
        } = self.context.entry_point_data;
        let FunEnt {
            module, sig, hint, ..
        } = self.funs[id];
        let module_ent = &mut self.modules[module];

        let value = if sig.ret.is_none() {
            None
        } else {
            Some(module_ent.add_temp_value(sig.ret.unwrap()))
        };

        let args = match module_ent.type_slice(sig.args) {
            &[] => EntityList::new(),
            &[count, args] => {
                let int = self.state.builtin_repo.int;
                let temp_ptr = self.pointer_of(int, false);
                if count != int || args != self.pointer_of(temp_ptr, false) {
                    return Err(FError::new(error::Kind::InvalidEntrySignature, hint));
                }
                self.modules[module].add_values(&[arg1, arg2])
            }
            _ => {
                return Err(FError::new(error::Kind::InvalidEntrySignature, hint));
            }
        };

        let module_ent = &mut self.modules[module];
        if let Some(value) = value {
            module_ent.add_inst(IKind::Call(id, args), value, hint, body);
            module_ent.add_inst(IKind::Assign(return_value), value, hint, body);
        } else {
            module_ent.add_valueless_inst(IKind::Call(id, args), hint, body);
        }

        Ok(())
    }

    fn parse_signature(&mut self, module: Mod, header: Ast) -> Result<Signature> {
        let mut args = EntityList::new();
        let module_ent = &self.modules[module];
        let header_len = module_ent.ast_len(header);

        for i in 1..header_len - 2 {
            let module_ent = &self.modules[module];
            let arg_section = module_ent.son_ent(header, i).sons;
            let len = module_ent.len(arg_section);
            let last = module_ent.get(arg_section, len - 1);
            let ty = self.parse_type(module, last)?;
            for _ in 0..len - 1 {
                self.modules[module].push_type(&mut args, ty)
            }
        }

        let raw_ret_ty = self.modules[module].son(header, header_len - 2);
        let ret = if raw_ret_ty.is_reserved_value() {
            PackedOption::default()
        } else {
            PackedOption::from(self.parse_type(module, raw_ret_ty)?)
        };

        Ok(Signature {
            call_conv: CallConv::Fast,
            args,
            ret,
        })
    }

    fn load_arg(
        &mut self,
        module: Mod,
        scope: Ast,
        ast: Ast,
        params: &[ID],
        buffer: &mut Vec<GenericElement>,
    ) -> Result {
        let mut stack = self.context.pool.get();
        stack.push((ast, false));

        while let Some(&(ast, done)) = stack.last() {
            let module_ent = &self.modules[module];
            let &AstEnt { kind, sons, token } = module_ent.load(ast);
            if done {
                if kind == AKind::Instantiation {
                    buffer.push(GenericElement::ScopeEnd);
                }
                stack.pop();
                continue;
            }
            stack.last_mut().unwrap().1 = true;
            match kind {
                AKind::Ident => {
                    if token.span.hash == ID::new("Self") && !scope.is_reserved_value() {
                        let ty = module_ent.son(scope, 1);
                        stack.push((ty, false));
                    } else {
                        let id = token.span.hash;
                        if let Some(index) = params.iter().position(|&p| p == id) {
                            buffer.push(GenericElement::Parameter(index));
                        } else {
                            let ty = self.parse_type(module, ast)?;
                            buffer.push(GenericElement::Element(ty, None));
                        }
                    }
                }
                AKind::Instantiation => {
                    let sons = module_ent.sons(ast);
                    let header = module_ent.get(sons, 0);
                    let ty = self.parse_type(module, header)?;
                    buffer.push(GenericElement::Element(ty, None));
                    buffer.push(GenericElement::ScopeStart);
                    stack.extend(
                        self.modules[module].slice(sons)[1..]
                            .iter()
                            .map(|&a| (a, false)),
                    );
                }
                AKind::Ref(mutable) => {
                    let pointed = module_ent.get(sons, 0);
                    buffer.push(GenericElement::Pointer(mutable));
                    stack.push((pointed, false));
                }
                AKind::Array => {
                    let element = module_ent.get(sons, 0);
                    let len = module_ent.get(sons, 1);
                    buffer.push(GenericElement::Array(None));
                    stack.push((element, false));
                    stack.push((len, false));
                }
                AKind::Lit => {
                    let ty = self.parse_type(module, ast)?;
                    buffer.push(GenericElement::Element(ty, None));
                }
                _ => todo!(
                    "{}",
                    AstDisplay::new(self.state, &self.modules[module].a_state, ast)
                ),
            }
        }

        Ok(())
    }

    fn load_arg_from_datatype(
        &mut self,
        ty: Ty,
        arg_buffer: &mut Vec<GenericElement>,
        stack: &mut Vec<(Ty, bool)>,
    ) {
        debug_assert!(stack.is_empty());
        stack.push((ty, false));

        while let Some((ty, done)) = stack.last_mut() {
            let ty = *ty;
            let TypeEnt {
                params,
                kind,
                module,
                ..
            } = &self.types[ty];

            if *done {
                if !params.is_empty() {
                    arg_buffer.push(GenericElement::ScopeEnd);
                }
                stack.pop();
                continue;
            }

            *done = true;

            if params.is_empty() {
                match kind {
                    &TKind::Pointer(pointed, mutable) => {
                        arg_buffer.push(GenericElement::Pointer(mutable));
                        stack.push((pointed, false));
                    }
                    &TKind::Array(element, size) => {
                        arg_buffer.push(GenericElement::Array(Some(ty)));
                        stack.push((element, false));
                        let size = self
                            .state
                            .constant_of(self.module, TypeConst::Int(size as i64));
                        stack.push((size, false));
                    }
                    _ => {
                        arg_buffer.push(GenericElement::Element(ty, Some(ty)));
                    }
                }
                continue;
            }

            let module_ent = &self.modules[*module];
            let slice = module_ent.type_slice(*params);
            arg_buffer.push(GenericElement::Element(slice[0], Some(ty)));

            arg_buffer.push(GenericElement::ScopeStart);
            stack.extend(slice[1..].iter().map(|&p| (p, false)));
        }
    }

    fn pointer_base(&mut self, ty: Ty, token: Token) -> Result<Ty> {
        self.t_state
            .pointer_base(ty)
            .ok_or_else(|| FError::new(error::Kind::NonPointerDereference, token))
    }

    fn parse_type(&mut self, module: Mod, ast: Ast) -> Result<Ty> {
        TParser::new(self.state, self.context)
            .parse_type(module, ast)
            .map_err(|err| FError::new(error::Kind::TypeError(err), Token::default()))
    }

    fn resolve_linkage(&self, module: Mod, attrs: Ast) -> Result<(Linkage, Option<Span>)> {
        let module_ent = &self.modules[module];
        if let Some(attr) = module_ent.attr(attrs, ID::new("linkage")) {
            let len = module_ent.ast_len(attr);
            if len < 2 {
                return Err(FError::new(
                    error::Kind::TooShortAttribute(len - 1, 1),
                    *module_ent.token(attr),
                ));
            }
            let linkage = module_ent.son_ent(attr, 1).token.span;
            let linkage = match self.state.display(&linkage) {
                "import" => Linkage::Import,
                "export" => Linkage::Export,
                "hidden" => Linkage::Hidden,
                "preemptible" => Linkage::Preemptible,
                "local" => Linkage::Local,
                _ => return Err(FError::new(error::Kind::InvalidLinkage, *module_ent.token(attr))),
            };

            Ok((
                linkage,
                module_ent
                    .son_optional(attr, 2)
                    .map(|s| module_ent.token(s).span),
            ))
        } else {
            Ok((Linkage::Export, None))
        }
    }

    fn pointer_of(&mut self, ty: Ty, mutable: bool) -> Ty {
        self.state.pointer_of(self.module, ty, mutable)
    }*/

    fn find_computed(&mut self, source_module: Mod, id: ID) -> Option<Fun> {
        if let Some(&fun) = self.funs.index(id) {
            self.modules[source_module].add_fun(fun);
            return Some(fun);
        }

        None
    }

    fn add_fun(&mut self, module: Mod, fun_ent: FunEnt) -> (Option<FunEnt>, Fun) {
        let id = fun_ent.id;
        let (shadow, fun) = self.funs.insert(id, fun_ent);
        self.modules[module].add_fun(fun);
        (shadow, fun)
    }

    fn push_scope(&mut self) {
        self.frames.push(self.vars.len());
    }

    fn pop_scope(&mut self) {
        let idx = self.frames.pop().unwrap();
        self.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Local> {
        self.vars.iter().rev().find(|v| v.0 == id).map(|v| v.1)
    }

    fn find_loop(&self, token: &Token) -> std::result::Result<Loop, bool> {
        if token.span.len() == 0 {
            return self.loops.last().cloned().ok_or(true);
        }

        let name = token.span.hash;

        self.loops
            .iter()
            .rev()
            .find(|l| l.name == name)
            .cloned()
            .ok_or_else(|| self.loops.is_empty())
    }

    fn add_builtin_functions(&mut self) {
        for &i in ALL_BUILTIN_TYPES {
            for &j in ALL_BUILTIN_TYPES {
                let name = self.type_name(i);
                self.create_builtin_fun(
                    Some(j),
                    name,
                    &[j],
                    Some(i),
                );
            }
        }

        let integer_types = &[
            I8_TY,
            I16_TY,
            I32_TY,
            I64_TY,
            U8_TY,
            U16_TY,
            U32_TY,
            U64_TY,
            INT_TY,
            UINT_TY
        ][..];

        let builtin_unary_ops = [
            ("~ + ++ --", integer_types),
            (
                "- abs",
                &[
                    I8_TY,
                    I16_TY,
                    I32_TY,
                    I64_TY,
                    F32_TY,
                    F64_TY,
                    INT_TY,
                ][..],
            ),
            ("!", &[BOOL_TY][..]),
        ];

        for &(operators, types) in builtin_unary_ops.iter() {
            for op in operators.split(' ') {
                let op = self.builtin_span(op);
                for &datatype in types.iter() {
                    self.create_builtin_fun(
                        Some(datatype),
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
                &[F32_TY, F64_TY][..],
            ),
            ("&& || ^ | &", &[BOOL_TY][..]),
        ];

        for &(operators, types) in builtin_bin_ops.iter() {
            for op in operators.split(' ') {
                let op_span = self.builtin_span(op);
                for &ty in types.iter() {
                    let return_type = if matches!(op, "==" | "!=" | ">" | "<" | ">=" | "<=") {
                        BOOL_TY
                    } else {
                        ty
                    };
                    self.create_builtin_fun(
                        Some(ty),
                        op_span,
                        &[ty, ty],
                        Some(return_type),
                    );
                }
            }
        }
    }

    fn create_builtin_fun(
        &mut self,
        caller: Option<Ty>,
        name: Span,
        args: &[Ty],
        ret: Option<Ty>,
    ) {
        /*let id = salt.add(name.hash).add(self.types[args[0]].id);
        let module_ent = &mut self.modules[module];
        let id = id.add(module_ent.id);
        let args = module_ent.add_type_slice(args);
        let sig = Signature {
            call_conv: CallConv::Fast,
            args,
            ret,
        };

        let fun_ent = FunEnt {
            id,
            name,
            vis: Vis::Public,
            module,
            kind: FKind::Builtin,
            sig,

            ..Default::default()
        };

        assert!(self.add_fun(module, fun_ent).0.is_none());
        */
    }
}

impl Deref for Ctx {
    type Target = types::Ctx;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for Ctx {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

crate::impl_entity!(
    Command, Section
);

fn assert_type(actual: Ty, expected: Ty, token: &Token) -> Result {
    if actual == expected {
        Ok(())
    } else {
        Err(Error::new(error::Kind::TypeMismatch(actual, expected), *token))
    }
}

#[derive(Debug, Clone, Default, Copy, RealQuickSer)]
pub struct ValueEnt {
    pub ty: Ty,
    pub inst: PackedOption<Command>,
    pub offset: Size,
    pub mutable: bool,
    pub on_stack: bool,
}

impl ValueEnt {
    pub fn temp(ty: Ty) -> Self {
        Self {
            ty,
            ..Default::default()
        }
    }
}

#[derive(Debug, Default, Clone, Copy, RealQuickSer)]
pub struct CommandEnt {
    pub kind: IKind,
    pub value: PackedOption<Value>,
    pub prev: PackedOption<Command>,
    pub next: PackedOption<Command>,
    pub block: PackedOption<Section>,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub enum IKind {
    NoOp,
    FunPointer(Fun),
    FunPointerCall(Local, EntityList<Local>),
    GlobalLoad(GlobalValue),
    Call(Fun, EntityList<Local>),
    VarDecl(Local),
    Zeroed,
    Uninitialized,
    Lit(token::Kind),
    Return(PackedOption<Local>),
    Assign(Local),
    Jump(Section, EntityList<Local>),
    JumpIfTrue(Local, Section, EntityList<Local>),
    Offset(Local),
    Deref(Local, bool),
    Ref(Local),
    Cast(Local),
}

impl IKind {
    pub fn is_closing(&self) -> bool {
        matches!(self, IKind::Jump(..) | IKind::Return(..))
    }
}

impl Default for IKind {
    fn default() -> Self {
        IKind::NoOp
    }
}

#[derive(Debug, Clone, Copy, Default, RealQuickSer)]
pub struct BlockEnt {
    pub prev: PackedOption<Section>,
    pub next: PackedOption<Section>,

    pub args: EntityList<Local>,

    pub start: PackedOption<Command>,
    pub end: PackedOption<Command>,
}

impl ErrorDisplayState<Error> for Ctx {
    fn fmt(&self, e: &Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match e.kind() {
            &error::Kind::DuplicateEntrypoint(other) => {
                let other = self.state.funs[other].hint.clone();
                writeln!(
                    f,
                    "entrypoint already defined here:\n{}",
                    TokenDisplay::new(self.state, &other)
                )?;
            },
            error::Kind::TooShortAttribute(actual, expected) => {
                writeln!(
                    f,
                    "too short attribute, expected {} but got {}",
                    expected, actual
                )?;
            },
            error::Kind::InvalidCallConv => {
                crate::types::call_conv_error(f)?;
            },
            error::Kind::InvalidLinkage => {
                writeln!(f, "Invalid linkage, valid linkages are:")?;
                for cc in ["import", "local", "export", "preemptible", "hidden"] {
                    writeln!(f, "  {}", cc)?;
                }
            },
            error::Kind::TypeError(error) => {
                writeln!(f, "{}", TErrorDisplay::new(self.state, &error))?;
            },
            error::Kind::Redefinition(other) => {
                writeln!(f, "redefinition of\n{}", TokenDisplay::new(self.state, &other))?;
            },
            error::Kind::InvalidBitCast(actual, expected) => {
                writeln!(
                    f,
                    "invalid bit-cast, expected type of size {:?} but got {:?}",
                    expected, actual
                )?;
            },
            error::Kind::AssignToImmutable => {
                writeln!(f, "cannot assign to immutable value")?;
            },
            error::Kind::ExpectedValue => {
                writeln!(f, "expected this expression to have a value")?;
            },
            &error::Kind::TypeMismatch(actual, expected) => {
                writeln!(
                    f,
                    "type mismatch, expected '{}' but got '{}'",
                    TypeDisplay::new(&self.state, expected),
                    TypeDisplay::new(&self.state, actual)
                )?;
            },
            error::Kind::FunctionNotFound(name, arguments) => {
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
            error::Kind::GenericMismatch(name, arguments) => {
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
            error::Kind::UnexpectedValue => {
                writeln!(
                    f,
                    "value not expected here, consider adding 'pass' after expression"
                )?;
            },
            error::Kind::UnexpectedReturnValue => {
                writeln!(f, "return value not expected, if you want to return something, add '-> <type>' after '()' in signature")?;
            },
            error::Kind::UnexpectedAuto => {
                writeln!(f, "'auto' not allowed here")?;
            },
            error::Kind::UndefinedVariable => {
                writeln!(f, "cannot find variable in current scope")?;
            },
            error::Kind::UnresolvedType => {
                writeln!(
                    f,
                    "type of this expression cannot be inferred, consider annotating the type"
                )?;
            },
            &error::Kind::UnknownField(ty) => {
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
            error::Kind::MutableToImmutable => {
                writeln!(f, "cannot take mutable reference of immutable value")?;
            },
            error::Kind::MissingElseBranch => {
                writeln!(f, "expected 'else' branch since 'if' branch returns value, consider adding 'pass' after last expression if this is intended")?;
            },
            error::Kind::ContinueOutsideLoop => {
                writeln!(f, "cannot use 'continue' outside of loop")?;
            },
            error::Kind::BreakOutsideLoop => {
                writeln!(f, "cannot use 'break' outside of loop")?;
            },
            error::Kind::WrongLabel => {
                writeln!(f, "parent loop with this label does not exist")?;
            },
            error::Kind::NonPointerDereference => {
                writeln!(f, "cannot dereference non-pointer type")?;
            },
            error::Kind::InvalidFunctionHeader => {
                writeln!(f, "invalid function header, syntax for header is:\n  ident | op [ '[' ident {{ ',' ident }} ']' ]")?;
            },
            &error::Kind::AmbiguousFunction(a, b) => {
                let a = self.state.funs[a].hint.clone();
                let b = self.state.funs[b].hint.clone();
                writeln!(
                    f,
                    "ambiguous function call, matches\n{}\nand\n{}",
                    TokenDisplay::new(self.state, &a),
                    TokenDisplay::new(self.state, &b)
                )?;
            },
            error::Kind::EmptyArray => {
                writeln!(
                    f,
                    "cannot create empty array from '[]' syntax as type of element is unknown"
                )?;
            },
            error::Kind::RedefinedGlobal(other) => {
                writeln!(
                    f,
                    "redefinition of global variable\n{}\n",
                    TokenDisplay::new(self.state, &other)
                )?;
            },
            &error::Kind::AmbiguousGlobal(a, b) => {
                let a = self.state.globals[a].hint.clone();
                let b = self.state.globals[b].hint.clone();
                writeln!(
                    f,
                    "ambiguous global variable, matches\n{}\nand\n{}",
                    TokenDisplay::new(self.state, &a),
                    TokenDisplay::new(self.state, &b)
                )?;
            },
            error::Kind::InvalidEntrySignature => {
                writeln!(f, "invalid entry point signature, expected 'fun (int, & &u8)' or 'fun ()'")?;
            },
            error::Kind::RecursiveInline => {
                writeln!(f, "cannot inline recursive function")?;
            },
            error::Kind::VarInsideGenericScope(scope) => {
                writeln!(
                    f,
                    "cannot declare global inside generic scope\n{}",
                    TokenDisplay::new(self.state, scope)
                )?;
            },
            error::Kind::UnknownModule => {
                writeln!(f, "unknown module")?;
            },
            error::Kind::InvalidDotCall => {
                writeln!(f, "call cannot have explicit caller type and be a dot call")?;
            },
            error::Kind::VisibilityViolation => {
                writeln!(f, "function visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
            },
            error::Kind::FieldVisibilityViolation => {
                writeln!(f, "field visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
            },
            error::Kind::GlobalVisibilityViolation => {
                writeln!(f, "global variable visibility disallows access, {}", crate::types::VISIBILITY_MESSAGE)?;
            },
            error::Kind::FunArgMismatch(fun, arguments) => {
                let sig = &self.state.funs[*fun].sig;
                let module = self.state.funs[*fun].module;
                writeln!(
                    f,
                    "function argument types are '({})' but you provided '({})'",
                    self.state.modules[module]
                        .type_slice(sig.args)
                        .iter()
                        .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                        .collect::<Vec<_>>().join(", "),
                    arguments
                        .iter()
                        .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                        .collect::<Vec<_>>().join(", ")
                )?;
            },
            error::Kind::FunPointerArgMismatch(ty, arguments) => {
                let module = self.state.types[*ty].module;
                writeln!(
                    f,
                    "function pointer argument types are '({})' but you provided '({})'",
                    &self.state.modules[module].type_slice(
                            self.state.types[*ty].kind
                                .fun_pointer()
                                .args
                        )
                        .iter()
                        .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                        .collect::<Vec<_>>().join(", "),
                    arguments
                        .iter()
                        .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            },
            error::Kind::ExpectedFunctionPointer => {
                writeln!(f, "only dereferenced function pointer can be called")?;
            },
        }

        Ok(())
    }

    fn sources(&self) -> &lexer::Ctx {
        self.ctx.sources()
    }
}

#[derive(Debug)]
pub struct Error {
    kind: error::Kind,
    token: Token,
}

impl Error {
    pub fn new(kind: error::Kind, token: Token) -> Self {
        Error { kind, token }
    }

    pub fn kind(&self) -> &error::Kind {
        &self.kind
    }
}

impl DisplayError for Error {
    fn token(&self) -> Token {
        self.token
    }
}

mod error {
    use super::*;
    
    #[derive(Debug)]
    pub enum Kind {
        MutableToImmutable,
        FunPointerArgMismatch(Ty, Vec<Ty>),
        ExpectedFunctionPointer,
        FunArgMismatch(Fun, Vec<Ty>),
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
        TypeError(types::Error),
        Redefinition(Token),
        InvalidBitCast(Size, Size),
        AssignToImmutable,
        ExpectedValue,
        TypeMismatch(Ty, Ty),
        FunctionNotFound(Span, Vec<Ty>),
        GenericMismatch(Span, Vec<Ty>),
        UnexpectedValue,
        UnexpectedReturnValue,
        UnexpectedAuto,
        UndefinedVariable,
        UnresolvedType,
        UnknownField(Ty),
        MissingElseBranch,
        ContinueOutsideLoop,
        BreakOutsideLoop,
        WrongLabel,
        NonPointerDereference,
        InvalidFunctionHeader,
        AmbiguousFunction(Fun, Fun),
        AmbiguousGlobal(Global, Global),
    }
}



pub enum DotInstr {
    None,
    Deref,
    Ref,
}

#[derive(Debug, Clone, QuickDefault, Copy, RealQuickSer)]
pub struct FunEnt {
    id: ID,
    module: Mod,
    hint: Token,
    params: EntityList<Ty>, // must drop
    base_fun: PackedOption<Fun>,
    sig: Signature, // must drop
    body: FunBody,
    kind: FKind,
    name: Span,
    ast: Ast,
    attrs: Ast,
    scope: Ast,
    alias: Option<Span>,
    vis: Vis,
    linkage: Linkage,
    untraced: bool,
    inline: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum FKind {
    Builtin,
    Generic,
    Normal,
    Represented,
    Compiled,
    JitCompiled,
    CompiledAndJitCompiled
}

impl FKind {
    pub fn add(&mut self, other: Self) {
        match (*self, other) {
            (Self::Compiled, Self::JitCompiled) | 
            (Self::JitCompiled, Self::Compiled) => *self = Self::CompiledAndJitCompiled,
            _ =>  *self = other,
        }
    }

    pub fn is_compiled(&self) -> bool {
        match self {
            Self::Compiled | Self::CompiledAndJitCompiled => true,
            _ => false,
        }
    }

    pub fn is_jit_compiled(&self) -> bool {
        match self {
            Self::JitCompiled | Self::CompiledAndJitCompiled => true,
            _ => false,
        }
    }
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Builtin
    }
}

#[derive(Debug, Default, Clone, Copy, RealQuickSer)]
pub struct FunBody {
    pub dependant_functions: EntityList<Fun>,
    pub dependant_globals: EntityList<GlobalValue>,
    pub current_block: PackedOption<Section>,
    pub entry_block: PackedOption<Section>,
    pub last_block: PackedOption<Section>,
}

impl FunBody {
    pub fn clear(&mut self) {
        self.entry_block = PackedOption::default();
        self.last_block = PackedOption::default();
        self.current_block = PackedOption::default();
    }
}

#[derive(Debug, Clone, Default, Copy, RealQuickSer)]
pub struct GlobalEnt {
    id: ID,
    vis: Vis,
    mutable: bool,
    module: Mod,
    ty: Ty,
    hint: Token,
    ast: Ast,
    attrs: Ast,
    alias: Option<Span>,
    linkage: Linkage,
}

#[derive(Debug, Clone, Default, QuickSer)]
pub struct GFun {
    id: Fun,
    call_conv: CallConv,
    sig: GenericSignature,
}

impl SparseMapValue<Fun> for GFun {
    fn key(&self) -> Fun {
        self.id
    }
}

#[derive(Debug, Clone, Default, QuickSer)]
pub struct GenericSignature {
    params: Vec<ID>,
    elements: Vec<GenericElement>,
    arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RealQuickSer)]
pub enum GenericElement {
    ScopeStart,
    ScopeEnd,
    Pointer(bool), // true if mutable
    Array(Option<Ty>),
    Element(Ty, Option<Ty>),
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

#[derive(Debug, Clone)]
pub struct Loop {
    name: ID,
    start_block: Section,
    end_block: Section,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct MainFunData {
    id: Fun,
    arg1: Local,
    arg2: Local,
    return_value: Local,
}

impl Default for MainFunData {
    fn default() -> Self {
        Self {
            id: Fun::reserved_value(),
            arg1: Local::reserved_value(),
            arg2: Local::reserved_value(),
            return_value: Local::reserved_value(),
        }
    }
}

pub struct FunDisplay<'a> {
    ctx: &'a Ctx,
    fun: Fun,
}

impl<'a> FunDisplay<'a> {
    pub fn new(ctx: &'a Ctx, fun: Fun) -> Self {
        Self { ctx, fun }
    }
}

impl std::fmt::Display for FunDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        /*let fun = &self.ctx.funs[self.fun];
        let module_ent = &self.ctx.modules[fun.module];

        writeln!(f, "{}", self.ctx.display(&fun.hint.span))?;
        writeln!(f)?;

        let mut current = fun.body.entry_block;
        while current.is_some() {
            let block = &module_ent.blocks[current.unwrap()];
            writeln!(
                f,
                "  {} {:?}:",
                current.unwrap(),
                module_ent.block_args(current.unwrap())
            )?;
            let mut current_inst = block.start;
            while current_inst.is_some() {
                let inst = &module_ent.insts[current_inst.unwrap()];
                if inst.value.is_none() {
                    writeln!(f, "    {:?}", inst.kind)?;
                } else {
                    writeln!(f, "    {} = {:?}", inst.value.unwrap(), inst.kind)?;
                }
                current_inst = inst.next;
            }
            current = block.next;
        }*/

        Ok(())
    }
}

pub fn test() {
    /*panic!("{}", std::mem::size_of::<Span>());

    const PATH: &str = "src/functions/test_project";

    let now = std::time::Instant::now();
    let (mut state, hint) = Ctx::load_data(PATH, ID(0)).unwrap_or_default();
    let mut context = Ctx::default();
    println!("{}", now.elapsed().as_secs_f32());

    MTParser::new(&mut state, &mut context)
        .parse(PATH)
        .map_err(|e| panic!("\n{}", MTErrorDisplay::new(&state, &e)))
        .unwrap();

    for global in context.globals_to_remove.drain(..) {
        let id = state.globals[global].id;
        state.globals.remove(id);
    }

    let order = std::mem::take(&mut state.module_order);

    // mark all unchanged module type dependencies as used
    let mut used_types = EntitySet::with_capacity(state.types.len());
    let mut used_funs = EntitySet::with_capacity(state.funs.len());
    for &module in &order {
        if state.modules[module].clean {
            let module_ent = &state.t_state.mt_state.modules[module];
            for &ty in module_ent.used_types() {
                used_types.insert(ty);
            }
            for &fun in module_ent.used_functions() {
                used_funs.insert(fun);
            }
        }
    }

    state.t_state.remove_garbage(&used_types);
    state.remove_garbage(&used_funs);

    for &module in &order {
        if state.modules[module].clean {
            continue;
        }

        FParser::new(&mut state, &mut context, I64)
            .parse(module)
            .map_err(|e| panic!("\n{}", FErrorDisplay::new(&mut state, &e)))
            .unwrap();
        
        
    }
   
    println!("{}", now.elapsed().as_secs_f32());
    state.save_data(PATH, ID(0), Some(hint)).unwrap();
    println!("{}", now.elapsed().as_secs_f64());
    */
}