use std::ops::{Deref, DerefMut};
use std::time::Instant;

use crate::ast::{AKind, AstDisplay, AstEnt, OpKind, Vis};
use crate::entities::{Ast, Fun, FunBody, IKind, Mod, Ty, ValueEnt, BUILTIN_MODULE};
use crate::lexer::TKind as LTKind;
use crate::lexer::{Span, Token, TokenDisplay};
use crate::module_tree::{MTErrorDisplay, MTParser};
use crate::util::sdbm::ID;
use crate::util::storage::Table;
use crate::util::Size;
use crate::{incr, types::*};

use cranelift::codegen::ir::types::I64;
use cranelift::codegen::ir::{Block, GlobalValue, Type, Value};
use cranelift::codegen::packed_option::{PackedOption, ReservedValue};
use cranelift::entity::{EntityList, SparseMap, SparseMapValue};
use cranelift::module::Linkage;
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

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
    ptr_ty: Type,
}

crate::inherit!(FParser<'_>, state, FState);

impl<'a> FParser<'a> {
    pub fn new(state: &'a mut FState, context: &'a mut FContext, ptr_ty: Type) -> Self {
        Self {
            state,
            context,
            ptr_ty,
        }
    }

    pub fn parse(&mut self, module: Mod) -> Result {
        TParser::new(self.state, self.context)
            .parse(module)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))?;

        self.clear_incremental_data(module);
        self.init_module(module);
        self.collect(module)?;
        self.translate()?;
        self.finalize_module(module);

        Ok(())
    }

    pub fn clear_incremental_data(&mut self, module: Mod) {
        let mut funs = std::mem::take(&mut self.modules[module].functions);
        for &fun in &funs {
            let id = self.funs[fun].id;
            self.funs.remove(id);
        }
        funs.clear();
        self.modules[module].functions = funs;

        let mut globals = std::mem::take(&mut self.modules[module].globals);
        for &global in &globals {
            let id = self.globals[global].id;
            self.globals.remove(id);
        }
        globals.clear();
        self.modules[module].globals = globals;
    }

    pub fn finalize_module(&mut self, module: Mod) {
        let MainFunData {
            id, return_value, ..
        } = self.context.entry_point_data;
        let mut body = self.funs[id].body;
        self.modules[module].add_return_stmt(Some(return_value), Token::default(), &mut body);
        self.funs[id].body = body;
        self.context.represented.push(id);
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
        let (shadow, id) = self.add_fun(fnu_ent);
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
            let arg_sons = module_ent.son_ent(header, arg_group).sons;
            let arg_sons_len = module_ent.len(arg_sons);
            for arg in 0..arg_sons_len - 1 {
                let module_ent = &mut self.modules[module];
                let id = module_ent.get_ent(arg_sons, arg).token.span.hash;
                let ty = module_ent.type_slice(sig.args)[i];
                let var = module_ent.add_temp_value(ty);
                module_ent.push_block_arg(entry_point, var);
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
                let ty = self.pointer_of(ty);
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
        self.state.funs[fun].body = body;
        self.context.represented.push(fun);
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
                FError::new(FEKind::ContinueOutsideLoop, token)
            } else {
                FError::new(FEKind::WrongLabel, token)
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
                FError::new(FEKind::BreakOutsideLoop, token)
            } else {
                FError::new(FEKind::WrongLabel, token)
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
                return Err(FError::new(FEKind::UnexpectedReturnValue, token));
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
            FError::new(FEKind::ExpectedValue, token)
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
            AKind::Ref => self.ref_expr(fun, ast, body),
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
        let span = self.state.index_span;
        let result = self
            .call_low(fun, None, None, FUN_SALT, span, &[], args, token, body)?
            .ok_or_else(|| FError::new(FEKind::ExpectedValue, token))?;

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
            return Err(FError::new(FEKind::EmptyArray, token));
        }

        let element_ty = element_ty.unwrap();
        let element_size = self.types[element_ty].size;

        let ty = self.array_of(element_ty, length);
        let module_ent = &mut self.state.modules[module];

        let result = module_ent.add_value(ty, true);
        module_ent.add_inst(IKind::Uninitialized, result, token, body);

        for (i, &(value, token)) in values.iter().enumerate() {
            let offset = element_size.mul(Size::new(i as u32, i as u32));
            let offset = module_ent.offset_value(result, element_ty, offset, token, body);
            module_ent.assign(offset, value, token, body);
        }

        Ok(Some(result))
    }

    fn ref_expr(&mut self, fun: Fun, ast: Ast, body: &mut FunBody) -> ExprResult {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let &AstEnt { sons, token, .. } = module_ent.load(ast);
        let value = module_ent.get(sons, 0);
        
        let prev = self.context.in_assign;
        self.context.in_assign = true;
        let value = self.expr(fun, value, body)?;
        self.context.in_assign = prev;

        let reference = self.ref_expr_low(fun, value, token, body);

        Ok(Some(reference))
    }

    fn ref_expr_low(&mut self, fun: Fun, value: Value, token: Token, body: &mut FunBody) -> Value {
        let module = self.funs[fun].module;
        let module_ent = &self.state.modules[module];
        let ty = module_ent.type_of_value(value);
        let ty = self.pointer_of(ty);
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

        reference
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

        let module_ent = &mut self.state.modules[module];
        let value = module_ent.add_value(pointed, true);
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
                &TKind::Pointer(pointed) => match &self.types[pointed].kind {
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
        let mut then_filled = false;
        if let Some(val) = then_result {
            if else_block.is_none() {
                return Err(FError::new(FEKind::MissingElseBranch, token));
            }

            let args = module_ent.add_values(&[val]);
            module_ent.add_valueless_inst(IKind::Jump(merge_block, args), token, body);

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
                    return Err(FError::new(FEKind::UnexpectedValue, token));
                }
            } else {
                if body.current_block.is_some() {
                    if result.is_some() {
                        return Err(FError::new(FEKind::ExpectedValue, token));
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
                                FEKind::ExpectedFunctionPointer,
                                pointer_ast_token,
                            ));
                        }
                    };

                    (self.modules[fp_module].verify_args(&types, fp.args), fp.ret)
                };

                if mismatched {
                    return Err(FError::new(
                        FEKind::FunPointerArgMismatch(
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

        let (_, other_fun) = result
            .map_err(|(a, b)| FError::new(FEKind::AmbiguousFunction(a, b), token))?
            .ok_or_else(|| {
                FError::new(
                    FEKind::FunctionNotFound(name.clone(), types.to_vec()),
                    token,
                )
            })?;

        let other_fun = if let FKind::Generic = self.funs[other_fun].kind {
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
                FError::new(FEKind::GenericMismatch(name.clone(), types.to_vec()), token)
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

        if caller.is_none() {
            if let Some(field) = field {
                values[0] = self.field_access(fun, values[0], field, token, body)?;
            }

            let first_arg_ty = self.modules[other_module].type_slice(sig_args)[0];
            let first_real_arg_ty = self.modules[module].type_of_value(values[0]);

            if first_real_arg_ty != first_arg_ty {
                if self.t_state.pointer_base(first_real_arg_ty) == Some(first_arg_ty) {
                    values[0] = self.deref_expr_low(fun, values[0], token, body)?;
                } else {
                    values[0] = self.ref_expr_low(fun, values[0], token, body);
                }
                debug_assert!(self.modules[module].type_of_value(values[0]) == first_arg_ty);
            }
        }

        if types.len() > 0 {
            types[0] = self.modules[module].type_of_value(values[0]);
        }

        let mismatched = self.modules[other_module].verify_args(&types, sig_args);

        if mismatched {
            return Err(FError::new(
                FEKind::FunArgMismatch(other_fun, types.to_vec()),
                token,
            ));
        }

        let do_stacktrace =
            self.state.do_stacktrace && !untraced && !matches!(other_kind, FKind::Builtin);

        if do_stacktrace {
            self.gen_frame_push(fun, token, body);
        }

        if !self.state.can_access(module, other_module, vis) {
            return Err(FError::new(FEKind::VisibilityViolation, token));
        }

        let module_ent = &mut self.modules[module];
        let args = module_ent.add_values(&values);

        if let Some(value) = value {
            module_ent.add_inst(IKind::Call(other_fun, args), value, token, body);
        } else {
            module_ent.add_valueless_inst(IKind::Call(other_fun, args), token, body);
        }

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
        let ptr = self.pointer_of(u8);
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
        .ok_or_else(|| FError::new(FEKind::UndefinedVariable, token))?;

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
                        .ok_or_else(|| FError::new(FEKind::UnknownModule, module_name_token))?;
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
                .map_err(|(a, b)| FError::new(FEKind::AmbiguousFunction(a, b), ident))?
            {
                Some((other_module, f)) => {
                    let FunEnt { vis, sig, .. } = self.funs[f];
                    if !self.state.can_access(module, other_module, vis) {
                        return Err(FError::new(FEKind::VisibilityViolation, ident));
                    }
                    // we store the pointers in the module function comes from,
                    // this makes it more likely we will reuse already instantiated
                    // pointers, it also means we don't have to reallocate signature
                    // to modules pool
                    let ty = self.function_type_of(other_module, sig);
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
            .map_err(|(a, b)| FError::new(FEKind::AmbiguousGlobal(a, b), name))?;

        let found = if let Some((other_module, found)) = global {
            if !self
                .state
                .can_access(module, other_module, self.state.globals[found].vis)
            {
                return Err(FError::new(FEKind::GlobalVisibilityViolation, name));
            }
            found
        } else {
            return Ok(None);
        };

        let ty = self.state.globals[found].ty;

        let mutable = self.state.globals[found].mutable;
        let module_ent = &mut self.modules[module];
        let value = module_ent.add_value(ty, mutable);
        module_ent.add_inst(IKind::GlobalLoad(found), value, name, body);

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
                        TypeConst::String(val) => (LTKind::String(val), self.pointer_of(repo.u8)),
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
            LTKind::String(_) => self.pointer_of(repo.u8),
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
                FEKind::InvalidBitCast(original_size, datatype_size),
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
        let mutable = module_ent.is_mutable(header) || self.t_state.pointer_base(ty).is_some();
        let mut path = self.context.pool.get();
        let success = self.find_field(ty, field, &mut path);
        if !success {
            return Err(FError::new(FEKind::UnknownField(ty), token));
        };

        let mut offset = Size::ZERO;
        let mut current_type = ty;
        for &i in path.iter().rev() {
            let ty = &self.types[current_type];
            match &ty.kind {
                TKind::Structure(stype) => {
                    let s_field = &stype.fields[i];
                    if !self.state.can_access(module, ty.module, s_field.vis) {
                        return Err(FError::new(FEKind::FieldVisibilityViolation, token));
                    }
                    offset = offset.add(s_field.offset);
                    current_type = s_field.ty;
                }
                &TKind::Pointer(pointed) => {
                    let value =
                        self.modules[module].offset_value(header, pointed, offset, token, body);
                    let ty = &self.types[pointed];
                    match &ty.kind {
                        TKind::Structure(stype) => {
                            let s_field = &stype.fields[i];
                            if !self.state.can_access(module, ty.module, s_field.vis) {
                                return Err(FError::new(FEKind::FieldVisibilityViolation, token));
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

        let prev_in_assign = self.context.in_assign;
        self.context.in_assign = true;
        let target = self.expr(fun, target, body)?;
        self.context.in_assign = prev_in_assign;

        let value = self.expr(fun, value, body)?;

        let module_ent = &mut self.modules[module];
        let target_datatype = module_ent.type_of_value(target);
        let value_datatype = module_ent.type_of_value(value);
        let mutable = module_ent.is_mutable(target);
        if !mutable {
            return Err(FError::new(FEKind::AssignToImmutable, token));
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
        if let Some(&fun) = self.state.funs.index(id) {
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

        let (shadowed, id) = self.add_fun(new_fun_ent);
        debug_assert!(shadowed.is_none());

        self.context.unresolved.push(id);

        Ok(Some(id))
    }

    fn collect(&mut self, module: Mod) -> Result {
        let module_ent = &self.modules[module];
        let funs_len = module_ent.funs().len();
        let globals_len = module_ent.globals().len();
        let mut scope_state = (Ast::reserved_value(), Ast::reserved_value(), ID(0), None);

        for i in (0..funs_len).step_by(3) {
            let funs = self.modules[module].funs();
            let (ast, attrs, scope) = (funs[i], funs[i + 1], funs[i + 2]);
            self.parse_scope(module, scope, &mut scope_state)?;
            self.collect_fun(module, ast, attrs, scope, scope_state.2, scope_state.1)?
        }

        let main_fun_id = self.context.entry_point_data.id;

        let mut body = self.funs[main_fun_id].body;

        for i in (0..globals_len).step_by(3) {
            let globals = self.modules[module].globals();
            let (ast, attrs, scope) = (globals[i], globals[i + 1], globals[i + 2]);
            self.parse_scope(module, scope, &mut scope_state)?;
            self.collect_global_var(module, ast, attrs, scope_state.2, &mut body)?
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
        (previous, generics, id, shadow): &mut (Ast, Ast, ID, Option<(ID, Option<Ty>)>),
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
        let sons = module_ent.sons(ast);
        let generic_ast = module_ent.get(sons, 0);
        let ty = module_ent.get(sons, 1);
        let kind = module_ent.kind(ty);
        let module_id = module_ent.id;

        *generics = generic_ast;

        let ty = match kind {
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
    ) -> Result {
        let fun = self.context.entry_point_data.id;
        let module_ent = &self.modules[module];
        let module_id = module_ent.id;
        let &AstEnt { kind, sons, .. } = module_ent.load(ast);
        let ast_len = module_ent.len(sons);
        let (vis, mutable) = match kind {
            AKind::VarStatement(vis, mutable) => (vis, mutable),
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
                        FEKind::RedefinedGlobal(shadowed.hint.clone()),
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

                self.modules[module].globals.push(global);

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
    ) -> Result {
        let module_ent = &self.modules[module];
        let module_id = module_ent.id;
        let &AstEnt { kind, sons, .. } = module_ent.load(ast);
        let vis = match kind {
            AKind::Fun(vis) => vis,
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
            CallConv::from_str(str).ok_or_else(|| FError::new(FEKind::InvalidCallConv, token))?
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
                    return Err(FError::new(FEKind::InvalidFunctionHeader, name.token));
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
                return Err(FError::new(FEKind::InvalidFunctionHeader, name_ent.token));
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
        let (shadowed, id) = self.add_fun(fun_ent);
        if let Some(shadowed) = shadowed {
            return Err(FError::new(
                FEKind::Redefinition(shadowed.hint.clone()),
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
                let temp_ptr = self.pointer_of(int);
                if count != int || args != self.pointer_of(temp_ptr) {
                    return Err(FError::new(FEKind::InvalidEntrySignature, hint));
                }
                self.modules[module].add_values(&[arg1, arg2])
            }
            _ => {
                return Err(FError::new(FEKind::InvalidEntrySignature, hint));
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
                AKind::Ref => {
                    let pointed = module_ent.get(sons, 0);
                    buffer.push(GenericElement::Pointer);
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
                    &TKind::Pointer(pointed) => {
                        arg_buffer.push(GenericElement::Pointer);
                        stack.push((pointed, false));
                    }
                    &TKind::Array(element, size) => {
                        arg_buffer.push(GenericElement::Array(Some(ty)));
                        stack.push((element, false));
                        let size = self.constant_of(TypeConst::Int(size as i64));
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
            .ok_or_else(|| FError::new(FEKind::NonPointerDereference, token))
    }

    fn parse_type(&mut self, module: Mod, ast: Ast) -> Result<Ty> {
        TParser::new(self.state, self.context)
            .parse_type(module, ast)
            .map(|t| t.1)
            .map_err(|err| FError::new(FEKind::TypeError(err), Token::default()))
    }

    fn resolve_linkage(&self, module: Mod, attrs: Ast) -> Result<(Linkage, Option<Span>)> {
        let module_ent = &self.modules[module];
        if let Some(attr) = module_ent.attr(attrs, ID::new("linkage")) {
            let len = module_ent.ast_len(attr);
            if len < 2 {
                return Err(FError::new(
                    FEKind::TooShortAttribute(len - 1, 1),
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
                _ => return Err(FError::new(FEKind::InvalidLinkage, *module_ent.token(attr))),
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

    fn add_fun(&mut self, fun_ent: FunEnt) -> (Option<FunEnt>, Fun) {
        let module = fun_ent.module;
        let id = fun_ent.id;
        let (shadow, fun) = self.funs.insert(id, fun_ent);
        self.modules[module].add_fun(fun);
        (shadow, fun)
    }
}

fn assert_type(actual: Ty, expected: Ty, token: &Token) -> Result {
    if actual == expected {
        Ok(())
    } else {
        Err(FError::new(FEKind::TypeMismatch(actual, expected), *token))
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

impl<'a> ItemSearch<GlobalValue> for FParser<'a> {
    fn find(&self, id: ID) -> Option<GlobalValue> {
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
            let sig = &self.state.funs[*fun].sig;
            let module = self.state.funs[*fun].module;
            writeln!(
                f,
                "function argument types are '({})' but you provided '({})'",
                sig.args
                    .as_slice(&self.state.modules[module].type_slices)
                    .iter()
                    .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                    .collect::<Vec<_>>().join(", "),
                arguments
                    .iter()
                    .map(|&a| format!("{}", TypeDisplay::new(&self.state, a)))
                    .collect::<Vec<_>>().join(", ")
            )?;
        },
        FEKind::FunPointerArgMismatch(ty, arguments) => {
            let module = self.state.types[*ty].module;
            writeln!(
                f,
                "function pointer argument types are '({})' but you provided '({})'",
                self.state.types[*ty].kind
                    .fun_pointer()
                    .args.as_slice(&self.state.modules[module].type_slices)
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
    TypeError(TError),
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
    MutableRefOfImmutable,
    MissingElseBranch,
    ContinueOutsideLoop,
    BreakOutsideLoop,
    WrongLabel,
    NonPointerDereference,
    InvalidFunctionHeader,
    AmbiguousFunction(Fun, Fun),
    AmbiguousGlobal(GlobalValue, GlobalValue),
}

pub enum DotInstr {
    None,
    Deref,
    Ref,
}

#[derive(Debug, Clone, QuickDefault, Copy, RealQuickSer)]
pub struct FunEnt {
    pub id: ID,
    pub module: Mod,
    pub hint: Token,
    pub params: EntityList<Ty>,
    pub base_fun: PackedOption<Fun>,
    pub sig: Signature,
    pub body: FunBody,
    pub kind: FKind,
    pub name: Span,
    pub ast: Ast,
    pub attrs: Ast,
    pub scope: Ast,
    pub alias: Option<Span>,
    pub vis: Vis,
    pub linkage: Linkage,
    pub untraced: bool,
    pub inline: bool,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub enum FKind {
    Builtin,
    Generic,
    Normal,
    Represented,
}

impl Default for FKind {
    fn default() -> Self {
        FKind::Builtin
    }
}

#[derive(Debug, Clone, Default, QuickSer)]
pub struct GFun {
    pub id: Fun,
    pub call_conv: CallConv,
    pub sig: GenericSignature,
}

impl SparseMapValue<Fun> for GFun {
    fn key(&self) -> Fun {
        self.id
    }
}

#[derive(Debug, Clone, Default, QuickSer)]
pub struct GenericSignature {
    pub params: Vec<ID>,
    pub elements: Vec<GenericElement>,
    pub arg_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RealQuickSer)]
pub enum GenericElement {
    ScopeStart,
    ScopeEnd,
    Pointer,
    Array(Option<Ty>),
    ArraySize(u32),
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
    start_block: Block,
    end_block: Block,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct GlobalEnt {
    pub id: ID,
    pub vis: Vis,
    pub mutable: bool,
    pub module: Mod,
    pub ty: Ty,
    pub hint: Token,
    pub ast: Ast,
    pub attrs: Ast,
    pub alias: Option<Span>,
    pub linkage: Linkage,
}

impl Default for GlobalEnt {
    fn default() -> Self {
        Self {
            id: ID(0),
            vis: Vis::Public,
            mutable: false,
            module: Mod::reserved_value(),
            ty: Ty::reserved_value(),
            hint: Token::default(),
            ast: Ast::reserved_value(),
            attrs: Ast::reserved_value(),
            alias: None,
            linkage: Linkage::Export,
        }
    }
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct MainFunData {
    id: Fun,
    arg1: Value,
    arg2: Value,
    return_value: Value,
}

impl Default for MainFunData {
    fn default() -> Self {
        Self {
            id: Fun::reserved_value(),
            arg1: Value::reserved_value(),
            arg2: Value::reserved_value(),
            return_value: Value::reserved_value(),
        }
    }
}

#[derive(QuickSer)]
pub struct FState {
    pub t_state: TState,
    pub funs: Table<Fun, FunEnt>,
    pub generic_funs: SparseMap<Fun, GFun>,
    pub globals: Table<GlobalValue, GlobalEnt>,

    pub index_span: Span,
    pub do_stacktrace: bool,

    pub pop_fun_hahs: ID,
    pub push_fun_hash: ID,
}

crate::inherit!(FState, t_state, TState);

impl Default for FState {
    fn default() -> Self {
        let mut state = Self {
            t_state: TState::default(),
            funs: Table::new(),
            generic_funs: SparseMap::new(),
            index_span: Span::default(),
            globals: Table::new(),
            do_stacktrace: false,

            pop_fun_hahs: ID(0),
            push_fun_hash: ID(0),
        };

        state.pop_fun_hahs = FUN_SALT
            .add(ID::new("pop_frame"))
            .add(ID(0))
            .add(state.modules[BUILTIN_MODULE].id);

        state.push_fun_hash = FUN_SALT
            .add(ID::new("push_frame"))
            .add(ID(0))
            .add(state.modules[BUILTIN_MODULE].id);

        let span = state.builtin_span("__index__");

        state.index_span = span;

        let module_id = BUILTIN_MODULE;

        let types = state.builtin_repo.type_list();

        fn create_builtin_fun(
            state: &mut FState,
            module: Mod,
            salt: ID,
            name: Span,
            args: &[Ty],
            ret: PackedOption<Ty>,
        ) {
            let id = salt.add(name.hash).add(state.types[args[0]].id);
            let module_ent = &mut state.modules[module];
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
                module: BUILTIN_MODULE,
                kind: FKind::Builtin,
                sig,

                ..Default::default()
            };
            assert!(state.funs.insert(id, fun_ent).0.is_none());
        }

        for i in types {
            for j in types {
                let name = state.types[i].name.clone();
                create_builtin_fun(
                    &mut state,
                    module_id,
                    FUN_SALT,
                    name,
                    &[j],
                    PackedOption::from(i),
                );
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
                        PackedOption::from(datatype),
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
                        PackedOption::from(return_type),
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

    pub vars: Vec<(ID, Value)>,
    pub loops: Vec<Loop>,
    pub frames: Vec<usize>,

    pub in_assign: bool,

    pub unresolved_globals: Vec<GlobalValue>,
    pub resolved_globals: Vec<GlobalValue>,
    pub unresolved: Vec<Fun>,
    pub represented: Vec<Fun>,
    pub entry_points: Vec<Fun>,

    pub entry_point_data: MainFunData,
}

crate::inherit!(FContext, t_context, TContext);

impl FContext {
    fn push_scope(&mut self) {
        self.frames.push(self.vars.len());
    }

    fn pop_scope(&mut self) {
        let idx = self.frames.pop().unwrap();
        self.vars.truncate(idx)
    }

    fn find_variable(&self, id: ID) -> Option<Value> {
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
        let module_ent = &self.state.modules[fun.module];

        writeln!(f, "{}", self.state.display(&fun.hint.span))?;
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
        }

        Ok(())
    }
}

pub fn test() {
    const PATH: &str = "src/functions/test_project";

    let now = Instant::now();

    let (mut state, hint) = incr::load_data::<FState>(PATH, ID(0)).unwrap_or_default();
    let mut context = FContext::default();

    MTParser::new(&mut state, &mut context)
        .parse(PATH)
        .map_err(|e| panic!("\n{}", MTErrorDisplay::new(&state, &e)))
        .unwrap();

    for module in std::mem::take(&mut state.module_order).drain(..) {
        if state.modules[module].clean {
            continue;
        }

        crate::test_println!("re-parsing {}", state.display(&state.modules[module].name));

        FParser::new(&mut state, &mut context, I64)
            .parse(module)
            .map_err(|e| panic!("\n{}", FErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }

    for module in state.modules.iter_mut() {
        module.clean = true;
    }

    /*for &fun in &context.represented {
        println!("{}", FunDisplay::new(&state, fun));
    }*/

    incr::save_data(PATH, &state, ID(0), Some(hint)).unwrap();

    println!("compiled code in {}s", now.elapsed().as_secs_f64());
}
