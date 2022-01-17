use std::ops::{Deref, DerefMut};

use crate::ast::{AError, AErrorDisplay, AKind, AstEnt, Vis};
use crate::entities::{
    Ast, Mod, Ty, 
    BUILTIN_MODULE, TypeConst, Signature, 
    TKind, TypeEnt, CallConv, 
    SField, SType, SKind, CrTypeWr,
};
use crate::incr;
use crate::lexer::{TKind as LTKind, Token, TokenDisplay};
use crate::module_tree::{MTContext, MTErrorDisplay, MTParser, MTState, TreeStorage};
use crate::util::sdbm::ID;
use crate::util::storage::Table;
use crate::util::Size;
use cranelift::codegen::ir::types::Type;
use cranelift::codegen::ir::Signature as CrSignature;
use cranelift::codegen::ir::{types::*, AbiParam, ArgumentPurpose};
use cranelift::codegen::isa::TargetIsa;
use cranelift::codegen::packed_option::PackedOption;
use cranelift::entity::EntityList;
use cranelift::entity::{packed_option::ReservedValue, EntityRef};
use quick_proc::{QuickSer, RealQuickSer};

type Result<T = ()> = std::result::Result<T, TError>;

pub const TYPE_SALT: ID = ID(0x9e3779b97f4a7c15);

pub const VISIBILITY_MESSAGE: &str = concat!(
    "removing 'priv' in case of different module but same package or adding",
    " 'pub' in case of different package can help",
);

pub static mut POINTER_TYPE: Type = INVALID;

pub struct TParser<'a> {
    module: Mod,
    state: &'a mut TState,
    context: &'a mut TContext,
}

crate::inherit!(TParser<'_>, state, TState);

impl<'a> TParser<'a> {
    pub const MAX_TYPE_INSTANTIATION_DEPTH: usize = 1000;

    pub fn new(state: &'a mut TState, context: &'a mut TContext) -> Self {
        Self {
            module: Mod::new(0),
            state,
            context,
        }
    }

    pub fn parse(&mut self, module: Mod) -> Result {
        self.module = module;
        self.collect(module)?;
        self.connect()?;
        self.calc_sizes()?;
        Ok(())
    }

    pub fn parse_type(&mut self, module: Mod, ast: Ast) -> Result<(Mod, Ty)> {
        self.module = module;
        let result = self.ty(module, ast, 0)?;

        self.connect()?;
        self.calc_sizes()?;
        Ok(result)
    }

    fn calc_sizes(&mut self) -> Result {
        let mut lookup = std::mem::take(&mut self.type_cycle_map);
        let mut resolved = std::mem::take(&mut self.context.resolved);
        let mut ordering = self.context.pool.get();
        let mut cycle_stack = self.context.pool.get();
        lookup.resize(self.types.len(), (false, false));

        for ty in resolved.drain(..) {
            if lookup[ty.index()].0 {
                continue;
            }

            if let Some(cycle) =
                self.detect_cycles(ty, &mut cycle_stack, &mut lookup, Some(&mut ordering))
            {
                return Err(TError::new(TEKind::InfiniteSize(cycle), Token::default()));
            }

            for ty in ordering.drain(..) {
                self.calc_size(ty)?;
            }
        }

        self.context.resolved = resolved;
        self.type_cycle_map = lookup;

        Ok(())
    }

    fn calc_size(&mut self, ty: Ty) -> Result {
        let ty_ent = &mut self.types[ty];
        match &mut ty_ent.kind {
            TKind::Structure(stype) => {
                let mut size = Size::ZERO;
                let mut fields = std::mem::take(&mut stype.fields);
                let kind = stype.kind;
                let align = fields
                    .iter()
                    .map(|field| self.types[field.ty].align)
                    .max()
                    .unwrap_or(Size::ZERO);

                if align != Size::ZERO {
                    match kind {
                        SKind::Struct => {
                            let calc = move |offset: Size| {
                                let temp = Size::new(
                                    offset.s32 & (align.s32 - 1),
                                    offset.s64 & (align.s64 - 1),
                                );
                                let add = (temp != Size::ZERO) as u32;
                                Size::new(align.s32 * add - temp.s32, align.s64 * add - temp.s64)
                            };

                            for field in &mut fields {
                                size = size.add(calc(size));
                                field.offset = size;
                                size = size.add(self.types[field.ty].size);
                            }

                            size = size.add(calc(size));
                        }
                        SKind::Union => {
                            size = fields
                                .iter()
                                .map(|field| self.types[field.ty].size)
                                .max()
                                .unwrap();
                        }
                    }
                }

                self.types[ty].kind.structure_mut().fields = fields;

                let ty_ent = &mut self.types[ty];
                ty_ent.align = align;
                ty_ent.size = size;
            }
            &mut TKind::Array(element, size) => {
                let element_size = self.types[element].size;
                self.types[ty].size = Size::new(size, size).mul(element_size);
            }
            TKind::Enumeration(_) |
            TKind::Pointer(..) | 
            TKind::Builtin(..) | 
            TKind::FunPointer(..) => (),
            
            TKind::Constant(_) |
            TKind::Generic(_) |
            TKind::Unresolved(_) => unreachable!("{:?}", ty_ent.kind),
        }

        Ok(())
    }

    fn connect(&mut self) -> Result {
        while let Some((id, depth)) = self.context.unresolved.pop() {
            if depth > Self::MAX_TYPE_INSTANTIATION_DEPTH {
                return Err(TError::new(
                    TEKind::InstantiationDepthExceeded,
                    self.types[id].hint.clone(),
                ));
            }

            let ty = &self.types[id];
            let ty_module = ty.module;

            match &ty.kind {
                &TKind::Unresolved(ast) => self.connect_type(ty_module, id, ast, depth)?,
                _ => unreachable!("{:?}", &self.types[id].kind),
            }

            self.context.resolved.push(id);
        }
        Ok(())
    }

    fn connect_type(&mut self, module: Mod, id: Ty, ast: Ast, depth: usize) -> Result {
        match self.modules[module].kind(ast) {
            AKind::Struct(_) => {
                self.connect_structure(module, id, ast, SKind::Struct, depth)?;
            }
            AKind::Union(_) => {
                self.connect_structure(module, id, ast, SKind::Union, depth)?;
            }
            kind => unreachable!("{:?}", kind),
        }

        Ok(())
    }

    fn connect_structure(
        &mut self,
        module: Mod,
        id: Ty,
        ast: Ast,
        kind: SKind,
        depth: usize,
    ) -> Result {
        let mut fields = self.context.pool.get();

        let module_ent = &self.state.modules[module];

        let module_id = module_ent.id;
        let params = self.state.types[id].params;
        let params_len = module_ent.type_slice(params).len();
        let mut shadowed = self.context.pool.get();

        let header = module_ent.son(ast, 0);
        let header_ent = module_ent.load(header);
        let header_len = module_ent.len(header_ent.sons);

        let is_instance = header_ent.kind == AKind::Instantiation;

        if is_instance {
            if params_len != header_len {
                return Err(TError::new(
                    TEKind::WrongInstantiationArgAmount(params_len - 1, header_len - 1),
                    self.types[id].hint.clone(),
                ));
            }
            for i in 1..header_len {
                let module_ent = &self.modules[module];
                let param = module_ent.type_slice(params)[i];
                let hash = module_ent.son_ent(header, i).token.span.hash;
                let id = TYPE_SALT.add(hash).add(module_id);

                let sha = self.state.types.link(id, param);
                shadowed.push((id, sha));
            }
        }

        let module_ent = &self.modules[module];
        let body = module_ent.son(ast, 1);
        if body != Ast::reserved_value() {
            let body = *module_ent.load(body);
            let len = module_ent.len(body.sons);
            for i in 0..len {
                let module_ent = &self.modules[module];
                let &AstEnt { sons, kind, token } = module_ent.get_ent(body.sons, i);
                let field_line_len = module_ent.len(sons);
                let type_ast = module_ent.get(sons, field_line_len - 1);
                let (vis, embedded) = match &kind {
                    &AKind::StructField(vis, embedded) => (vis, embedded),
                    _ => unreachable!("{:?}", kind),
                };
                let (_, ty) = self.ty(module, type_ast, depth)?;
                let hint = token;
                let module_ent = &self.modules[module];
                let field_ids = self.modules[module].slice(sons);
                for &field in field_ids[..field_line_len - 1].iter() {
                    let id = module_ent.token(field).span.hash;
                    let field = SField {
                        embedded,
                        vis,
                        id,
                        offset: Size::ZERO,
                        ty,
                        hint: hint.clone(),
                    };

                    fields.push(field);
                }
            }
        }

        for (id, ty) in shadowed.drain(..) {
            self.types.remove_link(id, ty);
        }

        let s_ent = SType {
            kind,
            fields: fields.clone(),
        };

        self.types[id].kind = TKind::Structure(s_ent);

        Ok(())
    }

    fn ty(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.modules[module];
        let &AstEnt { kind, token, sons } = module_ent.a_state.load(ast);
        let (ty_module, ty) = match kind {
            AKind::Ident => self.simple_type(module, None, ast, &token),
            AKind::Path => {
                let module_name = module_ent.get(sons, 0);
                let name = module_ent.get(sons, 1);
                self.simple_type(module, Some(module_name), name, &token)
            }
            AKind::Instantiation => self.instance(module, ast, depth),
            AKind::Ref(mutable) => self.pointer(module, ast, depth, mutable),
            AKind::Array => self.array(module, ast, depth),
            AKind::Lit => self.constant(module, &token),
            AKind::FunHeader(..) => self.function_pointer(module, ast, depth),
            _ => unreachable!("{:?}", kind),
        }?;

        if !self.state.can_access(module, ty_module, self.types[ty].vis) {
            return Err(TError::new(TEKind::VisibilityViolation, token));
        }

        Ok((module, ty))
    }

    fn function_pointer(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.modules[module];
        let sons = module_ent.sons(ast);
        let len = module_ent.len(sons);

        let mut args = EntityList::new();
        for i in 1..len - 2 {
            let arg = self.modules[module].get(sons, i);
            let (_, ty) = self.ty(module, arg, depth)?;
            self.modules[module].push_type(&mut args, ty);
        }

        let module_ent = &self.modules[module];
        let ret = module_ent.get(sons, len - 2);
        let ret = if ret != Ast::reserved_value() {
            let (_, ty) = self.ty(module, ret, depth)?;
            PackedOption::from(ty)
        } else {
            PackedOption::default()
        };

        let module_ent = &self.modules[module];
        let call_conv = module_ent.get(sons, len - 1);
        let call_conv = if call_conv != Ast::reserved_value() {
            let token = module_ent.token(call_conv);
            let str = self.display(&token.span);
            CallConv::from_str(str).ok_or_else(|| TError::new(TEKind::InvalidCallConv, *token))?
        } else {
            CallConv::Fast
        };

        let sig = Signature {
            args: args.clone(),
            ret,
            call_conv,
        };

        let id = self.function_type_of(module, sig);

        Ok((module, id))
    }

    fn array(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.modules[module];
        let element = module_ent.son(ast, 0);
        let length_ast = module_ent.son(ast, 1);

        let (_, element) = self.ty(module, element, depth)?;
        let (_, length) = self.ty(module, length_ast, depth)?;
        let length = match self.types[length].kind {
            TKind::Constant(TypeConst::Int(i)) => i,
            _ => {
                return Err(TError::new(
                    TEKind::ExpectedIntConstant,
                    *self.modules[module].token(length_ast),
                ))
            }
        };

        Ok((module, self.array_of(element, length as usize)))
    }

    fn constant(&mut self, module: Mod, token: &Token) -> Result<(Mod, Ty)> {
        let constant = match token.kind.clone() {
            LTKind::Int(val, _) => TypeConst::Int(val),
            LTKind::Uint(val, _) => TypeConst::Int(val as i64),
            LTKind::Float(val, _) => TypeConst::Float(val),
            LTKind::Bool(val) => TypeConst::Bool(val),
            LTKind::Char(val) => TypeConst::Char(val),
            LTKind::String(val) => TypeConst::String(val),
            _ => unreachable!("{:?}", token.kind),
        };

        let ty = self.constant_of(constant);

        Ok((module, ty))
    }

    fn pointer(&mut self, module: Mod, ast: Ast, depth: usize, mutable: bool) -> Result<(Mod, Ty)> {
        let (module, datatype) = self.ty(module, self.modules[module].son(ast, 0), depth)?;
        let datatype = self.pointer_of(datatype, mutable);

        Ok((module, datatype))
    }

    fn instance(&mut self, source_module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.modules[source_module];
        let ident = module_ent.son(ast, 0);
        let &AstEnt { token, sons, kind } = module_ent.load(ident);
        let (module, ty) = match kind {
            AKind::Ident => self.simple_type(source_module, None, ident, &token)?,
            AKind::Path => {
                let module_name = module_ent.get(sons, 0);
                let name = module_ent.get(sons, 1);
                self.simple_type(source_module, Some(module_name), name, &token)?
            }
            _ => unreachable!("{:?}", kind),
        };

        let mut params = EntityList::new();
        let module_ent = &mut self.modules[source_module];
        let sons = module_ent.sons(ast);
        let ast_len = module_ent.len(sons);

        self.modules[module].push_type(&mut params, ty);

        let mut id = TYPE_SALT.add(self.types[ty].id);
        for i in 1..ast_len {
            let ty = self.modules[source_module].get(sons, i);
            let ty = self.ty(source_module, ty, depth)?.1;
            id = id.add(self.types[ty].id);
            self.modules[module].push_type(&mut params, ty);
        }
        id = id.add(self.modules[module].id);

        if let Some(id) = self.type_index(id) {
            self.modules[module].clear_type_slice(&mut params);
            return Ok((module, id));
        }

        let ty_ent = &self.types[ty];

        let ast = match ty_ent.kind {
            TKind::Generic(ast) => ast,
            _ => {
                return Err(TError::new(
                    TEKind::InstancingNonGeneric(ty_ent.hint.clone()),
                    token,
                ))
            }
        };

        let &TypeEnt {
            vis, name, attrs, ..
        } = ty_ent;

        let type_ent = TypeEnt {
            id,
            module,
            vis,
            params,
            kind: TKind::Unresolved(ast),
            name,
            hint: token,
            attrs,
            size: Size::ZERO,
            align: Size::ZERO,
        };

        let ty = self.add_type(type_ent);

        self.context.unresolved.push((ty, depth));

        Ok((module, ty))
    }

    fn simple_type(
        &mut self,
        module: Mod,
        target: Option<Ast>,
        name: Ast,
        token: &Token,
    ) -> Result<(Mod, Ty)> {
        let module_ent = &self.modules[module];
        let id = TYPE_SALT.add(module_ent.token(name).span.hash);

        let target = if let Some(target) = target {
            let token = module_ent.token(target);
            Some(
                self.find_dep(module, token)
                    .ok_or(TError::new(TEKind::UnknownModule, *token))?,
            )
        } else {
            None
        };

        let mut buffer = self.context.pool.get();
        self.find_item(module, id, target, &mut buffer)
            .map_err(|(a, b)| TError::new(TEKind::AmbiguousType(a, b), *token))?
            .ok_or_else(|| TError::new(TEKind::UnknownType, *token))
    }

    fn collect(&mut self, module: Mod) -> Result<()> {
        let module_ent = &self.modules[module];
        let module_name = module_ent.id;
        let types = module_ent.types();

        for i in (0..types.len()).step_by(2) {
            let module_ent = &self.modules[module];
            let types = module_ent.types();
            let type_ast = types[i];
            let attrs = types[i + 1];
            let &AstEnt { token, kind, sons } = module_ent.load(type_ast);
            match kind {
                AKind::Enum(vis) => {
                    let ident = *module_ent.get_ent(sons, 0);
                    let variants = module_ent.get(sons, 1);
                    let variants = if !variants.is_reserved_value() {
                        let variants = module_ent.sons(variants);
                        let variants_len = module_ent.len(variants);
                        let mut real_variants = Vec::with_capacity(variants_len);
                        for i in 0..variants_len {
                            real_variants.push(module_ent.get_ent(variants, i).token.span.hash);
                        }
                        real_variants
                    } else {
                        vec![]
                    };

                    let kind = TKind::Enumeration(variants);
                    let id = TYPE_SALT.add(ident.token.span.hash).add(module_name);
                    let datatype = TypeEnt {
                        vis,
                        id,
                        module,
                        kind,
                        name: ident.token.span,
                        attrs,
                        hint: ident.token,

                        ..Default::default()
                    };

                    let (replaced, _) = self.add_type_low(datatype, true);
                    if let Some(other) = replaced {
                        return Err(TError::new(TEKind::Redefinition(other.hint), token));
                    }
                }
                AKind::Struct(vis) | AKind::Union(vis) => {
                    let ident = module_ent.get(sons, 0);
                    let ident_ent = module_ent.load(ident);
                    let (ident, kind) = if ident_ent.kind == AKind::Ident {
                        (ident_ent, TKind::Unresolved(type_ast))
                    } else if ident_ent.kind == AKind::Instantiation {
                        (
                            module_ent.a_state.get_ent(ident_ent.sons, 0),
                            TKind::Generic(type_ast),
                        )
                    } else {
                        return Err(TError::new(
                            TEKind::UnexpectedAst(String::from("expected struct identifier")),
                            ident_ent.token,
                        ));
                    };

                    let id = TYPE_SALT.add(ident.token.span.hash).add(module_name);
                    let datatype = TypeEnt {
                        vis,
                        id,
                        module,
                        kind,
                        name: ident.token.span,
                        attrs,
                        hint: ident.token,

                        ..Default::default()
                    };

                    let (replaced, id) = self.add_type_low(datatype, true);
                    if let Some(other) = replaced {
                        return Err(TError::new(TEKind::Redefinition(other.hint), token));
                    }

                    if let TKind::Unresolved(_) = &self.types[id].kind {
                        self.context.unresolved.push((id, 0));
                    }
                }
                kind => unreachable!("{:?}", kind),
            }
        }

        Ok(())
    }

    fn type_index(&self, id: ID) -> Option<Ty> {
        self.types.index(id).cloned()
    }
}

impl<'a> ItemSearch<Ty> for TParser<'a> {
    fn find(&self, id: ID) -> Option<Ty> {
        self.types.index(id).cloned()
    }

    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        self.collect_scopes(module, buffer)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.modules[module].id
    }
}

impl<'a> TreeStorage<Ty> for TParser<'a> {
    fn node_dep(&self, id: Ty, idx: usize) -> Ty {
        let node = &self.types[id];
        match &node.kind {
            TKind::Structure(stype) => stype.fields[idx].ty,
            TKind::Array(ty, _) => *ty,
            TKind::FunPointer(fun) => {
                if idx == self.modules[node.module].type_slice(fun.args).len() {
                    fun.ret.unwrap()
                } else {
                    self.modules[node.module].type_slice(fun.args)[idx]
                }
            }
            _ => unreachable!("{:?}", node.kind),
        }
    }

    fn node_len(&self, id: Ty) -> usize {
        let node = &self.types[id];

        match &node.kind {
            TKind::Builtin(_) | TKind::Pointer(..) | TKind::Enumeration(_) => 0,
            TKind::FunPointer(fun) => {
                self.modules[node.module].type_slice(fun.args).len() + fun.ret.is_some() as usize
            }
            TKind::Array(..) => 1,
            TKind::Structure(stype) => stype.fields.len(),
            TKind::Generic(_) | TKind::Unresolved(_) | TKind::Constant(_) => {
                unreachable!("{:?}", node)
            }
        }
    }

    fn len(&self) -> usize {
        self.types.len()
    }
}

pub trait ItemSearch<T: EntityRef> {
    fn find(&self, id: ID) -> Option<T>;
    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>);
    fn module_id(&self, module: Mod) -> ID;

    fn find_item(
        &self,
        module: Mod,
        id: ID,
        target_module: Option<Mod>,
        buffer: &mut Vec<(Mod, ID)>,
    ) -> std::result::Result<Option<(Mod, T)>, (T, T)> {
        if let Some(module) = target_module {
            Ok(self
                .find(id.add(self.module_id(module)))
                .map(|id| (module, id)))
        } else {
            if let Some(fun) = self.find(id.add(self.module_id(module))) {
                Ok(Some((module, fun)))
            } else {
                self.scopes(module, buffer);

                let mut found = None;
                for (module, module_id) in buffer.drain(1..) {
                    if let Some(fun) = self.find(id.add(module_id)) {
                        if let Some((_, found)) = found {
                            return Err((found, fun));
                        }
                        found = Some((module, fun));
                        break;
                    }
                }
                Ok(found)
            }
        }
    }
}

pub struct TypeConstDisplay<'a> {
    state: &'a TState,
    constant: &'a TypeConst,
}

impl<'a> TypeConstDisplay<'a> {
    pub fn new(state: &'a TState, constant: &'a TypeConst) -> Self {
        Self { state, constant }
    }
}

impl std::fmt::Display for TypeConstDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.constant {
            TypeConst::Bool(b) => write!(f, "{}", b),
            TypeConst::Int(i) => write!(f, "{}", i),
            TypeConst::Float(float) => write!(f, "{}", float),
            TypeConst::Char(c) => write!(f, "'{}'", c),
            TypeConst::String(s) => write!(f, "\"{}\"", self.state.display(s)),
        }
    }
}

impl Signature {
    pub fn to_cr_signature(
        &self,
        module: Mod,
        state: &TState,
        isa: &dyn TargetIsa,
        target: &mut CrSignature,
    ) {
        target.call_conv = self.call_conv.to_cr_call_conv(isa);
        target.params.extend(
            state.modules[module]
                .type_slice(self.args)
                .iter()
                .map(|&ty| AbiParam::new(state.types[ty].to_cr_type(isa))),
        );
        if self.ret.is_some() {
            let ret = self.ret.unwrap();
            let ty = &state.types[ret];
            let param = if ty.on_stack(isa.pointer_type()) {
                let param = AbiParam::special(ty.to_cr_type(isa), ArgumentPurpose::StructReturn);
                target.params.push(param);
                param
            } else {
                AbiParam::new(ty.to_cr_type(isa))
            };
            target.returns.push(param);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TContext {
    pub mt_context: MTContext,
    pub constant_buffer: String,
    pub unresolved: Vec<(Ty, usize)>,
    pub resolved: Vec<Ty>,
}

crate::inherit!(TContext, mt_context, MTContext);

#[derive(Debug, Clone, QuickSer)]
pub struct TState {
    pub builtin_repo: BuiltinRepo,
    pub types: Table<Ty, TypeEnt>,

    pub type_cycle_map: Vec<(bool, bool)>,
    pub mt_state: MTState,
}

impl TState {
    pub fn pointer_of(&mut self, ty: Ty, mutable: bool) -> Ty {
        let module = self.types[ty].module;
        let name = if mutable { "&var " } else { "&" };
        let id = TYPE_SALT
            .add(ID::new(name))
            .add(self.types[ty].id)
            .add(self.modules[module].id);

        if let Some(&index) = self.types.index(id) {
            return index;
        }

        let size = Size::POINTER;

        let pointer_type = TypeEnt {
            vis: Vis::Public,
            id,
            kind: TKind::Pointer(ty, mutable),
            module,
            size,
            align: size,

            ..Default::default()
        };

        self.add_type(pointer_type)
    }

    pub fn array_of(&mut self, element: Ty, length: usize) -> Ty {
        let TypeEnt {
            id, module, ..
        } = self.types[element];

        let id = TYPE_SALT
            .add(ID::new("[]"))
            .add(id)
            .add(ID(length as u64));

        if let Some(&index) = self.types.index(id) {
            return index;
        }

        let ty_ent = TypeEnt {
            id,
            vis: Vis::Public,
            module,
            kind: TKind::Array(element, length as u32),

            size: self.types[element]
                .size
                .mul(Size::new(length as u32, length as u32)),
            align: self.types[element].align,

            ..Default::default()
        };

        self.add_type(ty_ent)
    }

    pub fn constant_of(&mut self, constant: TypeConst) -> Ty {
        let display = format!("{}", TypeConstDisplay::new(self, &constant));

        let id = TYPE_SALT.add(ID::new(&display));

        if let Some(&tp) = self.types.index(id) {
            return tp;
        }

        let ty_ent = TypeEnt {
            id,
            vis: Vis::Public,
            kind: TKind::Constant(constant),
            module: Mod::new(0),

            ..Default::default()
        };

        self.add_type(ty_ent)
    }

    pub fn function_type_of(&mut self, module: Mod, sig: Signature) -> Ty {
        let mut id = TYPE_SALT.add(ID::new("fun")).add(ID(unsafe {
            std::mem::transmute::<_, u8>(sig.call_conv)
        } as u64));

        for arg in self.modules[module].type_slice(sig.args).iter() {
            id = id.add(self.types[*arg].id);
        }

        if sig.ret.is_some() {
            id = id.add(ID::new("->")).add(self.types[sig.ret.unwrap()].id);
        }

        if let Some(&id) = self.types.index(id) {
            return id;
        }

        let size = Size::POINTER;
        let type_ent = TypeEnt {
            kind: TKind::FunPointer(sig),
            id,
            module,
            vis: Vis::None,
            size,
            align: size,

            ..Default::default()
        };

        self.add_type(type_ent)
    }

    pub fn add_type(&mut self, ent: TypeEnt) -> Ty {
        let (shadow, id) = self.add_type_low(ent, false);
        debug_assert!(shadow.is_none(), "{:?}", id);
        id
    }

    pub fn add_type_low(&mut self, ent: TypeEnt, allow_shadow: bool) -> (Option<TypeEnt>, Ty) {
        let module = ent.module;
        let (shadow, ty) = self.types.insert(ent.id, ent);
        self.modules[module].add_type(ty);
        debug_assert!(shadow.is_none() || allow_shadow);
        (shadow, ty)
    }

    pub fn pointer_base(&self, ty: Ty) -> Option<Ty> {
        if let TKind::Pointer(base, _) = self.types[ty].kind {
            Some(base)
        } else {
            None
        }
    }

    pub fn pointer_mutability(&self, ty: Ty) -> bool {
        if let TKind::Pointer(_, mutability) = self.types[ty].kind {
            mutability
        } else {
            false
        }
    }

    pub fn base_of(&self, ty: Ty) -> Ty {
        if let TKind::Array(..) = self.types[ty].kind {
            return self.builtin_repo.array;
        }
        let TypeEnt { module, params, .. } = self.types[ty];
        self.modules[module]
            .type_slice(params)
            .first()
            .cloned()
            .unwrap_or(ty)
    }
}

crate::inherit!(TState, mt_state, MTState);

impl Default for TState {
    fn default() -> Self {
        let mut s = Self {
            builtin_repo: Default::default(),
            types: Table::new(),
            mt_state: MTState::default(),
            type_cycle_map: Vec::new(),
        };

        s.builtin_repo = BuiltinRepo::new(&mut s);

        return s;
    }
}

macro_rules! define_repo {
    (
        $($name:ident, $repr:expr, $s32:expr, $s64:expr);+
    ) => {
        #[derive(Clone, Debug, Copy, RealQuickSer)]
        pub struct BuiltinRepo {
            $(pub $name: Ty,)+
        }

        impl Default for BuiltinRepo {
            fn default() -> Self {
                Self {
                    $(
                        $name: Ty::new(0),
                    )+
                }
            }
        }

        impl BuiltinRepo {
            pub fn new(state: &mut TState) -> Self {
                let module = BUILTIN_MODULE;
                let builtin_id = state.modules[module].id;

                $(
                    let name = state.builtin_span(stringify!($name));
                    let id = TYPE_SALT.add(ID::new(stringify!($name))).add(builtin_id);
                    let type_ent = TypeEnt {
                        id,
                        vis: Vis::Public,
                        kind: TKind::Builtin(CrTypeWr($repr)),
                        size: Size::new($s32, $s64),
                        align: Size::new($s32, $s64).min(Size::new(4, 8)),
                        module,
                        hint: Token::new(LTKind::Ident, name.clone()),
                        name,

                        ..Default::default()
                    };
                    let $name = state.add_type(type_ent);
                )+

                Self {
                    $($name,)+
                }
            }

            pub fn type_list(&self) -> [Ty; 14] {
                [
                    $(self.$name,)+
                ]
            }
        }
    };
}

define_repo!(
    i8, I8, 1, 1;
    i16, I16, 2, 2;
    i32, I32, 4, 4;
    i64, I64, 8, 8;
    u8, I8, 1, 1;
    u16, I16, 2, 2;
    u32, I32, 4, 4;
    u64, I64, 8, 8;
    f32, F32, 4, 4;
    f64, F64, 8, 8;
    bool, B1, 1, 1;
    int, INVALID, 4, 8;
    uint, INVALID, 4, 8;
    array, INVALID, 0, 0
);

pub struct TypeDisplay<'a> {
    state: &'a TState,
    type_id: Ty,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(state: &'a TState, type_id: Ty) -> Self {
        Self { state, type_id }
    }
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let ty = &self.state.types[self.type_id];
        match &ty.kind {
            &TKind::Pointer(id, mutable) => if mutable {
                write!(f, "&var {}", Self::new(self.state, id))
            } else {
                write!(f, "&{}", Self::new(self.state, id))
            }
            TKind::Structure(_) if !ty.params.is_empty() => {
                let params = self.state.modules[ty.module].type_slice(ty.params);
                write!(f, "{}", Self::new(self.state, params[0]))?;
                write!(f, "[")?;
                write!(f, "{}", Self::new(self.state, params[1]))?;
                for param in params[2..].iter() {
                    write!(f, ", {}", Self::new(self.state, *param))?;
                }
                write!(f, "]")
            }
            TKind::Builtin(_) | 
            TKind::Unresolved(_) | 
            TKind::Generic(_) | 
            TKind::Structure(_) | 
            TKind::Enumeration(_) => {
                write!(f, "{}", self.state.display(&ty.name))
            }
            TKind::Constant(value) => {
                write!(f, "{}", TypeConstDisplay::new(self.state, value))
            }
            TKind::Array(id, len) => {
                write!(f, "[{}, {}]", Self::new(self.state, *id), len)
            }
            TKind::FunPointer(fun) => {
                write!(
                    f,
                    "fn({})",
                    self.state.modules[ty.module]
                        .type_slice(fun.args)
                        .iter()
                        .map(|id| format!("{}", Self::new(self.state, *id)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if fun.ret.is_some() {
                    write!(f, " -> {}", Self::new(self.state, fun.ret.unwrap()))?;
                }
                Ok(())
            }
        }
    }
}

crate::def_displayer!(
    TErrorDisplay,
    TState,
    TError,
    |self, f| {
        TEKind::VisibilityViolation => {
            write!(f, "visibility of the type disallows the access, {}", VISIBILITY_MESSAGE)?;
        },
        TEKind::InstancingNonGeneric(origin) => {
            writeln!(
                f,
                "instancing non-generic type, defined here:\n {}",
                TokenDisplay::new(&self.state, origin)
            )?;
        },
        TEKind::AError(error) => {
            writeln!(f, "{}", AErrorDisplay::new(self.state, error))?;
        },
        TEKind::UnexpectedAst(token) => {
            writeln!(f, "{}", token)?;
        },
        &TEKind::AmbiguousType(a, b) => {
            let a = self.state.types[a].hint.clone();
            let b = self.state.types[b].hint.clone();
            writeln!(
                f,
                "matches\n{}\nand\n{}\nambiguity is not allowed",
                TokenDisplay::new(&self.state, &a),
                TokenDisplay::new(&self.state, &b)
            )?;
        },
        TEKind::UnknownType => {
            writeln!(f, "type not defined in current scope")?;
        },
        TEKind::NotGeneric => {
            writeln!(f, "type is not generic thus cannot be instantiated")?;
        },
        TEKind::UnknownModule => {
            writeln!(f, "module not defined in current scope")?;
        },
        TEKind::InstantiationDepthExceeded => {
            writeln!(
                f,
                "instantiation depth exceeded, max is {}",
                TParser::MAX_TYPE_INSTANTIATION_DEPTH
            )?;
        },
        TEKind::WrongInstantiationArgAmount(actual, expected) => {
            writeln!(
                f,
                "wrong amount of arguments for type instantiation, expected {} but got {}",
                expected, actual
            )?;
        },
        TEKind::AccessingExternalPrivateType => {todo!()},
        TEKind::AccessingFilePrivateType =>  {todo!()},
        TEKind::InfiniteSize(cycle) => {
            writeln!(f, "infinite size detected, cycle:")?;
            for ty in cycle.iter() {
                writeln!(f, "  {}", TypeDisplay::new(self.state, *ty))?;
            }
        },
        TEKind::Redefinition(other) => {
            writeln!(f, "is redefinition of\n{}", TokenDisplay::new(&self.state, other))?;
        },

        TEKind::ExpectedIntConstant => {
            writeln!(f, "expected positive integer constant")?;
        },
        TEKind::InvalidCallConv => {
            call_conv_error(f)?;
        },
    }
);

#[derive(Debug)]
pub struct TError {
    pub kind: TEKind,
    pub token: Token,
}

impl TError {
    pub fn new(kind: TEKind, token: Token) -> Self {
        Self { kind, token }
    }
}

#[derive(Debug)]
pub enum TEKind {
    InvalidCallConv,
    VisibilityViolation,
    InstancingNonGeneric(Token),
    AError(AError),
    UnexpectedAst(String),
    AmbiguousType(Ty, Ty),
    UnknownType,
    NotGeneric,
    UnknownModule,
    InstantiationDepthExceeded,
    WrongInstantiationArgAmount(usize, usize),
    AccessingExternalPrivateType,
    AccessingFilePrivateType,
    InfiniteSize(Vec<Ty>),
    Redefinition(Token),
    ExpectedIntConstant,
}

pub fn call_conv_error(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(
        f,
        "Invalid call convention, list of valid call conventions:"
    )?;
    for cc in [
        "platform - picks call convention based of target platform",
        "fast",
        "cold",
        "system_v",
        "windows_fastcall",
        "apple_aarch64",
        "baldrdash_system_v",
        "baldrdash_windows",
        "baldrdash_2020",
        "probestack",
        "wasmtime_system_v",
        "wasmtime_fastcall",
        "wasmtime_apple_aarch64",
    ] {
        writeln!(f, "  {}", cc)?;
    }
    Ok(())
}

pub fn test() {
    const PATH: &str = "src/types/test_project";

    let (mut state, hint) = incr::load_data::<TState>(PATH, ID(0)).unwrap_or_default();
    let mut context = TContext::default();

    MTParser::new(&mut state, &mut context)
        .parse(PATH)
        .map_err(|e| panic!("{}", MTErrorDisplay::new(&state, &e)))
        .unwrap();

    for module in std::mem::take(&mut state.module_order).drain(..) {
        if state.modules[module].clean {
            continue;
        }

        TParser::new(&mut state, &mut context)
            .parse(module)
            .map_err(|e| panic!("\n{}", TErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }

    for module in state.modules.iter_mut() {
        module.clean = true;
    }

    incr::save_data(PATH, &state, ID(0), Some(hint)).unwrap();
}
