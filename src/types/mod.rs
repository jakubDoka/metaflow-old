use std::ops::{Deref, DerefMut};

use crate::ast::{AError, AErrorDisplay, AKind, AParser, AstEnt, Vis};
use crate::entities::{Ast, Mod, Ty};
use crate::lexer::{Span, TKind as LTKind, Token, TokenDisplay};
use crate::module_tree::{MTContext, MTParser, MTState, TreeStorage};
use crate::util::sdbm::ID;
use crate::util::storage::Table;
use crate::util::Size;
use cranelift::codegen::ir::types::Type;
use cranelift::codegen::ir::Signature as CrSignature;
use cranelift::codegen::ir::{types::*, AbiParam, ArgumentPurpose};
use cranelift::codegen::isa::CallConv as CrCallConv;
use cranelift::codegen::isa::TargetIsa;
use cranelift::entity::{packed_option::ReservedValue, EntityRef};
use cranelift::entity::{EntityList, ListPool};
use quick_proc::{QuickDefault, QuickEnumGets, QuickSer, RealQuickSer};

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
        let result = self.resolve_type(module, ast, 0)?;

        self.connect()?;
        self.calc_sizes()?;
        Ok(result)
    }

    fn calc_sizes(&mut self) -> Result {
        let mut lookup = std::mem::take(&mut self.state.type_cycle_map);
        let mut resolved = std::mem::take(&mut self.context.resolved);
        let mut ordering = self.context.pool.get();
        let mut cycle_stack = self.context.pool.get();
        lookup.resize(self.state.types.len(), (false, false));

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
        self.state.type_cycle_map = lookup;

        Ok(())
    }

    fn calc_size(&mut self, ty: Ty) -> Result {
        let ty_ent = &mut self.state.types[ty];
        match &mut ty_ent.kind {
            TKind::Structure(stype) => {
                let mut size = Size::ZERO;
                let mut fields = std::mem::take(&mut stype.fields);
                let kind = stype.kind;
                let align = fields
                    .iter()
                    .map(|field| self.state.types[field.ty].align)
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
                                size = size.add(self.state.types[field.ty].size);
                            }

                            size = size.add(calc(size));
                        }
                        SKind::Union => {
                            size = fields
                                .iter()
                                .map(|field| self.state.types[field.ty].size)
                                .max()
                                .unwrap();
                        }
                    }
                }

                self.state.types[ty].kind.structure_mut().fields = fields;

                let ty_ent = &mut self.state.types[ty];
                ty_ent.align = align;
                ty_ent.size = size;
            }
            &mut TKind::Array(element, size) => {
                let element_size = self.state.types[element].size;
                self.state.types[ty].size = Size::new(size, size).mul(element_size);
            }
            TKind::Pointer(..) | TKind::Builtin(..) | TKind::FunPointer(..) => (),
            _ => unreachable!("{:?}", ty_ent.kind),
        }

        Ok(())
    }

    fn connect(&mut self) -> Result {
        while let Some((id, depth)) = self.context.unresolved.pop() {
            if depth > Self::MAX_TYPE_INSTANTIATION_DEPTH {
                return Err(TError::new(
                    TEKind::InstantiationDepthExceeded,
                    self.state.types[id].hint.clone(),
                ));
            }

            let ty = &self.state.types[id];
            let ty_module = ty.module;

            match &ty.kind {
                &TKind::Unresolved(ast) => self.connect_type(ty_module, id, ast, depth)?,
                _ => unreachable!("{:?}", &self.state.types[id].kind),
            }

            self.context.resolved.push(id);
        }
        Ok(())
    }

    fn connect_type(&mut self, module: Mod, id: Ty, ast: Ast, depth: usize) -> Result {
        match self.state.modules[module].kind(ast) {
            AKind::StructDeclaration(_) => {
                self.connect_structure(module, id, ast, SKind::Struct, depth)?;
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
        let params_len = params.len(&self.state.type_slices);
        let mut shadowed = self.context.pool.get();

        let header = module_ent.son(ast, 0);
        let header_ent = module_ent.load(header);
        let header_len = module_ent.len(header_ent.sons);

        let is_instance = header_ent.kind == AKind::Instantiation;

        if is_instance {
            if params_len != header_len {
                return Err(TError::new(
                    TEKind::WrongInstantiationArgAmount(
                        params_len - 1,
                        header_len - 1,
                    ),
                    self.state.types[id].hint.clone(),
                ));
            }
            for (i, &param) in (1..header_len).zip(params.as_slice(&self.state.type_slices)[1..].iter())
            {
                let module_ent = &self.state.modules[module];
                let hash = module_ent.son_ent(header, i).token.span.hash;
                let id = TYPE_SALT.add(hash).add(module_id);

                let sha = self.state.types.link(id, param);
                shadowed.push((id, sha));
            }
        }

        self.state.types[id].params = params;

        let module_ent = &self.state.modules[module];
        let body = module_ent.son(ast, 1);
        if body != Ast::reserved_value() {
            let body = *module_ent.load(body);
            let len = module_ent.len(body.sons);
            for i in 0..len {
                let module_ent = &self.state.modules[module];
                let &AstEnt { sons, kind, token } = module_ent.get_ent(body.sons, i);
                let field_line_len = module_ent.len(sons);
                let type_ast = module_ent.get(sons, field_line_len - 1);
                let (vis, embedded) = match &kind {
                    &AKind::StructField(vis, embedded) => (vis, embedded),
                    _ => unreachable!("{:?}", kind),
                };
                let (_, ty) = self.resolve_type(module, type_ast, depth)?;
                let hint = token;
                let module_ent = &self.state.modules[module];
                let field_ids = self.state.modules[module].slice(sons);
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
            self.state.types.remove_link(id, ty);
        }

        let s_ent = SType {
            kind,
            fields: fields.clone(),
        };

        self.state.types[id].kind = TKind::Structure(s_ent);

        Ok(())
    }

    fn resolve_type(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.state.modules[module];
        let &AstEnt { kind, token, sons } = module_ent.a_state.load(ast);
        let (ty_module, ty) = match kind {
            AKind::Ident => self.resolve_simple_type(module, None, ast, &token),
            AKind::Path => {
                let module_name = module_ent.get(sons, 0);
                let name = module_ent.get(sons, 1);
                self.resolve_simple_type(module, Some(module_name), name, &token)
            }
            AKind::Instantiation => self.resolve_instance(module, ast, depth),
            AKind::Ref => self.resolve_pointer(module, ast, depth),
            AKind::Array => self.resolve_array(module, ast, depth),
            AKind::Lit => self.resolve_constant(module, &token),
            AKind::FunHeader(..) => self.resolve_function_pointer(module, ast, depth),
            _ => unreachable!("{:?}", kind),
        }?;

        if !self
            .state
            .can_access(module, ty_module, self.state.types[ty].vis)
        {
            return Err(TError::new(TEKind::VisibilityViolation, token));
        }

        Ok((module, ty))
    }

    fn resolve_function_pointer(
        &mut self,
        module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<(Mod, Ty)> {
        let module_ent = &self.state.modules[module];
        let sons = module_ent.sons(ast);
        let len = module_ent.len(sons);

        let mut args = EntityList::new();
        for i in 1..len - 2 {
            let arg = self.state.modules[module].get(sons, i);
            let (_, ty) = self.resolve_type(module, arg, depth)?;
            args.push(ty, &mut self.state.type_slices);
        }

        let module_ent = &self.state.modules[module];
        let ret = module_ent.get(sons, len - 2);
        let ret = if ret != Ast::reserved_value() {
            let (_, ty) = self.resolve_type(module, ret, depth)?;
            Some(ty)
        } else {
            None
        };

        let module_ent = &self.state.modules[module];
        let call_conv = module_ent.get(sons, len - 1);
        let call_conv = if call_conv != Ast::reserved_value() {
            let token = module_ent.token(call_conv);
            let str = self.state.display(&token.span);
            CallConv::from_str(str).ok_or_else(|| TError::new(TEKind::InvalidCallConv, *token))?
        } else {
            CallConv::Fast
        };

        let sig = Signature {
            args: args.clone(),
            ret,
            call_conv,
        };

        let id = self.state.function_type_of(module, sig);

        Ok((module, id))
    }

    fn resolve_array(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let module_ent = &self.state.modules[module];
        let element = module_ent.son(ast, 0);
        let length_ast = module_ent.son(ast, 1);

        let (_, element) = self.resolve_type(module, element, depth)?;
        let (_, length) = self.resolve_type(module, length_ast, depth)?;
        let length = match self.state.types[length].kind {
            TKind::Constant(TypeConst::Int(i)) => i,
            _ => {
                return Err(TError::new(
                    TEKind::ExpectedIntConstant,
                    *self.state.modules[module].token(length_ast),
                ))
            }
        };

        Ok((module, self.state.array_of(element, length as usize)))
    }

    fn resolve_constant(&mut self, module: Mod, token: &Token) -> Result<(Mod, Ty)> {
        let constant = match token.kind.clone() {
            LTKind::Int(val, _) => TypeConst::Int(val),
            LTKind::Uint(val, _) => TypeConst::Int(val as i64),
            LTKind::Float(val, _) => TypeConst::Float(val),
            LTKind::Bool(val) => TypeConst::Bool(val),
            LTKind::Char(val) => TypeConst::Char(val),
            LTKind::String(val) => TypeConst::String(val),
            _ => unreachable!("{:?}", token.kind),
        };

        let ty = self.state.constant_of(constant);

        Ok((module, ty))
    }

    fn resolve_pointer(&mut self, module: Mod, ast: Ast, depth: usize) -> Result<(Mod, Ty)> {
        let (module, datatype) =
            self.resolve_type(module, self.state.modules[module].son(ast, 0), depth)?;
        let datatype = self.state.pointer_of(datatype);

        Ok((module, datatype))
    }

    fn resolve_instance(
        &mut self,
        source_module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<(Mod, Ty)> {
        let module_ent = &self.state.modules[source_module];
        let ident = module_ent.son(ast, 0);
        let &AstEnt { token, sons, kind } = module_ent.load(ident);
        let (module, ty) = match kind {
            AKind::Ident => self.resolve_simple_type(source_module, None, ident, &token)?,
            AKind::Path => {
                let module_name = module_ent.get(sons, 0);
                let name = module_ent.get(sons, 1);
                self.resolve_simple_type(source_module, Some(module_name), name, &token)?
            }
            _ => unreachable!("{:?}", kind),
        };

        let mut params = EntityList::new();
        let module_ent = &self.state.modules[source_module];
        let module_id = module_ent.id;
        let sons = module_ent.sons(ast);
        let ast_len = module_ent.len(sons);

        self.state.push(&mut params, ty);

        let mut id = TYPE_SALT.add(self.state.types[ty].id);
        for i in 1..ast_len {
            let ty = self.state.modules[source_module].get(sons, i);
            let ty = self.resolve_type(source_module, ty, depth)?.1;
            id = id.add(self.state.types[ty].id);
            self.state.push(&mut params, ty);
        }
        id = id.add(module_id);

        if let Some(id) = self.type_index(id) {
            self.state.clear(&mut params);
            return Ok((module, id));
        }

        let ty_ent = &self.state.types[ty];

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

        let ty = self.state.add_type(type_ent);

        self.context.unresolved.push((ty, depth));

        Ok((module, ty))
    }

    fn resolve_simple_type(
        &mut self,
        module: Mod,
        target: Option<Ast>,
        name: Ast,
        token: &Token,
    ) -> Result<(Mod, Ty)> {
        let module_ent = &self.state.modules[module];
        let id = TYPE_SALT.add(module_ent.token(name).span.hash);

        let target = if let Some(target) = target {
            let token = module_ent.token(target);
            Some(
                self.state
                    .find_dep(module, token)
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
        let module_ent = &self.state.modules[module];
        let module_name = module_ent.id;
        let types = module_ent.types();

        for i in (0..types.len()).step_by(2) {
            let module_ent = &self.state.modules[module];
            let types = module_ent.types();
            let type_ast = types[i];
            let attrs = types[i + 1];
            let &AstEnt { token, kind, sons } = module_ent.load(type_ast);
            match kind {
                AKind::StructDeclaration(vis) => {
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

                    let (replaced, id) = self.state.types.insert(id, datatype);
                    if let Some(other) = replaced {
                        return Err(TError::new(TEKind::Redefinition(other.hint), token));
                    }

                    let mut types = self.state.modules[module].types;
                    types.push(id, &mut self.state.type_slices);
                    self.state.modules[module].types = types;

                    if let TKind::Unresolved(_) = &self.state.types[id].kind {
                        self.context.unresolved.push((id, 0));
                    }
                }
                kind => unreachable!("{:?}", kind),
            }
        }

        Ok(())
    }

    fn type_index(&self, id: ID) -> Option<Ty> {
        self.state.types.index(id).cloned()
    }
}

impl<'a> ItemSearch<Ty> for TParser<'a> {
    fn find(&self, id: ID) -> Option<Ty> {
        self.state.types.index(id).cloned()
    }

    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        self.state.collect_scopes(module, buffer)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.state.modules[module].id
    }
}

impl<'a> TreeStorage<Ty> for TParser<'a> {
    fn node_dep(&self, id: Ty, idx: usize) -> Ty {
        let node = &self.state.types[id];
        match &node.kind {
            TKind::Structure(stype) => stype.fields[idx].ty,
            TKind::Array(ty, _) => *ty,
            TKind::FunPointer(fun) => {
                if idx == fun.args.len(&self.state.type_slices) {
                    fun.ret.unwrap()
                } else {
                    fun.args.get(idx, &self.state.type_slices).unwrap()
                }
            }
            _ => unreachable!("{:?}", node.kind),
        }
    }

    fn node_len(&self, id: Ty) -> usize {
        let node = &self.state.types[id];

        match &node.kind {
            TKind::Builtin(_) | TKind::Pointer(..) => 0,
            TKind::FunPointer(fun) => fun.args.len(&self.state.type_slices) + fun.ret.is_some() as usize,
            TKind::Array(..) => 1,
            TKind::Structure(stype) => stype.fields.len(),
            TKind::Generic(_) | TKind::Unresolved(_) | TKind::Constant(_) => 
                unreachable!("{:?}", node),
        }
    }

    fn len(&self) -> usize {
        self.state.types.len()
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

#[derive(Debug, Clone, QuickSer, QuickDefault)]
pub struct TypeEnt {
    pub id: ID,
    #[default(Mod::reserved_value())]
    pub module: Mod,
    pub vis: Vis,
    pub params: EntityList<Ty>,
    pub kind: TKind,
    pub name: Span,
    pub hint: Token,
    #[default(Ast::reserved_value())]
    pub attrs: Ast,
    pub size: Size,
    pub align: Size,
}

impl TypeEnt {
    pub fn to_cr_type(&self, isa: &dyn TargetIsa) -> Type {
        match &self.kind {
            TKind::Pointer(_) | TKind::Array(_, _) | TKind::FunPointer(_) | TKind::Structure(_) => {
                isa.pointer_type()
            }
            &TKind::Builtin(ty) => ty.0,
            TKind::Generic(_) | TKind::Constant(_) | TKind::Unresolved(_) => unreachable!(),
        }
    }

    pub fn on_stack(&self, ptr_ty: Type) -> bool {
        self.size.pick(ptr_ty == I32) > ptr_ty.bytes() as u32
    }
}

#[derive(Debug, Clone, QuickEnumGets, QuickSer)]
pub enum TKind {
    Builtin(CrTypeWr),
    Pointer(Ty),
    Array(Ty, u32),
    FunPointer(Signature),
    Constant(TypeConst),
    Structure(SType),
    Generic(Ast),
    Unresolved(Ast),
}

crate::impl_wrapper!(CrTypeWr, Type);

impl Default for TKind {
    fn default() -> Self {
        TKind::Builtin(CrTypeWr(INVALID))
    }
}

#[derive(Debug, Clone, Default, QuickSer)]
pub struct Signature {
    pub call_conv: CallConv,
    pub args: EntityList<Ty>,
    pub ret: Option<Ty>,
}

impl Signature {
    pub fn to_cr_signature(&self, state: &TState, isa: &dyn TargetIsa, target: &mut CrSignature) {
        target.call_conv = self.call_conv.to_cr_call_conv(isa);
        target.params.extend(
            self.args.as_slice(&state.type_slices)
                .iter()
                .map(|&ty| AbiParam::new(state.types[ty].to_cr_type(isa))),
        );
        if let Some(ret) = self.ret {
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

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub enum TypeConst {
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),
    String(Span),
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

#[derive(Debug, Clone, QuickSer)]
pub struct SType {
    pub kind: SKind,
    pub fields: Vec<SField>,
}

#[derive(Debug, Clone, Copy, RealQuickSer)]
pub struct SField {
    pub embedded: bool,
    pub vis: Vis,
    pub id: ID,
    pub offset: Size,
    pub ty: Ty,
    pub hint: Token,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum SKind {
    Struct,
    Union,
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
    pub type_slices: ListPool<Ty>,
    pub type_cycle_map: Vec<(bool, bool)>,
    pub mt_state: MTState,
}

impl TState {
    pub fn push(&mut self, list: &mut EntityList<Ty>, value: Ty) {
        list.push(value, &mut self.type_slices);
    }

    pub fn param(&self, ty: Ty, index: usize) -> Ty {
        self.types[ty].params.get(index, &self.type_slices).unwrap()
    }

    pub fn params(&self, ty: Ty) -> &[Ty] {
        self.types[ty].params.as_slice(&self.type_slices)
    }

    fn clear(&mut self, params: &mut EntityList<Ty>) {
        params.clear(&mut self.type_slices);
    }

    pub fn pointer_of(&mut self, ty: Ty) -> Ty {
        let module = self.types[ty].module;
        let name = "&";
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
            kind: TKind::Pointer(ty),
            module,
            size,
            align: size,

            ..Default::default()
        };

        self.add_type(pointer_type)
    }

    pub fn array_of(&mut self, element: Ty, length: usize) -> Ty {
        let element_id = self.types[element].id;

        let id = TYPE_SALT
            .add(ID::new("[]"))
            .add(element_id)
            .add(ID(length as u64));

        if let Some(&index) = self.types.index(id) {
            return index;
        }

        let ty_ent = TypeEnt {
            id,
            vis: Vis::Public,
            module: Mod::new(0),
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

        for arg in sig.args.as_slice(&self.type_slices).iter() {
            id = id.add(self.types[*arg].id);
        }

        if let Some(ret) = sig.ret {
            id = id.add(ID::new("->")).add(self.types[ret].id);
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
        let module = ent.module;
        let (shadow, ty) = self.types.insert(ent.id, ent);
        let mut types = self.modules[module].types;
        types.push(ty, &mut self.type_slices);
        self.modules[module].types = types;
        debug_assert!(shadow.is_none());
        ty
    }

    pub fn remove_type(&mut self, ty: Ty) {
        let mut type_ent = std::mem::take(&mut self.types[ty]);
        type_ent.params.clear(&mut self.type_slices);
        match type_ent.kind {
            TKind::Builtin(_) |
            TKind::Pointer(_) |
            TKind::Constant(_) |
            TKind::Structure(_) |
            TKind::Generic(_) |
            TKind::Unresolved(_) |
            TKind::Array(_, _) => (),
            TKind::FunPointer(mut sig) => {
                sig.args.clear(&mut self.type_slices);
            },
        }
    }
}

crate::inherit!(TState, mt_state, MTState);

impl Default for TState {
    fn default() -> Self {
        let mut s = Self {
            builtin_repo: Default::default(),
            types: Table::new(),
            mt_state: MTState::default(),
            type_slices: ListPool::new(),
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
                let module = state.builtin_module;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum CallConv {
    Fast,
    Cold,
    SystemV,
    WindowsFastcall,
    AppleAarch64,
    BaldrdashSystemV,
    BaldrdashWindows,
    Baldrdash2020,
    Probestack,
    WasmtimeSystemV,
    WasmtimeFastcall,
    WasmtimeAppleAarch64,
    Platform,
}

impl CallConv {
    pub fn from_str(s: &str) -> Option<Self> {
        Some(match s {
            "fast" => Self::Fast,
            "cold" => Self::Cold,
            "system_v" => Self::SystemV,
            "windows_fastcall" => Self::WindowsFastcall,
            "apple_aarch64" => Self::AppleAarch64,
            "baldrdash_system_v" => Self::BaldrdashSystemV,
            "baldrdash_windows" => Self::BaldrdashWindows,
            "baldrdash_2020" => Self::Baldrdash2020,
            "probestack" => Self::Probestack,
            "wasmtime_system_v" => Self::WasmtimeSystemV,
            "wasmtime_fastcall" => Self::WasmtimeFastcall,
            "wasmtime_apple_aarch64" => Self::WasmtimeAppleAarch64,
            "platform" => Self::Platform,
            _ => return None,
        })
    }

    pub fn to_cr_call_conv(&self, isa: &dyn TargetIsa) -> CrCallConv {
        match self {
            Self::Platform => isa.default_call_conv(),
            _ => unsafe { std::mem::transmute(*self) },
        }
    }
}

impl Default for CallConv {
    fn default() -> Self {
        Self::Fast
    }
}

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
            TKind::Pointer(id, ..) => {
                write!(f, "&{}", Self::new(self.state, *id))
            }
            TKind::Structure(_) if !ty.params.is_empty() => {
                let params = self.state.params(self.type_id);
                write!(f, "{}", Self::new(self.state, params[0]))?;
                write!(f, "[")?;
                write!(f, "{}", Self::new(self.state, params[1]))?;
                for param in params[2..].iter() {
                    write!(f, ", {}", Self::new(self.state, *param))?;
                }
                write!(f, "]")
            }
            TKind::Builtin(_) | TKind::Unresolved(_) | TKind::Generic(_) | TKind::Structure(_) => {
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
                    fun.args.as_slice(&self.state.type_slices)
                        .iter()
                        .map(|id| format!("{}", Self::new(self.state, *id)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if let Some(ret) = fun.ret {
                    write!(f, " -> {}", Self::new(self.state, ret))?;
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
    let mut state = TState::default();
    let mut context = TContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/types/test_project")
        .unwrap();

    for module in std::mem::take(&mut state.module_order).drain(..) {
        let mut a_state = std::mem::take(&mut state.modules[module].a_state);

        AParser::new(&mut state.a_main_state, &mut a_state, &mut context)
            .parse()
            .map_err(|err| panic!("\n{}", AErrorDisplay::new(&state, &err)))
            .unwrap();

        state.modules[module].a_state = a_state;

        TParser::new(&mut state, &mut context)
            .parse(module)
            .map_err(|e| panic!("\n{}", TErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }
}
