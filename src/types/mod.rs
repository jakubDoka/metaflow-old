use std::fmt::Write;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use crate::ast::{AError, AErrorDisplay, AKind, AParser, Ast, Vis};
use crate::collector::{Attrs, Collector, Item};
use crate::lexer::{Span, TKind as LTKind, Token, TokenDisplay};
use crate::module_tree::{self, MTContext, MTParser, MTState, Mod, TreeStorage};
use crate::util::sdbm::ID;
use crate::util::storage::{IndexPointer, List, ReusableList, Table};
use cranelift_codegen::ir::types::{Type as CrType, INVALID};
use cranelift_codegen::ir::{types::*, AbiParam, ArgumentPurpose, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_module::Module;
use cranelift_object::{ObjectBuilder, ObjectModule};

type Result<T = ()> = std::result::Result<T, TError>;

pub const TYPE_SALT: ID = ID(0x9e3779b97f4a7c15);

pub const VISIBILITY_MESSAGE: &str =
"removing 'priv' in case of different module but same package or adding 'pub' in case of different package can help";

pub static mut POINTER_TYPE: CrType = INVALID;

pub fn ptr_ty() -> CrType {
    unsafe { POINTER_TYPE }
}

pub struct TParser<'a> {
    module: Mod,
    program: &'a mut Program,
    state: &'a mut TState,
    context: &'a mut TContext,
    collector: &'a mut Collector,
}

impl<'a> TParser<'a> {
    pub const MAX_TYPE_INSTANTIATION_DEPTH: usize = 1000;

    pub fn new(
        program: &'a mut Program,
        state: &'a mut TState,
        context: &'a mut TContext,
        collector: &'a mut Collector,
    ) -> Self {
        Self {
            module: Mod::new(0),
            program,
            state,
            context,
            collector,
        }
    }

    pub fn parse(&mut self, module: Mod) -> Result {
        self.module = module;
        self.collect(module)?;
        self.connect()?;
        self.calc_sizes()?;
        Ok(())
    }

    pub fn parse_type(&mut self, module: Mod, ast: &Ast) -> Result<(Mod, Type)> {
        self.module = module;
        let result = self.resolve_type(module, ast, 0)?;

        self.connect()?;
        self.calc_sizes()?;
        Ok(result)
    }

    fn calc_sizes(&mut self) -> Result {
        let mut resolved = std::mem::take(&mut self.state.resolved);
        for ty in resolved.drain(..) {
            if self.node_len(ty) != 0 {
                self.calc_size(ty)?;
            }
        }
        self.state.resolved = resolved;
        Ok(())
    }

    fn calc_size(&mut self, ty: Type) -> Result {
        let mut cycle_stack = self.context.pool.get();

        if let Some(cycle) = module_tree::detect_cycles(self, ty, &mut cycle_stack) {
            return Err(TError::new(TEKind::InfiniteSize(cycle), Token::default()));
        }

        let mut pool = std::mem::take(&mut self.context.pool);

        let order = module_tree::create_order(self, ty, &mut pool);

        self.context.pool = pool;

        for &ty in order.iter().rev() {
            let ty_ent = &self.state.types[ty];

            match ty_ent.kind {
                TKind::Structure(id) => {
                    let mut size = 0;
                    let structure = &mut self.state.stypes[id];
                    let mut fields = std::mem::take(&mut structure.fields);
                    let kind = structure.kind;
                    let align = fields
                        .iter()
                        .map(|field| self.state.types[field.ty].align)
                        .max()
                        .unwrap_or(0);

                    if align != 0 {
                        match kind {
                            SKind::Struct => {
                                let calc = move |offset| {
                                    align * ((offset & (align - 1)) != 0) as u32
                                        - (offset & (align - 1))
                                };

                                for field in &mut fields {
                                    size += calc(size);
                                    field.offset = size;
                                    size += self.state.types[field.ty].size;
                                }

                                size += calc(size);
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

                    self.state.stypes[id].fields = fields;

                    let ty_ent = &mut self.state.types[ty];
                    ty_ent.align = align;
                    ty_ent.size = size;
                }
                TKind::Array(element, size) => {
                    self.state.types[ty].size = size * self.state.types[element].size;
                }
                TKind::Pointer(..) | TKind::Builtin(..) | TKind::FunPointer(..) => (),
                _ => unreachable!("{:?}", ty_ent.kind),
            }
        }

        Ok(())
    }

    fn connect(&mut self) -> Result {
        while let Some((id, depth)) = self.state.unresolved.pop() {
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

            self.state.resolved.push(id);
        }

        Ok(())
    }

    fn connect_type(&mut self, module: Mod, id: Type, ast: GAst, depth: usize) -> Result {
        match self.state.asts[ast].kind {
            AKind::StructDeclaration(_) => {
                self.connect_structure(module, id, ast, SKind::Struct, depth)?;
            }
            _ => unreachable!("{:?}", self.state.asts[ast].kind),
        }

        Ok(())
    }

    fn connect_structure(
        &mut self,
        module: Mod,
        id: Type,
        ast_id: GAst,
        kind: SKind,
        depth: usize,
    ) -> Result<SType> {
        let mut fields = std::mem::take(&mut self.context.struct_field_buffer);

        // SAFETY: we can take a reference as we know that
        // nothing will mutate 'gtypes' since all types are collected
        let ast = std::mem::take(&mut self.state.asts[ast_id]);

        let module_id = self.state.modules[module].id;
        let params = std::mem::take(&mut self.state.types[id].params);
        let mut shadowed = self.context.pool.get();

        let header = &ast[0];

        let is_instance = header.kind == AKind::Instantiation;

        if is_instance {
            if params.len() != header.len() {
                return Err(TError::new(
                    TEKind::WrongInstantiationArgAmount(params.len() - 1, header.len() - 1),
                    self.state.types[id].hint.clone(),
                ));
            }
            for (a, &param) in header[1..].iter().zip(params[1..].iter()) {
                let id = TYPE_SALT
                    .add(ID::new(self.state.display(&a.token.span)))
                    .add(module_id);

                let sha = self.state.types.link(id, param);
                shadowed.push((id, sha));
            }
        }

        self.state.types[id].params = params;

        for field_line in ast[1].iter() {
            let (vis, embedded) = match &field_line.kind {
                &AKind::StructField(vis, embedded) => (vis, embedded),
                _ => unreachable!("{:?}", field_line.kind),
            };
            let type_ast = &field_line[field_line.len() - 1];
            let (_, ty) = self.resolve_type(module, type_ast, depth)?;
            let hint = field_line.token.clone();

            for field in field_line[..field_line.len() - 1].iter() {
                let id = field.token.span.hash;
                let field = SField {
                    embedded,
                    vis,
                    id,
                    offset: 0,
                    ty,
                    hint: hint.clone(),
                };

                fields.push(field);
            }
        }

        // we ruse ast since this is not a generic type
        if !is_instance {
            self.state.asts.remove(ast_id);
            self.context.recycle(ast);
        } else {
            self.state.asts[ast_id] = ast;
        }

        for (id, ty) in shadowed.drain(..) {
            self.state.types.remove_link(id, ty);
        }

        let s_ent = STypeEnt {
            kind,
            fields: fields.clone(),
        };
        let s_id = self.state.stypes.add(s_ent);

        self.state.types[id].kind = TKind::Structure(s_id);

        fields.clear();
        self.context.struct_field_buffer = fields;

        Ok(s_id)
    }

    fn resolve_type(&mut self, module: Mod, ast: &Ast, depth: usize) -> Result<(Mod, Type)> {
        let (ty_module, ty) = match ast.kind {
            AKind::Ident => self.resolve_simple_type(module, None, &ast.token),
            AKind::Path => self.resolve_simple_type(module, Some(&ast[0].token), &ast.token),
            AKind::Instantiation => self.resolve_instance(module, ast, depth),
            AKind::Ref => self.resolve_pointer(module, ast, depth),
            AKind::Array => self.resolve_array(module, ast, depth),
            AKind::Lit => self.resolve_constant(module, &ast.token),
            AKind::FunHeader(..) => self.resolve_function_pointer(module, ast, depth),
            _ => unreachable!("{:?}", ast.kind),
        }?;

        if !self
            .state
            .can_access(module, ty_module, self.state.types[ty].vis)
        {
            return Err(TError::new(TEKind::VisibilityViolation, ast.token.clone()));
        }

        Ok((module, ty))
    }

    fn resolve_function_pointer(
        &mut self,
        module: Mod,
        ast: &Ast,
        depth: usize,
    ) -> Result<(Mod, Type)> {
        let mut args = self.context.pool.get();

        for arg in ast[1..ast.len() - 2].iter() {
            let (_, ty) = self.resolve_type(module, arg, depth)?;

            args.push(ty);
        }

        let ret = if ast[ast.len() - 2].kind != AKind::None {
            let (_, ty) = self.resolve_type(module, &ast[ast.len() - 2], depth)?;
            Some(ty)
        } else {
            None
        };

        let call_conv = if ast[ast.len() - 1].kind != AKind::None {
            let str = self.state.display(&ast[ast.len() - 1].token.span);
            self.program.parse_call_conv(str).ok_or_else(|| {
                TError::new(TEKind::InvalidCallConv, ast[ast.len() - 1].token.clone())
            })?
        } else {
            CallConv::Fast
        };

        let id = self.function_type_of(module, args.as_slice(), ret, call_conv);

        Ok((module, id))
    }

    fn resolve_array(&mut self, module: Mod, ast: &Ast, depth: usize) -> Result<(Mod, Type)> {
        let element = &ast[0];
        let length = &ast[1];

        let (_, element) = self.resolve_type(module, element, depth)?;
        let (_, length) = self.resolve_type(module, length, depth)?;
        let length = match self.state.types[length].kind {
            TKind::Const(TypeConst::Int(i)) => i,
            _ => {
                return Err(TError::new(
                    TEKind::ExpectedIntConstant,
                    ast[1].token.clone(),
                ))
            }
        };

        Ok((module, self.array_of(element, length as usize)))
    }

    fn resolve_constant(&mut self, module: Mod, token: &Token) -> Result<(Mod, Type)> {
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

    fn resolve_pointer(&mut self, module: Mod, ast: &Ast, depth: usize) -> Result<(Mod, Type)> {
        let (module, datatype) = self.resolve_type(module, &ast[0], depth)?;
        let datatype = self.pointer_of(datatype);

        Ok((module, datatype))
    }

    fn resolve_instance(
        &mut self,
        source_module: Mod,
        ast: &Ast,
        depth: usize,
    ) -> Result<(Mod, Type)> {
        let name = &ast[0];
        let (module, ty) = match name.kind {
            AKind::Ident => self.resolve_simple_type(source_module, None, &name.token)?,
            AKind::Path => {
                self.resolve_simple_type(source_module, Some(&name[0].token), &name[1].token)?
            }
            _ => unreachable!("{:?}", ast[0].kind),
        };

        let module_id = self.state.modules[module].id;

        let mut params = self.context.pool.get();
        params.clear();
        params.push(ty);

        for ty in ast[1..].iter() {
            params.push(self.resolve_type(source_module, ty, depth)?.1);
        }

        let mut id = TYPE_SALT;
        for &param in params.iter() {
            id = id.add(self.state.types[param].id);
        }
        id = id.add(module_id);

        if let Some(id) = self.type_index(id) {
            return Ok((module, id));
        }

        let ty_ent = &self.state.types[ty];

        let ast_id = match ty_ent.kind {
            TKind::Generic(ast) => ast,
            _ => {
                return Err(TError::new(
                    TEKind::InstancingNonGeneric(ty_ent.hint.clone()),
                    ast.token.clone(),
                ))
            }
        };

        let type_ent = TypeEnt {
            id,
            module,
            vis: ty_ent.vis,
            params: params.clone(),
            kind: TKind::Unresolved(ast_id),
            name: ty_ent.name.clone(),
            hint: ast.token.clone(),
            attrs: ty_ent.attrs.clone(),
            size: 0,
            align: 0,
        };

        let (shadowed, ty) = self.state.types.insert(id, type_ent);
        debug_assert!(shadowed.is_none());

        self.state.unresolved.push((ty, depth));

        Ok((module, ty))
    }

    fn resolve_simple_type(
        &mut self,
        module: Mod,
        target: Option<&Token>,
        name: &Token,
    ) -> Result<(Mod, Type)> {
        let id = TYPE_SALT.add(name.span.hash);

        let target = if let Some(target) = target {
            Some(
                self.state
                    .find_dep(module, target)
                    .ok_or(TError::new(TEKind::UnknownModule, target.clone()))?,
            )
        } else {
            None
        };

        let mut buffer = self.context.pool.get();
        self.find_item(module, id, target, &mut buffer)
            .map_err(|(a, b)| TError::new(TEKind::AmbiguousType(a, b), name.clone()))?
            .ok_or_else(|| TError::new(TEKind::UnknownType, name.clone()))
    }

    fn collect(&mut self, module: Mod) -> Result<()> {
        let module_name = self.state.modules[module].id;

        for Item { attrs, ast, .. } in self.collector.types.drain(..) {
            match ast.kind.clone() {
                AKind::StructDeclaration(visibility) => {
                    let ast_id = self.state.asts.add(ast);

                    let ast = &self.state.asts[ast_id];

                    let ident = &self.state.asts[ast_id][0];
                    let (ident, kind) = if ident.kind == AKind::Ident {
                        (ident, TKind::Unresolved(ast_id))
                    } else if ident.kind == AKind::Instantiation {
                        (&ident[0], TKind::Generic(ast_id))
                    } else {
                        return Err(TError::new(
                            TEKind::UnexpectedAst(String::from("expected struct identifier")),
                            ident.token.clone(),
                        ));
                    };

                    let hint = ast[0].token.clone();
                    let id = TYPE_SALT.add(ident.token.span.hash).add(module_name);
                    let datatype = TypeEnt {
                        vis: visibility,
                        id,
                        params: vec![],
                        module,
                        kind,
                        name: ident.token.span.clone(),
                        attrs,
                        hint: hint.clone(),
                        size: 0,
                        align: 0,
                    };

                    let (replaced, id) = self.state.types.insert(id, datatype);
                    if let Some(other) = replaced {
                        return Err(TError::new(TEKind::Redefinition(other.hint), hint.clone()));
                    }

                    if let TKind::Unresolved(_) = &self.state.types[id].kind {
                        self.state.unresolved.push((id, 0));
                    }
                }
                _ => unreachable!("{:?}", ast.kind),
            }
        }

        Ok(())
    }

    pub fn pointer_of(&mut self, ty: Type) -> Type {
        let module = self.state.types[ty].module;
        let name = "&";
        let id = TYPE_SALT
            .add(ID::new(name))
            .add(self.state.types[ty].id)
            .add(self.state.modules[module].id);

        if let Some(index) = self.type_index(id) {
            return index;
        }

        let size = ptr_ty().bytes() as u32;

        let pointer_type = TypeEnt {
            vis: Vis::Public,
            id,
            params: vec![],
            kind: TKind::Pointer(ty),
            name: Span::default(),
            hint: Token::default(),
            module,
            attrs: Attrs::default(),
            size,
            align: size,
        };

        let (_, ty) = self.state.types.insert(id, pointer_type);

        ty
    }

    pub fn array_of(&mut self, element: Type, length: usize) -> Type {
        let element_id = self.state.types[element].id;

        let id = TYPE_SALT
            .add(ID::new("[]"))
            .add(element_id)
            .add(ID(length as u64));

        if let Some(&index) = self.state.types.index(id) {
            return index;
        }

        let ty_ent = TypeEnt {
            id,
            vis: Vis::Public,
            kind: TKind::Array(element, length as u32),

            size: self.state.types[element].size * length as u32,
            align: self.state.types[element].align,

            ..Default::default()
        };

        let (shadow, ty_id) = self.state.types.insert(id, ty_ent);
        debug_assert!(shadow.is_none());

        ty_id
    }

    pub fn constant_of(&mut self, constant: TypeConst) -> Type {
        self.context.constant_buffer.clear();
        write!(
            self.context.constant_buffer,
            "{}",
            TypeConstDisplay::new(self.state, &constant)
        )
        .unwrap();

        let id = TYPE_SALT.add(ID::new(&self.context.constant_buffer));

        if let Some(&tp) = self.state.types.index(id) {
            return tp;
        }

        let ty_ent = TypeEnt {
            id,
            vis: Vis::Public,
            kind: TKind::Const(constant),

            ..Default::default()
        };

        let (shadow, ty) = self.state.types.insert(id, ty_ent);
        debug_assert!(shadow.is_none());

        ty
    }

    fn type_index(&self, id: ID) -> Option<Type> {
        self.state.types.index(id).cloned()
    }

    pub fn function_type_of(
        &mut self,
        module: Mod,
        args: &[Type],
        ret: Option<Type>,
        call_conv: CallConv,
    ) -> Type {
        let mut id = TYPE_SALT
            .add(ID::new("fun"))
            .add(ID(unsafe { std::mem::transmute::<_, u8>(call_conv) } as u64));

        for arg in args.iter() {
            id = id.add(self.state.types[*arg].id);
        }

        if let Some(ret) = ret {
            id = id.add(ID::new("->")).add(self.state.types[ret].id);
        }

        if let Some(&id) = self.state.types.index(id) {
            return id;
        }

        let fun = FunPointerEnt {
            call_conv,
            args: args.to_vec(),
            ret,
        };

        let fun = self.state.fun_pointers.add(fun);

        let size = ptr_ty().bytes() as u32;
        let type_ent = TypeEnt {
            kind: TKind::FunPointer(fun),
            params: vec![],
            hint: Token::default(),
            id,
            module,
            vis: Vis::None,
            name: Span::default(),
            attrs: Attrs::default(),
            size,
            align: size,
        };

        let (shadowed, id) = self.state.types.insert(id, type_ent);
        debug_assert!(shadowed.is_none());

        id
    }
}

impl<'a> ItemSearch<Type> for TParser<'a> {
    fn find(&self, id: ID) -> Option<Type> {
        self.state.types.index(id).cloned()
    }

    fn scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        self.state.collect_scopes(module, buffer)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.state.modules[module].id
    }
}

impl<'a> TreeStorage<Type> for TParser<'a> {
    fn node_dep(&self, id: Type, idx: usize) -> Type {
        let node = &self.state.types[id];
        match node.kind {
            TKind::Structure(id) => {
                let structure = &self.state.stypes[id];
                structure.fields[idx].ty
            }
            TKind::Array(ty, _) => ty,
            TKind::FunPointer(id) => {
                let fun = &self.state.fun_pointers[id];
                if idx == fun.args.len() {
                    fun.ret.unwrap()
                } else {
                    fun.args[idx]
                }
            }
            _ => unreachable!("{:?}", node.kind),
        }
    }

    fn node_len(&self, id: Type) -> usize {
        let node = &self.state.types[id];

        match node.kind {
            _ if node.module != self.module || node.size != 0 => 0,
            TKind::Builtin(_) | TKind::Pointer(..) => 0,
            TKind::FunPointer(id) => {
                let fun = &self.state.fun_pointers[id];
                fun.args.len() + fun.ret.is_some() as usize
            }
            TKind::Array(..) => 1,
            TKind::Structure(id) => self.state.stypes[id].fields.len(),
            TKind::Generic(_) | TKind::Unresolved(_) | TKind::Const(_) => unreachable!(),
        }
    }

    fn len(&self) -> usize {
        self.state.types.len()
    }
}

pub trait ItemSearch<T: IndexPointer> {
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

crate::index_pointer!(Type);

#[derive(Debug, Clone)]
pub struct TypeEnt {
    pub id: ID,
    pub module: Mod,
    pub vis: Vis,
    pub params: Vec<Type>,
    pub kind: TKind,
    pub name: Span,
    pub hint: Token,
    pub attrs: Attrs,
    pub size: u32,
    pub align: u32,
}

impl Default for TypeEnt {
    fn default() -> Self {
        Self {
            id: ID::new(""),
            module: Mod::new(0),
            vis: Vis::Public,
            params: vec![],
            kind: TKind::Unresolved(GAst::new(0)),
            name: Span::default(),
            hint: Token::default(),
            attrs: Attrs::default(),
            size: 0,
            align: 0,
        }
    }
}

impl TypeEnt {
    pub fn on_stack(&self) -> bool {
        self.size > ptr_ty().bytes() as u32
    }

    pub fn repr(&self) -> CrType {
        match self.kind {
            TKind::Builtin(ty) => ty,
            TKind::Structure(..)
            | TKind::Pointer(..)
            | TKind::FunPointer(..)
            | TKind::Array(..) => ptr_ty(),
            TKind::Generic(..) | TKind::Unresolved(..) | TKind::Const(..) => unreachable!(),
        }
    }

    pub fn base(&self) -> Option<Type> {
        if let TKind::Array(..) = self.kind {
            Some(Type::new(13))
        } else {
            self.params.first().cloned()
        }
    }
}

#[derive(Debug, Clone)]
pub enum TKind {
    Builtin(CrType),
    Pointer(Type),
    Array(Type, u32),
    FunPointer(FunPointer),
    Const(TypeConst),
    Structure(SType),
    Generic(GAst),
    Unresolved(GAst),
}

impl Default for TKind {
    fn default() -> Self {
        TKind::Builtin(ptr_ty())
    }
}

super::index_pointer!(FunPointer);

#[derive(Debug, Clone)]
pub struct FunPointerEnt {
    pub call_conv: CallConv,
    pub args: Vec<Type>,
    pub ret: Option<Type>,
}

#[derive(Debug, Clone)]
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

crate::index_pointer!(GAst);

crate::index_pointer!(SType);

#[derive(Debug, Clone)]
pub struct STypeEnt {
    pub kind: SKind,
    pub fields: Vec<SField>,
}

#[derive(Debug, Clone)]
pub struct SField {
    pub embedded: bool,
    pub vis: Vis,
    pub id: ID,
    pub offset: u32,
    pub ty: Type,
    pub hint: Token,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SKind {
    Struct,
    Union,
}

#[derive(Debug, Clone, Default)]
pub struct TContext {
    pub mt_context: MTContext,
    pub struct_field_buffer: Vec<SField>,
    pub constant_buffer: String,
}

crate::inherit!(TContext, mt_context, MTContext);

#[derive(Debug, Clone)]
pub struct TState {
    pub builtin_repo: BuiltinRepo,
    pub types: Table<Type, TypeEnt>,
    pub asts: ReusableList<GAst, Ast>,
    pub stypes: List<SType, STypeEnt>,
    pub fun_pointers: List<FunPointer, FunPointerEnt>,
    pub mt_state: MTState,
    pub unresolved: Vec<(Type, usize)>,
    pub resolved: Vec<Type>,
    pub parsed_ast: Ast,
}

impl TState {
    pub fn signature_of_fun_pointer(&self, fun: FunPointer) -> Signature {
        let fun = &self.fun_pointers[fun];

        let mut params = fun
            .args
            .iter()
            .map(|&ty| AbiParam::new(self.types[ty].repr()))
            .collect::<Vec<_>>();

        let mut returns = Vec::new();
        if let Some(ret) = fun.ret {
            let ret = &self.types[ret];
            if ret.on_stack() {
                let param = AbiParam::special(ret.repr(), ArgumentPurpose::StructReturn);
                params.push(param);
                returns.push(param);
            } else {
                returns.push(AbiParam::new(ret.repr()));
            }
        }

        Signature {
            params,
            returns,
            call_conv: fun.call_conv,
        }
    }
}

crate::inherit!(TState, mt_state, MTState);

impl Default for TState {
    fn default() -> Self {
        let mut s = Self {
            builtin_repo: Default::default(),
            types: Table::new(),
            asts: ReusableList::new(),
            stypes: List::new(),
            mt_state: MTState::default(),
            unresolved: vec![],
            resolved: vec![],
            parsed_ast: Ast::default(),
            fun_pointers: List::new(),
        };

        s.builtin_repo = BuiltinRepo::new(&mut s);

        return s;
    }
}

macro_rules! define_repo {
    (
        $($name:ident, $repr:expr, $size:expr);+
    ) => {
        #[derive(Clone, Debug)]
        pub struct BuiltinRepo {
            $(pub $name: Type,)+
        }

        impl Default for BuiltinRepo {
            fn default() -> Self {
                Self {
                    $(
                        $name: Type::new(0),
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
                        kind: TKind::Builtin($repr),
                        size: $size,
                        align: $size.min(8),
                        module,
                        hint: Token::new(LTKind::Ident, name.clone()),
                        name,
                        params: vec![],
                        attrs: Attrs::default(),
                    };
                    let (_, $name) = state.types.insert(id, type_ent);
                )+

                Self {
                    $($name,)+
                }
            }

            pub fn type_list(&self) -> [Type; 14] {
                [
                    $(self.$name,)+
                ]
            }
        }
    };
}

define_repo!(
    i8, I8, 1;
    i16, I16, 2;
    i32, I32, 4;
    i64, I64, 8;
    u8, I8, 1;
    u16, I16, 2;
    u32, I32, 4;
    u64, I64, 8;
    f32, F32, 4;
    f64, F64, 8;
    bool, B1, 1;
    int, ptr_ty(), ptr_ty().bytes() as u32;
    uint, ptr_ty(), ptr_ty().bytes() as u32;
    array, INVALID, 0
);

pub struct Program {
    pub module: ObjectModule,
    pub stacktrace: bool,
}

impl Program {
    pub fn new(module: ObjectModule, stacktrace: bool) -> Self {
        unsafe {
            POINTER_TYPE = module.isa().pointer_type();
        }
        Self { module, stacktrace }
    }

    pub fn parse_call_conv(&self, call_conv: &str) -> Option<CallConv> {
        if call_conv == "platform" {
            let triple = self.module.isa().triple();
            Some(CallConv::triple_default(triple))
        } else {
            CallConv::from_str(call_conv).ok()
        }
    }
}

impl Default for Program {
    fn default() -> Self {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder().unwrap().finish(flags);
        let builder =
            ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();
        Self::new(ObjectModule::new(builder), true)
    }
}

pub struct TypeDisplay<'a> {
    state: &'a TState,
    type_id: Type,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(state: &'a TState, type_id: Type) -> Self {
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
                write!(f, "{}", Self::new(self.state, ty.params[0]))?;
                write!(f, "[")?;
                write!(f, "{}", Self::new(self.state, ty.params[1]))?;
                for param in ty.params[2..].iter() {
                    write!(f, ", {}", Self::new(self.state, *param))?;
                }
                write!(f, "]")
            }
            TKind::Builtin(_) | TKind::Unresolved(_) | TKind::Generic(_) | TKind::Structure(_) => {
                write!(f, "{}", self.state.display(&ty.name))
            }
            TKind::Const(value) => {
                write!(f, "{}", TypeConstDisplay::new(self.state, value))
            }
            TKind::Array(id, len) => {
                write!(f, "[{}, {}]", Self::new(self.state, *id), len)
            }
            &TKind::FunPointer(id) => {
                let fun = &self.state.fun_pointers[id];
                write!(
                    f,
                    "fn({})",
                    fun.args
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
    AmbiguousType(Type, Type),
    UnknownType,
    NotGeneric,
    UnknownModule,
    InstantiationDepthExceeded,
    WrongInstantiationArgAmount(usize, usize),
    AccessingExternalPrivateType,
    AccessingFilePrivateType,
    InfiniteSize(Vec<Type>),
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
        "cold - then its unlikely this gets called",
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
    let mut program = Program::default();
    let mut state = TState::default();
    let mut context = TContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/types/test_project")
        .unwrap();

    let mut collector = Collector::default();

    for module in std::mem::take(&mut state.module_order).drain(..).rev() {
        let mut ast = std::mem::take(&mut state.modules[module].ast);

        let mut ast = AParser::new(&mut state, &mut ast, &mut context)
            .parse()
            .map_err(|err| panic!("\n{}", AErrorDisplay::new(&state, &err)))
            .unwrap();

        collector.clear(&mut context);
        collector.parse(&mut state, &mut ast, Vis::None);

        context.recycle(ast);

        TParser::new(&mut program, &mut state, &mut context, &mut collector)
            .parse(module)
            .map_err(|e| panic!("\n{}", TErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }
}
