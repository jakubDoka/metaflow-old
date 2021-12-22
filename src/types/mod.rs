use std::fmt::Write;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use crate::ast::{AError, AErrorDisplay, AKind, AParser, Ast, Vis};
use crate::collector::{Attrs, Collector, Item};
use crate::lexer::{LineData, Spam, TKind as LTKind, Token, TokenDisplay};
use crate::module_tree::{self, MTContext, MTParser, MTState, Mod, TreeStorage};
use crate::util::sdbm::ID;
use crate::util::storage::{IndexPointer, List, ReusableList, Table};
use cranelift_codegen::ir::types::*;
use cranelift_codegen::ir::types::{Type as CrType, INVALID};

type Result<T = ()> = std::result::Result<T, TError>;

pub const TYPE_SALT: ID = ID(0x9e3779b97f4a7c15);

pub static mut POINTER_TYPE: CrType = INVALID;

pub fn ptr_ty() -> CrType {
    unsafe { POINTER_TYPE }
}

pub struct TParser<'a> {
    module: Mod,
    state: &'a mut TState,
    context: &'a mut TContext,
    collector: &'a mut Collector,
}

impl<'a> TParser<'a> {
    pub const MAX_TYPE_INSTANTIATION_DEPTH: usize = 1000;

    pub fn new(
        state: &'a mut TState,
        context: &'a mut TContext,
        collector: &'a mut Collector,
    ) -> Self {
        Self {
            module: Mod::new(0),
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
                    .add(ID::new(self.state.display(&a.token.spam)))
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
                let id = field.token.spam.hash;
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
        match ast.kind {
            AKind::Ident => self.resolve_simple_type(module, &ast.token),
            AKind::Path => self.resolve_explicit_package_type(module, ast),
            AKind::Instantiation => self.resolve_instance(module, ast, depth),
            AKind::Ref => self.resolve_pointer(module, ast, depth),
            AKind::Array => self.resolve_array(module, ast, depth),
            AKind::Lit => self.resolve_constant(module, &ast.token),
            AKind::Fun(..) => self.resolve_function_pointer(module, ast, depth),
            _ => unreachable!("{:?}", ast.kind),
        }
    }

    fn resolve_function_pointer(
        &mut self,
        module: Mod,
        ast: &Ast,
        depth: usize,
    ) -> Result<(Mod, Type)> {
        let mut args = self.context.pool.get();

        let ast = &ast[0];

        let mut id = TYPE_SALT.add(ID::new("fun"));

        for arg in ast[1..ast.len() - 1].iter() {
            let (_, ty) = self.resolve_type(module, arg, depth)?;
            id = id.add(self.state.types[ty].id);
            args.push(ty);
        }

        let ret = if ast[ast.len() - 1].kind != AKind::None {
            let (_, ty) = self.resolve_type(module, &ast[ast.len() - 1], depth)?;
            id = id.add(ID::new("->")).add(self.state.types[ty].id);
            Some(ty)
        } else {
            None
        };

        if let Some(&id) = self.state.types.index(id) {
            return Ok((module, id));
        }

        let fun = FunPointerEnt {
            args: args.clone(),
            ret,
        };
        let fun = self.state.fun_pointers.add(fun);

        let size = ptr_ty().bytes() as u32;
        let type_ent = TypeEnt {
            kind: TKind::FunPointer(fun),
            params: vec![],
            hint: ast.token.clone(),
            id,
            module,
            visibility: Vis::None,
            name: ast.token.spam.clone(),
            attrs: Attrs::default(),
            size,
            align: size,
        };

        let (shadowed, id) = self.state.types.insert(id, type_ent);
        debug_assert!(shadowed.is_none());

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
        let (module, ty) = match ast[0].kind {
            AKind::Ident => self.resolve_simple_type(source_module, &ast[0].token)?,
            AKind::Path => self.resolve_explicit_package_type(source_module, &ast[0])?,
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
            visibility: ty_ent.visibility,
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

    fn resolve_explicit_package_type(&mut self, module: Mod, ast: &Ast) -> Result<(Mod, Type)> {
        let module = self
            .state
            .find_dep(module, &ast[0].token)
            .ok_or_else(|| TError::new(TEKind::UnknownModule, ast.token.clone()))?;
        let module_id = self.state.modules[module].id;
        let id = TYPE_SALT.add(ast[1].token.spam.hash);
        self.type_index(id.add(module_id))
            .map(|id| (module, id))
            .ok_or_else(|| TError::new(TEKind::UnknownType, ast[0].token.clone()))
    }

    fn resolve_simple_type(&mut self, module: Mod, name: &Token) -> Result<(Mod, Type)> {
        let id = TYPE_SALT.add(name.spam.hash);

        let mut buffer = self.context.pool.get();
        self.state.collect_scopes(module, &mut buffer);

        let (module, module_id) = buffer[0];
        if let Some(ty) = self.type_index(id.add(module_id)) {
            return Ok((module, ty));
        }

        let mut found = None;

        for (module, module_id) in buffer.drain(1..) {
            if let Some(ty) = self.type_index(id.add(module_id)) {
                if let Some((_, found)) = found {
                    return Err(TError::new(TEKind::AmbiguousType(ty, found), name.clone()));
                }
                found = Some((module, ty));
            }
        }

        found.ok_or_else(|| TError::new(TEKind::UnknownType, name.clone()))
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
                    let id = TYPE_SALT.add(ident.token.spam.hash).add(module_name);
                    let datatype = TypeEnt {
                        visibility,
                        id,
                        params: vec![],
                        module,
                        kind,
                        name: ident.token.spam.clone(),
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

        let pointer_type = TypeEnt {
            visibility: Vis::Public,
            id,
            params: vec![],
            kind: TKind::Pointer(ty),
            name: Spam::default(),
            hint: Token::default(),
            module,
            attrs: Attrs::default(),
            size: 8,
            align: 8,
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
            visibility: Vis::Public,
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
        write!(self.context.constant_buffer, "{}", constant).unwrap();

        let id = TYPE_SALT.add(ID::new(&self.context.constant_buffer));

        if let Some(&tp) = self.state.types.index(id) {
            return tp;
        }

        let ty_ent = TypeEnt {
            id,
            visibility: Vis::Public,
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

crate::index_pointer!(Type);

#[derive(Debug, Clone)]
pub struct TypeEnt {
    pub id: ID,
    pub module: Mod,
    pub visibility: Vis,
    pub params: Vec<Type>,
    pub kind: TKind,
    pub name: Spam,
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
            visibility: Vis::Public,
            params: vec![],
            kind: TKind::Unresolved(GAst::new(0)),
            name: Spam::default(),
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
    args: Vec<Type>,
    ret: Option<Type>,
}

#[derive(Debug, Clone)]
pub enum TypeConst {
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),
    String(Rc<Vec<u8>>),
}

impl std::fmt::Display for TypeConst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeConst::Bool(b) => write!(f, "{}", b),
            TypeConst::Int(i) => write!(f, "{}", i),
            TypeConst::Float(float) => write!(f, "{}", float),
            TypeConst::Char(c) => write!(f, "'{}'", c),
            TypeConst::String(s) => {
                write!(f, "\"{}\"", unsafe { std::str::from_utf8_unchecked(s) })
            }
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
                    let name = state.builtin_spam(stringify!($name));
                    let id = TYPE_SALT.add(ID::new(stringify!($name))).add(builtin_id);
                    let type_ent = TypeEnt {
                        id,
                        visibility: Vis::Public,
                        kind: TKind::Builtin($repr),
                        size: $size,
                        align: $size.min(8),
                        module,
                        hint: Token::new(LTKind::Ident, name.clone(), LineData::default()),
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
                write!(f, "{}", value)
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

pub fn test() {
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
            .map_err(|err| TError::new(TEKind::AError(err), Token::default()))
            .unwrap();

        collector.clear(&mut context);
        collector.parse(&mut state, &mut ast);

        context.recycle(ast);

        TParser::new(&mut state, &mut context, &mut collector)
            .parse(module)
            .map_err(|e| println!("{}", TErrorDisplay::new(&mut state, &e)))
            .unwrap();
    }
}
