use std::ops::{Deref, DerefMut};

use crate::ast::{Ast, Vis, AstParser, AstError, AKind};
use crate::lexer::Token;
use crate::module_tree::{MTState, Mod, MTContext, TreeStorage, OrderingContext, self};
use crate::util::sdbm::{ID, SdbmHashState};
use crate::util::storage::{IndexPointer, Table, List};
use cranelift_codegen::ir::types::{Type as CrType, INVALID};
use cranelift_codegen::ir::types::*;

type Result<T = ()> = std::result::Result<T, TypeError>;

pub const TYPE_SALT: ID = ID(0x9e3779b97f4a7c15);

pub static mut POINTER_TYPE: CrType = INVALID;

pub fn ptr_ty() -> CrType {
    unsafe { POINTER_TYPE }
}

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

    pub fn resolve(&mut self, module: Mod) -> Result {
        self.module = module;
        self.collect(module)?;
        self.connect(module)?;
        self.calc_sizes()?;
        Ok(())
    }

    fn calc_sizes(&mut self) -> Result {
        let mut resolved = std::mem::take(&mut self.state.resolved);
        for ty in resolved.drain(..) {
            if self.node_len(ty) != 0 {
                self.calc_size(ty)?;
            }
        }
        Ok(())
    }

    fn calc_size(&mut self, ty: Type) -> Result {
        // SAFETY: This only avoids memmove of context which would otherwise do
        // except that context is big
        let ctx: &mut TContext = unsafe {
            std::mem::transmute(&mut self.context)
        };

        if let Some(cycle) = module_tree::detect_cycles(self, ty, &mut ctx.cycle_stack) {
            return Err(TypeError::new(
                TEKind::InfiniteSize(cycle),
                Token::default(),
            ));
        }

        module_tree::create_order(self, ty, &mut ctx.ordering);

        for &ty in ctx.ordering.result() {
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
                TKind::Pointer(..) | TKind::Builtin(_) => (),
                _ => unreachable!("{:?}", ty_ent.kind),
            }
        }

        Ok(())
    }
    
    fn connect(&mut self, _module: Mod) -> Result {
        while let Some((id, depth)) = self.state.unresolved.pop() {
            if depth > Self::MAX_TYPE_INSTANTIATION_DEPTH {
                return Err(TypeError::new(
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

    fn connect_type(&mut self, module: Mod, id: Type, ast: GType, depth: usize) -> Result {
        match self.state.gtypes[ast].kind {
            AKind::StructDeclaration(_) => {
                self.connect_structure(module, id, ast, SKind::Struct, depth)?;
            }
            _ => unreachable!("{:?}", self.state.gtypes[ast].kind),
        }
        
        Ok(())
    }

    fn connect_structure(&mut self, module: Mod, id: Type, ast: GType, kind: SKind, depth: usize) -> Result<SType> {
        let mut fields = std::mem::take(&mut self.context.struct_field_buffer); 

        // SAFETY: we can take a reference as we know that 
        // nothing will mutate 'gtypes' since all types are collected
        let ast = unsafe { std::mem::transmute::<&Ast, &Ast>(
            &self.state.gtypes[ast]) };
        
        let module_id = self.state.modules[module].id;
        let params = std::mem::take(&mut self.state.types[id].params);
        let mut shadowed = std::mem::take(&mut self.context.shadowed_types);

        let header = &ast[0];

        if header.kind == AKind::Instantiation {
            if params.len() != header.len() {
                return Err(TypeError::new(
                    TEKind::WrongInstantiationArgAmount(
                        params.len() - 1,
                        header.len() - 1,
                    ),
                    self.state.types[id].hint.clone(),
                ));
            }
            for (a, &param) in header[1..].iter().zip(params[1..].iter()) {
                let id = TYPE_SALT
                    .add(a.token.spam.raw())
                    .combine(module_id);
                
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
                let name = field.token.spam.raw();
                let id = ID(0).add(name);
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

        for (id, ty) in shadowed.drain(..) {
            self.state.types.remove_link(id, ty);
        }

        self.context.shadowed_types = shadowed;

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
            AKind::Ident => self.resolve_simple_type(module, ast.token.clone()),
            AKind::ExplicitPackage => self.resolve_explicit_package_type(module, ast),
            AKind::Instantiation => self.resolve_instance(module, ast, depth),
            AKind::Ref(mutable) => self.resolve_pointer(module, ast, mutable, false, depth),
            AKind::Deref(mutable) => self.resolve_pointer(module, ast, mutable, true, depth),
            _ => unreachable!("{:?}", ast.kind),
        }
    }

    fn resolve_pointer(&mut self, module: Mod, ast: &Ast, mutable: bool, nullable: bool, depth: usize) -> Result<(Mod, Type)> {
        let (module, datatype) = self.resolve_type(module, &ast[0], depth)?;
        let datatype = self.pointer_of(datatype, mutable, nullable);

        Ok((module, datatype))
    }

    fn resolve_instance(&mut self, source_module: Mod, ast: &Ast, depth: usize) -> Result<(Mod, Type)> {
        let (module, ty) = match ast[0].kind {
            AKind::Ident => self.resolve_simple_type(source_module, ast[0].token.clone())?,
            AKind::ExplicitPackage => self.resolve_explicit_package_type(source_module, &ast[0])?,
            _ => unreachable!("{:?}", ast[0].kind),
        };
        
        let module_id = self.state.modules[module].id;
        
        let mut params = std::mem::take(&mut self.context.instance_buffer);
        params.clear();
        params.push(ty);

        for ty in ast[1..].iter() {
            params.push(self.resolve_type(source_module, ty, depth)?.1);
        }

        let mut id = TYPE_SALT;
        for &param in params.iter() {
            id = id.combine(self.state.types[param].id);
        }
        id = id.combine(module_id);

        if let Some(id) = self.type_index(id) {
            return Ok((module, id));
        }

        let ty_ent = &self.state.types[ty];

        let ast_id = match ty_ent.kind {
            TKind::Generic(ast) => ast,
            _ => unreachable!("{:?}", ty_ent.kind),
        };

        let type_ent = TypeEnt {
            id,
            module,
            visibility: ty_ent.visibility,
            params: params.clone(),
            kind: TKind::Unresolved(ast_id),
            name: "",
            hint: ast.token.clone(),
            attribute_id: ty_ent.attribute_id,
            size: 0,
            align: 0,
        };

        self.context.instance_buffer = params;

        let (shadowed, ty) = self.state.types.insert(id, type_ent);
        debug_assert!(shadowed.is_none());

        self.state.unresolved.push((ty, depth));

        Ok((module, ty))
    }

    fn resolve_explicit_package_type(&mut self, module: Mod, ast: &Ast) -> Result<(Mod, Type)> {
        let module = self.state.find_dep(module, &ast[0].token)
            .ok_or_else(|| TypeError::new(TEKind::UnknownPackage, ast.token.clone()))?;
        let result = self.resolve_simple_type(module, ast.token.clone());
        result
    }

    fn resolve_simple_type(&mut self, module: Mod, name: Token) -> Result<(Mod, Type)> {
        let id = TYPE_SALT.add(name.spam.raw());
        self.find_by_id(module, id)
            .ok_or_else(|| TypeError::new(TEKind::UnknownType, name))
    }

    fn find_by_id(&mut self, module: Mod, id: ID) -> Option<(Mod, Type)> {
        let mut buffer = std::mem::take(&mut self.context.scope_buffer);
        self.state.collect_scopes(module, &mut buffer);

        for (module, module_id) in buffer.drain(..) {
            if let Some(ty) = self.type_index(id.combine(module_id)) {
                return Some((module, ty));
            }
        }

        self.context.scope_buffer = buffer;
        
        None
    }

    fn collect(&mut self, module: Mod) -> Result<()> {
        let mut context = std::mem::take(&mut self.context.ast);

        let module_ent = &mut self.state.modules[module];

        let mut ast = AstParser::new(&mut module_ent.ast, &mut context)
            .parse()
            .map_err(|err| TypeError::new(TEKind::AstError(err), Token::default()))?;

        let module_name = module_ent.id;
        for (i, a) in ast.iter_mut().enumerate() {
            let ast = std::mem::take(a);
            let ast = self.state.gtypes.add(ast);
            match a.kind.clone() {
                AKind::StructDeclaration(visibility) => {
                    let ident = &self.state.gtypes[ast][0];
                    let (ident, kind) = if ident.kind == AKind::Ident {
                        (ident, TKind::Unresolved(ast))
                    } else if ident.kind == AKind::Instantiation {
                        (&ident[0], TKind::Generic(ast))
                    } else {
                        return Err(TypeError::new(
                            TEKind::UnexpectedAst(String::from("expected struct identifier")),
                            ident.token.clone(),
                        ));
                    };

                    let name = ident.token.spam.raw();
                    let hint = a[0].token.clone();
                    let id = TYPE_SALT.add(name).combine(module_name);

                    let datatype = TypeEnt {
                        visibility,
                        id,
                        params: vec![],
                        module,
                        kind,
                        name,
                        attribute_id: i,
                        hint: hint.clone(),
                        size: 0,
                        align: 0,
                    };

                    let (replaced, id) = self.state.types.insert(id, datatype);
                    if let Some(other) = replaced {
                        return Err(TypeError::new(
                            TEKind::Redefinition(other.hint),
                            hint.clone(),
                        ));
                    }

                    if let TKind::Unresolved(_) = &self.state.types[id].kind {
                        self.state.unresolved.push((id, 0));
                    }
                }
                _ => (),
            }
        }

        Ok(())
    }
    


    pub fn pointer_of(&mut self, ty: Type, mutable: bool, nullable: bool) -> Type {
        let module = self.state.types[ty].module;
        let name = if mutable { "&var " } else { "&" };
        let id = TYPE_SALT
            .add(name)
            .combine(self.state.types[ty].id)
            .combine(self.state.modules[module].id);
        
        if let Some(index) = self.type_index(id) {
            return index;
        }

        let pointer_type = TypeEnt {
            visibility: Vis::Public,
            id,
            params: vec![],
            kind: TKind::Pointer(ty, mutable, nullable),
            name,
            hint: Token::default(),
            module,
            attribute_id: 0,
            size: 8,
            align: 8,
        };

        let (_, ty) = self.state.types.insert(id, pointer_type);

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
            _ => unreachable!("{:?}", node.kind),
        }
    }

    fn node_len(&self, id: Type) -> usize {
        let node = &self.state.types[id];

        match node.kind {
            _ if node.module != self.module || node.size != 0 => 0,
            TKind::Builtin(_) | 
            TKind::Pointer(..) => 0,
            TKind::Structure(id) => {
                self.state.stypes[id].fields.len()
            },
            TKind::Generic(_) |
            TKind::Unresolved(_) => unreachable!(),
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
    pub name: &'static str,
    pub hint: Token,
    pub attribute_id: usize,
    pub size: u32,
    pub align: u32,
}

#[derive(Debug, Clone)]
pub enum TKind {
    Builtin(CrType),
    Pointer(Type, bool, bool), // mutable, nullable
    Structure(SType),
    Generic(GType),
    Unresolved(GType),
}

crate::index_pointer!(GType);

crate::index_pointer!(SType);

#[derive(Debug, Clone)]
pub struct STypeEnt {
    pub kind: SKind,
    pub fields: Vec<SField>
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
    pub scope_buffer: Vec<(Mod, ID)>,
    pub instance_buffer: Vec<Type>,
    pub instance_id_buffer: Vec<ID>,
    pub shadowed_types: Vec<(ID, Option<Type>)>,
    pub mt_context: MTContext,
    pub struct_field_buffer: Vec<SField>,
    pub ordering: OrderingContext<Type>,
    pub cycle_stack: Vec<(Type, usize)>
}

impl TContext {
    pub fn new(mt_context: MTContext) -> Self {
        Self {
            mt_context,
            ..Default::default()
        }
    }
}

crate::inherit!(TContext, mt_context, MTContext);

pub struct TState {
    pub builtin_repo: BuiltinRepo,
    pub types: Table<Type, TypeEnt>,
    pub gtypes: List<GType, Ast>,
    pub stypes: List<SType, STypeEnt>,
    pub mt_state: MTState,
    pub unresolved: Vec<(Type, usize)>,
    pub resolved: Vec<Type>,
}

impl TState {
    pub fn new(mt_state: MTState) -> Self {
        let mut s = Self {
            builtin_repo: unsafe { std::mem::zeroed() },
            types: Table::new(),
            gtypes: List::new(),
            stypes: List::new(),
            mt_state,
            unresolved: vec![],
            resolved: vec![],
        };

        s.builtin_repo = BuiltinRepo::new(&mut s);
        
        return s;
    }
}

crate::inherit!(TState, mt_state, MTState);

macro_rules! define_repo {
    (
        $($name:ident, $repr:expr, $size:expr);+
    ) => {
        #[derive(Clone, Debug)]
        pub struct BuiltinRepo {
            $(pub $name: Type,)+
        }

        impl BuiltinRepo {
            pub fn new(state: &mut TState) -> Self {
                let module = state.builtin_module;
                let builtin_id = state.modules[module].id;

                $(
                    let id = TYPE_SALT.add(stringify!($name)).combine(builtin_id);
                    let type_ent = TypeEnt {
                        id,
                        visibility: Vis::Public,
                        kind: TKind::Builtin($repr),
                        size: $size,
                        align: $size.min(8),
                        module,
                        hint: Token::builtin(stringify!($name)),
                        name: stringify!($name),
                        params: vec![],
                        attribute_id: 0,
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
    auto, INVALID, 0;
    int, ptr_ty(), ptr_ty().bytes() as u32;
    uint, ptr_ty(), ptr_ty().bytes() as u32
);

pub struct TypeDisplay<'a> {
    state: &'a TState,
    type_id: Type,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(state: &'a TState, type_id: Type) -> Self {
        Self {
            state,
            type_id,
        }
    }
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let ty = &self.state.types[self.type_id];
        match &ty.kind {
            TKind::Pointer(id, ..) => {
                write!(f, "{}", ty.name)?;
                write!(f, "{}", Self::new(self.state, *id))
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
            TKind::Builtin(_) | 
            TKind::Unresolved(_) | 
            TKind::Generic(_) |
            TKind::Structure(_) => write!(f, "{}", ty.name),
        }
    }
}

#[derive(Debug)]
pub struct TypeError {
    pub kind: TEKind,
    pub token: Token,
}

impl TypeError {
    pub fn new(kind: TEKind, token: Token) -> Self {
        Self {
            kind,
            token,
        }
    }
}

#[derive(Debug)]
pub enum TEKind {
    AstError(AstError),
    UnexpectedAst(String),
    UnknownType,
    NotGeneric, 
    UnknownPackage,
    InstantiationDepthExceeded,
    WrongInstantiationArgAmount(usize, usize),
    AccessingExternalPrivateType,
    AccessingFilePrivateType,
    InfiniteSize(Vec<Type>),
    Redefinition(Token),
}

pub fn test() {

}