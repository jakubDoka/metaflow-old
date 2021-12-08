use std::ops::{Index, IndexMut};

use crate::ast::{Ast, Vis, AstParser, AstError, AKind};
use crate::lexer::Token;
use crate::module_tree::{MTState, Mod, MTContext};
use crate::util::sdbm::{ID, SdbmHashState};
use crate::util::storage::{IndexPointer, SyncList, SyncTable, Table, List};
use cranelift_codegen::ir::types::Type as CrType;

type Result<T = ()> = std::result::Result<T, TypeError>;

pub const TYPE_SALT: ID = ID(0x9e3779b97f4a7c15);

pub struct TParser<'a> {
    state: &'a mut TState,
    main_state: &'a mut TMainState,
    context: &'a mut TContext,
}

impl<'a> TParser<'a> {
    pub const MAX_TYPE_INSTANTIATION_DEPTH: usize = 1000;

    pub fn new(state: &'a mut TState, main_state: &'a mut TMainState, context: &'a mut TContext) -> Self {
        Self {
            state,
            context,
            main_state,
        }
    }

    pub fn resolve(&mut self, module: Mod) -> Result {
        self.collect(module)?;
        self.connect(module)?;
        Ok(())
    }

    /*pub fn resolve(mut self) -> Result<()> {
        self.collect()?;
        self.connect()?;
        self.materialize()?;
        Ok(())
    }

    fn materialize(&mut self) -> Result<()> {
        for datatype in unsafe { self.program.types.direct_ids() } {
            if !self.program.types.is_direct_valid(datatype) {
                continue;
            }
            self.materialize_datatype(datatype)?;
        }

        Ok(())
    }

    fn materialize_datatype(&mut self, datatype: Type) -> Result<()> {
        if let Some(idx) = self
            .context
            .instance_buffer
            .iter()
            .position(|&dt| dt == datatype)
        {
            let cycle: Vec<Token> = self.context.instance_buffer[idx..]
                .iter()
                .map(|&dt| self.program[dt].token_hint.clone())
                .chain(std::iter::once(self.program[datatype].token_hint.clone()))
                .collect();
            return Err(TypeError::new(
                TEKind::InfiniteSize(cycle),
                &Token::default(),
            ));
        }

        if self.program[datatype].size != u32::MAX {
            return Ok(());
        }

        self.context.instance_buffer.push(datatype);

        let mut kind = std::mem::take(&mut self.program[datatype].kind);
        let (size, align) = match &mut kind {
            TKind::Pointer(..) => {
                let size = self.program.isa().pointer_bytes() as u32;
                (size, size)
            }
            TKind::Structure(structure) => {
                let mut size = 0;
                let mut align = 0;
                match structure.kind {
                    SKind::Struct => {
                        align = structure
                            .fields
                            .iter()
                            .map(|field| self.program[field.datatype].align)
                            .max()
                            .unwrap_or(0);

                        if align != 0 {
                            let calc = move |offset| {
                                align * ((offset & (align - 1)) != 0) as u32
                                    - (offset & (align - 1))
                            };

                            for field in &mut structure.fields {
                                self.materialize_datatype(field.datatype)?;
                                size += calc(size);
                                field.offset = size;
                                size += self.program[field.datatype].size;
                            }

                            size += calc(size);
                        }
                    }
                    SKind::Union => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype)?;
                            size = std::cmp::max(size, self.program[field.datatype].size);
                        }
                    }
                }
                (size, align)
            }
            _ => unreachable!(),
        };

        let dt = &mut self.program[datatype];
        dt.kind = kind;
        dt.size = size;
        dt.align = align;

        self.context
            .instance_buffer
            .pop()
            .expect("expected previously pushed datatype");

        Ok(())
    }
    */

    fn calc_size(&mut self, ty: Type) -> Result {
         let type_order = vec![];


    }
    
    fn connect(&mut self, _module: Mod) -> Result {
        while let Some((id, depth)) = self.state.unresolved.pop() {
            if depth > Self::MAX_TYPE_INSTANTIATION_DEPTH {
                return Err(TypeError::new(
                    TEKind::InstantiationDepthExceeded,
                    self[id].hint.clone(),
                ));
            }

            let ty = &self.state.types[id];
            let ty_module = ty.module;

            match &ty.kind {
                &TKind::Unresolved(ast) => self.connect_type(ty_module, id, ast, depth)?,
                _ => unreachable!("{:?}", &self.state.types[id].kind),
            }
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
        
        let module_id = self.main_state.mt_state.modules[module].id;
        let params = std::mem::take(&mut self[id].params);
        let mut shadowed = std::mem::take(&mut self.context.shadowed_types);

        if ast[0].kind == AKind::Instantiation {
            for (a, &param) in ast[1..].iter().zip(params[1..].iter()) {
                let id = TYPE_SALT
                    .add(a.token.spam.raw())
                    .combine(module_id);
                
                let sha = self.state.types.link(id, param);
                shadowed.push((id, sha));
            }
        }

        self[id].params = params;
        
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
            AKind::Ref(mutable) => self.resolve_pointer(module, ast, mutable, depth),
            _ => unreachable!("{:?}", ast.kind),
        }
    }

    fn resolve_pointer(&mut self, module: Mod, ast: &Ast, mutable: bool, depth: usize) -> Result<(Mod, Type)> {
        let (module, datatype) = self.resolve_type(module, &ast[0], depth)?;
        let datatype = self.pointer_of(datatype, mutable);

        Ok((module, datatype))
    }

    fn resolve_instance(&mut self, source_module: Mod, ast: &Ast, depth: usize) -> Result<(Mod, Type)> {
        let (module, ty) = match ast[0].kind {
            AKind::Ident => self.resolve_simple_type(source_module, ast[0].token.clone())?,
            AKind::ExplicitPackage => self.resolve_explicit_package_type(source_module, &ast[0])?,
            _ => unreachable!("{:?}", ast[0].kind),
        };
        
        let module_id = self.main_state.mt_state.modules[module].id;
        
        let mut params = std::mem::take(&mut self.context.instance_buffer);
        params.clear();
        params.push(ty);

        for ty in ast[1..].iter() {
            params.push(self.resolve_type(source_module, ty, depth)?.1);
        }

        let mut id = TYPE_SALT;
        for &param in params.iter() {
            id = id.combine(self[param].id);
        }
        id = id.combine(module_id);

        if let Some(id) = self.type_index(id) {
            return Ok((module, id));
        }

        let ty_ent = &self[ty];

        let ast = match ty_ent.kind {
            TKind::Generic(ast) => ast,
            _ => unreachable!("{:?}", ty_ent.kind),
        };

        let type_ent = TypeEnt {
            id,
            module,
            visibility: ty_ent.visibility,
            params: params.clone(),
            kind: TKind::Unresolved(ast),
            name: "",
            hint: ty_ent.hint.clone(),
            attribute_id: ty_ent.attribute_id,
        };

        self.context.instance_buffer = params;

        let (shadowed, ty) = self.state.types.insert(id, type_ent);
        debug_assert!(shadowed.is_none());

        self.state.unresolved.push((ty, depth));

        Ok((module, ty))
    }

    fn resolve_explicit_package_type(&mut self, module: Mod, ast: &Ast) -> Result<(Mod, Type)> {
        let module = self.main_state.mt_state.find_dep(module, &ast[0].token)
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
        self.main_state.mt_state.collect_scopes(module, &mut buffer);

        for (module, module_id) in buffer.drain(..) {
            if let Some(ty) = self.type_index(id.combine(module_id)) {
                return Some((module, ty));
            }
        }

        self.context.scope_buffer = buffer;
        
        None
    }

    fn collect(&mut self, module: Mod) -> Result<()> {
        let mut context = std::mem::take(&mut self.context.mt_context.ast);

        let module_ent = &mut self.main_state.mt_state.modules[module];

        let mut ast = AstParser::new(&mut module_ent.ast, &mut context)
            .parse()
            .map_err(|err| TypeError::new(TEKind::AstError(err), Token::default()))?;

        let module_name = module_ent.id;
        for (i, a) in ast.iter_mut().enumerate() {
            let ast = std::mem::take(a);
            let ast = self.state.gtypes.add(ast);
            match a.kind.clone() {
                AKind::StructDeclaration(visibility) => {
                    let ident = &self[ast][0];
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
    


    pub fn pointer_of(&mut self, datatype: Type, mutable: bool) -> Type {
        let module = self[datatype].module;
        let name = if mutable { "&var " } else { "&" };
        let id = TYPE_SALT
            .add(name)
            .combine(self[datatype].id)
            .combine(self.main_state.mt_state.modules[module].id);
        
        if let Some(index) = self.type_index(id) {
            return index;
        }

        let pointer_type = TypeEnt {
            visibility: Vis::Public,
            id,
            params: vec![],
            kind: TKind::Pointer(datatype, mutable),
            name,
            hint: Token::default(),
            module,
            attribute_id: 0,
        };

        let (_, datatype) = self.state.types.insert(id, pointer_type);

        datatype
    }

    fn type_index(&self, id: ID) -> Option<Type> {
        self.state.types.index(id).or_else(|| self.main_state.types.index(id)).map(|&id| id)
    } 
}

impl<'a> Index<ID> for TParser<'a> {
    type Output = TypeEnt;

    fn index(&self, id: ID) -> &Self::Output {
        self.state.types.get(id).or_else(|| self.main_state.types.get(id)).unwrap()
    }
}

impl<'a> IndexMut<ID> for TParser<'a> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        &mut self.state.types[id]
    }
}

macro_rules! impl_type_indexing {
    ($by:ty, $to:ty, $field:ident) => {
        impl<'a> Index<$by> for TParser<'a> {
            type Output = $to;
        
            fn index(&self, index: $by) -> &Self::Output {
                if index.raw() > self.main_state.$field.len() {
                    &self.state.$field[index]
                } else {
                    &self.main_state.$field[index]
                }
            }
        }
        
        impl<'a> IndexMut<$by> for TParser<'a> {
            fn index_mut(&mut self, index: $by) -> &mut Self::Output {
                &mut self.state.$field[index]
            }
        }
    };
}

impl_type_indexing!(Type, TypeEnt, types);
impl_type_indexing!(SType, STypeEnt, stypes);
impl_type_indexing!(GType, Ast, gtypes);

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
}

#[derive(Debug, Clone)]
pub enum TKind {
    Builtin(CrType),
    Pointer(Type, bool),
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
}

pub struct TMainState {
    pub types: Table<Type, TypeEnt>,
    pub gtypes: List<GType, Ast>,
    pub stypes: List<SType, STypeEnt>,
    pub mt_state: MTState,
}

#[derive(Debug, Default, Clone)]
pub struct TState {
    pub unresolved: Vec<(Type, usize)>,
    pub types: SyncTable<Type, TypeEnt>,
    pub gtypes: SyncList<GType, Ast>,
    pub stypes: SyncList<SType, STypeEnt>,
}


/*pub struct TypePrinter<'a> {
    program: &'a Program,
}

impl<'a> TypePrinter<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self { program }
    }

    pub fn print(&self, datatype: Type) -> String {
        let mut buffer = String::new();

        self.print_buff(datatype, &mut buffer);

        buffer
    }

    pub fn print_buff(&self, datatype: Type, buffer: &mut String) {
        let dt = &self.program[datatype];
        match &dt.kind {
            TKind::Structure(_) if dt.params.len() > 1 => {
                self.print_buff(dt.params[0], buffer);
                buffer.push('[');
                for param in &dt.params[1..] {
                    self.print_buff(*param, buffer);
                    buffer.push(',');
                }
                buffer.pop();
                buffer.push(']');
            }
            TKind::Structure(_) | TKind::Builtin(_) | TKind::Generic => {
                buffer.push_str(dt.debug_name)
            }
            TKind::Pointer(pointed, _) => {
                buffer.push_str(dt.debug_name);
                self.print_buff(*pointed, buffer);
            }
            TKind::Unresolved => unreachable!(),
        }
    }
}*/

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
    InfiniteSize(Vec<Token>),
    Redefinition(Token),
}
