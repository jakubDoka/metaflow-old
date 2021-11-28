use std::ops::Deref;

use crate::ast::{AKind, Ast, Vis};
use crate::ir::{Field, SKind, TKind};
use crate::util::sdbm::ID;
use crate::{lexer::Token, util::sdbm::SdbmHashState};

use super::module_tree::ModuleTreeBuilder;
use super::{Module, Program, Structure, Type, TypeEnt};

type Result<T> = std::result::Result<T, TypeError>;

pub struct TypeResolver<'a> {
    immediate: bool,
    program: &'a mut Program,
    context: &'a mut TypeResolverContext,
    depth: usize,
}

impl<'a> TypeResolver<'a> {
    #[cfg(debug_assertions)]
    pub const MAX_DEPTH: usize = 50;
    #[cfg(not(debug_assertions))]
    pub const MAX_DEPTH: usize = 500;

    pub fn new(program: &'a mut Program, context: &'a mut TypeResolverContext) -> Self {
        context.clear();
        Self {
            context,
            program,
            immediate: false,
            depth: 0,
        }
    }

    pub fn resolve_immediate(&mut self, module: Module, ast: &Ast) -> Result<Type> {
        let (_, datatype) = self.find_or_instantiate(module, ast)?;
        self.materialize_datatype(datatype)?;

        Ok(datatype)
    }

    pub fn resolve(mut self) -> Result<()> {
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
        let size = match &mut kind {
            TKind::Pointer(_) => self.program.isa.pointer_bytes() as u32,
            TKind::Structure(structure) => {
                let mut size = 0;
                match structure.kind {
                    SKind::Struct => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype)?;
                            field.offset = size;
                            size += self.program[field.datatype].size;
                        }
                    }
                    SKind::Union => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype)?;
                            size = std::cmp::max(size, self.program[field.datatype].size);
                        }
                    }
                }
                size
            }
            _ => unreachable!(),
        };

        let dt = &mut self.program[datatype];
        dt.kind = kind;
        dt.size = size;

        self.context
            .instance_buffer
            .pop()
            .expect("expected previously pushed datatype");

        Ok(())
    }

    fn connect(&mut self) -> Result<()> {
        for datatype in unsafe { self.program.types.direct_ids() } {
            if !self.program.types.is_direct_valid(datatype) {
                continue;
            }
            let dt = &self.program[datatype];
            if dt.kind != TKind::Unresolved {
                continue;
            }
            match dt.ast.kind {
                AKind::StructDeclaration(_) => {
                    let dt = &mut self.program[datatype];
                    let module = dt.module;
                    let ast = std::mem::take(&mut dt.ast);
                    self.program[datatype].kind =
                        TKind::Structure(self.connect_struct(module, &ast)?);
                    self.program[datatype].ast = ast;
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn connect_struct(&mut self, module: Module, ast: &Ast) -> Result<Structure> {
        let mut fields = vec![];

        for field_line in ast[1].iter() {
            let (_, datatype) = self.find_or_instantiate(module, field_line.last().unwrap())?;
            let embedded = field_line.kind == AKind::StructField(true);
            for name in field_line[..field_line.len() - 1].iter() {
                fields.push(Field {
                    visibility: Vis::Public,
                    name: name.token.spam.clone(),
                    embedded,
                    offset: 0,
                    datatype: datatype.clone(),
                })
            }
        }

        Ok(Structure {
            kind: SKind::Struct,
            fields,
        })
    }

    fn find_or_instantiate(&mut self, module: Module, ast: &Ast) -> Result<(Module, Type)> {
        self.depth += 1;
        if self.depth > Self::MAX_DEPTH {
            return Err(TypeError::new(
                TEKind::InstantiationDepthExceeded,
                &ast.token,
            ));
        }
        let (host_module, datatype) = match ast.kind {
            AKind::Identifier => self.find_by_token(module, &ast.token)?,
            AKind::ExplicitPackage => {
                let package_name = ID::new().add(ast[0].token.spam.deref());
                let dep = self.program[module]
                    .dependency
                    .iter()
                    .rev()
                    .find(|(name, _)| *name == package_name)
                    .map(|(_, dep)| *dep)
                    .ok_or_else(|| TypeError::new(TEKind::UnknownPackage, &ast[0].token))?;
                self.find_by_token(dep, &ast[1].token)?
            }
            AKind::Instantiation => {
                let start = self.context.instance_buffer.len();
                let (id, base_type, host_module) = self.create_instance_id(module, &ast)?;

                if let Some(datatype) = self.program.types.id_to_direct(id) {
                    self.context.instance_buffer.truncate(start);
                    return Ok((host_module, datatype));
                }

                let actual = self.context.instance_buffer.len() - start - 1;
                let bt = &mut self.program[base_type];
                let ast = std::mem::take(&mut bt.ast);
                let token_hint = bt.token_hint.clone();
                let supposed = if ast[0].kind == AKind::Instantiation {
                    ast[0].len() - 1
                } else {
                    0
                };

                if actual != supposed {
                    return Err(TypeError::new(
                        TEKind::WrongInstantiationArgAmount(actual, supposed),
                        &ast.token,
                    ));
                }

                let old_len = self.context.shadowed_types.len();
                let old_id_len = self.context.instance_id_buffer.len();

                //println!("{:?}", self.context.instance_buffer);

                let params = self.context.instance_buffer.clone();

                for (name, param) in ast[0][1..]
                    .iter()
                    .zip(self.context.instance_buffer.drain(start..).skip(1))
                {
                    let id = ID::new()
                        .add(name.token.spam.deref())
                        .combine(self.program.modules.direct_to_id(host_module));

                    if let Some(shadowed) = self.program.types.redirect(id, param) {
                        self.context.shadowed_types.push(shadowed);
                    } else {
                        self.context.instance_id_buffer.push(id);
                    }
                }

                let datatype = match ast.kind.clone() {
                    AKind::StructDeclaration(visibility) => {
                        let structure = self.connect_struct(host_module, &ast)?;
                        TypeEnt {
                            visibility,
                            name: id,
                            kind: TKind::Structure(structure),
                            token_hint,
                            ast: Ast::none(),
                            size: u32::MAX,
                            module: host_module,
                            attribute_id: self.program[base_type].attribute_id,
                            params,
                            align: 0,
                        }
                    }
                    _ => unreachable!("found {}", ast),
                };

                self.program[base_type].ast = ast;

                for i in old_id_len..self.context.instance_id_buffer.len() {
                    self.program
                        .types
                        .remove_redirect(self.context.instance_id_buffer[i], None);
                }
                self.context.instance_id_buffer.truncate(old_id_len);

                for i in old_len..self.context.shadowed_types.len() {
                    let direct_id = self.context.shadowed_types[i];
                    let id = self.program.types.direct_to_id(direct_id);
                    self.program.types.remove_redirect(id, Some(direct_id));
                }
                self.context.shadowed_types.truncate(old_len);

                (host_module, self.program.types.insert(id, datatype).1)
            }
            _ => unreachable!("{}", ast),
        };

        let visibility = self.program[datatype].visibility;

        if visibility == Vis::Private && self.program[host_module].is_external {
            return Err(TypeError::new(
                TEKind::AccessingExternalPrivateType,
                &ast.token,
            ));
        }

        if visibility == Vis::FilePrivate && module != host_module {
            return Err(TypeError::new(TEKind::AccessingFilePrivateType, &ast.token));
        }

        self.depth -= 1;

        Ok((host_module, datatype))
    }

    fn create_instance_id(&mut self, module: Module, ast: &Ast) -> Result<(ID, Type, Module)> {
        let (host_module, base_type) = self.find_or_instantiate(module, &ast[0])?;
        self.context.instance_buffer.push(base_type);
        let mut id = self.program[base_type].name;
        for param in ast[1..].iter() {
            let (_, param_type) = self.find_or_instantiate(module, param)?;
            self.context.instance_buffer.push(param_type.clone());
            id = id.combine(self.program[param_type].name);
        }

        Ok((id, base_type, host_module))
    }

    pub fn find_by_token(&mut self, module: Module, token: &Token) -> Result<(Module, Type)> {
        self.find_by_name(module, ID::new().add(token.spam.deref()))
            .ok_or_else(|| TypeError::new(TEKind::UnknownType, token))
    }

    fn find_by_name(&self, module: Module, name: ID) -> Option<(Module, Type)> {
        self.program.walk_accessible_scopes(module, |id, module| {
            self.program
                .types
                .id_to_direct(name.combine(id))
                .map(|id| (module, id))
        })
    }

    fn collect(&mut self) -> Result<()> {
        for module in unsafe { self.program.modules.direct_ids() } {
            if !self.program.modules.is_direct_valid(module) {
                continue;
            }
            let mut ast = std::mem::take(&mut self.program[module].ast);
            let module_name = self.program.modules.direct_to_id(module);
            for (i, a) in ast.iter_mut().enumerate() {
                match a.kind.clone() {
                    AKind::StructDeclaration(visibility) => {
                        let ident = &a[0];
                        let (ident, kind) = if ident.kind == AKind::Identifier {
                            (ident, TKind::Unresolved)
                        } else {
                            (&ident[0], TKind::Generic)
                        };

                        if ident.kind != AKind::Identifier {
                            return Err(TypeError::new(
                                TEKind::UnexpectedAst(ident.clone()),
                                &ident.token,
                            ));
                        }

                        let name = ID::new().add(ident.token.spam.deref()).combine(module_name);
                        let token_hint = a[0].token.clone();

                        let datatype = TypeEnt {
                            visibility,
                            size: u32::MAX * !matches!(kind, TKind::Generic) as u32,
                            kind,
                            name,
                            token_hint: token_hint.clone(),
                            ast: std::mem::take(a),
                            module,
                            attribute_id: i,
                            params: Vec::new(),
                            align: 0,
                        };

                        if let (Some(datatype), _) = self.program.types.insert(name, datatype) {
                            return Err(TypeError::new(
                                TEKind::Redefinition(datatype.token_hint.clone()),
                                &token_hint,
                            ));
                        };
                    }
                    _ => (),
                }
            }

            self.program[module].ast = ast;
        }

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct TypeResolverContext {
    pub instance_buffer: Vec<Type>,
    pub instance_id_buffer: Vec<ID>,
    pub shadowed_types: Vec<Type>,
    pub connect_buffer: Vec<Type>,
}

impl TypeResolverContext {
    pub fn clear(&mut self) {
        self.instance_buffer.clear();
        self.instance_id_buffer.clear();
        self.shadowed_types.clear();
        self.connect_buffer.clear();
    }
}

#[derive(Clone, Debug)]
pub struct TypeError {
    pub kind: TEKind,
    pub token: Token,
}

impl TypeError {
    pub fn new(kind: TEKind, token: &Token) -> Self {
        Self {
            kind,
            token: token.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum TEKind {
    UnexpectedAst(Ast),
    UnknownType,
    UnknownPackage,
    InstantiationDepthExceeded,
    WrongInstantiationArgAmount(usize, usize),
    AccessingExternalPrivateType,
    AccessingFilePrivateType,
    InfiniteSize(Vec<Token>),
    Redefinition(Token),
}

pub fn test() {
    let builder = ModuleTreeBuilder::default();
    let mut program = builder.build("src/ir/tests/module_tree/root").unwrap();

    let mut ctx = TypeResolverContext::default();

    TypeResolver::new(&mut program, &mut ctx).resolve().unwrap();
}
