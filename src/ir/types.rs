use std::ops::Deref;

use crate::ast::AKind;
use crate::{lexer::Token, util::sdbm::SdbmHashState};

use super::module_tree::ModTreeBuilder;

use super::*;

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

    /*pub fn resolve_immediate(mut self, module: Mod, ast: &Ast) -> Result<Datatype> {
        self.immediate = true;
        let (_, datatype) = self.find_or_instantiate(module, ast)?;

        for i in 0..types.len() {
            self.materialize_datatype(types[i].clone())?;
        }

        Ok(datatype)
    }*/

    pub fn resolve(mut self) -> Result<()> {
        self.collect()?;
        self.connect()?;
        self.materialize()?;
        Ok(())
    }

    fn materialize(&mut self) -> Result<()> {
        for datatype in self.program.types.direct_ids() {
            self.materialize_datatype(datatype)?;
        }

        Ok(())
    }

    fn materialize_datatype(&mut self, datatype: Datatype) -> Result<()> {
        if let Some(idx) = self
            .context
            .instance_buffer
            .iter()
            .position(|&dt| dt == datatype)
        {
            let cycle: Vec<Token> = self.context.instance_buffer[idx..]
                .iter()
                .map(|&dt| self.program.types[dt].token_hint.clone())
                .chain(std::iter::once(
                    self.program.types[datatype].token_hint.clone(),
                ))
                .collect();
            return Err(TypeError::new(
                TEKind::InfiniteSize(cycle),
                &Token::default(),
            ));
        }

        if self.program.types[datatype].size != u32::MAX {
            return Ok(());
        }

        self.context.instance_buffer.push(datatype);

        let mut kind = std::mem::take(&mut self.program.types[datatype].kind);
        let size = match &mut kind {
            DKind::Pointer(_) => self.program.isa.pointer_bytes() as u32,
            DKind::Structure(structure) => {
                let mut size = 0;
                match structure.kind {
                    SKind::Struct => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype)?;
                            field.offset = size;
                            size += self.program.types[field.datatype].size;
                        }
                    }
                    SKind::Union => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype)?;
                            size = std::cmp::max(size, self.program.types[field.datatype].size);
                        }
                    }
                }
                size
            }
            _ => unreachable!(),
        };

        let dt = &mut self.program.types[datatype];
        dt.kind = kind;
        dt.size = size;

        self.context
            .instance_buffer
            .pop()
            .expect("expected previously pushed datatype");

        Ok(())
    }

    fn connect(&mut self) -> Result<()> {
        for datatype in self.program.types.direct_ids() {
            let dt = &self.program.types[datatype];
            if dt.kind != DKind::Unresolved {
                continue;
            }
            match dt.ast.kind {
                AKind::StructDeclaration(_) => {
                    let dt = &mut self.program.types[datatype];
                    let module = dt.module;
                    let ast = std::mem::take(&mut dt.ast);
                    self.program.types[datatype].kind =
                        DKind::Structure(self.connect_struct(module, &ast)?);
                    self.program.types[datatype].ast = ast;
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn connect_struct(&mut self, module: Mod, ast: &Ast) -> Result<Structure> {
        let mut fields = vec![];

        for field_line in ast[1].iter() {
            let (_, datatype) = self.find_or_instantiate(module, field_line.last().unwrap())?;
            let embedded = field_line.kind == AKind::StructField(true);
            for name in field_line[..field_line.len() - 1].iter() {
                fields.push(Field {
                    visibility: Visibility::Public,
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

    fn find_or_instantiate(&mut self, module: Mod, ast: &Ast) -> Result<(Mod, Datatype)> {
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
                let dep = self.program.modules[module]
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

                let actual = self.context.instance_buffer.len() - start;
                let bt = &mut self.program.types[base_type];
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

                for (name, param) in ast[0][1..]
                    .iter()
                    .zip(self.context.instance_buffer.drain(start..))
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
                        DatatypeEntity {
                            visibility,
                            name: id,
                            kind: DKind::Structure(structure),
                            token_hint,
                            ast: Ast::none(),
                            size: u32::MAX,
                            module: host_module,
                        }
                    }
                    _ => unreachable!("found {}", ast),
                };

                self.program.types[base_type].ast = ast;

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
            _ => unreachable!(),
        };

        let visibility = self.program.types[datatype].visibility;

        if visibility == Visibility::Private && self.program.modules[host_module].is_external {
            return Err(TypeError::new(
                TEKind::AccessingExternalPrivateType,
                &ast.token,
            ));
        }

        if visibility == Visibility::FilePrivate && module != host_module {
            return Err(TypeError::new(TEKind::AccessingFilePrivateType, &ast.token));
        }

        self.depth -= 1;

        Ok((host_module, datatype))
    }

    fn create_instance_id(&mut self, module: Mod, ast: &Ast) -> Result<(ID, Datatype, Mod)> {
        let (host_module, base_type) = self.find_or_instantiate(module, &ast[0])?;
        let mut id = self.program.types[base_type].name;
        for param in ast[1..].iter() {
            let (_, param_type) = self.find_or_instantiate(module, param)?;
            self.context.instance_buffer.push(param_type.clone());
            id = id.combine(self.program.types[param_type].name);
        }

        Ok((id, base_type, host_module))
    }

    fn find_by_token(&mut self, module: Mod, token: &Token) -> Result<(Mod, Datatype)> {
        self.find_by_name(module, ID::new().add(token.spam.deref()), false)
            .ok_or_else(|| TypeError::new(TEKind::UnknownType, token))
    }

    fn find_by_name(&self, module: Mod, name: ID, nested: bool) -> Option<(Mod, Datatype)> {
        self
            .program
            .types
            .id_to_direct(name.combine(self.program.modules.direct_to_id(module)))
            .map(|datatype| (module, datatype))
            .or_else(|| {
                if nested {
                    None
                } else {
                    self.program.modules[module]
                        .dependency
                        .iter()
                        .rev()
                        .map(|&(_, dep)| self.find_by_name(dep, name, true))
                        .find(|x| x.is_some())
                        .map(|x| x.unwrap())
                }
            })
    }

    fn collect(&mut self) -> Result<()> {
        for module in self.program.modules.direct_ids() {
            let mut ast = std::mem::take(&mut self.program.modules[module].ast);
            let module_name = self.program.modules.direct_to_id(module);
            for a in ast.iter_mut() {
                match a.kind.clone() {
                    AKind::StructDeclaration(visibility) => {
                        let ident = &a[0];
                        let (ident, kind) = if ident.kind == AKind::Identifier {
                            (ident, DKind::Unresolved)
                        } else {
                            (&ident[0], DKind::Generic)
                        };

                        if ident.kind != AKind::Identifier {
                            return Err(TypeError::new(
                                TEKind::UnexpectedAst(ident.clone()),
                                &ident.token,
                            ));
                        }

                        let name = ID::new().add(ident.token.spam.deref()).combine(module_name);
                        let token_hint = a[0].token.clone();

                        let datatype = DatatypeEntity {
                            visibility,
                            size: u32::MAX * !matches!(kind, DKind::Generic) as u32,
                            kind,
                            name,
                            token_hint: token_hint.clone(),
                            ast: std::mem::take(a),
                            module,
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
        }

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct TypeResolverContext {
    instance_buffer: Vec<Datatype>,
    instance_id_buffer: Vec<ID>,
    shadowed_types: Vec<Datatype>,
    connect_buffer: Vec<Datatype>,
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
    let builder = ModTreeBuilder::default();
    let mut program = builder.build("src/ir/tests/module_tree/root").unwrap();

    let mut ctx = TypeResolverContext::default();

    TypeResolver::new(&mut program, &mut ctx).resolve().unwrap();
}
