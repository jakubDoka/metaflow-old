use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::settings;

use crate::{lexer::Token, util::sdbm::SdbmHashState};

use super::module_tree::ModTreeBuilder;

use super::*;

type Result<T> = std::result::Result<T, TypeError>;

pub struct TypeResolver<'a> {
    immediate: bool,
    isa: &'a dyn TargetIsa,
    program: &'a mut Program,
    context: &'a mut TypeResolverContext,
    depth: usize,
}

impl<'a> TypeResolver<'a> {
    #[cfg(debug_assertions)]
    pub const MAX_DEPTH: usize = 50;
    #[cfg(not(debug_assertions))]
    pub const MAX_DEPTH: usize = 500;

    pub fn new(program: &'a mut Program, context: &'a mut TypeResolverContext, isa: &'a dyn TargetIsa) -> Self {
        context.clear();
        Self { program, context, isa, immediate: false, depth: 0 }
    }

    pub fn resolve_immediate(mut self, module: Cell<Mod>, ast: &Ast) -> Result<Cell<Datatype>> {
        self.immediate = true;
        let (_, datatype) = self.find_or_instantiate(module, ast)?;

        for i in 0..self.context.new_types.len() {
            self.materialize_datatype(self.context.new_types[i].clone())?;
        }

        Ok(datatype)
    }

    pub fn resolve(mut self) -> Result<()> {
        for i in 0..self.program.mods.len() {
            self.collect(self.program.mods[i].clone())?;
        }

        for i in 0..self.program.mods.len() {
            self.connect(self.program.mods[i].clone())?;
        }

        for i in 0..self.program.mods.len() {
            self.materialize(self.program.mods[i].clone())?;
        }

        Ok(())
    }

    fn materialize(&mut self, module: Cell<Mod>) -> Result<()> {
        for (_, datatype) in module.types.iter() {
            self.materialize_datatype(datatype.clone())?;
        }

        Ok(())
    }

    fn materialize_datatype(&mut self, mut datatype: Cell<Datatype>) -> Result<()> {
        if let Some(idx) = self.context.instance_buffer.iter().position(|dt| dt.name == datatype.name) {
            let cycle: Vec<Token> = self.context.instance_buffer[idx..]
                .iter()
                .map(|dt| dt.token_hint.clone())
                .chain(std::iter::once(datatype.token_hint.clone()))
                .collect();
            return Err(TypeError::new(TEKind::InfiniteSize(cycle), &Token::default()));
        }

        if datatype.size != u32::MAX {
            return Ok(());
        }

        self.context.instance_buffer.push(datatype.clone());

        let size = match &mut datatype.kind {
            DKind::Pointer(_) => self.isa.pointer_bytes() as u32,
            DKind::Structure(structure) => {
                let mut size = 0;
                match structure.kind {
                    SKind::Struct => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype.clone())?;
                            field.offset = size;
                            size += field.datatype.size;
                        } 
                    }
                    SKind::Union => {
                        for field in &mut structure.fields {
                            self.materialize_datatype(field.datatype.clone())?;
                            size = std::cmp::max(size, field.datatype.size);
                        }
                    }
                }
                size
            },
            _ => unreachable!(),
        };

        datatype.size = size;

        self.context.instance_buffer.pop().expect("expected previously pushed datatype");

        Ok(())
    }

    fn connect(&mut self, module: Cell<Mod>) -> Result<()> {
        for mut datatype in module
            .types
            .iter()
            .map(|(_, t)| t.clone())
            .filter(|t| t.kind == DKind::Unresolved)
        {
            match datatype.ast.kind {
                AKind::StructDeclaration(_) => {
                    datatype.kind =
                        DKind::Structure(self.connect_struct(module.clone(), datatype.clone())?);
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn connect_struct(&mut self, module: Cell<Mod>, datatype: Cell<Datatype>) -> Result<Structure> {
        let mut fields = vec![];
        for field_line in datatype.ast[1].iter() {
            let (_, datatype) =
                self.find_or_instantiate(module.clone(), field_line.last().unwrap())?;
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

    fn find_or_instantiate(
        &mut self,
        module: Cell<Mod>,
        ast: &Ast,
    ) -> Result<(Cell<Mod>, Cell<Datatype>)> {
        self.depth += 1;
        println!("{}", self.depth);
        if self.depth > Self::MAX_DEPTH {
            return Err(TypeError::new(TEKind::InstantiationDepthExceeded, &ast.token));
        }
        let (host_module, datatype) = match ast.kind {
            AKind::Identifier => self.find_by_token(module.clone(), &ast.token)?,
            AKind::ExplicitPackage => {
                let package_name = ID::new().add(ast[0].token.spam.deref());
                let dep = module
                    .dependency
                    .iter()
                    .rev()
                    .find(|(nickname, _)| {
                        println!("{:?} {:?}", nickname, package_name);
                        *nickname == package_name 
                    })
                    .map(|(_, dep)| dep)
                    .ok_or_else(|| TypeError::new(TEKind::UnknownPackage, &ast[0].token))?;
                self.find_by_token(dep.clone(), &ast[1].token)?
            }
            AKind::Instantiation => {
                let start = self.context.instance_buffer.len();
                let (id, base_type, mut host_module) = self.create_instance_id(module.clone(), &ast)?;

                if let Some(datatype) = host_module
                    .types
                    .iter()
                    .find(|(name, _)| *name == id)
                    .map(|(_, t)| t.clone())
                {
                    self.context.instance_buffer.truncate(start);
                    return Ok((host_module, datatype.clone()));
                }

                let actual = self.context.instance_buffer.len() - start;
                let supposed = if base_type.ast[0].kind == AKind::Instantiation {
                    base_type.ast[0].len() - 1
                } else {
                    0
                };

                if actual != supposed {
                    return Err(TypeError::new(
                        TEKind::WrongInstantiationArgAmount(actual, supposed),
                        &ast.token,
                    ));
                }

                let old_len = host_module.types.len();
                for (name, param) in base_type.ast[0][1..]
                    .iter()
                    .zip(self.context.instance_buffer[start..].iter())
                {
                    let id = ID::new().add(name.token.spam.deref()).combine(host_module.id);
                    host_module
                        .types
                        .push((id, param.clone()));
                }

                let datatype = match base_type.ast.kind.clone() {
                    AKind::StructDeclaration(visibility) => {
                        let structure =
                            self.connect_struct(host_module.clone(), base_type.clone())?;
                        Cell::new(Datatype {
                            visibility,
                            name: id,
                            kind: DKind::Structure(structure),
                            token_hint: base_type.token_hint.clone(),
                            ast: base_type.ast.clone(),
                            size: u32::MAX,
                        })
                    }
                    _ => unreachable!(),
                };

                if self.immediate {
                    self.context.new_types.push(datatype.clone());
                }

                self.context.instance_buffer.truncate(start);
                host_module.types.truncate(old_len);
                host_module.types.push((id, datatype.clone()));

                (host_module, datatype)
            }
            _ => unreachable!(),
        };

        if datatype.visibility == Visibility::Private && host_module.is_external {
            return Err(TypeError::new(TEKind::AccessingExternalPrivateType, &ast.token));
        }

        if datatype.visibility == Visibility::FilePrivate && module != host_module {
            return Err(TypeError::new(TEKind::AccessingFilePrivateType, &ast.token));
        }

        self.depth -= 1;

        Ok((host_module, datatype))
    }

    fn create_instance_id(
        &mut self,
        module: Cell<Mod>,
        ast: &Ast,
    ) -> Result<(ID, Cell<Datatype>, Cell<Mod>)> {
        let (host_module, base_type) = self.find_or_instantiate(module.clone(), &ast[0])?;
        let mut id = base_type.name;
        for param in ast[1..].iter() {
            let (_, param_type) = self.find_or_instantiate(module.clone(), param)?;
            self.context.instance_buffer.push(param_type.clone());
            id = id.combine(param_type.name);
        }

        Ok((id, base_type, host_module))
    }

    fn find_by_token(
        &mut self,
        module: Cell<Mod>,
        token: &Token,
    ) -> Result<(Cell<Mod>, Cell<Datatype>)> {
        self.find_by_name(module, ID::new().add(token.spam.deref()), false)
            .ok_or_else(|| TypeError::new(TEKind::UnknownType, token))
    }

    fn find_by_name(
        &self,
        module: Cell<Mod>,
        name: ID,
        nested: bool,
    ) -> Option<(Cell<Mod>, Cell<Datatype>)> {
        module
            .types
            .iter()
            .rev()
            .find(|(datatype_name, _)| *datatype_name == name.combine(module.id))
            .map(|(_, datatype)| (module.clone(), datatype.clone()))
            .or_else(|| {
                if nested {
                    None
                } else {
                    module
                        .dependency
                        .iter()
                        .map(|(_, dep)| {
                            (
                                dep.clone(),
                                dep.types
                                    .iter()
                                    .rev()
                                    .find(|(datatype_name, _)| *datatype_name == name.combine(dep.id))
                                    .map(|(_, datatype)| datatype.clone()),
                            )
                        })
                        .find(|(_, res)| res.is_some())
                        .map(|(dep, res)| (dep, res.unwrap().clone()))
                }
            })
            .or_else(|| {
                module
                    .dependency
                    .iter()
                    .map(|(_, dep)| dep.exports.iter())
                    .flatten()
                    .map(|dep| self.find_by_name(dep.clone(), name, true))
                    .find(|res| res.is_some())
                    .map(|res| res.clone().unwrap())
            })
    }

    fn collect(&mut self, mut module: Cell<Mod>) -> Result<()> {
        let module_id = module.id;
        crate::retain!(module.ast, |a| {
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

                    let datatype = Datatype {
                        visibility,
                        size: u32::MAX * !matches!(kind, DKind::Generic) as u32,
                        kind,
                        name: ID::new().add(ident.token.spam.deref()).combine(module_id),
                        token_hint: a[0].token.clone(),
                        ast: std::mem::take(a),
                    };

                    module.types.push((datatype.name, Cell::new(datatype)));

                    false
                }
                _ => true,
            }
        });

        Ok(())
    }
}

pub struct TypeResolverContext {
    instance_buffer: Vec<Cell<Datatype>>,
    new_types: Vec<Cell<Datatype>>,
}

impl TypeResolverContext {
    pub fn new() -> Self {
        Self {
            instance_buffer: Vec::new(),
            new_types: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.instance_buffer.clear();
    }
}

#[derive(Clone, Debug)]
pub struct TypeError {
    kind: TEKind,
    token: Token,
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
}

pub fn test() {
    let builder = ModTreeBuilder::default();
    let mut program = builder.build("src/ir/tests/module_tree/root").unwrap();
    let mut ctx = TypeResolverContext::new();

    
    let flags = settings::Flags::new(settings::builder());
    let isa = cranelift_native::builder().unwrap().finish(flags);

    TypeResolver::new(&mut program, &mut ctx, isa.as_ref()).resolve().unwrap();
}
