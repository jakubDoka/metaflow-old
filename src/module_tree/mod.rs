use std::path::{Path, PathBuf};
use std::ops::{Deref, DerefMut};

use crate::ast::{AstError, AstParser, AstState, Dep, Import};
use crate::lexer::Lexer;
use crate::util::sdbm::{SdbmHashState, ID};
use crate::util::storage::{IndexPointer, Table};
use crate::{ast::AstContext, lexer::Token, util::storage::List};

type Result<T = ()> = std::result::Result<T, MTError>;

pub const MOD_SALT: ID = ID(0x64739273646);
pub const SOURCE_EXT: &str = "mf";
pub const MANIFEST_EXT: &str = "mfm";

pub struct MTParser<'a> {
    pub state: &'a mut MTState,
    pub context: &'a mut MTContext,
}

impl<'a> MTParser<'a> {
    pub fn new(state: &'a mut MTState, context: &'a mut MTContext) -> Self {
        Self { state, context }
    }

    pub fn parse(&mut self, root: &str) -> Result {
        let mut path_buffer = PathBuf::new();

        self.load_manifests(root, &mut path_buffer)?;

        let root_manifest_id = Manifest::new(0);

        let root_manifest_hash = self.state.manifests[root_manifest_id].id;
        
        let builtin_module = ModEnt {
            id: MOD_SALT.add("builtin").combine(root_manifest_hash),
            dependency: vec![],
            dependant: vec![],
            ast: AstState::default(),
            manifest: root_manifest_id,
        };

        self.state.builtin_module = self.state.modules.insert(builtin_module.id, builtin_module).1;
        
        let root_manifest_name = self.state.manifests[root_manifest_id].name;

        let module = self.load_module(
            root_manifest_name,
            Token::default(),
            root_manifest_id,
            &mut path_buffer,
        )?;
        let mut frontier = vec![module];

        while let Some(module_id) = frontier.pop() {
            let mut module = std::mem::take(&mut self.state.modules[module_id]);
            AstParser::new(&mut module.ast, &mut self.context.ast)
                .take_imports()
                .map_err(Into::into)?;
            for import in module.ast.imports.iter() {
                let manifest = if import.external {
                    let head = Path::new(import.path)
                        .components()
                        .next()
                        .unwrap()
                        .as_os_str()
                        .to_str()
                        .unwrap();
                    let id = ID(0).add(head);
                    self.state.manifests[module.manifest]
                        .deps
                        .iter()
                        .find(|dep| dep.0 == id)
                        .map(|dep| dep.1)
                        .ok_or_else(|| MTError::new(MTEKind::ImportNotFound, import.token.clone()))?
                        .clone()
                } else {
                    module.manifest
                };

                let dependency = self.load_module(
                    import.path,
                    import.token.clone(),
                    manifest,
                    &mut path_buffer,
                )?;
                frontier.push(dependency);
                let nickname = MOD_SALT.add(import.nickname);
                module.dependency.push((nickname, dependency));
                module.dependant.push(module_id);
            }
            module.dependency.push((MOD_SALT.add("builtin"), self.state.builtin_module));
            self.state.modules[module_id] = module;
        }

        let mut stack = vec![];

        if let Some(cycle) = detect_cycles(&self.state.modules, module, &mut stack) {
            return Err(MTError::new(
                MTEKind::CyclicDependency(cycle),
                Token::default(),
            ));
        }


        let mut module_order = OrderingContext::new();

        create_order(&self.state.modules, module, &mut module_order);

        module_order.result();

        self.state.module_order = module_order.frontier;


        Ok(())
    }

    fn load_module(
        &mut self,
        root: &str,
        token: Token,
        manifest_id: Manifest,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        let manifest = &self.state.manifests[manifest_id];
        path_buffer.push(Path::new(manifest.base_path.as_str()));
        path_buffer.push(Path::new(manifest.root_path));
        path_buffer.push(Path::new(manifest.name));

        let module_path = Path::new(root);
        let module_path = module_path
            .strip_prefix(
                module_path
                    .components()
                    .next()
                    .map(|c| c.as_os_str().to_str().unwrap())
                    .unwrap_or(""),
            )
            .unwrap();
        
        if module_path == Path::new("") && manifest.name != root {
            return Err(MTError::new(
                MTEKind::DisplacedModule,
                token,
            ));
        }

        path_buffer.push(module_path);
        path_buffer.set_extension(SOURCE_EXT);

        let id = MOD_SALT.add(path_buffer.to_str().unwrap());

        if let Some(module) = self.state.modules.index(id) {
            path_buffer.clear();
            return Ok(*module);
        }

        let content = std::fs::read_to_string(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        let lexer = Lexer::new(path_buffer.to_str().unwrap().to_string(), content);
        path_buffer.clear();
        let ast = AstState::new(lexer);

        let ent = ModEnt {
            id,
            dependency: vec![],
            dependant: vec![],
            ast,
            manifest: manifest_id,
        };

        let (_, module) = self.state.modules.insert(id, ent);

        Ok(module)
    }

    fn load_manifests(&mut self, base_path: &str, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var("METAFLOW_CACHE")
            .map_err(|_| MTError::new(MTEKind::MissingCache, Token::default()))?;

        let manifest_id = self.state.manifests.add(ManifestEnt {
            base_path: base_path.to_string(),
            ..ManifestEnt::default()
        });

        let mut frontier = vec![(manifest_id, Token::default(), Option::<Dep>::None)];

        while let Some((manifest_id, token, import)) = frontier.pop() {
            path_buffer.clear();
            path_buffer.push(Path::new(
                self.state.manifests[manifest_id].base_path.as_str(),
            ));

            if let Some(import) = import {
                if !path_buffer.exists() {
                    if import.external {
                        self.download(import, manifest_id)?;
                    } else {
                        return Err(MTError::new(
                            MTEKind::MissingDependency(path_buffer.clone()),
                            token,
                        ));
                    }
                }
            }

            path_buffer.push(Path::new("project"));
            path_buffer.set_extension(MANIFEST_EXT);

            let content = std::fs::read_to_string(&path_buffer).map_err(|err| {
                MTError::new(
                    MTEKind::ManifestReadError(path_buffer.clone(), err),
                    token.clone(),
                )
            })?;

            let full_path = path_buffer
                .canonicalize()
                .unwrap()
                .to_str()
                .ok_or_else(|| MTError::new(MTEKind::InvalidPathEncoding, token.clone()))?
                .to_string();

            let lexer = Lexer::new(full_path, content);
            let mut state = AstState::new(lexer);
            let manifest = AstParser::new(&mut state, &mut self.context.ast)
                .parse_manifest()
                .map_err(Into::into)?;

            let root_file = manifest
                .attrs
                .iter()
                .find(|(name, _)| *name == "root")
                .map(|(_, value)| *value)
                .unwrap_or("main.mf");

            let parent = Path::new(root_file).parent().unwrap().to_str().unwrap();

            let name = Path::new(root_file).file_stem().unwrap().to_str().unwrap();

            let manifest_ent = &mut self.state.manifests[manifest_id];
            manifest_ent.name = name;
            manifest_ent.root_path = parent;

            for dependency in &manifest.deps {
                path_buffer.clear();
                if dependency.external {
                    path_buffer.push(Path::new(&cache_root));
                    path_buffer.push(Path::new(dependency.path));
                    path_buffer.push(Path::new(dependency.version));
                } else {
                    path_buffer.push(Path::new(base_path));
                    path_buffer.push(Path::new(dependency.path));
                }

                let id = ID(0).add(path_buffer.to_str().unwrap());

                let manifest = self
                    .state
                    .manifests
                    .iter()
                    .find(|(_, m)| m.id == id)
                    .map(|(id, _)| id);

                let manifest = manifest.unwrap_or_else(|| {
                    self.state.manifests.add(ManifestEnt {
                        id,
                        base_path: path_buffer.to_str().unwrap().to_string(),
                        ..ManifestEnt::default()
                    })
                });

                let id = ID(0).add(dependency.name);

                self.state.manifests[manifest_id].deps.push((id, manifest));

                frontier.push((manifest, dependency.token.clone(), Some(dependency.clone())));
            }

            self.context.ast.temp_manifest = manifest;
        }

        let mut stack = vec![];

        if let Some(cycle) = detect_cycles(&self.state.manifests, Manifest::new(0), &mut stack) {
            return Err(MTError::new(MTEKind::CyclicManifests(cycle), Token::default()));
        }

        path_buffer.clear();

        Ok(())
    }

    pub fn download(&mut self, dep: Dep, manifest: Manifest) -> Result {
        let base_path = &self.state.manifests[manifest].base_path;

        std::fs::create_dir_all(base_path).unwrap();

        let link = format!("https://{}", &dep.path);

        let code = std::process::Command::new("git")
            .args(&[
                "clone",
                "--depth",
                "1",
                "--branch",
                &dep.version,
                &link,
                base_path,
            ])
            .status()
            .map_err(|err| MTError::new(MTEKind::DownloadError(err), dep.token.clone()))?;

        if !code.success() {
            return Err(MTError::new(MTEKind::DownloadFailed, dep.token.clone()));
        }

        Ok(())
    }
}

pub fn create_order<I: IndexPointer + 'static, S: TreeStorage<I>>(
    storage: &S,
    root: I,
    ctx: &mut OrderingContext<I>,
) {
    ctx.clear();
    let len = storage.len();
    ctx.result.reserve(len * 2);
    ctx.frontier.reserve(len * 4);
    ctx.frontier.push(root);
    ctx.lookup.resize(len, None);

    let mut i = 0;

    while i < ctx.frontier.len() {
        let node = ctx.frontier[i];
        if let Some(seen_at) = ctx.lookup[node.raw()] {
            ctx.result[seen_at] = None;
            ctx.lookup[node.raw()] = Some(ctx.result.len());
        }
        ctx.result.push(Some(node));
        let last = ctx.frontier.len() - 1;
        let last = ctx.frontier[last];

        ctx.frontier.extend(
            iter(storage, node)
                .filter(|module| *module != last),
        );
        i += 1;
    }
}

#[derive(Debug, Clone)]
pub struct OrderingContext<I> {
    pub lookup: Vec<Option<usize>>,
    pub result: Vec<Option<I>>,
    pub frontier: Vec<I>,
}

impl<I> OrderingContext<I> {
    pub fn new() -> Self {
        Self {
            lookup: Vec::new(),
            result: Vec::new(),
            frontier: Vec::new(),
        }
    }

    pub fn result(&mut self) -> &[I] {
        let mut frontier = std::mem::take(&mut self.frontier);
        frontier.clear();
        frontier.extend(self.result.drain(..).filter_map(|node| node));
        self.frontier = frontier;
        &self.frontier
    }

    pub fn clear(&mut self) {
        self.lookup.clear();
        self.result.clear();
        self.frontier.clear();
    }
}

impl<I> Default for OrderingContext<I> {
    fn default() -> Self {
        Self::new()
    }
}

pub fn detect_cycles<I: IndexPointer, S: TreeStorage<I>>(
    storage: &S,
    root: I,
    stack: &mut Vec<(I, usize)>,
) -> Option<Vec<I>> {
    stack.clear();
    stack.reserve(storage.len());
    stack.push((root, 0));

    while let Some(&(node_id, idx)) = stack.last() {
        let len = storage.node_len(node_id);
        if idx >= len {
            stack.pop();
        } else {
            let len = stack.len();
            stack[len - 1].1 += 1;
            let dependency = storage.node_dep(node_id, idx);
            if let Some(position) = stack.iter().position(|d| d.0 == dependency) {
                let mut log = Vec::with_capacity(stack.len() - position);

                log.extend(stack[position..].iter().map(|&(id, _)| id));

                return Some(log);
            } else {
                stack.push((dependency, 0));
            }
        }
    }

    None
}


fn iter<'a, I: 'static + Clone + Copy, T: TreeStorage<I>>(storage: &'a T, id: I) -> impl Iterator<Item = I> + 'a {
    (0..storage.node_len(id)).map(move |i| storage.node_dep(id, i))
}

impl TreeStorage<Mod> for Table<Mod, ModEnt> {
    fn node_dep(&self, id: Mod, idx: usize) -> Mod {
        self[id].dependency[idx].1
    }

    fn node_len(&self, id: Mod) -> usize {
        self[id].dependency.len()
    }

    fn len(&self) -> usize {
        Table::len(self)
    }
}

impl TreeStorage<Manifest> for List<Manifest, ManifestEnt> {
    fn node_dep(&self, id: Manifest, idx: usize) -> Manifest {
        self[id].deps[idx].1
    }

    fn node_len(&self, id: Manifest) -> usize {
        self[id].deps.len()
    }

    fn len(&self) -> usize {
        List::len(self)
    }
}

pub trait TreeStorage<I> {
    fn node_dep(&self, id: I, idx: usize) -> I;
    fn node_len(&self, id: I) -> usize;
    fn len(&self) -> usize;
}

crate::index_pointer!(Manifest);

#[derive(Debug, Clone, Default)]
pub struct ManifestEnt {
    pub id: ID,
    pub base_path: String,
    pub name: &'static str,
    pub root_path: &'static str,
    pub deps: Vec<(ID, Manifest)>,
}

#[derive(Debug, Clone, Default)]
pub struct MTState {
    pub builtin_module: Mod,
    pub manifests: List<Manifest, ManifestEnt>,
    pub modules: Table<Mod, ModEnt>,
    pub module_order: Vec<Mod>,
}

impl MTState {
    pub fn collect_scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        let module_ent = &self.modules[module];
        buffer.push((module, module_ent.id));
        buffer.extend(module_ent.dependency.iter().map(|&(_, id)| (id, self.modules[id].id)));
    }

    pub fn find_dep(&self, inside: Mod, name: &Token) -> Option<Mod> {
        let id = ID(0).add(name.spam.raw());
        self
            .modules[inside]
            .dependency.iter()
            .find(|&(m_id, _)| *m_id == id)
            .map(|&(_, id)| id)
    } 
}

#[derive(Debug, Clone, Default)]
pub struct MTContext {
    pub ast: AstContext,
    pub import_buffer: Vec<Import>,
}

crate::inherit!(MTContext, ast, AstContext);

crate::index_pointer!(Mod);

#[derive(Debug, Clone)]
pub struct ModEnt {
    pub id: ID,
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,
    pub ast: AstState,
    pub manifest: Manifest,
}

impl Default for ModEnt {
    fn default() -> Self {
        Self {
            id: ID(0),
            dependency: vec![],
            dependant: vec![],
            ast: Default::default(),
            manifest: Manifest::new(0),
        }
    }
}

#[derive(Debug)]
pub struct MTError {
    pub kind: MTEKind,
    pub token: Token,
}

impl MTError {
    pub fn new(kind: MTEKind, token: Token) -> Self {
        Self { kind, token }
    }
}

impl Into<MTError> for AstError {
    fn into(self) -> MTError {
        MTError {
            kind: MTEKind::AstError(self),
            token: Token::default(),
        }
    }
}

#[derive(Debug)]
pub enum MTEKind {
    InvalidPathEncoding,
    MissingPathStem,
    MissingCache,
    ImportNotFound,
    DisplacedModule,
    FileReadError(PathBuf, std::io::Error),
    ManifestReadError(PathBuf, std::io::Error),
    AstError(AstError),
    CyclicDependency(Vec<Mod>),
    CyclicManifests(Vec<Manifest>),
    MissingDependency(PathBuf),
    DownloadError(std::io::Error),
    DownloadFailed,
}

pub fn test() {
    let mut state = MTState::default();
    let mut context = MTContext::default();

    let mut parser = MTParser::new(&mut state, &mut context);
    parser.parse("src/module_tree/test_project").unwrap();
}
