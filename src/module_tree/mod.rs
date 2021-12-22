use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};

use crate::ast::{AContext, AError, AErrorDisplay, AMainState, AParser, AState, Dep};
use crate::lexer::{SourceEnt, Spam, TokenDisplay};
use crate::util::pool::{Pool, PoolRef};
use crate::util::sdbm::ID;
use crate::util::storage::{IndexPointer, Table};
use crate::{lexer::Token, util::storage::List};

type Result<T = ()> = std::result::Result<T, MTError>;

pub const CACHE_VAR: &str = "METAFLOW_CACHE";
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

        let root_manifest_name = self.state.manifests[root_manifest_id].name.clone();

        let module = self.load_module(
            root_manifest_name,
            Token::default(),
            root_manifest_id,
            &mut path_buffer,
        )?;
        let mut frontier = vec![module];

        let mut imports = self.context.pool.get();

        while let Some(module_id) = frontier.pop() {
            let mut module = std::mem::take(&mut self.state.modules[module_id]);
            AParser::new(&mut self.state, &mut module.ast, &mut self.context.ast)
                .take_imports(&mut imports)
                .map_err(Into::into)?;
            for import in imports.drain(..) {
                let path = self.state.display(&import.path);
                let head = Path::new(path)
                    .components()
                    .next()
                    .unwrap()
                    .as_os_str()
                    .to_str()
                    .unwrap();
                let id = ID::new(head);
                let manifest = self.state.manifests[module.manifest]
                    .deps
                    .iter()
                    .find(|dep| dep.0 == id)
                    .map(|dep| dep.1)
                    .or_else(|| {
                        if head
                            == self
                                .state
                                .display(&self.state.manifests[module.manifest].name)
                        {
                            Some(module.manifest)
                        } else {
                            None
                        }
                    })
                    .ok_or_else(|| MTError::new(MTEKind::ImportNotFound, import.token.clone()))?
                    .clone();

                let dependency = self.load_module(
                    import.path,
                    import.token.clone(),
                    manifest,
                    &mut path_buffer,
                )?;
                frontier.push(dependency);
                let nickname = MOD_SALT.add(
                    import
                        .nickname
                        .map(|n| n.hash)
                        .unwrap_or_else(|| self.state.modules[dependency].name.hash),
                );
                module.dependency.push((nickname, dependency));
                module.dependant.push(module_id);
            }
            module
                .dependency
                .push((MOD_SALT.add(ID::new("builtin")), self.state.builtin_module));
            self.state.modules[module_id] = module;
        }

        let mut stack = vec![];

        if let Some(cycle) = detect_cycles(&self.state.modules, module, &mut stack) {
            return Err(MTError::new(
                MTEKind::CyclicDependency(cycle),
                Token::default(),
            ));
        }

        let order = create_order(&self.state.modules, module, &mut self.context.pool);

        self.state.module_order = order.deref().clone();

        Ok(())
    }

    fn load_module(
        &mut self,
        root_spam: Spam,
        token: Token,
        manifest_id: Manifest,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        let manifest = &self.state.manifests[manifest_id];
        path_buffer.push(Path::new(manifest.base_path.as_str()));
        path_buffer.push(Path::new(self.state.display(&manifest.root_path)));
        let manifest_name = self.state.display(&manifest.name);
        path_buffer.push(Path::new(manifest_name));

        let root = self.state.display(&root_spam);

        let module_path = Path::new(root);

        let name_len = module_path.file_stem().unwrap().len();
        let whole_len = module_path.file_name().unwrap().len();

        let name = self.state.new_spam(
            root_spam.source,
            root_spam.range.end - whole_len..root_spam.range.end + whole_len - name_len,
        );

        let module_path = module_path
            .strip_prefix(
                module_path
                    .components()
                    .next()
                    .map(|c| c.as_os_str().to_str().unwrap())
                    .unwrap_or(""),
            )
            .unwrap();

        if module_path == Path::new("") && manifest_name != root {
            return Err(MTError::new(MTEKind::DisplacedModule, token));
        }

        path_buffer.push(module_path);
        path_buffer.set_extension(SOURCE_EXT);

        let id = MOD_SALT.add(ID::new(path_buffer.to_str().unwrap()));

        if let Some(&module) = self.state.modules.index(id) {
            path_buffer.clear();
            return Ok(module);
        }

        let content = std::fs::read_to_string(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        let source = SourceEnt {
            name: path_buffer.to_str().unwrap().to_string(),
            content,
        };

        let source = self.state.sources.add(source);
        let ast = self.state.a_state_for(source);

        path_buffer.clear();

        let ent = ModEnt {
            id,
            dependency: vec![],
            dependant: vec![],
            ast,
            manifest: manifest_id,
            name,
        };

        let (_, module) = self.state.modules.insert(id, ent);

        Ok(module)
    }

    fn load_manifests(&mut self, base_path: &str, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var(CACHE_VAR)
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

            let source = SourceEnt {
                name: full_path,
                content,
            };
            let source = self.state.sources.add(source);

            let mut state = self.state.a_state_for(source);
            let manifest = AParser::new(&mut self.state, &mut state, &mut self.context.ast)
                .parse_manifest()
                .map_err(Into::into)?;

            let root_file_spam = self
                .state
                .attr_of(&manifest, "root")
                .unwrap_or_else(|| self.state.builtin_spam("main.mf"));
            let root_file = self.state.display(&root_file_spam);

            let parent_len = Path::new(root_file).parent().unwrap().as_os_str().len();

            let name_len = Path::new(root_file)
                .file_stem()
                .ok_or_else(|| MTError::new(MTEKind::MissingPathStem, token.clone()))?
                .len();
            let whole_len = Path::new(root_file).file_name().unwrap().len();

            let name = self.state.new_spam(
                root_file_spam.source,
                root_file_spam.range.end - whole_len
                    ..root_file_spam.range.end - whole_len + name_len,
            );

            let root_path = self.state.new_spam(
                root_file_spam.source,
                root_file_spam.range.start..root_file_spam.range.start + parent_len,
            );

            let manifest_ent = &mut self.state.manifests[manifest_id];
            manifest_ent.name = name;
            manifest_ent.root_path = root_path;

            for dependency in &manifest.deps {
                path_buffer.clear();
                let dependency_path = self.state.display(&dependency.path);
                if dependency.external {
                    path_buffer.push(Path::new(&cache_root));
                    path_buffer.push(Path::new(dependency_path));
                    path_buffer.push(Path::new(self.state.display(&dependency.version)));
                } else {
                    path_buffer.push(Path::new(base_path));
                    path_buffer.push(Path::new(dependency_path));
                }

                let id = ID::new(path_buffer.to_str().unwrap());

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

                let id = dependency.name.hash;

                self.state.manifests[manifest_id].deps.push((id, manifest));

                frontier.push((manifest, dependency.token.clone(), Some(dependency.clone())));
            }
        }

        let mut stack = vec![];

        if let Some(cycle) = detect_cycles(&self.state.manifests, Manifest::new(0), &mut stack) {
            return Err(MTError::new(
                MTEKind::CyclicManifests(cycle),
                Token::default(),
            ));
        }

        path_buffer.clear();

        Ok(())
    }

    pub fn download(&mut self, dep: Dep, manifest: Manifest) -> Result {
        let base_path = &self.state.manifests[manifest].base_path;

        std::fs::create_dir_all(base_path).unwrap();

        let link = format!("https://{}", self.state.display(&dep.path));

        let code = std::process::Command::new("git")
            .args(&[
                "clone",
                "--depth",
                "1",
                "--branch",
                self.state.display(&dep.version),
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
    pool: &mut Pool,
) -> PoolRef<I> {
    let len = storage.len();
    let mut result = pool.get();
    result.reserve(len * 2);
    let mut frontier = pool.get();
    frontier.reserve(len * 4);
    frontier.push(root);
    let mut lookup = pool.get();
    lookup.resize(len, None);

    let mut i = 0;

    while i < frontier.len() {
        let node = frontier[i];
        if let Some(seen_at) = lookup[node.raw()] {
            result[seen_at] = None;
            lookup[node.raw()] = Some(result.len());
        }
        result.push(Some(node));
        let last = frontier.len() - 1;
        let last = frontier[last];

        frontier.extend(iter(storage, node).filter(|module| *module != last));
        i += 1;
    }

    let mut final_result = pool.get();
    final_result.extend(result.iter().filter_map(|node| node.clone()));
    final_result
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

fn iter<'a, I: 'static + Clone + Copy, T: TreeStorage<I>>(
    storage: &'a T,
    id: I,
) -> impl Iterator<Item = I> + 'a {
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
    pub name: Spam,
    pub root_path: Spam,
    pub deps: Vec<(ID, Manifest)>,
}

#[derive(Debug, Clone)]
pub struct MTState {
    pub a_main_state: AMainState,
    pub builtin_module: Mod,
    pub manifests: List<Manifest, ManifestEnt>,
    pub modules: Table<Mod, ModEnt>,
    pub module_order: Vec<Mod>,
}

crate::inherit!(MTState, a_main_state, AMainState);

impl Default for MTState {
    fn default() -> Self {
        let mut s = Self {
            a_main_state: AMainState::default(),
            builtin_module: Mod::new(0),
            manifests: List::new(),
            modules: Table::new(),
            module_order: Vec::new(),
        };

        let source = SourceEnt {
            name: "builtin.mf".to_string(),
            content: include_str!("builtin.mf").to_string(),
        };
        let source = s.sources.add(source);

        let ast = s.a_state_for(source);

        let builtin_module = ModEnt {
            id: MOD_SALT.add(ID::new("builtin")),
            ast,
            ..Default::default()
        };

        s.builtin_module = s.modules.insert(builtin_module.id, builtin_module).1;

        s
    }
}

impl MTState {
    pub fn collect_scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
        let module_ent = &self.modules[module];
        buffer.push((module, module_ent.id));
        buffer.extend(
            module_ent
                .dependency
                .iter()
                .map(|&(_, id)| (id, self.modules[id].id)),
        );
    }

    pub fn find_dep(&self, inside: Mod, name: &Token) -> Option<Mod> {
        let id = MOD_SALT.add(name.spam.hash);
        self.modules[inside]
            .dependency
            .iter()
            .find(|&(m_id, _)| *m_id == id)
            .map(|&(_, id)| id)
    }
}

#[derive(Debug, Clone, Default)]
pub struct MTContext {
    pub ast: AContext,
    pub pool: Pool,
}

crate::inherit!(MTContext, ast, AContext);

crate::index_pointer!(Mod);

#[derive(Debug, Clone, Default)]
pub struct ModEnt {
    pub id: ID,
    pub name: Spam,
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,
    pub ast: AState,
    pub manifest: Manifest,
}

crate::def_displayer!(
    MTErrorDisplay,
    MTState,
    MTError,
    |self, f| {
        MTEKind::InvalidPathEncoding => {
            writeln!(f, "invalid path encoding")?;
        },
        MTEKind::MissingPathStem => {
            writeln!(f, "root attribute of the manifest if missing path stem (simply is not pointing to file)")?;
        },
        MTEKind::MissingCache => {
            writeln!(f, "missing dependency cache, the environment variable 'METAFLOW_CACHE' has to be set")?;
        },
        MTEKind::ImportNotFound => {
            writeln!(
                f,
                "root of import not found inside manifest, nor it is root of current project"
            )?;
        },
        MTEKind::DisplacedModule => {
            writeln!(f, "module violates project structure, all submodules have to be placed in directory with the name of root module that are in same directory as root module")?;
        },
        MTEKind::FileReadError(path, error) => {
            writeln!(f, "error reading module '{}', this may be due to invalid project structure, original error: {}", path.as_os_str().to_str().unwrap(), error)?;
        },
        MTEKind::ManifestReadError(path, error) => {
            writeln!(
                f,
                "error reading manifest '{}', original error: {}",
                path.as_os_str().to_str().unwrap(),
                error
            )?;
        },
        MTEKind::AError(error) => {
            writeln!(f, "{}", AErrorDisplay::new(self.state, error))?;
        },
        MTEKind::CyclicDependency(cycle) => {
            writeln!(f, "cyclic module dependency detected:")?;
            for &id in cycle.iter() {
                writeln!(f, "  {}", self.state.sources[self.state.modules[id].ast.l_state.source].name)?;
            }
        },
        MTEKind::CyclicManifests(cycle) => {
            writeln!(f, "cyclic package dependency detected:")?;
            for &id in cycle.iter() {
                writeln!(f, "  {}", self.state.display(&self.state.manifests[id].name))?;
            }
        },
        MTEKind::MissingDependency(path) => {
            writeln!(
                f,
                "missing dependency '{}'",
                path.as_os_str().to_str().unwrap()
            )?;
        },
        MTEKind::DownloadError(error) => {
            writeln!(f, "error downloading dependency, original error: {}", error)?;
        },
        MTEKind::DownloadFailed => {
            writeln!(f, "failed to download dependency")?;
        },
    }
);

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

impl Into<MTError> for AError {
    fn into(self) -> MTError {
        MTError {
            kind: MTEKind::AError(self),
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
    AError(AError),
    CyclicDependency(Vec<Mod>),
    CyclicManifests(Vec<Manifest>),
    MissingDependency(PathBuf),
    DownloadError(std::io::Error),
    DownloadFailed,
}

pub fn test() {
    let mut state = MTState::default();
    let mut context = MTContext::default();

    MTParser::new(&mut state, &mut context)
        .parse("src/module_tree/test_project")
        .unwrap();
}
