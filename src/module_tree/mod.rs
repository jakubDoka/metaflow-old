use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use cranelift::codegen::ir::GlobalValue;
use cranelift::codegen::packed_option::PackedOption;
use cranelift::entity::{EntityRef, EntityList};
use quick_proc::{QuickDefault, QuickSer};

use crate::ast::{AContext, AError, AErrorDisplay, AMainState, AParser, AState, Dep, Vis};
use crate::entities::{Fun, Manifest, Mod, Source, Ty};
use crate::incr;
use crate::lexer::Token;
use crate::lexer::{SourceEnt, Span, TokenDisplay};
use crate::util::pool::Pool;
use crate::util::sdbm::ID;
use crate::util::storage::Table;

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
            AParser::new(self.state, &mut module.a_state, self.context)
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
                let manifest = &self.state.manifests[module.manifest];
                let manifest = if id == manifest.name.hash {
                    module.manifest
                } else {
                    manifest
                        .deps
                        .iter()
                        .find(|dep| dep.0.name.hash == id)
                        .map(|dep| dep.1)
                        .ok_or_else(|| MTError::new(MTEKind::ImportNotFound, import.token))?
                        .clone()
                };

                let dependency =
                    self.load_module(import.path, import.token, manifest, &mut path_buffer)?;
                let dep_ent = &self.state.modules[dependency];
                frontier.push(dependency);
                let nickname = MOD_SALT.add(
                    import
                        .nickname
                        .map(|n| n.hash)
                        .unwrap_or_else(|| dep_ent.name.hash),
                );

                module.dependency.push((nickname, dependency));

                self.state.modules[dependency].dependant.push(module_id);
            }
            module
                .dependency
                .push((MOD_SALT.add(ID::new("builtin")), self.state.builtin_module));

            self.state.modules[module_id] = module;
        }

        let mut order = Vec::with_capacity(self.state.modules.len());
        let mut stack = vec![];
        let mut map = vec![(false, false); self.state.modules.len()];

        if let Some(cycle) =
            self.state
                .modules
                .detect_cycles(module, &mut stack, &mut map, Some(&mut order))
        {
            return Err(MTError::new(
                MTEKind::CyclicDependency(cycle),
                Token::default(),
            ));
        }

        self.state.module_order = order;

        Ok(())
    }

    fn load_module(
        &mut self,
        root_span: Span,
        token: Token,
        manifest_id: Manifest,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        let manifest = &self.state.manifests[manifest_id];
        path_buffer.push(Path::new(manifest.base_path.as_str()));
        path_buffer.push(Path::new(self.state.display(&manifest.root_path)));
        let manifest_name = self.state.display(&manifest.name);
        path_buffer.push(Path::new(manifest_name));

        let root = self.state.display(&root_span);

        let module_path = Path::new(root);

        let name_len = module_path.file_stem().unwrap().len();
        let whole_len = module_path.file_name().unwrap().len();

        let len = root_span.len();
        let name = self
            .state
            .slice_span(&root_span, len - whole_len, len - name_len + whole_len);

        let module_path = module_path
            .strip_prefix(
                module_path
                    .components()
                    .next()
                    .map(|c| c.as_os_str().to_str().unwrap())
                    .unwrap_or(""),
            )
            .unwrap();

        path_buffer.push(module_path);
        path_buffer.set_extension(SOURCE_EXT);

        let id = MOD_SALT.add(ID::new(path_buffer.to_str().unwrap()));

        let modified = std::fs::metadata(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?
            .modified()
            .ok();

        let last_module = if let Some(&module) = self.state.modules.index(id) {
            let source = self.state.modules[module].a_state.l_state.source;
            if modified == Some(self.state.sources[source].modified) {
                path_buffer.clear();
                return Ok(module);
            }
            Some(module)
        } else {
            None
        };

        let content = std::fs::read_to_string(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        let source = SourceEnt {
            name: path_buffer.to_str().unwrap().to_string(),
            content,
            modified: modified.unwrap_or(SystemTime::now()),
        };

        let module_id = if let Some(m) = last_module {
            let mut module = std::mem::take(&mut self.state.modules[m]);
            self.state.sources[module.source] = source;
            module.dependant.clear();
            module.dependency.clear();
            module.clean = false;
            module.seen = false;
            self.state.a_state_for(module.source, &mut module.a_state);
            self.state.modules[m] = module;
            m
        } else {
            let mut module = ModEnt::default();
            module.name = name;
            module.source = self.state.sources.push(source);
            self.state.a_state_for(module.source, &mut module.a_state);
            let (shadowed, m) = self.state.modules.insert(id, module);
            debug_assert!(shadowed.is_none());
            m
        };

        println!("reloaded: {}", path_buffer.display());

        path_buffer.clear();

        Ok(module_id)
    }

    fn load_manifests(&mut self, base_path: &str, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var(CACHE_VAR)
            .map_err(|_| MTError::new(MTEKind::MissingCache, Token::default()))?;

        let id = ID::new(base_path);

        let manifest_id = self.state.manifests.index_or_insert(
            id,
            ManifestEnt {
                id,
                base_path: base_path.to_string(),
                ..ManifestEnt::default()
            },
        );

        let mut frontier = vec![(manifest_id, Token::default(), Option::<Dep>::None)];

        while let Some((manifest_id, token, import)) = frontier.pop() {
            if self.state.manifests[manifest_id].seen {
                continue;
            }
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

            let modified = std::fs::metadata(&path_buffer)
                .map_err(|err| {
                    MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token)
                })?
                .modified()
                .ok();

            let id = ID::new(path_buffer.to_str().unwrap());

            let last_source = if let Some(&manifest) = self.state.manifests.index(id) {
                let source = self.state.manifests[manifest].source;
                if modified == Some(self.state.sources[source].modified) {
                    frontier.extend(
                        self.state.manifests[manifest]
                            .deps
                            .iter()
                            .map(|(dep, manifest)| (*manifest, dep.token, Some(dep.clone()))),
                    );
                    continue;
                }
                Some(source)
            } else {
                None
            };

            let content = std::fs::read_to_string(&path_buffer).map_err(|err| {
                MTError::new(MTEKind::ManifestReadError(path_buffer.clone(), err), token)
            })?;

            let source = SourceEnt {
                name: path_buffer.to_str().unwrap().to_string(),
                content,
                modified: modified.unwrap_or(SystemTime::now()),
            };

            let source = if let Some(last_source) = last_source {
                self.state.sources[last_source] = source;
                last_source
            } else {
                self.state.sources.push(source)
            };
            self.state.manifests[manifest_id].source = source;

            let mut state = AState::default();
            self.state.a_state_for(source, &mut state);
            let manifest = AParser::new(&mut self.state, &mut state, self.context)
                .parse_manifest()
                .map_err(Into::into)?;

            let root_file_span = self
                .state
                .attr_of(&manifest, "root")
                .unwrap_or_else(|| self.state.builtin_span("main.mf"));
            let root_file = self.state.display(&root_file_span);

            let parent_len = Path::new(root_file).parent().unwrap().as_os_str().len();

            let name_len = Path::new(root_file)
                .file_stem()
                .ok_or_else(|| MTError::new(MTEKind::MissingPathStem, token))?
                .len();
            let whole_len = Path::new(root_file).file_name().unwrap().len();

            let len = root_file_span.len();
            let name =
                self.state
                    .slice_span(&root_file_span, len - whole_len, len - whole_len + name_len);
            let root_path = self.state.slice_span(&root_file_span, 0, parent_len);

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

                let manifest = self.state.manifests.index_or_insert(
                    id,
                    ManifestEnt {
                        id,
                        base_path: path_buffer.to_str().unwrap().to_string(),
                        ..ManifestEnt::default()
                    },
                );

                self.state.manifests[manifest_id]
                    .deps
                    .push((dependency.clone(), manifest));

                frontier.push((manifest, dependency.token, Some(dependency.clone())));
            }

            self.state.manifests[manifest_id].seen = true;
        }

        let mut stack = vec![];
        let mut map = vec![(false, false); self.state.manifests.len()];

        if let Some(cycle) =
            self.state
                .manifests
                .detect_cycles(Manifest::new(0), &mut stack, &mut map, None)
        {
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
            .map_err(|err| MTError::new(MTEKind::DownloadError(err), dep.token))?;

        if !code.success() {
            return Err(MTError::new(MTEKind::DownloadFailed, dep.token));
        }

        Ok(())
    }
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

impl TreeStorage<Manifest> for Table<Manifest, ManifestEnt> {
    fn node_dep(&self, id: Manifest, idx: usize) -> Manifest {
        self[id].deps[idx].1
    }

    fn node_len(&self, id: Manifest) -> usize {
        self[id].deps.len()
    }

    fn len(&self) -> usize {
        Table::len(self)
    }
}

pub trait TreeStorage<I: EntityRef + 'static + Debug>
where
    Self: Sized,
{
    fn node_dep(&self, id: I, idx: usize) -> I;
    fn node_len(&self, id: I) -> usize;
    fn len(&self) -> usize;

    fn detect_cycles(
        &self,
        root: I,
        stack: &mut Vec<(I, usize)>,
        lookup: &mut [(bool, bool)],
        mut ordering: Option<&mut Vec<I>>,
    ) -> Option<Vec<I>> {
        debug_assert!(stack.is_empty());
        stack.push((root, 0));

        while let Some(&(node, index)) = stack.last() {
            let (seen, in_recurse) = lookup[node.index()];

            if in_recurse {
                return Some(
                    stack
                        .drain(stack.iter().position(|i| i.0 == node).unwrap()..)
                        .map(|i| i.0)
                        .collect(),
                );
            }

            let done = self.node_len(node) == index;
            if done || seen {
                if !seen {
                    ordering.as_mut().map(|o| o.push(node));
                }
                lookup[node.index()].0 = true;
                stack.pop().unwrap();
                if stack.len() != 0 {
                    lookup[stack[stack.len() - 1].0.index()].1 = false;
                }
                continue;
            }

            let len = stack.len();
            stack[len - 1].1 += 1;
            lookup[node.index()] = (false, true);
            stack.push((self.node_dep(node, index), 0));
        }

        None
    }
}

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct ManifestEnt {
    pub id: ID,
    pub base_path: String,
    pub name: Span,
    pub root_path: Span,
    pub deps: Vec<(Dep, Manifest)>,
    #[default(Source::new(0))]
    pub source: Source,
    pub seen: bool,
}

#[derive(Debug, Clone, QuickSer)]
pub struct MTState {
    pub a_main_state: AMainState,
    pub builtin_module: Mod,
    pub manifests: Table<Manifest, ManifestEnt>,
    pub modules: Table<Mod, ModEnt>,
    pub module_order: Vec<Mod>,
}

crate::inherit!(MTState, a_main_state, AMainState);

impl Default for MTState {
    fn default() -> Self {
        let mut s = Self {
            a_main_state: AMainState::default(),
            builtin_module: Mod::new(0),
            manifests: Table::new(),
            modules: Table::new(),
            module_order: Vec::new(),
        };

        let source = SourceEnt {
            name: "builtin.mf".to_string(),
            content: include_str!("builtin.mf").to_string(),
            ..Default::default()
        };
        let source = s.sources.push(source);

        let mut builtin_module = ModEnt {
            id: MOD_SALT.add(ID::new("builtin")),
            ..Default::default()
        };
        s.a_state_for(source, &mut builtin_module.a_state);

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
                .map(|dep| (dep.1, self.modules[dep.1].id)),
        );
    }

    pub fn find_dep(&self, inside: Mod, name: &Token) -> Option<Mod> {
        let id = MOD_SALT.add(name.span.hash);
        self.modules[inside]
            .dependency
            .iter()
            .find(|dep| dep.0 == id)
            .map(|dep| dep.1)
    }

    pub fn can_access(&self, from: Mod, to: Mod, vis: Vis) -> bool {
        matches!(
            (
                from == to,
                self.modules[from].manifest == self.modules[to].manifest,
                vis
            ),
            (true, ..) | (_, true, Vis::None | Vis::Public) | (.., Vis::Public)
        )
    }
}

#[derive(Debug, Clone, Default)]
pub struct MTContext {
    pub a_context: AContext,
    pub pool: Pool,
}

crate::inherit!(MTContext, a_context, AContext);

#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct ModEnt {
    pub id: ID,
    pub name: Span,
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,
    pub a_state: AState,
    #[default(Manifest::new(0))]
    pub manifest: Manifest,
    
    pub functions: EntityList<Fun>,
    pub types: EntityList<Ty>,
    pub globals: EntityList<GlobalValue>,
    pub entry_point: PackedOption<Fun>,

    pub clean: bool,
    pub seen: bool,
}

crate::inherit!(ModEnt, a_state, AState);

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
                writeln!(f, "  {}", self.state.sources[self.state.modules[id].a_state.l_state.source].name)?;
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
    const PATH: &str = "src/module_tree/test_project";

    let (mut state, hint) = incr::load_data(PATH, ID(0)).unwrap_or_default();
    let mut context = MTContext::default();

    MTParser::new(&mut state, &mut context)
        .parse(PATH)
        .map_err(|e| panic!("{}", MTErrorDisplay::new(&state, &e)))
        .unwrap();

    incr::save_data(PATH, &state, ID(0), Some(hint)).unwrap();
}
