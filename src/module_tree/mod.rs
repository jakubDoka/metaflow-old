use std::path::{Path, PathBuf};

use crate::ast::{AstError, AstParser, AstState, Dep, Import};
use crate::lexer::Lexer;
use crate::util::sdbm::{SdbmHashState, ID};
use crate::util::storage::{Map, SymID};
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

        path_buffer.clear();

        let root_manifest_id = Manifest::new(0);

        let root_manifest_name = self.state.manifests[root_manifest_id].name;

        let module =
            self.load_module(root_manifest_name, Token::default(), root_manifest_id, &mut path_buffer)?;
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
                    self
                        .state
                        .manifests[module.manifest]
                        .deps
                        .get(ID(0).add(head))
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
                self.state.modules[dependency].dependant.push(module_id);
            }
        }

        self.detect_cycles()?;

        self.create_order()?;

        Ok(())
    }

    fn create_order(&mut self) -> Result {
        let mut result = Vec::with_capacity(self.state.modules.len() * 2);
        let mut frontier = Vec::with_capacity(self.state.modules.len() * 4);
        frontier.push(Mod::new(0));
        let mut lookup = std::iter::repeat(None)
            .take(self.state.modules.len())
            .collect::<Vec<_>>();

        let mut i = 0;

        while i < frontier.len() {
            let node = frontier[i];
            if let Some(seen_at) = lookup[node.0] {
                result[seen_at] = None;
                lookup[node.0] = Some(result.len());
            }
            result.push(Some(node));
            let last = frontier.len() - 1;
            let last = frontier[last];
            frontier.extend(
                self.state.modules[node]
                    .dependency
                    .iter()
                    .filter(|(_, module)| *module != last)
                    .map(|(_, module)| *module),
            );
            i += 1;
        }

        self.state.order.reserve(self.state.modules.len());
        self.state.order.extend(
            result
                .drain(..)
                .filter(|module| module.is_some())
                .map(|module| module.unwrap()),
        );

        Ok(())
    }

    fn detect_cycles(&mut self) -> Result {
        let mut stack = Vec::with_capacity(self.state.modules.len());
        stack.push((Mod::new(0), 0));

        while let Some(&(module_id, idx)) = stack.last() {
            let module = &self.state.modules[module_id];
            if idx >= module.dependency.len() {
                stack.pop();
            } else {
                let len = stack.len();
                stack[len - 1].1 += 1;
                let (_, dependency) = module.dependency[idx];
                if let Some(position) = stack.iter().position(|d| d.0 == dependency) {
                    let mut log = String::new();

                    for module in stack[position..]
                        .iter()
                        .chain(std::iter::once(&stack[position]))
                    {
                        log.push_str("  ");
                        log.push_str(self.state.modules[module.0].ast.file_name());
                        log.push('\n');
                    }

                    return Err(MTError::new(
                        MTEKind::CyclicDependency(log),
                        module.ast.imports[idx].token.clone(),
                    ));
                } else {
                    stack.push((dependency, 0));
                }
            }
        }

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
        
        path_buffer.push(module_path);
        path_buffer.set_extension(SOURCE_EXT);

        let id = MOD_SALT.add(path_buffer.to_str().unwrap());

        if let Some(module) = self.state.module_map.get(id) {
            return Ok(*module);
        }

        let content = std::fs::read_to_string(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        let lexer = Lexer::new(path_buffer.to_str().unwrap().to_string(), content);
        path_buffer.clear();
        let ast = AstState::new(lexer);

        let ent = MTEnt {
            dependency: vec![],
            dependant: vec![],
            ast,
            manifest: manifest_id,
        };

        let module = self.state.modules.add(ent);

        self.state.module_map.insert(id, module);

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
            
            let root_file = manifest.attrs
                .iter()
                .find(|(name, _)| *name == "root")
                .map(|(_, value)| *value)
                .unwrap_or("main.mf");

            let parent = Path::new(root_file)
                .parent()
                .unwrap()
                .to_str()
                .unwrap();
            
            let name = Path::new(root_file)
                .file_stem()
                .unwrap()
                .to_str()
                .unwrap();

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

                self.state.manifests[manifest_id].deps.insert(id, manifest);

                frontier.push((manifest, dependency.token.clone(), Some(dependency.clone())));
            }

            self.context.ast.temp_manifest = manifest;
        }

        Ok(())
    }

    pub fn download(&mut self, dep: Dep, manifest: Manifest) -> Result {
        let base_path = &self.state.manifests[manifest].base_path;

        std::fs::create_dir_all(base_path).unwrap();

        let link = format!("https://{}",  &dep.path);

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

crate::sym_id!(Manifest);

#[derive(Debug, Clone, Default)]
pub struct ManifestEnt {
    pub id: ID,
    pub base_path: String,
    pub name: &'static str,
    pub root_path: &'static str,
    pub deps: Map<Manifest>,
}

#[derive(Debug, Clone, Default)]
pub struct MTState {
    pub manifests: List<Manifest, ManifestEnt>,
    pub module_map: Map<Mod>,
    pub modules: List<Mod, MTEnt>,
    pub order: Vec<Mod>,
}

#[derive(Debug, Clone, Default)]
pub struct MTContext {
    pub ast: AstContext,
    pub import_buffer: Vec<Import>,
}

crate::sym_id!(Mod);

#[derive(Debug, Clone)]
pub struct MTEnt {
    pub dependency: Vec<(ID, Mod)>,
    pub dependant: Vec<Mod>,
    pub ast: AstState,
    pub manifest: Manifest,
}

impl Default for MTEnt {
    fn default() -> Self {
        Self {
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
    FileReadError(PathBuf, std::io::Error),
    ManifestReadError(PathBuf, std::io::Error),
    AstError(AstError),
    CyclicDependency(String),
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
