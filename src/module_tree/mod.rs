use std::path::{Path, PathBuf};

use crate::ast::{AstError, AstParser, AstState, Import, Manifest};
use crate::lexer::Lexer;
use crate::util::sdbm::{SdbmHashState, ID};
use crate::util::storage::{Map, SymID};
use crate::{ast::AstContext, lexer::Token, util::storage::List};

type Result<T = ()> = std::result::Result<T, MTError>;

pub const MOD_SALT: ID = ID(0x64739273646);
pub const SOURCE_EXT: &str = ".mf";
pub const MANIFEST_EXT: &str = ".mfm";

pub struct MTParser<'a> {
    pub state: &'a mut MTState,
    pub context: &'a mut MTContext,
}

impl<'a> MTParser<'a> {
    pub fn new(state: &'a mut MTState, context: &'a mut MTContext) -> Self {
        Self { state, context }
    }

    pub fn parse(&mut self, root: &str) -> Result {
        let base_path = Path::new(root)
            .parent()
            .unwrap_or(Path::new(""))
            .to_str()
            .ok_or_else(|| MTError::new(MTEKind::InvalidPathEncoding, Token::default()))?
            .to_string();

        let root = Path::new(root)
            .file_stem()
            .ok_or_else(|| MTError::new(MTEKind::MissingPathStem, Token::default()))?
            .to_str()
            .ok_or_else(|| MTError::new(MTEKind::InvalidPathEncoding, Token::default()))?;

        let mut path_buffer = PathBuf::new();

        self.load_manifests(root, base_path, &mut path_buffer)?;

        let module = self.load_module(root, Token::default(), Mnf::new(0), &mut path_buffer)?;
        let mut frontier = vec![module];

        while let Some(module_id) = frontier.pop() {
            let mut module = std::mem::take(&mut self.state.modules[module_id]);
            AstParser::new(&mut module.ast, &mut self.context.ast)
                .take_imports()
                .map_err(Into::into)?;
            for import in module.ast.imports.iter() {
                let manifest = if import.external {
                    todo!()
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
        manifest: Mnf,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        path_buffer.push(Path::new(self.state.manifests[manifest].base_path.as_str()));
        path_buffer.push(Path::new(root));
        path_buffer.set_extension(SOURCE_EXT);

        let id = MOD_SALT.add(path_buffer.to_str().unwrap());

        if let Some(module) = self.state.module_map.get(id) {
            return Ok(*module);
        }

        let content = std::fs::read_to_string(path_buffer.as_path())
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        let lexer = Lexer::new(path_buffer.to_str().unwrap().to_string(), content);
        path_buffer.clear();
        let ast = AstState::new(lexer);

        let ent = MTEnt {
            dependency: vec![],
            dependant: vec![],
            ast,
            manifest,
        };

        let module = self.state.modules.add(ent);

        self.state.module_map.insert(id, module);

        Ok(module)
    }

    fn load_manifests(&mut self, base_path: String, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var("METAFLOW_CACHE")
            .map_err(|_| MTError::new(MTEKind::MissingCache, Token::default()))?;

        let mut frontier = vec![(base_path, Token::default())];

        while let Some((base_path, token)) = frontier.pop() {
            path_buffer.clear();
            path_buffer.push(Path::new(&base_path));
            path_buffer.push(Path::new("project"));
            path_buffer.set_extension(MANIFEST_EXT);

            let content = std::fs::read_to_string(&path_buffer).map_err(|err| {
                MTError::new(
                    MTEKind::FileReadError(path_buffer.clone(), err),
                    token.clone(),
                )
            })?;

            let full_path = path_buffer
                .canonicalize()
                .map_err(|err| {
                    MTError::new(
                        MTEKind::FileReadError(path_buffer.clone(), err),
                        token.clone(),
                    )
                })?
                .to_str()
                .ok_or_else(|| MTError::new(MTEKind::InvalidPathEncoding, token.clone()))?
                .to_string();

            let lexer = Lexer::new(full_path, content);
            let mut state = AstState::new(lexer);
            let manifest = AstParser::new(&mut state, &mut self.context.ast)
                .parse_manifest(base_path)
                .map_err(Into::into)?;

            for dependency in manifest.deps.values() {
                path_buffer.push(Path::new(&cache_root));
                path_buffer.push(Path::new(dependency.path));
                path_buffer.push(Path::new(dependency.version));
            }
        }

        todo!()
    }
}

crate::sym_id!(Mnf);

#[derive(Debug, Clone, Default)]
pub struct MTState {
    pub manifest_map: Map<Mnf>,
    pub manifests: List<Mnf, Manifest>,
    pub module_map: Map<Mod>,
    pub modules: List<Mod, MTEnt>,
    pub order: Vec<Mod>,
}

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
    pub manifest: Mnf,
}

impl Default for MTEnt {
    fn default() -> Self {
        Self {
            dependency: vec![],
            dependant: vec![],
            ast: Default::default(),
            manifest: Mnf::new(0),
        }
    }
}

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

pub enum MTEKind {
    InvalidPathEncoding,
    MissingPathStem,
    MissingCache,
    FileReadError(PathBuf, std::io::Error),
    AstError(AstError),
    CyclicDependency(String),
}
