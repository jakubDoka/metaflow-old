use std::fmt::Debug;
use std::path::{PathBuf, Path};
use std::time::SystemTime;

use cranelift::entity::*;
use quick_proc::*;


use crate::util::pool::PoolRef;
use crate::ast::{AstData, self};
use crate::entities::*;
use crate::incr::IncrementalData;
use crate::lexer::*;
use crate::util::sdbm::ID;
use crate::util::storage::*;

pub use error:: {MTError, MTEKind};
pub use modules::Modules;
pub use mod_ent::ModEnt;
pub use context::Context;
pub use manifest_ent::ManifestEnt;
pub use dep_header::Dep;
pub use module_context::ModuleContext;

type Result<T = ()> = std::result::Result<T, MTError>;

pub const CACHE_VAR: &str = "METAFLOW_CACHE";
pub const MOD_SALT: ID = ID(0x64739273646);
pub const SOURCE_EXT: &str = "mf";
pub const MANIFEST_EXT: &str = "mfm";

pub struct MTParser<'a> {
    pub modules: &'a mut Modules,
    pub context: &'a mut Context,
}

impl<'a> MTParser<'a> {
    pub fn new(modules: &'a mut Modules, context: &'a mut Context) -> Self {
        Self { modules, context }
    }

    pub fn parse(&mut self, root: &str) -> Result<Vec<Mod>> {
        self.clean_incremental_data();

        let mut path_buffer = PathBuf::new();

        self.load_manifests(root, &mut path_buffer)?;

        let root_manifest_id = Manifest::new(0);

        let in_code_path = self.manifest(root_manifest_id).name();
        let mut frontier = vec![(
            in_code_path, 
            Token::default(), 
            root_manifest_id, 
            Option::<(Mod, Option<Span>)>::None
        )];

        let module = Mod::new(1); // cause builtin module is 0

        let mut imports = self.context.temp_vec();
        let mut ast_data = AstData::default();

        while let Some((in_code_path, token, manifest_id, destination)) = frontier.pop() {
            let module = self.load_module(in_code_path, token, manifest_id, &mut path_buffer)?;

            let module_ent = self.modules.take_module(module);

            if let Some((dest, nickname)) = destination {
                module_ent.add_use(dest);
                let nick = nickname.unwrap_or(module_ent.name());
                let hash = self.modules.hash_span(nick);
                self.module_mut(dest).add_dep(Dep::new(
                    MOD_SALT.add(hash),
                    in_code_path,
                    token,
                    module,
                ));
            }

            if self.context.is_module_complete(module) {
                self.modules.put_module(module, module_ent);
                continue;
            }

            if self.context.is_module_clean(module) {
                // we still want to walk the tree to see some deeper changed files
                let len = module_ent.deps().len();
                for i in 0..len {
                    let dep = module_ent.deps()[i];
                    if dep.module() == BUILTIN_MODULE {
                        continue;
                    }
                    let manifest_id = self.module(dep.module()).manifest();
                    frontier.push((dep.in_code_path(), dep.hint(), manifest_id, None));
                    module_ent.add_use(dep.module());
                }
                continue;
            }

            let mut ast_state = ast::State::new(module_ent.source(), self.modules.sources())
                .map_err(Into::into)?;
            

            let mut parser = ast::Parser::new(self.modules.sources(), &mut ast_state, &mut ast_data, self.context.ast_mut());
            parser.parse_imports(&mut imports).map_err(Into::into)?;

            self.context.save_ast_state(module, ast_state);

            for import in imports.drain(..) {
                let path = self.modules.display(import.path());
                let head = Path::new(path)
                    .components()
                    .next()
                    .unwrap()
                    .as_os_str()
                    .to_str()
                    .unwrap();
                let id = ID::new(head);
                let manifest = &self.modules.manifest(module_ent.manifest());
                // here we see that first segment of path sets manifest
                let manifest = if id == self.modules.hash_span(manifest.name()) {
                    module_ent.manifest()
                } else {
                    manifest
                        .deps()
                        .iter()
                        .find(|dep| dep.0.nick() == id)
                        .map(|dep| dep.1)
                        .ok_or_else(|| MTError::new(MTEKind::ImportNotFound, import.token()))?
                        .clone()
                };

                frontier.push((
                    import.path(),
                    import.token(),
                    manifest,
                    Some((module, import.nickname())),
                ));
            }

            module_ent.add_dep(Dep::new(
                MOD_SALT.add(ID::new("builtin")),
                Default::default(),
                Default::default(),
                BUILTIN_MODULE,
            ));

            self.context.is_module_complete(module);
            self.modules.put_module(module, module_ent);
        }

        let order = self.modules.create_order(module)
            .map_err(|err| MTError::new(
                MTEKind::CyclicDependency(err),
                Token::default(),
            ))?;

        Ok(order)
    }

    fn load_module(
        &mut self,
        in_code_path: Span,
        token: Token,
        manifest_id: Manifest,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        let manifest = self.manifest(manifest_id);
        // in case this is dependency or command line argument is not '.'
        path_buffer.push(Path::new(manifest.base_path()));
        path_buffer.push(Path::new(self.modules.display(manifest.root_path())));
        let manifest_name = self.modules.display(manifest.name());
        path_buffer.push(Path::new(manifest_name));

        let root = self.modules.display(in_code_path);

        let module_path = Path::new(root);

        // finding module name span
        let name_len = module_path.file_stem().unwrap().len();
        let whole_len = module_path.file_name().unwrap().len();

        let len = in_code_path.len();
        let name = in_code_path.slice(len - whole_len..len - name_len + whole_len);

        // now we have to strip first path segment from root span and replace it with real name
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
        // done, path is constructed

        let id = MOD_SALT.add(ID::new(path_buffer.to_str().unwrap()));

        let modified = std::fs::metadata(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?
            .modified()
            .ok();

        let mut content = std::fs::read_to_string(&path_buffer)
            .map_err(|err| MTError::new(MTEKind::FileReadError(path_buffer.clone(), err), token))?;

        // stop if module is clean
        let saved_module = self.modules.module_index(id); 
        if let Some(module) = saved_module {
            match self.modules.is_unchanged(modified, module, content) {
                Some(c) => content = c,
                None => {
                    path_buffer.clear();
                    return Ok(module);
                }
            }
        }

        let source = SourceEnt {
            name: path_buffer.to_str().unwrap().to_string(),
            content,
            modified: modified.unwrap_or(SystemTime::now()),
        };

        // we still reuse old allocations
        let module = if let Some(module) = saved_module {
            let mut module_ent = self.module_mut(module);
            self.modules.put_source(module_ent.source(), source);
            module_ent.clear_deps();
            self.context.mark_module_dirty(module);
            module
        } else {
            let mut module = ModEnt {
                id,
                name,
                manifest: manifest_id,

                ..Default::default()
            };
            module.source = self.sources.push(source);
            self.a_state_for(module.source, &mut module.ast_data);
            let (shadowed, m) = self.modules.insert(id, module);
            debug_assert!(shadowed.is_none());
            m
        };

        path_buffer.clear();

        Ok(module)
    }

    fn load_manifests(&mut self, base_path: &str, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var(CACHE_VAR)
            .map_err(|_| MTError::new(MTEKind::MissingCache, Token::default()))?;

        let id = ID::new(base_path);

        let manifest_id = self.manifests.index_or_insert(
            id,
            ManifestEnt {
                id,
                base_path: base_path.to_string(),
                ..ManifestEnt::default()
            },
        );

        let mut frontier = vec![(manifest_id, Token::default(), Option::<Dep>::None)];

        while let Some((manifest_id, token, import)) = frontier.pop() {
            if self.context.seen_manifests.contains(manifest_id) {
                continue;
            }

            path_buffer.clear();
            path_buffer.push(Path::new(self.manifests[manifest_id].base_path.as_str()));

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

            let last_source = if let Some(&manifest) = self.manifests.index(id) {
                let source = self.manifests[manifest].source;
                if modified == Some(self.sources[source].modified) {
                    frontier.extend(
                        self.manifests[manifest]
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
                self.sources[last_source] = source;
                last_source
            } else {
                self.sources.push(source)
            };
            self.manifests[manifest_id].source = source;

            let mut state = ast::State::default();
            self.a_state_for(source, &mut state);
            let manifest = AParser::new(self.modules, &mut state, self.context)
                .parse_manifest()
                .map_err(Into::into)?;

            let root_file_span = self
                .modules
                .attr_of(&manifest, "root")
                .unwrap_or_else(|| self.builtin_span("main.mf"));
            let root_file = self.display(&root_file_span);

            let parent_len = Path::new(root_file).parent().unwrap().as_os_str().len();

            let name_len = Path::new(root_file)
                .file_stem()
                .ok_or_else(|| MTError::new(MTEKind::MissingPathStem, token))?
                .len();
            let whole_len = Path::new(root_file).file_name().unwrap().len();

            let len = root_file_span.len();
            let name =
                self.slice_span(&root_file_span, len - whole_len, len - whole_len + name_len);
            let root_path = self.slice_span(&root_file_span, 0, parent_len);

            let manifest_ent = &mut self.manifests[manifest_id];
            manifest_ent.name = name;
            manifest_ent.root_path = root_path;

            for dependency in &manifest.deps {
                path_buffer.clear();
                let dependency_path = self.display(&dependency.path);
                if dependency.external {
                    path_buffer.push(Path::new(&cache_root));
                    path_buffer.push(Path::new(dependency_path));
                    path_buffer.push(Path::new(self.display(&dependency.version)));
                } else {
                    path_buffer.push(Path::new(base_path));
                    path_buffer.push(Path::new(dependency_path));
                }

                let id = ID::new(path_buffer.to_str().unwrap());

                let manifest = self.manifests.index_or_insert(
                    id,
                    ManifestEnt {
                        id,
                        base_path: path_buffer.to_str().unwrap().to_string(),
                        ..ManifestEnt::default()
                    },
                );

                self.manifests[manifest_id]
                    .deps
                    .push((dependency.clone(), manifest));

                frontier.push((manifest, dependency.token, Some(dependency.clone())));
            }

            self.context.seen_manifests.insert(manifest_id);
        }

        let mut stack = vec![];
        let mut map = vec![(false, false); self.manifests.len()];

        if let Some(cycle) =
            self.manifests
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
        let base_path = &self.manifests[manifest].base_path;

        std::fs::create_dir_all(base_path).unwrap();

        let link = format!("https://{}", self.display(&dep.path));

        let code = std::process::Command::new("git")
            .args(&[
                "clone",
                "--depth",
                "1",
                "--branch",
                self.display(&dep.version),
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

    fn clean_incremental_data(&mut self) {
        for (_, module) in self.modules.modules.iter_mut() {
            module.dependant.take().clear(module.slices.transmute_mut());
        }
    }

    fn manifest(&self, module: Manifest) -> &ManifestEnt {
        &self.modules.manifests[module]
    }

    fn manifest_mut(&mut self, module: Manifest) -> &mut ManifestEnt {
        &mut self.modules.manifests[module]
    }


    fn module(&self, module: Mod) -> &ModEnt {
        &self.modules.modules[module]
    }

    fn module_mut(&self, module: Mod) -> &ModEnt {
        &self.modules.modules[module]
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

mod manifest_ent {
    use crate::util::storage::TableId;

    use super::*;

    #[derive(Debug, Clone, Default, QuickSer)]
    pub struct ManifestEnt {
        id: ID,
        base_path: String,
        name: Span,
        root_path: Span,
        deps: Vec<(Dep, Manifest)>,
        source: Source,
    }

    impl ManifestEnt {
        pub fn new(
            id: ID,
            base_path: &str,
            name: Span,
            root_path: Span,
            deps: Vec<(Dep, Manifest)>,
            source: Source,
        ) -> Self {
            Self {
                id,
                base_path: base_path.to_string(),
                name,
                root_path,
                deps,
                source,
            }
        }
        
        pub fn base_path(&self) -> &str {
            &self.base_path
        }

        pub fn name(&self) -> Span {
            self.name
        }

        pub fn root_path(&self) -> Span {
            self.root_path
        }

        pub fn deps(&self) -> &[(Dep, Manifest)] {
            &self.deps
        }

        pub fn source(&self) -> Source {
            self.source
        }
    }

    impl TableId for ManifestEnt {
        fn id(&self) -> ID {
            self.id
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
}


mod modules {
    use super::*;

    #[derive(Debug, Clone, QuickSer)]
    pub struct Modules {
        pub sources: Sources,
        pub manifests: Table<Manifest, ManifestEnt>,
        pub modules: Table<Mod, ModEnt>,
    }
    
    
    impl Modules {
        pub fn collect_scopes(&self, module: Mod, buffer: &mut Vec<(Mod, ID)>) {
            let module_ent = &self.modules[module];
            buffer.push((module, module_ent.id()));
            buffer.extend(
                module_ent
                    .deps()
                    .iter()
                    .map(|dep| (dep.module(), self.modules[dep.module()].id())),
            );
        }
    
        pub fn find_dep(&self, inside: Mod, name: Token) -> Option<Mod> {
            let nick = MOD_SALT.add(self.hash_token(name));
            self.modules[inside]
                .deps()
                .iter()
                .find(|dep| dep.nick() == nick)
                .map(|dep| dep.module())
        }
    
        pub fn can_access(&self, from: Mod, to: Mod, vis: Vis) -> bool {
            matches!(
                (
                    from == to,
                    self.modules[from].manifest() == self.modules[to].manifest(),
                    vis
                ),
                (true, ..) | (_, true, Vis::None | Vis::Public) | (.., Vis::Public)
            )
        }

        pub fn module(&self, module: Mod) -> &ModEnt {
            &self.modules[module]
        }

        pub fn module_mut(&mut self, module: Mod) -> &mut ModEnt {
            &mut self.modules[module]
        }

        pub fn manifest(&self, module: Manifest) -> &ManifestEnt {
            &self.manifests[module]
        }
    
        pub fn hash_span(&self, span: Span) -> ID {
            ID::new(self.sources.display(span))
        }

        pub fn hash_token(&self, token: Token) -> ID {
            ID::new(self.sources.display_token(token))
        }

        pub fn take_module(&mut self, module: Mod) -> ModEnt {
            std::mem::take(&mut self.modules[module])
        }

        pub fn put_module(&mut self, module: Mod, module_ent: ModEnt) {
            self.modules[module] = module_ent;
        }

        pub(crate) fn display(&self, path: Span) -> &str {
            self.sources.display(path)
        }

        pub fn detect_cycles(
            &self, 
            root: Mod, 
            stack: &mut Vec<(Mod, usize)>, 
            lookup: &mut [(bool, bool)], 
            ordering: Option<&mut Vec<Mod>>
        ) -> Option<Vec<Mod>> {
            self.modules.detect_cycles(root, stack, lookup, ordering)
        }

        pub fn create_order(&self, root: Mod) -> std::result::Result<Vec<Mod>, Vec<Mod>> {
            let mut ordering = Vec::with_capacity(self.modules.len());
            let mut stack = Vec::with_capacity(self.modules.len());
            let mut lookup = vec![(false, false); self.modules.len()];
            
            if let Some(cycle) = self.modules.detect_cycles(root, &mut stack, &mut lookup, Some(&mut ordering)) {
                return Err(cycle);
            }

            return Ok(ordering);
        }

        pub fn sources(&self) -> &Sources {
            &self.sources
        }

        pub fn module_index(&self, id: ID) -> Option<Mod> {
            self.modules.index(id).cloned()
        }

        pub fn is_unchanged(&self, modified: Option<SystemTime>, module: Mod, content: String) -> Option<String> {
            let source = self.modules[module].source();
            let source_ent = self.sources.source_mut(source);
            if modified == Some(source_ent.modified()) {
                source_ent.reload(content);
                None
            } else {
                Some(content)
            }
        }

        pub fn put_source(&mut self, source: Source, ent: SourceEnt) {
            self.sources.put_source(source, ent); 
        }
    }

    impl Default for Modules {
        fn default() -> Self {
            let mut s = Self {
                sources: Sources::default(),
                manifests: Table::new(),
                modules: Table::new(),
            };
    
            todo!()
            /*let source = SourceEnt {
                name: "builtin.mf".to_string(),
                content: include_str!("builtin.mf").to_string(),
                ..Default::default()
            };
            let source = s.sources.push(source);
    
            let mut builtin_module = ModEnt {
                id: MOD_SALT.add(ID::new("builtin")),
                ..Default::default()
            };
            s.a_state_for(source, &mut builtin_module.ast_data);
    
            s.modules.insert(builtin_module.id, builtin_module);
            s
            */
        }
    }
    
    impl IncrementalData for Modules {
        fn prepare(&mut self) {            
            self.sources.clear_source_content();
        }
    }

    impl ErrorDisplayState<MTError> for Modules {
        fn fmt(&self, e: &MTError, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match e.kind() {
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
                    writeln!(f, "{}", ErrorDisplay::new(self, error))?;
                },
                MTEKind::CyclicDependency(cycle) => {
                    writeln!(f, "cyclic module dependency detected:")?;
                    for &id in cycle.iter() {
                        writeln!(f, "  {}", self.sources.source(self.modules[id].source()).name())?;
                    }
                },
                MTEKind::CyclicManifests(cycle) => {
                    writeln!(f, "cyclic package dependency detected:")?;
                    for &id in cycle.iter() {
                        writeln!(f, "  {}", self.sources.display(self.manifests[id].name()))?;
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

            Ok(())
        }

        fn sources(&self) -> &Sources {
            &self.sources
        }
    }

    impl ErrorDisplayState<ast::Error> for Modules {
        fn fmt(&self, e: &ast::Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            ErrorDisplayState::fmt(&self.sources, e, f)
        }

        fn sources(&self) -> &Sources {
            &self.sources
        }
    }
}

mod module_context {
    use super::*;

    pub struct ModuleContext {
        deps: Vec<(ID, Mod)>,
        used: Vec<Mod>,
    }
}

mod context {
    use super::*;

    #[derive(Debug, Clone, Default)]
    pub struct Context {
        ast: ast::Context,
        seen_manifests: EntitySet<Manifest>,
        seen_modules: EntitySet<Mod>,
        clean_modules: EntitySet<Mod>,
        modules: SecondaryMap<Mod, ModuleContext>,
    }

    impl Context {
        pub fn prepare(&mut self, initial_module_count: usize) {
            self.seen_manifests.resize(initial_module_count);
            self.seen_modules.resize(initial_module_count);
            self.clean_modules.resize(initial_module_count);
            self.clean_modules.fill(); // Initially all modules from incremental data are clean.
            self.modules.resize(initial_module_count);
        }

        pub fn temp_vec<T>(&mut self) -> PoolRef<T> {
            self.ast.temp_vec()
        }

        pub fn is_manifest_complete(&self, manifest: Manifest) -> bool {
            self.seen_manifests.contains(manifest)
        }

        pub fn is_module_complete(&mut self, module: Mod) -> bool {
            !self.seen_modules.insert(module)
        }

        pub fn ast_mut(&mut self) -> &mut ast::Context {
            &mut self.ast
        }

        pub fn save_ast_state(&mut self, module: Mod, ast_state: ast::State) {
            self.a_states[module] = ast_state;
        }

        pub fn is_module_clean(&self, module: Mod) -> bool {
            self.clean_modules.contains(module)
        }

        pub fn mark_module_dirty(&self, module: Mod) {
            self.clean_modules.remove(module);    
        }
    }
}

mod mod_ent {
    use super::*;

    #[derive(Debug, Clone, Default, QuickSer)]
    pub struct ModEnt {
        id: ID,
        name: Span,
        source: Source,
        manifest: Manifest,
        
        ast: AstData,
    }
        
    impl ModEnt {
        pub fn source(&self) -> Source {
            self.source
        }

        pub fn deps(&self) -> &[Dep] {
            &self.deps
        }

        pub fn manifest(&self) -> Manifest {
            self.manifest
        }

        
        pub fn name(&self) -> Span {
            self.name
        }

        pub fn add_dep(&self, dep_header: Dep) {
            self.deps.push(dep_header);
        }

        pub fn add_use(&self, dest: Mod) {
            self.uses.push(dest);
        }

        pub fn clear_deps(&mut self) {
            self.deps.clear();
        }
    }

    impl TableId for ModEnt {
        fn id(&self) -> ID {
            self.id
        }
    }

    impl TreeStorage<Mod> for Table<Mod, ModEnt> {
        fn node_dep(&self, id: Mod, idx: usize) -> Mod {
            self[id].deps[idx].module()
        }
    
        fn node_len(&self, id: Mod) -> usize {
            self[id].deps.len()
        }
    
        fn len(&self) -> usize {
            Table::len(self)
        }
    }
}

mod dep_header {
    use super::*;

    #[derive(Debug, Clone, Copy, Default, RealQuickSer)]
    pub struct Dep {
        nick: ID,
        in_code_path: Span,
        hint: Token,
        module: Mod,
    }

    impl Dep {
        pub fn new(nick: ID, in_code_path: Span, hint: Token, module: Mod) -> Dep {
            Dep {
                nick,
                in_code_path,
                hint,
                module,
            }
        }

        pub fn nick(&self) -> ID {
            self.nick
        }

        pub fn in_code_path(&self) -> Span {
            self.in_code_path
        }

        pub fn hint(&self) -> Token {
            self.hint
        }

        pub fn module(&self) -> Mod {
            self.module
        }
    }
}

mod error {
    use crate::lexer::DisplayError;

    use super::*;
    
    #[derive(Debug)]
    pub struct MTError {
        pub kind: MTEKind,
        pub token: Token,
    }
    
    impl MTError {
        pub fn new(kind: MTEKind, token: Token) -> Self {
            Self { kind, token }
        }

        pub fn kind(&self) -> &MTEKind {
            &self.kind
        }
    }
    
    impl Into<MTError> for ast::Error {
        fn into(self) -> MTError {
            MTError {
                kind: MTEKind::AError(self),
                token: Token::default(),
            }
        }
    }

    impl DisplayError for MTError {
        fn token(&self) -> Token {
            self.token
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
        AError(ast::Error),
        CyclicDependency(Vec<Mod>),
        CyclicManifests(Vec<Manifest>),
        MissingDependency(PathBuf),
        DownloadError(std::io::Error),
        DownloadFailed,
    }
}


pub fn test() {
    /*const PATH: &str = "src/module_tree/test_project";

    let (mut state, hint) = Modules::load_data(PATH, ID(0)).unwrap_or_default();
    let mut context = Context::default();

    MTParser::new(&mut state, &mut context)
        .parse(PATH)
        .map_err(|e| panic!("{}", MTErrorDisplay::new(&state, &e)))
        .unwrap();

    state.save_data(PATH, ID(0), Some(hint)).unwrap();
    */
}