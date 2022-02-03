//! Module builds and stores the module tree and manifest tree.
//! Dependency cycles are detected and modules are marked clean
//! if no changes were made to them.
//!
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use __core::ops::{Deref, DerefMut};
use cranelift::entity::packed_option::ReservedValue;
use cranelift::entity::*;
use quick_proc::*;

use crate::ast::{Ast, Vis};
use crate::lexer::*;
use crate::util::sdbm::ID;
use crate::util::storage::*;
use crate::{ast, lexer};

type Result<T = ()> = std::result::Result<T, Error>;

/// Root manifest is always the first manifest, constant removes ambiguity.
pub const ROOT_MANIFEST: Manifest = Manifest(0);
/// Builtin module is always the first module, constant removes ambiguity.
pub const BUILTIN_MODULE: Mod = Mod(0);
/// Root module is always the second module, constant removes ambiguity.
pub const ROOT_MODULE: Mod = Mod(1);
/// Environment variable under which compiler searches already downloaded dependencies.
pub const CACHE_VAR: &str = "METAFLOW_CACHE";
/// Source file extension.
pub const SOURCE_EXT: &str = "mf";
/// Manifest file extension.
pub const MANIFEST_EXT: &str = "mfm";

/// Ctx embeds ast context and module tree.
#[derive(Debug, Clone, Default)]
pub struct Ctx {
    ctx: ast::Ctx,
    seen_manifests: EntitySet<Manifest>,
    seen_modules: EntitySet<Mod>,
    clean_modules: EntitySet<Mod>,
    manifest_lookup: Map<Manifest>,
    manifests: PoolMap<Manifest, ManifestEnt>,
    module_lookup: Map<Mod>,
    modules: PoolMap<Mod, ModEnt>,
    module_ctxs: SecondaryMap<Mod, ModCtx>,
}

impl Ctx {
    /// Loads all modules and manifests into tree. It returns the order
    /// in which modules should be processed.
    pub fn compute_module_tree(&mut self, root: &str) -> Result<Vec<Mod>> {
        if self.modules.len() == 0 {
            self.load_builtin_module();
        }

        let mut path_buffer = PathBuf::new();

        self.load_manifests(root, &mut path_buffer)?;

        let in_code_path = self.manifests[ROOT_MANIFEST].name;
        let mut frontier = vec![(
            in_code_path,
            Token::default(),
            Option::<(Option<Span>, Mod)>::None,
            ROOT_MANIFEST,
        )];

        let builtin_span = self.builtin_span("builtin");

        // cleared each loop
        let mut imports = self.temp_vec();
        let mut ast_data = ast::Data::default();
        let mut collector = ast::Collector::default();

        // loop eliminates recursion
        while let Some((in_code_path, token, from, manifest_id)) = frontier.pop() {
            let module = self.load_module(in_code_path, token, manifest_id, &mut path_buffer)?;
            let ModCtx {
                name,
                source,
                manifest,
                ..
            } = self.module_ctxs[module];
            let module_ent = std::mem::take(&mut self.modules[module]);
            if let Some((nick, parent_module)) = from {
                let nick_span = nick.unwrap_or(name);
                let nick = self.hash_span(nick_span);

                self.module_ctxs[module].used.push(parent_module);
                self.module_ctxs[parent_module]
                    .deps
                    .push((nick_span, module));
                self.import_item(
                    parent_module,
                    nick,
                    Item::new(item::Kind::Mod(module), parent_module, token),
                )?;
            }

            if self.seen_modules.contains(module) {
                self.modules[module] = module_ent;
                continue;
            }

            let mut ast_state = ast::State::new(source, &self.ctx).map_err(Into::into)?;

            ast::Parser::new(&mut ast_state, &mut ast_data, &mut self.ctx, &mut collector)
                .parse_imports(&mut imports)
                .map_err(Into::into)?;

            for import in imports.drain(..) {
                let path = self.display(import.path());
                let head = Path::new(path)
                    .components()
                    .next()
                    .ok_or_else(|| Error::new(error::Kind::MissingPathStem, import.token()))?
                    .as_os_str()
                    .to_str()
                    .unwrap();
                let id = ID::new(head);
                let manifest_ent = &self.manifests[manifest];
                // here we see that first segment of path sets manifest
                let manifest = if id == self.hash_span(manifest_ent.name) {
                    manifest
                } else {
                    manifest_ent
                        .find_dep(id)
                        .ok_or_else(|| Error::new(error::Kind::ImportNotFound, import.token()))?
                        .clone()
                };

                frontier.push((
                    import.path(),
                    import.token(),
                    Some((import.nickname(), module)),
                    manifest,
                ));
            }

            self.module_ctxs[module]
                .deps
                .push((builtin_span, BUILTIN_MODULE));
            self.import_item(
                module,
                ID::new("builtin"),
                Item::new(item::Kind::Mod(BUILTIN_MODULE), module, token),
            )?;

            self.module_ctxs[module].ast_state = ast_state;

            self.seen_modules.insert(module);
            self.modules[module] = module_ent;
        }

        let order = self
            .create_order(ROOT_MODULE)
            .map_err(|err| Error::new(error::Kind::CyclicDependency(err), Token::default()))?;

        Ok(order)
    }

    /// Loads the module and returns reference. `in_code_path` should point to
    /// content of string defining import in 'use' statement. `token` is used for
    /// error display. `manifest` is the is of manifest of project that contains
    /// it. `path_buffer` should be empty and will remain empty after call.
    pub fn load_module(
        &mut self,
        in_code_path: Span,
        token: Token,
        manifest: Manifest,
        path_buffer: &mut PathBuf,
    ) -> Result<Mod> {
        let manifest_ent = &self.manifests[manifest];
        // in case this is dependency or command line argument is not '.'
        path_buffer.push(Path::new(self.display(manifest_ent.base_path)));
        path_buffer.push(Path::new(self.display(manifest_ent.root_path)));
        let manifest_name = self.display(manifest_ent.name);
        path_buffer.push(Path::new(manifest_name));

        let root = self.display(in_code_path);

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

        let id = ID::new(path_buffer.to_str().unwrap());

        let modified = std::fs::metadata(&path_buffer)
            .map_err(|err| Error::new(error::Kind::FileReadError(path_buffer.clone(), err), token))?
            .modified()
            .ok();

        let content = std::fs::read_to_string(&path_buffer).map_err(|err| {
            Error::new(error::Kind::FileReadError(path_buffer.clone(), err), token)
        })?;
        let source = SourceEnt::new(path_buffer.to_str().unwrap().to_string(), content);
        let source = self.add_source(source);

        path_buffer.clear();

        // stop if module is clean
        let saved_module = self.module_lookup.get(id).cloned();
        let module = if let Some(module) = saved_module {
            let module_ent = &mut self.modules[module];
            module_ent.id = id;
            if Some(module_ent.modified) != modified {
                // if we cant get the modification time juts use unique
                // time so module gets always refreshed
                module_ent.modified = modified.unwrap_or(SystemTime::now());
                self.clean_modules.remove(module);
            }

            module
        } else {
            let module = ModEnt {
                id,
                ..Default::default()
            };
            let module = self.modules.push(module);
            let shadow = self.module_lookup.insert(id, module);
            debug_assert!(shadow.is_none());
            module
        };

        self.module_ctxs[module] = ModCtx {
            name,
            source,
            manifest,

            ..Default::default()
        };

        Ok(module)
    }

    /// Loads and builds manifest tree. `base_path` should point to directory with manifest.
    /// `path_buffer` should be empty and will remain empty after call.
    pub fn load_manifests(&mut self, base_path: &str, path_buffer: &mut PathBuf) -> Result {
        let cache_root = std::env::var(CACHE_VAR)
            .map_err(|_| Error::new(error::Kind::MissingCache, Token::default()))?;

        let id = ID::new(base_path);

        let manifest_id = if let Some(&manifest) = self.manifest_lookup.get(id) {
            manifest
        } else {
            let module = self.manifests.push(ManifestEnt {
                id,
                base_path: self.ctx.builtin_span(base_path),
                ..ManifestEnt::default()
            });
            self.manifest_lookup.insert(id, module);
            module
        };

        let mut frontier = vec![(manifest_id, ast::Dep::default())];
        let mut data = ast::Data::default();
        let mut collector = ast::Collector::default();
        while let Some((manifest_id, import)) = frontier.pop() {
            if self.seen_manifests.contains(manifest_id) {
                continue;
            }

            let manifest_base_path = self.display(self.manifests[manifest_id].base_path);
            path_buffer.clear();
            path_buffer.push(Path::new(manifest_base_path));

            if !path_buffer.exists() {
                if import.external() {
                    self.download(import, manifest_base_path)?;
                } else {
                    return Err(Error::new(
                        error::Kind::MissingDependency(path_buffer.clone()),
                        import.token(),
                    ));
                }
            }

            path_buffer.push(Path::new("project"));
            path_buffer.set_extension(MANIFEST_EXT);

            let content = std::fs::read_to_string(&path_buffer).map_err(|err| {
                Error::new(
                    error::Kind::ManifestReadError(path_buffer.clone(), err),
                    import.token(),
                )
            })?;

            let source = SourceEnt::new(path_buffer.to_str().unwrap().to_string(), content);

            let source = self.add_source(source);
            self.manifests[manifest_id].source = source;

            let mut state = ast::State::new(source, &self.ctx).map_err(Into::into)?;
            let manifest = ast::Parser::new(&mut state, &mut data, self, &mut collector)
                .parse_manifest()
                .map_err(Into::into)?;

            let root_file_span = manifest
                .find_attr(ID::new("root"))
                .unwrap_or_else(|| self.builtin_span("main.mf"));
            let root_file = self.display(root_file_span);

            let parent_len = Path::new(root_file).parent().unwrap().as_os_str().len();

            let name_len = Path::new(root_file)
                .file_stem()
                .ok_or_else(|| Error::new(error::Kind::MissingPathStem, import.token()))?
                .len();
            let whole_len = Path::new(root_file).file_name().unwrap().len();

            let len = root_file_span.len();
            let name = root_file_span.slice(len - whole_len..len - whole_len + name_len);
            let root_path = root_file_span.slice(0..parent_len);

            let manifest_ent = &mut self.manifests[manifest_id];
            manifest_ent.name = name;
            manifest_ent.root_path = root_path;

            for dep in manifest.deps() {
                path_buffer.clear();
                let dep_path = self.display(dep.path());
                if dep.external() {
                    path_buffer.push(Path::new(&cache_root));
                    path_buffer.push(Path::new(dep_path));
                    path_buffer.push(Path::new(self.display(dep.version())));
                } else {
                    path_buffer.push(Path::new(base_path));
                    path_buffer.push(Path::new(dep_path));
                }

                let id = ID::new(path_buffer.to_str().unwrap());

                let manifest = if let Some(&manifest) = self.manifest_lookup.get(id) {
                    manifest
                } else {
                    let module = self.manifests.push(ManifestEnt {
                        base_path: self.ctx.builtin_span(path_buffer.to_str().unwrap()),
                        ..ManifestEnt::default()
                    });
                    self.manifest_lookup.insert(id, module);
                    module
                };

                let id = self.hash_span(dep.name());
                self.manifests[manifest_id].deps.push((id, manifest));

                frontier.push((manifest, dep.clone()));
            }

            self.seen_manifests.insert(manifest_id);
        }

        let mut stack = vec![];
        let mut map = vec![(false, false); self.manifests.len()];

        if let Some(cycle) = self.detect_cycles(Manifest::new(0), &mut stack, &mut map, None) {
            return Err(Error::new(
                error::Kind::CyclicManifests(cycle),
                Token::default(),
            ));
        }

        path_buffer.clear();

        Ok(())
    }

    /// Downloads the dependency pointed by `dep`. `destination` is
    /// path to directory where files should be located.
    pub fn download(&self, dep: ast::Dep, destination: &str) -> Result {
        std::fs::create_dir_all(destination).unwrap();

        let link = format!("https://{}", self.display(dep.path()));

        let code = std::process::Command::new("git")
            .args(&[
                "clone",
                "--depth",
                "1",
                "--branch",
                self.display(dep.version()),
                &link,
                destination,
            ])
            .status()
            .map_err(|err| Error::new(error::Kind::DownloadError(err), dep.token()))?;

        if !code.success() {
            return Err(Error::new(error::Kind::DownloadFailed, dep.token()));
        }

        Ok(())
    }

    /// Returns whether accessing item inside `target` with `vis` from `accessor`  
    pub fn can_access(&self, accessor: Mod, target: Mod, vis: Vis) -> bool {
        matches!(
            (
                accessor == target,
                self.module_ctxs[accessor].manifest == self.module_ctxs[target].manifest,
                vis
            ),
            (true, ..) | (_, true, Vis::None | Vis::Public) | (.., Vis::Public)
        )
    }

    /// Computes hash of span content.
    pub fn hash_span(&self, span: Span) -> ID {
        ID::new(self.display(span))
    }

    /// Computes hash fo token content.
    pub fn hash_token(&self, token: Token) -> ID {
        ID::new(self.display_token(token))
    }

    /// Creates a module order fro given root. It returns the sequence
    /// of modules creating cycle as error.
    pub fn create_order(&self, root: Mod) -> std::result::Result<Vec<Mod>, Vec<Mod>> {
        let mut ordering = Vec::with_capacity(self.modules.len());
        let mut stack = Vec::with_capacity(self.modules.len());
        let mut lookup = vec![(false, false); self.modules.len()];

        if let Some(cycle) = self.detect_cycles(root, &mut stack, &mut lookup, Some(&mut ordering))
        {
            return Err(cycle);
        }

        return Ok(ordering);
    }

    /// Collects scopes of a module.
    pub fn collect_scopes(&self, module: Mod, buffer: &mut Vec<Mod>) {
        let module_ent = &self.module_ctxs[module];
        buffer.push(module);
        buffer.extend(module_ent.deps.iter().map(|dep| dep.1));
    }

    /// Loads a builtin module. Source code is included with macro.
    pub fn load_builtin_module(&mut self) {
        let content = include_str!("builtin.mf").to_string();
        let name = "builtin.mf".to_string();
        let source = SourceEnt::new(name, content);
        let source = self.add_source(source);
        let module = ModEnt {
            id: ID::new("builtin"),
            modified: SystemTime::now(),

            ..Default::default()
        };
        let module = self.modules.push(module);
        self.module_ctxs[module].ast_state = ast::State::new(source, &self.ctx).unwrap();
    }

    /// Computes ast of module. If true is returned, parsing was
    /// interrupted by top level 'break'.
    pub fn compute_ast(
        &mut self,
        module: Mod,
        buffer: &mut ast::Data,
        collector: &mut ast::Collector,
    ) -> Result<bool> {
        ast::Parser::new(
            &mut self.module_ctxs[module].ast_state,
            buffer,
            &mut self.ctx,
            collector,
        )
        .parse()
        .map_err(|err| Error::new(error::Kind::AError(err), Token::default()))
    }

    pub fn collect_imported_items(&self, module: Mod, buffer: &mut Vec<(ID, Item)>) {
        for &(.., module) in self.module_ctxs[module].deps.iter() {
            buffer.extend_from_slice(self.modules[module].owned_items.as_slice());
        }
    }

    /// Finds item in scope, if collision occurred, or item does not exist, method returns error.
    pub fn find_item(&self, module: Mod, id: ID, hint: Token) -> Result<Item> {
        let scope = &self.module_ctxs[module].scope;
        let item = scope
            .get(id)
            .ok_or_else(|| Error::new(error::Kind::ItemNotFound, hint))?
            .clone();

        if item.kind == item::Kind::Collision {
            let candidates = self.module_ctxs[module]
                .deps
                .iter()
                .filter_map(|&(span, module)| {
                    scope.get(id.add(self.modules[module].id)).map(|_| span)
                })
                .collect::<Vec<_>>();
            return Err(Error::new(error::Kind::ItemCollision(candidates), hint));
        }

        Ok(item)
    }

    /// Adds item to module, which means it will be inserted both to owned items and to scope.
    /// Error can originate from [`Self::import_item()`].
    pub fn add_item(&mut self, module: Mod, id: ID, item: Item) -> Result {
        self.modules[module].owned_items.push((id, item));
        self.import_item(module, id, item)
    }

    /// Imports item into the scope. This can trigger moving items behind external module scope
    /// if two items have same hash. IF collision between two `module`-owned items occurs, method returns
    /// error.
    pub fn import_item(&mut self, module: Mod, mut id: ID, item: Item) -> Result {
        let scope = &mut self.module_ctxs[module].scope;
        if let Some(&collision) = scope.get(id) {
            if collision.kind == item::Kind::Collision {
                if item.module != module {
                    id = id.add(self.modules[item.module].id);
                }
            } else if collision.module == module {
                if item.module == module {
                    return Err(Error::new(
                        error::Kind::Redefinition(collision.hint),
                        item.hint,
                    ));
                }
                id = id.add(self.modules[item.module].id);
            } else {
                let redirect = id.add(self.modules[collision.module].id);
                let shadow = scope.insert(redirect, collision);
                debug_assert!(
                    shadow.is_none(),
                    "seems like unlucky hashing corrupted the scope"
                );

                scope.insert(id, Item::collision());
                if item.module != module {
                    id = id.add(self.modules[item.module].id);
                }
            }

            let shadow = scope.insert(id, item);
            debug_assert!(
                shadow.is_none() || shadow.unwrap().kind == item::Kind::Collision,
                "this means that we did not detect collision when compiling module {:?} {}",
                shadow,
                token::Display::new(self.sources(), &item.hint),
            );
        } else {
            scope.insert(id, item);
        }

        Ok(())
    }

    pub fn push_item(&mut self, module: Mod, id: ID, item: item::Kind) -> Option<Item> {
        let item = Item::new(item, module, Token::default());
        self.module_ctxs[module].scope.insert(id, item)
    }

    pub fn pop_item(&mut self, module: Mod, id: ID, shadow: Option<Item>) {
        if let Some(shadow) = shadow {
            self.module_ctxs[module].scope.insert(id, shadow);
        } else {
            self.module_ctxs[module].scope.remove(id);
        }
    }

    pub fn module_id(&self, module: Mod) -> ID {
        self.modules[module].id
    }

    pub fn find_item_unchecked(&self, module: Mod, id: ID) -> Option<Item> {
        self.module_ctxs[module].scope.get(id).cloned()
    }

    pub fn find_attribute(&self, ast_data: &ast::Data, attributes: Ast, name: &str) -> Option<Ast> {
        let id = ID::new(name);
        for &attr in ast_data.sons(attributes) {
            let attr_id = self.hash_token(ast_data.son_ent(attr, 0).token());
            if id == attr_id {
                return Some(attr);
            }
        }

        None
    }
}

crate::impl_entity!(Fun, Global, Local, Ty, Const);

#[derive(Debug, Clone, Copy, Default, RealQuickSer)]
pub struct Item {
    kind: item::Kind,
    module: Mod,
    hint: Token,
}

impl Item {
    pub fn new(kind: item::Kind, module: Mod, hint: Token) -> Item {
        Item { kind, module, hint }
    }

    pub fn collision() -> Self {
        Self {
            kind: item::Kind::Collision,

            ..Default::default()
        }
    }

    pub fn kind(&self) -> item::Kind {
        self.kind
    }
}

pub mod item {
    use super::*;

    /// Kind specifies to what [`Item`] points to.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
    pub enum Kind {
        /// Item is colliding with another and needs
        /// to be referred to by module path.
        Collision,
        /// Item refers to imported module.
        Mod(Mod),
        /// Item refers to type.
        Ty(Ty),
        /// Item refers to const.
        Const(Const),
        /// Item refers to global.
        Global(Global),
        /// Item refers to local value.
        Local(Local),
        /// Item refers to function.
        Fun(Fun),
    }

    impl std::fmt::Display for Kind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Kind::Collision => write!(f, "collision"),
                Kind::Mod(..) => write!(f, "module"),
                Kind::Ty(..) => write!(f, "type"),
                Kind::Const(..) => write!(f, "constant"),
                Kind::Global(..) => write!(f, "global variable"),
                Kind::Local(..) => write!(f, "local variable"),
                Kind::Fun(..) => write!(f, "function"),
            }
        }
    }

    impl Default for Kind {
        fn default() -> Self {
            Kind::Collision
        }
    }
}

type ManifestDep = (ID, Manifest);

///
#[derive(Debug, Clone, Default, QuickSer)]
pub struct ManifestEnt {
    id: ID,
    base_path: Span,
    name: Span,
    root_path: Span,
    deps: Vec<ManifestDep>,
    source: Source,
}

impl ManifestEnt {
    /// Finds dependant manifest by hash of its alias.
    pub fn find_dep(&self, id: ID) -> Option<Manifest> {
        self.deps.iter().find_map(|dep| {
            if dep.0 == id {
                Some(dep.1.clone())
            } else {
                None
            }
        })
    }
}

impl TreeStorage<Manifest> for Ctx {
    fn node_dep(&self, id: Manifest, idx: usize) -> Manifest {
        self.manifests[id].deps[idx].1
    }

    fn node_len(&self, id: Manifest) -> usize {
        self.manifests[id].deps.len()
    }

    fn len(&self) -> usize {
        self.manifests.len()
    }
}

impl ErrorDisplayState<Error> for Ctx {
    fn fmt(&self, e: &Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match e.kind() {
            error::Kind::ItemCollision(candidates) => {
                writeln!(
                    f,
                    "tri specifying module this item comes from, here are all candidates:"
                )?;
                for &candidate in candidates {
                    writeln!(f, "  {}:: ", self.display(candidate))?;
                }
            }
            error::Kind::ItemNotFound => {
                writeln!(f, "item not found in current scope")?;
            }
            error::Kind::Redefinition(token) => {
                writeln!(
                    f,
                    "is redefinition of\n{}",
                    token::Display::new(self.sources(), token)
                )?;
            }
            error::Kind::InvalidPathEncoding => {
                writeln!(f, "invalid path encoding")?;
            }
            error::Kind::MissingPathStem => {
                writeln!(f, "root attribute of the manifest if missing path stem (simply is not pointing to file)")?;
            }
            error::Kind::MissingCache => {
                writeln!(f, "missing dependency cache, the environment variable 'METAFLOW_CACHE' has to be set")?;
            }
            error::Kind::ImportNotFound => {
                writeln!(
                    f,
                    "root of module import not found inside manifest, nor it is root of current project"
                )?;
            }
            error::Kind::FileReadError(path, error) => {
                writeln!(f, "error reading module '{}', this may be due to invalid project structure, original error: {}", path.as_os_str().to_str().unwrap(), error)?;
            }
            error::Kind::ManifestReadError(path, error) => {
                writeln!(
                    f,
                    "error reading manifest '{}', original error: {}",
                    path.as_os_str().to_str().unwrap(),
                    error
                )?;
            }
            error::Kind::AError(error) => {
                writeln!(f, "{}", ErrorDisplay::new(self.deref(), error))?;
            }
            error::Kind::CyclicDependency(cycle) => {
                writeln!(f, "cyclic module dependency detected:")?;
                for &id in cycle.iter() {
                    writeln!(f, "  {}", self.source(self.module_ctxs[id].source).name())?;
                }
            }
            error::Kind::CyclicManifests(cycle) => {
                writeln!(f, "cyclic package dependency detected:")?;
                for &id in cycle.iter() {
                    writeln!(f, "  {}", self.display(self.manifests[id].name))?;
                }
            }
            error::Kind::MissingDependency(path) => {
                writeln!(
                    f,
                    "missing dependency '{}'",
                    path.as_os_str().to_str().unwrap()
                )?;
            }
            error::Kind::DownloadError(error) => {
                writeln!(f, "error downloading dependency, original error: {}", error)?;
            }
            error::Kind::DownloadFailed => {
                writeln!(f, "failed to download dependency")?;
            }
        }

        Ok(())
    }

    fn sources(&self) -> &lexer::Ctx {
        self.ctx.sources()
    }
}

impl Deref for Ctx {
    type Target = ast::Ctx;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for Ctx {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

/// Struct contains data that should not be serialized with Module.
#[derive(Debug, Clone, Default)]
pub struct ModCtx {
    scope: Map<Item>,
    name: Span,
    source: Source,
    manifest: Manifest,

    ast_state: ast::State,
    deps: Vec<(Span, Mod)>,
    used: Vec<Mod>,
}

impl TreeStorage<Mod> for Ctx {
    fn node_dep(&self, id: Mod, idx: usize) -> Mod {
        self.module_ctxs[id].deps[idx].1
    }

    fn node_len(&self, id: Mod) -> usize {
        self.module_ctxs[id].deps.len()
    }

    fn len(&self) -> usize {
        self.modules.len()
    }
}

crate::impl_entity!(Mod, Manifest);

///
#[derive(Debug, Clone, QuickDefault, QuickSer)]
pub struct ModEnt {
    id: ID,
    #[default(SystemTime::UNIX_EPOCH)]
    modified: SystemTime,
    owned_items: Vec<(ID, Item)>,
}

/// Error create upon module building failure.
#[derive(Debug)]
pub struct Error {
    kind: error::Kind,
    token: Token,
}

impl Error {
    /// Creates new error.
    pub fn new(kind: error::Kind, token: Token) -> Self {
        Self { kind, token }
    }

    /// Returns error kind.
    pub fn kind(&self) -> &error::Kind {
        &self.kind
    }
}

impl Into<Error> for ast::Error {
    fn into(self) -> Error {
        Error {
            kind: error::Kind::AError(self),
            token: Token::default(),
        }
    }
}

impl DisplayError for Error {
    fn token(&self) -> Token {
        self.token
    }
}

mod error {
    use super::*;

    #[derive(Debug)]
    pub enum Kind {
        ItemCollision(Vec<Span>),
        ItemNotFound,
        Redefinition(Token),
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

/// Tree storage generalizes tree cycle detection.
pub trait TreeStorage<I: EntityRef + 'static + Debug>
where
    Self: Sized,
{
    /// Returns dependency of node at given index.
    fn node_dep(&self, id: I, idx: usize) -> I;

    /// Returns number of dependencies of node.
    fn node_len(&self, id: I) -> usize;

    /// Returns number of nodes.
    fn len(&self) -> usize;

    /// Returns none if no cycles found, otherwise returns sequence
    /// of nodes creating the cycle. `stack` should be empty, lookup
    /// has to be as long as the number of nodes. Optionally, ordering
    /// can be passed to create order in which no children is preceding
    /// its parents.
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

/// Module test.
pub fn test() {
    const PATH: &str = "src/modules/test_project";

    let mut context = Ctx::default();

    context
        .compute_module_tree(PATH)
        .map_err(|e| panic!("{}", ErrorDisplay::new(&context, &e)))
        .unwrap();
}
