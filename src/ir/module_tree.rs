use std::{ops::Deref, path::Path};

use crate::{
    ast::{AKind, AstError, AstParser},
    lexer::{Lexer, Token},
    util::sdbm::SdbmHashState,
};

use super::*;

type Result<T> = std::result::Result<T, ModTreeError>;

#[derive(Clone, Default)]
pub struct ModTreeBuilder {
    import_stack: Vec<Cell<Mod>>,
    base: String,
    buffer: String,
    program: Program,
    module_id_counter: u64,
}

impl ModTreeBuilder {
    pub fn build(mut self, root: &str) -> Result<Program> {
        self.base = root[..root.rfind('/').map(|i| i + 1).unwrap_or(root.len())].to_string();
        self.load_module(&root[root.rfind('/').unwrap_or(0)..], &Token::default())?;

        Ok(self.program)
    }

    pub fn load_module(&mut self, path: &str, token: &Token) -> Result<Cell<Mod>> {
        self.load_path(path);

        let id = ID::new().add(&self.buffer);

        if let Some(module) = self.program.mods.iter().find(|m| m.id == id) {
            return Ok(module.clone());
        }

        let file = std::fs::read_to_string(self.buffer.as_str())
            .map_err(|err| ModTreeError::new(MTEKind::Io(err), token))?;
        let absolute_path = Path::new(self.buffer.as_str())
            .canonicalize()
            .map_err(|err| ModTreeError::new(MTEKind::Io(err), token))?
            .to_str()
            .ok_or_else(|| ModTreeError::new(MTEKind::NonUTF8Path, token))?
            .to_string();

        let ast = AstParser::new(Lexer::new(id, path.to_string(), file))
            .parse()
            .map_err(|err| ModTreeError::new(MTEKind::Ast(err), &Token::default()))?;

        let name = Path::new(path)
            .file_stem()
            .ok_or_else(|| ModTreeError::new(MTEKind::NoFileStem, token))?
            .to_str()
            .ok_or_else(|| ModTreeError::new(MTEKind::NonUTF8Path, token))?;

        let name = ID::new().add(name);

        if let Some(idx) = self.import_stack.iter().position(|m| m.name == name) {
            let message = self.import_stack[idx..]
                .iter()
                .map(|m| &m.absolute_path)
                .chain(std::iter::once(&absolute_path))
                .fold(String::new(), |mut acc, path| {
                    acc.push_str(path);
                    acc.push_str("\n");
                    acc
                });
            return Err(ModTreeError::new(MTEKind::CyclicDependency(message), token));
        }

        let mut module = Cell::new(Mod {
            name,
            id,
            absolute_path,
            dependency: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            ast,
            is_external: false,
        });

        self.import_stack.push(module.clone());

        crate::retain!(module.ast, |a| {
            if let AKind::UseStatement(external, export) = a.kind {
                if external {
                    todo!("external package use not implemented");
                }
                let path = a[1].token.spam.deref();
                let m = self.load_module(&path[1..path.len() - 1], &a[1].token)?; // strip "
                let nickname = if a[0].kind != AKind::None {
                    ID::new().add(a[0].token.spam.deref())
                } else {
                    m.name
                };
                module.dependency.push((nickname, m.clone()));
                if export {
                    module.exports.push(m.clone());
                }
                false
            } else {
                true
            }
        });

        self.import_stack.pop().unwrap(); // unwrap may catch a bug

        self.program.mods.push(module.clone());

        Ok(module)
    }

    fn load_path(&mut self, path: &str) {
        self.buffer.clear();
        self.buffer.push_str(self.base.as_str());
        self.buffer.push_str(path);
        self.buffer.push_str(crate::FILE_EXTENSION);
    }
}

#[derive(Debug)]
pub struct ModTreeError {
    pub kind: MTEKind,
    pub token: Token,
}

impl ModTreeError {
    pub fn new(kind: MTEKind, token: &Token) -> Self {
        Self {
            kind,
            token: token.clone(),
        }
    }
}

#[derive(Debug)]
pub enum MTEKind {
    Io(std::io::Error),
    Ast(AstError),
    NonUTF8Path,
    NoFileStem,
    CyclicDependency(String),
}

pub fn test() {
    let builder = ModTreeBuilder::default();
    let _program = builder.build("src/ir/tests/module_tree/root").unwrap();
}
