use std::{ops::Deref, path::Path};

use crate::{
    ast::{AEKind, AKind, AstError, AstParser},
    lexer::{Lexer, Token},
    util::{self, sdbm::SdbmHashState},
};

use super::attributes::Attributes;
use super::*;

type Result<T> = std::result::Result<T, ModuleTreeError>;

#[derive(Default)]
pub struct ModuleTreeBuilder {
    import_stack: Vec<ID>,
    base: String,
    buffer: String,
    program: Program,
    module_id_counter: u64,
    attributes: Attributes,
}

impl ModuleTreeBuilder {
    pub fn build(mut self, root: &str) -> Result<Program> {
        self.program.build_builtin();

        self.base = root[..root.rfind('/').map(|i| i + 1).unwrap_or(root.len())].to_string();
        self.load_module(&root[root.rfind('/').unwrap_or(0)..], &Token::default())?;

        Ok(self.program)
    }

    fn load_module(&mut self, path: &str, token: &Token) -> Result<Module> {
        self.load_path(path);

        let id = ID::new().add(&self.buffer);

        if let Some(idx) = self.import_stack.iter().position(|&m| m == id) {
            let absolute_path = Path::new(self.buffer.as_str())
                .canonicalize()
                .map_err(|err| ModuleTreeError::new(MTEKind::Io(err), token))?
                .to_str()
                .ok_or_else(|| ModuleTreeError::new(MTEKind::NonUTF8Path, token))?
                .to_string();

            let message = self.import_stack[idx..]
                .iter()
                .map(|m| {
                    self.program
                        .modules
                        .get_id(*m)
                        .unwrap()
                        .absolute_path
                        .as_str()
                })
                .chain(std::iter::once(absolute_path.as_str()))
                .fold(String::new(), |mut acc, path| {
                    acc.push_str(path);
                    acc.push_str("\n");
                    acc
                });
            return Err(ModuleTreeError::new(
                MTEKind::CyclicDependency(message),
                token,
            ));
        }

        self.import_stack.push(id);

        if let Some(module) = self.program.modules.id_to_direct(id) {
            return Ok(module);
        }

        let file = std::fs::read_to_string(self.buffer.as_str())
            .map_err(|err| ModuleTreeError::new(MTEKind::Io(err), token))?;
        let absolute_path = Path::new(self.buffer.as_str())
            .canonicalize()
            .map_err(|err| ModuleTreeError::new(MTEKind::Io(err), token))?
            .to_str()
            .ok_or_else(|| ModuleTreeError::new(MTEKind::NonUTF8Path, token))?
            .to_string();

        let ast = AstParser::new(Lexer::new(id, path.to_string(), file))
            .parse()
            .map_err(Into::into)?;

        let name = Path::new(path)
            .file_stem()
            .ok_or_else(|| ModuleTreeError::new(MTEKind::NoFileStem, token))?
            .to_str()
            .ok_or_else(|| ModuleTreeError::new(MTEKind::NonUTF8Path, token))?;

        let name = ID::new().add(name);

        let module = ModuleEnt {
            name,
            id,
            absolute_path,
            ast,

            dependency: vec![(ID::new().add("builtin"), self.program.builtin)],

            ..Default::default()
        };

        let (_, module_id) = self.program.modules.insert(id, module);

        let mut ast = std::mem::take(&mut self.program[module_id].ast);
        util::try_retain(&mut ast, |a| {
            if let AKind::UseStatement(external) = a.kind {
                if external {
                    todo!("external package use not implemented");
                }
                let path = a[1].token.spam.deref();
                let m_id = self.load_module(&path[1..path.len() - 1], &a[1].token)?; // strip "
                let m = &mut self.program[m_id];
                let nickname = if a[0].kind != AKind::None {
                    ID::new().add(a[0].token.spam.deref())
                } else {
                    m.name
                };
                m.dependant.push(module_id);
                let module = &mut self.program[module_id];
                module.dependency.push((nickname, m_id));
                Ok(false)
            } else {
                Ok(true)
            }
        })?;

        let attributes = self.attributes.resolve(&mut ast);

        let module = &mut self.program[module_id];
        module.ast = ast;
        module.attributes = attributes;

        self.import_stack
            .pop()
            .expect("expected previously pushed element");

        Ok(module_id)
    }

    fn load_path(&mut self, path: &str) {
        self.buffer.clear();
        self.buffer.push_str(self.base.as_str());
        self.buffer.push_str(path);
        self.buffer.push_str(crate::FILE_EXTENSION);
    }
}

#[derive(Debug)]
pub struct ModuleTreeError {
    pub kind: MTEKind,
    pub token: Token,
}

impl ModuleTreeError {
    pub fn new(kind: MTEKind, token: &Token) -> Self {
        Self {
            kind,
            token: token.clone(),
        }
    }
}

impl Into<ModuleTreeError> for AstError {
    fn into(self) -> ModuleTreeError {
        ModuleTreeError {
            kind: MTEKind::Ast(self.kind),
            token: self.token,
        }
    }
}

#[derive(Debug)]
pub enum MTEKind {
    Io(std::io::Error),
    Ast(AEKind),
    NonUTF8Path,
    NoFileStem,
    CyclicDependency(String),
}

pub fn test() {
    let builder = ModuleTreeBuilder::default();
    let _program = builder.build("src/ir/tests/module_tree/root").unwrap();
}
