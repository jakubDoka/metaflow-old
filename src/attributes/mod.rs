use crate::{
    ast::{AKind, Ast},
    lexer::LMainState,
    util::{
        sdbm::ID,
        storage::{IndexPointer, Table},
    },
};

crate::index_pointer!(Attribute);

#[derive(Debug, Clone, Default)]
pub struct Attributes {
    pub map: Table<Attribute, Ast>,
    pub stack: Vec<Attribute>,
    pub frames: Vec<usize>,
}

impl Attributes {
    pub fn parse(&mut self, state: &LMainState, ast: &mut Ast) {
        let mut marker = 0;
        let mut i = 0;
        while i < ast.len() {
            if ast[i].kind != AKind::Attribute {
                for &stacked in &self.stack {
                    for attr in 1..self.map[stacked].len() {
                        let id = self.map[stacked][attr][0]
                            .token
                            .spam
                            .hash
                            .add(ID(marker as u64));
                        let shadowed = self.map.link(id, stacked);
                        debug_assert!(shadowed.is_none());
                    }
                }
                if marker < i {
                    ast.drain(marker..i).for_each(|mut attr| {
                        attr.drain(..)
                            .for_each(|mut ast| match state.display(&ast[0].token.spam) {
                                "push" => {
                                    self.frames.push(ast.len());
                                    for ast in ast.drain(1..) {
                                        let id = self.map.add_hidden(ast);
                                        self.stack.push(id);
                                    }
                                }
                                "pop" => {
                                    let len = self.frames.pop().unwrap_or(0);
                                    self.stack.truncate(len);
                                }
                                _ => {
                                    let id = ast[0].token.spam.hash.add(ID(marker as u64));
                                    self.map.insert(id, ast);
                                }
                            })
                    });
                    i = marker;
                }

                marker = i + 1;
            }
            i += 1;
        }
    }

    pub fn enabled(&self, idx: usize, name: &str) -> bool {
        self.attr(idx, name).is_some()
    }

    pub fn attr(&self, idx: usize, name: &str) -> Option<&Ast> {
        let id = ID::new(name).add(ID(idx as u64));

        self.map.get(id)
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.stack.clear();
    }
}
