use crate::{
    ast::{AKind, Ast},
    util::{
        sdbm::{SdbmHashState, ID},
        storage::{IndexPointer, Table},
    },
};

crate::index_pointer!(Attribute);

#[derive(Debug, Clone, Default)]
pub struct Attributes {
    pub map: Table<Attribute, Ast>,
    pub stack: Vec<Attribute>,
}

impl Attributes {
    pub fn parse(&mut self, ast: &mut Ast) {
        let mut marker = 0;
        let mut i = 0;
        while i < ast.len() {
            if ast[i].kind != AKind::Attribute {
                for &stacked in &self.stack {
                    for attr in 1..self.map[stacked].len() {
                        let id = ID(0)
                            .add(self.map[stacked][attr][0].token.spam.raw())
                            .combine(ID(marker as u64));
                        self.map.link(id, stacked);
                    }
                }
                if marker < i {
                    ast.drain(marker..i).for_each(|mut attr| {
                        attr.drain(..).for_each(|ast| {
                            let id = ID(0)
                                .add(ast[0].token.spam.raw())
                                .combine(ID(marker as u64));
                            let (_, id) = self.map.insert(id, ast);
                            match self.map[id][0].token.spam.raw() {
                                "push" => {
                                    self.stack.push(id);
                                }
                                "pop" => {
                                    self.stack.pop();
                                }
                                _ => (),
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
        self.get_attr(idx, name).is_some()
    }

    pub fn get_attr(&self, idx: usize, name: &str) -> Option<&Ast> {
        let id = ID(0).add(name).combine(ID(idx as u64));

        self.map.get(id)
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.stack.clear();
    }
}
