use std::ops::Deref;

use crate::{
    ast::{AKind, Ast},
    util::{
        sdbm::{SdbmHashState, ID},
        sym_table::{SymID, SymTable},
    },
};

crate::sym_id!(Attribute);

#[derive(Debug, Clone, Default)]
pub struct Attributes {
    pub map: SymTable<Attribute, Ast>,
    pub stack: Vec<Attribute>,
}

impl Attributes {
    pub fn resolve(&mut self, ast: &mut Ast) -> Attributes {
        let mut marker = 0;
        let mut i = 0;
        while i < ast.len() {
            if ast[i].kind != AKind::Attribute {
                for &stacked in &self.stack {
                    let id = ID::new()
                        .add(self.map[stacked][0].token.spam.deref())
                        .add(i);
                    self.map.redirect(id, stacked);
                }
                if marker < i {
                    ast.drain(marker..i).for_each(|mut attr| {
                        attr.drain(..).for_each(|ast| {
                            let id = ID::new().add(ast[0].token.spam.deref()).add(i);
                            let (_, id) = self.map.insert(id, ast);
                            match self.map[id][0].token.spam.deref() {
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
                }
                marker = i + 1;
            }
            i += 1;
        }

        self.stack.clear();
        let clone = self.clone();
        self.map.clear();
        clone
    }

    pub fn enabled(&self, idx: usize, name: &str) -> bool {
        self.get_attr(idx, name).is_some()
    }

    pub fn get_attr(&self, idx: usize, name: &str) -> Option<&Ast> {
        let id = ID::new().add(name).add(idx);

        self.map.get_id(id)
    }
}
