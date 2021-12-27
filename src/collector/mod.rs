use crate::{
    ast::{AKind, AMainState, Ast, AstDisplay, Vis},
    util::{
        sdbm::ID,
        storage::{IndexPointer, List, ReusableList},
    },
};

crate::index_pointer!(Attr);

/// Collector organizes ast so it can be quickly accessed by the compiler.
/// It builds a structure that preserves attributes for quick lookup.
#[derive(Debug, Clone, Default)]
pub struct Collector {
    pub globals: Vec<Item>,
    pub types: Vec<Item>,
    pub functions: Vec<Item>,
    pub scopes: List<Scope, ScopeEnt>,
    scope: Option<Scope>,

    pub attributes: ReusableList<Attr, Ast>,

    ordering: Vec<Attr>,
    stack: Vec<Attr>,
    frames: Vec<usize>,

    marker: usize,
}

impl Collector {
    pub fn parse(&mut self, l_state: &AMainState, ast: &mut Ast, vis: Vis) {
        for mut item in ast.drain(..) {
            match item.kind {
                AKind::Fun(_)
                | AKind::Impl(_)
                | AKind::VarStatement(_, _)
                | AKind::StructDeclaration(_) => {
                    let start = self.marker;
                    let no_stack_end = self.ordering.len();
                    self.ordering.extend(&self.stack);
                    self.marker = self.ordering.len();
                    let end = self.marker;
                    let mut item = Item {
                        scope: self.scope,
                        attrs: Attrs(start as u32, end as u32),
                        ast: item,
                    };

                    match item.ast.kind {
                        AKind::Impl(vis) => {
                            let scope = ScopeEnt {
                                attributes: item.attrs,
                                params: item.ast[0]
                                    .iter()
                                    .map(|param| param.token.span.hash)
                                    .collect(),
                                ty: std::mem::take(&mut item.ast[1]),
                            };
                            self.frames.push(self.stack.len());
                            self.stack.extend(&self.ordering[start..no_stack_end]);
                            let scope = self.scopes.add(scope);
                            self.scope = Some(scope);
                            self.parse(l_state, &mut item.ast[2], vis);
                            self.scope = None;
                            self.stack.truncate(self.frames.pop().unwrap_or(0));
                        }
                        AKind::Fun(fun_vis) => {
                            item.ast.kind = AKind::Fun(vis.join(fun_vis));
                            self.functions.push(item)
                        }
                        AKind::VarStatement(var_vis, mutable) => {
                            item.ast.kind = AKind::VarStatement(vis.join(var_vis), mutable);
                            self.globals.push(item)
                        }
                        AKind::StructDeclaration(_) => self.types.push(item),
                        _ => unreachable!(),
                    }
                }
                AKind::Attribute => {
                    for mut attr in item.drain(..) {
                        let hash = attr[0].token.span.hash;
                        if hash == ID::new("pop") {
                            let frame = self.frames.pop().unwrap_or(0);
                            self.stack.truncate(frame);
                        } else if hash == ID::new("push") {
                            self.frames.push(self.stack.len());
                            for attr in attr.drain(1..) {
                                self.stack.push(self.attributes.add(attr));
                            }
                        } else {
                            let id = self.attributes.add(attr);
                            self.ordering.push(id);
                        }
                    }
                }
                AKind::Comment => {
                    let id = self.attributes.add(item);
                    self.ordering.push(id);
                }
                _ => unreachable!("{}", AstDisplay::new(l_state, &item)),
            }
        }
    }

    pub fn attr(&self, attrs: &Attrs, hash: ID) -> Option<&Ast> {
        self.attr_id(attrs, hash).map(|id| &self.attributes[id])
    }

    pub fn attr_id(&self, attrs: &Attrs, hash: ID) -> Option<Attr> {
        self.ordering[attrs.0 as usize..attrs.1 as usize]
            .iter()
            .find(|&&attr| {
                self.attributes[attr].kind != AKind::Comment
                    && self.attributes[attr][0].token.span.hash == hash
            })
            .copied()
    }

    pub fn clear(&mut self) {
        self.globals.clear();
        self.types.clear();
        self.functions.clear();
        self.stack.clear();
        self.frames.clear();
        self.ordering.clear();
        self.marker = 0;
    }
}

crate::index_pointer!(Scope);

#[derive(Debug, Clone, Default)]
pub struct ScopeEnt {
    pub attributes: Attrs,
    pub params: Vec<ID>,
    pub ty: Ast,
}

#[derive(Debug, Clone, Default)]
pub struct Item {
    pub scope: Option<Scope>,
    pub attrs: Attrs,
    pub ast: Ast,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Attrs(u32, u32);
