use std::ops::Range;

use crate::{
    ast::{AContext, AKind, AMainState, Ast, AstDisplay, Vis},
    util::{
        sdbm::ID,
        storage::{IndexPointer, List, ReusableList},
    },
};

crate::index_pointer!(Attr);

/// Collector organizes ast so it can be quickly accessed by the compiler.
/// It builds a structure that preserves attributes for quick lookup.
#[derive(Debug, Clone)]
pub struct Collector {
    pub globals: Vec<Item>,
    pub types: Vec<Item>,
    pub functions: Vec<Item>,
    pub scopes: List<Scope, ScopeEnt>,
    scope: Option<Scope>,

    pub attributes: ReusableList<Attr, (Ast, bool)>,

    ordering: Vec<Attr>,
    stack: Vec<Attr>,
    frames: Vec<usize>,

    permanent_ordering: Vec<Attr>,

    marker: usize,

    push_hash: ID,
    pop_hash: ID,
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
                    self.ordering.extend(&self.stack);
                    self.marker = self.ordering.len();
                    let end = self.marker;
                    let mut item = Item {
                        scope: self.scope,
                        attrs: Attrs(start..end, false),
                        ast: item,
                    };

                    match item.ast.kind {
                        AKind::Impl(vis) => {
                            let scope = ScopeEnt {
                                attributes: self.to_permanent(item.attrs),
                                params: item.ast[0]
                                    .iter()
                                    .map(|param| param.token.span.hash)
                                    .collect(),
                                ty: std::mem::take(&mut item.ast[1]),
                            };
                            let scope = self.scopes.add(scope);
                            self.scope = Some(scope);
                            self.parse(l_state, &mut item.ast[2], vis);
                            self.scope = None;
                        }
                        AKind::Fun(fun_vis) => {
                            item.ast.kind = AKind::Fun(vis.join(fun_vis));
                            self.functions.push(item)
                        },
                        AKind::VarStatement(var_vis, mutable) => {
                            item.ast.kind = AKind::VarStatement(vis.join(var_vis), mutable);
                            self.globals.push(item)
                        },
                        AKind::StructDeclaration(_) => self.types.push(item),
                        _ => unreachable!(),
                    }
                }
                AKind::Attribute => {
                    for mut attr in item.drain(..) {
                        let hash = attr[0].token.span.hash;
                        if hash == self.pop_hash {
                            let frame = self.frames.pop().unwrap_or(0);
                            self.stack.truncate(frame);
                        } else if hash == self.push_hash {
                            self.frames.push(self.stack.len());
                            for attr in attr.drain(1..) {
                                self.stack.push(self.attributes.add((attr, false)));
                            }
                        } else {
                            let id = self.attributes.add((attr, false));
                            self.ordering.push(id);
                        }
                    }
                }
                AKind::Comment => {
                    let id = self.attributes.add((item, false));
                    self.ordering.push(id);
                }
                _ => unreachable!("{}", AstDisplay::new(l_state, &item)),
            }
        }
    }

    pub fn attr(&self, attrs: &Attrs, hash: ID) -> Option<&Ast> {
        self.attr_id(attrs, hash).map(|id| &self.attributes[id].0)
    }

    pub fn attr_id(&self, attrs: &Attrs, hash: ID) -> Option<Attr> {
        self.attrs(attrs)
            .iter()
            .find(|&&attr| 
                self.attributes[attr].0.kind != AKind::Comment && 
                self.attributes[attr].0[0].token.span.hash == hash
            )
            .copied()
    }

    pub fn attrs(&self, attrs: &Attrs) -> &[Attr] {
        if attrs.1 {
            &self.permanent_ordering[attrs.0.clone()]
        } else {
            &self.ordering[attrs.0.clone()]
        }
    }

    pub fn drain<'a>(&'a mut self, attrs: Attrs) -> impl Iterator<Item = Ast> + 'a {
        let s = unsafe { std::mem::transmute::<&mut Self, &mut Self>(self) };
        if attrs.1 {
            &self.permanent_ordering[attrs.0]
        } else {
            &self.ordering[attrs.0]
        }
        .iter()
        .filter_map(move |&attr| {
            if s.attributes[attr].1 {
                None
            } else {
                Some(s.attributes.remove(attr).0)
            }
        })
    }

    pub fn to_permanent(&mut self, range: Attrs) -> Attrs {
        let start = self.permanent_ordering.len();
        for &attr in &self.ordering[range.0.clone()] {
            self.attributes[attr].1 = true;
        }
        self.permanent_ordering
            .extend(&self.ordering[range.0.clone()]);
        let end = self.permanent_ordering.len();
        Attrs(start..end, true)
    }

    pub fn clear(&mut self, ctx: &mut AContext) {
        self.attributes.retain(|attr| {
            if attr.1 {
                true
            } else {
                ctx.recycle(std::mem::take(&mut attr.0));
                false
            }
        });

        self.globals.clear();
        self.types.clear();
        self.functions.clear();
        self.stack.clear();
        self.frames.clear();
        self.ordering.clear();
        self.marker = 0;
    }
}

impl Default for Collector {
    fn default() -> Self {
        Self {
            globals: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            scopes: Default::default(),
            scope: Default::default(),
            attributes: Default::default(),
            ordering: Default::default(),
            stack: Default::default(),
            frames: Default::default(),
            permanent_ordering: Default::default(),
            marker: Default::default(),

            push_hash: ID::new("push"),
            pop_hash: ID::new("pop"),
        }
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

#[derive(Debug, Clone, Default)]
pub struct Attrs(Range<usize>, bool);
