pub mod module_tree;
pub mod types;

use std::ops::Deref;

use crate::{
    ast::{AKind, Ast, Visibility},
    lexer::Spam,
    util::{cell::Cell, sdbm::ID},
};

#[derive(Clone, Default, Debug)]
pub struct Program {
    pub mods: Vec<Cell<Mod>>,
}

#[derive(Clone, Debug)]
pub struct Mod {
    pub name: ID,
    pub id: ID,
    pub absolute_path: String,
    pub dependency: Vec<(ID, Cell<Mod>)>,
    pub exports: Vec<Cell<Mod>>,

    pub types: Vec<(ID, Cell<Datatype>)>,

    pub ast: Ast,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Datatype {
    pub visibility: Visibility,
    pub kind: DKind,
    pub name: ID,
    pub ast: Ast,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DKind {
    Unresolved,
    Builtin,
    Generic,
    Pointer(Cell<Datatype>),
    Structure(Structure),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Structure {
    pub kind: SKind,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SKind {
    Struct,
    Union,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub visibility: Visibility,
    pub embedded: bool,
    pub offset: u32,
    pub name: Spam,
    pub datatype: Cell<Datatype>,
}

pub fn test() {
    module_tree::test();

    let mut vec = vec![1, 2, 3, 4, 5];

    crate::retain!(vec, |x| *x % 2 == 0);

    assert_eq!(vec, vec![2, 4]);
}

#[macro_export]
macro_rules! retain {
    ($vec:expr, |$i:ident, $e:ident| $body:expr) => {
        let mut j = 0;
        #[allow(unused_variables)]
        for $i in 0..$vec.len() {
            let $e = &mut $vec[$i];
            #[allow(unused_braces)]
            if $body {
                $vec[j] = std::mem::take(&mut $vec[$i]);
                j += 1;
            }
        }

        $vec.truncate(j);
    };

    ($vec:expr, |$e:ident| $body:expr) => {
        crate::retain!($vec, |i, $e| $body)
    };
}
