use std::{
    collections::HashMap,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use super::sdbm::ID;

#[derive(Clone, Debug)]
pub struct SymTable<I: SymID, T: Default> {
    table: HashMap<ID, I>,
    data: Vec<(ID, T)>,
    free: Vec<usize>,
}

impl<I: SymID, T: Default> SymTable<I, T> {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
            data: Vec::new(),
            free: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.table.clear();
        self.data.clear();
        self.free.clear();
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        macro_rules! insert {
            () => {{
                let i = I::new(if let Some(i) = self.free.pop() {
                    i
                } else {
                    self.data.len()
                });
                self.table.insert(id, i);
                self.data.push((id, data));
                (None, i)
            }};
        }

        match self.table.get(&id) {
            Some(i) => {
                if self.data[i.raw()].0 != id {
                    insert!()
                } else {
                    (Some(std::mem::replace(&mut self.data[i.raw()].1, data)), *i)
                }
            }
            None => {
                insert!()
            }
        }
    }

    #[inline]
    pub fn get_id(&self, id: ID) -> Option<&T> {
        self.table.get(&id).map(|i| &self.data[i.raw()].1)
    }

    #[inline]
    pub fn get_mut_id(&mut self, id: ID) -> Option<&mut T> {
        self.table
            .get(&id)
            .cloned()
            .map(move |i| &mut self.data[i.raw()].1)
    }

    pub fn direct_to_id(&self, direct: I) -> ID {
        self.data[direct.raw()].0
    }

    pub fn id_to_direct(&self, id: ID) -> Option<I> {
        self.table.get(&id).cloned()
    }

    pub fn remove(&mut self, id: ID) -> Option<T> {
        self.table.remove(&id).map(|i| {
            self.free.push(i.raw());
            std::mem::take(&mut self.data[i.raw()].1)
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter().map(|x| &x.1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut().map(|x| &mut x.1)
    }

    pub unsafe fn as_mut<'a>(&self) -> &'a mut Self {
        &mut *(self as *const _ as *mut _)
    }

    pub unsafe fn direct_ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(|i| I::new(i))
    }

    pub fn is_direct_valid(&self, direct: I) -> bool {
        self.data[direct.raw()].0 != ID::new()
    }

    pub fn redirect(&mut self, id: ID, param: I) -> Option<I> {
        match self.table.get_mut(&id) {
            Some(idx) => return Some(std::mem::replace(idx, param)),
            None => self.table.insert(id, param),
        };
        None
    }

    pub fn remove_redirect(&mut self, id: ID, shadowed: Option<I>) -> Option<I> {
        match self.table.get_mut(&id) {
            Some(idx) => {
                // this is not a redirect
                if self.data[idx.raw()].0 == id {
                    return None;
                }
                if let Some(shadowed) = shadowed {
                    let current = *idx;
                    *idx = shadowed;
                    Some(current)
                } else {
                    Some(self.table.remove(&id).unwrap())
                }
            }
            None => None,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &ID> {
        self.table.keys()
    }

    pub fn get_mut_or_default(&mut self, id: ID) -> &mut T {
        let i = self
            .table
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.insert(id, T::default()).1);
        &mut self.data[i.raw()].1
    }
}

impl<I: SymID, T: Default> Index<I> for SymTable<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        debug_assert!(!id.is_null());
        debug_assert!(self.data[id.raw()].0 != ID::new());
        &self.data[id.raw()].1
    }
}

impl<I: SymID, T: Default> IndexMut<I> for SymTable<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        debug_assert!(!id.is_null());
        debug_assert!(self.data[id.raw()].0 != ID::new());
        &mut self.data[id.raw()].1
    }
}

impl<I: SymID, T: Default> Index<ID> for SymTable<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        self.get_id(id).unwrap()
    }
}

impl<I: SymID, T: Default> IndexMut<ID> for SymTable<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        self.get_mut_id(id).unwrap()
    }
}

impl<I: SymID, T: Default> Default for SymTable<I, T> {
    fn default() -> Self {
        Self {
            table: Default::default(),
            data: Default::default(),
            free: Default::default(),
        }
    }
}

#[derive(Debug, Default)]
pub struct LockedSymVec<I: SymID, T> {
    inner: SymVec<I, T>,
}

impl<I: SymID, T> LockedSymVec<I, T> {
    pub fn new(inner: SymVec<I, T>) -> Self {
        Self { inner }
    }

    // SAFETY: ensure that LockedSymVec does not get dropped
    // while reference still lives
    pub unsafe fn get<'a>(&self, id: I) -> &'a T {
        std::mem::transmute::<_, &T>(&self.inner[id])
    }
}

impl<I: SymID, T> Index<I> for LockedSymVec<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.inner[id]
    }
}

impl<I: SymID, T> IndexMut<I> for LockedSymVec<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.inner[id]
    }
}

#[derive(Debug)]
pub struct SymVec<I: SymID, T> {
    data: Vec<T>,
    p: PhantomData<I>,
}

impl<I: SymID, T> SymVec<I, T> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            p: PhantomData,
        }
    }

    pub fn add(&mut self, data: T) -> I {
        self.data.push(data);
        I::new(self.data.len() - 1)
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }

    pub fn iter(&self) -> impl Iterator<Item = (I, &T)> {
        self.data.iter().enumerate().map(|(i, d)| (I::new(i), d))
    }
}

impl<I: SymID, T: Clone> Clone for SymVec<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            p: PhantomData,
        }
    }
}

impl<I: SymID, T> Default for SymVec<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: SymID, T> Index<I> for SymVec<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        debug_assert!(!id.is_null());
        &self.data[id.raw()]
    }
}

impl<I: SymID, T> IndexMut<I> for SymVec<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        debug_assert!(!id.is_null());
        &mut self.data[id.raw()]
    }
}

#[macro_export]
macro_rules! sym_id {
    ($id:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $id(usize);

        impl $id {
            pub const NULL: Self = Self(usize::MAX);
        }

        impl SymID for $id {
            fn new(idx: usize) -> Self {
                Self(idx)
            }

            fn raw(&self) -> usize {
                self.0
            }

            fn is_null(&self) -> bool {
                self.0 == usize::MAX
            }
        }

        impl Default for $id {
            fn default() -> Self {
                Self::NULL
            }
        }

        impl std::fmt::Display for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                if self.is_null() {
                    write!(f, "NULL")
                } else {
                    write!(f, "{}{}", stringify!($id), self.0)
                }
            }
        }
    };
}

pub trait SymID: Copy + Clone {
    fn new(value: usize) -> Self;
    fn raw(&self) -> usize;
    fn is_null(&self) -> bool;
}
