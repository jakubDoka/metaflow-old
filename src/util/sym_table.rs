use std::ops::{Index, IndexMut};

use super::sdbm::ID;

#[derive(Clone, Debug)]
pub struct SymTable<I: SymID, T: Default> {
    table: Vec<(ID, I)>,
    data: Vec<(ID, T)>,
    free: Vec<usize>,
}

impl<I: SymID, T: Default> SymTable<I, T> {
    pub fn new() -> Self {
        Self {
            table: Vec::new(),
            data: Vec::new(),
            free: Vec::new(),
        }
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => {
                let (_, i) = self.table[idx];
                return (Some(std::mem::replace(&mut self.data[i.raw()].1, data)), i);
            }
            Err(idx) => {
                let i = I::new(if let Some(i) = self.free.pop() {
                    i
                } else {
                    self.data.len()
                });
                self.table.insert(idx, (id, i));
                self.data.push((id, data));
                return (None, i);
            }
        };
    }

    #[inline]
    pub fn get_id(&self, id: ID) -> Option<&T> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => Some(&self.data[self.table[idx].1.raw()].1),
            Err(_) => None,
        }
    }

    #[inline]
    pub fn get_mut_id(&mut self, id: ID) -> Option<&mut T> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => Some(&mut self.data[self.table[idx].1.raw()].1),
            Err(_) => None,
        }
    }

    pub fn get_ref(&self, id: ID) -> Option<I> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => Some(self.table[idx].1),
            Err(_) => None,
        }
    }

    pub fn direct_to_id(&self, direct: I) -> ID {
        self.table[direct.raw()].0
    }

    pub fn id_to_direct(&self, id: ID) -> Option<I> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => Some(self.table[idx].1),
            Err(_) => None,
        }
    }

    pub fn remove(&mut self, id: ID) -> Option<T> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => {
                let (_, i) = self.table.remove(idx);
                let data = std::mem::take(&mut self.data[i.raw()].1);
                self.free.push(i.raw());
                return Some(data);
            }
            Err(_) => return None,
        };
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

    pub fn direct_ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(|i| I::new(i))
    }

    pub fn redirect(&mut self, id: ID, param: I) -> Option<I> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => return Some(std::mem::replace(&mut self.table[idx].1, param)),
            Err(idx) => self.table.insert(idx, (id, param)),
        }
        None
    }

    pub fn remove_redirect(&mut self, id: ID, shadowed: Option<I>) -> Option<I> {
        match self.table.binary_search_by(|(i, _)| id.cmp(i)) {
            Ok(idx) => {
                // this is not a redirect
                if self.data[self.table[idx].1.raw()].0 == id {
                    return None;
                }
                if let Some(shadowed) = shadowed {
                    self.table[idx].1 = shadowed;
                    Some(self.table[idx].1)
                } else {
                    Some(self.table.remove(idx).1)
                }
            }
            Err(_) => None,
        }
    }
}

impl<I: SymID, T: Default> Index<I> for SymTable<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.data[id.raw()].1
    }
}

impl<I: SymID, T: Default> IndexMut<I> for SymTable<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
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

#[macro_export]
macro_rules! sym_id {
    ($id:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
        pub struct $id(usize);

        impl SymID for $id {
            fn new(idx: usize) -> Self {
                Self(idx)
            }

            fn raw(&self) -> usize {
                self.0
            }
        }
    };
}

pub trait SymID: Copy + Clone {
    fn new(value: usize) -> Self;
    fn raw(&self) -> usize;
}
