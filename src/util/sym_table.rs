use std::{collections::HashMap, ops::{Index, IndexMut}};

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
            () => {
                {
                    let i = I::new(if let Some(i) = self.free.pop() {
                        i
                    } else {
                        self.data.len()
                    });
                    self.table.insert(id, i);
                    self.data.push((id, data));
                    (None, i)
                }
            }
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
        self.table.get(&id).cloned().map(move |i| &mut self.data[i.raw()].1)
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
        let i = self.table.get(&id).cloned().unwrap_or_else(|| self.insert(id, T::default()).1);
        &mut self.data[i.raw()].1
    }
}

impl<I: SymID, T: Default> Index<I> for SymTable<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        debug_assert!(self.data[id.raw()].0 != ID::new());
        &self.data[id.raw()].1
    }
}

impl<I: SymID, T: Default> IndexMut<I> for SymTable<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
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

#[macro_export]
macro_rules! sym_id {
    ($id:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $id(usize);

        impl SymID for $id {            
            fn new(idx: usize) -> Self {
                Self(idx)
            }

            fn raw(&self) -> usize {
                self.0
            }
        }

        impl Default for $id {
            fn default() -> Self {
                Self::null()
            }
        }
    };
}

pub trait SymID: Copy + Clone {
    fn new(value: usize) -> Self;
    fn raw(&self) -> usize;

    #[inline]
    fn null() -> Self {
        Self::new(usize::MAX)
    }
}