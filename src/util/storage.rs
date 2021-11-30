use std::{
    collections::HashMap,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use super::sdbm::ID;

#[derive(Clone, Debug)]
pub struct Table<I: SymID, T> {
    table: HashMap<ID, I>,
    data: Vec<(ID, T)>,
    free: Vec<usize>,
}

impl<I: SymID, T> Table<I, T> {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
            data: vec![],
            free: vec![],
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
            unsafe { std::mem::replace(&mut self.data[i.raw()], std::mem::zeroed()).1 }
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter().filter(|x| x.0 != ID::new()).map(|x| &x.1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data
            .iter_mut()
            .filter(|x| x.0 != ID::new())
            .map(|x| &mut x.1)
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

    pub fn get_mut_or(&mut self, id: ID, data: T) -> &mut T {
        let i = self
            .table
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.insert(id, data).1);
        &mut self.data[i.raw()].1
    }
}

impl<I: SymID, T> Index<I> for Table<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        debug_assert!(self.data[id.raw()].0 != ID::new(), "invalid direct index",);
        &self.data[id.raw()].1
    }
}

impl<I: SymID, T> IndexMut<I> for Table<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        debug_assert!(self.data[id.raw()].0 != ID::new(), "invalid direct index",);
        &mut self.data[id.raw()].1
    }
}

impl<I: SymID, T> Index<ID> for Table<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        self.get_id(id).unwrap()
    }
}

impl<I: SymID, T> IndexMut<ID> for Table<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        self.get_mut_id(id).unwrap()
    }
}

impl<I: SymID, T> Default for Table<I, T> {
    fn default() -> Self {
        Self {
            table: Default::default(),
            data: Default::default(),
            free: Default::default(),
        }
    }
}

#[derive(Debug)]
pub struct LinkedList<I: SymID, T> {
    data: Vec<(I, T, I)>,
    free: Vec<I>,
}

impl<I: SymID, T> LinkedList<I, T> {
    pub fn new() -> Self {
        Self {
            data: vec![unsafe { std::mem::zeroed() }],
            free: vec![],
        }
    }

    pub fn push(&mut self, data: T) -> I {
        let last = self.data[0].0;

        let id = self.allocate(last, data, I::new(0));

        self.data[id.raw()].0 = last;
        self.data[0].0 = id;
        self.data[last.raw()].2 = id;
        id
    }

    pub fn insert(&mut self, id: I, data: T) -> I {
        let previous = id;
        let after = self.data[previous.raw()].2;

        let id = self.allocate(previous, data, after);

        self.data[previous.raw()].2 = id;
        self.data[after.raw()].0 = id;

        id
    }

    pub fn add_hidden(&mut self, data: T) -> I {
        self.allocate(I::new(0), data, I::new(0))
    }

    pub fn hide(&mut self, id: I) {
        let previous = self.data[id.raw()].0;
        let after = self.data[id.raw()].2;

        self.data[previous.raw()].2 = after;
        self.data[after.raw()].0 = previous;

        self.data[id.raw()].0 = I::new(0);
        self.data[id.raw()].2 = I::new(0);
    }

    pub fn show_as_last(&mut self, id: I) {
        let last = self.data[0].0;
        self.show(id, last);
    }

    pub fn show(&mut self, id: I, at: I) {
        debug_assert!(
            self.data[id.raw()].0 == I::new(0) && self.data[id.raw()].2 == I::new(0),
            "element is already visible",
        );

        let previous = at;
        let after = self.data[at.raw()].2;

        self.data[previous.raw()].2 = id;
        self.data[after.raw()].0 = id;

        self.data[id.raw()].0 = previous;
        self.data[id.raw()].2 = after;
    }

    pub fn last(&self) -> Option<I> {
        self.previous(I::new(0))
    }

    pub fn first(&self) -> Option<I> {
        self.next(I::new(0))
    }

    pub fn remove(&mut self, id: I) -> T {
        let previous = self.data[id.raw()].0;
        let after = self.data[id.raw()].2;

        self.data[previous.raw()].2 = after;
        self.data[after.raw()].0 = previous;

        self.free.push(id);

        std::mem::replace(&mut self.data[id.raw()].1, unsafe { std::mem::zeroed() })
    }

    pub fn iter(&self) -> impl Iterator<Item = (I, &T)> {
        LinkedListIter::new(self)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (I, &mut T)> {
        LinkedListIterMut::new(self)
    }

    pub fn clear(&mut self) {
        self.data.truncate(1);
        self.free.clear();
        self.data[0].0 = I::new(0);
        self.data[0].2 = I::new(0);
    }

    pub fn next(&self, id: I) -> Option<I> {
        let id = self.data[id.raw()].2;
        if id == I::new(0) {
            None
        } else {
            Some(id)
        }
    }

    pub fn previous(&self, id: I) -> Option<I> {
        let id = self.data[id.raw()].0;
        if id == I::new(0) {
            None
        } else {
            Some(id)
        }
    }

    fn allocate(&mut self, previous: I, data: T, after: I) -> I {
        if let Some(id) = self.free.pop() {
            self.data[id.raw()] = (previous, data, after);
            id
        } else {
            self.data.push((previous, data, after));
            I::new(self.data.len() - 1)
        }
    }
}

impl<I: SymID, T> Index<I> for LinkedList<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.data[index.raw()].1
    }
}

impl<I: SymID, T> IndexMut<I> for LinkedList<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.data[index.raw()].1
    }
}

impl<I: SymID, T> Default for LinkedList<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: SymID, T: Clone> Clone for LinkedList<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            free: self.free.clone(),
        }
    }
}

macro_rules! impl_linked_iter {
    ($name:ident $($modifier:tt)*) => {
        pub struct $name<'a, I: SymID, T: 'a> {
            list: &'a $($modifier)* LinkedList<I, T>,
            current: Option<I>,
        }

        impl <'a, I: SymID, T: 'a> $name<'a, I, T> {
            pub fn new(list: &'a $($modifier)* LinkedList<I, T>) -> Self {
                Self {
                    current: Some(I::new(0)),
                    list,
                }
            }
        }



        impl <'a, I: SymID, T: 'a> Iterator for $name<'a, I, T> {
            type Item = (I, &'a $($modifier)* T);

            fn next(&mut self) -> Option<Self::Item> {
                self.current.map(|id| {
                    let next =  self.list.data[id.raw()].2;
                    let (_, data, _) = unsafe {
                        std::mem::transmute::<_, & $($modifier)* (I, T, I)>(
                            & $($modifier)* self.list.data[next.raw()]
                        )
                    };
                    if I::new(0) == next {
                        self.current = None;
                        return None;
                    }
                    self.current = Some(next);
                    Some((next, data))
                }).flatten()
            }
        }
    };
}

impl_linked_iter!(LinkedListIter);
impl_linked_iter!(LinkedListIterMut mut);

#[derive(Debug)]
pub struct LockedList<I: SymID, T> {
    inner: List<I, T>,
}

impl<I: SymID, T> LockedList<I, T> {
    pub fn new(inner: List<I, T>) -> Self {
        Self { inner }
    }

    // SAFETY: ensure that LockedList does not get dropped
    // while reference still lives
    pub unsafe fn get<'a>(&self, id: I) -> &'a T {
        std::mem::transmute::<_, &T>(&self.inner[id])
    }
}

impl<I: SymID, T> Default for LockedList<I, T> {
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}

impl<I: SymID, T> Index<I> for LockedList<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.inner[id]
    }
}

impl<I: SymID, T> IndexMut<I> for LockedList<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.inner[id]
    }
}

#[derive(Debug)]
pub struct List<I: SymID, T> {
    data: Vec<T>,
    p: PhantomData<I>,
}

impl<I: SymID, T> List<I, T> {
    pub fn new() -> Self {
        Self {
            data: vec![],
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

    pub fn ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(I::new)
    }
}

impl<I: SymID, T: Clone> Clone for List<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            p: PhantomData,
        }
    }
}

impl<I: SymID, T> Default for List<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: SymID, T> Index<I> for List<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.data[id.raw()]
    }
}

impl<I: SymID, T> IndexMut<I> for List<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id.raw()]
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

        impl std::fmt::Display for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}{}", stringify!($id), self.0)
            }
        }
    };
}

pub trait SymID: Copy + Clone + PartialEq + Eq {
    fn new(value: usize) -> Self;
    fn raw(&self) -> usize;
}

crate::sym_id!(Dummy);

pub fn test() {
    let mut ll = LinkedList::<Dummy, usize>::new();

    println!("{}", ll.push(0));

    println!("{:?}", ll.iter().collect::<Vec<_>>());

    println!("{:?}", ll.remove(Dummy::new(1)));

    println!("{:?}", ll.add_hidden(0));

    println!("{:?}", ll.iter().collect::<Vec<_>>());

    ll.show_as_last(Dummy::new(1));

    println!("{:?}", ll.iter().collect::<Vec<_>>());
}
