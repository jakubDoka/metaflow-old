use std::{
    ops::{Index, IndexMut},
};

use cranelift::codegen::entity::{EntityRef, PrimaryMap};
use quick_proc::QuickSer;

use super::sdbm::ID;

#[derive(Clone, Debug, QuickSer)]
pub struct Map<V> {
    cache: Vec<Vec<Value<V>>>,
    size: u32,
    mod_mask: u64,
    count: usize,
}

#[derive(Clone, Debug, QuickSer)]
pub struct Value<V>(ID, V);

impl<V> Map<V> {
    pub fn new() -> Self {
        Map::with_capacity(4)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut map = Map {
            cache: Vec::new(),
            size: 0,
            count: 0,
            mod_mask: 0,
        };

        map.increase_cache();

        while map.lim() < capacity {
            map.increase_cache();
        }

        map
    }

    pub fn reserve(&mut self, additional: usize) {
        let capacity = (self.count + additional).next_power_of_two();
        while self.lim() < capacity {
            self.increase_cache();
        }
    }

    pub fn insert(&mut self, key: ID, value: V) -> Option<V> {
        let ix = self.calc_index(key);

        {
            let ref mut vals = self.cache[ix];
            for kv in vals.iter_mut() {
                if kv.0 == key {
                    return Some(std::mem::replace(&mut kv.1, value));
                }
            }

            self.count += 1;
            vals.push(Value(key, value));
        }
        if (self.count & 4) == 4 {
            self.ensure_load_rate();
        }

        None
    }

    pub fn get(&self, key: ID) -> Option<&V> {
        let ix = self.calc_index(key);

        let ref vals = self.cache[ix];

        if vals.len() > 0 {
            for kv in vals.iter() {
                if kv.0 == key {
                    return Some(&kv.1);
                }
            }

            return None;
        } else {
            return None;
        }
    }

    pub fn get_mut(&mut self, key: ID) -> Option<&mut V> {
        let ix = self.calc_index(key);

        let ref mut vals = self.cache[ix];

        if vals.len() > 0 {
            for kv in vals {
                if kv.0 == key {
                    return Some(&mut kv.1);
                }
            }

            return None;
        } else {
            return None;
        }
    }

    pub fn remove(&mut self, key: ID) -> Option<V> {
        let ix = self.calc_index(key);

        let ref mut vals = self.cache[ix];

        if vals.len() > 0 {
            for i in 0..vals.len() {
                let peek = vals[i].0;

                if peek == key {
                    self.count -= 1;
                    let kv = vals.swap_remove(i);
                    return Some(kv.1);
                }
            }

            return None;
        } else {
            return None;
        }
    }

    pub fn contains_key(&self, key: ID) -> bool {
        match self.get(key) {
            Some(_) => true,
            None => false,
        }
    }

    pub fn clear(&mut self) {
        for i in 0..self.cache.len() {
            self.cache[i].clear();
        }

        self.count = 0;
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(ID, &V) -> bool,
    {
        let mut removed = 0;
        for i in 0..self.cache.len() {
            self.cache[i].retain(|Value(k, v)| {
                let keep = (f)(*k, v);
                if !keep {
                    removed += 1;
                }
                keep
            });
        }

        self.count -= removed;
    }

    pub fn is_empty(&mut self) -> bool {
        self.count == 0
    }

    #[inline]
    fn hash_u64(seed: u64) -> u64 {
        let a = 11400714819323198549u64;
        let val = a.wrapping_mul(seed);
        val
    }

    #[inline]
    fn calc_index(&self, key: ID) -> usize {
        let hash = Self::hash_u64(key.0);
        // Faster modulus
        (hash & self.mod_mask) as usize
    }

    #[inline]
    fn lim(&self) -> usize {
        2u64.pow(self.size) as usize
    }

    fn increase_cache(&mut self) {
        self.size += 1;
        let new_lim = self.lim();
        self.mod_mask = (new_lim as u64) - 1;

        let mut vec: Vec<Vec<Value<V>>> = Vec::new();

        vec.append(&mut self.cache);

        for _ in 0..new_lim {
            self.cache.push(Vec::with_capacity(0));
        }

        while vec.len() > 0 {
            let mut values = vec.pop().unwrap();
            while values.len() > 0 {
                if let Some(k) = values.pop() {
                    let ix = self.calc_index(k.0);

                    let ref mut vals = self.cache[ix];
                    vals.push(k);
                }
            }
        }

        debug_assert!(
            self.cache.len() == self.lim(),
            "cache vector the wrong length, lim: {:?} cache: {:?}",
            self.lim(),
            self.cache.len()
        );
    }

    fn ensure_load_rate(&mut self) {
        while ((self.count * 100) / self.cache.len()) > 70 {
            self.increase_cache();
        }
    }

    pub fn len(&self) -> usize {
        self.count as usize
    }

    pub fn load(&self) -> u64 {
        let mut count = 0;

        for i in 0..self.cache.len() {
            if self.cache[i].len() > 0 {
                count += 1;
            }
        }

        count
    }

    pub fn load_rate(&self) -> f64 {
        (self.count as f64) / (self.cache.len() as f64) * 100f64
    }

    pub fn capacity(&self) -> usize {
        self.cache.len()
    }

    pub fn assert_count(&self) -> bool {
        let mut count = 0;

        for i in 0..self.cache.len() {
            for _ in self.cache[i].iter() {
                count += 1;
            }
        }

        self.count == count
    }

    pub fn collisions(&self) -> Map<u64> {
        let mut map = Map::new();

        for s in self.cache.iter() {
            let key = ID(s.len() as u64);
            if key.0 > 1 {
                if !map.contains_key(key) {
                    map.insert(key, 1);
                } else {
                    let counter = map.get_mut(key).unwrap();
                    *counter += 1;
                }
            }
        }

        map
    }

    pub fn keys<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.cache.iter().map(|c| c.iter()).flatten().map(|kv| kv.0)
    }

    pub fn values<'a>(&'a self) -> impl Iterator<Item = &'a V> + 'a {
        self.cache
            .iter()
            .map(|c| c.iter())
            .flatten()
            .map(|kv| &kv.1)
    }

    pub fn values_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut V> + 'a {
        self.cache
            .iter_mut()
            .map(|c| c.iter_mut())
            .flatten()
            .map(|kv| &mut kv.1)
    }
}

impl<V> Default for Map<V> {
    fn default() -> Self {
        Map::new()
    }
}

#[derive(Clone, Debug, QuickSer)]
pub struct Table<I: EntityRef, T> {
    map: Map<I>,
    data: PrimaryMap<I, Value<T>>,
}

impl<I: EntityRef, T> Table<I, T> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            data: PrimaryMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.data.clear();
    }

    pub fn add_hidden(&mut self, value: T) -> I {
        self.data.push(Value(ID(0), value))
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        if let Some(&i) = self.map.get(id) {
            if id == self.data[i].0 {
                return (Some(std::mem::replace(&mut self.data[i].1, data)), i);
            }
        }
        let i = self.data.push(Value(id, data));
        self.map.insert(id, i);
        (None, i)
    }

    pub fn index_or_insert(&mut self, id: ID, data: T) -> I {
        if let Some(&i) = self.map.get(id) {
            if id == self.data[i].0 {
                return i;
            }
        }
        let i = self.data.push(Value(id, data));
        self.map.insert(id, i);
        i
    }

    pub fn index(&self, id: ID) -> Option<&I> {
        self.map.get(id)
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.data.iter().map(|v| &v.1 .1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut().map(|v| &mut v.1 .1)
    }

    pub fn link(&mut self, id: ID, index: I) -> Option<I> {
        self.map.insert(id, index)
    }

    pub fn remove_link(&mut self, id: ID, shadowed: Option<I>) -> Option<I> {
        if let Some(shadowed) = shadowed {
            self.map.insert(id, shadowed)
        } else {
            self.map.remove(id)
        }
    }

    pub fn keys<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.map.keys()
    }

    pub fn get_mut_or_else<F: FnOnce() -> T>(&mut self, id: ID, data: F) -> &mut T {
        let i = self
            .map
            .get(id)
            .cloned()
            .unwrap_or_else(|| self.insert(id, data()).1);
        &mut self.data[i].1
    }

    pub fn get(&self, id: ID) -> Option<&T> {
        self.map.get(id).map(|&i| &self.data[i].1)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<I: EntityRef, T> Index<I> for Table<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, id: I) -> &Self::Output {
        &self.data[id].1
    }
}

impl<I: EntityRef, T> IndexMut<I> for Table<I, T> {
    #[inline]
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id].1
    }
}

impl<I: EntityRef, T> Index<ID> for Table<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &self.data[i].1
    }
}

impl<I: EntityRef, T> IndexMut<ID> for Table<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &mut self.data[i].1
    }
}

impl<I: EntityRef, T> Default for Table<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(QuickSer)]
pub struct LinkedList<I: EntityRef, T> {
    data: Vec<LinkedNode<I, T>>,
    free: Vec<I>,
}

#[derive(QuickSer, Clone)]
pub struct LinkedNode<I: EntityRef, T> {
    prev: I, 
    next: I,
    value: T, 
}

impl<I: EntityRef, T> From<(I, I, T)> for LinkedNode<I, T> {
    fn from((prev, next, value): (I, I, T)) -> Self {
        Self { prev, next, value }
    }
}

impl<I: EntityRef + std::fmt::Debug, T: Default> LinkedList<I, T> {
    pub fn new() -> Self {
        Self {
            data: vec![(I::new(0), I::new(0), T::default()).into()],
            free: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.data.len() - self.free.len() - 1
    }

    pub fn push(&mut self, data: T) -> I {
        let last = self.data[0].prev;

        let id = self.allocate(last, data, I::new(0));

        self.data[id.index()].prev = last;
        self.data[0].prev = id;
        self.data[last.index()].next = id;
        id
    }

    pub fn insert(&mut self, id: I, data: T) -> I {
        let previous = id;
        let after = self.data[previous.index()].next;

        let id = self.allocate(previous, data, after);

        self.data[previous.index()].next = id;
        self.data[after.index()].prev = id;

        id
    }

    pub fn insert_before(&mut self, id: I, data: T) -> I {
        let previous = self.data[id.index()].prev;
        let after = id;

        let id = self.allocate(previous, data, after);

        self.data[previous.index()].next = id;
        self.data[after.index()].prev = id;

        id
    }

    pub fn add_hidden(&mut self, data: T) -> I {
        self.allocate(I::new(0), data, I::new(0))
    }

    pub fn hide(&mut self, id: I) {
        let previous = self.data[id.index()].prev;
        let after = self.data[id.index()].next;

        self.data[previous.index()].next = after;
        self.data[after.index()].prev = previous;

        self.data[id.index()].prev = I::new(0);
        self.data[id.index()].next = I::new(0);
    }

    pub fn show_as_last(&mut self, id: I) {
        let last = self.data[0].prev;
        self.show(id, last);
    }

    pub fn show(&mut self, id: I, at: I) {
        debug_assert!(
            self.data[id.index()].prev == I::new(0) && self.data[id.index()].next == I::new(0),
            "element is already visible",
        );

        let previous = at;
        let after = self.data[at.index()].next;

        self.data[previous.index()].next = id;
        self.data[after.index()].prev = id;

        self.data[id.index()].prev = previous;
        self.data[id.index()].next = after;
    }

    pub fn last(&self) -> Option<I> {
        self.previous(I::new(0))
    }

    pub fn first(&self) -> Option<I> {
        self.next(I::new(0))
    }

    pub fn remove(&mut self, id: I) -> T {
        let previous = self.data[id.index()].prev;
        let after = self.data[id.index()].next;

        self.data[previous.index()].next = after;
        self.data[after.index()].prev = previous;

        self.free.push(id);

        std::mem::take(&mut self.data[id.index()].value)
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
        self.data[0].prev = I::new(0);
        self.data[0].next = I::new(0);
    }

    pub fn next(&self, id: I) -> Option<I> {
        let id = self.data[id.index()].next;
        if id == I::new(0) {
            None
        } else {
            Some(id)
        }
    }

    pub fn previous(&self, id: I) -> Option<I> {
        let id = self.data[id.index()].prev;
        if id == I::new(0) {
            None
        } else {
            Some(id)
        }
    }

    fn allocate(&mut self, previous: I, data: T, after: I) -> I {
        if let Some(id) = self.free.pop() {
            self.data[id.index()] = (previous, after, data).into();
            id
        } else {
            self.data.push((previous, after, data).into());
            I::new(self.data.len() - 1)
        }
    }
}

impl<I: EntityRef + std::fmt::Debug, T: std::fmt::Debug + Default> std::fmt::Debug
    for LinkedList<I, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter().map(|a| a.1)).finish()
    }
}

impl<I: EntityRef, T> Index<I> for LinkedList<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.data[index.index()].value
    }
}

impl<I: EntityRef, T> IndexMut<I> for LinkedList<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.data[index.index()].value
    }
}

impl<I: EntityRef + std::fmt::Debug, T: Default> Default for LinkedList<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: EntityRef, T: Clone> Clone for LinkedList<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            free: self.free.clone(),
        }
    }
}

macro_rules! impl_linked_iter {
    ($name:ident $($modifier:tt)*) => {
        pub struct $name<'a, I: EntityRef, T: 'a> {
            list: &'a $($modifier)* LinkedList<I, T>,
            current: Option<I>,
        }

        impl <'a, I: EntityRef, T: 'a> $name<'a, I, T> {
            pub fn new(list: &'a $($modifier)* LinkedList<I, T>) -> Self {
                Self {
                    current: Some(I::new(0)),
                    list,
                }
            }
        }



        impl <'a, I: EntityRef, T: 'a> Iterator for $name<'a, I, T> {
            type Item = (I, &'a $($modifier)* T);

            fn next(&mut self) -> Option<Self::Item> {
                self.current.map(|id| {
                    let next =  self.list.data[id.index()].next;
                    let (_, data, _) = unsafe {
                        std::mem::transmute::<_, & $($modifier)* (I, T, I)>(
                            & $($modifier)* self.list.data[next.index()]
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