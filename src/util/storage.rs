use std::ops::{Index, IndexMut};

use cranelift::{
    codegen::entity::{EntityRef, PrimaryMap},
    entity::SecondaryMap,
};
use quick_proc::QuickSer;

use super::sdbm::ID;

#[derive(Clone, Debug, QuickSer)]
pub struct Map<V> {
    indices: Vec<(u32, u32, u32)>,
    ids: Vec<ID>,
    cache: Vec<V>,
    size: u32,
    mod_mask: u64,
    count: usize,
}

impl<V: Default> Default for Map<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Default> Map<V> {
    pub fn new() -> Self {
        Map::with_capacity(4)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut map = Self {
            indices: Vec::new(),
            ids: Vec::new(),
            cache: Vec::new(),
            size: 0,
            mod_mask: 0,
            count: 0,
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

        let slice = self.indices[ix];
        for i in slice.0..slice.1 {
            if self.ids[i as usize] == key {
                return Some(std::mem::replace(&mut self.cache[i as usize], value));
            }
        }

        self.count += 1;

        if slice.1 != slice.2 {
            // there is spare space
            self.indices[ix] = (slice.0, slice.1 + 1, slice.2);
            self.ids[slice.1 as usize] = key;
            self.cache[slice.1 as usize] = value;
            return None;
        } else {
            // reallocate the elements
            let start = self.cache.len() as u32;
            for i in slice.0..slice.1 {
                let id = self.ids[i as usize];
                let elem = std::mem::take(&mut self.cache[i as usize]);
                self.ids.push(id);
                self.cache.push(elem);
            }
            self.ids.push(key);
            self.cache.push(value);
            self.indices[ix] = (start, self.cache.len() as u32, self.cache.len() as u32);
        }

        if self.count > self.indices.len() {
            self.increase_cache();
        }

        None
    }

    pub fn get(&self, key: ID) -> Option<&V> {
        let ix = self.calc_index(key);

        let slice = self.indices[ix];

        for i in slice.0..slice.1 {
            if self.ids[i as usize] == key {
                return Some(&self.cache[i as usize]);
            }
        }

        return None;
    }

    pub fn get_mut(&mut self, key: ID) -> Option<&mut V> {
        let ix = self.calc_index(key);

        let slice = self.indices[ix];

        for i in slice.0..slice.1 {
            if self.ids[i as usize] == key {
                return Some(&mut self.cache[i as usize]);
            }
        }

        return None;
    }

    pub fn remove(&mut self, key: ID) -> Option<V> {
        let ix = self.calc_index(key);

        let slice = self.indices[ix];

        for i in slice.0..slice.1 {
            let elem = &mut self.cache[i as usize];

            if self.ids[i as usize] == key {
                self.count -= 1;
                let elem = std::mem::take(elem);
                self.ids.swap(i as usize, slice.1 as usize - 1);
                self.cache.swap(i as usize, slice.1 as usize - 1);
                self.indices[ix] = (slice.0, slice.1 - 1, slice.2);
                return Some(elem);
            }
        }

        return None;
    }

    pub fn contains_key(&self, key: ID) -> bool {
        match self.get(key) {
            Some(_) => true,
            None => false,
        }
    }

    pub fn clear(&mut self) {
        for i in self.indices.iter_mut() {
            *i = (0, 0, 0);
        }

        self.ids.clear();
        self.cache.clear();

        self.count = 0;
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

        let indices = std::mem::take(&mut self.indices);
        let ids = std::mem::replace(&mut self.ids, Vec::with_capacity(new_lim));
        let mut cache = std::mem::replace(&mut self.cache, Vec::with_capacity(new_lim));
        self.indices.resize(new_lim, (0, 0, 0));

        for slice in indices {
            for j in slice.0..slice.1 {
                let id = ids[j as usize];
                let elem = std::mem::take(&mut cache[j as usize]);
                let new_idx = self.calc_index(id);
                let slice = self.indices[new_idx];
                let start = self.cache.len();
                for k in slice.0..slice.1 {
                    let id = self.ids[k as usize];
                    let elem = std::mem::take(&mut self.cache[k as usize]);
                    self.ids.push(id);
                    self.cache.push(elem);
                }
                self.ids.push(id);
                self.cache.push(elem);
                self.indices[new_idx] = (
                    start as u32,
                    self.cache.len() as u32,
                    self.cache.len() as u32,
                );
            }
        }
    }

    pub fn len(&self) -> usize {
        self.count as usize
    }

    pub fn load(&self) -> usize {
        self.indices.iter().map(|s| s.1 - s.0).sum::<u32>() as usize
    }

    pub fn load_rate(&self) -> f64 {
        (self.count as f64) / (self.cache.len() as f64) * 100f64
    }

    pub fn capacity(&self) -> usize {
        self.cache.len()
    }

    pub fn assert_count(&self) -> bool {
        self.count == self.load()
    }

    pub fn keys<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.indices
            .iter()
            .map(move |c| self.ids[c.0 as usize..c.1 as usize].iter())
            .flatten()
            .map(|kv| *kv)
    }

    pub fn values<'a>(&'a self) -> impl Iterator<Item = &'a V> + 'a {
        self.indices
            .iter()
            .map(move |c| self.cache[c.0 as usize..c.1 as usize].iter())
            .flatten()
            .map(|kv| kv)
    }

    pub fn values_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut V> + 'a {
        MapValueMutIterator {
            map: self,
            index: 0,
            sub_index: 0,
        }
    }
}

pub struct MapValueMutIterator<'a, V> {
    map: &'a mut Map<V>,
    index: usize,
    sub_index: usize,
}

impl<'a, V: Default> Iterator for MapValueMutIterator<'a, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.map.indices.len() {
            return None;
        }

        let slice = self.map.indices[self.index];

        if self.sub_index >= slice.1 as usize {
            self.index += 1;

            if self.index >= self.map.indices.len() {
                return None;
            }

            self.sub_index = 0;
        }

        let elem = unsafe {
            std::mem::transmute::<&mut _, &'a mut V>(
                &mut self.map.cache[slice.0 as usize + self.sub_index],
            )
        };
        self.sub_index += 1;

        Some(elem)
    }
}

#[derive(Clone, Debug, QuickSer)]
pub struct Table<I: EntityRef, T> {
    map: Map<I>,
    ids: SecondaryMap<I, ID>,
    data: PrimaryMap<I, T>,
    free: Vec<I>,
}

impl<I: EntityRef + Default, T> Table<I, T> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            ids: SecondaryMap::new(),
            data: PrimaryMap::new(),
            free: Vec::new(),
        }
    }

    pub fn next_key(&self) -> I {
        self.data.next_key()
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.data.clear();
        self.free.clear();
    }

    pub fn add_hidden(&mut self, value: T) -> I {
        self.data.push(value)
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        if let Some(&i) = self.map.get(id) {
            if id == self.ids[i] {
                return (Some(std::mem::replace(&mut self.data[i], data)), i);
            }
        }
        let i = if let Some(free) = self.free.pop() {
            self.data[free] = data;
            free
        } else {
            self.data.push(data)
        };
        self.ids[i] = id;
        self.map.insert(id, i);
        (None, i)
    }

    pub fn index_or_insert(&mut self, id: ID, data: T) -> I {
        if let Some(&i) = self.map.get(id) {
            if id == self.ids[i] {
                return i;
            }
        }
        let i = if let Some(free) = self.free.pop() {
            self.data[free] = data;
            free
        } else {
            self.data.push(data)
        };
        self.ids[i] = id;
        self.map.insert(id, i);
        i
    }

    pub fn index(&self, id: ID) -> Option<&I> {
        self.map.get(id)
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.data.iter().map(|v| v.1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut().map(|v| v.1)
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
        &mut self.data[i]
    }

    pub fn get(&self, id: ID) -> Option<&T> {
        self.map.get(id).map(|&i| &self.data[i])
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<I: EntityRef + Default, T: Default> Table<I, T> {
    pub fn remove(&mut self, id: ID) -> Option<T> {
        if let Some(&i) = self.map.get(id) {
            let value = std::mem::take(&mut self.data[i]);
            self.map.remove(id);
            self.free.push(i);
            Some(value)
        } else {
            None
        }
    }
}

impl<I: EntityRef, T> Index<I> for Table<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, id: I) -> &Self::Output {
        &self.data[id]
    }
}

impl<I: EntityRef, T> IndexMut<I> for Table<I, T> {
    #[inline]
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id]
    }
}

impl<I: EntityRef + Default, T> Index<ID> for Table<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &self.data[i]
    }
}

impl<I: EntityRef + Default, T> IndexMut<ID> for Table<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &mut self.data[i]
    }
}

impl<I: EntityRef + Default, T> Default for Table<I, T> {
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

pub fn test() {
    let mut map = Map::<usize>::new();

    let count = 1000;

    for _ in 0..100 {
        for i in 0..count {
            map.insert(ID((i * i) as u64), i);
        }

        for i in 0..count {
            assert_eq!(map.get(ID((i * i) as u64)), Some(&i));
        }

        for i in 0..count {
            assert_eq!(map.remove(ID((i * i) as u64)), Some(i));
        }

        for i in 0..count {
            map.insert(ID((i * i) as u64), i);
        }

        map.clear();
    }
}
