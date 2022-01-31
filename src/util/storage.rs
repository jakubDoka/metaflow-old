use std::ops::{Index, IndexMut};

use cranelift::codegen::entity::EntityRef;
use quick_proc::QuickSer;

use super::sdbm::ID;

#[derive(Clone, Debug, QuickSer)]
pub struct Map<V> {
    indices: Vec<u32>,
    cache: Vec<MapEntry<V>>,
}

#[derive(Clone, Debug, Default, QuickSer)]
pub struct MapEntry<V>(ID, Option<V>, u32);

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
            cache: Vec::new(),
        };

        map.reserve(capacity.max(1));

        map
    }

    pub fn reserve(&mut self, capacity: usize) {
        if capacity < self.indices.len() {
            return;
        }
        self.increase_cache(capacity.next_power_of_two());
    }

    pub fn insert(&mut self, key: ID, value: V) -> Option<V> {
        let ix = self.calc_index(key);

        let mut last = self.indices[ix];
        let mut current = last;
        loop {
            if current == u32::MAX {
                let new = self.cache.len();
                let next = new.next_power_of_two();
                if next > self.indices.len() {
                    self.increase_cache(next);
                    return self.insert(key, value);
                }
                self.cache.push(MapEntry(key, Some(value), u32::MAX));
                if last == u32::MAX {
                    self.indices[ix] = new as u32;
                } else {
                    self.cache[last as usize].2 = new as u32;
                }
                break;
            }

            let entry = &mut self.cache[current as usize];
            if entry.1.is_none() {
                entry.0 = key;
                entry.1 = Some(value);
                break;
            }
            if entry.0 == key {
                return std::mem::replace(&mut entry.1, Some(value));
            }

            last = current;
            current = entry.2;
        }

        None
    }

    pub fn get(&self, key: ID) -> Option<&V> {
        let ix = self.calc_index(key);

        let mut current = self.indices[ix];

        while current != u32::MAX {
            let entry = &self.cache[current as usize];

            if entry.1.is_none() {
                break;
            }

            if entry.0 == key {
                return entry.1.as_ref();
            }

            current = entry.2;
        }

        return None;
    }

    pub fn get_mut(&mut self, key: ID) -> Option<&mut V> {
        let ix = self.calc_index(key);

        let mut current = self.indices[ix];

        while current != u32::MAX {
            let entry = &self.cache[current as usize];

            if entry.0 == key || entry.1.is_none() {
                break;
            }

            current = entry.2;
        }

        if current == u32::MAX {
            None
        } else {
            self.cache[current as usize].1.as_mut()
        }
    }

    pub fn remove(&mut self, key: ID) -> Option<V> {
        let ix = self.calc_index(key);

        let mut previous = u32::MAX;
        let mut current = self.indices[ix];
        let mut prev_found = u32::MAX;
        let mut found = u32::MAX;

        while current != u32::MAX {
            let entry = &mut self.cache[current as usize];

            if entry.0 == key {
                entry.0 = ID(0);
                prev_found = previous;
                found = current;
            }

            previous = current;
            current = entry.2;
        }

        if found == u32::MAX {
            return None;
        }

        if prev_found == u32::MAX {
            if self.cache[found as usize].2 != u32::MAX {
                self.indices[ix] = self.cache[found as usize].2;
            }
        } else {
            self.cache[prev_found as usize].2 = self.cache[found as usize].2;
        }

        self.cache[previous as usize].2 = found;
        self.cache[found as usize].2 = u32::MAX;

        std::mem::take(&mut self.cache[found as usize].1)
    }

    pub fn contains_key(&self, key: ID) -> bool {
        self.get(key).is_some()
    }

    pub fn clear(&mut self) {
        for i in self.indices.iter_mut() {
            *i = u32::MAX;
        }

        self.cache.clear();
    }

    #[inline]
    fn hash_u64(seed: u64) -> u64 {
        // don't need it here
        //let a = 11400714819323198549u64;
        //let val = a.wrapping_mul(seed);
        //val
        seed
    }

    #[inline]
    fn calc_index(&self, key: ID) -> usize {
        let hash = Self::hash_u64(key.0);
        // Faster modulus
        (hash & (self.indices.len() as u64 - 1)) as usize
    }

    fn increase_cache(&mut self, size: usize) {
        let indices = std::mem::take(&mut self.indices);
        let mut cache = std::mem::replace(&mut self.cache, Vec::with_capacity(size));
        self.indices.resize(size, u32::MAX);

        for mut index in indices {
            while index != u32::MAX {
                let entry = std::mem::take(&mut cache[index as usize]);
                if entry.1.is_none() {
                    break;
                }
                self.insert(entry.0, entry.1.unwrap());
                index = entry.2;
            }
        }
    }

    pub fn capacity(&self) -> usize {
        self.cache.len()
    }

    pub fn keys<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.cache
            .iter()
            .filter_map(|i| if i.1.is_some() { Some(i.0) } else { None })
    }

    pub fn values<'a>(&'a self) -> impl Iterator<Item = &'a V> + 'a {
        self.cache.iter().filter_map(|i| i.1.as_ref())
    }

    pub fn values_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut V> + 'a {
        self.cache.iter_mut().filter_map(|i| i.1.as_mut())
    }
}

/*#[derive(Clone, Debug, QuickSer)]
pub struct Table<I: EntityRef, T: Default> {
    map: Map<I>,
    ids: SecondaryMap<I, ID>,
    data: PoolMap<I, T>,
}

impl<I: EntityRef + Default, T: Default> Table<I, T> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            ids: SecondaryMap::new(),
            data: PoolMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.data.clear();
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
        let i = self.data.push(data);
        self.ids[i] = id;
        self.map.insert(id, i);
        (None, i)
    }

    pub fn index(&self, id: ID) -> Option<&I> {
        self.map.get(id)
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (I, &'a T)> + 'a {
        self.data.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (I, &mut T)> {
        self.data.iter_mut()
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

    pub fn get_mut(&mut self, id: ID) -> Option<&mut T> {
        if let Some(&id) = self.map.get(id) {
            return Some(&mut self.data[id]);
        }
        None
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_valid(&self, k: I) -> bool {
        self.data.is_valid(k)
    }
}

impl<I: EntityRef + Default, T: Default + TableId> Table<I, T> {
    pub fn remove_by_index(&mut self, index: I) -> T {
        let value = self.data.remove(index);
        self.map.remove(value.id());
        value
    }
}

pub trait TableId {
    fn id(&self) -> ID;
}

impl<I: EntityRef + Default, T: Default> Table<I, T> {
    pub fn remove(&mut self, id: ID) -> Option<T> {
        if let Some(&i) = self.map.get(id) {
            self.map.remove(id);
            Some(self.data.remove(i))
        } else {
            None
        }
    }
}

impl<I: EntityRef, T: Default> Index<I> for Table<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, id: I) -> &Self::Output {
        &self.data[id]
    }
}

impl<I: EntityRef, T: Default> IndexMut<I> for Table<I, T> {
    #[inline]
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id]
    }
}

impl<I: EntityRef + Default, T: Default> Index<ID> for Table<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &self.data[i]
    }
}

impl<I: EntityRef + Default, T: Default> IndexMut<ID> for Table<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &mut self.data[i]
    }
}

impl<I: EntityRef + Default, T: Default> Default for Table<I, T> {
    fn default() -> Self {
        Self::new()
    }
}*/

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
        for i in 1..count {
            map.insert(ID((i * i) as u64), i);
        }

        for i in 1..count {
            assert_eq!(map.get(ID((i * i) as u64)), Some(&i));
        }

        for i in 1..count {
            assert_eq!(map.remove(ID((i * i) as u64)), Some(i));
        }

        for i in 1..count {
            map.insert(ID((i * i) as u64), i);
        }

        for i in 1..count {
            map.insert(ID((i * i) as u64), i);
        }

        map.clear();
    }
}
