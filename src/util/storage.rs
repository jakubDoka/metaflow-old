use std::{
    marker::PhantomData,
    ops::{Index, IndexMut}, sync::{atomic::{AtomicUsize, Ordering}, Arc},
};

use super::sdbm::ID;

#[derive(Clone, Debug)]
pub struct Map<V> {
    cache: Vec<Vec<(ID, V)>>,
    size: u32,
    mod_mask: u64,
    count: usize,
}

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
            vals.push((key, value));
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
            self.cache[i].retain(|(k, v)| {
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

        let mut vec: Vec<Vec<(ID, V)>> = Vec::new();

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

pub struct SyncTable<I: IndexPointer, T> {
    pub map: Map<I>,
    pub data: SyncList<I, T>,
}

impl<I: IndexPointer, T> SyncTable<I, T> {
    pub fn new(cursor: Cursor, offset: usize) -> Self {
        Self {
            map: Map::new(),
            data: SyncList::new(cursor, offset),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.data.clear();
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        if let Some(&i) = self.map.get(id) {
            (Some(std::mem::replace(&mut self.data[i], data)), i)
        } else {
            let i = self.data.add(data);
            self.map.insert(id, i);
            (None, i)
        }
    }

    #[inline]
    pub fn index(&self, id: ID) -> Option<&I> {
        self.map.get(id)
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.data.iter().map(|v| v.1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut().map(|v| v.1)
    }

    pub unsafe fn direct_ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(|i| I::new(i))
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

    pub fn get(&self, id: ID) -> Option<&T> {
        self.map.get(id).map(|&i| &self.data[i])
    }

    pub fn get_mut_or_else<F: FnOnce() -> T>(&mut self, id: ID, data: F) -> &mut T {
        let i = self
            .map
            .get(id)
            .cloned()
            .unwrap_or_else(|| self.insert(id, data()).1);
        &mut self.data[i]
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<I: IndexPointer, T> Index<I> for SyncTable<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, id: I) -> &Self::Output {
        &self.data[id]
    }
}

impl<I: IndexPointer, T> IndexMut<I> for SyncTable<I, T> {
    #[inline]
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id]
    }
}

impl<I: IndexPointer, T> Index<ID> for SyncTable<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &self.data[i]
    }
}

impl<I: IndexPointer, T> IndexMut<ID> for SyncTable<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &mut self.data[i]
    }
}

impl<I: IndexPointer, T> Default for SyncTable<I, T> {
    fn default() -> Self {
        Self::new(Cursor::new(), 0)
    }
}

impl<I: IndexPointer, T: Clone> Clone for SyncTable<I, T> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            data: self.data.clone(),
        }
    }
}

impl<I: IndexPointer, T: std::fmt::Debug> std::fmt::Debug for SyncTable<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f
            .debug_list()
            .entries(self.map.keys().map(|k| {
                format!("{:?}: {:?}", k, &self[k])
            })).finish()
    }
}


#[derive(Clone, Debug)]
pub struct Table<I: IndexPointer, T> {
    map: Map<I>,
    data: List<I, T>,
}

impl<I: IndexPointer, T> Table<I, T> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            data: List::new(),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.data.clear();
    }

    pub fn insert(&mut self, id: ID, data: T) -> (Option<T>, I) {
        if let Some(&i) = self.map.get(id) {
            (Some(std::mem::replace(&mut self.data[i], data)), i)
        } else {
            let i = self.data.add(data);
            self.map.insert(id, i);
            (None, i)
        }
    }

    #[inline]
    pub fn index(&self, id: ID) -> Option<&I> {
        self.map.get(id)
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.data.iter().map(|v| v.1)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut().map(|v| v.1)
    }

    pub unsafe fn direct_ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(|i| I::new(i))
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

impl<I: IndexPointer, T> Index<I> for Table<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, id: I) -> &Self::Output {
        &self.data[id]
    }
}

impl<I: IndexPointer, T> IndexMut<I> for Table<I, T> {
    #[inline]
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id]
    }
}

impl<I: IndexPointer, T> Index<ID> for Table<I, T> {
    type Output = T;

    fn index(&self, id: ID) -> &Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &self.data[i]
    }
}

impl<I: IndexPointer, T> IndexMut<ID> for Table<I, T> {
    fn index_mut(&mut self, id: ID) -> &mut Self::Output {
        let i = *self.map.get(id).expect("invalid ID");
        &mut self.data[i]
    }
}

impl<I: IndexPointer, T> Default for Table<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct LinkedList<I: IndexPointer, T> {
    data: Vec<(I, T, I)>,
    free: Vec<I>,
}

impl<I: IndexPointer, T> LinkedList<I, T> {
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

impl<I: IndexPointer, T: std::fmt::Debug> std::fmt::Debug for LinkedList<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter().map(|a| a.1)).finish()
    }
}

impl<I: IndexPointer, T> Index<I> for LinkedList<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.data[index.raw()].1
    }
}

impl<I: IndexPointer, T> IndexMut<I> for LinkedList<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.data[index.raw()].1
    }
}

impl<I: IndexPointer, T> Default for LinkedList<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: IndexPointer, T: Clone> Clone for LinkedList<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            free: self.free.clone(),
        }
    }
}

macro_rules! impl_linked_iter {
    ($name:ident $($modifier:tt)*) => {
        pub struct $name<'a, I: IndexPointer, T: 'a> {
            list: &'a $($modifier)* LinkedList<I, T>,
            current: Option<I>,
        }

        impl <'a, I: IndexPointer, T: 'a> $name<'a, I, T> {
            pub fn new(list: &'a $($modifier)* LinkedList<I, T>) -> Self {
                Self {
                    current: Some(I::new(0)),
                    list,
                }
            }
        }



        impl <'a, I: IndexPointer, T: 'a> Iterator for $name<'a, I, T> {
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
pub struct LockedList<I: IndexPointer, T> {
    inner: List<I, T>,
}

impl<I: IndexPointer, T> LockedList<I, T> {
    pub fn new(inner: List<I, T>) -> Self {
        Self { inner }
    }

    // SAFETY: ensure that LockedList does not get dropped
    // while reference still lives
    pub unsafe fn get<'a>(&self, id: I) -> &'a T {
        std::mem::transmute::<_, &T>(&self.inner[id])
    }
}

impl<I: IndexPointer, T> Default for LockedList<I, T> {
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}

impl<I: IndexPointer, T> Index<I> for LockedList<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.inner[id]
    }
}

impl<I: IndexPointer, T> IndexMut<I> for LockedList<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.inner[id]
    }
}

pub struct SyncList<I: IndexPointer, T> {
    data: Vec<T>,
    used: Vec<usize>,
    cursor: Cursor,
    offset: usize,
    phantom: PhantomData<I>,
}

impl<I: IndexPointer, T> SyncList<I, T> {
    pub fn new(cursor: Cursor, offset: usize) -> Self {
        Self {
            data: vec![],
            used: vec![],
            cursor,
            offset,
            phantom: PhantomData,
        }
    }

    pub fn set_offset(&mut self, offset: usize) {
        self.offset = offset;
    }

    pub fn set_cursor(&mut self, cursor: Cursor) {
        self.cursor = cursor;
    }

    pub fn add(&mut self, data: T) -> I {
        let id = self.cursor.next();
        let len = id + 1;
        self.data.reserve(len);

        unsafe {
            self.data.set_len(len);
        }

        self.data[id] = data;

        I::new(id + self.offset)
    }

    pub fn clear(&mut self) {
        for u in 0..self.used.len() {
            let idx = self.used[u];
            // SAFETY: we are dropping occupied elements so we can set_len later on 
            unsafe {
                drop(std::ptr::read(&mut self.data[idx] as *const T));
            }
        }
        unsafe {
            self.data.set_len(0);
        }
        self.used.clear();
    }

    pub fn merge(target: &mut Vec<T>, with: &mut [Self]) {
        let len = with[0].len();
        
        // should ensure there are no gaps in merged list
        #[cfg(debug_assertions)]
        {
            let range = 0..len;

            assert!(with.iter().all(|l| l.len() == len));

            let mut all: Vec<_> = with.iter().map(|s| s.used.iter().peekable()).collect();

           'o: for i in range {
                for iter in all.iter_mut() {
                    if let Some(&&idx) = iter.peek() {
                        if idx == i {
                            iter.next();
                            continue'o;
                        }
                    }
                }
                panic!("missing index {}", i);
            }
        }

        let target_len = target.len();
        let total_len = target_len + len;

        target.reserve(total_len);
        // SAFETY: reserve ensures the length, but we want uninitialized memory
        unsafe {
            target.set_len(total_len);
        }

        for collection in with {
            for u in 0..collection.used.len() {
                let idx = collection.used[u];
                let data = &collection.data[idx];
                // SAFETY: 
                unsafe {
                    std::ptr::copy(
                        data as *const T, 
                        &mut target[target_len + u] as *mut T, 
                        std::mem::size_of::<T>()
                    )
                }
            }
            
            // SAFETY: we copied all elements to target so they does not need drop
            unsafe {
                collection.data.set_len(0);
            }
            collection.used.clear();
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (I, &T)> {
        self.used.iter().map(move |&idx| (I::new(idx + self.offset), &self.data[idx]))
    }

    pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (I, &'a mut T)> + 'a {
        (0..self.used.len()).map(move |idx| {
            let idx = self.used[idx];
            (
                I::new(idx + self.offset), 
                // SAFETY: while iterator lives the self is mutably borrowed but rust
                // cannot recognize this
                unsafe {
                    std::mem::transmute::<_, &'a mut T>(&mut self.data[idx])
                },
            )
        })
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<I: IndexPointer, T> Index<I> for SyncList<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        debug_assert!(self.used.iter().any(|&i| i == index.raw()));
        &self.data[index.raw() - self.offset]
    }
}

impl<I: IndexPointer, T> IndexMut<I> for SyncList<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        debug_assert!(self.used.iter().any(|&i| i == index.raw()));
        &mut self.data[index.raw() - self.offset]
    }
}

impl<I: IndexPointer, T: Clone> Clone for SyncList<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            used: self.used.clone(),
            cursor: self.cursor.clone(),
            offset: self.offset,
            phantom: PhantomData,
        }
    }
}

impl<I: IndexPointer, T> Default for SyncList<I, T> {
    fn default() -> Self {
        Self::new(Cursor::default(), 0)
    }
}

impl<I: IndexPointer, T: std::fmt::Debug> std::fmt::Debug for SyncList<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f
            .debug_list()
            .entries(self.iter().map(|(_, v)| v))
            .finish()
    }
}

#[derive(Debug)]
pub struct List<I: IndexPointer, T> {
    data: Vec<T>,

    p: PhantomData<I>,
}

impl<I: IndexPointer, T> List<I, T> {
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
        self.data
            .iter()
            .enumerate()
            .map(move |(i, d)| (I::new(i), d))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (I, &mut T)> {
        self.data
            .iter_mut()
            .enumerate()
            .map(move |(i, d)| (I::new(i), d))
    }

    pub fn ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(I::new)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<I: IndexPointer, T: Clone> Clone for List<I, T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            p: PhantomData,
        }
    }
}

impl<I: IndexPointer, T> Default for List<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: IndexPointer, T> Index<I> for List<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        &self.data[id.raw()]
    }
}

impl<I: IndexPointer, T> IndexMut<I> for List<I, T> {
    fn index_mut(&mut self, id: I) -> &mut Self::Output {
        &mut self.data[id.raw()]
    }
}

#[derive(Debug, Clone, Default)]
pub struct Cursor {
    counter: Arc<AtomicUsize>,
}

impl Cursor {
    pub fn new() -> Self {
        Self {
            counter: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn next(&self) -> usize {
        self.counter.fetch_add(1, Ordering::Relaxed)
    }

    pub fn set(&self, value: usize) {
        self.counter.store(value, Ordering::Relaxed)
    }
}

#[macro_export]
macro_rules! index_pointer {
    ($id:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $id(usize);

        impl IndexPointer for $id {
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

pub trait IndexPointer: Copy + Clone + PartialEq + Eq {
    fn new(value: usize) -> Self;
    fn raw(&self) -> usize;
}

crate::index_pointer!(Dummy);

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
