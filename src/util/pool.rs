use std::ops::{Deref, DerefMut};

/// Pool offers a simple way to reuse allocations. All you need to do is get() and
/// you will get a Vec that may have some capacity for free. Vec is wrapped in type that
/// returns it to the pool when it is dropped. If you attempt to drop pool sooner then
/// all borrowed Vectors, pool will panic, but only on debug build.
#[derive(Debug, Clone)]
pub struct Pool {
    inner: Box<PoolObj>,
}

impl Pool {
    pub fn new() -> Pool {
        Pool {
            inner: Box::new(PoolObj::new()),
        }
    }
}

impl Deref for Pool {
    type Target = PoolObj;

    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl DerefMut for Pool {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.inner
    }
}

impl Default for Pool {
    fn default() -> Self {
        Pool::new()
    }
}

#[derive(Debug, Clone)]
pub struct PoolObj {
    elements: Vec<Vec<(*mut u8, usize, usize)>>,
    #[cfg(debug_assertions)]
    ref_count: u64,
}

impl PoolObj {
    pub fn new() -> PoolObj {
        PoolObj {
            elements: vec![Vec::new(); 8],
            #[cfg(debug_assertions)]
            ref_count: 0,
        }
    }

    pub fn recycle<T>(&mut self, target: Vec<T>) {
        let (ptr, len, cap) = target.into_raw_parts();
        let cap = cap * std::mem::size_of::<T>();
        let len = len * std::mem::size_of::<T>();
        let ptr = unsafe { std::mem::transmute::<*mut T, *mut u8>(ptr) };
        self.elements[std::mem::align_of::<T>() - 1].push((ptr, len, cap));
    }

    pub fn get<T>(&mut self) -> PoolRef<T> {
        let vec = if let Some((ptr, len, cap)) = self.elements[std::mem::align_of::<T>() - 1].pop()
        {
            let cap = cap / std::mem::size_of::<T>();
            let len = len / std::mem::size_of::<T>();
            unsafe {
                let ptr = std::mem::transmute::<*mut u8, *mut T>(ptr);
                Vec::from_raw_parts(ptr, len, cap)
            }
        } else {
            Vec::new()
        };
        #[cfg(debug_assertions)]
        {
            self.ref_count += 1;
        }
        PoolRef {
            origin: self as *mut _,
            value: vec,
        }
    }
}

impl Default for PoolObj {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(debug_assertions)]
impl Drop for PoolObj {
    fn drop(&mut self) {
        assert_eq!(self.ref_count, 0);
    }
}

#[derive(Debug)]
pub struct PoolRef<T> {
    origin: *mut PoolObj,
    value: Vec<T>,
}

impl<T> Deref for PoolRef<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for PoolRef<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> Drop for PoolRef<T> {
    fn drop(&mut self) {
        let pool = unsafe { &mut *self.origin };

        #[cfg(debug_assertions)]
        {
            pool.ref_count -= 1;
        }

        self.value.clear();
        pool.recycle(std::mem::take(&mut self.value));
    }
}

pub fn test() {
    let mut pool = Pool::new();

    {
        let mut store = pool.get::<i32>();
        store.push(1);
        store.push(2);
        let mut store = pool.get::<i128>();
        store.push(3);
        store.push(4);
    }

    {
        let store = pool.get::<i32>();
        assert!(store.capacity() >= 2);
        let store = pool.get::<i128>();
        assert!(store.capacity() >= 2);
    }

    {
        uh_oh(&mut pool);
    }
}

pub fn uh_oh(pool: &mut Pool) -> PoolRef<i32> {
    let mut store = pool.get::<i32>();
    store.push(3);
    store.push(4);
    store
}
