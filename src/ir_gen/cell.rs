use std::ops::{Deref, DerefMut};

#[cfg(debug_assertions)]
static mut DEBUG_CELL_COUNT: usize = 0;

#[cfg(debug_assertions)]
pub fn report_cell_state() -> usize {
    unsafe { DEBUG_CELL_COUNT }
}

// basically a Rc that allows mutating the inner value
pub struct Cell<T> {
    inner: *mut (T, usize),
}

impl<T> Cell<T> {
    pub fn new(inner: T) -> Self {
        #[cfg(debug_assertions)]
        unsafe {
            DEBUG_CELL_COUNT += 1;
        }

        Self {
            inner: Box::into_raw(Box::new((inner, 1))),
        }
    }
}

impl<T: PartialEq> PartialEq for Cell<T> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            if self.inner == other.inner {
                return true;
            }
            let (a, _a_count) = &*self.inner;
            let (b, _b_count) = &*other.inner;
            *a == *b
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Cell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", unsafe { &*self.inner })
    }
}

impl<T> Clone for Cell<T> {
    fn clone(&self) -> Self {
        unsafe {
            (*self.inner).1 += 1;
            Self { inner: self.inner }
        }
    }
}

impl<T> Drop for Cell<T> {
    fn drop(&mut self) {
        unsafe {
            (*self.inner).1 -= 1;
            if (*self.inner).1 == 0 {
                Box::from_raw(self.inner);
                #[cfg(debug_assertions)]
                {
                    DEBUG_CELL_COUNT -= 1;
                }
            }
        }
    }
}

impl<T> DerefMut for Cell<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut (*self.inner).0 }
    }
}

impl<T> Deref for Cell<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.inner).0 }
    }
}