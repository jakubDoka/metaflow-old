use std::{
    ops::{Deref, DerefMut},
};

pub struct Cell<T> {
    inner: *mut T,
}

impl<T> Cell<T> {
    pub fn new(inner: T) -> Self {
        Self {
            inner: Box::into_raw(Box::new(inner)),
        }
    }

    fn drop(self) {
        unsafe {
            drop(Box::from_raw(self.inner));
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
            Self { inner: self.inner }
        }
    }
}

impl<T> DerefMut for Cell<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.inner }
    }
}

impl<T> Deref for Cell<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.inner }
    }
}
