use std::{
    cell::RefCell,
    ops::{Deref, DerefMut},
    rc::Rc,
};

#[cfg(debug_assertions)]
static mut DEBUG_CELL_COUNT: usize = 0;

#[cfg(debug_assertions)]
pub fn report_cell_state() -> usize {
    unsafe { DEBUG_CELL_COUNT }
}

// basically a Rc that allows mutating the inner value
pub struct Cell<T> {
    inner: *mut (T, usize, Option<Pool<T>>),
}

impl<T> Cell<T> {
    pub fn new(inner: T) -> Self {
        Self::with_pool(inner, None)
    }

    fn with_pool(inner: T, pool: Option<Pool<T>>) -> Self {
        #[cfg(debug_assertions)]
        unsafe {
            DEBUG_CELL_COUNT += 1;
        }

        Self {
            inner: Box::into_raw(Box::new((inner, 1, pool))),
        }
    }

    fn load_pool(&mut self, inner: T, pool: Pool<T>) {
        unsafe {
            *self.inner = (inner, 1, Some(pool));
        }
    }
}

impl<T: PartialEq> PartialEq for Cell<T> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            if self.inner == other.inner {
                return true;
            }
            let (a, ..) = &*self.inner;
            let (b, ..) = &*other.inner;
            *a == *b
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Cell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", unsafe { &(*self.inner).0 })
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
                if let Some(mut pool) = (*self.inner).2.take() {
                    pool.push(self.clone());
                } else {
                    Box::from_raw(self.inner);
                    #[cfg(debug_assertions)]
                    {
                        DEBUG_CELL_COUNT -= 1;
                    }
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

pub struct Pool<T> {
    cells: Rc<RefCell<Vec<Cell<T>>>>,
}

impl<T> Pool<T> {
    pub fn new() -> Self {
        Self {
            cells: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn wrap(&mut self, value: T) -> Cell<T> {
        match self.cells.borrow_mut().pop() {
            Some(mut cell) => {
                cell.load_pool(value, self.clone());

                cell
            }
            None => Cell::with_pool(value, Some(self.clone())),
        }
    }

    fn push(&mut self, cell: Cell<T>) {
        self.cells.borrow_mut().push(cell);
    }
}

impl<T> Clone for Pool<T> {
    fn clone(&self) -> Self {
        Self {
            cells: self.cells.clone(),
        }
    }
}
