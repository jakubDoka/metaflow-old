use std::{
    fmt::Debug,
    ops::{Deref, Range},
    rc::Rc,
};

#[derive(Clone, PartialEq)]
pub struct Spam {
    rc: Option<Rc<String>>,
    range: Range<usize>,
    string: *const str,
}

impl Spam {
    pub fn new(rc: &Rc<String>, range: Range<usize>) -> Self {
        Self {
            rc: Some(rc.clone()),
            string: &rc[range.clone()] as *const str,
            range,
        }
    }

    pub fn whole(rc: &Rc<String>) -> Self {
        Self {
            rc: Some(rc.clone()),
            range: 0..rc.len(),
            string: &rc[..] as *const str,
        }
    }

    pub fn infinite(str: &'static str) -> Self {
        Self {
            rc: None,
            range: 0..0,
            string: str,
        }
    }

    pub fn empty() -> Self {
        Self {
            rc: None,
            range: 0..0,
            string: "" as *const str,
        }
    }

    pub fn sub(&self, range: Range<usize>) -> Self {
        let new_range = self.range.start + range.start..self.range.start + range.end;
        Self {
            rc: self.rc.clone(),
            string: &self[range.clone()] as *const str,
            range: new_range,
        }
    }

    pub fn get_range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub unsafe fn get_static_ref(&self) -> &'static str {
        &*self.string as &'static str
    }
}

impl Default for Spam {
    fn default() -> Self {
        Self::empty()
    }
}

impl Debug for Spam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl Deref for Spam {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        //SAFETY: instance holds ref-count to string
        unsafe { &*self.string }
    }
}
