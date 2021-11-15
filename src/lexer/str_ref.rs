use std::{
    fmt::Debug,
    ops::{Deref, Range},
    rc::Rc,
};

#[derive(Clone, PartialEq)]
pub struct StrRef {
    rc: Option<Rc<String>>,
    string: *const str,
}

impl StrRef {
    pub fn new(rc: &Rc<String>, range: Range<usize>) -> Self {
        StrRef {
            rc: Some(rc.clone()),
            string: &rc[range] as *const str,
        }
    }

    pub fn whole(rc: &Rc<String>) -> Self {
        StrRef {
            rc: Some(rc.clone()),
            string: &rc[..] as *const str,
        }
    }

    pub fn infinite(str: &'static str) -> Self {
        StrRef {
            rc: None,
            string: str,
        }
    }

    pub fn empty() -> Self {
        StrRef {
            rc: None,
            string: "" as *const str,
        }
    }

    pub fn sub(&self, range: Range<usize>) -> Self {
        StrRef {
            rc: self.rc.clone(),
            string: &self[range] as *const str,
        }
    }

    pub unsafe fn get_static_ref(&self) -> &'static str {
        &*self.string as &'static str
    }
}

impl Default for StrRef {
    fn default() -> Self {
        StrRef::empty()
    }
}

impl Debug for StrRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl Deref for StrRef {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        //SAFETY: instance holds ref-count to string
        unsafe { &*self.string }
    }
}
