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

    pub fn join(&self, other: &Self, trim: bool) -> Self {
        let rc = self.rc.clone().unwrap();
        if self.rc != other.rc {
            if other.rc.is_none() {
                return Self::new(&rc, self.range.start..rc.len());
            }
            panic!("Spam::join: Spams must be from the same String");
        }

        let end = if trim {
            let mut init = other.range.start;
            while (rc.as_bytes()[init - 1] as char).is_whitespace() {
                init -= 1;
            }
            init
        } else {
            self.range.end.max(other.range.end)
        };

        let new_range = self.range.start.min(other.range.start)..end;

        Self::new(self.rc.as_ref().unwrap(), new_range)
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
