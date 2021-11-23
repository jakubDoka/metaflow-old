use std::{
    fmt::Debug,
    ops::{Deref, Range},
};

use crate::util::sdbm::SdbmHash;

#[derive(Clone, PartialEq, Default)]
pub struct Spam {
    pub string: &'static str,
    pub range: Range<usize>,
}

impl Spam {
    #[inline]
    pub fn new(string: &'static str, range: Range<usize>) -> Self {
        Self { string, range }
    }

    #[inline]
    pub fn whole(string: &'static str) -> Self {
        Self::new(string, 0..string.len())
    }

    #[inline]
    pub fn sub(&self, range: Range<usize>) -> Self {
        let new_range = self.range.start + range.start..self.range.start + range.end;
        Self::new(self.string, new_range)
    }

    pub fn join(&self, other: &Self, trim: bool) -> Self {
        if self.string != other.string {
            if other.string.is_empty() {
                return Self::new(self.string, self.range.start..self.string.len());
            }
            panic!("Spam::join: Spams must be from the same String");
        }

        let end = if trim {
            let mut init = other.range.start;
            while (self.string.as_bytes()[init - 1] as char).is_whitespace() {
                init -= 1;
            }
            init
        } else {
            self.range.end.max(other.range.end)
        };

        let new_range = self.range.start.min(other.range.start)..end;

        Self::new(self.string, new_range)
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
        &self.string[self.range.clone()]
    }
}

impl SdbmHash for Spam {
    #[inline]
    fn bytes(&self) -> &[u8] {
        self.deref().as_bytes()
    }
}
