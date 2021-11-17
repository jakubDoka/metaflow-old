use std::ops::Range;

use super::*;

pub struct Cursor {
    data: Spam,
    chars: Chars<'static>,
    line: usize,
    last_n_line: usize,
}

impl Cursor {
    pub fn new(data: Spam) -> Self {
        Cursor {
            //SAFETY: cursor disposes data only upon drop
            chars: unsafe { data.get_static_ref().chars() },
            data,
            line: 1,
            last_n_line: 0,
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    pub fn peek_n(&self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    pub fn progress(&self) -> usize {
        self.data.len() - self.chars.as_str().len()
    }

    #[inline]
    pub fn advance(&mut self) -> Option<char> {
        let char = self.chars.next();
        if char == Some('\n') {
            self.line += 1;
            self.last_n_line = self.progress();
        }
        char
    }

    pub fn sub(&self, range: Range<usize>) -> Spam {
        self.data.sub(range)
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn column(&self) -> usize {
        self.progress() - self.last_n_line
    }
}
