pub mod pool;
pub mod sdbm;
pub mod storage;
pub mod cli;

#[macro_export]
macro_rules! inherit {
    ($type:ty, $field:ident, $target:ty) => {
        impl Deref for $type {
            type Target = $target;

            fn deref(&self) -> &Self::Target {
                &self.$field
            }
        }

        impl DerefMut for $type {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.$field
            }
        }
    };
}

#[macro_export]
macro_rules! def_displayer {
    ($name:ident, $state:ty, $target:ty, |$self:ident, $f:ident| {
        $($pattern:pat => $code:tt,)*
    }) => {
        pub struct $name<'a> {
            pub state: &'a $state,
            pub error: &'a $target,
        }

        impl<'a> $name<'a> {
            pub fn new(state: &'a $state, error: &'a $target) -> Self {
                Self { state, error }
            }
        }

        impl std::fmt::Display for $name<'_> {
            fn fmt(&$self, $f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                writeln!($f, "{}", TokenDisplay::new($self.state, &$self.error.token))?;

                match &$self.error.kind {
                    $($pattern => $code,)*
                }

                Ok(())
            }
        }
    };
}

#[macro_export]
macro_rules! unwrap_enum {
    ($value:expr, $pattern:pat => $unwrapped:expr) => {
        match $value {
            $pattern => $unwrapped,
            _ => unreachable!(),
        }
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct Size {
    pub s32: u32,
    pub s64: u32,
}

impl Size {
    pub const ZERO: Self = Self { s32: 0, s64: 0 };
    pub const POINTER: Self = Self { s32: 4, s64: 8 };

    pub fn new(s32: u32, s64: u32) -> Self {
        Self { s32, s64 }
    }

    pub fn zero() -> Self {
        Self::new(0, 0)
    }

    pub fn add(self, other: Self) -> Self {
        Self::new(self.s32 + other.s32, self.s64 + other.s64)
    }

    pub fn mul(self, other: Self) -> Self {
        Self::new(self.s32 * other.s32, self.s64 * other.s64)
    }

    pub fn rem(self, other: Self) -> Self {
        Self::new(self.s32 % other.s32, self.s64 % other.s64)
    }

    pub fn max(self, other: Self) -> Self {
        Self::new(self.s32.max(other.s32), self.s64.max(other.s64))
    }

    pub fn min(self, other: Self) -> Self {
        Self::new(self.s32.min(other.s32), self.s64.min(other.s64))
    }

    pub fn pick(self, s32: bool) -> u32 {
        if s32 {
            self.s32
        } else {
            self.s64
        }
    }
}

pub fn write_radix(mut number: u64, radix: u64, buffer: &mut String) {
    while number > 0 {
        let mut digit = (number % radix) as u8;
        digit += (digit < 10) as u8 * b'0' + (digit >= 10) as u8 * (b'a' - 10);
        buffer.push(digit as char);
        number /= radix;
    }
}

pub fn test() {
    storage::test();
    pool::test();
    cli::test();
}
