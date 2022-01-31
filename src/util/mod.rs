//! Module util holds some utility that cannot really be related with main modules.
use quick_proc::RealQuickSer;

pub mod cli;
pub mod pool;
pub mod sdbm;
pub mod storage;

/// Size defines any size or offset inside generated code.
/// It takes track of both 32 and 64 bit pointer width and allows
/// picking the final value. This is useful when we don't know which
/// or even both sizes has to be used.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, RealQuickSer, PartialOrd, Ord)]
pub struct Size {
    /// Size for 32 bit arch.
    s32: u32,
    /// Size for 64 bit arch.
    s64: u32,
}

impl Size {
    /// Zero value.
    pub const ZERO: Self = Self { s32: 0, s64: 0 };
    /// Represents the pointer size.
    pub const POINTER: Self = Self { s32: 4, s64: 8 };

    /// Because of private fields
    pub fn new(s32: u32, s64: u32) -> Self {
        Self { s32, s64 }
    }

    /// Adds two sizes.
    pub fn add(self, other: Self) -> Self {
        Self::new(self.s32 + other.s32, self.s64 + other.s64)
    }

    /// Multiplies two sizes.
    pub fn mul(self, other: Self) -> Self {
        Self::new(self.s32 * other.s32, self.s64 * other.s64)
    }

    /// Returns reminder of division by other.
    pub fn rem(self, other: Self) -> Self {
        Self::new(self.s32 % other.s32, self.s64 % other.s64)
    }

    /// Returns max of both sizes.
    pub fn max(self, other: Self) -> Self {
        Self::new(self.s32.max(other.s32), self.s64.max(other.s64))
    }

    /// Returns min of both sizes.
    pub fn min(self, other: Self) -> Self {
        Self::new(self.s32.min(other.s32), self.s64.min(other.s64))
    }

    /// Picks the size. If s32 is true, then self.s32 is picked, otherwise self.s64.
    pub fn pick(self, s32: bool) -> u32 {
        if s32 {
            self.s32
        } else {
            self.s64
        }
    }

    pub fn s64(&self) -> u32 {
        self.s64
    }

    pub fn s32(&self) -> u32 {
        self.s32
    }
}

/// Writes the `number` with given `radix` to `buffer`.
pub fn write_radix(mut number: u64, radix: u64, buffer: &mut String) {
    while number > 0 {
        let mut digit = (number % radix) as u8;
        digit += (digit < 10) as u8 * b'0' + (digit >= 10) as u8 * (b'a' - 10);
        buffer.push(digit as char);
        number /= radix;
    }
}

#[macro_export]
macro_rules! impl_wrapper {
    ($name:ident, $type:ty) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, RealQuickSer)]
        pub struct $name(pub $type);
    };
}

#[macro_export]
macro_rules! impl_entity {
    ($($name:ident),*) => {
        $(
            #[derive(Clone, Copy, Debug, PartialEq, Eq, RealQuickSer)]
            pub struct $name(u32);

            impl Default for $name {
                fn default() -> Self {
                    Self::reserved_value()
                }
            }

            cranelift::entity::entity_impl!($name);
        )*
    };
}

pub fn test() {
    pool::test();
    cli::test();
    storage::test();
}
