pub mod sdbm;
pub mod storage;
pub mod pool;

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

pub fn test() {
    storage::test();
    pool::test();
}
