pub mod pool;
pub mod sdbm;
pub mod storage;

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

pub fn test() {
    storage::test();
    pool::test();
}
