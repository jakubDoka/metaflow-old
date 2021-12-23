pub const TEST_CODE: &str = include_str!("test_code.mf");
pub const TEST_GEN_CODE: &str = include_str!("test_gen_code.mf");

#[macro_export]
macro_rules! test_println {
    ($string:literal, $($arg:expr)*) => {
        #[cfg(feature = "testing")]
        {
            println!($string, $($arg)*);
        }
    }
}
