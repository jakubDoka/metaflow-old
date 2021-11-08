pub mod lexer;

fn main() {
    #[cfg(feature = "testing")]
    test();
}

#[cfg(feature = "testing")]
fn test() {
    lexer::test();
}
