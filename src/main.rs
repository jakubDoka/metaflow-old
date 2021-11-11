#![allow(dead_code)]
extern crate cranelift_codegen;
extern crate cranelift_frontend;

pub mod ast;
pub mod gen;
pub mod lexer;
pub mod testing;

fn main() {
    #[cfg(feature = "testing")]
    test();
    #[cfg(not(feature = "testing"))]
    run();
}

fn run() {}

#[cfg(feature = "testing")]
fn test() {
    lexer::test();
    ast::test();
    gen::test();
}
