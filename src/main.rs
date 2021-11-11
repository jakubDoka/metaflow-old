#![allow(dead_code)]
extern crate cranelift_codegen;
extern crate cranelift_frontend;

pub mod ast;
pub mod ir_gen;
pub mod lexer;
pub mod testing;

fn main() {
    #[cfg(feature = "testing")]
    test();
    #[cfg(not(feature = "testing"))]
    run();
}

fn run() {
    let args = std::env::args().collect::<Vec<_>>();
    match ir_gen::gen::compile(&args[1]) {
        Ok(_) => println!("Successfully compiled"),
        Err(err) => println!("Failed to compile: {:?}", err),
    };
}

#[cfg(feature = "testing")]
fn test() {
    lexer::test();
    ast::test();
    ir_gen::test();
}
