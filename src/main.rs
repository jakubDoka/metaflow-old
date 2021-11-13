#![allow(dead_code)]
extern crate cranelift_codegen;
extern crate cranelift_frontend;

pub mod ast;
pub mod cli;
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
    let args = match cli::Arguments::new(std::env::args()) {
        Ok(args) => args,
        Err(e) => {
            println!("{:?}", e);
            return;
        }
    };

    match ir_gen::gen::compile(args) {
        Ok(_) => println!("Successfully compiled"),
        Err(err) => println!("Failed to compile: {:?}", err),
    };
}

#[cfg(feature = "testing")]
fn test() {
    cli::test();
    lexer::test();
    ast::test();
    ir_gen::gen::test();
}
