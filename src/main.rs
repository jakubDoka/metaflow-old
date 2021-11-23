#![allow(dead_code)]
extern crate cranelift_codegen;
extern crate cranelift_frontend;

pub mod ast;
pub mod cli;
pub mod ir;
pub mod ir_gen;
pub mod lexer;
pub mod testing;
pub mod util;

pub const FILE_EXTENSION: &str = ".pmt";

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

    #[cfg(debug_assertions)]
    assert!(util::cell::report_cell_state() == 0);
}

#[cfg(feature = "testing")]
fn test() {
    cli::test();
    lexer::test();
    ast::test();
    ir::test();
    ir_gen::gen::test();
}
