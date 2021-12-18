#![allow(dead_code)]
#![feature(vec_into_raw_parts)]
extern crate cranelift_codegen;
extern crate cranelift_frontend;

pub mod ast;
pub mod attributes;
pub mod cli;
pub mod functions;
pub mod gen;
pub mod lexer;
pub mod module_tree;
pub mod testing;
pub mod types;
pub mod util;

pub const FILE_EXTENSION: &str = ".pmt";

fn main() {
    #[cfg(feature = "testing")]
    test();
    #[cfg(not(feature = "testing"))]
    run();
}

fn run() {
    /*let args = match cli::Arguments::new(std::env::args()) {
        Ok(args) => args,
        Err(e) => {
            println!("{:?}", e);
            return;
        }
    };

    match gen::compile(args) {
        Ok(_) => println!("Successfully compiled"),
        Err(err) => println!("Failed to compile: {:?}", err),
    };*/
}

#[repr(C)]
struct AlignmentTest {
    a: u8,
    b: u8,
    c: u8,
    d: u16,
}

//#[repr(C)]
enum Foo {
    A,
    B,
    C,
    D,
}

#[cfg(feature = "testing")]
fn test() {
    cli::test();
    util::test();
    lexer::test();
    ast::test();
    module_tree::test();
    types::test();
    functions::test();
    gen::test();
}
