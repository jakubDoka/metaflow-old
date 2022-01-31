//! Crate metaflow is a compiler executable for metaflow language.

#![feature(vec_into_raw_parts)]
//#![warn(missing_docs)]

use cranelift::codegen::ir::Function;

//use std::time::Instant;

//use gen::GErrorDisplay;

pub mod ast;
//pub mod entities;
//pub mod functions;
//pub mod gen;
pub mod incr;
pub mod lexer;
pub mod modules;
pub mod types;
pub mod util;

/// Crate version used for validating incremental data.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    println!("{}", std::mem::size_of::<Function>());
    #[cfg(feature = "testing")]
    test();
    #[cfg(not(feature = "testing"))]
    run();
}

#[cfg(not(feature = "testing"))]
fn run() {
    /*let args = match util::cli::Arguments::new(std::env::args()) {
        Ok(args) => args,
        Err(e) => {
            println!("{:?}", e);
            return;
        }
    };

    let now = Instant::now();

    match gen::compile(args) {
        Ok(line_count) => {
            println!(
                "Successfully compiled! ({} lines of code in {}s)",
                line_count,
                now.elapsed().as_secs_f32()
            );
        },
        Err((state, err)) => println!(
            "Failed to compile:\n {}",
            GErrorDisplay::new(state.as_ref(), &err)
        ),
    };*/
}

#[cfg(feature = "testing")]
fn test() {
    util::test();
    lexer::test();
    ast::test();
    modules::test();
    //types::test();
    //functions::test();
    //gen::test();
}
