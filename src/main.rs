#![feature(vec_into_raw_parts)]

//use gen::GErrorDisplay;

pub mod ast;
//pub mod functions;
//pub mod gen;
pub mod incr;
pub mod entities;
pub mod lexer;
pub mod module_tree;
pub mod testing;
pub mod types;
pub mod util;

pub const FILE_EXTENSION: &str = ".pmt";
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    #[cfg(feature = "testing")]
    test();
    #[cfg(not(feature = "testing"))]
    run();
}

fn run() {
    /*let args = match util::cli::Arguments::new(std::env::args()) {
        Ok(args) => args,
        Err(e) => {
            println!("{:?}", e);
            return;
        }
    };

    match gen::compile(args) {
        Ok(_) => println!("Successfully compiled"),
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
    module_tree::test();
    types::test();
    //functions::test();
    //gen::test();
}
