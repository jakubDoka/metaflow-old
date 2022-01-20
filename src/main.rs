#![feature(vec_into_raw_parts)]

//use std::time::Instant;

//use gen::GErrorDisplay;

pub mod ast;
pub mod entities;
pub mod functions;
//pub mod gen;
pub mod incr;
pub mod lexer;
pub mod module_tree;
pub mod testing;
pub mod types;
pub mod util;

pub const COMMIT_HASH: &str = env!("GIT_HASH");

fn main() {
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
    module_tree::test();
    types::test();
    functions::test();
    gen::test();
}
