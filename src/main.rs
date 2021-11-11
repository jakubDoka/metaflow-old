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

fn run() {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() < 2 {
        println!("Usage: <file>.pmh");
        return;
    }

    let mut generator = gen::Generator::new();
    let data = generator.generate(&args[1]).unwrap();
    std::fs::write(format!("{}.exe", args[1]), data).unwrap();
}

#[cfg(feature = "testing")]
fn test() {
    lexer::test();
    ast::test();
}
