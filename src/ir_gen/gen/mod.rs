use cranelift_codegen::{
    isa::{self, LookupError},
    settings::{self, Configurable, SetError},
};

use cranelift_object::{ObjectBuilder, ObjectModule};
use std::process::Command;

use crate::cli::Arguments;

use super::*;

pub type Result<T> = std::result::Result<T, GenError>;

pub fn compile(args: Arguments) -> Result<()> {
    if args.args.len() < 1 {
        return Err(GEKind::NoFiles.into());
    }

    let obj_file = generate_obj_file(&args)?;

    let name = args.args[0]
        .split("/")
        .last()
        .unwrap()
        .split(".")
        .next()
        .unwrap();

    let output_name = args.field_flags
        .iter()
        .find(|(f, _)| f == "o")
        .map(|(_, v)| v.as_str())
        .unwrap_or(name);

    let obj_name = format!("{}.o", output_name);

    std::fs::write(&obj_name, obj_file).map_err(Into::into)?;

    if args.flags.iter().any(|f| f == "obj") {
        return Ok(());
    }

    let link_with = args
        .field_flags
        .iter()
        .find(|(f, _)| f == "lw")
        .map(|(_, f)| f.as_str())
        .unwrap_or("")
        .split(";")
        .filter(|s| !s.is_empty());

    assert_eq!(
        Command::new("cc")
            .args(
                ["-o", &format!("{}.exe", output_name), &obj_name]
                    .iter()
                    .map(|a| *a)
                    .chain(link_with),
            )
            .status()
            .map_err(Into::into)?
            .code()
            .unwrap(),
        0,
    );

    std::fs::remove_file(&obj_name).map_err(Into::into)?;

    Ok(())
}

pub fn generate_obj_file(args: &Arguments) -> Result<Vec<u8>> {
    

    let mut settings = settings::builder();
    for (_, values) in args.field_flags.iter().filter(|(f, _)| f == "comp_flags") {
        for value in values.split(" ") {
            let mut value = value.split("=");
            let flag = value.next().unwrap();
            if let Some(value) = value.next() {
                settings.set(flag, value)
            } else {
                settings.enable(flag)
            }
            .map_err(|e| GEKind::CompilationFlagError(e).into())?;
        }
    }

    let flags = settings::Flags::new(settings);

    let isa = if let Some((_, triplet)) = args.field_flags.iter().find(|(n, _)| n == "triplet") {
        isa::lookup_by_name(triplet)
            .map_err(|e| GEKind::InvalidTriplet(e).into())?
            .finish(flags)
    } else {
        cranelift_native::builder().unwrap().finish(flags)
    };

    let _optimize = args.flags.iter().any(|f| f == "opt");

    let builder =
        ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();

    let main_module = Generator::new(ObjectModule::new(builder))
        .generate(&args.args[0])
        .map_err(Into::into)?;

    Ok(main_module.finish().emit().unwrap())
}

#[derive(Debug)]
pub struct GenError {
    kine: GEKind,
    token: Option<Token>,
}

impl Into<GenError> for IrGenError {
    fn into(self) -> GenError {
        GenError {
            kine: GEKind::IrGenError(self.kind),
            token: self.token,
        }
    }
}

impl Into<GenError> for std::io::Error {
    fn into(self) -> GenError {
        GenError {
            kine: GEKind::IoError(self),
            token: None,
        }
    }
}

#[derive(Debug)]
pub enum GEKind {
    IrGenError(IGEKind),
    IoError(std::io::Error),
    InvalidTriplet(LookupError),
    CompilationFlagError(SetError),
    NoFiles,
}

impl Into<GenError> for GEKind {
    fn into(self) -> GenError {
        GenError {
            kine: self,
            token: None,
        }
    }
}

pub fn test() {
    test_sippet(
        r#"
fun main -> i64:
  return 0
        "#,
        0,
    );
    test_sippet(
        r#"
fun main -> i64:
  return 1 - 1
        "#,
        0,
    );
    test_sippet(
        r#"
fun main -> i64:
  return 1 + 1
        "#,
        2,
    );
    test_sippet(
        r#"
fun main -> i64:
  return if 1 == 1: 0 else: 1
        "#,
        0,
    );
    test_sippet(
        r#"
fun fib(v: i32) -> i32:
  return if v < 2i32:
    1i32
  else:
    fib(v - 1i32) + fib(v - 2i32)

attr linkage(import), call_conv(windows_fastcall)
fun putchar(c: i32)

fun fib_loop(v: i32) -> i32:
  var 
    a, b, c = 1i32
    v = v
  loop'a:
    c = a + b
    a = b
    b = c
    v = v - 1i32
    putchar(v)
    if v == 1i32:
      break'a
  return c

fun main -> i32:
  let v = 10i32
  return fib_loop(v) - fib(v)
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: i64

struct Point3:
  embed point: Point
  z: i64

struct Rect:
  mi: Point
  ma: Point

fun main -> i64: 
  var 
    p: Point
    p3: Point3
    r: Rect
  return 0
        "#,
        0,
    );
}

pub fn test_sippet(sippet: &str, exit_code: i32) {
    std::fs::write("test_case.pmt", sippet).unwrap();

    let args = Arguments::from_str("root test_case.pmt").unwrap();

    compile(args).unwrap();

    let output = Command::new("test_case.exe").output().unwrap();

    assert_eq!(output.status.code().unwrap(), exit_code);

    std::fs::remove_file("test_case.pmt").unwrap_or(());
    std::fs::remove_file("test_case.exe").unwrap_or(());
}
