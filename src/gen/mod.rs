pub mod generator;

use generator::*;

use cranelift_codegen::{
    isa::{self, LookupError},
    settings::{self, Configurable, SetError},
};

use cranelift_object::{ObjectBuilder, ObjectModule};
use std::{fmt::Display, process::Command};

use crate::{
    cli::Arguments,
    functions::{FContext, FEDisplay, FError, FState, Program},
    lexer::{TKind as LTKind, Token, TokenView},
    module_tree::{MTContext, MTEDisplay, MTError, MTParser, MTState},
    types::{TContext, TState},
};

use super::*;

type Result<T> = std::result::Result<T, GenError>;

pub fn compile(args: Arguments) -> Result<()> {
    if args.len() < 1 {
        return Err(GEKind::NoFiles.into());
    }

    let obj_file = generate_obj_file(&args)?;

    let name = args[0]
        .split("/")
        .last()
        .unwrap()
        .split(".")
        .next()
        .unwrap();

    let output_name = args
        .get_flag("o")
        .or(args.get_flag("output"))
        .unwrap_or(name);

    let obj_name = format!("{}.o", output_name);

    std::fs::write(&obj_name, obj_file).map_err(|e| GEKind::IoError(e).into())?;

    if args.enabled("obj") {
        return Ok(());
    }

    let link_with = args
        .get_flag("lv")
        .or(args.get_flag("link-with"))
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
            .map_err(|e| GEKind::IoError(e).into())?
            .code()
            .unwrap(),
        0,
    );

    std::fs::remove_file(&obj_name).map_err(|e| GEKind::IoError(e).into())?;

    Ok(())
}

pub fn generate_obj_file(args: &Arguments) -> Result<Vec<u8>> {
    let mut settings = settings::builder();
    if let Some(s) = args.get_flag("co").or(args.get_flag("compiler-options")) {
        for value in s.split(" ") {
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

    //let const_fold = args.enabled("const-fold") || args.enabled("cf");

    if let Some(opt_level) = args.get_flag("opt_level").or(args.get_flag("ol")) {
        settings
            .set("opt_level", opt_level)
            .map_err(|e| GEKind::CompilationFlagError(e).into())?;
    }

    let flags = settings::Flags::new(settings);

    let isa = if let Some(triplet) = args.get_flag("triplet") {
        isa::lookup_by_name(triplet)
            .map_err(|e| GEKind::InvalidTriplet(e).into())?
            .finish(flags)
    } else {
        cranelift_native::builder().unwrap().finish(flags)
    };

    let builder =
        ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();

    let mut program = Program::new(ObjectModule::new(builder));

    let mut state = MTState::default();
    let mut context = MTContext::default();

    if let Err(error) = MTParser::new(&mut state, &mut context).parse(&args[0]) {
        eprintln!("{}", MTEDisplay::new(&state, &error));
        return Err(GEKind::ModuleTreeError(error).into());
    }

    let state = TState::new(state);
    let context = TContext::new(context);
    let state = FState::new(state);
    let context = FContext::new(context);
    let mut state = GState::new(state);
    let mut context = GContext::new(context);

    for i in (0..state.module_order.len()).rev() {
        let module = state.module_order[i];
        if let Err(error) = Generator::new(&mut program, &mut state, &mut context).generate(module)
        {
            eprintln!("{}", GEDisplay::new(&state, &error));
            return Err(error);
        }
    }

    Ok(program.module.finish().emit().unwrap())
}

pub struct GEDisplay<'a> {
    state: &'a GState,
    error: &'a GenError,
}

impl<'a> GEDisplay<'a> {
    pub fn new(state: &'a GState, error: &'a GenError) -> Self {
        Self { state, error }
    }
}

impl<'a> Display for GEDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.error.token.kind != LTKind::None {
            writeln!(f, "{}", TokenView::new(&self.error.token))?;
        }
        match &self.error.kind {
            GEKind::FunError(error) => {
                write!(f, "{}", FEDisplay::new(&self.state, error))
            }
            GEKind::ModuleTreeError(error) => {
                write!(f, "{}", MTEDisplay::new(&self.state, error))
            }
            GEKind::IoError(err) => {
                writeln!(f, "{}", err)?;
                Ok(())
            }
            GEKind::InvalidTriplet(error) => {
                writeln!(f, "invalid triplet: {}", error)?;
                Ok(())
            }
            GEKind::CompilationFlagError(err) => {
                writeln!(f, "invalid compilation flag: {}", err)?;
                Ok(())
            }
            GEKind::NoFiles => writeln!(f, "first argument is missing <FILE>"),
        }
    }
}

#[derive(Debug)]
pub struct GenError {
    kind: GEKind,
    token: Token,
}

impl GenError {
    pub fn new(kind: GEKind, token: Token) -> GenError {
        GenError { kind, token }
    }
}

#[derive(Debug)]
pub enum GEKind {
    ModuleTreeError(MTError),
    FunError(FError),
    IoError(std::io::Error),
    InvalidTriplet(LookupError),
    CompilationFlagError(SetError),
    NoFiles,
}

impl Into<GenError> for GEKind {
    fn into(self) -> GenError {
        GenError {
            kind: self,
            token: Token::default(),
        }
    }
}

pub fn test() {
    test_sippet(
        r#"
attr entry
fun main -> int:
  return 0
        "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  return 1 - 1
        "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  return 1 + 1
        "#,
        2,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
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

fun fib_loop(v: i32) -> i32:
  var
    a, b, c = 1i32
    v = v
  loop'a:
    c = a + b
    a = b
    b = c
    v = v - 1i32
    if v == 1i32:
      break'a
  return c

attr entry
fun main -> i32:
  let v = 10i32
  return fib_loop(v) - fib(v)
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: int

struct Point3:
  embed point: Point
  z: int

struct Rect:
  mi: Point
  ma: Point

attr entry
fun main -> int:
  var
    p: Point
    p3: Point3
    r: Rect

  p.x = 1
  p3.point = p
  p3.y = 2
  r.mi = p3.point

  return r.mi.x - r.mi.y + 1
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: int

fun set(p: Point, x: int, y: int) -> Point:
  var p = p
  p.x = x
  p.y = y
  return p

attr entry
fun main -> int:
  var p, q: Point
  p = p.set(1, 2)
  return p.x + p.y - 3
        "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  var a: int
  ++a
  --a
  return int(!true) + ~1 + 2 + abs -1 - 1 + a
        "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  var a = 1.0
  loop:
    a = a + 1.0
    if a > 100.0:
      break
  return int(a) - 101
        "#,
        0,
    );
    test_sippet(
        r#"
attr linkage(import), call_conv(platform)
fun putchar(c: i32)

attr entry
fun main -> int:
  var
    a = "Hello, World!"
    b = a as uint
  loop:
    let char = *(b as &u8)
    if char == 0u8:
      break
    putchar(char.i32())
    b += 1 as uint
  return 0
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: int

fun init(v: &var Point, x: int, y: int) -> Point:
  (*v).x = x
  (*v).y = y
  pass

attr entry
fun main -> int:
  var p: Point
  p.init(2, 2)
  return p.x - p.y
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: int

struct Cell[T]:
  priv embed p: &var T

attr entry
fun main -> int:
  var 
    p: Point
    c: Cell[Point]
  c.p = &var p
  
  c.x = 1
  c.y = 2

  return 0
        "#,
        0,
    );
    test_sippet(
        r#"
struct EightBytes:
  a, b, c, d, e, f, g, h: i8
  
attr entry
fun main -> int:
  var eb: EightBytes
  eb.a = 1i8
  eb.b = 2i8
  eb.c = 3i8
  eb.d = 4i8
  eb.e = 5i8
  eb.f = 6i8
  eb.g = 7i8
  eb.h = 8i8

  return int(eb.a + eb.h + eb.g + eb.f + eb.e + eb.d + eb.c + eb.b - 4i8 * 9i8)
  "#,
        0,
    );
}

pub fn test_sippet(sippet: &str, exit_code: i32) {
    std::fs::write("src/gen/test_project/root.mf", sippet).unwrap();

    let args = Arguments::from_str("root src/gen/test_project").unwrap();

    compile(args).unwrap();

    let output = Command::new("test_project.exe").output().unwrap();

    assert_eq!(output.status.code().unwrap(), exit_code);

    std::fs::remove_file("src/gen/test_project/root.mf").unwrap_or(());
    std::fs::remove_file("test_project.exe").unwrap_or(());
}
