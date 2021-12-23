pub mod generator;

use generator::*;

use cranelift_codegen::{
    isa::{self, LookupError},
    settings::{self, Configurable, SetError},
};

use cranelift_object::{ObjectBuilder, ObjectModule};
use std::process::Command;

use crate::{
    cli::Arguments,
    functions::{FError, FErrorDisplay, Program},
    lexer::{Token, TokenDisplay},
    module_tree::{MTError, MTErrorDisplay, MTParser}, collector::Collector, ast::{AParser, AErrorDisplay, AError},
};

use super::*;

type Result<T> = std::result::Result<T, (Option<GState>, GError)>;

pub fn compile(args: Arguments) -> Result<()> {
    if args.len() < 1 {
        return Err((None, GEKind::NoFiles.into()));
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

    std::fs::write(&obj_name, obj_file).map_err(|e| (None, GEKind::IoError(e).into()))?;

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
            .map_err(|e| (None, GEKind::IoError(e).into()))?
            .code()
            .unwrap(),
        0,
    );

    std::fs::remove_file(&obj_name).map_err(|e| (None, GEKind::IoError(e).into()))?;

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
            .map_err(|e| (None, GEKind::CompilationFlagError(e).into()))?;
        }
    }

    if let Some(opt_level) = args.get_flag("opt_level").or(args.get_flag("ol")) {
        settings
            .set("opt_level", opt_level)
            .map_err(|e| (None, GEKind::CompilationFlagError(e).into()))?;
    }

    let flags = settings::Flags::new(settings);

    let isa = if let Some(triplet) = args.get_flag("triplet") {
        isa::lookup_by_name(triplet)
            .map_err(|e| (None, GEKind::InvalidTriplet(e).into()))?
            .finish(flags)
    } else {
        cranelift_native::builder().unwrap().finish(flags)
    };

    let builder =
        ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();

    let stacktrace = args.enabled("trace");

    let mut program = Program::new(ObjectModule::new(builder), stacktrace);

    let mut state = GState::default();
    let mut context = GContext::default();

    if let Err(e) = MTParser::new(&mut state, &mut context).parse(&args[0]) {
        return Err((Some(state), GEKind::MTError(e).into()));
    }
      
    let mut collector = Collector::default();

    for module in std::mem::take(&mut state.module_order).drain(..).rev() {
        let mut ast = std::mem::take(&mut state.modules[module].ast);

        let result = AParser::new(&mut state, &mut ast, &mut context).parse();
        let mut ast = match result {
            Ok(ast) => ast,
            Err(e) => return Err((Some(state), GEKind::AError(e).into())),
        };

        collector.clear(&mut context);
        collector.parse(&mut state, &mut ast);

        context.recycle(ast);

        if let Err(e) = Generator::new(&mut program, &mut state, &mut context, &mut collector)
            .generate(module) {
            return Err((Some(state), e));
        }
      
    }

    Generator::new(&mut program, &mut state, &mut context, &mut collector)
        .finalize()
        .map_err(|err| (Some(state), err))?;

    Ok(program.module.finish().emit().unwrap())
}

pub struct GErrorDisplay<'a> {
  pub state: Option<&'a GState>,
  pub error: &'a GError,
}

impl<'a> GErrorDisplay<'a> {
  pub fn new(state: Option<&'a GState>, error: &'a GError) -> Self {
      Self { state, error }
  }
}

impl std::fmt::Display for GErrorDisplay<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      writeln!(f, "{}", TokenDisplay::new(&self.state.unwrap(), &self.error.token))?;

      match &self.error.kind {
          GEKind::FError(error) => {
              write!(f, "{}", FErrorDisplay::new(&self.state.unwrap(), error))?;
          },
          GEKind::MTError(error) => {
              write!(f, "{}", MTErrorDisplay::new(&self.state.unwrap(), error))?;
          },
          GEKind::AError(error) => {
              write!(f, "{}", AErrorDisplay::new(&self.state.unwrap(), error))?;
          },
          GEKind::IoError(err) => {
              writeln!(f, "{}", err)?;
          },
          GEKind::InvalidTriplet(error) => {
              writeln!(f, "invalid triplet: {}", error)?;
          },
          GEKind::CompilationFlagError(err) => {
              writeln!(f, "invalid compilation flag: {}", err)?;
          },
          GEKind::NoFiles => {
              writeln!(f, "first argument is missing <FILE>")?;
          },
      }

      Ok(())
  }
}

#[derive(Debug)]
pub struct GError {
    kind: GEKind,
    token: Token,
}

impl GError {
    pub fn new(kind: GEKind, token: Token) -> Self {
        Self { kind, token }
    }
}

#[derive(Debug)]
pub enum GEKind {
    MTError(MTError),
    FError(FError),
    AError(AError),
    IoError(std::io::Error),
    InvalidTriplet(LookupError),
    CompilationFlagError(SetError),
    NoFiles,
}

impl Into<GError> for GEKind {
    fn into(self) -> GError {
        GError {
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
attr entry
fun main -> int:
  goo()
  return 1

fun goo:
  foo()

fun foo:
  panic("foo")
      "#,
      1,
    );
    test_sippet(
        r#"
fun fib(v: int) -> int:
  return if v < 2:
    1
  else:
    fib(v - 1) + fib(v - 2)

fun fib_loop(v: int) -> int:
  var
    a, b, c = 1
    v = v
  loop'a:
    c = a + b
    a = b
    b = c
    v = v - 1
    if v == 1:
      break'a
  return c

attr entry
fun main -> int:
  let v = 10
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

impl Point:
  fun set(p: Self, x: int, y: int) -> Self:
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
  return bool::int(!true) + ~1 + 2 + abs -1 - 1 + a
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
  return f64::int(a) - 101
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

impl Point:
  fun init(v: &Point, x: int, y: int) -> Point:
    (*v).x = x
    (*v).y = y
    pass

attr entry
fun main -> int:
  var p: Point
  p.init(2, 2)
  return p.x + p.y - 4
        "#,
        0,
    );
    test_sippet(
        r#"
struct Point:
  x, y: int

struct Cell[T]:
  priv embed p: &T

attr entry
fun main -> int:
  var 
    p: Point
    c: Cell[Point]
  c.p = &p
  
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

  return u8::int(eb.a + eb.h + eb.g + eb.f + eb.e + eb.d + eb.c + eb.b - 4i8 * 9i8)
  "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  let array = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  var 
    i = 0
    sum = 0
  
  loop:
    if i >= array.len():
      break
    sum += array[i]
    i += 1

  return sum - 11 * 5
        "#,
        0,
    );
    test_sippet(
        r#"

var storage: [int, 10]

attr entry
fun main -> int:
  let array = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  var 
    i = 0
    sum = 0
  
  loop:
    if i >= array.len():
      break
    sum += array[i]
    storage[i] = array[i]
    i += 1

  return sum - 11 * 5
        "#,
        0,
    );
    test_sippet(
        r#"
attr entry
fun main -> int:
  var a = 1
  var b = &a
  *b = 0
  return a 
      "#,
        0,
    );

    test_sippet(
        r#"
let a = 1

attr entry
fun main -> int:
  return a - 1
    "#,
        0,
    );
    test_sippet(
        r#"
attr inline
fun something(a, b: int) -> int:
  return (a + b) - 2 * a

attr inline
fun even_worse(a, b: int) -> int:
  if a > b:
    return something(a, b)
  else:
    return something(b, a)

attr entry
fun main -> int:
  return even_worse(1, 1)
    "#,
        0,
    );

    std::fs::remove_file("src/gen/test_project/root.mf").unwrap_or(());
    std::fs::remove_file("test_project.exe").unwrap_or(());
}

pub fn test_sippet(sippet: &str, exit_code: i32) {
    std::fs::write("src/gen/test_project/root.mf", sippet).unwrap();

    let args = Arguments::from_str("root src/gen/test_project -trace").unwrap();


    compile(args)
      .map_err(|(state, e)| panic!("{}", GErrorDisplay::new(state.as_ref(), &e)))
      .unwrap();

    println!("output:");
    let output = Command::new(".\\test_project.exe").status().unwrap();
    println!(":end");

    assert_eq!(output.code().unwrap(), exit_code);
}
