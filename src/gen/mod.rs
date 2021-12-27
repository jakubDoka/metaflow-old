pub mod generator;

use generator::*;

use cranelift_codegen::{
    isa::{self, LookupError},
    settings::{self, Configurable, SetError},
};

use cranelift_object::{ObjectBuilder, ObjectModule};
use std::process::Command;

use crate::{
    ast::{AError, AErrorDisplay, AParser, Vis},
    util::cli::Arguments,
    collector::Collector,
    functions::{FError, FErrorDisplay},
    lexer::{Token, TokenDisplay},
    module_tree::{MTError, MTErrorDisplay, MTParser},
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
        collector.parse(&mut state, &mut ast, Vis::None);

        context.recycle(ast);

        if let Err(e) =
            Generator::new(&mut program, &mut state, &mut context, &mut collector).generate(module)
        {
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
        if let Some(state) = self.state {
            writeln!(
                f,
                "{}",
                TokenDisplay::new(state, &self.error.token)
            )?;
        }

        match &self.error.kind {
            GEKind::FError(error) => {
                write!(f, "{}", FErrorDisplay::new(&self.state.unwrap(), error))?;
            }
            GEKind::MTError(error) => {
                write!(f, "{}", MTErrorDisplay::new(&self.state.unwrap(), error))?;
            }
            GEKind::AError(error) => {
                write!(f, "{}", AErrorDisplay::new(&self.state.unwrap(), error))?;
            }
            GEKind::IoError(err) => {
                writeln!(f, "{}", err)?;
            }
            GEKind::InvalidTriplet(error) => {
                writeln!(f, "invalid triplet: {}", error)?;
            }
            GEKind::CompilationFlagError(err) => {
                writeln!(f, "invalid compilation flag: {}", err)?;
            }
            GEKind::NoFiles => {
                writeln!(f, "first argument is missing <FILE>")?;
            }
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
    let args = Arguments::from_str("root src/gen/test_project -trace").unwrap();

    compile(args)
        .map_err(|(state, e)| panic!("{}", GErrorDisplay::new(state.as_ref(), &e)))
        .unwrap();

    println!("output:");
    let output = Command::new(".\\test_project.exe").status().unwrap();
    println!("\n:end");

    assert_eq!(output.code().unwrap(), 0);

    std::fs::remove_file(".\\test_project.exe").unwrap();
}
