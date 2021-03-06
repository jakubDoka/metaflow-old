pub mod generator;

use generator::*;

use cranelift::{codegen::{
    isa::{self, LookupError},
    settings::{self, Configurable, SetError},
}, entity::EntitySet};

use cranelift::object::{ObjectBuilder, ObjectModule};
use std::process::Command;

use crate::{
    ast::{AError, AErrorDisplay},
    functions::{FError, FErrorDisplay},
    lexer::{Token, TokenDisplay},
    module_tree::{MTError, MTErrorDisplay, MTParser},
    util::cli::Arguments, entities::{AnonString, Ty, Fun}, types::GarbageTarget,
};

use crate::incr::IncrementalData; 

type Result<T> = std::result::Result<T, (Option<GState>, GError)>;

pub fn compile(args: Arguments) -> Result<usize> {
    if args.len() < 1 {
        return Err((None, GEKind::NoFiles.into()));
    }

    let (obj_file, lines_of_code) = generate_obj_file(&args)?;

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

    std::fs::write(&obj_name, obj_file).map_err(|e| (None, GEKind::IoError(
        "failed to write temporary object file", e
    ).into()))?;

    if args.enabled("obj") {
        return Ok(lines_of_code);
    }

    let link_with = args
        .get_flag("lv")
        .or(args.get_flag("link-with"))
        .unwrap_or("")
        .split(";")
        .filter(|s| !s.is_empty());

    let linker = args
        .get_flag("linker")
        .unwrap_or("cc");

    assert_eq!(
        Command::new(linker)
            .args(
                ["-o", &format!("{}.exe", output_name), &obj_name]
                    .iter()
                    .map(|a| *a)
                    .chain(link_with),
            )
            .status()
            .map_err(|e| (None, GEKind::IoError(
                "problem with linker", e
            ).into()))?
            .code()
            .unwrap(),
        0,
    );

    std::fs::remove_file(&obj_name).map_err(|e| (None, GEKind::IoError(
       "failed to remove temporary object file", e
    ).into()))?;

    Ok(lines_of_code)
}

pub fn generate_obj_file(args: &Arguments) -> Result<(Vec<u8>, usize)> {
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
        cranelift::native::builder().unwrap().finish(flags)
    };

    let builder =
        ObjectBuilder::new(isa, "all", cranelift::module::default_libcall_names()).unwrap();

    let stacktrace = args.enabled("trace");

    let mut module = ObjectModule::new(builder);

    let (mut state, size_hint) = GState::load_data(&args[0], args.hash()).unwrap_or_default();

    state.do_stacktrace = stacktrace;
    let mut context = GContext::default();

    if let Err(e) = MTParser::new(&mut state, &mut context).parse(&args[0]) {
        return Err((Some(state), GEKind::MTError(e).into()));
    }

    let order = std::mem::take(&mut state.module_order);

    let mut used_strings = EntitySet::<AnonString>::with_capacity(state.anon_strings.len());
    let mut used_functions = EntitySet::<Fun>::with_capacity(state.funs.len());
    let mut used_types = EntitySet::<Ty>::with_capacity(state.types.len());

    for &module in &order {
        let module = &state.modules[module];
        if module.clean {
            for &fun in module.used_functions() {
                used_functions.insert(fun);
            }
            for &ty in module.used_types() {
                used_types.insert(ty);
            }
            for &string in module.used_strings() {
                used_strings.insert(string);
            }
        }
    }

    state.remove_garbage(&used_strings);
    state.remove_garbage(&used_functions);
    state.t_state.remove_garbage(&used_types);

    if let Err(e) = Generator::new(&mut module, &mut state, &mut context, false)
        .generate(&order) {
        return Err((Some(state), e));
    }

    state.save_data(&args[0], args.hash(), Some(size_hint)).unwrap();

    Ok((module.finish().emit().unwrap(), context.lines_of_code))
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
            writeln!(f, "{}", TokenDisplay::new(state, &self.error.token))?;
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
            GEKind::IoError(message, err) => {
                writeln!(f, "{}: {}", message, err)?;
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
    IoError(&'static str, std::io::Error),
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
    println!("gen-test");
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