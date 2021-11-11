use cranelift_codegen::{
    binemit::{NullStackMapSink, NullTrapSink},
    settings,
};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::process::Command;

use super::*;

pub type Result<T> = std::result::Result<T, GenError>;

pub fn compile(root_file: &str) -> Result<()> {
    let obj_file = generate_obj_file(root_file)?;

    let name = root_file
        .split("/")
        .last()
        .unwrap()
        .split(".")
        .next()
        .unwrap();

    let obj_name = format!("{}.o", name);

    std::fs::write(&obj_name, obj_file).map_err(Into::into)?;

    Command::new("cc")
        .args(&["-o", &format!("{}.exe", name), &obj_name])
        .status()
        .map_err(Into::into)?;

    Ok(())
}

pub fn generate_obj_file(root_file: &str) -> Result<Vec<u8>> {
    let mut context = Generator::new().generate(root_file).map_err(Into::into)?;

    let settings = settings::builder();
    let flags = settings::Flags::new(settings);
    let isa = cranelift_native::builder().unwrap().finish(flags);

    let builder =
        ObjectBuilder::new(isa, "all", cranelift_module::default_libcall_names()).unwrap();
    let mut main_module = ObjectModule::new(builder);
    let mut ctx = cranelift_codegen::Context::new();
    for module in &mut context.modules {
        for mut function in module
            .borrow_mut()
            .functions
            .iter_mut()
            .map(|f| f.borrow_mut())
        {
            let signature = function.signature.to_signature();
            let fun_id = main_module
                .declare_function(function.signature.name.deref(), Linkage::Export, &signature)
                .unwrap();
            ctx.func = std::mem::take(&mut function.function).unwrap();
            main_module
                .define_function(
                    fun_id,
                    &mut ctx,
                    &mut NullTrapSink::default(),
                    &mut NullStackMapSink {},
                )
                .unwrap();
        }
    }

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
}

impl Into<GenError> for GEKind {
    fn into(self) -> GenError {
        GenError {
            kine: self,
            token: None,
        }
    }
}
