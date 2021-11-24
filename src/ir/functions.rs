/*use cranelift_codegen::isa::TargetIsa;

use crate::util::sdbm::SdbmHashState;

use super::*;
use super::types::{TEKind, TypeError, TypeResolver, TypeResolverContext};

type Result<T> = std::result::Result<T, FunctionError>;

pub struct FunctionResolver<'a> {
    isa: &'a dyn TargetIsa,
    program: &'a mut Program,
    context: &'a mut FunctionResolverContext,
}

impl<'a> FunctionResolver<'a> {
    pub fn new(
        program: &'a mut Program,
        context: &'a mut FunctionResolverContext,
        isa: &'a dyn TargetIsa
    ) -> Self {
        FunctionResolver {
            program,
            context,
            isa,
        }
    }

    pub fn resolve(mut self) -> Result<()> {
        for i in 0..self.program.mods.len() {
            self.collect(self.program.mods[i].clone())?;
        }

        Ok(())
    }

    fn collect(&mut self, mut module: Cell<Mod>) -> Result<()> {
        let mut ast = std::mem::take(&mut module.ast);
        for a in ast.iter_mut() {
            match a.kind.clone() {
                AKind::Function(visibility) => {

                    let header = &a[0];
                    let id = ID::new()
                        .add(header[0].token.spam.deref());


                    for param in &header[1..header.len()] {
                        self.resolve_datatype(module.clone(), param)?;
                    }

                }
                _ => (),
            }
        }
        module.ast = ast;

        Ok(())
    }

    fn resolve_datatype(&mut self, module: Cell<Mod>, ast: &Ast) -> Result<Datatype> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context, self.isa)
            .resolve_immediate(module, ast)
            .map_err(Into::into)
    }
}

pub struct FunctionResolverContext {
    pub type_resolver_context: TypeResolverContext,
}

impl FunctionResolverContext {
    pub fn new() -> Self {
        Self {
            type_resolver_context: TypeResolverContext::new(),
        }
    }

    pub fn clear(&mut self) {
        self.type_resolver_context.clear();
    }
}

#[derive(Debug)]
pub struct FunctionError {
    pub kind: FEKind,
    pub token: Token,
}

#[derive(Debug)]
pub enum FEKind {
    TypeError(TEKind),
}

impl Into<FunctionError> for TypeError {
    fn into(self) -> FunctionError {
        FunctionError {
            kind: FEKind::TypeError(self.kind),
            token: self.token,
        }
    }
}*/
