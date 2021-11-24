use std::ops::Deref;

use crate::ast::AKind;
use crate::util::sdbm::SdbmHashState;

use super::*;
use super::types::{TEKind, TypeError, TypeResolver, TypeResolverContext};

type Result<T> = std::result::Result<T, FunctionError>;

pub struct FunctionResolver<'a> {
    program: &'a mut Program,
    context: &'a mut FunctionResolverContext,
}

impl<'a> FunctionResolver<'a> {
    pub fn new(
        program: &'a mut Program,
        context: &'a mut FunctionResolverContext,
    ) -> Self {
        FunctionResolver {
            program,
            context,
        }
    }

    pub fn resolve(mut self) -> Result<()> {
        self.collect()?;

        Ok(())
    }

    fn collect(&mut self) -> Result<()> {
        for module in unsafe { self.program.modules.direct_ids() } {
            if !self.program.modules.is_direct_valid(module) {
                continue;
            }
            
            let mut ast = std::mem::take(&mut self.program.modules[module].ast);
            for a in ast.iter_mut() {
                match a.kind.clone() {
                    AKind::Function(visibility) => {
                        let header = &a[0];
                        match header.kind {
                            AKind::Identifier => {
                                let mut name = ID::new()
                                    .add(header.token.spam.deref())
                                    .combine(self.program.modules.direct_to_id(module));
                                let mut params = Vec::new();
                                for param_line in &a[1..a.len() - 1] {
                                    let datatype = param_line.last().unwrap();
                                    let datatype = self.resolve_datatype(module, datatype)?;
                                    name = name.combine(self.program.types.direct_to_id(datatype));
                                    for param in param_line[0..param_line.len() - 1].iter() {
                                        let name = ID::new().add(param.token.spam.deref());
                                        let mutable = param_line.kind == AKind::FunctionArgument(true);
                                        params.push(Val {
                                            name,
                                            datatype,
                                            mutable,
                                            on_stack: false,
                                        });
                                    }
                                }
                                let return_type = &a[a.len() - 1];
                                let ret = if return_type.kind == AKind::None {
                                    None
                                } else {
                                    Some(self.resolve_datatype(module, return_type)?)
                                };

                                let function_signature = NormalFunction {
                                    params,
                                    ret,
                                };

                                let token_hint = header.token.clone();

                                let function = FunctionEntity {
                                    visibility,
                                    name,
                                    module,
                                    hint_token: token_hint.clone(),
                                    kind: FKind::Normal(function_signature),
                                    ast: std::mem::take(a),
                                };

                                if let (Some(function), _) = self.program.functions.insert(name, function) {
                                    return Err(FunctionError::new(
                                        FEKind::Duplicate(function.hint_token), &token_hint));
                                }
                            }
                            AKind::Instantiation => {
                                let name = ID::new()
                                    .add(header[0].token.spam.deref())
                                    .combine(self.program.modules.direct_to_id(module));
                                
                                let function = FunctionEntity {
                                    visibility,
                                    name,
                                    module,
                                    hint_token: header.token.clone(),
                                    kind: FKind::Generic,
                                    ast: std::mem::take(a),
                                };

                                self.program.generic_functions.get_mut_or_default(name).push(function);
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => (),
                }
            }
        }

        Ok(())
    }

    fn resolve_datatype(&mut self, module: Mod, ast: &Ast) -> Result<Datatype> {
        TypeResolver::new(self.program, &mut self.context.type_resolver_context)
            .resolve_immediate(module, ast)
            .map_err(Into::into)
    }
}

#[derive(Debug, Default)]
pub struct FunctionResolverContext {
    pub type_resolver_context: TypeResolverContext,
}

impl FunctionResolverContext {
    pub fn clear(&mut self) {
        self.type_resolver_context.clear();
    }
}

#[derive(Debug)]
pub struct FunctionError {
    pub kind: FEKind,
    pub token: Token,
}

impl FunctionError {
    pub fn new(kind: FEKind, token: &Token) -> Self {
        FunctionError {
            kind,
            token: token.clone(),
        }
    }
}

#[derive(Debug)]
pub enum FEKind {
    TypeError(TEKind),
    Duplicate(Token),
}

impl Into<FunctionError> for TypeError {
    fn into(self) -> FunctionError {
        FunctionError {
            kind: FEKind::TypeError(self.kind),
            token: self.token,
        }
    }
}
