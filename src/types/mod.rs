//! Module defines a type parser. It transforms types into a Tree that can be later traversed
//! when generating code.
use crate::ast::{self, Ast, CallConv, Vis};
use crate::lexer::{
    self, token, DisplayError, ErrorDisplay, ErrorDisplayState, LexerBase, LineData, Span, Token,
};
use crate::modules::{self, Mod, TreeStorage, BUILTIN_MODULE, ScopeManager, Item, Ty, Const};
use crate::util::sdbm::ID;
use crate::util::Size;
use cranelift::codegen::ir::types::Type;
use cranelift::codegen::ir::Signature as CrSignature;
use cranelift::codegen::ir::{types::*, AbiParam, ArgumentPurpose};
use cranelift::codegen::isa::TargetIsa;
use cranelift::codegen::packed_option::PackedOption;
use cranelift::entity::{packed_option::ReservedValue, EntityRef};
use cranelift::entity::{EntityList, ListPool, PoolMap, PrimaryMap};
use quick_proc::{QuickEnumGets, QuickSer, RealQuickSer};
use std::fmt::Write;
use std::ops::{Deref, DerefMut};
use std::str::Chars;

type Result<T = ()> = std::result::Result<T, Error>;

/// This message is used in multiple places, thus the constant.
pub const VISIBILITY_MESSAGE: &str = concat!(
    "removing 'priv' in case of different module (but same package) or adding",
    " 'pub' in case of different package can help",
);

/// There is a limit to how deep compiler is willing to instantiate a type.
/// Otherwise, user could encounter weird compiler freezes.
pub const MAX_TYPE_INSTANTIATION_DEPTH: usize = 1000;

/// Another extension that handles type parsing on parsed ast. Its important to note
#[derive(Debug, Clone, Default)]
pub struct Ctx {
    ctx: modules::Ctx,
    unresolved: Vec<(Ty, usize)>,
    resolved: Vec<Ty>,

    module: Mod,

    enum_slices: ListPool<EnumVariant>,
    enum_variants: PrimaryMap<EnumVariant, EnumVariantEnt>,
    constants: PoolMap<Const, ConstEnt>,
    constant_slices: ListPool<Const>,
    types: PoolMap<Ty, TyEnt>,
    type_slices: ListPool<Ty>,
    fields: PoolMap<Field, FieldEnt>,
    field_slices: ListPool<Field>,
    type_cycle_map: Vec<(bool, bool)>,
}

impl Ctx {
    /// Computes types which ast is loaded in context and adds them to `module`.
    pub fn compute_types(&mut self, module: Mod) -> Result {
        if module == BUILTIN_MODULE {
            self.add_builtin_types();
        }
        self.module = module;
        self.collect(module)?;
        self.connect()?;
        self.calc_sizes()?;
        Ok(())
    }

    /// Parses Type expression and returns the entity. This can instantiate new types.
    pub fn parse_type(&mut self, module: Mod, ast: Ast) -> Result<Ty> {
        self.module = module;
        let ast_data = self.take_ast_data(module);
        let result = self.ty(&ast_data, module, ast, 0)?;
        self.put_ast_data(module, ast_data);
        self.connect()?;
        self.calc_sizes()?;
        Ok(result)
    }

    /// Calculates size of all new types.
    fn calc_sizes(&mut self) -> Result {
        let mut lookup = std::mem::take(&mut self.type_cycle_map);
        let mut resolved = std::mem::take(&mut self.resolved);
        let mut ordering = self.temp_vec();
        let mut cycle_stack = self.temp_vec();
        lookup.resize(self.types.len(), (false, false));

        for ty in resolved.drain(..) {
            if lookup[ty.index()].0 {
                continue;
            }

            if let Some(cycle) =
                self.detect_cycles(ty, &mut cycle_stack, &mut lookup, Some(&mut ordering))
            {
                return Err(Error::new(
                    error::Kind::InfiniteSize(cycle),
                    Token::default(),
                ));
            }

            for ty in ordering.drain(..) {
                self.calc_size(ty)?;
            }
        }

        self.resolved = resolved;
        self.type_cycle_map = lookup;

        Ok(())
    }

    /// Calculates size of the type, assuming all dependant types are calculated.
    fn calc_size(&mut self, ty: Ty) -> Result {
        let ty_ent = &mut self.types[ty];
        match ty_ent.kind {
            ty::Kind::Structure(kind, fields) => {
                let mut size = Size::ZERO;
                let align = fields
                    .as_slice(&self.field_slices)
                    .iter()
                    .map(|&field| self.types[self.fields[field].ty].align)
                    .max()
                    .unwrap_or(Size::ZERO);

                if align != Size::ZERO {
                    match kind {
                        StructureKind::Struct | StructureKind::Tuple => {
                            let calc = move |offset: Size| {
                                let temp = Size::new(
                                    offset.s32() & (align.s32() - 1),
                                    offset.s64() & (align.s64() - 1),
                                );
                                let add = (temp != Size::ZERO) as u32;
                                Size::new(
                                    align.s32() * add - temp.s32(),
                                    align.s64() * add - temp.s64(),
                                )
                            };

                            for &field in fields.as_slice(&self.field_slices) {
                                size = size.add(calc(size));
                                let field = &mut self.fields[field];
                                field.offset = size;
                                size = size.add(self.types[field.ty].size);
                            }

                            size = size.add(calc(size));
                        }
                        StructureKind::Union => {
                            size = fields
                                .as_slice(&self.field_slices)
                                .iter()
                                .map(|&field| self.types[self.fields[field].ty].size)
                                .max()
                                .unwrap_or(Size::ZERO);
                        }
                    }
                }

                let ty_ent = &mut self.types[ty];
                ty_ent.align = align;
                ty_ent.size = size;
            }
            ty::Kind::Array(element, size) => {
                let element_size = self.types[element].size;
                self.types[ty].size = Size::new(size, size).mul(element_size);
            }
            ty::Kind::Enumeration(_)
            | ty::Kind::Pointer(..)
            | ty::Kind::Builtin(..)
            | ty::Kind::FunPointer(..) => (),

            ty::Kind::Constant(_) | ty::Kind::Generic(_) | ty::Kind::Unresolved(_) => {
                unreachable!("{:?}", ty_ent.kind)
            }
        }

        Ok(())
    }

    /// Connects all collected types with their dependency. Not all types have dependency
    /// so they can be handled wile collecting.
    fn connect(&mut self) -> Result {
        while let Some((id, depth)) = self.unresolved.pop() {
            if depth > MAX_TYPE_INSTANTIATION_DEPTH {
                return Err(Error::new(
                    error::Kind::InstantiationDepthExceeded,
                    self.types[id].hint.clone(),
                ));
            }

            let TyEnt { module, kind, .. } = self.types[id].clone();

            let ast_data = self.take_ast_data(module);

            match kind {
                ty::Kind::Unresolved(ast) => {
                    self.connect_type(&ast_data, module, id, ast, depth)?
                }
                kind => unreachable!("{:?}", kind),
            }

            self.put_ast_data(module, ast_data);

            self.resolved.push(id);
        }
        Ok(())
    }

    /// Connects given type, using `ast_data` as source of ast. For more practical parsing
    /// ast_data should be first taken from `module` and passed to the method by reference.
    /// `depth` is used to detect infinite type instantiation.
    fn connect_type(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        id: Ty,
        ast: Ast,
        depth: usize,
    ) -> Result {
        match ast_data.kind(ast) {
            ast::Kind::Struct(_) => {
                self.connect_structure(ast_data, module, id, ast, StructureKind::Struct, depth)?;
            }
            ast::Kind::Union(_) => {
                self.connect_structure(ast_data, module, id, ast, StructureKind::Union, depth)?;
            }
            kind => unreachable!("{:?}", kind),
        }

        Ok(())
    }

    /// Connects structure type. Refer to [`Self::connect_type`] for argument documentation. Kind of the structure type
    /// will be simply saved inside resulting type.
    fn connect_structure(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        id: Ty,
        ast: Ast,
        kind: StructureKind,
        depth: usize,
    ) -> Result {
        let mut fields = self.temp_vec();
        let mut params = self.temp_vec();
        let mut shadowed = self.temp_vec();
        let header = ast_data.son(ast, 0);
        let sons = ast_data.sons(header);

        params.extend_from_slice(self.type_slice(self.types[id].params));

        if ast_data.kind(header) == ast::Kind::Instantiation {
            if params.len() != sons.len() {
                return Err(Error::new(
                    error::Kind::WrongInstantiationArgAmount(params.len() - 1, sons.len() - 1),
                    self.types[id].hint.clone(),
                ));
            }
            for (&param, &son) in params.iter().zip(sons.iter()) {
                let id = self.hash_token(ast_data.token(son));

                let shadow = self.add_temporary_item(module, id, Item::Ty(param));
                shadowed.push((id, shadow));
            }
        }

        let body = ast_data.son(ast, 1);
        if body != Ast::reserved_value() {
            let sons = ast_data.sons(body);
            for &son in sons {
                let (kind, sons, token) = ast_data.ent(son).parts();
                let field_line_len = ast_data.len(sons);
                let type_ast = ast_data.get(sons, field_line_len - 1);
                let (vis, embedded) = match &kind {
                    &ast::Kind::StructField(vis, embedded) => (vis, embedded),
                    _ => unreachable!("{:?}", kind),
                };
                let ty = self.ty(ast_data, module, type_ast, depth)?;
                let hint = token;
                for &field in &ast_data.slice(sons)[..field_line_len - 1] {
                    let id = self.hash_token(ast_data.token(field));
                    let field = FieldEnt {
                        embedded,
                        vis,
                        id,
                        offset: Size::ZERO,
                        ty,
                        hint: hint.clone(),
                    };

                    fields.push(self.fields.push(field));
                }
            }
        }

        for (id, ty) in shadowed.drain(..) {
            match ty {
                Some(item) => self.add_temporary_item(module, id, item),
                None => self.remove_temporary_item(module, id),
            };
        }

        self.types[id].kind = ty::Kind::Structure(
            kind, 
            EntityList::from_slice(fields.as_slice(), &mut self.field_slices),
        );

        Ok(())
    }

    /// Returns type for given ast expression. `ast_data` fir from `module`, `ast` is entity from `ast_data`
    /// and `depth` is used to detect infinite type instantiation.
    pub fn ty(&mut self, ast_data: &ast::Data, module: Mod, ast: Ast, depth: usize) -> Result<Ty> {
        let (kind, sons, token) = ast_data.ent(ast).parts();
        let ty = match kind {
            ast::Kind::Ident => self.simple_type(ast_data, module, None, ast, token),
            ast::Kind::Path => {
                let module_name = ast_data.get(sons, 0);
                let name = ast_data.get(sons, 1);
                self.simple_type(ast_data, module, Some(module_name), name, token)
            }
            ast::Kind::Instantiation => self.instance(ast_data, module, ast, depth),
            ast::Kind::Ref(mutable) => self.pointer(ast_data, module, ast, depth, mutable),
            ast::Kind::Array => self.array(ast_data, module, ast, depth),
            ast::Kind::FunHeader(..) => self.function_pointer(ast_data, module, ast, depth),
            ast::Kind::Tuple => self.tuple(ast_data, module, ast, depth),
            _ => self.constant(ast_data, module, ast),
        }?;

        let TyEnt { vis, module, .. } = self.types[ty];

        if !self.ctx.can_access(module, module, vis) {
            return Err(Error::new(error::Kind::VisibilityViolation, token));
        }

        Ok(ty)
    }

    pub fn tuple(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<Ty> {
        let mut fields = self.temp_vec();
        let sons = ast_data.sons(ast);
        for &ty in sons {
            fields.push(self.ty(ast_data, module, ty, depth)?);
        }

        let ty = self.tuple_of(fields.as_slice());

        Ok(ty)
    }

    pub fn function_pointer(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<Ty> {
        let mut args = self.temp_vec();
        let kind = ast_data.kind(ast);
        let sons = ast_data.sons(ast);

        for &arg in &sons[1..sons.len() - 1] {
            let ty = self.ty(ast_data, module, arg, depth)?;
            args.push(ty);
        }

        let ret = sons[sons.len() - 1];
        let ret = if ret != Ast::reserved_value() {
            let ty = self.ty(ast_data, module, ret, depth)?;
            PackedOption::from(ty)
        } else {
            PackedOption::default()
        };

        let call_conv = match kind {
            ast::Kind::FunHeader(_, _, call_conv) => call_conv,
            _ => unreachable!("{:?}", kind),
        };

        let sig = Signature {
            args: EntityList::from_slice(args.as_slice(), &mut self.type_slices),
            ret,
            call_conv,
        };

        let id = self.function_type_of(module, sig);

        Ok(id)
    }

    pub fn array(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<Ty> {
        let element = ast_data.son(ast, 0);
        let length_ast = ast_data.son(ast, 1);
        let token = ast_data.token(length_ast);

        let element = self.ty(ast_data, module, element, depth)?;
        let length = self.ty(ast_data, module, length_ast, depth)?;
        let length = match self.types[length].kind {
            ty::Kind::Constant(constant) => match self.constants[constant].kind {
                constant::Kind::Int(int, _) => int,
                _ => return Err(Error::new(error::Kind::ExpectedIntConstant, token)),
            },
            _ => return Err(Error::new(error::Kind::ExpectedIntConstant, token)),
        };

        Ok(self.array_of(element, length as usize))
    }

    pub fn constant(&mut self, ast_data: &ast::Data, module: Mod, ast: Ast) -> Result<Ty> {
        let mut new_constants = self.temp_vec();
        let constant = self.fold_const(module, ast_data, ast, ID(0), &mut new_constants)?;
        self.ctx.extend_temp_items(
            new_constants
                .drain(..)
                .map(|constant| Item::Const(constant))
        );
        Ok(self.constant_of(module, constant))
    }

    pub fn pointer(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        ast: Ast,
        depth: usize,
        mutable: bool,
    ) -> Result<Ty> {
        let ty = ast_data.son(ast, 0);
        let ty = self.ty(ast_data, module, ty, depth)?;
        let ty = self.pointer_of(ty, mutable);
        Ok(ty)
    }

    pub fn instance(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        ast: Ast,
        depth: usize,
    ) -> Result<Ty> {
        let ident = ast_data.son(ast, 0);
        let (kind, sons, token) = ast_data.ent(ident).parts();
        let ty = match kind {
            ast::Kind::Ident => self.simple_type(ast_data, module, None, ident, token)?,
            ast::Kind::Path => {
                let module_name = ast_data.get(sons, 0);
                let name = ast_data.get(sons, 1);
                self.simple_type(ast_data, module, Some(module_name), name, token)?
            }
            _ => unreachable!("{:?}", kind),
        };

        let TyEnt {
            vis,
            name,
            attrs,
            module: original_module,
            id: ty_id,
            ..
        } = self.types[ty];

        let mut params = self.temp_vec();
        let sons = ast_data.sons(ast);

        params.push(ty);

        let mut id = ty_id;
        for &ty in &sons[1..] {
            let ty = self.ty(ast_data, module, ty, depth)?;
            id = id.add(self.types[ty].id);
            params.push(ty);
        }

        if let Some(id) = self.find_computed_type(self.module, id) {
            return Ok(id);
        }

        let ty_ent = &self.types[ty];

        let ast = match ty_ent.kind {
            ty::Kind::Generic(ast) => ast,
            _ => {
                return Err(Error::new(
                    error::Kind::InstancingNonGeneric(ty_ent.hint.clone()),
                    token,
                ))
            }
        };

        let type_ent = TyEnt {
            id,
            module: original_module,
            vis,
            params: EntityList::from_slice(params.as_slice(), &mut self.type_slices),
            kind: ty::Kind::Unresolved(ast),
            name,
            hint: token,
            attrs,
            size: Size::ZERO,
            align: Size::ZERO,
        };

        let ty = self.add_type(self.module, type_ent);

        self.unresolved.push((ty, depth));

        Ok(ty)
    }

    pub fn simple_type(
        &mut self,
        ast_data: &ast::Data,
        module: Mod,
        target: Option<Ast>,
        name: Ast,
        token: Token,
    ) -> Result<Ty> {
        let mut id = self.hash_token(ast_data.token(name));

        if let Some(target) = target {
            let token = ast_data.token(target);
            let module = self.find_dep(module, token)
                .ok_or(Error::new(error::Kind::UnknownModule, token))?;
            id = id.add(self.module_id(module));
        }

        self.find_type(module, id, token).map_err(Into::into)
    }

    pub fn collect(&mut self, module: Mod) -> Result<()> {
        let mut temp = self.ctx.temp_vec();
        let ast_data = self.take_ast_data(module);

        println!("Collecting types for module {:?}", module);

        for &(type_ast, attrs) in self.ctx.types().as_slice() {
            let (kind, sons, _) = ast_data.ent(type_ast).parts();
            match kind {
                ast::Kind::Enum(vis) => {
                    let ident = ast_data.slice(sons)[0];
                    let variants = ast_data.get(sons, 1);
                    let variants = if !variants.is_reserved_value() {
                        temp.clear();
                        for &var in ast_data.sons(variants) {
                            temp.push(self.enum_variants.push(EnumVariantEnt {
                                id: self.hash_token(ast_data.token(var)),
                            }));
                        }
                        EntityList::from_slice(temp.as_slice(), &mut self.enum_slices)
                    } else {
                        EntityList::new()
                    };

                    let ident = ast_data.token(ident);
                    let id = self.hash_token(ident);

                    let kind = ty::Kind::Enumeration(variants);
                    let datatype = TyEnt {
                        vis,
                        id,
                        module,
                        kind,
                        name: ident.span(),
                        attrs,
                        hint: ident,

                        ..Default::default()
                    };

                    self.add_type(module, datatype);
                }
                ast::Kind::Struct(vis) | ast::Kind::Union(vis) => {
                    let ident = ast_data.get(sons, 0);
                    let ident_ent = ast_data.ent(ident);
                    let (ident, kind) = if ident_ent.kind() == ast::Kind::Ident {
                        (ident_ent, ty::Kind::Unresolved(type_ast))
                    } else if ident_ent.kind() == ast::Kind::Instantiation {
                        (
                            ast_data.get_ent(ident_ent.sons(), 0),
                            ty::Kind::Generic(type_ast),
                        )
                    } else {
                        return Err(Error::new(
                            error::Kind::UnexpectedAst(String::from("expected struct identifier")),
                            ident_ent.token(),
                        ));
                    };

                    let id = self.hash_token(ident.token());
                    let datatype = TyEnt {
                        vis,
                        id,
                        module,
                        kind,
                        name: ident.span(),
                        attrs,
                        hint: ident.token(),

                        ..Default::default()
                    };

                    let id = self.add_type(module, datatype);

                    if let ty::Kind::Unresolved(_) = &self.types[id].kind {
                        self.unresolved.push((id, 0));
                    }
                }
                kind => unreachable!("{:?}", kind),
            }
        }

        self.put_ast_data(module, ast_data);

        Ok(())
    }

    pub fn tuple_of(&mut self, types: &[Ty]) -> Ty {
        let mut filed_name = String::with_capacity(2);
        let mut fields = Vec::with_capacity(types.len());
        let mut id = ID::new("()");
        let mut best_module = Mod::reserved_value();
        for (i, &ty) in types.iter().enumerate() {
            let TyEnt {
                id: ty_id, module, ..
            } = self.types[ty];
            if module != BUILTIN_MODULE && module.index() < best_module.index() {
                best_module = module;
            }
            id = id.add(ty_id);
            writeln!(filed_name, "f{}", i).unwrap();
            let field = FieldEnt {
                id: ID::new(&filed_name),
                ty,

                embedded: false,
                vis: Vis::Public,
                offset: Size::ZERO,
                hint: Token::default(),
            };
            fields.push(self.fields.push(field));
            filed_name.clear();
        }

        if best_module.is_reserved_value() {
            best_module = BUILTIN_MODULE;
        }

        if let Some(ty) = self.find_computed_type(best_module, id) {
            return ty;
        }

        let ty_ent = TyEnt {
            id,
            module: BUILTIN_MODULE,
            vis: Vis::Public,
            kind: ty::Kind::Structure(
                StructureKind::Tuple, 
                EntityList::from_slice(fields.as_slice(), &mut self.field_slices)
            ),

            ..Default::default()
        };

        self.add_type(best_module, ty_ent)
    }

    pub fn pointer_of(&mut self, ty: Ty, mutable: bool) -> Ty {
        let TyEnt { module, id, .. } = self.types[ty];
        let name = if mutable { "&var " } else { "&" };
        let id = ID::new(name).add(id);

        if let Some(ty) = self.find_computed_type(module, id) {
            return ty;
        }

        let size = Size::POINTER;

        let pointer_type = TyEnt {
            id,
            kind: ty::Kind::Pointer(ty, mutable),
            module,
            size,
            align: size,

            ..Default::default()
        };

        self.add_type(module, pointer_type)
    }

    pub fn array_of(&mut self, element: Ty, length: usize) -> Ty {
        let TyEnt {
            id,
            module,
            size,
            align,
            vis,
            ..
        } = self.types[element];

        let id = ID::new("[]").add(id).add(ID(length as u64));

        if let Some(ty) = self.find_computed_type(module, id) {
            return ty;
        }

        let ty_ent = TyEnt {
            id,
            vis,
            module,
            kind: ty::Kind::Array(element, length as u32),
            size: size.mul(Size::new(length as u32, length as u32)),
            align,

            ..Default::default()
        };

        self.add_type(module, ty_ent)
    }

    pub fn constant_of(&mut self, source_module: Mod, constant: Const) -> Ty {
        let id = self.constants[constant].kind.hash(self);

        if let Some(ty) = self.find_computed_type(source_module, id) {
            return ty;
        }

        let ty_ent = TyEnt {
            id,
            vis: Vis::Public,
            kind: ty::Kind::Constant(constant),
            module: BUILTIN_MODULE,

            ..Default::default()
        };

        self.add_type(source_module, ty_ent)
    }

    /// Creates a function pointer type of given `sig`. `module` is the module where signature
    /// has ist argument slice stored.
    pub fn function_type_of(&mut self, module: Mod, sig: Signature) -> Ty {
        let mut id = ID::new("fun").add(ID(
            unsafe { std::mem::transmute::<_, u8>(sig.call_conv) } as u64
        ));

        let mut best_module = Mod::reserved_value();

        for &arg in self.type_slice(sig.args) {
            let TyEnt {
                id: ty_id, module, ..
            } = self.types[arg];
            id = id.add(ty_id);
            if module != BUILTIN_MODULE && module.index() < best_module.index() {
                best_module = module;
            }
        }

        if sig.ret.is_some() {
            let TyEnt {
                id: ty_id, module, ..
            } = self.types[sig.ret.unwrap()];
            id = id.add(ID::new("->")).add(ty_id);
            if module != BUILTIN_MODULE && module.index() < best_module.index() {
                best_module = module;
            }
        }

        if best_module.is_reserved_value() {
            best_module = BUILTIN_MODULE;
        }

        if let Some(ty) = self.find_computed_type(best_module, id) {
            return ty;
        }

        let size = Size::POINTER;
        let type_ent = TyEnt {
            kind: ty::Kind::FunPointer(sig),
            id,
            module,
            vis: Vis::None,
            size,
            align: size,

            ..Default::default()
        };

        self.add_type(best_module, type_ent)
    }

    pub fn find_computed_type(&mut self, source_module: Mod, id: ID) -> Option<Ty> {
        if let Some(ty) = self.get_item_unchecked(source_module, id) {
            if let Item::Ty(ty) = ty {
                return Some(ty);
            } else {
                panic!("Expected type, found {:?}", ty);
            }
        }

        None
    }

    pub fn pointer_base(&self, ty: Ty) -> Option<Ty> {
        if let ty::Kind::Pointer(base, _) = self.types[ty].kind {
            Some(base)
        } else {
            None
        }
    }

    pub fn pointer_mutability(&self, ty: Ty) -> bool {
        if let ty::Kind::Pointer(_, mutability) = self.types[ty].kind {
            mutability
        } else {
            false
        }
    }

    pub fn base_of(&self, ty: Ty) -> Ty {
        if let ty::Kind::Array(..) = self.types[ty].kind {
            return ARRAY_TY;
        }

        self.type_slice(self.types[ty].params)
            .first()
            .cloned()
            .unwrap_or(ty)
    }

    pub fn add_type(&mut self, source_module: Mod, ent: TyEnt) -> Ty {
        let id = ent.id;
        let ty = self.types.push(ent);
        let item = Item::Ty(ty);
        if source_module == self.module {
            self.add_temp_item(item);
        } else {
            self.extend_module_items(source_module, &[item]);
            let shadow = self.add_temporary_item(source_module, id, item);
            debug_assert!(shadow.is_none());
        }
        ty
    }

    pub fn push_type(&mut self, list: &mut EntityList<Ty>, ty: Ty) {
        list.push(ty, &mut self.type_slices);
    }

    pub fn type_slice(&self, list: EntityList<Ty>) -> &[Ty] {
        list.as_slice(&self.type_slices)
    }

    pub fn fold_const(
        &mut self,
        module: Mod,
        ast_data: &ast::Data,
        ast: Ast,
        id: ID,
        new_constants: &mut Vec<Const>,
    ) -> Result<Const> {
        let mut garbage = self.temp_vec();
        let constant =
            self.fold_const_low(module, ast_data, ast, new_constants, &mut garbage, true)?;
        self.constants[constant].id = id;

        new_constants.push(constant);

        for &garbage in garbage.iter() {
            let value = self.constants[garbage].kind;
            if let constant::Kind::Array(mut values) = value {
                values.clear(&mut self.constant_slices);
            }
            self.constants.remove(garbage);
        }

        Ok(constant)
    }

    pub fn fold_const_low(
        &mut self,
        module: Mod,
        ast_data: &ast::Data,
        ast: Ast,
        new_constants: &mut Vec<Const>,
        garbage: &mut Vec<Const>,
        is_root: bool,
    ) -> Result<Const> {
        let (kind, sons, token) = ast_data.ent(ast).parts();
        let sons = ast_data.slice(sons);
        match kind {
            ast::Kind::Index => {
                let header = self.fold_const_low(
                    module,
                    ast_data,
                    sons[0],
                    new_constants,
                    garbage,
                    is_root,
                )?;
                let accessor = self.fold_const_low(
                    module,
                    ast_data,
                    sons[1],
                    new_constants,
                    garbage,
                    is_root,
                )?;

                let accessed = match (self.constants[header].kind, self.constants[accessor].kind) {
                    (constant::Kind::Array(elements), constant::Kind::Int(value, _)) => elements
                        .get(value as usize, &self.constant_slices)
                        .ok_or_else(|| Error::new(error::Kind::IndexOutOfBounds, token))?,
                    (constant::Kind::Array(elements), constant::Kind::Uint(value, _)) => elements
                        .get(value as usize, &self.constant_slices)
                        .ok_or_else(|| Error::new(error::Kind::IndexOutOfBounds, token))?,
                    _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                };

                Ok(accessed)
            }
            ast::Kind::Binary => {
                let a =
                    self.fold_const_low(module, ast_data, sons[1], new_constants, garbage, false)?;
                let b =
                    self.fold_const_low(module, ast_data, sons[2], new_constants, garbage, false)?;
                let op = self.display_token(ast_data.token(sons[0]));
                let new = match (self.constants[a].kind, self.constants[b].kind) {
                    (constant::Kind::Int(a, base_a), constant::Kind::Int(b, base_b)) => {
                        if matches!(op, "==" | "!=" | "<" | ">" | "<=" | ">=") {
                            constant::Kind::Bool(match op {
                                "==" => a == b,
                                "!=" => a != b,
                                "<" => a < b,
                                ">" => a > b,
                                "<=" => a <= b,
                                ">=" => a >= b,
                                _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                            })
                        } else {
                            constant::Kind::Int(
                                match op {
                                    "+" => a + b,
                                    "-" => a - b,
                                    "*" => a * b,
                                    "/" => a / b,
                                    "%" => a % b,
                                    "<<" => a << b,
                                    ">>" => a >> b,
                                    "&" => a & b,
                                    "|" => a | b,
                                    "^" => a ^ b,
                                    "max" => a.max(b),
                                    "min" => a.min(b),
                                    _ => {
                                        return Err(Error::new(
                                            error::Kind::UnsupportedConst,
                                            token,
                                        ))
                                    }
                                },
                                base_a.max(base_b),
                            )
                        }
                    }
                    (constant::Kind::Uint(a, base_a), constant::Kind::Uint(b, base_b)) => {
                        if matches!(op, "==" | "!=" | "<" | ">" | "<=" | ">=") {
                            constant::Kind::Bool(match op {
                                "==" => a == b,
                                "!=" => a != b,
                                "<" => a < b,
                                ">" => a > b,
                                "<=" => a <= b,
                                ">=" => a >= b,
                                _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                            })
                        } else {
                            constant::Kind::Uint(
                                match op {
                                    "+" => a + b,
                                    "-" => a - b,
                                    "*" => a * b,
                                    "/" => a / b,
                                    "%" => a % b,
                                    "<<" => a << b,
                                    ">>" => a >> b,
                                    "&" => a & b,
                                    "|" => a | b,
                                    "^" => a ^ b,
                                    "max" => a.max(b),
                                    "min" => a.min(b),
                                    _ => {
                                        return Err(Error::new(
                                            error::Kind::UnsupportedConst,
                                            token,
                                        ))
                                    }
                                },
                                base_a.max(base_b),
                            )
                        }
                    }
                    (constant::Kind::Float(a, base_a), constant::Kind::Float(b, base_b)) => {
                        if matches!(op, "==" | "!=" | "<" | ">" | "<=" | ">=") {
                            constant::Kind::Bool(match op {
                                "==" => a == b,
                                "!=" => a != b,
                                "<" => a < b,
                                ">" => a > b,
                                "<=" => a <= b,
                                ">=" => a >= b,
                                _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                            })
                        } else {
                            constant::Kind::Float(
                                match op {
                                    "+" => a + b,
                                    "-" => a - b,
                                    "*" => a * b,
                                    "/" => a / b,
                                    "%" => a % b,
                                    "max" => a.max(b),
                                    "min" => a.min(b),
                                    _ => {
                                        return Err(Error::new(
                                            error::Kind::UnsupportedConst,
                                            token,
                                        ))
                                    }
                                },
                                base_a.max(base_b),
                            )
                        }
                    }
                    _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                };

                let constant = self.constants.push(ConstEnt {
                    kind: new,
                    module,

                    ..Default::default()
                });
                if !is_root {
                    garbage.push(constant);
                }
                Ok(constant)
            }

            ast::Kind::Unary => {
                let constant =
                    self.fold_const_low(module, ast_data, sons[1], new_constants, garbage, false)?;
                let op = self.display_token(ast_data.token(sons[0]));
                let new = match self.constants[constant].kind {
                    constant::Kind::Int(value, base) => constant::Kind::Int(
                        match op {
                            "-" => -value,
                            "!" => !value,
                            "++" => value + 1,
                            "--" => value - 1,
                            "abs" => value.abs(),
                            _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                        },
                        base,
                    ),
                    constant::Kind::Uint(value, base) => constant::Kind::Uint(
                        match op {
                            "!" => !value,
                            "++" => value + 1,
                            "--" => value - 1,
                            _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                        },
                        base,
                    ),
                    constant::Kind::Float(value, base) => constant::Kind::Float(
                        match op {
                            "-" => -value,
                            "abs" => value.abs(),
                            _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                        },
                        base,
                    ),
                    constant::Kind::Bool(value) => constant::Kind::Bool(match op {
                        "!" => !value,
                        _ => return Err(Error::new(error::Kind::UnsupportedConst, token)),
                    }),
                    constant::Kind::Str(_) | constant::Kind::Array(_) => {
                        return Err(Error::new(error::Kind::UnsupportedConst, token))
                    }
                };

                let constant = self.constants.push(ConstEnt {
                    kind: new,
                    module,

                    ..Default::default()
                });
                if !is_root {
                    garbage.push(constant);
                }
                Ok(constant)
            }
            ast::Kind::Array => {
                let mut list = EntityList::new();
                for &son in sons.iter() {
                    let constant =
                        self.fold_const_low(module, ast_data, son, new_constants, garbage, false)?;
                    if is_root {
                        new_constants.push(constant);
                    } else {
                        garbage.push(constant);
                    }
                    list.push(constant, &mut self.constant_slices);
                }
                let constant = self.constants.push(ConstEnt {
                    kind:  constant::Kind::Array(list),
                    module,

                    ..Default::default()
                });
                if !is_root {
                    garbage.push(constant);
                }
                return Ok(constant);
            }
            ast::Kind::Path => {
                let hash = sons[1..]
                    .iter()
                    .fold(None, |acc: Option<ID>, &e| {
                        let hash = self.hash_token(ast_data.token(e));
                        acc.map(|h| h.add(hash)).or(Some(hash))
                    })
                    .unwrap();

                self.find_const(module, hash, token)
            }
            ast::Kind::Ident => {
                let hash = self.hash_token(token);
                self.find_const(module, hash, token)
            }
            ast::Kind::Lit => {
                let constant = constant::Kind::from_token(self, token);
                let constant = self.constants.push(ConstEnt {
                    kind: constant,
                    module,

                    ..Default::default()
                });
                if !is_root {
                    garbage.push(constant);
                }
                Ok(constant)
            }
            _ => Err(Error::new(error::Kind::UnsupportedConst, token)),
        }
    }

    pub fn find_const(&self, module: Mod, hash: ID, token: Token) -> Result<Const> {
        let item = self.find_item(module, hash, token).map_err(Into::into)?;
        if let Item::Const(constant) = item {
            Ok(constant)
        } else {
            Err(Error::new(error::Kind::NotConst, token))
        }
    }

    pub fn find_type(&self, module: Mod, hash: ID, token: Token) -> Result<Ty> {
        let item = self.find_item(module, hash, token).map_err(Into::into)?;
        if let Item::Ty(ty) = item {
            Ok(ty)
        } else {
            Err(Error::new(error::Kind::NotType, token))
        }
    }

    pub fn type_name(&self, ty: Ty) -> Span {
        self.types[ty].name
    }
}

impl Deref for Ctx {
    type Target = modules::Ctx;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for Ctx {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

impl<'a> TreeStorage<Ty> for Ctx {
    fn node_dep(&self, id: Ty, idx: usize) -> Ty {
        let node = &self.types[id];
        match &node.kind {
            ty::Kind::Structure(_, fields) => self.fields[fields.as_slice(&self.field_slices)[idx]].ty,
            ty::Kind::Array(ty, _) => *ty,
            ty::Kind::FunPointer(fun) => {
                if idx == self.type_slice(fun.args).len() {
                    fun.ret.unwrap()
                } else {
                    self.type_slice(fun.args)[idx]
                }
            }
            _ => unreachable!("{:?}", node.kind),
        }
    }

    fn node_len(&self, id: Ty) -> usize {
        let node = &self.types[id];

        match &node.kind {
            ty::Kind::Builtin(_) | ty::Kind::Pointer(..) | ty::Kind::Enumeration(_) => 0,
            ty::Kind::FunPointer(fun) => {
                self.type_slice(fun.args).len() + fun.ret.is_some() as usize
            }
            ty::Kind::Array(..) => 1,
            ty::Kind::Structure(_, fields) => fields.len(&self.field_slices),
            ty::Kind::Generic(_) | ty::Kind::Unresolved(_) | ty::Kind::Constant(_) => {
                unreachable!("{:?}", node)
            }
        }
    }

    fn len(&self) -> usize {
        self.types.len()
    }
}

crate::impl_entity!(EnumVariant);

#[derive(Debug, Clone, Default)]
pub struct EnumVariantEnt {
    id: ID,
}

impl EnumVariantEnt {
    pub fn id(&self) -> ID {
        self.id
    }
}

#[derive(Debug, Clone, Default)]
pub struct ModCtx {}

impl Signature {
    pub fn to_cr_signature(&self, state: &Ctx, isa: &dyn TargetIsa, target: &mut CrSignature) {
        target.call_conv = self.call_conv.to_cr_call_conv(isa);
        target.params.extend(
            state
                .type_slice(self.args)
                .iter()
                .map(|&ty| AbiParam::new(state.types[ty].to_cr_type(isa))),
        );
        if self.ret.is_some() {
            let ret = self.ret.unwrap();
            let ty = &state.types[ret];
            let param = if ty.on_stack(isa.pointer_type()) {
                let param = AbiParam::special(ty.to_cr_type(isa), ArgumentPurpose::StructReturn);
                target.params.push(param);
                param
            } else {
                AbiParam::new(ty.to_cr_type(isa))
            };
            target.returns.push(param);
        }
    }
}

macro_rules! define_repo {
    (
        $($const_name:ident, $name:ident, $repr:expr, $s32:expr, $s64:expr, $index:expr);+
    ) => {
        $(
            pub const $const_name: Ty = Ty($index);
        )+
        pub const ALL_BUILTIN_TYPES: &[Ty] = &[$($const_name),+];

        impl Ctx {
            pub fn add_builtin_types(&mut self) {
                let module = BUILTIN_MODULE;
                let builtin_id = self.module_id(module);

                $(
                    let name = self.builtin_span(stringify!($name));
                    let id = ID::new(stringify!($name)).add(builtin_id);
                    let type_ent = TyEnt {
                        id,
                        kind: ty::Kind::Builtin(CrTypeWr($repr)),
                        size: Size::new($s32, $s64),
                        align: Size::new($s32, $s64).min(Size::new(4, 8)),
                        module,
                        hint: Token::new(token::Kind::Ident, name.clone(), LineData::default()),
                        name,

                        ..Default::default()
                    };
                    self.add_type(module, type_ent);
                )+
            }
        }
    };
}

define_repo!(
    I8_TY, i8, I8, 1, 1, 0;
    I16_TY, i16, I16, 2, 2, 1;
    I32_TY, i32, I32, 4, 4, 2;
    I64_TY, i64, I64, 8, 8, 3;
    U8_TY, u8, I8, 1, 1, 4;
    U16_TY, u16, I16, 2, 2, 5;
    U32_TY, u32, I32, 4, 4, 6;
    U64_TY, u64, I64, 8, 8, 7;
    F32_TY, f32, F32, 4, 4, 8;
    F64_TY, f64, F64, 8, 8, 9;
    BOOL_TY, bool, B1, 1, 1, 10;
    INT_TY, int, INVALID, 4, 8, 11;
    UINT_TY, uint, INVALID, 4, 8, 12;
    ARRAY_TY, array, INVALID, 0, 0, 13
);

pub struct TypeDisplay<'a> {
    state: &'a Ctx,
    type_id: Ty,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(state: &'a Ctx, type_id: Ty) -> Self {
        Self { state, type_id }
    }
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let ty = &self.state.types[self.type_id];
        match &ty.kind {
            &ty::Kind::Pointer(id, mutable) => {
                if mutable {
                    write!(f, "&var {}", Self::new(self.state, id))
                } else {
                    write!(f, "&{}", Self::new(self.state, id))
                }
            }
            ty::Kind::Structure(..) if !ty.params.is_empty() => {
                let params = self.state.type_slice(ty.params);
                write!(f, "{}", Self::new(self.state, params[0]))?;
                write!(f, "[")?;
                write!(f, "{}", Self::new(self.state, params[1]))?;
                for param in params[2..].iter() {
                    write!(f, ", {}", Self::new(self.state, *param))?;
                }
                write!(f, "]")
            }
            ty::Kind::Builtin(_)
            | ty::Kind::Unresolved(_)
            | ty::Kind::Generic(_)
            | ty::Kind::Structure(..)
            | ty::Kind::Enumeration(_) => {
                write!(f, "{}", self.state.display(ty.name))
            }
            &ty::Kind::Constant(value) => {
                write!(f, "{}", ConstDisplay::new(self.state, value))
            }
            ty::Kind::Array(id, len) => {
                write!(f, "[{}, {}]", Self::new(self.state, *id), len)
            }
            ty::Kind::FunPointer(fun) => {
                write!(
                    f,
                    "fn({})",
                    self.state
                        .type_slice(fun.args)
                        .iter()
                        .map(|id| format!("{}", Self::new(self.state, *id)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if fun.ret.is_some() {
                    write!(f, " -> {}", Self::new(self.state, fun.ret.unwrap()))?;
                }
                Ok(())
            }
        }
    }
}

impl ErrorDisplayState<Error> for Ctx {
    fn fmt(&self, e: &Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &e.kind {
            error::Kind::VisibilityViolation => {
                write!(
                    f,
                    "visibility of the type disallows the access, {}",
                    VISIBILITY_MESSAGE
                )?;
            }
            error::Kind::InstancingNonGeneric(origin) => {
                writeln!(
                    f,
                    "instancing non-generic type, defined here:\n {}",
                    token::Display::new(&self.ctx, &origin)
                )?;
            }
            error::Kind::NotType => {
                write!(f, "expected type")?;
            }
            error::Kind::ModuleError(error) => {
                writeln!(f, "{}", ErrorDisplay::new(&self.ctx, error))?;
            }
            error::Kind::AstError(error) => {
                writeln!(f, "{}", ErrorDisplay::new(self.ctx.deref(), error))?;
            }
            error::Kind::UnexpectedAst(token) => {
                writeln!(f, "{}", token)?;
            }
            &error::Kind::AmbiguousType(a, b) => {
                let a = self.types[a].hint.clone();
                let b = self.types[b].hint.clone();
                writeln!(
                    f,
                    "matches\n{}\nand\n{}\nambiguity is not allowed",
                    token::Display::new(self.sources(), &a),
                    token::Display::new(self.sources(), &b)
                )?;
            }
            error::Kind::UnknownType => {
                writeln!(f, "type not defined in current scope")?;
            }
            error::Kind::NotGeneric => {
                writeln!(f, "type is not generic thus cannot be instantiated")?;
            }
            error::Kind::UnknownModule => {
                writeln!(f, "module not defined in current scope")?;
            }
            error::Kind::InstantiationDepthExceeded => {
                writeln!(
                    f,
                    "instantiation depth exceeded, max is {}",
                    MAX_TYPE_INSTANTIATION_DEPTH
                )?;
            }
            error::Kind::WrongInstantiationArgAmount(actual, expected) => {
                writeln!(
                    f,
                    "wrong amount of arguments for type instantiation, expected {} but got {}",
                    expected, actual
                )?;
            }
            error::Kind::AccessingExternalPrivateType => {
                todo!()
            }
            error::Kind::AccessingFilePrivateType => {
                todo!()
            }
            error::Kind::InfiniteSize(cycle) => {
                writeln!(f, "infinite size detected, cycle:")?;
                for ty in cycle.iter() {
                    writeln!(f, "  {}", TypeDisplay::new(self, *ty))?;
                }
            }
            error::Kind::Redefinition(other) => {
                writeln!(
                    f,
                    "is redefinition of\n{}",
                    token::Display::new(self.sources(), other)
                )?;
            }

            error::Kind::ExpectedIntConstant => {
                writeln!(f, "expected positive integer constant")?;
            }
            error::Kind::InvalidCallConv => {
                CallConv::error(f)?;
            }
            error::Kind::UnsupportedConst => {
                writeln!(
                    f,
                    "unsupported constant operation, use 'let' instead of 'const' if possible"
                )?;
            }
            error::Kind::NotConst => {
                writeln!(f, "value of this expression is not known at compile time")?;
            }
            error::Kind::Undefined => {
                writeln!(f, "expression points to undefined value")?;
            }
            error::Kind::IndexOutOfBounds => {
                writeln!(f, "index out of bounds inside a constant expression")?;
            }
        }

        Ok(())
    }

    fn sources(&self) -> &crate::lexer::Ctx {
        self.ctx.sources()
    }
}

#[derive(Debug)]
pub struct Error {
    kind: error::Kind,
    token: Token,
}

impl Error {
    pub fn new(kind: error::Kind, token: Token) -> Self {
        Self { kind, token }
    }
}

impl DisplayError for Error {
    fn token(&self) -> Token {
        self.token
    }
}

impl Into<Error> for modules::Error {
    fn into(self) -> Error {
        Error::new(error::Kind::ModuleError(self), Token::default())
    }
}

mod error {
    use super::*;

    #[derive(Debug)]
    pub enum Kind {
        NotType,
        InvalidCallConv,
        VisibilityViolation,
        InstancingNonGeneric(Token),
        AstError(ast::Error),
        ModuleError(modules::Error),
        UnexpectedAst(String),
        AmbiguousType(Ty, Ty),
        UnknownType,
        NotGeneric,
        UnknownModule,
        InstantiationDepthExceeded,
        WrongInstantiationArgAmount(usize, usize),
        AccessingExternalPrivateType,
        AccessingFilePrivateType,
        InfiniteSize(Vec<Ty>),
        Redefinition(Token),
        ExpectedIntConstant,
        UnsupportedConst,
        NotConst,
        Undefined,
        IndexOutOfBounds,
    }
}

#[derive(Debug, Clone, QuickSer, Default)]
pub struct TyEnt {
    pub id: ID,
    pub module: Mod,
    pub vis: Vis,
    pub params: EntityList<Ty>,
    pub kind: ty::Kind,
    pub name: Span,
    pub hint: Token,
    pub attrs: Ast,
    pub size: Size,
    pub align: Size,
}

impl TyEnt {
    pub fn to_cr_type(&self, isa: &dyn TargetIsa) -> Type {
        match &self.kind {
            ty::Kind::Pointer(..)
            | ty::Kind::Array(..)
            | ty::Kind::Structure(..)
            | ty::Kind::FunPointer(_) => isa.pointer_type(),
            ty::Kind::Enumeration(_) => I8, //temporary solution
            &ty::Kind::Builtin(ty) => ty.0,
            ty::Kind::Generic(_) | ty::Kind::Constant(_) | ty::Kind::Unresolved(_) => {
                unreachable!()
            }
        }
    }

    pub fn on_stack(&self, ptr_ty: Type) -> bool {
        self.size.pick(ptr_ty == I32) > ptr_ty.bytes() as u32
    }

    fn item_data(&self) -> (Mod, Token, ID) {
        (self.module, self.hint, self.id)
    }
}

mod ty {
    use super::*;

    #[derive(Debug, Clone, QuickEnumGets, Copy, RealQuickSer)]
    pub enum Kind {
        Builtin(CrTypeWr),
        Pointer(Ty, bool),
        Enumeration(EntityList<EnumVariant>),
        Array(Ty, u32),
        FunPointer(Signature),
        Constant(Const),
        Structure(StructureKind, EntityList<Field>),
        Generic(Ast),
        Unresolved(Ast),
    }

    impl Default for ty::Kind {
        fn default() -> Self {
            ty::Kind::Builtin(CrTypeWr(INVALID))
        }
    }
}

crate::impl_wrapper!(CrTypeWr, Type);

#[derive(Debug, Clone, Copy, Default, RealQuickSer)]
pub struct Signature {
    pub call_conv: CallConv,
    pub args: EntityList<Ty>,
    pub ret: PackedOption<Ty>,
}

crate::impl_entity!(Field);

#[derive(Debug, Clone, Default, Copy, RealQuickSer)]
pub struct FieldEnt {
    pub embedded: bool,
    pub vis: Vis,
    pub id: ID,
    pub offset: Size,
    pub ty: Ty,
    pub hint: Token,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RealQuickSer)]
pub enum StructureKind {
    Struct,
    Union,
    Tuple,
}

#[derive(Debug, Clone, Copy, RealQuickSer, Default)]
pub struct ConstEnt {
    id: ID,
    module: Mod,
    vis: Vis,
    hint: Token,
    kind: constant::Kind,
}

impl ConstEnt {
    pub fn item_data(&self) -> (Mod, Token, ID) {
        (self.module, self.hint, self.id)
    }

    pub fn vis(&self) -> Vis {
        self.vis
    }
}

mod constant {
    use super::*;

    #[derive(Clone, Debug, Copy)]
    pub enum Kind {
        Int(i64, u8),
        Uint(u64, u8),
        Float(f64, u8),
        Bool(bool),
        Str(Span),
        Array(EntityList<Const>),
    }
    
    impl Kind {
        pub fn from_token(ctx: &mut Ctx, token: Token) -> Self {
            let mut chars = ctx.display(token.span()).chars();
            match token.kind() {
                token::Kind::Int(_) | token::Kind::Uint(_) | token::Kind::Float(_) => {
                    match chars.number().unwrap() {
                        lexer::Number::Int(num, base) => Self::Int(num, base),
                        lexer::Number::Uint(num, base) => Self::Uint(num, base),
                        lexer::Number::Float(num, base) => Self::Float(num, base),
                    }
                }
                token::Kind::Bool(value) => Self::Bool(value),
                token::Kind::String => {
                    let mut result = String::with_capacity(chars.as_str().len());
                    chars.string(Some(&mut result));
                    let result = ctx.builtin_span(&result);
                    Self::Str(result)
                }
                token::Kind::Char => Self::Uint(chars.character() as u64, 32),
                _ => unreachable!(),
            }
        }
    
        pub fn hash(self, ctx: &Ctx) -> ID {
            match self {
                Kind::Int(value, base) => ID(0).add(ID(value as u64)).add(ID(base as u64)),
                Kind::Uint(value, base) => ID(1).add(ID(value as u64)).add(ID(base as u64)),
                Kind::Float(value, base) => ID(2).add(ID(value.to_bits())).add(ID(base as u64)),
                Kind::Bool(value) => ID(3).add(ID(value as u64)),
                Kind::Str(span) => ID(4).add(ctx.hash_span(span)),
                Kind::Array(elements) => {
                    let mut id = ID(5);
                    for &element in elements.as_slice(&ctx.constant_slices) {
                        id = id.add(ctx.constants[element].kind.hash(ctx));
                    }
                    id
                }
            }
        }
    }
}


pub struct ConstDisplay<'a> {
    ctx: &'a Ctx,
    constant: Const,
}

impl<'a> ConstDisplay<'a> {
    pub fn new(ctx: &'a Ctx, constant: Const) -> Self {
        Self { ctx, constant }
    }
}

impl std::fmt::Display for ConstDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.ctx.constants[self.constant].kind {
            constant::Kind::Bool(b) => write!(f, "{}", b),
            constant::Kind::Int(i, base) => write!(f, "{}i{}", i, base),
            constant::Kind::Uint(i, base) => write!(f, "{}u{}", i, base),
            constant::Kind::Float(float, base) => write!(f, "{}f{}", float, base),
            constant::Kind::Str(s) => write!(f, "\"{}\"", self.ctx.display(s)),
            constant::Kind::Array(elements) => {
                write!(f, "[")?;
                for (i, &element) in elements
                    .as_slice(&self.ctx.constant_slices)
                    .iter()
                    .enumerate()
                {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", Self::new(self.ctx, element))?;
                }
                write!(f, "]")
            }
        }
    }
}

impl LexerBase for Chars<'_> {
    fn next(&mut self) -> Option<char> {
        Iterator::next(self)
    }

    fn peek(&self) -> Option<char> {
        Iterator::next(&mut self.clone())
    }
}

impl Default for constant::Kind {
    fn default() -> Self {
        Self::Bool(false)
    }
}

impl ScopeManager for Ctx {
    fn get_item_unchecked(&self, module: Mod, id: ID) -> Option<Item> {
        self.ctx.get_item_unchecked(module, id)
    }

    fn module_id(&self, module: Mod) -> ID {
        self.ctx.module_id(module)
    }

    fn module_dependency(&self, module: Mod) -> &[(ID, Span, Mod)] {
        self.ctx.module_dependency(module)
    }

    fn module_scope(&mut self, module: Mod) -> &mut crate::util::storage::Map<Item> {
        self.ctx.module_scope(module)
    }

    fn item_data(&self, item: Item) -> (Mod, Token, ID) {
        match item {
            Item::Ty(ty) => self.types[ty].item_data(),
            Item::Const(constant) => self.constants[constant].item_data(),
            Item::Local(_) |
            Item::Global(_) |
            Item::Fun(_) |
            Item::Collision => unreachable!(),
        }
    }
}

pub fn test() {
    const PATH: &str = "src/types/test_project";

    let mut ctx = Ctx::default();
    let mut item_buffer = vec![];

    let order = ctx
        .compute_module_tree(PATH)
        .map_err(|e| panic!("{}", ErrorDisplay::new(&ctx.ctx, &e)))
        .unwrap();

    for &module in &order {
        ctx.collect_imported_items(module, &mut item_buffer);

        ctx.extend_scope(module, &item_buffer)
            .map_err(|e| panic!("{}", ErrorDisplay::new(&ctx.ctx, &e)))
            .unwrap();

        
        
        loop {
            let more = ctx
                .compute_ast(module)
                .map_err(|e| panic!("{}", ErrorDisplay::new(&ctx.ctx, &e)))
                .unwrap();

            ctx.compute_types(module)
                .map_err(|e| panic!("\n{}", ErrorDisplay::new(&ctx, &e)))
                .unwrap();
            
            item_buffer.clear();
            ctx.dump_temp_items(&mut item_buffer);
            ctx.extend_module_items(module, &item_buffer);
            ctx.extend_scope(module, &item_buffer)
                .map_err(|e| panic!("{}", ErrorDisplay::new(&ctx.ctx, &e)))
                .unwrap();
                
            if !more {
                break;
            }
        }

        ctx.clear_after_module();
    }
}
