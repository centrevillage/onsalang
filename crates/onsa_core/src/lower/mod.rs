//! Lowering (T3-3) and monomorphization (T3-4): from the typed AST of
//! `onsa_sema` to Core. Entry: [`lower`].
//!
//! Roots are every non-generic function, method, `test` and `const` of the
//! user package. Generic functions are instantiated on demand from the
//! `Instance` tables of the bodies that call them, deduplicated by
//! `(def, generic args)` and named `name__F32` / `sum__4`. Types are
//! instantiated the same way (`Ring__F32__4`); `Option[T]` / `Result[T, E]`
//! become ordinary enums (`Option__F32`).
//!
//! Flows are lowered by [`flow`] (T3-5): every flow of the user package is a
//! root, and a flow is also lowered on demand when a body refers to one of
//! its members (`voice.init`, `voice.State`).

mod body;
mod eq;
pub mod flow;
pub mod moves;

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span};
use onsa_sema::def::{DefKind, Fields, GenericKind};
use onsa_sema::ty::{BuiltinTy, Len, Ty as STy, TyId};
use onsa_sema::{Analysis, DefId, Package};

use crate::ir::*;

/// A generic argument after monomorphization.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Const(u32),
}

pub(crate) struct Fail {
    pub code: Code,
    pub span: Span,
    pub msg: String,
}

pub(crate) type R<T> = Result<T, Fail>;

pub(crate) fn unsupported(span: Span, what: &str) -> Fail {
    Fail { code: Code::E0200, span, msg: format!("this version does not lower {what} to Core") }
}

pub(crate) struct Lowerer<'a> {
    pub pkg: &'a Package,
    pub a: &'a Analysis,
    pub m: Module,
    /// Package index of the user package in `flat`.
    pub user_pkg: usize,
    fn_ids: HashMap<(DefId, Vec<GenericArg>), FnId>,
    worklist: Vec<(DefId, Vec<GenericArg>, FnId)>,
    type_ids: HashMap<(DefId, Vec<GenericArg>), TypeId>,
    named_types: HashMap<String, TypeId>,
    const_ids: HashMap<DefId, ConstId>,
    pub(crate) eq_fns: HashMap<Ty, FnId>,
    messages: HashMap<String, MsgId>,
    pub(crate) flow_fns: HashMap<DefId, flow::FlowFns>,
    pub(crate) flows_in_progress: HashSet<DefId>,
    /// `bulk_threshold` of the target (spec §12.4); `None`: everything fast.
    pub bulk_threshold: Option<u32>,
    /// Pointer width of the target in bytes (the bulk slot, `Span`s), T4-5.
    pub ptr_size: u32,
}

/// Options of a lowering.
#[derive(Debug, Clone)]
pub struct LowerOptions {
    /// Arrays of at least this many bytes in a flow state go to the bulk region (§12.4).
    pub bulk_threshold: Option<u32>,
    /// Pointer width of the target in bytes (8 on the reference host).
    pub ptr_size: u32,
}

impl Default for LowerOptions {
    fn default() -> Self {
        LowerOptions { bulk_threshold: None, ptr_size: crate::layout::PTR_SIZE }
    }
}

/// Lower the user package (and what it reaches in `std`) to Core.
pub fn lower(pkg: &Package, a: &Analysis) -> Result<Module, Vec<Diagnostic>> {
    lower_with(pkg, a, &LowerOptions::default())
}

/// [`lower`] with options (the target's `bulk_threshold`).
pub fn lower_with(pkg: &Package, a: &Analysis, opts: &LowerOptions) -> Result<Module, Vec<Diagnostic>> {
    let user_pkg = onsa_sema::flatten(pkg).len() - 1;
    let mut lw = Lowerer {
        pkg,
        a,
        m: Module::default(),
        user_pkg,
        fn_ids: HashMap::new(),
        worklist: Vec::new(),
        type_ids: HashMap::new(),
        named_types: HashMap::new(),
        const_ids: HashMap::new(),
        eq_fns: HashMap::new(),
        messages: HashMap::new(),
        flow_fns: HashMap::new(),
        flows_in_progress: HashSet::new(),
        bulk_threshold: opts.bulk_threshold,
        ptr_size: opts.ptr_size,
    };
    let mut diags = Vec::new();
    // Roots: non-generic items of the user package, in definition order.
    for (i, def) in a.defs.iter().enumerate() {
        let id = DefId(i as u32);
        if a.modules.get(def.module).pkg != user_pkg {
            continue;
        }
        match &def.kind {
            DefKind::Fn(f) if f.body.is_some() && lw.all_generics(id).is_empty() => {
                lw.fn_id(id, Vec::new());
            }
            DefKind::Test { .. } => {
                lw.fn_id(id, Vec::new());
            }
            DefKind::Flow(_) => {
                if let Err(e) = lw.ensure_flow(id) {
                    diags.push(lw.diagnostic(e));
                }
            }
            DefKind::Const(c) if c.value.is_some() && def.owner.is_none_or(|o| a.def(o).generics().is_empty()) => {
                if let Err(e) = lw.const_id(id) {
                    diags.push(lw.diagnostic(e));
                }
            }
            _ => {}
        }
    }
    while let Some((def, args, fid)) = lw.worklist.pop() {
        if let Err(e) = lw.lower_fn(def, &args, fid) {
            diags.push(lw.diagnostic(e));
        }
    }
    if !diags.is_empty() {
        diags.sort_by_key(|d| (d.span.file, d.span.start));
        return Err(diags);
    }
    let mut module = lw.m;
    module.moves = moves::collect(&module);
    if cfg!(debug_assertions)
        && let Err(e) = crate::verify::verify(&module)
    {
        panic!("{e}\n{}", crate::dump::dump(&module));
    }
    Ok(module)
}

impl<'a> Lowerer<'a> {
    pub(crate) fn diagnostic(&self, f: Fail) -> Diagnostic {
        Diagnostic::new(f.code, f.span, f.msg)
    }

    pub(crate) fn msg(&mut self, text: &str) -> MsgId {
        if let Some(&id) = self.messages.get(text) {
            return id;
        }
        let id = MsgId(self.m.messages.len() as u32);
        self.m.messages.push(text.to_string());
        self.messages.insert(text.to_string(), id);
        id
    }

    /// Generic parameters of a def. Methods already list their impl's
    /// generics first (`sig.rs` lowers them that way).
    pub(crate) fn all_generics(&self, id: DefId) -> Vec<GenericKind> {
        self.a.def(id).generics().iter().map(|g| g.kind.clone()).collect()
    }

    pub(crate) fn is_std_def(&self, id: DefId) -> bool {
        self.a.modules.get(self.a.def(id).module).pkg != self.user_pkg
    }

    /// `dsp.voice.wrap01`, `std.math.exp`, `methods.Point.new`, `voice.voice.init`.
    pub(crate) fn qual_name(&self, id: DefId) -> String {
        let def = self.a.def(id);
        let mut parts = Vec::new();
        let info = self.a.modules.get(def.module);
        if self.is_std_def(id) {
            parts.push(self.a.modules.names[info.pkg].clone());
        }
        if !info.path.is_empty() {
            parts.push(info.path.clone());
        }
        if let Some(o) = def.owner {
            match &self.a.def(o).kind {
                DefKind::Impl(i) => {
                    if let STy::Named(d, _) = self.a.types.get(i.self_ty) {
                        parts.push(self.a.def(*d).name.clone());
                    } else {
                        parts.push(self.a.display_type(i.self_ty));
                    }
                }
                _ => parts.push(self.a.def(o).name.clone()),
            }
        }
        match &def.kind {
            DefKind::Test { name, .. } => {
                parts.clear();
                parts.push("test".into());
                parts.push(name.clone());
            }
            _ => parts.push(def.name.clone()),
        }
        parts.join(".")
    }

    pub(crate) fn mangle(&self, t: &Ty) -> String {
        match t {
            Ty::Int(k) => k.name().to_string(),
            Ty::Float(k) => k.name().to_string(),
            Ty::Bool => "Bool".into(),
            Ty::Char => "Char".into(),
            Ty::Unit => "Unit".into(),
            Ty::Array(e, n) => format!("A{n}_{}", self.mangle(e)),
            Ty::Tuple(ts) => {
                format!("T{}_{}", ts.len(), ts.iter().map(|t| self.mangle(t)).collect::<Vec<_>>().join("_"))
            }
            Ty::Struct(id) | Ty::Enum(id) => self.m.ty(*id).name.replace('.', "_"),
            Ty::Span(e) => format!("Span_{}", self.mangle(e)),
            Ty::Buf(e) => format!("Buf_{}", self.mangle(e)),
            Ty::FnPtr(_) => "Fn".into(),
        }
    }

    fn mangle_args(&self, args: &[GenericArg]) -> String {
        args.iter()
            .map(|a| match a {
                GenericArg::Ty(t) => format!("__{}", self.mangle(t)),
                GenericArg::Const(n) => format!("__{n}"),
            })
            .collect()
    }

    // ------------------------------------------------------------ types

    /// Convert a sema type under the generic arguments of the enclosing instance.
    pub(crate) fn core_ty(&mut self, t: TyId, args: &[GenericArg], span: Span) -> R<Ty> {
        let st = self.a.types.get(t).clone();
        Ok(match st {
            STy::Int(k) => Ty::Int(k),
            STy::Float(k) => Ty::Float(k),
            STy::Bool => Ty::Bool,
            STy::Char => Ty::Char,
            STy::Unit => Ty::Unit,
            STy::Array(e, len) => {
                let n = match len {
                    Len::Const(n) => n,
                    Len::Param(i) => match args.get(i as usize) {
                        Some(GenericArg::Const(n)) => *n,
                        _ => return Err(internal(span, "unbound const parameter")),
                    },
                    Len::Var(_) => return Err(internal(span, "unresolved array length")),
                };
                Ty::Array(Box::new(self.core_ty(e, args, span)?), n)
            }
            STy::Tuple(ts) => {
                let mut out = Vec::new();
                for t in ts {
                    out.push(self.core_ty(t, args, span)?);
                }
                Ty::Tuple(out)
            }
            STy::Named(d, targs) => {
                let def = self.a.def(d);
                match &def.kind {
                    DefKind::Alias(inner) => return self.core_ty(*inner, args, span),
                    DefKind::Struct(_) | DefKind::Enum(_) => {
                        let gargs = self.generic_args(&targs, args, span)?;
                        let id = self.type_id(d, gargs, span)?;
                        if matches!(def.kind, DefKind::Struct(_)) { Ty::Struct(id) } else { Ty::Enum(id) }
                    }
                    _ => return Err(internal(span, "type refers to a non-type def")),
                }
            }
            STy::Builtin(b, targs) => match b {
                BuiltinTy::Option => {
                    let t = self.core_ty(targs[0], args, span)?;
                    Ty::Enum(self.option_type(t))
                }
                BuiltinTy::Result => {
                    let t = self.core_ty(targs[0], args, span)?;
                    let e = self.core_ty(targs[1], args, span)?;
                    Ty::Enum(self.result_type(t, e))
                }
                BuiltinTy::Span => Ty::Span(Box::new(self.core_ty(targs[0], args, span)?)),
                BuiltinTy::Buf => Ty::Buf(Box::new(self.core_ty(targs[0], args, span)?)),
                BuiltinTy::Ptr => return Err(unsupported(span, "`Ptr` (FFI)")),
                BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                    return Err(unsupported(span, &format!("the Shared type `{}`", b.name())));
                }
            },
            STy::Fn(f) => {
                let mut params = Vec::new();
                for (m, t) in &f.params {
                    params.push((core_mode(*m), self.core_ty(*t, args, span)?));
                }
                let ret = self.core_ty(f.ret, args, span)?;
                Ty::FnPtr(Box::new(FnSig { rt: f.rt, params, ret }))
            }
            STy::Param(i) => match args.get(i as usize) {
                Some(GenericArg::Ty(t)) => t.clone(),
                _ => return Err(internal(span, "unbound type parameter")),
            },
            STy::Rate(_, inner) => return self.core_ty(inner, args, span),
            STy::ConstVal(_) => return Err(internal(span, "const argument in type position")),
            STy::Var(_) | STy::Error => return Err(internal(span, "unresolved type")),
        })
    }

    pub(crate) fn generic_args(&mut self, targs: &[TyId], args: &[GenericArg], span: Span) -> R<Vec<GenericArg>> {
        let mut out = Vec::new();
        for &t in targs {
            match self.a.types.get(t) {
                STy::ConstVal(n) => out.push(GenericArg::Const(*n)),
                STy::Param(i) => match args.get(*i as usize) {
                    Some(g) => out.push(g.clone()),
                    None => return Err(internal(span, "unbound generic argument")),
                },
                _ => out.push(GenericArg::Ty(self.core_ty(t, args, span)?)),
            }
        }
        Ok(out)
    }

    /// Core type of a struct / enum def instance.
    pub(crate) fn type_id(&mut self, d: DefId, gargs: Vec<GenericArg>, span: Span) -> R<TypeId> {
        if let Some(&id) = self.type_ids.get(&(d, gargs.clone())) {
            return Ok(id);
        }
        let name = format!("{}{}", self.qual_name(d), self.mangle_args(&gargs));
        let id = TypeId(self.m.types.len() as u32);
        self.m.types.push(TypeDef { name, kind: TypeDefKind::Opaque });
        self.type_ids.insert((d, gargs.clone()), id);
        let def = self.a.def(d).clone();
        let kind = match &def.kind {
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => {
                    let mut fields = Vec::new();
                    for f in fs {
                        fields.push((f.name.clone(), self.core_ty(f.ty, &gargs, span)?));
                    }
                    TypeDefKind::Struct { fields }
                }
                Fields::Tuple(t) => TypeDefKind::Struct { fields: vec![("0".into(), self.core_ty(*t, &gargs, span)?)] },
                Fields::Opaque => TypeDefKind::Opaque,
            },
            DefKind::Enum(e) => {
                let mut variants = Vec::new();
                for v in &e.variants {
                    let mut tys = Vec::new();
                    for &t in &v.fields {
                        tys.push(self.core_ty(t, &gargs, span)?);
                    }
                    variants.push((v.name.clone(), tys));
                }
                TypeDefKind::Enum { variants }
            }
            _ => return Err(internal(span, "not a type def")),
        };
        self.m.types[id.0 as usize].kind = kind;
        Ok(id)
    }

    fn named_enum(&mut self, name: String, variants: Vec<(String, Vec<Ty>)>) -> TypeId {
        if let Some(&id) = self.named_types.get(&name) {
            return id;
        }
        let id = TypeId(self.m.types.len() as u32);
        self.m.types.push(TypeDef { name: name.clone(), kind: TypeDefKind::Enum { variants } });
        self.named_types.insert(name, id);
        id
    }

    /// `Option[T]` as an enum `None | Some(T)` (tags 0 / 1, as in sema).
    pub(crate) fn option_type(&mut self, t: Ty) -> TypeId {
        let name = format!("Option__{}", self.mangle(&t));
        self.named_enum(name, vec![("None".into(), vec![]), ("Some".into(), vec![t])])
    }

    /// `Result[T, E]` as an enum `Ok(T) | Err(E)` (tags 0 / 1).
    pub(crate) fn result_type(&mut self, t: Ty, e: Ty) -> TypeId {
        let name = format!("Result__{}__{}", self.mangle(&t), self.mangle(&e));
        self.named_enum(name, vec![("Ok".into(), vec![t]), ("Err".into(), vec![e])])
    }

    pub(crate) fn enum_variants(&self, id: TypeId) -> Vec<(String, Vec<Ty>)> {
        match &self.m.ty(id).kind {
            TypeDefKind::Enum { variants } => variants.clone(),
            _ => Vec::new(),
        }
    }

    pub(crate) fn struct_fields(&self, id: TypeId) -> Vec<(String, Ty)> {
        match &self.m.ty(id).kind {
            TypeDefKind::Struct { fields } => fields.clone(),
            _ => Vec::new(),
        }
    }

    // ------------------------------------------------------------ functions

    /// The Core function for a def instance; queues it for lowering on first use.
    pub(crate) fn fn_id(&mut self, d: DefId, args: Vec<GenericArg>) -> FnId {
        if let Some(&id) = self.fn_ids.get(&(d, args.clone())) {
            return id;
        }
        let id = FnId(self.m.fns.len() as u32);
        let name = format!("{}{}", self.qual_name(d), self.mangle_args(&args));
        let span = self.a.def(d).span;
        self.m.fns.push(FnDef {
            name,
            params: Vec::new(),
            ret: Ty::Unit,
            sret: false,
            rt: false,
            locals: Vec::new(),
            body: None,
            span,
        });
        self.fn_ids.insert((d, args.clone()), id);
        self.worklist.push((d, args, id));
        id
    }

    pub(crate) fn const_id(&mut self, d: DefId) -> R<ConstId> {
        if let Some(&id) = self.const_ids.get(&d) {
            return Ok(id);
        }
        let def = self.a.def(d).clone();
        let DefKind::Const(c) = &def.kind else { return Err(internal(def.span, "not a const")) };
        let ty = self.core_ty(c.ty, &[], def.span)?;
        let init = match self.a.const_values.get(&d) {
            Some(v) => self.const_value_expr(v, &ty, def.span)?,
            None => {
                // Evaluated by the interpreter at build time (T3-9): lower the initializer.
                let Some(body) = self.a.bodies.get(&d) else {
                    return Err(unsupported(def.span, "a `const` whose initializer was not checked"));
                };
                let Some(v) = c.value else { return Err(internal(def.span, "const without initializer")) };
                let mut cx = body::FnCx::new(self, d, Vec::new(), body, ty.clone())?;
                let e = body::lower_expr(self, &mut cx, v)?;
                if !cx.locals.is_empty() {
                    return Err(unsupported(def.span, "a `const` initializer with local bindings"));
                }
                e
            }
        };
        let id = ConstId(self.m.consts.len() as u32);
        self.m.consts.push(ConstDef { name: self.qual_name(d), ty, init });
        self.const_ids.insert(d, id);
        Ok(id)
    }

    fn const_value_expr(&mut self, v: &onsa_sema::ConstValue, ty: &Ty, span: Span) -> R<Expr> {
        use onsa_sema::ConstValue as C;
        let kind = match (v, ty) {
            (C::Int(n), Ty::Int(_)) => ExprKind::Lit(Lit::Int(*n)),
            (C::Float(f), Ty::Float(FloatKind::F32)) => ExprKind::Lit(Lit::F32(*f as f32)),
            (C::Float(f), Ty::Float(FloatKind::F64)) => ExprKind::Lit(Lit::F64(*f)),
            (C::Bool(b), Ty::Bool) => ExprKind::Lit(Lit::Bool(*b)),
            (C::Char(c), Ty::Char) => ExprKind::Lit(Lit::Char(*c)),
            (C::Unit, Ty::Unit) => ExprKind::Lit(Lit::Unit),
            (C::Array(xs), Ty::Array(et, _)) => {
                let mut out = Vec::new();
                for x in xs {
                    out.push(self.const_value_expr(x, et, span)?);
                }
                ExprKind::Array(out)
            }
            (C::Tuple(xs), Ty::Tuple(ts)) => {
                let mut out = Vec::new();
                for (x, t) in xs.iter().zip(ts) {
                    out.push(self.const_value_expr(x, t, span)?);
                }
                ExprKind::Tuple(out)
            }
            (C::Struct(xs), Ty::Struct(id)) => {
                let fields = self.struct_fields(*id);
                let mut out = Vec::new();
                for (x, (_, t)) in xs.iter().zip(&fields) {
                    out.push(self.const_value_expr(x, t, span)?);
                }
                ExprKind::Struct { ty: *id, fields: out }
            }
            _ => return Err(internal(span, "const value does not match its type")),
        };
        Ok(Expr::new(ty.clone(), span, kind))
    }

    fn lower_fn(&mut self, d: DefId, args: &[GenericArg], fid: FnId) -> R<()> {
        let def = self.a.def(d).clone();
        match &def.kind {
            DefKind::Fn(f) => {
                if f.flow_fn.is_some() {
                    // Generated by a flow (§11.6): lowering the flow fills every member.
                    let owner = def.owner.ok_or_else(|| internal(def.span, "flow member without an owner"))?;
                    self.ensure_flow(owner)?;
                    return Ok(());
                }
                let ret = self.core_ty(f.ret, args, def.span)?;
                if f.body.is_none() {
                    // `target`: declaration only.
                    let mut params = Vec::new();
                    let mut locals = Vec::new();
                    if let Some(m) = f.self_mode {
                        return Err(internal(def.span, format!("bodyless method with self mode {m:?}")));
                    }
                    for p in &f.params {
                        let ty = self.core_ty(p.ty, args, p.span)?;
                        let local = LocalId(locals.len() as u32);
                        locals.push(Local { name: p.name.clone(), ty: ty.clone() });
                        params.push(Param { local, mode: core_mode(p.mode), ty });
                    }
                    let fd = &mut self.m.fns[fid.0 as usize];
                    fd.params = params;
                    fd.sret = ret.is_aggregate();
                    fd.ret = ret;
                    fd.rt = f.rt;
                    fd.locals = locals;
                    return Ok(());
                }
                let Some(info) = self.a.bodies.get(&d) else {
                    return Err(internal(def.span, "function body was not checked"));
                };
                if !info.complete {
                    return Err(internal(def.span, "function body has errors"));
                }
                let mut cx = body::FnCx::new(self, d, args.to_vec(), info, ret.clone())?;
                let params = body::bind_params(self, &mut cx, d, f)?;
                let block = body::lower_fn_body(self, &mut cx, f.body.unwrap())?;
                let fd = &mut self.m.fns[fid.0 as usize];
                fd.params = params;
                fd.sret = ret.is_aggregate();
                fd.ret = ret;
                fd.rt = f.rt;
                fd.locals = cx.locals;
                fd.body = Some(block);
                Ok(())
            }
            DefKind::Test { body, .. } => {
                let Some(info) = self.a.bodies.get(&d) else {
                    return Err(internal(def.span, "test body was not checked"));
                };
                if !info.complete {
                    return Err(internal(def.span, "test body has errors"));
                }
                let mut cx = body::FnCx::new(self, d, Vec::new(), info, Ty::Unit)?;
                let block = body::lower_fn_body(self, &mut cx, *body)?;
                let fd = &mut self.m.fns[fid.0 as usize];
                fd.ret = Ty::Unit;
                fd.locals = cx.locals;
                fd.body = Some(block);
                Ok(())
            }
            _ => Err(internal(def.span, "not a function")),
        }
    }
}

pub(crate) fn core_mode(m: onsa_syntax::ast::Mode) -> Mode {
    match m {
        onsa_syntax::ast::Mode::Borrow => Mode::Borrow,
        onsa_syntax::ast::Mode::Inout => Mode::Inout,
        onsa_syntax::ast::Mode::Move => Mode::Move,
    }
}

pub(crate) fn internal(span: Span, msg: impl Into<String>) -> Fail {
    Fail { code: Code::E0200, span, msg: format!("internal lowering error: {}", msg.into()) }
}
