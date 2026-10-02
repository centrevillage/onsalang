//! Function-body checking (T2-5 .. T2-7, T2-10, T2-11): the inference of spec
//! §4.7 — statement order, unification variables, downward expected types —
//! plus generics instantiation, closures as arguments, builtin methods,
//! scopes (E0304) and `const` evaluation. Argument modes / exclusivity (T2-8)
//! and `rt` (T2-9) run after this pass over the tables in [`BodyInfo`].

use std::collections::HashMap;

use onsa_diag::{Code, Diagnostic, Fix, Span};
use onsa_syntax::ast::{
    Arg, Ast, BinOp, Block, CallKind, Expr, ExprId, ExprKind, Ident, Lit, MatchArm, Mode, OpGroup, Param, ParamName,
    PatId, PatKind, Path, StmtId, StmtKind, StrSeg, UnOp,
};

use crate::builtin;
use crate::def::{Bound, DefKind, Fields, FnDef, GenericDef, GenericKind};
use crate::exhaust::P;
use crate::infer::{Infer, LitKind, Mismatch};
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::ty::{BuiltinTy, FnTy, IntKind, Len, Ty, TyId};
use crate::{Analysis, DefId, Kind, ModId, Package, flatten};

// ---------------------------------------------------------------- tables

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalKind {
    /// A function parameter with its mode.
    Param(Mode),
    /// The `self` receiver with its mode.
    SelfParam(Mode),
    Let,
    Var,
    /// `for` variable; `moved` for `for x in move xs`.
    For {
        moved: bool,
    },
    MatchBind,
    ClosureParam(Mode),
}

#[derive(Debug, Clone)]
pub struct LocalInfo {
    pub name: String,
    pub span: Span,
    /// Resolved at the end of the body (may still contain `Ty::Param` in generic bodies).
    pub ty: TyId,
    pub kind: LocalKind,
    /// Borrow binding (§5.4): derived from a borrowed parameter, or a `for`
    /// over a place without `move`. Not enforced here.
    pub borrow: bool,
    /// `var`, `inout` parameter, `inout self`.
    pub mutable: bool,
}

/// Instantiation of a generic def at a call site (for monomorphization).
#[derive(Debug, Clone)]
pub struct Instance {
    pub def: DefId,
    /// One per generic parameter of the def (const parameters as `ConstVal`).
    pub args: Vec<TyId>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstId(pub u32);

/// What a path, field chain, or call resolved to.
#[derive(Debug, Clone)]
pub enum Target {
    Local(LocalId),
    /// A `const N` generic parameter used as a `U32` value.
    ConstParam(u32),
    /// A function item (as a value, or the callee of a `Call`).
    Fn {
        def: DefId,
        inst: Option<InstId>,
    },
    Const(DefId),
    /// A unit variant (value) or tuple variant (constructor / callee).
    Variant {
        def: DefId,
        index: u32,
    },
    /// `Some`, `None`, `Ok`, `Err`.
    Prelude(Builtin),
    /// `F32.PI`, `I32.MAX`, ...
    BuiltinConst {
        ty: TyId,
        name: String,
    },
    /// `x.m(...)` on a user type: the method def; the receiver is the callee's `base`.
    Method {
        def: DefId,
        inst: Option<InstId>,
    },
    /// A builtin method (`xs.len()`, `out.fill!(0.0)`) or associated function (`Buf.zeroed`).
    BuiltinMethod {
        recv: TyId,
        name: String,
        bang: bool,
    },
    /// A call through a function value (closure or `fn` value).
    Value,
}

/// Typed body of one function, test, or `const` initializer.
#[derive(Debug, Default, Clone)]
pub struct BodyInfo {
    /// Type of every expression, fully resolved (variables substituted).
    pub expr_types: HashMap<ExprId, TyId>,
    pub locals: Vec<LocalInfo>,
    /// Path / field-chain / call expressions → what they refer to.
    pub targets: HashMap<ExprId, Target>,
    /// `PatKind::Bind` patterns → the local they introduce.
    pub pat_locals: HashMap<PatId, LocalId>,
    pub instances: Vec<Instance>,
    /// Closure expression → outer locals it captures (by copy, §5.3).
    pub captures: HashMap<ExprId, Vec<LocalId>>,
    /// `[e; N]` expressions (the element must be Dup, §2.4; checked by T2-8).
    pub repeats: Vec<ExprId>,
    /// `false` when checking stopped at the first error (tables are partial).
    pub complete: bool,
}

// ---------------------------------------------------------------- checker

pub(crate) struct Stop;
pub(crate) type R<T> = Result<T, Stop>;

struct Scope {
    names: Vec<(String, LocalId)>,
}

/// A function or closure body being checked.
pub(crate) struct Frame {
    pub(crate) local_base: u32,
    pub(crate) ret: TyId,
    pub(crate) loop_depth: u32,
    pub(crate) captures: Vec<LocalId>,
}

pub(crate) struct Checker<'a> {
    pub(crate) a: &'a mut Analysis,
    pub(crate) ast: &'a Ast,
    pub(crate) text: &'a str,
    pub(crate) m: ModId,
    pub(crate) def: DefId,
    generics: Vec<GenericDef>,
    self_ty: Option<TyId>,
    pub(crate) infer: Infer,
    scopes: Vec<Scope>,
    pub(crate) frames: Vec<Frame>,
    pub(crate) info: BodyInfo,
    pub(crate) failed: bool,
    /// Flow mode (T3-1, `flow.rs`): set while checking a flow body.
    pub(crate) flow: Option<crate::flow::FlowCx>,
    /// `(expr, value)` of integer literals, for the range check (E0408).
    int_lits: Vec<(ExprId, u64)>,
    /// Integer literals negated by a prefix `-` (`-128` fits `I8`).
    negated: Vec<ExprId>,
    /// `-e` expressions whose operand type was a literal variable (sign checked at the end).
    neg_exprs: Vec<(ExprId, TyId)>,
    /// Float literals (E0405 when still unresolved at the end).
    float_lits: Vec<ExprId>,
    /// Or-pattern alternative being checked: names bound by the first alternative.
    or_bindings: Option<HashMap<String, LocalId>>,
    /// Typed holes (E0421): reported at the end of the body, once the type is known.
    holes: Vec<(ExprId, TyId, Vec<LocalId>)>,
}

/// Check every body of the package and its dependencies.
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let n = a.defs.len();
    for i in 0..n {
        let id = DefId(i as u32);
        let def = &a.defs[i];
        let Some(item) = def.item else { continue };
        let m = def.module;
        let info = a.modules.get(m);
        let Some(module) = flat.get(info.pkg).and_then(|p| info.module.and_then(|mi| p.modules.get(mi))) else {
            continue;
        };
        let _ = item;
        let (generics, self_ty, body, ret) = match &def.kind {
            DefKind::Fn(f) => {
                let Some(b) = f.body else { continue };
                let self_ty = def.owner.and_then(|o| match &a.defs[o.0 as usize].kind {
                    DefKind::Impl(i) => Some(i.self_ty),
                    _ => None,
                });
                (f.generics.clone(), self_ty, b, f.ret)
            }
            DefKind::Test { body, .. } => {
                let unit = a.types.unit();
                (Vec::new(), None, *body, unit)
            }
            DefKind::Const(c) => {
                let Some(v) = c.value else { continue };
                let generics = def.owner.map(|o| a.defs[o.0 as usize].generics().to_vec()).unwrap_or_default();
                let self_ty = def.owner.and_then(|o| match &a.defs[o.0 as usize].kind {
                    DefKind::Impl(i) => Some(i.self_ty),
                    _ => None,
                });
                (generics, self_ty, v, c.ty)
            }
            // Flow bodies (T3-1): the same inference, in flow mode (`flow.rs`).
            DefKind::Flow(f) => (Vec::new(), None, f.body, f.out),
            _ => continue,
        };
        // Items that already have a signature diagnostic are not checked (P-01).
        if a.diagnostics.iter().any(|d| d.span.file == module.file && def.span.contains(d.span.start)) {
            continue;
        }
        let mut ck = Checker {
            a,
            ast: &module.parsed.ast,
            text: &module.text,
            m,
            def: id,
            generics,
            self_ty,
            infer: Infer::default(),
            scopes: Vec::new(),
            frames: Vec::new(),
            info: BodyInfo::default(),
            failed: false,
            int_lits: Vec::new(),
            negated: Vec::new(),
            neg_exprs: Vec::new(),
            float_lits: Vec::new(),
            or_bindings: None,
            holes: Vec::new(),
            flow: None,
        };
        let is_const = matches!(ck.a.defs[i].kind, DefKind::Const(_));
        let is_flow = matches!(ck.a.defs[i].kind, DefKind::Flow(_));
        if is_const {
            ck.check_const(body, ret);
        } else if is_flow {
            ck.check_flow_body(body, ret);
        } else {
            ck.check_fn_body(body, ret);
        }
        let fcx = ck.flow.take();
        let info = ck.finish();
        match fcx {
            Some(fcx) => crate::flow::finish_flow(a, module, id, info, fcx),
            None => {
                a.bodies.insert(id, info);
            }
        }
    }
}

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ helpers

    pub(crate) fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    pub(crate) fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(code, span, msg).with_found(self.src(span)))
    }

    pub(crate) fn diag(&mut self, d: Diagnostic) -> Stop {
        if !self.failed {
            self.failed = true;
            self.a.diagnostics.push(d);
        }
        Stop
    }

    pub(crate) fn ty(&self, t: TyId) -> Ty {
        self.a.types.get(t).clone()
    }

    pub(crate) fn shallow(&self, t: TyId) -> TyId {
        self.infer.shallow(&self.a.types, t)
    }

    pub(crate) fn display(&mut self, t: TyId) -> String {
        let r = self.infer.resolve(&mut self.a.types, t);
        let names: Vec<String> = self.generics.iter().map(|g| g.name.clone()).collect();
        self.a.types.display(r, &|d| self.a.def(d).name.clone(), &|i| {
            names.get(i as usize).cloned().unwrap_or_else(|| format!("<{i}>"))
        })
    }

    pub(crate) fn unit(&mut self) -> TyId {
        self.a.types.unit()
    }

    pub(crate) fn bool_(&mut self) -> TyId {
        self.a.types.bool()
    }

    pub(crate) fn u32(&mut self) -> TyId {
        self.a.types.int(IntKind::U32)
    }

    pub(crate) fn fresh(&mut self) -> TyId {
        self.infer.fresh(&mut self.a.types, None)
    }

    pub(crate) fn record(&mut self, e: ExprId, t: TyId) -> TyId {
        self.info.expr_types.insert(e, t);
        t
    }

    pub(crate) fn expr(&self, e: ExprId) -> &'a Expr {
        self.ast.expr(e)
    }

    /// Unify, reporting E0401 at `span` on failure.
    pub(crate) fn unify_at(&mut self, span: Span, actual: TyId, expected: TyId) -> R<()> {
        match self.infer.unify(&mut self.a.types, actual, expected) {
            Ok(()) => Ok(()),
            Err(Mismatch::Literal) => {
                let e = self.display(expected);
                let what = match self.infer.lit_of(&self.a.types, actual) {
                    Some(LitKind::Int) => "an integer literal",
                    Some(LitKind::Float) => "a float literal",
                    None => match self.infer.lit_of(&self.a.types, expected) {
                        Some(LitKind::Int) => {
                            let shown = self.display(actual);
                            return Err(self.err(Code::E0401, span, format!("expected an integer, found `{shown}`")));
                        }
                        Some(LitKind::Float) => {
                            let shown = self.display(actual);
                            return Err(self.err(Code::E0401, span, format!("expected a float, found `{shown}`")));
                        }
                        None => "a literal",
                    },
                };
                Err(self.err(Code::E0401, span, format!("{what} cannot have type `{e}`")))
            }
            Err(Mismatch::Types) => {
                let (a, e) = (self.display(actual), self.display(expected));
                Err(self.err(Code::E0401, span, format!("expected `{e}`, found `{a}`")))
            }
        }
    }

    /// E0420: the operand's type must be known at this point (§4.7).
    pub(crate) fn known(&mut self, t: TyId, span: Span, what: &str) -> R<TyId> {
        let s = self.shallow(t);
        if matches!(self.ty(s), Ty::Var(_)) {
            return Err(self.diag(
                Diagnostic::new(
                    Code::E0420,
                    span,
                    format!("the type of this {what} must be known here; add an annotation (§4.7)"),
                )
                .with_found(self.src(span)),
            ));
        }
        Ok(s)
    }

    // ------------------------------------------------------------ scopes

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Scope { names: Vec::new() });
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn lookup_local(&mut self, name: &str) -> Option<LocalId> {
        for s in self.scopes.iter().rev() {
            if let Some((_, id)) = s.names.iter().rev().find(|(n, _)| n == name) {
                let id = *id;
                // Captured from an enclosing function (§5.3): record it.
                if let Some(f) = self.frames.last_mut()
                    && id.0 < f.local_base
                    && !f.captures.contains(&id)
                {
                    f.captures.push(id);
                }
                return Some(id);
            }
        }
        None
    }

    /// Declare a binding (E0304 when the name is already visible, §5.1).
    pub(crate) fn declare(&mut self, name: &Ident, ty: TyId, kind: LocalKind, borrow: bool) -> R<LocalId> {
        if name.name != "_" {
            let visible =
                self.scopes.iter().flat_map(|s| s.names.iter()).find(|(n, _)| *n == name.name).map(|(_, id)| *id);
            if let Some(prev) = visible {
                let prev_span = self.info.locals[prev.0 as usize].span;
                return Err(self.diag(
                    Diagnostic::new(
                        Code::E0304,
                        name.span,
                        format!("`{}` is already bound and visible here; Onsa has no shadowing (§5.1)", name.name),
                    )
                    .with_found(name.name.clone())
                    .with_note(prev_span, "first bound here"),
                ));
            }
        }
        let mutable = matches!(
            kind,
            LocalKind::Var
                | LocalKind::Param(Mode::Inout)
                | LocalKind::SelfParam(Mode::Inout)
                | LocalKind::ClosureParam(Mode::Inout)
        );
        let id = LocalId(self.info.locals.len() as u32);
        self.info.locals.push(LocalInfo { name: name.name.clone(), span: name.span, ty, kind, borrow, mutable });
        self.scopes.last_mut().expect("scope").names.push((name.name.clone(), id));
        Ok(id)
    }

    pub(crate) fn local_ty(&self, id: LocalId) -> TyId {
        self.info.locals[id.0 as usize].ty
    }

    // ------------------------------------------------------------ entry points

    fn check_fn_body(&mut self, body: ExprId, ret: TyId) {
        self.frames.push(Frame { local_base: 0, ret, loop_depth: 0, captures: Vec::new() });
        self.push_scope();
        let r = (|| -> R<()> {
            self.bind_params()?;
            let t = self.check_expr(body, Some(ret))?;
            let _ = t;
            Ok(())
        })();
        let _ = r;
        self.pop_scope();
        self.frames.pop();
    }

    fn bind_params(&mut self) -> R<()> {
        let def = self.a.defs[self.def.0 as usize].clone();
        let DefKind::Fn(f) = &def.kind else { return Ok(()) };
        let Some(item) = def.item else { return Ok(()) };
        let params: Vec<Param> = match &self.ast.item(item).kind {
            onsa_syntax::ast::ItemKind::Fn(fd) => fd.params.clone(),
            onsa_syntax::ast::ItemKind::Target(inner) => match inner.as_ref() {
                onsa_syntax::ast::ItemKind::Fn(fd) => fd.params.clone(),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let mut sig_params = f.params.iter();
        for p in &params {
            match &p.name {
                ParamName::SelfParam(span) => {
                    let Some(st) = self.self_ty else { continue };
                    let ident = Ident { name: "self".into(), span: *span };
                    self.declare(&ident, st, LocalKind::SelfParam(p.mode), false)?;
                }
                ParamName::Ident(id) => {
                    let Some(sig) = sig_params.next() else { continue };
                    let ty = sig.ty;
                    self.declare(id, ty, LocalKind::Param(p.mode), p.mode == Mode::Borrow)?;
                }
                ParamName::Wild(_) => {
                    sig_params.next();
                }
            }
        }
        Ok(())
    }

    fn check_const(&mut self, value: ExprId, ty: TyId) {
        self.frames.push(Frame { local_base: 0, ret: ty, loop_depth: 0, captures: Vec::new() });
        self.push_scope();
        let r = (|| -> R<()> {
            self.check_expr(value, Some(ty))?;
            // E0407: the result must be Copy (static Shared placement is phase 2).
            if let Some(k) = self.a.kind_of(ty)
                && k != Kind::Copy
            {
                let span = self.expr(value).span;
                let shown = self.display(ty);
                return Err(self.err(
                    Code::E0407,
                    span,
                    format!("a `const` must be Copy in this version; `{shown}` is {} (§6.6)", k.name()),
                ));
            }
            Ok(())
        })();
        let _ = r;
        self.pop_scope();
        self.frames.pop();
        if !self.failed
            && let Some(v) = crate::consteval::eval(self, value)
        {
            self.a.const_values.insert(self.def, v);
        }
    }

    /// Final checks (E0405, E0408, E0406 bounds) and resolution of the tables.
    fn finish(mut self) -> BodyInfo {
        if !self.failed {
            let mut late: Vec<Diagnostic> = Vec::new();
            // S-22 (§2.4, §4.7): an integer literal still unresolved at the end of the
            // body defaults to `I32`; float literals have no default (E0405 below).
            let i32_ = self.a.types.int(IntKind::I32);
            let mut defaulted: Vec<ExprId> = Vec::new();
            for (e, _) in self.int_lits.clone() {
                let t = self.info.expr_types[&e];
                if self.infer.lit_of(&self.a.types, t) == Some(LitKind::Int) {
                    let _ = self.infer.unify(&mut self.a.types, t, i32_);
                    defaulted.push(e);
                }
            }
            for (e, value) in self.int_lits.clone() {
                let t = self.info.expr_types[&e];
                let r = self.infer.resolve(&mut self.a.types, t);
                match self.ty(r) {
                    Ty::Int(k) => {
                        let neg = self.negated.contains(&e);
                        let v = if neg { -(value as i128) } else { value as i128 };
                        let (lo, hi) = k.range();
                        if v < lo || v > hi {
                            let span = self.expr(e).span;
                            let hint = if defaulted.contains(&e) {
                                " (the default for an unconstrained integer literal); add an annotation such as `: U32` or `: I64`"
                            } else {
                                ""
                            };
                            late.push(
                                Diagnostic::new(
                                    Code::E0408,
                                    span,
                                    format!(
                                        "literal `{}{value}` is out of range for `{}`{hint}",
                                        if neg { "-" } else { "" },
                                        k.name()
                                    ),
                                )
                                .with_found(self.src(span)),
                            );
                        }
                    }
                    Ty::Var(_) => {
                        let span = self.expr(e).span;
                        late.push(
                            Diagnostic::new(
                                Code::E0405,
                                span,
                                "the type of this integer literal cannot be determined; annotate it (§2.4)",
                            )
                            .with_found(self.src(span)),
                        );
                    }
                    _ => {}
                }
            }
            for e in self.float_lits.clone() {
                let t = self.info.expr_types[&e];
                let r = self.infer.resolve(&mut self.a.types, t);
                if matches!(self.ty(r), Ty::Var(_)) {
                    let span = self.expr(e).span;
                    late.push(
                        Diagnostic::new(
                            Code::E0405,
                            span,
                            "the type of this float literal cannot be determined; annotate it (§2.4)",
                        )
                        .with_found(self.src(span)),
                    );
                }
            }
            for (e, t) in self.neg_exprs.clone() {
                let r = self.infer.resolve(&mut self.a.types, t);
                if let Ty::Int(k) = self.ty(r)
                    && !k.signed()
                {
                    let span = self.expr(e).span;
                    late.push(
                        Diagnostic::new(Code::E0401, span, format!("`-` on the unsigned type `{}`", k.name()))
                            .with_found(self.src(span)),
                    );
                }
            }
            for i in 0..self.info.instances.len() {
                let inst = self.info.instances[i].clone();
                let generics = self.a.def(inst.def).generics().to_vec();
                // Methods: generics are the impl's followed by the fn's.
                let generics = match self.a.def(inst.def).owner {
                    Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) => {
                        let mut g = self.a.def(o).generics().to_vec();
                        g.extend(generics.into_iter().skip(g.len()));
                        g
                    }
                    _ => generics,
                };
                for (g, &arg) in generics.iter().zip(&inst.args) {
                    let r = self.infer.resolve(&mut self.a.types, arg);
                    if let GenericKind::Type { bounds, dup } = &g.kind
                        && let Some(b) = self.unsatisfied_bound(r, bounds, *dup)
                    {
                        let shown = self.display(r);
                        late.push(
                            Diagnostic::new(
                                Code::E0416,
                                inst.span,
                                format!("`{shown}` does not satisfy the bound `{}: {}`", g.name, bound_name(b)),
                            )
                            .with_found(self.src(inst.span)),
                        );
                    }
                }
            }
            for (e, t, visible) in self.holes.clone() {
                let want = self.infer.resolve(&mut self.a.types, t);
                let mut candidates = Vec::new();
                for id in visible {
                    let lt = self.info.locals[id.0 as usize].ty;
                    if self.infer.resolve(&mut self.a.types, lt) == want {
                        candidates.push(self.info.locals[id.0 as usize].name.clone());
                    }
                }
                let msg = match self.ty(want) {
                    Ty::Var(_) => "hole; the expected type is not known here".to_string(),
                    _ => {
                        let shown = self.display(want);
                        if candidates.is_empty() {
                            format!("hole of type `{shown}`")
                        } else {
                            format!("hole of type `{shown}`; candidates: {}", candidates.join(", "))
                        }
                    }
                };
                late.push(Diagnostic::new(Code::E0421, self.expr(e).span, msg).with_found("_"));
            }
            late.sort_by_key(|d| d.span.start);
            if let Some(d) = late.into_iter().next() {
                self.diag(d);
            }
        }
        // Resolve the tables.
        let keys: Vec<ExprId> = self.info.expr_types.keys().copied().collect();
        for e in keys {
            let t = self.info.expr_types[&e];
            let r = self.infer.resolve(&mut self.a.types, t);
            self.info.expr_types.insert(e, r);
        }
        for l in 0..self.info.locals.len() {
            let t = self.info.locals[l].ty;
            self.info.locals[l].ty = self.infer.resolve(&mut self.a.types, t);
        }
        for i in 0..self.info.instances.len() {
            for j in 0..self.info.instances[i].args.len() {
                let t = self.info.instances[i].args[j];
                self.info.instances[i].args[j] = self.infer.resolve(&mut self.a.types, t);
            }
        }
        self.info.complete = !self.failed;
        self.info
    }

    // ------------------------------------------------------------ bounds

    /// Whether a (resolved) type satisfies a builtin bound (§6.3).
    pub(crate) fn satisfies(&self, t: TyId, b: Bound) -> bool {
        let ty = self.ty(t);
        match (&ty, b) {
            (Ty::Error, _) => true,
            (Ty::Param(i), _) => {
                let Some(g) = self.generics.get(*i as usize) else { return false };
                match &g.kind {
                    GenericKind::Type { bounds, dup } => {
                        bounds.iter().any(|&have| implies(have, b)) || (b == Bound::Dup && *dup)
                    }
                    _ => false,
                }
            }
            (
                Ty::Int(_),
                Bound::Num
                | Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Eq
                | Bound::Ord
                | Bound::Copy
                | Bound::Dup
                | Bound::Hash
                | Bound::Default
                | Bound::Show,
            ) => true,
            (
                Ty::Float(_),
                Bound::Num
                | Bound::Float
                | Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Copy
                | Bound::Dup
                | Bound::Default
                | Bound::Show,
            ) => true,
            (
                Ty::Bool,
                Bound::PartialEq | Bound::Eq | Bound::Hash | Bound::Copy | Bound::Dup | Bound::Default | Bound::Show,
            ) => true,
            (
                Ty::Char,
                Bound::PartialEq
                | Bound::PartialOrd
                | Bound::Eq
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Show,
            ) => true,
            (Ty::Unit, Bound::PartialEq | Bound::Eq | Bound::Copy | Bound::Dup | Bound::Default) => true,
            (
                Ty::Array(e, _),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Default,
            ) => self.satisfies(*e, b),
            (
                Ty::Tuple(ts),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Copy
                | Bound::Dup
                | Bound::Default,
            ) => ts.iter().all(|&x| self.satisfies(x, b)),
            (
                Ty::Builtin(BuiltinTy::Option | BuiltinTy::Result, args),
                Bound::PartialEq | Bound::Eq | Bound::PartialOrd | Bound::Ord | Bound::Hash | Bound::Copy | Bound::Dup,
            ) => args.iter().all(|&x| self.satisfies(x, b)),
            (
                Ty::Builtin(BuiltinTy::Str | BuiltinTy::Bytes, _),
                Bound::PartialEq
                | Bound::Eq
                | Bound::PartialOrd
                | Bound::Ord
                | Bound::Hash
                | Bound::Dup
                | Bound::Show
                | Bound::Default,
            ) => true,
            (Ty::Builtin(BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set, _), Bound::Dup) => true,
            (Ty::Builtin(BuiltinTy::Array, args), Bound::PartialEq | Bound::Eq) => {
                args.iter().all(|&x| self.satisfies(x, b))
            }
            (Ty::Fn(_), Bound::Copy | Bound::Dup) => true,
            (Ty::Named(d, args), _) => {
                let def = self.a.def(*d);
                let derives = match &def.kind {
                    DefKind::Struct(s) => s.derives.clone(),
                    DefKind::Enum(e) => e.derives.clone(),
                    _ => Vec::new(),
                };
                let derived = |d: crate::def::Derive| derives.contains(&d);
                match b {
                    Bound::Copy => self.a.kind_of(t) == Some(Kind::Copy),
                    Bound::Dup => matches!(self.a.kind_of(t), Some(Kind::Copy | Kind::Shared)),
                    Bound::PartialEq => derived(crate::def::Derive::PartialEq) || derived(crate::def::Derive::Eq),
                    Bound::Eq => derived(crate::def::Derive::Eq),
                    Bound::PartialOrd => derived(crate::def::Derive::PartialOrd) || derived(crate::def::Derive::Ord),
                    Bound::Ord => derived(crate::def::Derive::Ord),
                    Bound::Default => derived(crate::def::Derive::Default),
                    _ => {
                        let _ = args;
                        false
                    }
                }
            }
            _ => false,
        }
    }

    fn unsatisfied_bound(&self, t: TyId, bounds: &[Bound], dup: bool) -> Option<Bound> {
        if matches!(self.ty(t), Ty::Var(_)) {
            return None;
        }
        if dup && !self.satisfies(t, Bound::Dup) && self.a.kind_of(t).is_some() {
            return Some(Bound::Dup);
        }
        bounds.iter().copied().find(|&b| !self.satisfies(t, b))
    }

    // ------------------------------------------------------------ generics

    /// Fresh variables for a def's generic parameters (owner's first for methods).
    pub(crate) fn fresh_args(&mut self, def: DefId) -> Vec<TyId> {
        let generics = self.all_generics(def);
        generics
            .iter()
            .map(|g| match g.kind {
                GenericKind::Const(_) => {
                    let len = self.infer.fresh_len();
                    let Len::Var(v) = len else { unreachable!() };
                    self.a.types.intern(Ty::Var(v))
                }
                _ => self.fresh(),
            })
            .collect()
    }

    fn all_generics(&self, def: DefId) -> Vec<GenericDef> {
        let d = self.a.def(def);
        match d.owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) => {
                // Method generics already include the impl's (sig.rs lowers them that way).
                d.generics().to_vec()
            }
            _ => d.generics().to_vec(),
        }
    }

    /// Substitute `Ty::Param(i)` / `Len::Param(i)` with `args[i]` (variables or concrete).
    fn subst(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        if args.is_empty() {
            return ty;
        }
        match self.ty(ty) {
            Ty::Param(i) => args.get(i as usize).copied().unwrap_or(ty),
            Ty::Array(e, len) => {
                let e2 = self.subst(e, args);
                let len2 = match len {
                    Len::Param(i) => match args.get(i as usize).map(|&t| self.ty(t)) {
                        Some(Ty::Var(v)) => Len::Var(v),
                        Some(Ty::ConstVal(n)) => Len::Const(n),
                        _ => len,
                    },
                    other => other,
                };
                self.a.types.intern(Ty::Array(e2, len2))
            }
            Ty::Tuple(ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Tuple(ns))
            }
            Ty::Named(d, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Named(d, ns))
            }
            Ty::Builtin(b, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Builtin(b, ns))
            }
            Ty::Fn(f) => {
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|(m, t)| (*m, self.subst(*t, args))).collect();
                let ret = self.subst(f.ret, args);
                self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }))
            }
            Ty::Rate(r, t) => {
                let t2 = self.subst(t, args);
                self.a.types.intern(Ty::Rate(r, t2))
            }
            _ => ty,
        }
    }

    /// Record an instantiation and check that every argument got resolved (E0406).
    fn finish_instance(&mut self, def: DefId, args: Vec<TyId>, span: Span) -> R<Option<InstId>> {
        if args.is_empty() {
            return Ok(None);
        }
        let generics = self.all_generics(def);
        for (g, &arg) in generics.iter().zip(&args) {
            if self.infer.is_unresolved(&self.a.types, arg) {
                let name = self.a.def(def).name.clone();
                return Err(self.diag(
                    Diagnostic::new(
                        Code::E0406,
                        span,
                        format!(
                            "the type parameter `{}` of `{name}` cannot be determined from the arguments or the expected type; annotate the result (§4.5)",
                            g.name
                        ),
                    )
                    .with_found(self.src(span)),
                ));
            }
        }
        let id = InstId(self.info.instances.len() as u32);
        self.info.instances.push(Instance { def, args, span });
        Ok(Some(id))
    }

    // ------------------------------------------------------------ names

    /// `a.b.c` as a chain of identifiers with the expression of each prefix.
    pub(crate) fn name_chain(&self, e: ExprId) -> Option<Vec<(ExprId, Ident)>> {
        let mut out = Vec::new();
        let mut cur = e;
        loop {
            match &self.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    out.push((cur, name.clone()));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    out.push((cur, p.segments[0].clone()));
                    break;
                }
                _ => return None,
            }
        }
        out.reverse();
        Some(out)
    }

    pub(crate) fn is_local_head(&mut self, name: &str) -> bool {
        name == "self" || self.lookup_local(name).is_some() || self.const_param(name).is_some()
    }

    fn const_param(&self, name: &str) -> Option<u32> {
        self.generics.iter().position(|g| g.name == name && matches!(g.kind, GenericKind::Const(_))).map(|i| i as u32)
    }

    /// Resolve the longest prefix of a dotted name that denotes a value, then
    /// apply the remaining segments as field accesses. Records types and
    /// targets of every prefix expression. Returns the type of the whole chain.
    fn check_chain(&mut self, chain: &[(ExprId, Ident)], expected: Option<TyId>) -> R<TyId> {
        let n = chain.len();
        let head = &chain[0].1;
        // Local, `self`, const parameter: ordinary field accesses from there.
        if self.is_local_head(&head.name) {
            let mut t = self.check_single_path(chain[0].0, head, if n == 1 { expected } else { None })?;
            for (e, name) in &chain[1..] {
                let base = self.known(t, self.expr(*e).span, "value")?;
                t = self.field_type(base, name)?;
                self.record(*e, t);
            }
            return Ok(t);
        }
        // Module-level resolution of the longest value prefix.
        let mut k = 1;
        let mut value_ty: Option<TyId> = None;
        while k <= n {
            let path = Path {
                segments: chain[..k].iter().map(|(_, i)| i.clone()).collect(),
                span: self.expr(chain[k - 1].0).span,
            };
            let entity = match self.a.resolve_path(self.m, &path) {
                Ok(e) => e,
                Err(err) => {
                    // A scalar / builtin type followed by an associated builtin item.
                    if k >= 2 {
                        let prefix =
                            Path { segments: chain[..k - 1].iter().map(|(_, i)| i.clone()).collect(), span: path.span };
                        if let Ok(Entity::Builtin(b)) = self.a.resolve_path(self.m, &prefix)
                            && let Some(t) = self.builtin_const(b, &chain[k - 1].1)
                        {
                            self.info.targets.insert(
                                chain[k - 1].0,
                                Target::BuiltinConst { ty: t, name: chain[k - 1].1.name.clone() },
                            );
                            value_ty = Some(t);
                            break;
                        }
                    }
                    return Err(self.diag(err.into_diagnostic()));
                }
            };
            let last = k == n;
            match self.value_of_entity(entity, chain[k - 1].0, &chain[k - 1].1, if last { expected } else { None })? {
                Some(t) => {
                    value_ty = Some(t);
                    break;
                }
                None => {
                    if last {
                        let name = self.src(path.span);
                        return Err(self.err(Code::E0401, path.span, format!("`{name}` is not a value")));
                    }
                }
            }
            k += 1;
        }
        let Some(mut t) = value_ty else {
            let span = self.expr(chain[n - 1].0).span;
            return Err(self.err(Code::E0401, span, "not a value"));
        };
        self.record(chain[k - 1].0, t);
        for (e, name) in &chain[k..] {
            let base = self.known(t, self.expr(*e).span, "value")?;
            t = self.field_type(base, name)?;
            self.record(*e, t);
        }
        Ok(t)
    }

    fn builtin_const(&mut self, b: Builtin, name: &Ident) -> Option<TyId> {
        match b {
            Builtin::Scalar(t) => builtin::assoc_const(&mut self.a.types, t, &name.name),
            _ => None,
        }
    }

    /// A single identifier in expression position.
    fn check_single_path(&mut self, e: ExprId, name: &Ident, expected: Option<TyId>) -> R<TyId> {
        if let Some(id) = self.lookup_local(&name.name) {
            if self.flow.is_some() {
                self.flow_use_local(id, name.span)?;
            }
            self.info.targets.insert(e, Target::Local(id));
            let t = self.local_ty(id);
            return Ok(self.record(e, t));
        }
        if let Some(i) = self.const_param(&name.name) {
            self.info.targets.insert(e, Target::ConstParam(i));
            let t = self.u32();
            return Ok(self.record(e, t));
        }
        if name.name == "self" {
            return Err(self.err(Code::E0302, name.span, "`self` is only available inside a method"));
        }
        let path = Path { segments: vec![name.clone()], span: name.span };
        let entity = match self.a.resolve_path(self.m, &path) {
            Ok(en) => en,
            Err(ResolveError::NotFound { .. }) => {
                return Err(self.err(Code::E0302, name.span, format!("cannot find `{}` in this scope", name.name)));
            }
            Err(err) => return Err(self.diag(err.into_diagnostic())),
        };
        match self.value_of_entity(entity, e, name, expected)? {
            Some(t) => Ok(self.record(e, t)),
            None => Err(self.err(Code::E0401, name.span, format!("`{}` is not a value", name.name))),
        }
    }

    /// Type of an entity used as a value (`None` when it is a type / module /
    /// namespace). Records the target on `e`.
    fn value_of_entity(&mut self, entity: Entity, e: ExprId, name: &Ident, expected: Option<TyId>) -> R<Option<TyId>> {
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                match &def.kind {
                    DefKind::Fn(f) => {
                        if f.self_mode.is_some() {
                            return Err(self.err(
                                Code::E0401,
                                name.span,
                                format!("`{}` is a method; call it as `value.{}(...)` (§6.2)", def.name, def.name),
                            ));
                        }
                        let args = self.fresh_args(d);
                        let fty = self.fn_type(f, &args);
                        if let Some(exp) = expected {
                            self.unify_at(name.span, fty, exp)?;
                        }
                        let inst = self.finish_instance(d, args, name.span)?;
                        self.info.targets.insert(e, Target::Fn { def: d, inst });
                        Ok(Some(fty))
                    }
                    DefKind::Const(c) => {
                        self.info.targets.insert(e, Target::Const(d));
                        Ok(Some(c.ty))
                    }
                    DefKind::Flow(_) => Err(self.err(
                        Code::E0401,
                        name.span,
                        format!(
                            "`{}` is a flow; outside a flow body use its namespace (`{}.init`, `{}.process`, §11.6)",
                            def.name, def.name, def.name
                        ),
                    )),
                    DefKind::Unsupported => Ok(Some(self.a.types.error())),
                    _ => Ok(None),
                }
            }
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                let variant = self.a.def(d).as_enum().unwrap().variants[i as usize].clone();
                let enum_ty = self.a.types.intern(Ty::Named(d, args.clone()));
                let t = if variant.fields.is_empty() {
                    enum_ty
                } else {
                    let params: Vec<(Mode, TyId)> =
                        variant.fields.iter().map(|&f| (Mode::Borrow, self.subst(f, &args))).collect();
                    self.a.types.intern(Ty::Fn(FnTy { rt: true, params, ret: enum_ty, effects: Default::default() }))
                };
                if let Some(exp) = expected {
                    self.unify_at(name.span, t, exp)?;
                }
                self.finish_instance(d, args, name.span)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(Some(t))
            }
            Entity::Builtin(b) => match b {
                Builtin::None => {
                    let t = self.fresh();
                    let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                    if let Some(exp) = expected {
                        self.unify_at(name.span, opt, exp)?;
                    }
                    self.info.targets.insert(e, Target::Prelude(b));
                    Ok(Some(opt))
                }
                Builtin::Some | Builtin::Ok | Builtin::Err => {
                    let t = self.fresh();
                    let (param, ret) = match b {
                        Builtin::Some => (t, self.a.types.builtin(BuiltinTy::Option, vec![t])),
                        Builtin::Ok => {
                            let e2 = self.fresh();
                            (t, self.a.types.builtin(BuiltinTy::Result, vec![t, e2]))
                        }
                        _ => {
                            let ok = self.fresh();
                            (t, self.a.types.builtin(BuiltinTy::Result, vec![ok, t]))
                        }
                    };
                    let fty = self.a.types.intern(Ty::Fn(FnTy {
                        rt: true,
                        params: vec![(Mode::Borrow, param)],
                        ret,
                        effects: Default::default(),
                    }));
                    if let Some(exp) = expected {
                        self.unify_at(name.span, fty, exp)?;
                    }
                    self.info.targets.insert(e, Target::Prelude(b));
                    Ok(Some(fty))
                }
                _ => Ok(None),
            },
            Entity::Module(_) => Ok(None),
        }
    }

    pub(crate) fn fn_type(&mut self, f: &FnDef, args: &[TyId]) -> TyId {
        let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, args))).collect();
        let ret = self.subst(f.ret, args);
        self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }))
    }

    /// Type of field `name` of a resolved base type.
    pub(crate) fn field_type(&mut self, base: TyId, name: &Ident) -> R<TyId> {
        match self.ty(base) {
            Ty::Named(d, args) => {
                let def = self.a.def(d).clone();
                if let DefKind::Struct(s) = &def.kind
                    && let Fields::Named(fs) = &s.fields
                    && let Some(f) = fs.iter().find(|f| f.name == name.name)
                {
                    return Ok(self.subst(f.ty, &args));
                }
                let shown = self.display(base);
                Err(self.err(Code::E0413, name.span, format!("`{shown}` has no field `{}`", name.name)))
            }
            Ty::Error => Ok(base),
            _ => {
                let shown = self.display(base);
                Err(self.err(Code::E0413, name.span, format!("`{shown}` has no field `{}`", name.name)))
            }
        }
    }

    // ------------------------------------------------------------ expressions

    pub(crate) fn check_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let t = self.check_expr_inner(e, expected)?;
        if let Some(exp) = expected {
            self.unify_at(span, t, exp)?;
        }
        Ok(self.record(e, t))
    }

    fn check_expr_inner(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let expr = self.expr(e);
        let span = expr.span;
        if self.flow.is_some()
            && let Some(t) = self.check_flow_expr(e, expected)?
        {
            return Ok(t);
        }
        match &expr.kind {
            ExprKind::Lit(lit) => self.check_lit(e, lit, expected),
            ExprKind::Path(p) => {
                if p.segments.len() == 1 {
                    let name = p.segments[0].clone();
                    self.check_single_path(e, &name, expected)
                } else {
                    let chain: Vec<(ExprId, Ident)> = p.segments.iter().map(|s| (e, s.clone())).collect();
                    self.check_chain(&chain, expected)
                }
            }
            ExprKind::Field { .. } => {
                if let Some(chain) = self.name_chain(e) {
                    self.check_chain(&chain, expected)
                } else {
                    let ExprKind::Field { base, name } = &expr.kind else { unreachable!() };
                    let bt = self.check_expr(*base, None)?;
                    let bt = self.known(bt, self.expr(*base).span, "value")?;
                    self.field_type(bt, name)
                }
            }
            ExprKind::Hole => {
                // Reported at the end of the body (§18.1), once later statements
                // have had the chance to decide the type.
                let t = expected.unwrap_or_else(|| self.fresh());
                let visible: Vec<LocalId> =
                    self.scopes.iter().flat_map(|s| s.names.iter().map(|(_, id)| *id)).collect();
                self.holes.push((e, t, visible));
                Ok(self.record(e, t))
            }
            ExprKind::Paren(inner) => self.check_expr(*inner, expected),
            ExprKind::Move(inner) => {
                // `move x` (§5.2, S-21): same type as its operand, which must be a place.
                let t = self.check_expr(*inner, expected)?;
                if !self.is_place(*inner) {
                    let ispan = self.expr(*inner).span;
                    return Err(self.err(
                        Code::E0711,
                        ispan,
                        "`move` needs a place (a variable or its field); other values are already owned by the expression",
                    ));
                }
                Ok(t)
            }
            ExprKind::Tuple(elems) => {
                if elems.is_empty() {
                    return Ok(self.unit());
                }
                let exp_elems: Option<Vec<TyId>> = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Tuple(ts) if ts.len() == elems.len() => Some(ts),
                    _ => None,
                });
                let mut ts = Vec::new();
                for (i, &el) in elems.iter().enumerate() {
                    let exp = exp_elems.as_ref().map(|v| v[i]);
                    ts.push(self.check_expr(el, exp)?);
                }
                Ok(self.a.types.intern(Ty::Tuple(ts)))
            }
            ExprKind::Array(elems) => {
                let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Array(el, _) => Some(el),
                    _ => None,
                });
                if elems.is_empty() {
                    let Some(el) = exp_elem else {
                        return Err(self.diag(
                            Diagnostic::new(
                                Code::E0420,
                                span,
                                "the type of an empty array must be known here; annotate it (§2.4)",
                            )
                            .with_found("[]"),
                        ));
                    };
                    return Ok(self.a.types.intern(Ty::Array(el, Len::Const(0))));
                }
                let first = self.check_expr(elems[0], exp_elem)?;
                for &el in &elems[1..] {
                    self.check_expr(el, Some(first))?;
                }
                Ok(self.a.types.intern(Ty::Array(first, Len::Const(elems.len() as u32))))
            }
            ExprKind::Repeat { elem, len } => {
                let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
                    Ty::Array(el, _) => Some(el),
                    _ => None,
                });
                let n = self.const_len(*len)?;
                let et = self.check_expr(*elem, exp_elem)?;
                self.info.repeats.push(e);
                Ok(self.a.types.intern(Ty::Array(et, n)))
            }
            ExprKind::Struct { path, fields } => self.check_struct_lit(path, fields, expected, self.expr(e).span),
            ExprKind::Block(b) => self.check_block(b, expected),
            ExprKind::If { cond, then, else_ } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                match else_ {
                    Some(el) => {
                        let t = self.check_expr(*then, expected)?;
                        self.check_expr(*el, Some(t))?;
                        Ok(t)
                    }
                    None => {
                        let unit = self.unit();
                        self.check_expr(*then, Some(unit))?;
                        Ok(unit)
                    }
                }
            }
            ExprKind::Match { scrutinee, arms } => self.check_match(*scrutinee, arms, expected, span),
            ExprKind::Closure { params, ret, effects, body } => {
                self.check_closure(e, params, *ret, effects.as_ref(), *body, expected)
            }
            ExprKind::Handle { .. } => {
                Err(self.err(Code::E0200, span, "this version does not support effect handlers (`handle ... with`)"))
            }
            ExprKind::Unsafe(_) => {
                Err(self.err(Code::E0200, span, "this version does not support `unsafe` blocks (FFI)"))
            }
            ExprKind::Par { .. } => Err(self.err(
                Code::E0401,
                span,
                "`par` replicates flow instances and is only written inside a flow body (§11.5)",
            )),
            ExprKind::Binary { operands, ops } => self.check_binary(operands, ops),
            ExprKind::Cast { expr: inner, ty } => {
                let it = self.check_expr(*inner, None)?;
                let from = self.known(it, self.expr(*inner).span, "operand of `as`")?;
                let to = self.lower_type_expr(*ty)?;
                if builtin::cast_allowed(&self.a.types, from, to) {
                    return Ok(to);
                }
                let (fs, ts) = (self.display(from), self.display(to));
                let mut d = Diagnostic::new(
                    Code::E0411,
                    span,
                    format!(
                        "`as` only widens without losing information; `{fs}` to `{ts}` needs a conversion method (§3.3)"
                    ),
                )
                .with_found(self.src(span));
                if let Some(m) = builtin::cast_suggestion(&self.a.types, from, to) {
                    let inner_src = self.src(self.expr(*inner).span);
                    d = d.with_fix(Fix::Replace { replace: format!("{inner_src}{m}") });
                }
                Err(self.diag(d))
            }
            ExprKind::Unary { op, expr: inner } => {
                let t = self.check_expr(*inner, None)?;
                let s = self.shallow(t);
                match op {
                    UnOp::Neg => {
                        if let ExprKind::Lit(Lit::Int { .. }) = self.expr(*inner).kind {
                            self.negated.push(*inner);
                        }
                        match self.ty(s) {
                            Ty::Int(k) if k.signed() => Ok(t),
                            Ty::Float(_) | Ty::Error => Ok(t),
                            Ty::Var(_) if self.infer.lit_of(&self.a.types, s).is_some() => {
                                self.neg_exprs.push((e, t));
                                Ok(t)
                            }
                            Ty::Param(_) if self.satisfies(s, Bound::Num) => Ok(t),
                            Ty::Var(_) => Err(self.known(t, span, "operand of `-`").unwrap_err()),
                            _ => {
                                let shown = self.display(t);
                                Err(self.err(
                                    Code::E0401,
                                    span,
                                    format!("`-` needs a signed integer or float; found `{shown}`"),
                                ))
                            }
                        }
                    }
                    UnOp::Not => match self.ty(s) {
                        Ty::Bool | Ty::Int(_) | Ty::Error => Ok(t),
                        Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => Ok(t),
                        Ty::Var(_) => Err(self.known(t, span, "operand of `!`").unwrap_err()),
                        _ => {
                            let shown = self.display(t);
                            Err(self.err(Code::E0401, span, format!("`!` needs `Bool` or an integer; found `{shown}`")))
                        }
                    },
                }
            }
            ExprKind::Call { callee, kind, args } => self.check_call(e, *callee, *kind, args, expected),
            ExprKind::TupleIndex { base, index, index_span } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known(bt, self.expr(*base).span, "value")?;
                match self.ty(bt) {
                    Ty::Tuple(ts) if (*index as usize) < ts.len() => Ok(ts[*index as usize]),
                    Ty::Named(d, args) => {
                        if let DefKind::Struct(s) = &self.a.def(d).kind
                            && let Fields::Tuple(inner) = s.fields
                            && *index == 0
                        {
                            return Ok(self.subst(inner, &args));
                        }
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, *index_span, format!("`{shown}` has no element `{index}`")))
                    }
                    Ty::Error => Ok(bt),
                    _ => {
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, *index_span, format!("`{shown}` has no element `{index}`")))
                    }
                }
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(*base, None)?;
                let bt = self.known(bt, self.expr(*base).span, "value")?;
                let u32 = self.u32();
                self.check_expr(*index, Some(u32))?;
                match self.ty(bt) {
                    Ty::Array(el, _) => Ok(el),
                    Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, args) => Ok(args[0]),
                    Ty::Builtin(BuiltinTy::Str, _) => Err(self.err(
                        Code::E0413,
                        span,
                        "`Str` has no index; use `.bytes()` / `.chars()` or `.substr(from, to)` (§4.2)",
                    )),
                    Ty::Error => Ok(bt),
                    _ => {
                        let shown = self.display(bt);
                        Err(self.err(Code::E0413, span, format!("`{shown}` cannot be indexed")))
                    }
                }
            }
            ExprKind::Try(inner) => {
                let it = self.check_expr(*inner, None)?;
                let it = self.known(it, self.expr(*inner).span, "operand of `?`")?;
                let ret = self.frames.last().unwrap().ret;
                let ret_s = self.shallow(ret);
                match (self.ty(it), self.ty(ret_s)) {
                    (Ty::Builtin(BuiltinTy::Option, a), Ty::Builtin(BuiltinTy::Option, _)) => Ok(a[0]),
                    (Ty::Builtin(BuiltinTy::Result, a), Ty::Builtin(BuiltinTy::Result, r)) => {
                        if self.infer.unify(&mut self.a.types, a[1], r[1]).is_err() {
                            let (ea, er) = (self.display(a[1]), self.display(r[1]));
                            return Err(self.err(
                                Code::E0414,
                                span,
                                format!("`?` needs the same error type as the function (`{er}`); found `{ea}`; convert it with `map_err` (§9.1)"),
                            ));
                        }
                        Ok(a[0])
                    }
                    (Ty::Error, _) => Ok(it),
                    (Ty::Builtin(BuiltinTy::Option | BuiltinTy::Result, _), _) => {
                        let (shown, rs) = (self.display(it), self.display(ret));
                        Err(self.err(
                            Code::E0414,
                            span,
                            format!(
                                "`?` on `{shown}` needs the function to return the same kind; it returns `{rs}` (§9.1)"
                            ),
                        ))
                    }
                    _ => {
                        let shown = self.display(it);
                        Err(self.err(Code::E0414, span, format!("`?` needs an `Option` or `Result`; found `{shown}`")))
                    }
                }
            }
            ExprKind::Range { .. } => {
                Err(self.err(Code::E0002, span, "ranges are only written in `for` and `par` heads (§7)"))
            }
        }
    }

    fn check_lit(&mut self, e: ExprId, lit: &Lit, expected: Option<TyId>) -> R<TyId> {
        match lit {
            Lit::Int { value, .. } => {
                self.int_lits.push((e, *value));
                let _ = expected;
                Ok(self.infer.fresh(&mut self.a.types, Some(LitKind::Int)))
            }
            Lit::Float { .. } => {
                self.float_lits.push(e);
                Ok(self.infer.fresh(&mut self.a.types, Some(LitKind::Float)))
            }
            Lit::Char(_) => Ok(self.a.types.intern(Ty::Char)),
            Lit::Bool(_) => Ok(self.bool_()),
            Lit::Str(s) => {
                for seg in &s.segments {
                    if let StrSeg::Interp(path) = seg {
                        let head = &path.segments[0];
                        let Some(id) = self.lookup_local(&head.name) else {
                            return Err(self.err(
                                Code::E0302,
                                head.span,
                                format!("cannot find `{}` for the interpolation", head.name),
                            ));
                        };
                        let mut t = self.local_ty(id);
                        for seg in &path.segments[1..] {
                            let base = self.known(t, seg.span, "value")?;
                            t = self.field_type(base, seg)?;
                        }
                    }
                }
                Ok(self.a.types.builtin(BuiltinTy::Str, vec![]))
            }
        }
    }

    /// `[e; N]` / array length in an expression: literal, constant, or const parameter.
    pub(crate) fn const_len(&mut self, len: ExprId) -> R<Len> {
        let expr = self.expr(len);
        match &expr.kind {
            ExprKind::Lit(Lit::Int { value, .. }) => {
                if *value > u32::MAX as u64 {
                    return Err(self.err(Code::E0408, expr.span, "array length does not fit in `U32`"));
                }
                let u32 = self.u32();
                self.record(len, u32);
                Ok(Len::Const(*value as u32))
            }
            ExprKind::Path(p) if p.segments.len() == 1 => {
                if let Some(i) = self.const_param(&p.segments[0].name) {
                    let u32 = self.u32();
                    self.record(len, u32);
                    return Ok(Len::Param(i));
                }
                self.const_len_path(len, p)
            }
            ExprKind::Field { .. } => {
                let chain = self.name_chain(len);
                match chain {
                    Some(c) => {
                        let p = Path { segments: c.iter().map(|(_, i)| i.clone()).collect(), span: expr.span };
                        self.const_len_path(len, &p)
                    }
                    None => Err(self.err(
                        Code::E0200,
                        expr.span,
                        "this version only accepts a literal or a constant as an array length",
                    )),
                }
            }
            _ => Err(self.err(
                Code::E0200,
                expr.span,
                "this version only accepts a literal or a constant as an array length",
            )),
        }
    }

    fn const_len_path(&mut self, len: ExprId, p: &Path) -> R<Len> {
        let span = self.expr(len).span;
        match self.a.resolve_path(self.m, p) {
            Ok(Entity::Def(d)) | Ok(Entity::Member(d)) => {
                if let DefKind::Const(c) = &self.a.def(d).kind {
                    let (ty, int_value) = (c.ty, c.int_value);
                    let u32 = self.u32();
                    self.unify_at(span, ty, u32)?;
                    self.record(len, ty);
                    self.info.targets.insert(len, Target::Const(d));
                    return match int_value {
                        Some(v) if v <= u32::MAX as u64 => Ok(Len::Const(v as u32)),
                        Some(_) => Err(self.err(Code::E0408, span, "array length does not fit in `U32`")),
                        None => Err(self.err(
                            Code::E0200,
                            span,
                            "constants computed by expressions as array lengths are evaluated in M3",
                        )),
                    };
                }
                Err(self.err(Code::E0302, span, "array length must be a constant"))
            }
            Ok(_) => Err(self.err(Code::E0302, span, "array length must be a constant")),
            Err(err) => Err(self.diag(err.into_diagnostic())),
        }
    }

    fn check_struct_lit(
        &mut self,
        path: &Path,
        fields: &[(Ident, ExprId)],
        expected: Option<TyId>,
        span: Span,
    ) -> R<TyId> {
        let entity = match self.a.resolve_path(self.m, path) {
            Ok(en) => en,
            Err(err) => return Err(self.diag(err.into_diagnostic())),
        };
        let d = match entity {
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
            _ => {
                let name = self.src(path.span);
                return Err(self.err(Code::E0401, path.span, format!("`{name}` is not a struct")));
            }
        };
        let s = self.a.def(d).as_struct().unwrap().clone();
        let Fields::Named(defs) = &s.fields else {
            let name = self.src(path.span);
            return Err(self.err(
                Code::E0410,
                path.span,
                format!("`{name}` is not built with a field list; it has no named fields"),
            ));
        };
        let args = self.fresh_args(d);
        // The expected type decides the generic arguments first (§4.7: expected
        // types flow downward; `Ring[F32, 4]` fixes `T` and `N` before the fields).
        if let Some(exp) = expected
            && let Ty::Named(d2, exp_args) = self.a.types.get(exp).clone()
            && d2 == d
            && exp_args.len() == args.len()
        {
            for (&a, &x) in args.iter().zip(&exp_args) {
                self.unify_at(span, a, x)?;
            }
        }
        let mut seen: Vec<&str> = Vec::new();
        for (name, value) in fields {
            if seen.contains(&name.name.as_str()) {
                return Err(self.err(Code::E0410, name.span, format!("field `{}` is given twice", name.name)));
            }
            seen.push(&name.name);
            let Some(f) = defs.iter().find(|f| f.name == name.name) else {
                let shown = self.a.def(d).name.clone();
                return Err(self.err(Code::E0410, name.span, format!("`{shown}` has no field `{}`", name.name)));
            };
            let ft = self.subst(f.ty, &args);
            self.check_expr(*value, Some(ft))?;
        }
        let missing: Vec<&str> = defs.iter().map(|f| f.name.as_str()).filter(|n| !seen.contains(n)).collect();
        if !missing.is_empty() {
            let shown = self.a.def(d).name.clone();
            return Err(self.err(
                Code::E0410,
                path.span,
                format!(
                    "missing field(s) {} of `{shown}`; struct literals name every field (§4.4)",
                    missing.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(", ")
                ),
            ));
        }
        let t = self.a.types.intern(Ty::Named(d, args.clone()));
        self.finish_instance(d, args, path.span)?;
        Ok(t)
    }

    pub(crate) fn check_block(&mut self, b: &Block, expected: Option<TyId>) -> R<TyId> {
        self.push_scope();
        if let Some(f) = &mut self.flow {
            f.depth += 1;
        }
        let r = (|| -> R<TyId> {
            for &s in &b.stmts {
                self.check_stmt(s)?;
            }
            match b.tail {
                Some(t) => self.check_expr(t, expected),
                None => {
                    // A block that ends in `return` / `break` / `continue` diverges: it
                    // takes any type (a trailing `return e` is allowed, §6.1).
                    let diverges = b.stmts.last().is_some_and(|&s| {
                        matches!(self.ast.stmt(s).kind, StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue)
                    });
                    if diverges { Ok(self.fresh()) } else { Ok(self.unit()) }
                }
            }
        })();
        if let Some(f) = &mut self.flow {
            f.depth -= 1;
        }
        self.pop_scope();
        r
    }

    fn check_match(&mut self, scrutinee: ExprId, arms: &[MatchArm], expected: Option<TyId>, span: Span) -> R<TyId> {
        let st = self.check_expr(scrutinee, None)?;
        let st = self.known(st, self.expr(scrutinee).span, "`match` operand")?;
        // §7 (S-21): `match x` binds borrows; only `match move x` gives the arms ownership.
        let borrow = !matches!(self.expr(scrutinee).kind, ExprKind::Move(_));
        let mut result: Option<TyId> = expected;
        let mut rows: Vec<Vec<P>> = Vec::new();
        for arm in arms {
            self.push_scope();
            let r = (|| -> R<()> {
                let p = self.bind_pat(arm.pat, st, false, borrow, LocalKind::MatchBind)?;
                if let Some(g) = arm.guard {
                    let bool_ = self.bool_();
                    self.check_expr(g, Some(bool_))?;
                } else {
                    rows.push(vec![p]);
                }
                let t = self.check_expr(arm.body, result)?;
                if result.is_none() {
                    result = Some(t);
                }
                Ok(())
            })();
            self.pop_scope();
            r?;
        }
        if let Some(missing) = self.missing_pattern(&rows, st) {
            return Err(self.diag(
                Diagnostic::new(
                    Code::E0501,
                    span,
                    format!("`match` is not exhaustive; `{missing}` is not covered (§7)"),
                )
                .with_found(self.src(self.expr(scrutinee).span)),
            ));
        }
        Ok(result.unwrap_or_else(|| self.unit()))
    }

    fn check_closure(
        &mut self,
        e: ExprId,
        params: &[Param],
        ret: Option<onsa_syntax::ast::TypeId>,
        effects: Option<&onsa_syntax::ast::EffectRow>,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let exp_fn: Option<FnTy> = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Fn(f) => Some(f),
            _ => None,
        });
        if let Some(f) = &exp_fn
            && f.params.len() != params.len()
        {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this function takes {} parameter(s) but {} are expected here", params.len(), f.params.len()),
            ));
        }
        let mut ptys = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let t = match p.ty {
                Some(t) => {
                    let lowered = self.lower_type_expr(t)?;
                    if let Some(f) = &exp_fn {
                        self.unify_at(self.ast.ty(t).span, lowered, f.params[i].1)?;
                    }
                    lowered
                }
                None => match &exp_fn {
                    Some(f) => f.params[i].1,
                    None => {
                        return Err(self.diag(
                            Diagnostic::new(
                                Code::E0420,
                                p.span,
                                "the parameter type of an anonymous function must be known here; annotate it (§6.1)",
                            )
                            .with_found(self.src(p.span)),
                        ));
                    }
                },
            };
            ptys.push((p.mode, t));
        }
        let ret_ty = match ret {
            Some(t) => self.lower_type_expr(t)?,
            None => match &exp_fn {
                Some(f) => f.ret,
                None => self.fresh(),
            },
        };
        let effects = match effects {
            Some(row) => {
                let mut set = crate::ty::EffectSet::default();
                for p in &row.effects {
                    let n = p.segments.last().unwrap();
                    if n.name == "Alloc" {
                        set.alloc = true;
                    } else {
                        return Err(self.err(
                            Code::E0200,
                            n.span,
                            format!("effects other than `Alloc` (`{}`)", n.name),
                        ));
                    }
                }
                set
            }
            None => exp_fn.as_ref().map(|f| f.effects.clone()).unwrap_or_default(),
        };
        let rt = exp_fn.as_ref().map(|f| f.rt).unwrap_or(false);
        // The body runs in its own frame: `return` targets the closure, captures are recorded.
        let frame =
            Frame { local_base: self.info.locals.len() as u32, ret: ret_ty, loop_depth: 0, captures: Vec::new() };
        self.frames.push(frame);
        self.push_scope();
        let r = (|| -> R<()> {
            for (p, (_, t)) in params.iter().zip(&ptys) {
                match &p.name {
                    ParamName::Ident(id) => {
                        self.declare(id, *t, LocalKind::ClosureParam(p.mode), p.mode == Mode::Borrow)?;
                    }
                    ParamName::SelfParam(s) => {
                        return Err(self.err(Code::E0002, *s, "an anonymous function has no `self`"));
                    }
                    ParamName::Wild(_) => {}
                }
            }
            self.check_expr(body, Some(ret_ty))?;
            Ok(())
        })();
        self.pop_scope();
        let frame = self.frames.pop().unwrap();
        r?;
        self.info.captures.insert(e, frame.captures);
        Ok(self.a.types.intern(Ty::Fn(FnTy { rt, params: ptys, ret: ret_ty, effects })))
    }

    fn check_binary(&mut self, operands: &[ExprId], ops: &[(BinOp, Span)]) -> R<TyId> {
        let mut t = self.check_expr(operands[0], None)?;
        for (i, (op, op_span)) in ops.iter().enumerate() {
            let rhs = operands[i + 1];
            let group = op.group();
            match group {
                OpGroup::And | OpGroup::Or => {
                    let bool_ = self.bool_();
                    self.unify_at(self.expr(operands[i]).span, t, bool_)?;
                    self.check_expr(rhs, Some(bool_))?;
                    t = bool_;
                }
                OpGroup::Comparison => {
                    let rt = self.check_expr(rhs, None)?;
                    self.unify_at(self.expr(rhs).span, rt, t)?;
                    let s = self.shallow(t);
                    let bound = if matches!(op, BinOp::Eq | BinOp::Ne) { Bound::PartialEq } else { Bound::PartialOrd };
                    self.require_operand(s, bound, *op, *op_span)?;
                    t = self.bool_();
                }
                OpGroup::Bitwise if matches!(op, BinOp::Shl | BinOp::Shr) => {
                    let u32 = self.u32();
                    self.check_expr(rhs, Some(u32))?;
                    let s = self.shallow(t);
                    self.require_int(s, *op, *op_span)?;
                }
                OpGroup::Bitwise => {
                    let rt = self.check_expr(rhs, None)?;
                    self.unify_at(self.expr(rhs).span, rt, t)?;
                    let s = self.shallow(t);
                    self.require_int(s, *op, *op_span)?;
                }
                OpGroup::Additive | OpGroup::Multiplicative => {
                    let rt = self.check_expr(rhs, None)?;
                    self.unify_at(self.expr(rhs).span, rt, t)?;
                    let s = self.shallow(t);
                    if matches!(
                        op,
                        BinOp::WrapAdd
                            | BinOp::WrapSub
                            | BinOp::WrapMul
                            | BinOp::SatAdd
                            | BinOp::SatSub
                            | BinOp::SatMul
                    ) {
                        self.require_int(s, *op, *op_span)?;
                    } else {
                        self.require_operand(s, Bound::Num, *op, *op_span)?;
                    }
                }
            }
        }
        Ok(t)
    }

    /// The operand type of an operator must support it (via its builtin trait, §3.2).
    pub(crate) fn require_operand(&mut self, s: TyId, bound: Bound, op: BinOp, span: Span) -> R<()> {
        match self.ty(s) {
            Ty::Var(_) => match (self.infer.lit_of(&self.a.types, s), bound) {
                (Some(_), Bound::Num | Bound::PartialEq | Bound::PartialOrd) => Ok(()),
                (Some(_), _) => Ok(()),
                (None, _) => Err(self.known(s, span, &format!("operand of `{}`", op.symbol())).unwrap_err()),
            },
            _ => {
                if self.satisfies(s, bound) {
                    Ok(())
                } else {
                    let shown = self.display(s);
                    Err(self.err(
                        Code::E0401,
                        span,
                        format!(
                            "`{}` is not defined for `{shown}` (it needs `{}`; §3.2)",
                            op.symbol(),
                            bound_name(bound)
                        ),
                    ))
                }
            }
        }
    }

    fn require_int(&mut self, s: TyId, op: BinOp, span: Span) -> R<()> {
        match self.ty(s) {
            Ty::Int(_) | Ty::Error => Ok(()),
            Ty::Var(_) => match self.infer.lit_of(&self.a.types, s) {
                Some(LitKind::Int) => Ok(()),
                Some(LitKind::Float) => {
                    Err(self.err(Code::E0401, span, format!("`{}` is defined for integers only (§3.4)", op.symbol())))
                }
                None => Err(self.known(s, span, &format!("operand of `{}`", op.symbol())).unwrap_err()),
            },
            _ => {
                let shown = self.display(s);
                Err(self.err(
                    Code::E0401,
                    span,
                    format!("`{}` is defined for integers only; found `{shown}` (§3.4)", op.symbol()),
                ))
            }
        }
    }

    // ------------------------------------------------------------ calls

    fn check_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        kind: CallKind,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        if self.flow.is_some()
            && let Some(t) = self.check_flow_call(e, callee, kind, args, expected)?
        {
            return Ok(t);
        }
        if kind == CallKind::Flow {
            let fix = self.src(span).replacen("~(", "(", 1);
            return Err(self.diag(
                Diagnostic::new(
                    Code::E0812,
                    span,
                    "`~(` creates a flow instance and is only written inside a flow body (§11.5)",
                )
                .with_found(self.src(span))
                .with_fix(Fix::Replace { replace: fix }),
            ));
        }
        // 1. Method call `recv.name(...)` when the base is a value.
        if let ExprKind::Field { base, name } = &self.expr(callee).kind {
            let base = *base;
            let name = name.clone();
            let chain = self.name_chain(callee);
            let head_is_local = chain.as_ref().is_some_and(|c| self.is_local_head(&c[0].1.name));
            let resolved_fn = if head_is_local {
                None
            } else if let Some(c) = &chain {
                let path = Path { segments: c.iter().map(|(_, i)| i.clone()).collect(), span: self.expr(callee).span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(en) => Some(en),
                    Err(_) => {
                        // `Buf.zeroed`, `F32.from_bits`: builtin associated functions.
                        let prefix = Path {
                            segments: c[..c.len() - 1].iter().map(|(_, i)| i.clone()).collect(),
                            span: path.span,
                        };
                        if let Ok(Entity::Builtin(b)) = self.a.resolve_path(self.m, &prefix) {
                            return self.check_builtin_assoc_call(e, callee, b, &name, args, expected);
                        }
                        None
                    }
                }
            } else {
                None
            };
            match resolved_fn {
                Some(entity)
                    if matches!(
                        entity,
                        Entity::Def(_)
                            | Entity::Member(_)
                            | Entity::Variant(..)
                            | Entity::Builtin(Builtin::Some | Builtin::Ok | Builtin::Err)
                    ) =>
                {
                    return self.check_fn_call(e, callee, entity, &name, args, expected, kind);
                }
                Some(Entity::Module(_)) | Some(Entity::Builtin(_)) => {
                    let shown = self.src(self.expr(callee).span);
                    return Err(self.err(Code::E0401, self.expr(callee).span, format!("`{shown}` is not a function")));
                }
                _ => {}
            }
            let recv = self.check_expr(base, None)?;
            let recv = self.known(recv, self.expr(base).span, "receiver")?;
            return self.check_method_call(e, callee, recv, &name, args, expected, kind);
        }
        // 2. Named function, variant constructor, or prelude constructor.
        if let ExprKind::Path(p) = &self.expr(callee).kind
            && p.segments.len() == 1
        {
            let name = p.segments[0].clone();
            if self.lookup_local(&name.name).is_none() && name.name != "self" {
                let path = Path { segments: vec![name.clone()], span: name.span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(
                        entity @ (Entity::Def(_)
                        | Entity::Member(_)
                        | Entity::Variant(..)
                        | Entity::Builtin(Builtin::Some | Builtin::Ok | Builtin::Err)),
                    ) => {
                        return self.check_fn_call(e, callee, entity, &name, args, expected, kind);
                    }
                    Ok(_) => {
                        return Err(self.err(Code::E0401, name.span, format!("`{}` is not a function", name.name)));
                    }
                    Err(ResolveError::NotFound { .. }) => {
                        return Err(self.err(
                            Code::E0302,
                            name.span,
                            format!("cannot find `{}` in this scope", name.name),
                        ));
                    }
                    Err(err) => return Err(self.diag(err.into_diagnostic())),
                }
            }
        }
        // 3. A function value.
        let ft = self.check_expr(callee, None)?;
        let ft = self.known(ft, self.expr(callee).span, "callee")?;
        let Ty::Fn(f) = self.ty(ft) else {
            let shown = self.display(ft);
            return Err(self.err(
                Code::E0401,
                self.expr(callee).span,
                format!("`{shown}` is not a function and cannot be called"),
            ));
        };
        if kind == CallKind::Bang {
            let fix = self.src(span).replacen("!(", "(", 1);
            return Err(self.diag(
                Diagnostic::new(Code::E0714, span, "`!` marks `inout self` method calls only (§5.2)")
                    .with_found(self.src(span))
                    .with_fix(Fix::Replace { replace: fix }),
            ));
        }
        self.info.targets.insert(e, Target::Value);
        self.check_args(args, &f.params, span)?;
        Ok(f.ret)
    }

    #[allow(clippy::too_many_arguments)]
    fn check_fn_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        entity: Entity,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                let DefKind::Fn(f) = &def.kind else {
                    if matches!(def.kind, DefKind::Unsupported) {
                        return Ok(self.a.types.error());
                    }
                    return Err(self.err(Code::E0401, name.span, format!("`{}` is not a function", def.name)));
                };
                if f.self_mode.is_some() {
                    return Err(self.err(
                        Code::E0401,
                        name.span,
                        format!("`{}` is a method; call it as `value.{}(...)` (§6.2)", def.name, def.name),
                    ));
                }
                if kind == CallKind::Bang {
                    let fix = self.src(span).replacen("!(", "(", 1);
                    return Err(self.diag(
                        Diagnostic::new(Code::E0714, span, "`!` marks `inout self` method calls only (§5.2)")
                            .with_found(self.src(span))
                            .with_fix(Fix::Replace { replace: fix }),
                    ));
                }
                let targs = self.fresh_args(d);
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, &targs))).collect();
                let ret = self.subst(f.ret, &targs);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                let inst = self.finish_instance(d, targs, span)?;
                self.info.targets.insert(e, Target::Fn { def: d, inst });
                let fty = self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }));
                self.record(callee, fty);
                Ok(ret)
            }
            Entity::Variant(d, i) => {
                let targs = self.fresh_args(d);
                let variant = self.a.def(d).as_enum().unwrap().variants[i as usize].clone();
                if variant.fields.is_empty() {
                    return Err(self.err(
                        Code::E0412,
                        span,
                        format!("`{}` is a unit variant and takes no arguments", variant.name),
                    ));
                }
                let params: Vec<(Mode, TyId)> =
                    variant.fields.iter().map(|&f| (Mode::Borrow, self.subst(f, &targs))).collect();
                let ret = self.a.types.intern(Ty::Named(d, targs.clone()));
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                self.finish_instance(d, targs, span)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(ret)
            }
            Entity::Builtin(b) => {
                let t = self.fresh();
                let ret = match b {
                    Builtin::Some => self.a.types.builtin(BuiltinTy::Option, vec![t]),
                    Builtin::Ok => {
                        let e2 = self.fresh();
                        self.a.types.builtin(BuiltinTy::Result, vec![t, e2])
                    }
                    _ => {
                        let ok = self.fresh();
                        self.a.types.builtin(BuiltinTy::Result, vec![ok, t])
                    }
                };
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &[(Mode::Borrow, t)], span)?;
                self.info.targets.insert(e, Target::Prelude(b));
                Ok(ret)
            }
            Entity::Module(_) => unreachable!(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_method_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let _ = callee;
        if let Ty::Named(d, targs_recv) = self.ty(recv) {
            let assoc = self.a.modules.assoc.get(&d).and_then(|m| m.get(&name.name)).copied();
            if let Some(md) = assoc {
                let mdef = self.a.def(md).clone();
                let DefKind::Fn(f) = &mdef.kind else {
                    return Err(self.err(Code::E0413, name.span, format!("`{}` is not a method", name.name)));
                };
                if f.self_mode.is_none() {
                    let tname = self.a.def(d).name.clone();
                    return Err(self.err(
                        Code::E0413,
                        name.span,
                        format!(
                            "`{}` is an associated function; call it as `{tname}.{}(...)` (§6.2)",
                            name.name, name.name
                        ),
                    ));
                }
                let targs = self.fresh_args(md);
                // The impl's own generic arguments come from the receiver.
                let impl_self = mdef.owner.and_then(|o| match &self.a.def(o).kind {
                    DefKind::Impl(i) => Some(i.self_ty),
                    _ => None,
                });
                if let Some(st) = impl_self {
                    let st2 = self.subst(st, &targs);
                    self.unify_at(name.span, recv, st2)?;
                }
                let _ = targs_recv;
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, &targs))).collect();
                let ret = self.subst(f.ret, &targs);
                if let Some(exp) = expected {
                    self.unify_at(span, ret, exp)?;
                }
                self.check_args(args, &params, span)?;
                let inst = self.finish_instance(md, targs, span)?;
                self.info.targets.insert(e, Target::Method { def: md, inst });
                let _ = kind;
                return Ok(ret);
            }
            if !matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_)) {
                return Ok(self.a.types.error());
            }
        }
        let Some(sig) = builtin::method(&mut self.a.types, recv, &name.name) else {
            if matches!(self.ty(recv), Ty::Error) {
                return Ok(recv);
            }
            let shown = self.display(recv);
            return Err(self.err(Code::E0413, name.span, format!("`{shown}` has no method `{}`", name.name)));
        };
        let params: Vec<(Mode, TyId)> = sig.params.iter().map(|&t| (Mode::Borrow, t)).collect();
        if let Some(exp) = expected {
            self.unify_at(span, sig.ret, exp)?;
        }
        self.check_args(args, &params, span)?;
        self.info.targets.insert(e, Target::BuiltinMethod { recv, name: name.name.clone(), bang: sig.bang });
        Ok(sig.ret)
    }

    fn check_builtin_assoc_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        b: Builtin,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let _ = callee;
        let (scalar, generic) = match b {
            Builtin::Scalar(t) => (Some(t), None),
            Builtin::Generic(g) => (None, Some(g)),
            _ => (None, None),
        };
        let targ = self.fresh();
        let Some((params, ret)) = builtin::assoc_fn(&mut self.a.types, scalar, generic, &name.name, targ) else {
            let shown = self.src(self.expr(callee).span);
            return Err(self.err(Code::E0413, name.span, format!("`{shown}` does not exist")));
        };
        if let Some(exp) = expected {
            self.unify_at(span, ret, exp)?;
        }
        let params: Vec<(Mode, TyId)> = params.into_iter().map(|t| (Mode::Borrow, t)).collect();
        self.check_args(args, &params, span)?;
        let recv = scalar.unwrap_or_else(|| self.a.builtin_key[&generic.unwrap()]);
        self.info.targets.insert(e, Target::BuiltinMethod { recv, name: name.name.clone(), bang: false });
        Ok(ret)
    }

    /// Arity and argument types. `Span[T]` parameters accept `[T; N]`,
    /// `Buf[T]` and `Span[T]` (§5.3); `[Span[T]; N]` accepts the planar forms.
    pub(crate) fn check_args(&mut self, args: &[Arg], params: &[(Mode, TyId)], span: Span) -> R<()> {
        if args.len() != params.len() {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this call takes {} argument(s) but {} were given", params.len(), args.len()),
            ));
        }
        for (arg, (_, pt)) in args.iter().zip(params) {
            let pt = *pt;
            let ps = self.shallow(pt);
            let coerce = match self.ty(ps) {
                Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], None)),
                Ty::Array(inner, len) => match self.ty(self.shallow(inner)) {
                    Ty::Builtin(BuiltinTy::Span, a) => Some((a[0], Some(len))),
                    _ => None,
                },
                _ => None,
            };
            match coerce {
                None => {
                    self.check_expr(arg.expr, Some(pt))?;
                }
                Some((elem, planar)) => {
                    let at = self.check_expr(arg.expr, None)?;
                    let at_s = self.known(at, self.expr(arg.expr).span, "argument")?;
                    let aspan = self.expr(arg.expr).span;
                    let ok = match (planar, self.ty(at_s)) {
                        (None, Ty::Array(el, _)) => self.infer.unify(&mut self.a.types, el, elem).is_ok(),
                        (None, Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a)) => {
                            self.infer.unify(&mut self.a.types, a[0], elem).is_ok()
                        }
                        (Some(n), Ty::Array(ch, m)) => {
                            let lens_ok =
                                self.infer.shallow_len(&self.a.types, n) == self.infer.shallow_len(&self.a.types, m);
                            lens_ok
                                && match self.ty(self.shallow(ch)) {
                                    Ty::Array(el, _) => self.infer.unify(&mut self.a.types, el, elem).is_ok(),
                                    Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a) => {
                                        self.infer.unify(&mut self.a.types, a[0], elem).is_ok()
                                    }
                                    _ => false,
                                }
                        }
                        (_, Ty::Error) => true,
                        _ => false,
                    };
                    if !ok {
                        let (ps_s, as_s) = (self.display(pt), self.display(at));
                        return Err(self.err(
                            Code::E0401,
                            aspan,
                            format!(
                                "expected `{ps_s}` (or an array / `Buf` of the same element), found `{as_s}` (§5.3)"
                            ),
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------ statements

    pub(crate) fn check_stmt(&mut self, s: StmtId) -> R<()> {
        if self.flow.is_some() {
            return self.check_flow_stmt(s);
        }
        let stmt = self.ast.stmt(s);
        match &stmt.kind {
            StmtKind::Let { pat, ty, init } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = self.check_expr(*init, ann)?;
                let borrow = self.is_borrow_source(*init);
                self.bind_pat(*pat, it, true, borrow, LocalKind::Let)?;
                Ok(())
            }
            StmtKind::Var { name, ty, init } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = self.check_expr(*init, ann)?;
                self.declare(name, it, LocalKind::Var, false)?;
                Ok(())
            }
            StmtKind::Assign { target, value } => {
                if !self.is_place(*target) {
                    let span = self.expr(*target).span;
                    return Err(self.err(
                        Code::E0415,
                        span,
                        "assignment needs a place: a `var`, or a field / element of one (§5.1)",
                    ));
                }
                let tt = self.check_expr(*target, None)?;
                self.check_expr(*value, Some(tt))?;
                Ok(())
            }
            StmtKind::For { pat, moved, iter, body } => {
                let (elem, borrow) = self.check_iter(*iter, *moved)?;
                self.push_scope();
                let r = (|| -> R<()> {
                    self.bind_pat(*pat, elem, true, borrow, LocalKind::For { moved: *moved })?;
                    self.frames.last_mut().unwrap().loop_depth += 1;
                    let unit = self.unit();
                    let r = self.check_expr(*body, Some(unit));
                    self.frames.last_mut().unwrap().loop_depth -= 1;
                    r.map(|_| ())
                })();
                self.pop_scope();
                r
            }
            StmtKind::While { cond, body } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                self.frames.last_mut().unwrap().loop_depth += 1;
                let unit = self.unit();
                let r = self.check_expr(*body, Some(unit));
                self.frames.last_mut().unwrap().loop_depth -= 1;
                r.map(|_| ())
            }
            StmtKind::Break | StmtKind::Continue => {
                if self.frames.last().unwrap().loop_depth == 0 {
                    let what = if matches!(stmt.kind, StmtKind::Break) { "break" } else { "continue" };
                    return Err(self.err(Code::E0002, stmt.span, format!("`{what}` outside a loop")));
                }
                Ok(())
            }
            StmtKind::Return(value) => {
                let ret = self.frames.last().unwrap().ret;
                match value {
                    Some(v) => {
                        self.check_expr(*v, Some(ret))?;
                    }
                    None => {
                        let unit = self.unit();
                        self.unify_at(stmt.span, unit, ret)?;
                    }
                }
                Ok(())
            }
            StmtKind::Assert(e) => {
                let bool_ = self.bool_();
                self.check_expr(*e, Some(bool_))?;
                Ok(())
            }
            StmtKind::Expr(e) => {
                self.check_expr(*e, None)?;
                Ok(())
            }
        }
    }

    /// Element type of a `for` iteration and whether the binding is a borrow.
    fn check_iter(&mut self, iter: ExprId, moved: bool) -> R<(TyId, bool)> {
        let span = self.expr(iter).span;
        if let ExprKind::Range { lo, hi } = &self.expr(iter).kind {
            let (lo, hi) = (*lo, *hi);
            let lt = self.check_expr(lo, None)?;
            self.check_expr(hi, Some(lt))?;
            let s = self.shallow(lt);
            match self.ty(s) {
                Ty::Int(_) | Ty::Error => {}
                Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => {}
                Ty::Var(_) => return Err(self.known(lt, span, "range bound").unwrap_err()),
                _ => {
                    let shown = self.display(lt);
                    return Err(self.err(Code::E0401, span, format!("a range needs integer bounds; found `{shown}`")));
                }
            }
            self.record(iter, lt);
            if moved {
                return Err(self.err(Code::E0401, span, "`move` applies to collections, not ranges (§7)"));
            }
            return Ok((lt, false));
        }
        let it = self.check_expr(iter, None)?;
        let it = self.known(it, span, "iterated value")?;
        match self.ty(it) {
            Ty::Array(el, _) => Ok((el, !moved)),
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, a) => Ok((a[0], !moved)),
            Ty::Builtin(BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Str, _) => {
                Err(self.err(Code::E0200, span, "this version iterates arrays, `Span`, `Buf` and `Array` only"))
            }
            Ty::Error => Ok((it, true)),
            _ => {
                let shown = self.display(it);
                Err(self.err(Code::E0401, span, format!("`{shown}` cannot be iterated (§7)")))
            }
        }
    }

    /// A place expression (§5.1): a local, or a field / element / tuple element of a place.
    fn is_place(&mut self, e: ExprId) -> bool {
        match &self.expr(e).kind {
            ExprKind::Path(p) => {
                p.segments.len() == 1
                    && (p.segments[0].name == "self" || self.lookup_local(&p.segments[0].name).is_some())
            }
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } | ExprKind::TupleIndex { base, .. } => {
                self.is_place(*base)
            }
            ExprKind::Paren(inner) => self.is_place(*inner),
            _ => false,
        }
    }

    /// §5.4: `let y = x`, `x.f`, `x[i]` where `x` is a borrowed parameter or a
    /// borrow binding derived from one.
    fn is_borrow_source(&mut self, e: ExprId) -> bool {
        match &self.expr(e).kind {
            ExprKind::Path(p) if p.segments.len() == 1 => match self.lookup_local(&p.segments[0].name) {
                Some(id) => {
                    let l = &self.info.locals[id.0 as usize];
                    l.borrow || matches!(l.kind, LocalKind::Param(Mode::Borrow) | LocalKind::SelfParam(Mode::Borrow))
                }
                None => false,
            },
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } | ExprKind::TupleIndex { base, .. } => {
                self.is_borrow_source(*base)
            }
            ExprKind::Paren(inner) => self.is_borrow_source(*inner),
            _ => false,
        }
    }

    // ------------------------------------------------------------ patterns

    /// Bind a pattern against `ty`. Returns the lowered pattern for the
    /// exhaustiveness check. `irrefutable` is the `let` / `for` context (E0502).
    fn bind_pat(&mut self, pat: PatId, ty: TyId, irrefutable: bool, borrow: bool, kind: LocalKind) -> R<P> {
        let p = self.ast.pat(pat);
        let span = p.span;
        match &p.kind {
            PatKind::Wild => Ok(P::Wild),
            PatKind::Bind(id) => {
                if let Some(or) = &self.or_bindings
                    && let Some(&prev) = or.get(&id.name)
                {
                    let pt = self.local_ty(prev);
                    self.unify_at(id.span, ty, pt)?;
                    self.info.pat_locals.insert(pat, prev);
                    return Ok(P::Wild);
                }
                let lid = self.declare(id, ty, kind, borrow)?;
                self.info.pat_locals.insert(pat, lid);
                if let Some(or) = &mut self.or_bindings {
                    or.insert(id.name.clone(), lid);
                }
                Ok(P::Wild)
            }
            PatKind::Lit(lit) | PatKind::Neg(lit) => {
                if irrefutable {
                    return Err(self.err(
                        Code::E0502,
                        span,
                        "a literal pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                    ));
                }
                match lit {
                    Lit::Int { value, .. } => {
                        let v = self.infer.fresh(&mut self.a.types, Some(LitKind::Int));
                        let neg = matches!(p.kind, PatKind::Neg(_));
                        self.unify_at(span, v, ty)?;
                        Ok(P::Lit(if neg { -(*value as i128) } else { *value as i128 }))
                    }
                    Lit::Float { .. } => {
                        Err(self.err(Code::E0002, span, "float literals are not patterns; use a guard (§7)"))
                    }
                    Lit::Char(c) => {
                        let t = self.a.types.intern(Ty::Char);
                        self.unify_at(span, t, ty)?;
                        Ok(P::Lit(*c as i128))
                    }
                    Lit::Bool(b) => {
                        let t = self.bool_();
                        self.unify_at(span, t, ty)?;
                        Ok(P::Ctor(*b as u32, vec![]))
                    }
                    Lit::Str(s) => {
                        let t = self.a.types.builtin(BuiltinTy::Str, vec![]);
                        self.unify_at(span, t, ty)?;
                        let text: String = s
                            .segments
                            .iter()
                            .map(|x| match x {
                                StrSeg::Text(t) => t.clone(),
                                _ => String::new(),
                            })
                            .collect();
                        Ok(P::Str(text))
                    }
                }
            }
            PatKind::Path(path) => self.bind_ctor_pat(pat, path, &[], ty, irrefutable, borrow, kind, false),
            PatKind::TupleStruct { path, elems } => {
                self.bind_ctor_pat(pat, path, elems, ty, irrefutable, borrow, kind, true)
            }
            PatKind::Tuple(elems) => {
                let s = self.known(ty, span, "matched value")?;
                let Ty::Tuple(ts) = self.ty(s) else {
                    if matches!(self.ty(s), Ty::Error) {
                        return Ok(P::Wild);
                    }
                    let shown = self.display(ty);
                    return Err(self.err(
                        Code::E0401,
                        span,
                        format!("expected a tuple pattern target, found `{shown}`"),
                    ));
                };
                if ts.len() != elems.len() {
                    return Err(self.err(
                        Code::E0401,
                        span,
                        format!("a tuple of {} element(s) cannot match this pattern of {}", ts.len(), elems.len()),
                    ));
                }
                let mut subs = Vec::new();
                for (&el, &t) in elems.iter().zip(&ts) {
                    subs.push(self.bind_pat(el, t, irrefutable, borrow, kind)?);
                }
                Ok(P::Ctor(0, subs))
            }
            PatKind::Struct { path, fields } => {
                let entity = match self.a.resolve_path(self.m, path) {
                    Ok(en) => en,
                    Err(err) => return Err(self.diag(err.into_diagnostic())),
                };
                let d = match entity {
                    Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
                    _ => return Err(self.err(Code::E0401, path.span, "a struct pattern needs a struct")),
                };
                let sd = self.a.def(d).as_struct().unwrap().clone();
                let Fields::Named(defs) = &sd.fields else {
                    return Err(self.err(Code::E0410, path.span, "this struct has no named fields"));
                };
                let args = self.fresh_args(d);
                let named = self.a.types.intern(Ty::Named(d, args.clone()));
                self.unify_at(span, named, ty)?;
                let mut subs = vec![P::Wild; defs.len()];
                let mut seen: Vec<&str> = Vec::new();
                for (name, fp) in fields {
                    let Some(i) = defs.iter().position(|f| f.name == name.name) else {
                        return Err(self.err(
                            Code::E0410,
                            name.span,
                            format!("`{}` has no field `{}`", sd_name(self.a, d), name.name),
                        ));
                    };
                    if seen.contains(&name.name.as_str()) {
                        return Err(self.err(Code::E0410, name.span, format!("field `{}` is given twice", name.name)));
                    }
                    seen.push(&name.name);
                    let ft = self.subst(defs[i].ty, &args);
                    subs[i] = self.bind_pat(*fp, ft, irrefutable, borrow, kind)?;
                }
                let missing: Vec<&str> = defs.iter().map(|f| f.name.as_str()).filter(|n| !seen.contains(n)).collect();
                if !missing.is_empty() {
                    return Err(self.err(
                        Code::E0410,
                        span,
                        format!(
                            "struct patterns name every field; missing {} (use `_`, §7)",
                            missing.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(", ")
                        ),
                    ));
                }
                Ok(P::Ctor(0, subs))
            }
            PatKind::Or(alts) => {
                if irrefutable {
                    return Err(self.err(
                        Code::E0502,
                        span,
                        "an or-pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                    ));
                }
                let outer = self.or_bindings.take();
                self.or_bindings = Some(outer.clone().unwrap_or_default());
                let mut lowered = Vec::new();
                let r = (|| -> R<()> {
                    for &alt in alts {
                        lowered.push(self.bind_pat(alt, ty, false, borrow, kind)?);
                    }
                    Ok(())
                })();
                self.or_bindings = outer;
                r?;
                Ok(P::Or(lowered))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_ctor_pat(
        &mut self,
        pat: PatId,
        path: &Path,
        elems: &[PatId],
        ty: TyId,
        irrefutable: bool,
        borrow: bool,
        kind: LocalKind,
        with_parens: bool,
    ) -> R<P> {
        let span = self.ast.pat(pat).span;
        let entity = match self.a.resolve_path(self.m, path) {
            Ok(en) => en,
            Err(err) => return Err(self.diag(err.into_diagnostic())),
        };
        // (constructor index, field types, number of constructors of the type)
        let (ctor, fields, nctors): (u32, Vec<TyId>, usize) = match entity {
            Entity::Builtin(Builtin::None) => {
                let t = self.fresh();
                let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                self.unify_at(span, opt, ty)?;
                (0, vec![], 2)
            }
            Entity::Builtin(Builtin::Some) => {
                let t = self.fresh();
                let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                self.unify_at(span, opt, ty)?;
                (1, vec![t], 2)
            }
            Entity::Builtin(Builtin::Ok) | Entity::Builtin(Builtin::Err) => {
                let (t, e2) = (self.fresh(), self.fresh());
                let res = self.a.types.builtin(BuiltinTy::Result, vec![t, e2]);
                self.unify_at(span, res, ty)?;
                if matches!(entity, Entity::Builtin(Builtin::Ok)) { (0, vec![t], 2) } else { (1, vec![e2], 2) }
            }
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                let en = self.a.def(d).as_enum().unwrap().clone();
                let named = self.a.types.intern(Ty::Named(d, args.clone()));
                self.unify_at(span, named, ty)?;
                let fields: Vec<TyId> = en.variants[i as usize].fields.iter().map(|&f| self.subst(f, &args)).collect();
                (i, fields, en.variants.len())
            }
            _ => {
                let shown = self.src(path.span);
                return Err(self.err(
                    Code::E0302,
                    path.span,
                    format!(
                        "`{shown}` is not a variant; patterns are literals, bindings, variants, tuples and structs (§7)"
                    ),
                ));
            }
        };
        if irrefutable && nctors > 1 {
            return Err(self.err(
                Code::E0502,
                span,
                "this pattern can fail to match; `let` takes only tuple and struct patterns; use `match` (§7)",
            ));
        }
        if !with_parens && !fields.is_empty() {
            return Err(self.err(
                Code::E0412,
                span,
                format!(
                    "this variant has {} field(s); write the pattern as `{}(...)`",
                    fields.len(),
                    self.src(path.span)
                ),
            ));
        }
        if with_parens && elems.len() != fields.len() {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this variant has {} field(s) but the pattern gives {}", fields.len(), elems.len()),
            ));
        }
        let mut subs = Vec::new();
        for (&el, &t) in elems.iter().zip(&fields) {
            subs.push(self.bind_pat(el, t, irrefutable, borrow, kind)?);
        }
        Ok(P::Ctor(ctor, subs))
    }

    // ------------------------------------------------------------ types in bodies

    /// Lower a type written inside a body (annotations, casts, closure params).
    pub(crate) fn lower_type_expr(&mut self, t: onsa_syntax::ast::TypeId) -> R<TyId> {
        let generics = self.generics.clone();
        let (ty, diags) =
            crate::sig::lower_type_in_body(self.a, self.m, self.ast, self.text, &generics, self.self_ty, self.def, t);
        if let Some(d) = diags.into_iter().next() {
            return Err(self.diag(d));
        }
        Ok(ty)
    }
}

impl<'a> Checker<'a> {
    pub(crate) fn ast_expr(&self, e: ExprId) -> &'a Expr {
        self.ast.expr(e)
    }

    pub(crate) fn body_type(&self, e: ExprId) -> Option<TyId> {
        self.info.expr_types.get(&e).copied()
    }

    pub(crate) fn target_of(&self, e: ExprId) -> Option<Target> {
        self.info.targets.get(&e).cloned()
    }

    pub(crate) fn subst_pub(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        self.subst(ty, args)
    }
}

fn sd_name(a: &Analysis, d: DefId) -> String {
    a.def(d).name.clone()
}

/// `have` implies `want` among the builtin bounds (§6.3): `Ord` ⇒ `PartialOrd`, `Eq`;
/// `Eq` ⇒ `PartialEq`; `Float` ⇒ `Num`; `Num` ⇒ `PartialEq`, `PartialOrd`, `Copy`.
fn implies(have: Bound, want: Bound) -> bool {
    if have == want {
        return true;
    }
    match have {
        Bound::Ord => matches!(want, Bound::PartialOrd | Bound::Eq | Bound::PartialEq),
        Bound::Eq => want == Bound::PartialEq,
        Bound::PartialOrd => want == Bound::PartialEq,
        Bound::Float => matches!(want, Bound::Num | Bound::PartialEq | Bound::PartialOrd | Bound::Copy | Bound::Dup),
        Bound::Num => matches!(want, Bound::PartialEq | Bound::PartialOrd | Bound::Copy | Bound::Dup),
        Bound::Copy => want == Bound::Dup,
        _ => false,
    }
}

pub(crate) fn bound_name(b: Bound) -> &'static str {
    match b {
        Bound::Num => "Num",
        Bound::Float => "Float",
        Bound::PartialEq => "PartialEq",
        Bound::PartialOrd => "PartialOrd",
        Bound::Eq => "Eq",
        Bound::Ord => "Ord",
        Bound::Copy => "Copy",
        Bound::Dup => "Dup",
        Bound::Hash => "Hash",
        Bound::Show => "Show",
        Bound::Default => "Default",
    }
}
