//! Function-body checking (T2-5 .. T2-7, T2-10, T2-11): the inference of spec
//! §4.7 — statement order, unification variables, downward expected types —
//! plus generics instantiation, closures as arguments, builtin methods,
//! scopes (E0304) and `const` evaluation. Argument modes / exclusivity (T2-8)
//! and `rt` (T2-9) run after this pass over the tables in [`BodyInfo`].

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{
    Arg, Ast, BinOp, Block, CallKind, Expr, ExprId, ExprKind, Ident, Lit, MatchArm, Mode, OpGroup, Param, ParamName,
    PatId, PatKind, Path, RangeEnd, RangeHead, StmtId, StmtKind, StrSeg, UnOp,
};

use crate::builtin;
use crate::def::{Bound, DefKind, Fields, FnDef, GenericDef, GenericKind};
use crate::deferred::{Deferred, DeferredKind, Required};
use crate::exhaust::P;
use crate::infer::{Cause, Infer, LitKind, Mismatch};
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
    /// `-e` expressions whose operand, without parentheses, is a numeric literal:
    /// the `-` is a part of the literal's value (§4.7, S-184, S-227). The lowering
    /// folds exactly these (R-03); every other `-` negates a value.
    pub neg_literals: HashSet<ExprId>,
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
    /// Checks that wait for a type a later statement decides (`deferred.rs`).
    pub(crate) deferred: Vec<Deferred>,
    /// The items of `deferred` looked at by the last statement, and the binding
    /// generation then (`check_deferred_now` skips them while nothing was bound).
    pub(crate) deferred_seen: usize,
    pub(crate) deferred_generation: u32,
    /// The items only the end of the body decides (E0405, E0406, E0421), and the
    /// number of items made so far (their order across both lists).
    pub(crate) deferred_end: Vec<Deferred>,
    pub(crate) deferred_count: u32,
    /// Where an expected type comes from (`an argument of `f``), for the note of
    /// E0416 (§4.5): it names a binding only when that very expected type is the
    /// one unified (an argument, an annotation, the result, a field); every other
    /// binding gets a note with its position alone.
    why: Option<(String, TyId)>,
    /// Or-pattern alternative being checked: names bound by the first alternative.
    or_bindings: Option<HashMap<String, LocalId>>,
}

/// Check every body of the package and its dependencies.
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let n = a.defs.len();
    for i in 0..n {
        let id = DefId(i as u32);
        let def = &a.defs[i];
        let Some(item) = def.item else { continue };
        // A panic names this declaration (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
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
        // The body of an item whose unit has a syntax error is not checked
        // (spec §18.1, S-59).
        if a.failed.contains_key(&id) {
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
            deferred: Vec::new(),
            deferred_seen: 0,
            deferred_generation: 0,
            deferred_end: Vec::new(),
            deferred_count: 0,
            why: None,
            or_bindings: None,
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

    /// A diagnostic of the typing pass (stage `Types`).
    pub(crate) fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Types, code, span, msg).with_found(self.src(span)))
    }

    /// A type that holds a struct or enum whose unit failed in the syntax
    /// stage (S-260): its fields and variants are not all known.
    fn mentions_failed(&self, t: TyId) -> bool {
        match self.ty(self.shallow(t)) {
            Ty::Named(d, args) => self.a.partly_read(d) || args.iter().any(|&a| self.mentions_failed(a)),
            Ty::Tuple(ts) | Ty::Builtin(_, ts) => ts.iter().any(|&a| self.mentions_failed(a)),
            Ty::Array(e, _) | Ty::Rate(_, e) => self.mentions_failed(e),
            _ => false,
        }
    }

    /// A path that does not resolve: its diagnostic, or none when the path
    /// goes through a struct or enum whose unit failed in the syntax stage
    /// (its fields and variants are not all known; the check of this body
    /// stops there without a diagnostic).
    // SPEC-GAP(S-260): the members of a failed struct or enum get no diagnostic.
    pub(crate) fn resolve_error(&mut self, path: &onsa_syntax::ast::Path, err: ResolveError) -> Stop {
        if self.a.through_partly_read(self.m, path) {
            self.failed = true;
            return Stop;
        }
        self.diag(err.into_diagnostic())
    }

    /// A name that does not resolve in a body: a diagnostic of the names
    /// stage (spec §18.1), so that it hides a type error of its unit (S-214).
    pub(crate) fn name_err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Names, code, span, msg).with_found(self.src(span)))
    }

    /// E0200 for a type argument written in an expression (`name::[…]`, §4.5)
    /// at the list `span`: the names stage gives the list to its item from
    /// W4-13; until then the list is neither dropped nor read (R-81).
    pub(crate) fn type_args_unsupported(&mut self, span: Span) -> Stop {
        self.unsupported_in(Stage::Names, span, Feature::TypeArgsInExpressions, &[])
    }

    /// E0200 for `feature` (S-224), with the details its phrase takes.
    pub(crate) fn unsupported(&mut self, span: Span, feature: Feature, details: &[&str]) -> Stop {
        self.unsupported_in(Stage::Types, span, feature, details)
    }

    /// E0200 for `feature` found by `stage`.
    pub(crate) fn unsupported_in(&mut self, stage: Stage, span: Span, feature: Feature, details: &[&str]) -> Stop {
        self.diag(feature.diagnostic(stage, span, details).with_found(self.src(span)))
    }

    /// E0200 for a range with its end (`a..=b`, S-224) in the head of a
    /// `for` (W8-03, the types stage) or a `par` (W7-04, the flow stage),
    /// once its ends are checked; it is never read as `a..<b` (R-81).
    pub(crate) fn closed_range_unsupported(&mut self, r: &RangeHead, stage: Stage, feature: Feature) -> Stop {
        let (lo, hi) = (self.expr(r.lo).span, self.expr(r.hi).span);
        self.unsupported_in(stage, Span::new(lo.file, lo.start, hi.end), feature, &[])
    }

    /// E0401 for an end of a range whose form is no integer, whatever its
    /// type is inferred to be (§7, S-257; [`Checker::non_integer_form`]).
    /// The `for` and the `par` heads both check it first.
    pub(crate) fn range_end_forms(&mut self, r: &RangeHead) -> R<()> {
        for e in [r.lo, r.hi] {
            if let Some(form) = self.non_integer_form(e) {
                let span = self.expr(e).span;
                let msg = format!("the ends of a range are integers; found {form} (§7)");
                return Err(self.err(Code::E0401, span, msg));
            }
        }
        Ok(())
    }

    /// The form of a value that is no integer in the operands of `e`
    /// (through parentheses, prefix and binary operators; a cast makes an
    /// integer): a float, string, character or `Bool` literal, a tuple, an
    /// array. The one check of the integer positions that are read before
    /// their type is inferred (the ends of a range, the constants of a
    /// flow), so that a message names the form, not a type variable (`?0`).
    pub(crate) fn non_integer_form(&self, e: ExprId) -> Option<&'static str> {
        match &self.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::Unary { expr: x, .. } => self.non_integer_form(*x),
            ExprKind::Binary { lhs, rhs, .. } => self.non_integer_form(*lhs).or_else(|| self.non_integer_form(*rhs)),
            ExprKind::Lit(Lit::Float { .. }) => Some("a float literal"),
            ExprKind::Lit(Lit::Str(_)) => Some("a string literal"),
            ExprKind::Lit(Lit::Char(_)) => Some("a character literal"),
            ExprKind::Lit(Lit::Bool(_)) => Some("a `Bool` literal"),
            ExprKind::Tuple(_) => Some("a tuple"),
            ExprKind::Array(_) | ExprKind::Repeat { .. } => Some("an array"),
            _ => None,
        }
    }

    /// A diagnostic of the flow checks (`flow.rs`, stage `Flow`).
    pub(crate) fn flow_err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Flow, code, span, msg).with_found(self.src(span)))
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
        let cause = self.cause(span, Some(expected));
        match self.infer.unify(&mut self.a.types, actual, expected, &cause) {
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

    /// The cause of a binding made while unifying at `span` with `expected`.
    pub(crate) fn cause(&self, span: Span, expected: Option<TyId>) -> Cause {
        let why = match (&self.why, expected) {
            (Some((w, t)), Some(e)) if *t == e => Some(w.clone()),
            _ => None,
        };
        Cause::At { span, why }
    }

    /// Check with `why` naming where the expected type `expected` comes from.
    pub(crate) fn with_why<T>(&mut self, why: String, expected: TyId, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let outer = self.why.replace((why, expected));
        let r = f(self);
        self.why = outer;
        r
    }

    /// Check without a reason: a statement, or a branch merged with another one.
    pub(crate) fn without_why<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let outer = self.why.take();
        let r = f(self);
        self.why = outer;
        r
    }

    /// E0420: the operand's type must be known at this point (§4.7).
    pub(crate) fn known(&mut self, t: TyId, span: Span, what: &str) -> R<TyId> {
        let s = self.shallow(t);
        if matches!(self.ty(s), Ty::Var(_)) {
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
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
                        Stage::Types,
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
            self.with_why("the result of the function".into(), ret, |ck| ck.check_expr(body, Some(ret)))?;
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
        // The literals first (E0408, E0401 of `-` on an unsigned type): the evaluation
        // below reads the values they denote.
        if !self.failed {
            self.check_deferred_end();
        }
        if !self.failed
            && let Some(v) = crate::consteval::eval(self, value)
        {
            // A negation of a value is evaluated, not folded into a literal (S-227), so it can
            // leave the type (`-(-2147483648)`, `-LOW`): the evaluation panics, E0419 (§6.6).
            // A stopgap for the value of the whole initializer until the evaluator of W9-03
            // (R-155) checks every operation; an out-of-range value must not reach Core.
            if let Some(k) = self.const_overflow(&v, ty) {
                let span = self.expr(value).span;
                self.err(
                    Code::E0419,
                    span,
                    format!("the compile-time evaluation of this `const` overflows `{}` (§6.6, §3.4)", k.name()),
                );
                return;
            }
            self.a.const_values.insert(self.def, v);
        }
    }

    /// E0406 at the first expression whose type still has a variable that is not a
    /// literal's at the end of the body (§4.7). The origins of `deferred.rs` name the
    /// expression that made a variable; this net catches every variable no origin covers,
    /// so that no open type reaches the lowering.
    // SPEC-GAP(S-262): a variable that only diverging expressions decide (`let x = { return }`,
    // `let x = if c { return } else { return }`) has no type: E0406 at that expression.
    fn open_variable_net(&mut self) {
        let mut open: Vec<(Span, ExprId)> = Vec::new();
        for (&e, &t) in &self.info.expr_types {
            if self.infer.has_open_vars(&self.a.types, t) {
                open.push((self.expr(e).span, e));
            }
        }
        // The first in the source; of nested ones starting together, the outermost.
        open.sort_by_key(|(s, e)| (s.start, std::cmp::Reverse(s.end), e.0));
        if let Some(&(span, _)) = open.first() {
            self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0406,
                    span,
                    "the type of this expression cannot be determined by the end of the function; annotate it (§4.7)",
                )
                .with_found(self.src(span)),
            );
        }
    }

    /// The integer type an evaluated `const` value leaves, looking into arrays, tuples and
    /// structs (the stopgap of `check_const`).
    fn const_overflow(&mut self, v: &crate::consteval::ConstValue, ty: TyId) -> Option<IntKind> {
        use crate::consteval::ConstValue as V;
        match (v, self.ty(ty)) {
            (V::Int(n), Ty::Int(k)) => (!(k.range().0..=k.range().1).contains(n)).then_some(k),
            (V::Array(xs), Ty::Array(e, _)) => xs.iter().find_map(|x| self.const_overflow(x, e)),
            (V::Tuple(xs), Ty::Tuple(ts)) => xs.iter().zip(ts).find_map(|(x, t)| self.const_overflow(x, t)),
            (V::Struct(xs), Ty::Named(d, args)) => {
                let s = self.a.def(d).as_struct().cloned()?;
                let Fields::Named(fs) = &s.fields else { return None };
                let tys: Vec<TyId> = fs.iter().map(|f| self.subst(f.ty, &args)).collect();
                xs.iter().zip(tys).find_map(|(x, t)| self.const_overflow(x, t))
            }
            _ => None,
        }
    }

    /// The checks at the end of the body (`deferred.rs`) and the resolution of the tables.
    fn finish(mut self) -> BodyInfo {
        if !self.failed {
            self.check_deferred_end();
        }
        if !self.failed {
            self.open_variable_net();
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

    /// Record an instantiation made by the expression at `span`. Its arguments
    /// may be decided by a later statement (§4.5, §4.7; S-174): each one is an
    /// origin (E0406 when still open at the end) and carries the requirements of
    /// its parameter (the bounds and the implicit `Dup`, E0416, S-235).
    fn finish_instance(&mut self, def: DefId, args: Vec<TyId>, span: Span) -> R<Option<InstId>> {
        if args.is_empty() {
            return Ok(None);
        }
        let generics = self.all_generics(def);
        // A method's generics start with its `impl`'s (sig.rs): those belong to the `impl`.
        let name = format!("`{}`", self.a.def(def).name);
        let (impl_count, impl_name) = match self.a.def(def).owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) && def != o => {
                let DefKind::Impl(i) = &self.a.def(o).kind else { unreachable!() };
                let head = match self.ty(i.self_ty) {
                    Ty::Named(d, _) => self.a.def(d).name.clone(),
                    _ => self.display(i.self_ty),
                };
                (self.a.def(o).generics().len(), format!("the `impl` of `{head}`"))
            }
            _ => (0, String::new()),
        };
        for (k, (g, &arg)) in generics.iter().zip(&args).enumerate() {
            let owner = if k < impl_count { impl_name.clone() } else { name.clone() };
            let what = match g.kind {
                GenericKind::Const(_) => format!("the const parameter `{}` of {owner}", g.name),
                _ => format!("the type parameter `{}` of {owner}", g.name),
            };
            self.defer(span, arg, DeferredKind::Origin { what });
            if let GenericKind::Type { bounds, dup } = &g.kind {
                let required = |param: &str| Required::Param { param: param.to_string(), owner: owner.clone() };
                if *dup {
                    self.defer(span, arg, DeferredKind::Require { bound: Bound::Dup, what: required(&g.name) });
                }
                for &b in bounds {
                    self.defer(span, arg, DeferredKind::Require { bound: b, what: required(&g.name) });
                }
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
                    return Err(self.resolve_error(&path, err));
                }
            };
            let last = k == n;
            // A def whose heading a syntax error cut (a flow's namespace, S-59):
            // its members are not known; the next segment does not resolve,
            // and `resolve_error` gives no diagnostic (R-71).
            if !last
                && let Entity::Def(d) = entity
                && self.a.heading_failed(d)
            {
                k += 1;
                continue;
            }
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
            return Err(self.name_err(Code::E0302, name.span, "`self` is only available inside a method"));
        }
        let path = Path { segments: vec![name.clone()], span: name.span };
        let entity = match self.a.resolve_path(self.m, &path) {
            Ok(en) => en,
            Err(ResolveError::NotFound { .. }) => {
                return Err(self.name_err(
                    Code::E0302,
                    name.span,
                    format!("cannot find `{}` in this scope", name.name),
                ));
            }
            Err(err) => return Err(self.resolve_error(&path, err)),
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
                    DefKind::Fn(_) if self.a.heading_failed(d) => Ok(Some(self.a.types.error())),
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
                        let espan = self.expr(e).span;
                        let inst = self.finish_instance(d, args, espan)?;
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
                // The whole path (`E.A`), where the variable is made.
                let espan = self.expr(e).span;
                self.finish_instance(d, args, espan)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(Some(t))
            }
            Entity::Builtin(b) => match b {
                Builtin::None => {
                    let t = self.fresh();
                    self.defer(name.span, t, DeferredKind::Origin { what: "the type in `None`".into() });
                    let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                    if let Some(exp) = expected {
                        self.unify_at(name.span, opt, exp)?;
                    }
                    self.info.targets.insert(e, Target::Prelude(b));
                    Ok(Some(opt))
                }
                Builtin::Some | Builtin::Ok | Builtin::Err => {
                    let ret = self.prelude_ctor(b, name.span);
                    let param = match self.ty(ret) {
                        Ty::Builtin(BuiltinTy::Result, a) if b == Builtin::Err => a[1],
                        Ty::Builtin(_, a) => a[0],
                        _ => unreachable!("a prelude constructor makes an `Option` or a `Result`"),
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

    /// The type `Some(_)` / `Ok(_)` / `Err(_)` makes at `span`: the argument's
    /// type, and an origin for the other type argument of `Result` (E0406, §4.7).
    fn prelude_ctor(&mut self, b: Builtin, span: Span) -> TyId {
        let t = self.fresh();
        self.defer(span, t, DeferredKind::Origin { what: format!("the type in `{}`", self.src(span)) });
        match b {
            Builtin::Some => self.a.types.builtin(BuiltinTy::Option, vec![t]),
            Builtin::Ok => {
                let e2 = self.fresh();
                self.defer(span, e2, DeferredKind::Origin { what: "the error type of `Ok`".into() });
                self.a.types.builtin(BuiltinTy::Result, vec![t, e2])
            }
            _ => {
                let ok = self.fresh();
                self.defer(span, ok, DeferredKind::Origin { what: "the value type of `Err`".into() });
                self.a.types.builtin(BuiltinTy::Result, vec![ok, t])
            }
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
                // SPEC-GAP(S-260): a field of a struct whose unit failed in the
                // syntax stage gets no diagnostic, whatever its name (the
                // fields that were not read are not known, R-71).
                if self.a.partly_read(d) {
                    return Ok(self.a.types.error());
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
            // What a syntax error left unread (S-59): the error type, and no
            // diagnostic. The body of a failed item is not checked at all.
            ExprKind::Error => Ok(self.a.types.error()),
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
                self.defer(span, t, DeferredKind::Hole { visible });
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
                    // The element type is the expected one or a later statement's (§2.4, S-226).
                    let el = match exp_elem {
                        Some(el) => el,
                        None => {
                            let el = self.fresh();
                            self.defer(span, el, DeferredKind::Origin { what: "the element type of `[]`".into() });
                            el
                        }
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
                // The element is copied N times: a kind constraint that a later
                // statement may decide (§2.4, §4.7, S-235).
                self.defer(span, et, DeferredKind::Require { bound: Bound::Dup, what: Required::RepeatElement });
                Ok(self.a.types.intern(Ty::Array(et, n)))
            }
            ExprKind::Struct { type_args, .. } if !type_args.is_empty() => {
                Err(self.type_args_unsupported(type_args[0].1.span))
            }
            ExprKind::Struct { path, fields, .. } => self.check_struct_lit(path, fields, expected, self.expr(e).span),
            ExprKind::TypeArgs { args, .. } => Err(self.type_args_unsupported(args.span)),
            ExprKind::Block(b) => self.check_block(b, expected),
            ExprKind::If { cond, then, else_ } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                match else_ {
                    Some(el) => {
                        let t = self.check_expr(*then, expected)?;
                        // Merged with the other branch: not the reason of the outer expectation.
                        self.without_why(|ck| ck.check_expr(*el, Some(t)))?;
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
            ExprKind::Handle { .. } => Err(self.unsupported(span, Feature::EffectHandlers, &[])),
            ExprKind::Unsafe(_) => Err(self.unsupported(span, Feature::Unsafe, &[])),
            ExprKind::Par { .. } => Err(self.err(
                Code::E0401,
                span,
                "`par` replicates flow instances and is only written inside a flow body (§11.5)",
            )),
            &ExprKind::Binary { op, op_span, lhs, rhs } => self.check_binary(op, op_span, lhs, rhs),
            ExprKind::Cast { expr: inner, ty } => {
                let it = self.check_expr(*inner, None)?;
                let from = self.known(it, self.expr(*inner).span, "operand of `as`")?;
                let to = self.lower_type_expr(*ty)?;
                // The error type (what a syntax error left unread, S-59) is not
                // checked: no diagnostic for it (R-71).
                let error = |t: TyId| matches!(self.a.types.get(t), Ty::Error);
                if builtin::cast_allowed(&self.a.types, from, to) || error(from) || error(to) {
                    return Ok(to);
                }
                let (fs, ts) = (self.display(from), self.display(to));
                let mut d = Diagnostic::new(
                    Stage::Types,
                    Code::E0411,
                    span,
                    format!(
                        "`as` only widens without losing information; `{fs}` to `{ts}` needs a conversion method (§3.3)"
                    ),
                )
                .with_found(self.src(span));
                if let Some(m) = builtin::cast_suggestion(&self.a.types, from, to) {
                    let inner_src = self.src(self.expr(*inner).span);
                    d = d.with_fix(Fix::replace(format!("call `{m}`"), span, format!("{inner_src}{m}")));
                }
                Err(self.diag(d))
            }
            ExprKind::Unary { op, expr: inner } => {
                let t = self.check_expr(*inner, None)?;
                let s = self.shallow(t);
                match op {
                    UnOp::Neg => {
                        // A `-` whose operand is a literal is a part of the literal's value
                        // (§4.7, S-184, S-227): the literal's own check covers the sign.
                        if let Some(lit) = self.ast.negated_literal(e) {
                            self.info.neg_literals.insert(e);
                            if let Some(item) = self
                                .deferred
                                .iter_mut()
                                .rev()
                                .find(|d| matches!(d.kind, DeferredKind::IntLit { lit: Some(l), .. } if l == lit))
                            {
                                item.span = span;
                                if let DeferredKind::IntLit { neg, .. } = &mut item.kind {
                                    *neg = true;
                                }
                            }
                            return Ok(t);
                        }
                        match self.ty(s) {
                            Ty::Int(k) if k.signed() => Ok(t),
                            Ty::Float(_) | Ty::Error => Ok(t),
                            Ty::Var(_) if self.infer.lit_of(&self.a.types, s).is_some() => {
                                self.defer(span, t, DeferredKind::UnsignedNeg);
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
                        let cause = self.cause(span, None);
                        if self.infer.unify(&mut self.a.types, a[1], r[1], &cause).is_err() {
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
            // The parser makes a range only as a head; the words of the row
            // that finds one elsewhere (`range_outside_header`).
            ExprKind::Range(_) => {
                let row = onsa_syntax::foreign::row(onsa_syntax::foreign::RowId::RangeOutsideHeader);
                Err(self.diag(Diagnostic::new(Stage::Syntax, Code::E0002, span, row.message).with_rule(row.rule)))
            }
        }
    }

    fn check_lit(&mut self, e: ExprId, lit: &Lit, expected: Option<TyId>) -> R<TyId> {
        match lit {
            Lit::Int { value, .. } => {
                let _ = expected;
                let t = self.infer.fresh(&mut self.a.types, Some(LitKind::Int));
                let span = self.expr(e).span;
                self.defer(span, t, DeferredKind::IntLit { value: *value, neg: false, lit: Some(e) });
                Ok(t)
            }
            Lit::Float { .. } => {
                let t = self.infer.fresh(&mut self.a.types, Some(LitKind::Float));
                let span = self.expr(e).span;
                self.defer(span, t, DeferredKind::FloatLit);
                Ok(t)
            }
            Lit::Char(_) => Ok(self.a.types.intern(Ty::Char)),
            Lit::Bool(_) => Ok(self.bool_()),
            Lit::Str(s) => {
                for seg in &s.segments {
                    if let StrSeg::Interp(path) = seg {
                        let head = &path.segments[0];
                        let Some(id) = self.lookup_local(&head.name) else {
                            return Err(self.name_err(
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

    /// `[e; N]` / array length in an expression (§4.5; the forms are read in `constarg.rs`).
    pub(crate) fn const_len(&mut self, len: ExprId) -> R<Len> {
        let generics = self.generics.clone();
        match crate::constarg::expr(self.a, self.m, self.ast, self.text, &generics, len) {
            Ok((value, constant)) => {
                let u32 = self.u32();
                self.record(len, u32);
                match value {
                    crate::constarg::ConstU32::Value(v) => {
                        if let Some(d) = constant {
                            self.info.targets.insert(len, Target::Const(d));
                        }
                        Ok(Len::Const(v))
                    }
                    crate::constarg::ConstU32::Param(i) => Ok(Len::Param(i)),
                }
            }
            Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => Err(self.diag(d)),
            // A constant whose value was not read (S-59): the check of this
            // body stops there without a diagnostic.
            Err(crate::constarg::ConstErr::Unknown) => {
                self.failed = true;
                Err(Stop)
            }
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
            Err(err) => return Err(self.resolve_error(path, err)),
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
        // The expected type may be a variable a field of an outer literal bound (R-148).
        if let Some(exp) = expected
            && let Ty::Named(d2, exp_args) = self.ty(self.shallow(exp))
            && d2 == d
            && exp_args.len() == args.len()
        {
            for (&a, &x) in args.iter().zip(&exp_args) {
                self.unify_at(span, a, x)?;
            }
        }
        // SPEC-GAP(S-260): the fields of a struct whose unit failed in the
        // syntax stage are not all known: no diagnostic for an unknown or a
        // missing field.
        let failed = self.a.partly_read(d);
        let mut seen: Vec<&str> = Vec::new();
        for (name, value) in fields {
            if seen.contains(&name.name.as_str()) {
                return Err(self.err(Code::E0410, name.span, format!("field `{}` is given twice", name.name)));
            }
            seen.push(&name.name);
            let Some(f) = defs.iter().find(|f| f.name == name.name) else {
                if failed {
                    let error = self.a.types.error();
                    self.check_expr(*value, Some(error))?;
                    continue;
                }
                let shown = self.a.def(d).name.clone();
                return Err(self.err(Code::E0410, name.span, format!("`{shown}` has no field `{}`", name.name)));
            };
            let ft = self.subst(f.ty, &args);
            self.with_why(format!("the field `{}`", name.name), ft, |ck| ck.check_expr(*value, Some(ft)))?;
        }
        let missing: Vec<&str> = defs.iter().map(|f| f.name.as_str()).filter(|n| !seen.contains(n)).collect();
        if !missing.is_empty() && !failed {
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
        self.finish_instance(d, args, span)?;
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
                // The arms after the first are merged with it (not the outer reason).
                let t = if result == expected {
                    self.check_expr(arm.body, result)?
                } else {
                    self.without_why(|ck| ck.check_expr(arm.body, result))?
                };
                if result.is_none() {
                    result = Some(t);
                }
                Ok(())
            })();
            self.pop_scope();
            r?;
        }
        // SPEC-GAP(S-260): the variants of an enum whose unit failed in the
        // syntax stage are not all known; its `match` is not counted.
        if !self.mentions_failed(st)
            && let Some(missing) = self.missing_pattern(&rows, st)
        {
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
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
                                Stage::Types,
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
                        return Err(self.unsupported(n.span, Feature::Effects, &[&n.name]));
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

    /// One operator of a chain (the tree of §3.1): the left operand, the
    /// right one, then what the operator requires of them (S-255).
    fn check_binary(&mut self, op: BinOp, op_span: Span, lhs: ExprId, rhs: ExprId) -> R<TyId> {
        let t = self.check_expr(lhs, None)?;
        Ok(match op.group() {
            OpGroup::And | OpGroup::Or => {
                let bool_ = self.bool_();
                self.unify_at(self.expr(lhs).span, t, bool_)?;
                self.check_expr(rhs, Some(bool_))?;
                bool_
            }
            OpGroup::Comparison => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                let s = self.shallow(t);
                let bound = if matches!(op, BinOp::Eq | BinOp::Ne) { Bound::PartialEq } else { Bound::PartialOrd };
                self.require_operand(s, bound, op, op_span)?;
                self.bool_()
            }
            OpGroup::Bitwise if matches!(op, BinOp::Shl | BinOp::Shr) => {
                let u32 = self.u32();
                self.check_expr(rhs, Some(u32))?;
                let s = self.shallow(t);
                self.require_int(s, op, op_span)?;
                t
            }
            OpGroup::Bitwise => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                let s = self.shallow(t);
                self.require_int(s, op, op_span)?;
                t
            }
            OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder => {
                let rt = self.check_expr(rhs, None)?;
                self.unify_at(self.expr(rhs).span, rt, t)?;
                let s = self.shallow(t);
                if matches!(
                    op,
                    BinOp::WrapAdd | BinOp::WrapSub | BinOp::WrapMul | BinOp::SatAdd | BinOp::SatSub | BinOp::SatMul
                ) {
                    self.require_int(s, op, op_span)?;
                } else {
                    self.require_operand(s, Bound::Num, op, op_span)?;
                }
                t
            }
        })
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
        if let ExprKind::TypeArgs { args, .. } = &self.expr(callee).kind {
            return Err(self.type_args_unsupported(args.span));
        }
        if self.flow.is_some()
            && let Some(t) = self.check_flow_call(e, callee, kind, args, expected)?
        {
            return Ok(t);
        }
        if kind == CallKind::Flow {
            // The `~` comes right after the callee (`f~(`, §2.6).
            let at = self.expr(callee).span.end;
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0812,
                    span,
                    "`~(` creates a flow instance and is only written inside a flow body (§11.5)",
                )
                .with_found(self.src(span))
                .with_fix(Fix::delete("remove `~`", Span::new(span.file, at, at + 1))),
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
                    // A variant or an associated function of a struct or enum a
                    // syntax error cut (S-260): not known, no diagnostic.
                    Err(_) if self.a.through_partly_read(self.m, &path) => {
                        self.failed = true;
                        return Err(Stop);
                    }
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
                        return Err(self.name_err(
                            Code::E0302,
                            name.span,
                            format!("cannot find `{}` in this scope", name.name),
                        ));
                    }
                    Err(err) => return Err(self.resolve_error(&path, err)),
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
            // The `!` comes right after the callee (`f!(`, §2.6).
            let at = self.expr(callee).span.end;
            return Err(self.diag(
                Diagnostic::new(Stage::Types, Code::E0714, span, "`!` marks `inout self` method calls only (§5.2)")
                    .with_found(self.src(span))
                    .with_fix(Fix::delete("remove `!`", Span::new(span.file, at, at + 1))),
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
                if self.a.heading_failed(d) {
                    return self.args_of_unknown_callee(args);
                }
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
                    let at = self.expr(callee).span.end;
                    return Err(self.diag(
                        Diagnostic::new(
                            Stage::Types,
                            Code::E0714,
                            span,
                            "`!` marks `inout self` method calls only (§5.2)",
                        )
                        .with_found(self.src(span))
                        .with_fix(Fix::delete("remove `!`", Span::new(span.file, at, at + 1))),
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
                let ret = self.prelude_ctor(b, span);
                let t = match self.ty(ret) {
                    Ty::Builtin(BuiltinTy::Result, a) if b == Builtin::Err => a[1],
                    Ty::Builtin(_, a) => a[0],
                    _ => unreachable!("a prelude constructor makes an `Option` or a `Result`"),
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
                if self.a.heading_failed(md) {
                    return self.args_of_unknown_callee(args);
                }
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
        if let Some(g) = generic {
            // `Buf.zeroed(4)`: the element type may be decided later (§4.7, S-226), and
            // it must be Copy (§4.5), a kind constraint checked when it is (S-235).
            let what = format!("the element type of `{}`", self.src(self.expr(callee).span));
            self.defer(span, targ, DeferredKind::Origin { what });
            if matches!(g, BuiltinTy::Buf | BuiltinTy::Span) {
                self.defer(span, targ, DeferredKind::Require { bound: Bound::Copy, what: Required::BufElement });
            }
        }
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
    /// The arguments of a call of a function whose heading a syntax error
    /// cut (S-59): each is checked on its own (its errors are the caller's),
    /// and the call is an error, with no diagnostic of its own (R-71).
    pub(crate) fn args_of_unknown_callee(&mut self, args: &[Arg]) -> R<TyId> {
        let error = self.a.types.error();
        for arg in args {
            self.check_expr(arg.expr, Some(error))?;
        }
        Ok(error)
    }

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
                    let callee = self.src(span);
                    let callee = callee.split('(').next().unwrap_or("").trim().to_string();
                    self.with_why(format!("an argument of `{callee}`"), pt, |ck| ck.check_expr(arg.expr, Some(pt)))?;
                }
                Some((elem, planar)) => {
                    let at = self.check_expr(arg.expr, None)?;
                    let at_s = self.known(at, self.expr(arg.expr).span, "argument")?;
                    let aspan = self.expr(arg.expr).span;
                    let cause = self.cause(aspan, None);
                    let ok = match (planar, self.ty(at_s)) {
                        (None, Ty::Array(el, _)) => self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok(),
                        (None, Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a)) => {
                            self.infer.unify(&mut self.a.types, a[0], elem, &cause).is_ok()
                        }
                        (Some(n), Ty::Array(ch, m)) => {
                            let lens_ok =
                                self.infer.shallow_len(&self.a.types, n) == self.infer.shallow_len(&self.a.types, m);
                            lens_ok
                                && match self.ty(self.shallow(ch)) {
                                    Ty::Array(el, _) => self.infer.unify(&mut self.a.types, el, elem, &cause).is_ok(),
                                    Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, a) => {
                                        self.infer.unify(&mut self.a.types, a[0], elem, &cause).is_ok()
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

    /// One statement, then the deferred checks whose type it decided (§4.5, §4.7, S-235).
    pub(crate) fn check_stmt(&mut self, s: StmtId) -> R<()> {
        // A statement sets its own reasons (an annotation, an argument, `return`).
        self.without_why(|ck| if ck.flow.is_some() { ck.check_flow_stmt(s) } else { ck.check_stmt_inner(s) })?;
        self.check_deferred_now()
    }

    fn check_stmt_inner(&mut self, s: StmtId) -> R<()> {
        let stmt = self.ast.stmt(s);
        match &stmt.kind {
            StmtKind::Let { pat, ty, init } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = match ann {
                    Some(t) => {
                        let why = self.annotation_of(*pat);
                        self.with_why(why, t, |ck| ck.check_expr(*init, ann))?
                    }
                    None => self.check_expr(*init, ann)?,
                };
                let borrow = self.is_borrow_source(*init);
                self.bind_pat(*pat, it, true, borrow, LocalKind::Let)?;
                Ok(())
            }
            StmtKind::Var { name, ty, init } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = match ann {
                    Some(t) => {
                        self.with_why(format!("the annotation of `{}`", name.name), t, |ck| ck.check_expr(*init, ann))?
                    }
                    None => self.check_expr(*init, ann)?,
                };
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
                let why = format!("the assignment to `{}`", self.src(self.expr(*target).span));
                self.with_why(why, tt, |ck| ck.check_expr(*value, Some(tt)))?;
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
                        self.with_why("the result of the function".into(), ret, |ck| ck.check_expr(*v, Some(ret)))?;
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

    /// How the note of E0416 names an annotated `let` (`the annotation of `ys``).
    fn annotation_of(&self, pat: PatId) -> String {
        match &self.ast.pat(pat).kind {
            PatKind::Bind(id) => format!("the annotation of `{}`", id.name),
            _ => "the annotation of the `let`".to_string(),
        }
    }

    /// Element type of a `for` iteration and whether the binding is a borrow.
    fn check_iter(&mut self, iter: ExprId, moved: bool) -> R<(TyId, bool)> {
        let span = self.expr(iter).span;
        if let ExprKind::Range(r) = &self.expr(iter).kind {
            let r = *r;
            self.range_end_forms(&r)?;
            let lt = self.check_expr(r.lo, None)?;
            self.check_expr(r.hi, Some(lt))?;
            let s = self.shallow(lt);
            match self.ty(s) {
                Ty::Int(_) | Ty::Error => {}
                Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => {}
                Ty::Var(_) => return Err(self.known(lt, span, "range bound").unwrap_err()),
                _ => {
                    let shown = self.display(lt);
                    let msg = format!("the ends of a range are integers; found `{shown}` (§7)");
                    return Err(self.err(Code::E0401, span, msg));
                }
            }
            self.record(iter, lt);
            if moved {
                return Err(self.err(Code::E0401, span, "`move` applies to collections, not ranges (§7)"));
            }
            if r.end == RangeEnd::Included {
                // Until the loop that ends at the type's maximum (W8-03).
                return Err(self.closed_range_unsupported(&r, Stage::Types, Feature::InclusiveRangeFor));
            }
            return Ok((lt, false));
        }
        let it = self.check_expr(iter, None)?;
        let it = self.known(it, span, "iterated value")?;
        match self.ty(it) {
            Ty::Array(el, _) => Ok((el, !moved)),
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, a) => Ok((a[0], !moved)),
            Ty::Builtin(BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Str, _) => {
                Err(self.unsupported(span, Feature::Iteration, &[]))
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
                        // Unified with the subject's type argument like an operand of `==`,
                        // and range-checked when that is decided (§4.7, §7; S-185, S-226).
                        let v = self.infer.fresh(&mut self.a.types, Some(LitKind::Int));
                        let neg = matches!(p.kind, PatKind::Neg(_));
                        self.defer(span, v, DeferredKind::IntLit { value: *value, neg, lit: None });
                        self.unify_at(span, v, ty)?;
                        Ok(P::Lit(if neg { -(*value as i128) } else { *value as i128 }))
                    }
                    // The parser refuses a float literal in a pattern (the
                    // table of the forms of other languages, S-252).
                    Lit::Float { .. } => {
                        onsa_diag::internal::bug(Some(span), "a float literal pattern after the parse")
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
                    Err(err) => return Err(self.resolve_error(path, err)),
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
                // SPEC-GAP(S-260): as for the fields of a struct literal.
                let failed = self.a.partly_read(d);
                for (name, fp) in fields {
                    let Some(i) = defs.iter().position(|f| f.name == name.name) else {
                        if failed {
                            let error = self.a.types.error();
                            self.bind_pat(*fp, error, irrefutable, borrow, kind)?;
                            continue;
                        }
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
                if !missing.is_empty() && !failed {
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
            Err(err) => return Err(self.resolve_error(path, err)),
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
                return Err(self.name_err(
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
