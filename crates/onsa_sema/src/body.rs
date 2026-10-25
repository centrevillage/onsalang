//! Function-body checking (T2-5 .. T2-7, T2-10, T2-11): the inference of spec
//! §4.7 — statement order, unification variables, downward expected types —
//! plus generics instantiation, closures as arguments, builtin methods,
//! scopes (E0304) and `const` evaluation. Argument modes / exclusivity (T2-8)
//! and `rt` (T2-9) run after this pass over the tables in [`BodyInfo`].
//!
//! Where the code is: this module holds the tables ([`BodyInfo`], the locals,
//! the targets), the checker (`Checker`, `check_all`), its helpers and
//! scopes, the accessors that the later passes read, and `bound_name`. The
//! rest of the checking is in a module per part, each an `impl` of
//! `Checker`: `entry` (a function body, a `const`), `bounds`, `generics`,
//! `names`, `expressions`, `calls`, `statements` and `patterns`. The tests
//! are `body_tests.rs`.

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::{Feature, FlowForm};
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
use crate::structpat::Written;
use crate::ty::{BuiltinTy, FnTy, IntKind, Len, Ty, TyId};
use crate::{Analysis, DefId, Kind, ModId, Package, flatten};

mod bounds;
mod calls;
mod entry;
mod expressions;
mod generics;
mod names;
mod patterns;
mod statements;

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
        /// [`crate::builtin::MethodSig::lazy_args`].
        lazy_args: bool,
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
            Ty::Array(e, _) => self.mentions_failed(e),
            _ => false,
        }
    }

    /// A path that does not resolve: its diagnostic, or none when the path
    /// goes through a struct or enum whose unit failed in the syntax stage
    /// (its fields and variants are not all known) or names what the names
    /// stage holds as an error (§18.1, S-462, S-675): the check of this body
    /// stops there without a diagnostic, and the body is not complete.
    // SPEC-GAP(S-260): the members of a failed struct or enum get no diagnostic.
    pub(crate) fn resolve_error(&mut self, path: &onsa_syntax::ast::Path, err: ResolveError) -> Stop {
        if err == ResolveError::Failed || self.a.through_partly_read(self.m, path) {
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
    /// W5-10; until then the list is neither dropped nor read (R-81).
    pub(crate) fn type_args_unsupported(&mut self, span: Span) -> Stop {
        self.unsupported_in(Stage::Names, span, Feature::TypeArgsInExpressions, &[])
    }

    /// E0200 for `feature` (S-224), with the details its phrase takes.
    pub(crate) fn unsupported(&mut self, span: Span, feature: Feature, details: &[&str]) -> Stop {
        self.unsupported_in(Stage::Types, span, feature, details)
    }

    /// E0200 for a form of the flow syntax outside a flow body (E0821 from
    /// W4-12): `crate::flow_syntax` stops its item first, so this is reached
    /// only through a gap in it.
    pub(crate) fn flow_form(&mut self, span: Span, form: FlowForm) -> Stop {
        self.diag(form.outside_flow(Stage::Names, span).with_found(self.src(span)))
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

    /// Lower a type written inside a body (annotations, casts, closure params).
    pub(crate) fn lower_type_expr(&mut self, t: onsa_syntax::ast::TypeId) -> R<TyId> {
        let generics = self.generics.clone();
        let (ty, diags) =
            crate::sig::lower_type_in_body(self.a, self.m, self.ast, self.text, &generics, self.self_ty, self.def, t);
        if let Some(d) = diags.into_iter().next() {
            return Err(self.diag(d));
        }
        // An error with no diagnostic: a name held as an error (§18.1), or a
        // member of a def a syntax error cut (S-260). The check stops there.
        // SPEC-GAP(S-690): the rest of the body is not checked.
        if self.holds_error(ty) {
            self.failed = true;
            return Err(Stop);
        }
        Ok(ty)
    }

    fn holds_error(&self, t: TyId) -> bool {
        match self.ty(t) {
            Ty::Error => true,
            Ty::Named(_, ts) | Ty::Tuple(ts) | Ty::Builtin(_, ts) => ts.iter().any(|&a| self.holds_error(a)),
            Ty::Array(e, _) => self.holds_error(e),
            _ => false,
        }
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
        Bound::Copy => onsa_syntax::foreign::COPY,
        Bound::Dup => onsa_syntax::foreign::DUP,
        Bound::Hash => "Hash",
        Bound::Show => "Show",
        Bound::Default => "Default",
    }
}
