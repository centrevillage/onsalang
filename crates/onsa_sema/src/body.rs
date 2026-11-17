//! Function-body checking (T2-5 .. T2-7, T2-10, T2-11): the inference of spec
//! §4.7 — statement order, unification variables, downward expected types —
//! plus generics instantiation, closures as arguments, the members this
//! version does not give a builtin type (`crate::builtin::MISSING`) and
//! `const` evaluation; the names and the bindings are the names stage's
//! record (`crate::names::body`). Argument modes / exclusivity (T2-8) run
//! after this pass over the tables in [`BodyInfo`]; `rt` (T2-9) and the
//! effects read the record of the uses (`crate::uses`).
//!
//! Where the code is: the tables that the later stages read ([`BodyInfo`],
//! the locals, the targets, the drop points) are in `info`. This module
//! holds the checker (`Checker`, `check_all`), its helpers, its locals and
//! its bounds (`crate::bounds`), and the accessors that the later passes
//! read. The rest of the checking is in a module per part (its doc says
//! which): `entry` (a function body, a `const`), `generics`, `named` (the
//! names the names stage resolved), `expressions`, `calls`, `statements`,
//! `patterns`, and the modules of the candidates and the notes of the
//! errors. The tests are `body_tests.rs`.

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{
    Arg, Ast, BinOp, Block, CallKind, Expr, ExprId, ExprKind, Ident, Lit, MatchArm, Mode, OpGroup, Param, ParamName,
    PatId, PatKind, Path, RangeEnd, RangeHead, StmtId, StmtKind, StrSeg, UnOp,
};

use crate::binding::Bind;
use crate::bounds::Bounds;
use crate::builtin;
use crate::def::{BodyKind, Bound, DefKind, Fields, FnDef, GenericDef, GenericKind};
use crate::deferred::{Deferred, DeferredKind, Verdict};
use crate::exhaust::{Missing, P, Seen};
use crate::infer::{Cause, Fit, Infer, LitKind, Mismatch};
use crate::names::body::{BodyNames, Origin, PatRes, PathRes, StructRes};
use crate::requirement::{ArgumentName, Required};
use crate::resolve::{Builtin, Entity};
use crate::structpat::Written;
use crate::tails::{Diverging, Patch};
use crate::traits::OpNeed;
use crate::ty::{BuiltinTy, FnTy, IntKind, Len, Ty, TyId};
use crate::{Analysis, DefId, Kind, ModId, Package, flatten};

mod arms;
mod call_forms;
mod calls;
mod const_patterns;
mod conversions;
mod entry;
mod expressions;
mod fixed_str;
mod generics;
mod info;
mod mode_note;
mod named;
mod operator_fix;
mod patterns;
mod reach;
mod receivers;
mod removed;
mod reread;
mod statements;
mod trial;

pub(crate) use mode_note::{Found, Merge};
pub(crate) use operator_fix::UNSIGNED_NEGATION;

// ---------------------------------------------------------------- tables

pub use info::{
    BodyInfo, Copied, CopiedWhy, Discard, DropPoint, Dropped, InstId, Instance, LocalId, LocalInfo, LocalKind, RowFrom,
    Taken, Target, TryArms, Unbound, View,
};

// ---------------------------------------------------------------- checker

pub(crate) struct Stop;
pub(crate) type R<T> = Result<T, Stop>;

/// A function or closure body being checked.
pub(crate) struct Frame {
    pub(crate) ret: TyId,
    pub(crate) loop_depth: u32,
}

pub(crate) struct Checker<'a> {
    pub(crate) a: &'a mut Analysis,
    pub(crate) ast: &'a Ast,
    pub(crate) text: &'a str,
    /// The module of the body (its tree, for a candidate read from its tokens).
    pub(crate) module: &'a crate::Module,
    pub(crate) m: ModId,
    pub(crate) def: DefId,
    generics: Vec<GenericDef>,
    self_ty: Option<TyId>,
    pub(crate) infer: Infer,
    pub(crate) frames: Vec<Frame>,
    /// The blocks being checked, innermost last: the node, the block and the
    /// item it is at ([`Checker::open_block`]; what stops at a statement reads
    /// what follows it here, §7).
    pub(crate) blocks: Vec<(ExprId, &'a Block, usize)>,
    pub(crate) info: BodyInfo,
    pub(crate) failed: bool,
    /// Whether a trial of a candidate ran ([`Checker::quietly`]): the body
    /// stops with an error then.
    tried: bool,
    /// The constants of a type no pattern compares found in the pattern
    /// being bound, with their types ([`Checker::bind_pat`]).
    bad_consts: Vec<(Span, TyId)>,
    /// How this read of the body goes.
    how: How<'a>,
    /// The candidates of the E0503 the read stopped at, to be read ([`reread`]).
    tries: Option<reread::Tries>,
    /// Flow mode (T3-1, `flow.rs`): set while checking a flow body.
    pub(crate) flow: Option<crate::flow::FlowCx>,
    /// Checks that wait for a type a later statement decides (`deferred.rs`):
    /// those made since the last statement was checked.
    pub(crate) deferred: Vec<Deferred>,
    /// The items only the end of the body decides (E0405, E0406, E0421), and the
    /// number of items made so far (their order across all lists).
    pub(crate) deferred_end: Vec<Deferred>,
    pub(crate) deferred_count: u32,
    /// The items that wait on a variable, and the limits of §4.4 (`limits.rs`).
    pub(crate) waits: crate::deferred::Waits,
    /// Where an expected type comes from (`an argument of `f``), for the note of
    /// E0416 (§4.5): it names a binding only when that very expected type is the
    /// one unified (an argument, an annotation, the result, a field); every other
    /// binding gets a note with its position alone.
    why: Option<(String, TyId)>,
    /// The anonymous function written directly as the argument being checked
    /// (the one whose E0401 has a candidate, §8.1; not one in parentheses).
    pub(crate) arg_closure: Option<ExprId>,
    /// The argument being checked (without its parentheses) and its mode:
    /// a literal of a generated `In` or `Out` there passes its fields as
    /// views by that mode (§11.6).
    pub(crate) arg_literal: Option<(ExprId, Mode)>,
    /// The candidate of an E0401 at a value of `@param` (§11.7, S-200),
    /// with the span of the value: [`Self::mismatch_at`] puts it on the
    /// E0401 of a literal at that span.
    pub(crate) literal_fix: Option<(Span, Fix)>,
    /// The expected type of the expression being checked is the type of an
    /// earlier part of a merge that joins function types (§4.7, S-1031):
    /// a function found there is joined, not fit ([`Self::check_expr_as`]).
    pub(crate) joining: Option<Merge>,
    /// The view the expression being checked passes on to its tails, as
    /// `joining` is ([`Self::check_tail`]); set by `view_arg` (§5.2, §5.3).
    pub(crate) viewing: Option<Viewing>,
    /// The expressions met under `viewing`, and whether each is a tail: the
    /// `view_arg` that set it records its own once the value is a view.
    pub(crate) view_marks: Vec<(ExprId, bool)>,
    /// A path checked as the base of type arguments written after it, with
    /// the span of both (the text of a wrapping function, S-874).
    pub(crate) written: Option<(ExprId, Span)>,
    /// The names of the body, which the names stage resolved (W4-04).
    pub(crate) names: crate::names::body::BodyNames,
    /// The local of each binding no pattern makes, by its [`Origin`].
    origins: HashMap<Origin, LocalId>,
    /// The locals given their type so far (a branch of a choice after the
    /// first unifies with it, §7).
    typed: Vec<bool>,
    /// The expression of the body, under which a candidate finds the place
    /// of an expression (`slot.rs`).
    root: ExprId,
    /// The names the defs of each module bind, made in the check of the
    /// package where a candidate asks (`removed.rs`).
    bound: &'a mut HashMap<ModId, HashSet<String>>,
}

/// A view passed at a position (§5.3): of the element `elem`, planar of
/// the length `planar` or a `Span`, by `mode` ([`BodyInfo::views`]).
#[derive(Clone, Copy)]
pub(crate) struct Viewing {
    pub elem: TyId,
    pub planar: Option<Len>,
    pub mode: Mode,
}

/// The body of the def `id` the types stage checks, with the type `Self`
/// stands for there and the type the body has: of a function, a test, a
/// `const` and a flow; none of another def and of a declaration with no
/// body.
fn body_of(a: &mut Analysis, id: DefId) -> Option<(Option<TyId>, ExprId, TyId)> {
    let self_ty = a.self_ty_of(id);
    let (self_ty, body, ret) = match a.body_kind(id)? {
        BodyKind::Fn(f) => (self_ty, f.body?, Some(f.ret)),
        BodyKind::Test(body) => (None, body, None),
        BodyKind::Initializer(c) => (self_ty, c.value?, Some(c.ty)),
        // Flow bodies (T3-1): the same inference, in flow mode (`flow.rs`).
        BodyKind::Flow(f) => (None, f.body, Some(f.out)),
    };
    Some((self_ty, body, ret.unwrap_or_else(|| a.types.unit())))
}

/// A body to read, as often as its candidates ask.
struct Job<'p> {
    module: &'p crate::Module,
    m: ModId,
    id: DefId,
    self_ty: Option<TyId>,
    body: ExprId,
    ret: TyId,
    generics: Vec<GenericDef>,
}

/// How a read of a body goes.
#[derive(Clone, Copy)]
pub(crate) enum How<'x> {
    /// The read of the body as it is written, the one that makes candidates.
    First,
    /// The read of its form with a candidate applied ([`reread`]).
    Applied(&'x Patch),
}

/// One read of the body of `job`, from a new state; the checks of the end
/// are the caller's. The tables of the [`Checker`] it gives back are the
/// read's, with the record of the names in them.
fn read_body<'c>(
    a: &'c mut Analysis,
    bound: &'c mut HashMap<ModId, HashSet<String>>,
    job: &Job<'c>,
    names: BodyNames,
    diverging: Diverging,
    how: How<'c>,
) -> Checker<'c> {
    let (locals, origins) = locals_of(a, &names);
    let mut info = BodyInfo { locals, diverging, ..Default::default() };
    info.captures = names.captures.iter().map(|(e, bs)| (*e, bs.iter().map(|b| LocalId(b.0)).collect())).collect();
    let typed = vec![false; info.locals.len()];
    let generics = job.generics.clone();
    let float_params =
        (0..).zip(&generics).filter(|(_, g)| crate::bounds::param_holds(g, Bound::Float)).map(|(i, _)| i).collect();
    let mut ck = Checker {
        a,
        ast: &job.module.parsed.ast,
        text: &job.module.text,
        module: job.module,
        m: job.m,
        def: job.id,
        generics,
        self_ty: job.self_ty,
        infer: Infer::new(float_params),
        frames: Vec::new(),
        blocks: Vec::new(),
        info,
        failed: false,
        tried: false,
        bad_consts: Vec::new(),
        how,
        tries: None,
        deferred: Vec::new(),
        deferred_end: Vec::new(),
        deferred_count: 0,
        waits: Default::default(),
        why: None,
        arg_closure: None,
        arg_literal: None,
        literal_fix: None,
        joining: None,
        viewing: None,
        view_marks: Vec::new(),
        written: None,
        flow: None,
        names,
        origins,
        typed,
        root: job.body,
        bound,
    };
    let check = match ck.a.body_kind(job.id) {
        Some(BodyKind::Fn(_) | BodyKind::Test(_)) => Checker::check_fn_body,
        Some(BodyKind::Initializer(_)) => Checker::check_const,
        Some(BodyKind::Flow(_)) => Checker::check_flow_body,
        None => onsa_diag::internal::bug(Some(ck.a.def(job.id).span), "a body read of a def with no body"),
    };
    check(&mut ck, job.body, job.ret);
    ck
}

/// Check every body of the package and its dependencies.
pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) {
    let flat = flatten(pkg);
    let mut bound = HashMap::default();
    for id in a.new_defs() {
        let def = a.def(id);
        if def.item.is_none() {
            continue;
        }
        // A panic names this declaration (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        let m = def.module;
        let Some(module) = a.modules.source(&flat, m) else { continue };
        let Some((self_ty, body, ret)) = body_of(a, id) else { continue };
        let generics = generics_of(a, id);
        // The body of an item whose unit has a syntax error is not checked
        // (spec §18.1, S-59).
        if a.failed.contains_key(&id) {
            continue;
        }
        // Nor is a body whose unit failed in the names stage (§18.1, S-78: in
        // its signature too), or whose names walk stopped at an error it
        // reported (its record ends there).
        let mut names = a.names.remove(&id).unwrap_or_default();
        if names.reported || a.failures.skips(id, Stage::Types) {
            let body = BodyInfo::default();
            match a.body_kind(id) {
                Some(BodyKind::Flow(_)) => {
                    drop(a.flows.insert(id, crate::flow::FlowInfo { body, ..Default::default() }))
                }
                Some(BodyKind::Fn(_) | BodyKind::Test(_) | BodyKind::Initializer(_)) | None => {
                    drop(a.bodies.insert(id, body))
                }
            }
            a.names.insert(id, names);
            continue;
        }
        // What the body reads and the check does not goes to `read_held` as
        // for a signature (`Analysis::unread_path`, `record_if_held`); it is
        // moved to the body below.
        let held = a.read_held.contains(&id);
        let diverging = std::mem::take(&mut names.diverging);
        let job = Job { module, m, id, self_ty, body, ret, generics };
        let mut ck = read_body(a, &mut bound, &job, names, diverging, How::First);
        ck.names.all_reported(!ck.failed, "the check");
        let fcx = ck.flow.take();
        let mut names = std::mem::take(&mut ck.names);
        let tries = ck.tries.take();
        let mut info = ck.finish();
        if (!held && a.read_held.remove(&id)) || names.read_unread {
            info.read_unread = true;
        }
        // The types stage stops where the walk of the names stopped (`Diverging`,
        // S-692), and a candidate can take that place away: a read of its form
        // would go on into code with no record, so a partial record has no read.
        if let Some(tries) = tries.filter(|_| names.complete) {
            reread::read_again(a, &mut bound, &job, &mut names, &info.diverging, tries);
        }
        a.names.insert(id, names);
        match fcx {
            Some(fcx) => crate::flow::finish_flow(a, module, id, info, fcx),
            None => {
                a.bodies.insert(id, info);
            }
        }
    }
}

/// The generic parameters the body and the signature of `def` see: those of
/// the owner of an initializer (an associated `const`, a default of a
/// field), else its own (a test and a flow have none). The one place of the
/// generics of an initializer.
pub(crate) fn generics_of(a: &Analysis, def: DefId) -> Vec<GenericDef> {
    let d = a.def(def);
    match a.body_kind(def) {
        Some(BodyKind::Initializer(_)) => d.owner.map(|o| a.def(o).generics().to_vec()).unwrap_or_default(),
        Some(BodyKind::Fn(_) | BodyKind::Test(_) | BodyKind::Flow(_)) | None => d.generics().to_vec(),
    }
}

/// The expression of the body of a function, a test or a `const` (the bodies
/// the modes stage reads; not a flow's).
pub(crate) fn root_of(a: &Analysis, def: DefId) -> Option<ExprId> {
    match a.body_kind(def)? {
        BodyKind::Fn(f) => f.body,
        BodyKind::Test(body) => Some(body),
        BodyKind::Initializer(c) => c.value,
        BodyKind::Flow(_) => None,
    }
}

/// The local of each binding no pattern makes (a parameter, a `var`), by
/// its origin: the local of the binding `b` is `LocalId(b.0)`.
pub(crate) fn origins(names: &BodyNames) -> HashMap<Origin, LocalId> {
    (names.bindings.iter().enumerate())
        .filter(|(_, b)| b.sites.is_empty())
        .map(|(i, b)| (b.origin, LocalId(i as u32)))
        .collect()
}

/// The locals of a body, one for each binding of its record (`LocalId(b.0)`
/// for the binding `b`), with the error type until the check gives them
/// theirs and the state of the table of §5.4 with no head (owned, for a
/// binding of a head: settled after the check, [`crate::binding`]); and
/// their [`origins`].
fn locals_of(a: &mut Analysis, names: &BodyNames) -> (Vec<LocalInfo>, HashMap<Origin, LocalId>) {
    let error = a.types.error();
    let mut locals = Vec::new();
    for b in &names.bindings {
        let kind = LocalKind::of(b.kind);
        let (name, span, state) = (b.name.clone(), b.span, Bind::Owned);
        let mut l = LocalInfo { name, span, ty: error, kind, state };
        l.set_state(crate::binding::row(b.kind, None));
        locals.push(l);
    }
    (locals, origins(names))
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

    /// The E0302 of the path at `span` in the body to `d`, an item its flow
    /// does not generate (`Out`, S-1087): of the types stage, as in a type.
    pub(crate) fn generated_at(&mut self, d: DefId, span: Span) -> R<()> {
        match self.a.not_generated_error(d, span) {
            Some(err) => Err(self.diag(err.with_found(self.src(span)))),
            None => Ok(()),
        }
    }

    /// Whether the error type is in `t` (§18.1).
    fn mentions_error(&mut self, t: TyId) -> bool {
        let t = self.infer.resolve(&mut self.a.types, t);
        self.a.types.has_error(t)
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

    /// A name that does not resolve in a body: a diagnostic of the names
    /// stage (spec §18.1), so that it hides a type error of its unit (S-214).
    pub(crate) fn name_err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(Stage::Names, code, span, msg).with_found(self.src(span)))
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
    /// The `for` head checks it first; the ends of a `par` are constant
    /// expressions (§4.5, `crate::constarg`).
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
    /// their type is inferred (the ends of the range of a `for`), so that a
    /// message names the form, not a type variable (`?0`).
    pub(crate) fn non_integer_form(&self, e: ExprId) -> Option<&'static str> {
        match &self.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::Unary { expr: x, .. } => self.non_integer_form(*x),
            ExprKind::Binary { lhs, rhs, .. } => self.non_integer_form(*lhs).or_else(|| self.non_integer_form(*rhs)),
            kind => crate::non_integer_noun(kind),
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
        // A variable left open: its literal kind, else a hole (R-353; no internal `?N`).
        let var_name = |i: u32| self.infer.var_lit(i).map_or("_", LitKind::braced).to_string();
        let param = Analysis::param_names(&self.generics);
        self.a.types.display_vars(r, &|d| self.a.shown_name(d), &param, &var_name)
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
        match self.mismatch_at(span, actual, expected, None) {
            Err(d) => Err(self.diag(d)),
            Ok(_) => Ok(()),
        }
    }

    /// The value of the type `actual` at `span`, of the form `found`, used
    /// where `expected` is expected ([`Infer::fits`], §8.1), or joined with
    /// it ([`Self::joining`]), reporting E0401 on failure. Whether both are
    /// function types.
    pub(crate) fn fit_at(&mut self, span: Span, actual: TyId, expected: TyId, found: Found) -> R<bool> {
        self.mismatch_at(span, actual, expected, Some(found)).map_err(|d| self.diag(d))
    }

    /// Unify, or fit a value of the form `fit` ([`Infer::fits`]: whether
    /// both are function types), giving the E0401 at `span` on failure, for
    /// the caller to report.
    pub(crate) fn mismatch_at(
        &mut self,
        span: Span,
        actual: TyId,
        expected: TyId,
        fit: Option<Found>,
    ) -> Result<bool, Diagnostic> {
        let cause = self.cause(span, Some(expected));
        let types = &mut self.a.types;
        let how = if self.joining.is_some() { Fit::Join } else { Fit::Directed };
        let r = match fit {
            Some(_) => self.infer.fits(types, (actual, expected), how, &cause),
            None => self.infer.unify(types, actual, expected, &cause).map(|()| false),
        };
        let mismatch = match r {
            Ok(both) => return Ok(both),
            Err(m) => m,
        };
        let (a, e) = (self.display(actual), self.display(expected));
        let (found, wanted) = (self.infer.lit_of(&self.a.types, actual), self.infer.lit_of(&self.a.types, expected));
        let text = match (&mismatch, found, wanted) {
            (Mismatch::Literal, Some(k), _) => format!("{} literal cannot have type `{e}`", k.words()),
            (Mismatch::Literal, None, Some(k)) => format!("expected {}, found `{a}`", k.words()),
            // A literal in a part of the types (`fn({integer})`): neither is one.
            _ => format!("expected `{e}`, found `{a}`"),
        };
        let mut d = Diagnostic::new(Stage::Types, Code::E0401, span, text).with_found(self.src(span));
        if let (Mismatch::Literal, Some((at, fix))) = (&mismatch, &self.literal_fix)
            && *at == span
        {
            d = d.with_fix(fix.clone());
        }
        if let (Some(fit), Mismatch::Modes(ps)) = (fit, &mismatch)
            && !self.mentions_error(actual)
            && !self.mentions_error(expected)
        {
            return Err(self.modes_help(d, (fit, self.joining), ps, (actual, expected)));
        }
        // The other side of a float literal (§6.6, S-881).
        let other = match (found, wanted) {
            (Some(LitKind::Float), _) => expected,
            (None, Some(LitKind::Float)) => actual,
            _ => return Err(d),
        };
        let other = self.shallow(other);
        Err(match self.ty(other) {
            Ty::Param(_) => {
                let t = self.display(other);
                d.with_rule(format!(
                    "a float literal is a value of `{t}` only when the bounds of `{t}` include `Float` (§6.6)"
                ))
            }
            _ => d,
        })
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

    /// [`Checker::known`] for an operation whose answer the kind of a literal variable
    /// already decides (a function value called, `.x`, `.0`, `[i]`, the operand of `?`;
    /// S-854): such a variable passes, and the operation reports the error of an
    /// annotated type, named by [`Checker::described`].
    pub(crate) fn known_shape(&mut self, t: TyId, span: Span, what: &str) -> R<TyId> {
        let s = self.shallow(t);
        if self.infer.lit_of(&self.a.types, s).is_some() { Ok(s) } else { self.known(t, span, what) }
    }

    /// A type in the words of a diagnostic: `` `F32` ``, or `an integer` / `a float` for a
    /// literal variable (S-854: the value may be a binding, so not "literal").
    pub(crate) fn described(&mut self, t: TyId) -> String {
        match self.infer.lit_of(&self.a.types, t) {
            Some(k) => k.words().into(),
            None => format!("`{}`", self.display(t)),
        }
    }

    // ------------------------------------------------------------ locals

    /// The local of the binding `origin` names (one no pattern makes).
    pub(crate) fn local_of(&mut self, origin: Origin) -> R<LocalId> {
        match self.origins.get(&origin) {
            Some(&id) => Ok(id),
            // After the name that stopped the walk (§18.1, S-692).
            None => Err(self.held_stop()),
        }
    }

    /// The local the pattern `pat` binds.
    pub(crate) fn local_of_pat(&mut self, pat: PatId) -> R<LocalId> {
        match self.names.pats.get(&pat) {
            Some(PatRes::Bind(b)) => Ok(LocalId(b.0)),
            _ => Err(self.held_stop()),
        }
    }

    /// Give the local `id` its type at `span`, or, when a branch of a choice
    /// before this one gave it one, unify with it (§7).
    pub(crate) fn bind_local(&mut self, id: LocalId, ty: TyId, span: Span) -> R<()> {
        let i = id.0 as usize;
        if std::mem::replace(&mut self.typed[i], true) {
            let lt = self.info.locals[i].ty;
            return self.unify_at(span, ty, lt);
        }
        self.info.locals[i].ty = ty;
        Ok(())
    }

    pub(crate) fn local_ty(&self, id: LocalId) -> TyId {
        self.info.locals[id.0 as usize].ty
    }
}

impl<'a> Checker<'a> {
    pub(crate) fn body_type(&self, e: ExprId) -> Option<TyId> {
        self.info.expr_types.get(&e).copied()
    }

    pub(crate) fn target_of(&self, e: ExprId) -> Option<Target> {
        self.info.targets.get(&e).cloned()
    }
}

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ bounds

    /// The judgments of the bounds under the generics of the body.
    pub(crate) fn bounds(&self) -> Bounds<'_> {
        Bounds { a: self.a, generics: &self.generics }
    }

    pub(crate) fn traits_unknown(&self, t: TyId) -> bool {
        self.bounds().traits_unknown(t)
    }

    pub(crate) fn satisfies(&self, t: TyId, b: Bound) -> bool {
        self.bounds().satisfies(t, b)
    }
}

/// The E0714 of `!` on a call of no `inout self` method (§5.2), wherever it
/// stands: the types stage's, the flow stage's and the modes stage's.
pub(crate) const BANG_ON_NO_INOUT_SELF: &str = "`!` marks `inout self` method calls only (§5.2)";

/// The base of `e` when `e` is a partial view of it (S-217: `xs.slice(a, b)`):
/// a call of a method of std whose type, as `ty` reads it, is a `Span` (std
/// alone returns one, S-861), known by that and not by its name (Q-14). The
/// one rule of the typing (`inout`, S-178) and of the states of the bindings
/// (§5.4).
pub(crate) fn view_base(
    (ast, info, a): (&Ast, &BodyInfo, &Analysis),
    e: ExprId,
    ty: impl Fn(TyId) -> TyId,
) -> Option<ExprId> {
    let ExprKind::Call { callee, .. } = &ast.expr(e).kind else { return None };
    let base = crate::names::body::receiver(ast, *callee)?;
    let span = info.expr_types.get(&e).is_some_and(|&t| matches!(a.types.get(ty(t)), Ty::Builtin(BuiltinTy::Span, _)));
    let std = matches!(info.targets.get(&e), Some(Target::Method { def, .. }) if a.modules.is_std(a.def(*def).module));
    (span && std).then_some(base)
}
