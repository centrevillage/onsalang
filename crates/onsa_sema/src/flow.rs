//! Flow body checking (T3-1; spec §11.2–§11.5, §4.7 last bullet). A flow body
//! is checked with the function-body inference of `body.rs` in "flow mode",
//! then a rate pass assigns every expression a rate, checks the flow rules,
//! and collects the state nodes for lowering (T3-5).
//!
//! # Output tables (`Analysis.flows[flow] = FlowInfo`)
//!
//! - `body: BodyInfo` — the typed body: `expr_types` (resolved), `locals`
//!   (inputs are `LocalKind::Param(Borrow)` locals in input order, `let`
//!   bindings are `LocalKind::Let`, `par` variables `LocalKind::Let`, match
//!   bindings `MatchBind`), `targets`, `pat_locals`, `instances` (generic
//!   instantiations used by the body, for monomorphization). Flow-instance
//!   calls (`saw~(f0)`), the delays `prev~` / `delay~` / `vdelay~` and
//!   `sample_rate()` have no `Target`; use `node_of_expr` / `sample_rate_calls`.
//!   A feedback reference `^y` has the `Target::Local` of `y`.
//! - `expr_rates: HashMap<ExprId, FlowRate>` — the rate of every expression
//!   (`Const < Init < Ctl < Sig`, §11.3).
//! - `local_rates` — the rate of every local (inputs: declared; `let`s: the
//!   rate of the `let`; `par` variables: `Init`; match bindings: the rate of
//!   the scrutinee).
//! - `inputs: Vec<LocalId>` — locals of the inputs, in signature order.
//! - `lets: Vec<FlowLet>` — the top-level `let`s in source order. `state`
//!   is set when the `let` is read at a higher rate than its own (an `Init`
//!   `let` read at `Ctl` / `Sig`, a `Ctl` `let` read at `Sig`; S-05):
//!   those become state fields. `Const`-rate `let`s are never state (they
//!   can be inlined).
//! - `nodes: Vec<Node>` — the stateful nodes in source order with their S-06
//!   names: the `let` name when the node is the whole initializer (`let y1 =
//!   prev~(^y)`, `let src = saw~(f0)`), otherwise `prev_0`, `delay_0`,
//!   `vdelay_0`, `<callee>_0`, numbered per kind in source order over the
//!   whole body. Nodes inside a `par` body are nested in `Node::Par.nodes`.
//! - `node_of_expr` — call expression → index into the node list that
//!   contains it (`nodes`, or the enclosing `Par.nodes`); a `par` expression
//!   maps to its `Par` node.
//! - `sample_rate_at: Option<FlowRate>` — the highest rate at which
//!   `sample_rate()` is read (`None`: never; `Init`: no state field needed;
//!   `Ctl` / `Sig`: store it, S-05). `sample_rate_calls` lists the calls.
//! - `output: ExprId` — the output expression (rate ≤ `Sig`, promoted).
//! - `complete` — `false` when checking stopped at a diagnostic (tables partial).
//!
//! The flow syntax of 0.3 (`at`, `^name`, `prev~`, the omitted `init`,
//! `if~` / `match~`) is read into these tables by [`map`] (W3-10, K-02).

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::{Feature, FlowForm};
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{
    Arg, BinOp, CallKind, ExprId, ExprKind, Ident, Lit, Mode, PatId, PatKind, Path, RangeEnd, RangeHead, StmtId,
    StmtKind, UnOp,
};

use crate::body::{BodyInfo, Checker, Frame, LocalId, LocalKind, R, Target};
use crate::consteval::{self, ConstValue};
use crate::def::{DefKind, FlowInput};
use crate::resolve::Entity;
use crate::ty::{FloatKind, Len, Rate, Ty, TyId};
use crate::{Analysis, DefId, Kind, Module};

#[path = "flow_map.rs"]
pub(crate) mod map;
use crate::flow_names::Delay;

/// Rates with constants as the bottom (§11.3: `定数 < Init < Ctl < Sig`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FlowRate {
    Const,
    Init,
    Ctl,
    Sig,
}

impl FlowRate {
    pub fn name(self) -> &'static str {
        match self {
            FlowRate::Const => "constant",
            FlowRate::Init => Rate::Init.clock(),
            FlowRate::Ctl => Rate::Ctl.clock(),
            FlowRate::Sig => Rate::Sig.clock(),
        }
    }

    pub fn from_rate(r: Rate) -> FlowRate {
        match r {
            Rate::Init => FlowRate::Init,
            Rate::Ctl => FlowRate::Ctl,
            Rate::Sig => FlowRate::Sig,
        }
    }
}

/// A top-level `let` of a flow body.
#[derive(Debug, Clone)]
pub struct FlowLet {
    pub pat: PatId,
    /// Locals bound by the pattern (one for `let y = ...`).
    pub locals: Vec<LocalId>,
    /// `Some` when the pattern is a single name.
    pub name: Option<String>,
    /// Type of the initializer (resolved).
    pub ty: TyId,
    pub rate: FlowRate,
    pub init: ExprId,
    pub span: Span,
    /// Read at a higher rate than its own: becomes a state field (S-05).
    pub state: bool,
}

/// The `init` argument of `prev~` / `delay~` / `vdelay~` (§11.4), or the
/// value of an omitted one (`map`).
#[derive(Debug, Clone)]
pub enum InitArg {
    /// A compile-time constant: no storage needed.
    Const(ConstValue),
    /// An `Init`-rate expression: stored in the state as `<name>.init` (S-06).
    Init(ExprId),
}

/// A stateful node of a flow body (§11.4, §11.5).
#[derive(Debug, Clone)]
pub enum Node {
    Prev { name: String, expr: ExprId, arg: ExprId, init: InitArg, ty: TyId },
    Delay { name: String, expr: ExprId, arg: ExprId, n: u32, init: InitArg, ty: TyId },
    Vdelay { name: String, expr: ExprId, arg: ExprId, d: ExprId, max: u32, init: InitArg, ty: TyId },
    Instance { name: String, expr: ExprId, callee: DefId, args: Vec<ExprId>, span: Span },
    Par { name: String, expr: ExprId, var: LocalId, from: u32, to: u32, body: ExprId, nodes: Vec<Node> },
}

impl Node {
    pub fn name(&self) -> &str {
        match self {
            Node::Prev { name, .. }
            | Node::Delay { name, .. }
            | Node::Vdelay { name, .. }
            | Node::Instance { name, .. }
            | Node::Par { name, .. } => name,
        }
    }

    /// The built-in delay of the node, if it is one.
    pub fn delay(&self) -> Option<Delay> {
        match self {
            Node::Prev { .. } => Some(Delay::Prev),
            Node::Delay { .. } => Some(Delay::Fixed),
            Node::Vdelay { .. } => Some(Delay::Variable),
            Node::Instance { .. } | Node::Par { .. } => None,
        }
    }

    pub fn expr(&self) -> ExprId {
        match self {
            Node::Prev { expr, .. }
            | Node::Delay { expr, .. }
            | Node::Vdelay { expr, .. }
            | Node::Instance { expr, .. }
            | Node::Par { expr, .. } => *expr,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct FlowInfo {
    pub body: BodyInfo,
    pub expr_rates: HashMap<ExprId, FlowRate>,
    pub local_rates: HashMap<LocalId, FlowRate>,
    pub inputs: Vec<LocalId>,
    pub lets: Vec<FlowLet>,
    pub nodes: Vec<Node>,
    pub node_of_expr: HashMap<ExprId, usize>,
    pub sample_rate_at: Option<FlowRate>,
    pub sample_rate_calls: Vec<ExprId>,
    pub output: Option<ExprId>,
    pub complete: bool,
}

// ---------------------------------------------------------------- checker side

/// A `let` of the body, pre-declared before checking (so that `prev~(^y)`
/// can name a later `let`, §11.2).
#[derive(Debug, Clone)]
struct PendingLet {
    stmt: StmtId,
    pat: PatId,
    init: ExprId,
    locals: Vec<LocalId>,
    name: Option<String>,
    /// The value type written on the `let` (`let s: St = …`), lowered when
    /// the `let` is pre-declared: a `^s` above it has that type (§4.7).
    annotation: Option<TyId>,
    span: Span,
}

#[derive(Debug, Clone)]
enum NodeKind {
    /// A built-in delay and its length (`N` of `delay~`, `MAX` of `vdelay~`,
    /// 0 for `prev~`).
    Delay(Delay, u32),
    Instance(DefId),
}

#[derive(Debug, Clone)]
struct NodeCall {
    expr: ExprId,
    kind: NodeKind,
    args: Vec<ExprId>,
    /// The `init` of a delay; `None` with no `init_expr` when it is omitted
    /// (its value is the rate pass's, `map`).
    init: Option<InitArg>,
    init_expr: Option<ExprId>,
    ty: TyId,
}

/// Flow-mode state of the [`Checker`].
#[derive(Debug, Default)]
pub(crate) struct FlowCx {
    /// Block nesting: `let` is allowed at depth 1 only.
    pub(crate) depth: u32,
    inputs: Vec<(LocalId, FlowRate)>,
    pending: Vec<PendingLet>,
    let_of_local: HashMap<LocalId, usize>,
    defined: HashSet<LocalId>,
    /// Nonzero while checking the first argument of a delay, where `^name` may
    /// look back; 0 again in the arguments of an instance there (§11.2).
    lookback: u32,
    /// Nonzero while checking the first argument of a delay, instances included
    /// (a delay there is E0200, K-08).
    delay_arg: u32,
    /// Nonzero while checking the body of a `par` (a `^` there is E0200, R-03).
    par_depth: u32,
    /// The clock of each `e at k` (§11.3), for the rate pass.
    ats: HashMap<ExprId, FlowRate>,
    calls: Vec<NodeCall>,
    /// `par` expression → (variable, from, to).
    pars: HashMap<ExprId, (LocalId, u32, u32)>,
    sample_rate_calls: Vec<ExprId>,
    /// `vdelay` calls: the element type must be a float (checked once resolved).
    float_checks: Vec<(Span, ExprId)>,
    output: Option<ExprId>,
}

/// The builtin of a flow that is no delay (§11.4); the delays are
/// [`Delay`].
const SAMPLE_RATE: &str = "sample_rate";

impl<'a> Checker<'a> {
    fn fcx(&mut self) -> &mut FlowCx {
        self.flow.as_mut().expect("flow mode")
    }

    /// Entry point: declare the inputs, pre-declare the `let`s, check the body.
    pub(crate) fn check_flow_body(&mut self, body: ExprId, out: TyId) {
        self.flow = Some(FlowCx::default());
        self.frames.push(Frame { local_base: 0, ret: out, loop_depth: 0, captures: Vec::new() });
        self.push_scope();
        let r = (|| -> R<()> {
            self.declare_flow_inputs()?;
            self.prescan_lets(body)?;
            self.check_expr(body, Some(out))?;
            Ok(())
        })();
        let _ = r;
        self.pop_scope();
        self.frames.pop();
    }

    fn declare_flow_inputs(&mut self) -> R<()> {
        let inputs: Vec<FlowInput> = self.a.def(self.def).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
        for input in inputs {
            let ident = Ident { name: input.name.clone(), span: input.span };
            let id = self.declare(&ident, input.ty, LocalKind::Param(Mode::Borrow), true)?;
            let rate = FlowRate::from_rate(input.rate);
            self.fcx().inputs.push((id, rate));
        }
        Ok(())
    }

    /// §11.2: the body is `let`s followed by the output expression. Every
    /// `let` binding is declared up front with a fresh type so that the first
    /// argument of `prev` / `delay` / `vdelay` can refer to a later one.
    fn prescan_lets(&mut self, body: ExprId) -> R<()> {
        let span = self.expr(body).span;
        let ExprKind::Block(b) = &self.expr(body).kind else {
            return Err(self.flow_err(
                Code::E0806,
                span,
                "a flow body is a block of `let`s and an output expression (§11.2)",
            ));
        };
        let stmts = b.stmts.clone();
        let tail = b.tail;
        let ast = self.ast;
        for s in stmts {
            let stmt = ast.stmt(s);
            if let StmtKind::Let { pat, init, ty } = stmt.kind {
                let mut locals = Vec::new();
                self.predeclare_pat(pat, &mut locals)?;
                // The annotation types the locals from the start, so that a
                // feedback reference above the `let` reads it (`prev~(^s.l)`).
                let annotation = match ty {
                    Some(t) => {
                        let lowered = self.lower_type_expr(t)?;
                        self.flow_unify_pat(pat, lowered)?;
                        Some(lowered)
                    }
                    // SPEC-GAP(S-395): with no annotation the locals stay unknown
                    // above the `let`, so `^s.l` there is E0420 (§4.7); the type is
                    // not taken from the value of the later `let`.
                    None => None,
                };
                let name = match &ast.pat(pat).kind {
                    PatKind::Bind(id) => Some(id.name.clone()),
                    _ => None,
                };
                let k = self.fcx().pending.len();
                for &l in &locals {
                    self.fcx().let_of_local.insert(l, k);
                }
                self.fcx().pending.push(PendingLet { stmt: s, pat, init, locals, name, annotation, span: stmt.span });
            }
        }
        match tail {
            Some(t) => {
                self.fcx().output = Some(t);
                Ok(())
            }
            None => {
                let end = Span::new(span.file, span.end.saturating_sub(1), span.end);
                Err(self.flow_err(Code::E0806, end, "a flow body ends with its output expression (§11.2)"))
            }
        }
    }

    fn predeclare_pat(&mut self, pat: PatId, locals: &mut Vec<LocalId>) -> R<()> {
        let ast = self.ast;
        match &ast.pat(pat).kind {
            PatKind::Bind(id) => {
                let id = id.clone();
                let t = self.fresh();
                let lid = self.declare(&id, t, LocalKind::Let, false)?;
                self.info.pat_locals.insert(pat, lid);
                locals.push(lid);
                Ok(())
            }
            PatKind::Tuple(elems) | PatKind::TupleStruct { elems, .. } => {
                for &e in &elems.clone() {
                    self.predeclare_pat(e, locals)?;
                }
                Ok(())
            }
            PatKind::Struct { fields, .. } => {
                for (_, fp) in &fields.clone() {
                    self.predeclare_pat(*fp, locals)?;
                }
                Ok(())
            }
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::Or(_) => Ok(()),
        }
    }

    /// E0801: a `let` name read before its definition (its own initializer
    /// included); a later `let` is read only as `^name` (§11.2).
    pub(crate) fn flow_use_local(&mut self, id: LocalId, span: Span) -> R<()> {
        let f = self.fcx();
        if let Some(&k) = f.let_of_local.get(&id)
            && !f.defined.contains(&id)
        {
            let name = self.info.locals[id.0 as usize].name.clone();
            let def_span = self.fcx().pending[k].span;
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Flow, Code::E0801,
                    span,
                    format!(
                        "`{name}` is defined below; names are defined from the top, and a later `let` is read as `^{name}` in the first argument of `prev~` / `delay~` / `vdelay~` (§11.2)"
                    ),
                )
                .with_found(name)
                .with_note(def_span, "defined here"),
            ));
        }
        Ok(())
    }

    /// Statements in flow mode (§11.2, E0806).
    pub(crate) fn check_flow_stmt(&mut self, s: StmtId) -> R<()> {
        let ast = self.ast;
        let stmt = ast.stmt(s);
        let span = stmt.span;
        let what = match &stmt.kind {
            StmtKind::Let { pat, init, .. } => return self.check_flow_let(s, *pat, *init),
            StmtKind::Var { .. } => "`var`; a flow has no mutable variables, state lives in `prev~` / `delay~`",
            StmtKind::Assign { .. } => "assignment; every signal is defined once by `let`",
            StmtKind::For { .. } => "`for`; a flow body has no loops (use `par` to replicate structure)",
            StmtKind::While { .. } => "`while`; a flow body has no loops",
            StmtKind::Break | StmtKind::Continue => "loop control; a flow body has no loops",
            StmtKind::Return(_) => "`return`; the output is the final expression",
            StmtKind::Assert(_) => "`assert`; checks are written as tests on `render` (§11.8)",
            StmtKind::Expr(_) => "an expression statement; a flow body is `let`s followed by one output expression",
        };
        Err(self.flow_err(Code::E0806, span, format!("a flow body cannot contain {what} (§11.2)")))
    }

    fn check_flow_let(&mut self, s: StmtId, pat: PatId, init: ExprId) -> R<()> {
        let span = self.ast.stmt(s).span;
        if self.fcx().depth != 1 {
            return Err(self.flow_err(
                Code::E0806,
                span,
                "`let` is written at the top level of a flow body only; nested blocks hold one expression (§11.2)",
            ));
        }
        let Some(k) = self.fcx().pending.iter().position(|p| p.stmt == s) else {
            return Err(self.flow_err(Code::E0806, span, "unexpected `let` in a flow body"));
        };
        // The annotation is a value type (§11.2), lowered when the `let` was
        // pre-declared; the clock is written on the value (`let ps = p at
        // sample`, §11.3).
        let expected = self.fcx().pending[k].annotation;
        let it = self.check_expr(init, expected)?;
        self.flow_unify_pat(pat, it)?;
        let f = self.fcx();
        let locals = f.pending[k].locals.clone();
        f.defined.extend(locals);
        Ok(())
    }

    /// Unify a `let` pattern with the pre-declared locals (irrefutable patterns only).
    fn flow_unify_pat(&mut self, pat: PatId, ty: TyId) -> R<()> {
        let ast = self.ast;
        let p = ast.pat(pat);
        let span = p.span;
        match &p.kind {
            PatKind::Wild => Ok(()),
            PatKind::Bind(_) => {
                let lid = self.info.pat_locals[&pat];
                let lt = self.local_ty(lid);
                self.unify_at(span, ty, lt)
            }
            PatKind::Tuple(elems) => {
                let elems = elems.clone();
                let s = self.known(ty, span, "matched value")?;
                let Ty::Tuple(ts) = self.ty(s) else {
                    let shown = self.display(ty);
                    return Err(self.flow_err(
                        Code::E0401,
                        span,
                        format!("expected a tuple pattern target, found `{shown}`"),
                    ));
                };
                if ts.len() != elems.len() {
                    return Err(self.flow_err(
                        Code::E0401,
                        span,
                        format!("a tuple of {} element(s) cannot match this pattern of {}", ts.len(), elems.len()),
                    ));
                }
                for (&el, &t) in elems.iter().zip(&ts) {
                    self.flow_unify_pat(el, t)?;
                }
                Ok(())
            }
            PatKind::Struct { path, fields, rest } => {
                let (path, fields, rest) = (path.clone(), fields.clone(), *rest);
                self.struct_pattern(
                    Stage::Flow,
                    span,
                    ty,
                    crate::structpat::Written { path: &path, fields: &fields, rest },
                    &mut |ck, fp, ft, _| ck.flow_unify_pat(fp, ft),
                )?;
                Ok(())
            }
            PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::TupleStruct { .. } | PatKind::Or(_) => {
                Err(self.flow_err(
                    Code::E0502,
                    span,
                    "this pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                ))
            }
        }
    }

    /// Expression forms that flow mode handles itself or forbids (E0806).
    /// `None` hands the expression back to the ordinary checker.
    pub(crate) fn check_flow_expr(&mut self, e: ExprId, expected: Option<TyId>) -> R<Option<TyId>> {
        let expr = self.expr(e);
        let span = expr.span;
        let what = match &expr.kind {
            ExprKind::Closure { .. } => "an anonymous function; flows call named `rt` functions only",
            ExprKind::Handle { .. } => "`handle`; flows have no effects",
            ExprKind::Unsafe(_) => "`unsafe`",
            ExprKind::Try(_) => "`?`; a flow has no error path",
            ExprKind::Move(_) => "`move`; signals are values and are never moved",
            ExprKind::Par { var, range, body } => {
                let (var, range, body) = (var.clone(), *range, *body);
                return self.check_par(e, &var, &range, body, expected).map(Some);
            }
            ExprKind::At { expr: inner, clock } => {
                let (inner, clock) = (*inner, clock.clone());
                return self.check_at(e, inner, &clock, expected).map(Some);
            }
            ExprKind::Feedback(name) => {
                let name = name.clone();
                return self.check_feedback(e, &name).map(Some);
            }
            _ => return Ok(None),
        };
        Err(self.flow_err(Code::E0806, span, format!("a flow body cannot contain {what} (§11.2)")))
    }

    /// `par i in a..<b { e }` (§11.5): `i` is an `Init`-rate `U32`, the result is `[T; b - a]`.
    /// `par i in a..=b` (`b - a + 1` instances) is E0200 until W7-04 (S-224).
    fn check_par(
        &mut self,
        e: ExprId,
        var: &Ident,
        range: &RangeHead,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        self.range_end_forms(range)?;
        let lo = self.flow_const_u32(range.lo, "a `par` bound")?;
        let hi = self.flow_const_u32(range.hi, "a `par` bound")?;
        let end = range.end;
        let (empty, count) = match end {
            RangeEnd::Excluded => (hi <= lo, "`b - a`"),
            RangeEnd::Included => (hi < lo, "`b - a + 1`"),
        };
        if empty {
            let sym = end.symbol();
            return Err(self.flow_err(
                Code::E0808,
                span,
                format!("`par` replicates {count} instances; the bounds `{lo}{sym}{hi}` give none (§11.5)"),
            ));
        }
        if end == RangeEnd::Included {
            return Err(self.closed_range_unsupported(range, Stage::Flow, Feature::InclusiveRangePar));
        }
        let exp_elem = expected.and_then(|t| match self.ty(self.shallow(t)) {
            Ty::Array(el, _) => Some(el),
            _ => None,
        });
        self.push_scope();
        let r = (|| -> R<TyId> {
            let u32 = self.u32();
            let lid = self.declare(var, u32, LocalKind::Let, false)?;
            self.fcx().pars.insert(e, (lid, lo, hi));
            self.fcx().par_depth += 1;
            let r = self.check_expr(body, exp_elem);
            self.fcx().par_depth -= 1;
            r
        })();
        self.pop_scope();
        let t = r?;
        Ok(self.a.types.intern(Ty::Array(t, Len::Const(hi - lo))))
    }

    /// A compile-time `U32` (§11.4, §4.5): the value of a constant
    /// expression. This version computes an integer literal and a `const`
    /// with a literal value; the other constant expressions are E0200 until
    /// W7-02 (R-195), and what is no constant expression is E0417.
    fn flow_const_u32(&mut self, e: ExprId, what: &str) -> R<u32> {
        let span = self.expr(e).span;
        let u32 = self.u32();
        let mut shape = ConstShape { leaves: Vec::new(), arith: true, neg: false, ops: false };
        self.const_shape(e, &mut shape);
        // Each leaf, its names read as the constants of type positions are
        // (`constarg::named`: `N`, `cfg.N`, `I32.BITS`).
        let mut leaves = Vec::new();
        for &l in &shape.leaves {
            let leaf = match &self.expr(l).kind {
                ExprKind::Lit(Lit::Int { value, .. }) => Leaf::Int(*value),
                ExprKind::Path(_) | ExprKind::Field { .. } => match crate::constarg::path_of(self.ast, l) {
                    // A local, or a field of one.
                    Some(p) if self.is_local_head(&p.segments[0].name) => Leaf::Other,
                    Some(p) => {
                        let lspan = self.expr(l).span;
                        match crate::constarg::named(self.a, self.m, self.ast, self.text, &p, lspan) {
                            Ok(Some(v)) => match self.a.resolve_path(self.m, &p) {
                                Ok(Entity::Def(d) | Entity::Member(d)) => Leaf::Value(v, Some(d)),
                                _ => Leaf::Value(v, None),
                            },
                            Ok(None) => Leaf::Other,
                            Err(crate::constarg::ConstErr::Uncomputed(_)) => Leaf::Uncomputed,
                            Err(crate::constarg::ConstErr::Report(d)) => Leaf::Error(d),
                            // A constant whose unit failed (S-59): no diagnostic.
                            Err(crate::constarg::ConstErr::Unknown) => {
                                self.failed = true;
                                return Err(crate::body::Stop);
                            }
                        }
                    }
                    None => Leaf::Other,
                },
                _ => Leaf::Other,
            };
            leaves.push((l, leaf));
        }
        // The names stage first (§18.1): a name that does not resolve.
        if let Some(i) = leaves.iter().position(|(_, l)| matches!(l, Leaf::Error(d) if d.stage == Stage::Names)) {
            let Leaf::Error(d) = leaves.swap_remove(i).1 else { unreachable!() };
            return Err(self.diag(d));
        }
        // The type: an integer (§7, §4.5), with no prefix `-` (S-228).
        if let Some(form) = self.non_integer_form(e) {
            return Err(self.err(Code::E0401, span, format!("{what} is an integer (`U32`); found {form}")));
        }
        if shape.neg {
            return Err(self.err(Code::E0401, span, format!("{what} is a `U32`, which has no prefix `-` (§4.5)")));
        }
        // A constant expression is made of literals and constants (§4.5).
        if !shape.arith || leaves.iter().any(|(_, l)| matches!(l, Leaf::Other)) {
            return Err(self.flow_not_const(span, what));
        }
        if let Some(i) = leaves.iter().position(|(_, l)| matches!(l, Leaf::Error(_))) {
            let Leaf::Error(d) = leaves.swap_remove(i).1 else { unreachable!() };
            return Err(self.diag(d));
        }
        // A literal that no `U32` holds, wherever it is (before the values
        // this version does not compute, S-224).
        if let Some(&(l, _)) = leaves.iter().find(|(_, l)| matches!(l, Leaf::Int(v) if *v > u32::MAX as u64)) {
            let lspan = self.expr(l).span;
            return Err(self.flow_err(Code::E0408, lspan, format!("{what} does not fit in `U32`")));
        }
        // The value: one literal or one constant, in parentheses or not.
        let value = match leaves.as_slice() {
            [(l, Leaf::Int(v))] if !shape.ops => {
                self.record(*l, u32);
                *v as u32
            }
            [(l, Leaf::Value(v, d))] if !shape.ops => {
                self.record(*l, u32);
                if let Some(d) = d {
                    self.info.targets.insert(*l, Target::Const(*d));
                }
                *v
            }
            // The values of the other constant expressions (W7-02, R-195).
            _ => return Err(self.unsupported_in(Stage::Flow, span, Feature::FlowConstExprs, &[])),
        };
        self.record(e, u32);
        Ok(value)
    }

    /// The leaves of `e` under parentheses, prefix `-` and binary operators,
    /// and whether those are the operators of a constant expression (§4.5:
    /// `+ - * / %`).
    fn const_shape(&self, e: ExprId, shape: &mut ConstShape) {
        match &self.expr(e).kind {
            ExprKind::Paren(x) => self.const_shape(*x, shape),
            ExprKind::Unary { op: UnOp::Neg, expr: x } => {
                shape.neg = true;
                self.const_shape(*x, shape);
            }
            ExprKind::Binary { op, lhs, rhs, .. } => {
                shape.ops = true;
                shape.arith &= matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem);
                self.const_shape(*lhs, shape);
                self.const_shape(*rhs, shape);
            }
            _ => shape.leaves.push(e),
        }
    }

    fn flow_not_const(&mut self, span: Span, what: &str) -> crate::body::Stop {
        self.err(
            Code::E0417,
            span,
            format!("{what} must be a constant expression (§4.5), so that the state size is fixed (§11.4)"),
        )
    }

    /// Calls in flow mode (§11.5, §2.6): flow instances `f~(...)`, the delays
    /// `prev~` / `delay~` / `vdelay~`, `sample_rate()`, E0811 / E0812. `None` hands
    /// the call back to the ordinary checker (functions, methods, constructors).
    pub(crate) fn check_flow_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        kind: CallKind,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<Option<TyId>> {
        // `v.(x)` calls a function value; the flow stage reads it with W8-09.
        if matches!(kind, CallKind::Value { .. }) {
            return Ok(None);
        }
        let span = self.expr(e).span;
        // 1. Reserved builtin names (§2.2): the delays are stateful flows
        // (`prev~(…)`), `sample_rate()` is not.
        if let ExprKind::Path(p) = &self.expr(callee).kind
            && p.segments.len() == 1
            && (Delay::named(&p.segments[0].name).is_some() || p.segments[0].name == SAMPLE_RATE)
            && self.lookup_local(&p.segments[0].name).is_none()
        {
            let name = p.segments[0].name.clone();
            return match (Delay::named(&name), kind) {
                (Some(d), CallKind::Flow) => self.check_delay(e, d, args, expected).map(Some),
                (Some(_), CallKind::Plain) => {
                    // `~` goes right after the callee (`prev~(`, §2.6).
                    let at = self.expr(callee).span.end;
                    Err(self.diag(
                        Diagnostic::new(
                            Stage::Flow,
                            Code::E0811,
                            span,
                            format!(
                                "`{name}` is a built-in delay; it holds state and is written `{name}~(…)` (§2.6, §11.4)"
                            ),
                        )
                        .with_found(self.src(span))
                        .with_fix(Fix::insert("add `~`", span.file, at, "~")),
                    ))
                }
                (None, CallKind::Plain) => self.check_sample_rate(e, args).map(Some),
                _ => Err(self.flow_bad_mark(span, kind, &name)),
            };
        }
        // 2. A path that names a flow.
        let chain = match &self.expr(callee).kind {
            ExprKind::Path(p) => Some(p.segments.clone()),
            ExprKind::Field { .. } => self.name_chain(callee).map(|c| c.into_iter().map(|(_, i)| i).collect()),
            _ => None,
        };
        let flow_def = match &chain {
            Some(segs) if !self.is_local_head(&segs[0].name) => {
                let path = Path { segments: segs.clone(), span: self.expr(callee).span };
                match self.a.resolve_path(self.m, &path) {
                    Ok(Entity::Def(d)) | Ok(Entity::Member(d)) if matches!(self.a.def(d).kind, DefKind::Flow(_)) => {
                        Some(d)
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        match (flow_def, kind) {
            (Some(d), CallKind::Flow) => self.check_instance(e, d, args, expected).map(Some),
            (Some(d), CallKind::Plain) => {
                let name = self.a.def(d).name.clone();
                // `~` goes right after the callee (`f~(`, §2.6).
                let at = self.expr(callee).span.end;
                Err(self.diag(
                    Diagnostic::new(
                        Stage::Flow,
                        Code::E0811,
                        span,
                        format!("`{name}` is a flow; calling it creates a stateful instance and needs `~` (§2.6)"),
                    )
                    .with_found(self.src(span))
                    .with_fix(Fix::insert("add `~`", span.file, at, "~")),
                ))
            }
            (Some(d), CallKind::Bang) => {
                let name = self.a.def(d).name.clone();
                Err(self.flow_bad_mark(span, kind, &name))
            }
            (None, CallKind::Flow) => {
                let at = self.expr(callee).span.end;
                let shown = self.src(self.expr(callee).span);
                Err(self.diag(
                    Diagnostic::new(
                        Stage::Flow,
                        Code::E0812,
                        span,
                        format!(
                            "`{shown}` is not a flow; `~` creates a flow instance and is written on flows only (§2.6)"
                        ),
                    )
                    .with_found(self.src(span))
                    .with_fix(Fix::delete("remove `~`", Span::new(span.file, at, at + 1))),
                ))
            }
            (None, _) | (_, CallKind::Value { .. }) => Ok(None),
        }
    }

    fn flow_bad_mark(&mut self, span: Span, kind: CallKind, name: &str) -> crate::body::Stop {
        match kind {
            CallKind::Flow => {
                let fix = self.src(span).replacen("~(", "(", 1);
                self.diag(
                    Diagnostic::new(
                        Stage::Flow,
                        Code::E0812,
                        span,
                        format!(
                            "`{name}` is not a flow; `~` creates a flow instance and is written on flows only (§2.6)"
                        ),
                    )
                    .with_found(self.src(span))
                    .with_fix(Fix::replace("remove `~`", span, fix)),
                )
            }
            _ => {
                let fix = self.src(span).replacen("!(", "(", 1);
                self.diag(
                    Diagnostic::new(Stage::Flow, Code::E0714, span, "`!` marks `inout self` method calls only (§5.2)")
                        .with_found(self.src(span))
                        .with_fix(Fix::replace("remove `!`", span, fix)),
                )
            }
        }
    }

    fn plain_args(&mut self, args: &[Arg]) -> R<()> {
        for a in args {
            if a.mode != Mode::Borrow {
                return Err(self.flow_err(
                    Code::E0806,
                    a.span,
                    "a flow body cannot contain `inout` / `move` arguments; signals are read-only values (§11.2)",
                ));
            }
        }
        Ok(())
    }

    /// `f~(args)` (§11.5): one argument per input, typed by the input's value type.
    fn check_instance(&mut self, e: ExprId, d: DefId, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        if self.a.heading_failed(d) {
            // A flow whose heading a syntax error cut (S-59): its inputs are
            // not known, and the instance is not checked against them.
            self.plain_args(args)?;
            return self.args_of_unknown_callee(args);
        }
        let f = self.a.def(d).as_flow().unwrap().clone();
        let name = self.a.def(d).name.clone();
        if args.len() != f.inputs.len() {
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!("flow `{name}` takes {} input(s) but {} were given", f.inputs.len(), args.len()),
            ));
        }
        self.plain_args(args)?;
        if let Some(exp) = expected {
            self.unify_at(span, f.out, exp)?;
        }
        // An argument of an instance takes no `^` (§11.2), even in the first
        // argument of a delay.
        let lookback = std::mem::take(&mut self.fcx().lookback);
        let r = (|| -> R<Vec<ExprId>> {
            let mut arg_exprs = Vec::new();
            for (arg, input) in args.iter().zip(&f.inputs) {
                self.check_expr(arg.expr, Some(input.ty))?;
                arg_exprs.push(arg.expr);
            }
            Ok(arg_exprs)
        })();
        self.fcx().lookback = lookback;
        let arg_exprs = r?;
        self.fcx().calls.push(NodeCall {
            expr: e,
            kind: NodeKind::Instance(d),
            args: arg_exprs,
            init: None,
            init_expr: None,
            ty: f.out,
        });
        Ok(f.out)
    }

    /// `sample_rate()` (§11.4).
    fn check_sample_rate(&mut self, e: ExprId, args: &[Arg]) -> R<TyId> {
        if !args.is_empty() {
            let span = self.expr(e).span;
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!("`{SAMPLE_RATE}` takes 0 argument(s) but {} were given", args.len()),
            ));
        }
        let f32 = self.a.types.float(FloatKind::F32);
        self.fcx().sample_rate_calls.push(e);
        Ok(f32)
    }

    /// `prev~(e)`, `delay~(e, N)`, `vdelay~(e, d, MAX)`, each with an
    /// optional last `init` (§11.4).
    fn check_delay(&mut self, e: ExprId, d: Delay, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let name = d.name();
        let most = d.init_index() + 1;
        if args.len() != most && args.len() != most - 1 {
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!(
                    "`{name}~` takes {} or {most} arguments (the last, `init`, may be omitted) but {} were given",
                    most - 1,
                    args.len()
                ),
            ));
        }
        self.plain_args(args)?;
        // The first argument may look back to a later `let` with `^` (§11.2).
        self.fcx().lookback += 1;
        self.fcx().delay_arg += 1;
        let r = self.check_expr(args[0].expr, expected);
        self.fcx().lookback -= 1;
        self.fcx().delay_arg -= 1;
        let t = r?;
        let init_expr = args.get(d.init_index()).map(|a| a.expr);
        let len = match d {
            Delay::Prev => 0,
            Delay::Fixed => {
                let n_expr = args[1].expr;
                let n = self.flow_const_u32(n_expr, "the length of `delay~`")?;
                if n == 1 {
                    let mut shown = vec![self.src(self.expr(args[0].expr).span)];
                    shown.extend(init_expr.map(|i| self.src(self.expr(i).span)));
                    let fix = format!("{}~({})", Delay::Prev.name(), shown.join(", "));
                    return Err(self.diag(
                        Diagnostic::new(Stage::Flow, Code::E0807, span, "a 1-sample delay is written `prev~` (§11.4)")
                            .with_found(self.src(span))
                            .with_fix(Fix::replace("write `prev~`", span, fix)),
                    ));
                }
                if n < 2 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(n_expr).span,
                        "`delay~` needs a length of at least 2 (§11.4)",
                    ));
                }
                n
            }
            Delay::Variable => {
                self.check_expr(args[1].expr, Some(t))?;
                let max_expr = args[2].expr;
                let max = self.flow_const_u32(max_expr, "the maximum of `vdelay~`")?;
                if max < 1 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(max_expr).span,
                        "`vdelay~` needs a maximum of at least 1 (§11.4)",
                    ));
                }
                self.fcx().float_checks.push((span, e));
                max
            }
        };
        let kind = NodeKind::Delay(d, len);
        let init = match init_expr {
            Some(i) => {
                self.check_expr(i, Some(t))?;
                Some(match consteval::eval(self, i) {
                    Some(v) => InitArg::Const(v),
                    None => InitArg::Init(i),
                })
            }
            None => None,
        };
        // K-08, R-13: the store of a delay inside the first argument of a
        // delay comes before the outer one reads it (W7-07).
        if self.fcx().delay_arg > 0 {
            return Err(self.unsupported_in(Stage::Flow, span, Feature::NestedDelays, &[]));
        }
        let arg_exprs: Vec<ExprId> = args.iter().map(|a| a.expr).collect();
        self.fcx().calls.push(NodeCall { expr: e, kind, args: arg_exprs, init, init_expr, ty: t });
        Ok(t)
    }
}

// ---------------------------------------------------------------- rate pass

/// After type checking: assign rates, check the flow rules, collect nodes.
pub(crate) fn finish_flow(a: &mut Analysis, module: &Module, id: DefId, body: BodyInfo, fcx: FlowCx) {
    let mut info = FlowInfo {
        inputs: fcx.inputs.iter().map(|(l, _)| *l).collect(),
        sample_rate_calls: fcx.sample_rate_calls.clone(),
        output: fcx.output,
        complete: false,
        ..Default::default()
    };
    if !body.complete {
        info.body = body;
        a.flows.insert(id, info);
        return;
    }
    let mut r = Rater {
        a,
        ast: &module.parsed.ast,
        text: &module.text,
        body: &body,
        fcx: &fcx,
        final_pass: false,
        rates: HashMap::new(),
        local_rates: HashMap::new(),
        let_rates: vec![FlowRate::Const; fcx.pending.len()],
        lets: Vec::new(),
        diag: None,
        node_lists: Vec::new(),
        node_of_expr: HashMap::new(),
        counters: HashMap::new(),
        sample_rate_at: None,
        let_names: HashMap::new(),
        call_of_expr: HashMap::new(),
        branch: 0,
    };
    for (i, c) in fcx.calls.iter().enumerate() {
        r.call_of_expr.insert(c.expr, i);
    }
    for p in &fcx.pending {
        if let Some(n) = &p.name {
            r.let_names.insert(p.init, n.clone());
        }
    }
    // Fixpoint on the `let` rates: a look-back (`prev~(^y)` before `let y`)
    // reads a rate that is only known after its `let` is rated. Rates only go
    // up, and the lattice has four levels, so this converges quickly.
    for _ in 0..6 {
        r.pass();
        let mut changed = false;
        for (i, l) in r.lets.iter().enumerate() {
            changed |= r.let_rates[i] != l.rate;
            r.let_rates[i] = l.rate;
        }
        if !changed {
            break;
        }
    }
    r.final_pass = true;
    r.pass();
    if r.diag.is_none() {
        r.mark_all();
    }
    let diag = r.diag.take();
    info.complete = diag.is_none();
    info.expr_rates = r.rates;
    info.local_rates = r.local_rates;
    info.lets = r.lets;
    info.nodes = r.node_lists.pop().unwrap_or_default();
    info.node_of_expr = r.node_of_expr;
    info.sample_rate_at = r.sample_rate_at;
    info.body = body;
    if let Some(d) = diag {
        a.diagnostics.push(d);
    }
    a.flows.insert(id, info);
}

struct RStop;
type RR<T> = Result<T, RStop>;

struct Rater<'a> {
    a: &'a mut Analysis,
    ast: &'a onsa_syntax::ast::Ast,
    text: &'a str,
    body: &'a BodyInfo,
    fcx: &'a FlowCx,
    /// Diagnostics and nodes are produced in the final pass only.
    final_pass: bool,
    rates: HashMap<ExprId, FlowRate>,
    local_rates: HashMap<LocalId, FlowRate>,
    /// Rates of the `let`s from the previous pass (read by look-backs).
    let_rates: Vec<FlowRate>,
    lets: Vec<FlowLet>,
    diag: Option<Diagnostic>,
    node_lists: Vec<Vec<Node>>,
    node_of_expr: HashMap<ExprId, usize>,
    counters: HashMap<String, u32>,
    sample_rate_at: Option<FlowRate>,
    let_names: HashMap<ExprId, String>,
    call_of_expr: HashMap<ExprId, usize>,
    /// Nonzero inside a branch, a guard or the right side of `&&` / `||` (K-08).
    branch: u32,
}

impl<'a> Rater<'a> {
    fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    fn fail(&mut self, d: Diagnostic) -> RStop {
        if self.final_pass && self.diag.is_none() {
            self.diag = Some(d);
        }
        RStop
    }

    fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) -> RStop {
        let found = self.src(span);
        self.fail(Diagnostic::new(Stage::Flow, code, span, msg).with_found(found))
    }

    fn expr(&self, e: ExprId) -> &'a onsa_syntax::ast::Expr {
        self.ast.expr(e)
    }

    fn display(&self, t: TyId) -> String {
        self.a.display_type(t)
    }

    fn pass(&mut self) {
        self.rates.clear();
        self.local_rates.clear();
        self.lets.clear();
        self.node_lists = vec![Vec::new()];
        self.node_of_expr.clear();
        self.counters.clear();
        self.sample_rate_at = None;
        self.branch = 0;
        for &(l, r) in &self.fcx.inputs {
            self.local_rates.insert(l, r);
        }
        let _ = self.pass_inner();
    }

    fn pass_inner(&mut self) -> RR<()> {
        for k in 0..self.fcx.pending.len() {
            let p = self.fcx.pending[k].clone();
            let rate = self.rate(p.init)?;
            // §11.3: the value type of a signal must be Copy.
            let ty = self.body.expr_types.get(&p.init).copied().unwrap_or_else(|| self.a.types.error());
            if self.final_pass
                && let Some(k) = self.a.kind_of(ty)
                && k != Kind::Copy
            {
                let shown = self.display(ty);
                return Err(self.err(
                    Code::E0810,
                    p.span,
                    format!("the value type of a signal must be Copy; `{shown}` is {} (§11.3)", k.name()),
                ));
            }
            for &l in &p.locals {
                self.local_rates.insert(l, rate);
            }
            self.lets.push(FlowLet {
                pat: p.pat,
                locals: p.locals.clone(),
                name: p.name.clone(),
                ty,
                rate,
                init: p.init,
                span: p.span,
                state: false,
            });
        }
        for &(span, call) in &self.fcx.float_checks {
            let t = self.body.expr_types.get(&call).map(|&t| self.a.types.get(t).clone()).unwrap_or(Ty::Error);
            if self.final_pass && !matches!(t, Ty::Float(_) | Ty::Error) {
                return Err(self.err(
                    Code::E0401,
                    span,
                    "`vdelay~` interpolates and needs a float signal (`F32` / `F64`, §11.4)",
                ));
            }
        }
        if let Some(out) = self.fcx.output {
            self.rate(out)?;
        }
        Ok(())
    }

    fn set(&mut self, e: ExprId, r: FlowRate) -> RR<FlowRate> {
        self.rates.insert(e, r);
        Ok(r)
    }

    fn rate_of_local(&mut self, id: LocalId) -> FlowRate {
        if let Some(&r) = self.local_rates.get(&id) {
            return r;
        }
        // A look-back to a later `let`: its rate from the previous pass.
        match self.fcx.let_of_local.get(&id) {
            Some(&k) => self.let_rates[k],
            None => FlowRate::Const,
        }
    }

    fn rate_target(&mut self, e: ExprId, t: &Target) -> RR<Option<FlowRate>> {
        Ok(Some(match t {
            Target::Local(id) => self.rate_of_local(*id),
            Target::Const(_) | Target::BuiltinConst { .. } | Target::ConstParam(_) | Target::Variant { .. } => {
                FlowRate::Const
            }
            Target::Prelude(_) => FlowRate::Const,
            Target::Fn { .. } | Target::Method { .. } | Target::Value => {
                let span = self.expr(e).span;
                return Err(self.err(
                    Code::E0806,
                    span,
                    "a flow body cannot contain function values; call the function directly (§11.2)",
                ));
            }
            Target::BuiltinMethod { .. } => return Ok(None),
        }))
    }

    /// The rate of an expression (§11.3): the maximum of its operands;
    /// the delays and instances are `Sig`.
    fn rate(&mut self, e: ExprId) -> RR<FlowRate> {
        let expr = self.expr(e);
        let span = expr.span;
        let r = match &expr.kind {
            ExprKind::Lit(_) | ExprKind::Hole | ExprKind::Error | ExprKind::Range(_) => FlowRate::Const,
            ExprKind::Path(_) | ExprKind::Feedback(_) => match self.body.targets.get(&e).cloned() {
                Some(t) => self.rate_target(e, &t)?.unwrap_or(FlowRate::Const),
                None => FlowRate::Const,
            },
            ExprKind::Field { base, .. } => match self.body.targets.get(&e).cloned() {
                Some(t) => match self.rate_target(e, &t)? {
                    Some(r) => r,
                    None => self.rate(*base)?,
                },
                None => self.rate(*base)?,
            },
            ExprKind::Paren(inner) | ExprKind::Cast { expr: inner, .. } | ExprKind::Unary { expr: inner, .. } => {
                self.rate(*inner)?
            }
            ExprKind::At { expr: inner, .. } => self.rate_at(e, *inner)?,
            ExprKind::Move(inner) | ExprKind::Try(inner) | ExprKind::Unsafe(inner) => self.rate(*inner)?,
            ExprKind::Tuple(elems) | ExprKind::Array(elems) => {
                let mut r = FlowRate::Const;
                for &x in elems {
                    r = r.max(self.rate(x)?);
                }
                r
            }
            ExprKind::Repeat { elem, .. } => self.rate(*elem)?,
            ExprKind::Struct { fields, .. } => {
                let mut r = FlowRate::Const;
                for (_, x) in fields {
                    r = r.max(self.rate(*x)?);
                }
                r
            }
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.rate(t)?,
                None => FlowRate::Const,
            },
            ExprKind::If { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, FlowForm::IfTilde)),
            ExprKind::Match { tilde: Some(t), .. } => return Err(self.tilde_branches(*t, FlowForm::MatchTilde)),
            ExprKind::If { cond, then, else_, tilde: None } => {
                let mut r = self.rate(*cond)?;
                self.branch += 1;
                let b = (|| -> RR<FlowRate> {
                    let mut r = self.rate(*then)?;
                    if let Some(el) = else_ {
                        r = r.max(self.rate(*el)?);
                    }
                    Ok(r)
                })();
                self.branch -= 1;
                r = r.max(b?);
                r
            }
            ExprKind::Match { scrutinee, arms, tilde: None } => {
                let sr = self.rate(*scrutinee)?;
                let mut r = sr;
                self.branch += 1;
                let b = (|| -> RR<FlowRate> {
                    let mut r = FlowRate::Const;
                    for arm in arms {
                        self.bind_pat_rates(arm.pat, sr);
                        if let Some(g) = arm.guard {
                            r = r.max(self.rate(g)?);
                        }
                        r = r.max(self.rate(arm.body)?);
                    }
                    Ok(r)
                })();
                self.branch -= 1;
                r = r.max(b?);
                r
            }
            ExprKind::Closure { .. } | ExprKind::Handle { .. } => FlowRate::Const,
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let l = self.rate(*lhs)?;
                let short = Self::short_circuits(*op);
                self.branch += short as u32;
                let r = self.rate(*rhs);
                self.branch -= short as u32;
                l.max(r?)
            }
            ExprKind::TupleIndex { base, .. } | ExprKind::TypeArgs { base, .. } => self.rate(*base)?,
            ExprKind::Index { base, index } => self.rate(*base)?.max(self.rate(*index)?),
            ExprKind::Par { body, .. } => self.rate_par(e, *body)?,
            ExprKind::Call { callee, args, .. } => {
                if let Some(&i) = self.call_of_expr.get(&e) {
                    self.rate_node(e, i)?
                } else if self.fcx.sample_rate_calls.contains(&e) {
                    FlowRate::Init
                } else {
                    self.rate_call(e, *callee, args, span)?
                }
            }
        };
        self.set(e, r)
    }

    fn bind_pat_rates(&mut self, pat: PatId, r: FlowRate) {
        if let Some(&l) = self.body.pat_locals.get(&pat) {
            self.local_rates.insert(l, r);
        }
        match &self.ast.pat(pat).kind {
            PatKind::Tuple(elems) | PatKind::TupleStruct { elems, .. } | PatKind::Or(elems) => {
                for &x in elems {
                    self.bind_pat_rates(x, r);
                }
            }
            PatKind::Struct { fields, .. } => {
                for (_, p) in fields {
                    self.bind_pat_rates(*p, r);
                }
            }
            _ => {}
        }
    }

    /// Ordinary calls (§11.5 table): `rt` effect-free functions apply point-wise;
    /// a non-`rt` function runs at `init` and takes `Init`-or-constant arguments.
    fn rate_call(&mut self, e: ExprId, callee: ExprId, args: &[Arg], span: Span) -> RR<FlowRate> {
        let mut r = FlowRate::Const;
        // Receiver of a method call.
        if let ExprKind::Field { base, .. } = &self.expr(callee).kind
            && self.body.expr_types.contains_key(base)
            && !matches!(self.body.targets.get(&e), Some(Target::Fn { .. }))
        {
            r = r.max(self.rate(*base)?);
        }
        // The arguments a builtin evaluates on some paths only are a branch
        // (`o.unwrap_or(d)`, K-08).
        let lazy = matches!(self.body.targets.get(&e), Some(Target::BuiltinMethod { lazy_args: true, .. }));
        self.branch += lazy as u32;
        let rated = args.iter().try_fold(r, |r, a| Ok(r.max(self.rate(a.expr)?)));
        self.branch -= lazy as u32;
        r = rated?;
        let target = self.body.targets.get(&e).cloned();
        match target {
            Some(Target::Fn { def, .. }) | Some(Target::Method { def, .. }) => {
                let f = self.a.def(def).as_fn().cloned();
                let name = self.a.def(def).name.clone();
                if let Some(f) = f {
                    if self.final_pass && !f.effects.is_empty() {
                        return Err(self.err(
                            Code::E0805,
                            span,
                            format!("`{name}` has effects; a flow calls effect-free functions only (§11.5)"),
                        ));
                    }
                    if self.final_pass && !f.rt && r > FlowRate::Init {
                        return Err(self.err(
                            Code::E0805,
                            span,
                            format!(
                                "`{name}` is not `rt` and takes arguments at the clock `init` or constants only; mark it `rt` or pass values at `init` (§11.5)"
                            ),
                        ));
                    }
                }
                Ok(r.max(FlowRate::Init))
            }
            Some(Target::BuiltinMethod { .. }) => Ok(r.max(FlowRate::Init)),
            Some(Target::Variant { .. }) | Some(Target::Prelude(_)) => Ok(r),
            Some(Target::Value) => Err(self.err(
                Code::E0806,
                span,
                "a flow body cannot contain function values; call the function directly (§11.2)",
            )),
            _ => Ok(r.max(FlowRate::Init)),
        }
    }

    fn next_name(&mut self, kind: &str) -> String {
        let n = self.counters.entry(kind.to_string()).or_insert(0);
        let name = format!("{kind}_{n}");
        *n += 1;
        name
    }

    fn push_node(&mut self, node: Node) {
        let list = self.node_lists.last_mut().expect("node list");
        let idx = list.len();
        self.node_of_expr.insert(node.expr(), idx);
        list.push(node);
    }

    fn node_name(&mut self, e: ExprId, kind: &str) -> String {
        match self.let_names.get(&e) {
            Some(n) => n.clone(),
            None => self.next_name(kind),
        }
    }

    /// The delays and instance calls (§11.4, §11.5, S-04, S-06).
    fn rate_node(&mut self, e: ExprId, i: usize) -> RR<FlowRate> {
        let call = self.fcx.calls[i].clone();
        let span = self.expr(e).span;
        self.stateful_here(span)?;
        match call.kind {
            NodeKind::Instance(callee) => {
                let inputs = self.a.def(callee).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
                let callee_name = self.a.def(callee).name.clone();
                for (arg, input) in call.args.iter().zip(&inputs) {
                    let ra = self.rate(*arg)?;
                    let ri = FlowRate::from_rate(input.rate);
                    if self.final_pass && ra > ri {
                        let aspan = self.expr(*arg).span;
                        return Err(self.err(
                            Code::E0815,
                            aspan,
                            format!(
                                "this argument is at the clock `{}` but the input `{}` of `{callee_name}` is at `{}`; a value is never made slower (§11.3)",
                                ra.name(),
                                input.name,
                                ri.name()
                            ),
                        ));
                    }
                }
                if self.final_pass {
                    let name = self.node_name(e, &callee_name);
                    self.push_node(Node::Instance { name, expr: e, callee, args: call.args.clone(), span });
                }
                Ok(FlowRate::Sig)
            }
            NodeKind::Delay(delay, len) => {
                let what = delay.name();
                let arg = call.args[0];
                let ra = self.rate(arg)?;
                if self.final_pass && ra != FlowRate::Sig {
                    let aspan = self.expr(arg).span;
                    let mut d = Diagnostic::new(
                        Stage::Flow,
                        Code::E0813,
                        aspan,
                        match ra {
                            FlowRate::Const => {
                                format!("the first argument of `{what}~` must be at the clock `sample`; this one is a constant (§11.4)")
                            }
                            _ => format!(
                                "the first argument of `{what}~` must be at the clock `sample`; this one is at `{}` (§11.4)",
                                ra.name()
                            ),
                        },
                    )
                    .with_found(self.src(aspan));
                    // The form to write is `prev~(p at sample)` (§11.4), where
                    // this version holds the promotion (`rate_at`).
                    if ra == FlowRate::Ctl && self.promotes_as_written(arg) {
                        let src = self.src(aspan);
                        d = d.with_note(aspan, format!("write `{what}~({src} at sample)` to delay it per sample"));
                    }
                    return Err(self.fail(d));
                }
                let d_e = (delay == Delay::Variable).then(|| call.args[1]);
                if let Some(d) = d_e {
                    self.rate(d)?;
                }
                if let Some(init_e) = call.init_expr {
                    let ri = self.rate(init_e)?;
                    if self.final_pass && ri > FlowRate::Init {
                        let ispan = self.expr(init_e).span;
                        // The clock of a value is faster than its position (S-147).
                        return Err(self.err(
                            Code::E0815,
                            ispan,
                            format!(
                                "the `init` of `{what}~` must be at the clock `init` or a constant; this one is at `{}` (§11.4)",
                                ri.name()
                            ),
                        ));
                    }
                }
                if self.final_pass {
                    let ty = self.body.expr_types.get(&e).copied().unwrap_or(call.ty);
                    let init = match (&call.init, call.init_expr) {
                        (Some(init), _) => init.clone(),
                        (None, Some(init_e)) => InitArg::Init(init_e),
                        (None, None) => self.default_init(ty, span)?,
                    };
                    let name = self.node_name(e, what);
                    let node = match (delay, d_e) {
                        (Delay::Prev, _) => Node::Prev { name, expr: e, arg, init, ty },
                        (Delay::Fixed, _) => Node::Delay { name, expr: e, arg, n: len, init, ty },
                        (Delay::Variable, Some(d)) => Node::Vdelay { name, expr: e, arg, d, max: len, init, ty },
                        (Delay::Variable, None) => onsa_diag::internal::bug(Some(span), "a `vdelay~` without its `d`"),
                    };
                    self.push_node(node);
                }
                Ok(FlowRate::Sig)
            }
        }
    }

    /// `par i in a..<b { e }` (§11.5): nodes of the body are nested in the `Par` node.
    fn rate_par(&mut self, e: ExprId, body: ExprId) -> RR<FlowRate> {
        self.stateful_here(self.expr(e).span)?;
        let (var, from, to) = self.fcx.pars[&e];
        self.local_rates.insert(var, FlowRate::Init);
        self.node_lists.push(Vec::new());
        let r = self.rate(body);
        let nodes = self.node_lists.pop().unwrap_or_default();
        let r = r?;
        if self.final_pass {
            let name = self.node_name(e, "par");
            self.push_node(Node::Par { name, expr: e, var, from, to, body, nodes });
        }
        Ok(r.max(FlowRate::Init))
    }

    // ------------------------------------------------------------ state marking

    /// Which `let`s are read at a higher rate than their own (S-05), and the
    /// rate at which `sample_rate()` is read.
    fn mark_all(&mut self) {
        for k in 0..self.lets.len() {
            let (init, rate) = (self.lets[k].init, self.lets[k].rate);
            self.mark(init, rate);
        }
        if let Some(out) = self.fcx.output {
            self.mark(out, FlowRate::Sig);
        }
    }

    fn mark(&mut self, e: ExprId, ctx: FlowRate) {
        let expr = self.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(Target::Local(id)) = self.body.targets.get(&e)
                    && let Some(&k) = self.fcx.let_of_local.get(id)
                    && k < self.lets.len()
                    && self.lets[k].rate >= FlowRate::Init
                    && self.lets[k].rate < ctx
                {
                    self.lets[k].state = true;
                }
                if let ExprKind::Field { base, .. } = &expr.kind
                    && !self.body.targets.contains_key(&e)
                {
                    self.mark(*base, ctx);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if let Some(&i) = self.call_of_expr.get(&e) {
                    let call = self.fcx.calls[i].clone();
                    match call.kind {
                        NodeKind::Instance(callee_def) => {
                            let inputs = self.a.def(callee_def).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
                            for (arg, input) in call.args.iter().zip(&inputs) {
                                self.mark(*arg, FlowRate::from_rate(input.rate));
                            }
                        }
                        NodeKind::Delay(delay, _) => {
                            self.mark(call.args[0], FlowRate::Sig);
                            if delay == Delay::Variable {
                                self.mark(call.args[1], FlowRate::Sig);
                            }
                            if let Some(i) = call.init_expr {
                                self.mark(i, FlowRate::Init);
                            }
                        }
                    }
                } else if self.fcx.sample_rate_calls.contains(&e) {
                    self.sample_rate_at = Some(self.sample_rate_at.map_or(ctx, |r| r.max(ctx)));
                } else {
                    self.non_rt_here(e, ctx);
                    if let ExprKind::Field { base, .. } = &self.expr(*callee).kind
                        && self.body.expr_types.contains_key(base)
                    {
                        self.mark(*base, ctx);
                    }
                    for a in args {
                        self.mark(a.expr, ctx);
                    }
                }
            }
            ExprKind::Par { body, .. } => self.mark(*body, ctx),
            _ => {
                for child in children(expr) {
                    self.mark(child, ctx);
                }
            }
        }
    }
}

/// Direct sub-expressions of an expression (for the marking walk).
fn children(expr: &onsa_syntax::ast::Expr) -> Vec<ExprId> {
    match &expr.kind {
        ExprKind::Paren(x) | ExprKind::Move(x) | ExprKind::Try(x) | ExprKind::Unsafe(x) => vec![*x],
        ExprKind::Cast { expr, .. } | ExprKind::Unary { expr, .. } | ExprKind::At { expr, .. } => vec![*expr],
        ExprKind::Tuple(xs) | ExprKind::Array(xs) => xs.clone(),
        ExprKind::Repeat { elem, .. } => vec![*elem],
        ExprKind::Struct { fields, .. } => fields.iter().map(|(_, x)| *x).collect(),
        ExprKind::Block(b) => b.tail.into_iter().collect(),
        ExprKind::If { cond, then, else_, .. } => {
            let mut v = vec![*cond, *then];
            v.extend(*else_);
            v
        }
        ExprKind::Match { scrutinee, arms, .. } => {
            let mut v = vec![*scrutinee];
            for arm in arms {
                v.extend(arm.guard);
                v.push(arm.body);
            }
            v
        }
        ExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        ExprKind::TupleIndex { base, .. } | ExprKind::TypeArgs { base, .. } => vec![*base],
        ExprKind::Index { base, index } => vec![*base, *index],
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        ExprKind::Range(r) => vec![r.lo, r.hi],
        ExprKind::Par { body, .. } => vec![*body],
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Feedback(_)
        | ExprKind::Hole
        | ExprKind::Error
        | ExprKind::Field { .. }
        | ExprKind::Closure { .. }
        | ExprKind::Handle { .. } => Vec::new(),
    }
}

/// The shape of a constant expression of a flow ([`Checker::const_shape`]).
struct ConstShape {
    leaves: Vec<ExprId>,
    /// Every binary operator is one of a constant expression.
    arith: bool,
    /// A prefix `-` (S-228).
    neg: bool,
    /// A binary operator.
    ops: bool,
}

/// A leaf of a constant expression of a flow.
enum Leaf {
    Int(u64),
    /// A constant with a value (and its item, for a `const`).
    Value(u32, Option<crate::DefId>),
    /// A constant whose value this version does not compute (W7-02).
    Uncomputed,
    Error(Diagnostic),
    /// No constant: a local, a function, a call, ...
    Other,
}
