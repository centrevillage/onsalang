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
//!   calls (`saw~(f0)`) and the builtins `prev` / `delay` / `vdelay` /
//!   `sample_rate` have no `Target`; use `node_of_expr` / `sample_rate_calls`.
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
//!   prev(y, 0.0)`, `let src = saw~(f0)`), otherwise `prev_0`, `delay_0`,
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

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind, Ident, Lit, Mode, PatId, PatKind, Path, StmtId, StmtKind};

use crate::body::{BodyInfo, Checker, Frame, LocalId, LocalKind, R, Target};
use crate::consteval::{self, ConstValue};
use crate::def::{DefKind, Fields, FlowInput};
use crate::resolve::Entity;
use crate::ty::{FloatKind, Len, Rate, Ty, TyId};
use crate::{Analysis, DefId, Kind, Module};

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
            FlowRate::Init => "Init",
            FlowRate::Ctl => "Ctl",
            FlowRate::Sig => "Sig",
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
    /// Rate written in the annotation (`let ps: Sig[F32] = p`), if any.
    pub annotated: Option<FlowRate>,
    pub init: ExprId,
    pub span: Span,
    /// Read at a higher rate than its own: becomes a state field (S-05).
    pub state: bool,
}

/// The `init` argument of `prev` / `delay` / `vdelay` (§11.4).
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

/// A `let` of the body, pre-declared before checking (so that `prev(y, 0.0)`
/// can name a later `let`, §11.2).
#[derive(Debug, Clone)]
struct PendingLet {
    stmt: StmtId,
    pat: PatId,
    init: ExprId,
    locals: Vec<LocalId>,
    name: Option<String>,
    annotated: Option<FlowRate>,
    span: Span,
}

#[derive(Debug, Clone)]
enum NodeKind {
    Prev,
    Delay(u32),
    Vdelay(u32),
    Instance(DefId),
}

#[derive(Debug, Clone)]
struct NodeCall {
    expr: ExprId,
    kind: NodeKind,
    args: Vec<ExprId>,
    init: Option<InitArg>,
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
    /// > 0 while checking the first argument of `prev` / `delay` / `vdelay`.
    lookback: u32,
    calls: Vec<NodeCall>,
    /// `par` expression → (variable, from, to).
    pars: HashMap<ExprId, (LocalId, u32, u32)>,
    sample_rate_calls: Vec<ExprId>,
    /// `vdelay` calls: the element type must be a float (checked once resolved).
    float_checks: Vec<(Span, ExprId)>,
    output: Option<ExprId>,
}

const BUILTINS: [&str; 4] = ["prev", "delay", "vdelay", "sample_rate"];

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
            if let StmtKind::Let { pat, init, .. } = stmt.kind {
                let mut locals = Vec::new();
                self.predeclare_pat(pat, &mut locals)?;
                let name = match &ast.pat(pat).kind {
                    PatKind::Bind(id) => Some(id.name.clone()),
                    _ => None,
                };
                let k = self.fcx().pending.len();
                for &l in &locals {
                    self.fcx().let_of_local.insert(l, k);
                }
                self.fcx().pending.push(PendingLet {
                    stmt: s,
                    pat,
                    init,
                    locals,
                    name,
                    annotated: None,
                    span: stmt.span,
                });
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
    /// included), outside the first argument of `prev` / `delay` / `vdelay`.
    pub(crate) fn flow_use_local(&mut self, id: LocalId, span: Span) -> R<()> {
        let f = self.fcx();
        if let Some(&k) = f.let_of_local.get(&id)
            && !f.defined.contains(&id)
            && f.lookback == 0
        {
            let name = self.info.locals[id.0 as usize].name.clone();
            let def_span = self.fcx().pending[k].span;
            return Err(self.diag(
                Diagnostic::new(
                    Stage::Flow, Code::E0801,
                    span,
                    format!(
                        "`{name}` is defined below; only the first argument of `prev`/`delay`/`vdelay` may refer to a later or current `let` (§11.2)"
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
            StmtKind::Let { pat, ty, init } => return self.check_flow_let(s, *pat, *ty, *init),
            StmtKind::Var { .. } => "`var`; a flow has no mutable variables, state lives in `prev` / `delay`",
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

    fn check_flow_let(&mut self, s: StmtId, pat: PatId, ty: Option<onsa_syntax::ast::TypeId>, init: ExprId) -> R<()> {
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
        // Annotation: `Sig[F32]` promotes (§11.3); a plain type only constrains the value.
        let (annotated, expected) = match ty {
            Some(t) => {
                let lowered = self.lower_type_expr(t)?;
                match self.ty(lowered) {
                    Ty::Rate(r, inner) => (Some(FlowRate::from_rate(r)), Some(inner)),
                    _ => (None, Some(lowered)),
                }
            }
            None => (None, None),
        };
        let it = self.check_expr(init, expected)?;
        self.flow_unify_pat(pat, it)?;
        let f = self.fcx();
        f.pending[k].annotated = annotated;
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
            PatKind::Struct { path, fields } => {
                let (path, fields) = (path.clone(), fields.clone());
                let entity = match self.a.resolve_path(self.m, &path) {
                    Ok(en) => en,
                    Err(err) => return Err(self.diag(err.into_diagnostic())),
                };
                let d = match entity {
                    Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
                    _ => return Err(self.flow_err(Code::E0401, path.span, "a struct pattern needs a struct")),
                };
                let sd = self.a.def(d).as_struct().unwrap().clone();
                let Fields::Named(defs) = &sd.fields else {
                    return Err(self.flow_err(Code::E0410, path.span, "this struct has no named fields"));
                };
                let args = self.fresh_args(d);
                let named = self.a.types.intern(Ty::Named(d, args.clone()));
                self.unify_at(span, named, ty)?;
                let mut seen: Vec<String> = Vec::new();
                for (name, fp) in &fields {
                    let Some(fd) = defs.iter().find(|f| f.name == name.name) else {
                        return Err(self.flow_err(
                            Code::E0410,
                            name.span,
                            format!("`{}` has no field `{}`", self.a.def(d).name, name.name),
                        ));
                    };
                    if seen.contains(&name.name) {
                        return Err(self.flow_err(
                            Code::E0410,
                            name.span,
                            format!("field `{}` is given twice", name.name),
                        ));
                    }
                    seen.push(name.name.clone());
                    let ft = self.subst_pub(fd.ty, &args);
                    self.flow_unify_pat(*fp, ft)?;
                }
                let missing: Vec<&str> =
                    defs.iter().map(|f| f.name.as_str()).filter(|n| !seen.iter().any(|s| s == n)).collect();
                if !missing.is_empty() {
                    return Err(self.flow_err(
                        Code::E0410,
                        span,
                        format!(
                            "struct patterns name every field; missing {} (use `_`, §7)",
                            missing.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(", ")
                        ),
                    ));
                }
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
            ExprKind::Par { var, from, to, body } => {
                let (var, from, to, body) = (var.clone(), *from, *to, *body);
                return self.check_par(e, &var, from, to, body, expected).map(Some);
            }
            _ => return Ok(None),
        };
        Err(self.flow_err(Code::E0806, span, format!("a flow body cannot contain {what} (§11.2)")))
    }

    /// `par i in a..b { e }` (§11.5): `i` is an `Init`-rate `U32`, the result is `[T; b - a]`.
    fn check_par(
        &mut self,
        e: ExprId,
        var: &Ident,
        from: ExprId,
        to: ExprId,
        body: ExprId,
        expected: Option<TyId>,
    ) -> R<TyId> {
        let span = self.expr(e).span;
        let lo = self.flow_const_u32(from, "a `par` bound")?;
        let hi = self.flow_const_u32(to, "a `par` bound")?;
        if hi <= lo {
            return Err(self.flow_err(
                Code::E0808,
                span,
                format!("`par` replicates `b - a` instances; the bounds `{lo}..{hi}` give none (§11.5)"),
            ));
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
            self.check_expr(body, exp_elem)
        })();
        self.pop_scope();
        let t = r?;
        Ok(self.a.types.intern(Ty::Array(t, Len::Const(hi - lo))))
    }

    /// A compile-time `U32` (§11.4, E0808): an integer literal or a `const` with a known value.
    fn flow_const_u32(&mut self, e: ExprId, what: &str) -> R<u32> {
        let span = self.expr(e).span;
        let u32 = self.u32();
        match &self.expr(e).kind {
            ExprKind::Lit(Lit::Int { value, .. }) => {
                let value = *value;
                if value > u32::MAX as u64 {
                    return Err(self.flow_err(Code::E0408, span, format!("{what} does not fit in `U32`")));
                }
                self.record(e, u32);
                Ok(value as u32)
            }
            ExprKind::Path(_) | ExprKind::Field { .. } => {
                let path = match &self.expr(e).kind {
                    ExprKind::Path(p) => p.clone(),
                    _ => match self.name_chain(e) {
                        Some(c) => Path { segments: c.iter().map(|(_, i)| i.clone()).collect(), span },
                        None => return Err(self.flow_not_const(span, what)),
                    },
                };
                if path.segments.len() == 1 && self.is_local_head(&path.segments[0].name) {
                    return Err(self.flow_not_const(span, what));
                }
                match self.a.resolve_path(self.m, &path) {
                    Ok(Entity::Def(d)) | Ok(Entity::Member(d)) => {
                        if let DefKind::Const(c) = &self.a.def(d).kind {
                            let (ty, int_value) = (c.ty, c.int_value);
                            self.unify_at(span, ty, u32)?;
                            self.record(e, ty);
                            self.info.targets.insert(e, Target::Const(d));
                            return match int_value {
                                Some(v) if v <= u32::MAX as u64 => Ok(v as u32),
                                Some(_) => {
                                    Err(self.flow_err(Code::E0408, span, format!("{what} does not fit in `U32`")))
                                }
                                None => Err(self.flow_not_const(span, what)),
                            };
                        }
                        Err(self.flow_not_const(span, what))
                    }
                    Ok(_) => Err(self.flow_not_const(span, what)),
                    Err(err) => Err(self.diag(err.into_diagnostic())),
                }
            }
            _ => Err(self.flow_not_const(span, what)),
        }
    }

    fn flow_not_const(&mut self, span: Span, what: &str) -> crate::body::Stop {
        self.flow_err(
            Code::E0808,
            span,
            format!(
                "{what} must be a compile-time constant (an integer literal or a `const`), so that the state size is fixed (§11.4)"
            ),
        )
    }

    /// Calls in flow mode (§11.5, §2.6): flow instances `f~(...)`, the builtins
    /// `prev` / `delay` / `vdelay` / `sample_rate`, E0811 / E0812. `None` hands
    /// the call back to the ordinary checker (functions, methods, constructors).
    pub(crate) fn check_flow_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        kind: CallKind,
        args: &[Arg],
        expected: Option<TyId>,
    ) -> R<Option<TyId>> {
        let span = self.expr(e).span;
        // 1. Reserved builtin names (§2.2).
        if let ExprKind::Path(p) = &self.expr(callee).kind
            && p.segments.len() == 1
            && BUILTINS.contains(&p.segments[0].name.as_str())
            && self.lookup_local(&p.segments[0].name).is_none()
        {
            let name = p.segments[0].name.clone();
            if kind != CallKind::Plain {
                return Err(self.flow_bad_mark(span, kind, &name));
            }
            return self.check_flow_builtin(e, &name, args, expected).map(Some);
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
            (None, _) => Ok(None),
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
        let mut arg_exprs = Vec::new();
        for (arg, input) in args.iter().zip(&f.inputs) {
            self.check_expr(arg.expr, Some(input.ty))?;
            arg_exprs.push(arg.expr);
        }
        self.fcx().calls.push(NodeCall {
            expr: e,
            kind: NodeKind::Instance(d),
            args: arg_exprs,
            init: None,
            ty: f.out,
        });
        Ok(f.out)
    }

    /// `prev(e, init)`, `delay(e, N, init)`, `vdelay(e, d, MAX, init)`, `sample_rate()` (§11.4).
    fn check_flow_builtin(&mut self, e: ExprId, name: &str, args: &[Arg], expected: Option<TyId>) -> R<TyId> {
        let span = self.expr(e).span;
        let arity = match name {
            "prev" => 2,
            "delay" => 3,
            "vdelay" => 4,
            _ => 0,
        };
        if args.len() != arity {
            return Err(self.flow_err(
                Code::E0412,
                span,
                format!("`{name}` takes {arity} argument(s) but {} were given", args.len()),
            ));
        }
        self.plain_args(args)?;
        if name == "sample_rate" {
            let f32 = self.a.types.float(FloatKind::F32);
            self.fcx().sample_rate_calls.push(e);
            return Ok(f32);
        }
        // The first argument may look back to a later `let` (§11.2).
        self.fcx().lookback += 1;
        let r = self.check_expr(args[0].expr, expected);
        self.fcx().lookback -= 1;
        let t = r?;
        let (kind, init_idx) = match name {
            "prev" => (NodeKind::Prev, 1),
            "delay" => {
                let n_expr = args[1].expr;
                let n = self.flow_const_u32(n_expr, "the length of `delay`")?;
                if n == 1 {
                    let fix = format!(
                        "prev({}, {})",
                        self.src(self.expr(args[0].expr).span),
                        self.src(self.expr(args[2].expr).span)
                    );
                    return Err(self.diag(
                        Diagnostic::new(Stage::Flow, Code::E0807, span, "a 1-sample delay is written `prev` (§11.4)")
                            .with_found(self.src(span))
                            .with_fix(Fix::replace("write `prev`", span, fix)),
                    ));
                }
                if n < 2 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(n_expr).span,
                        "`delay` needs a length of at least 2 (§11.4)",
                    ));
                }
                (NodeKind::Delay(n), 2)
            }
            _ => {
                self.check_expr(args[1].expr, Some(t))?;
                let max_expr = args[2].expr;
                let max = self.flow_const_u32(max_expr, "the maximum of `vdelay`")?;
                if max < 1 {
                    return Err(self.flow_err(
                        Code::E0808,
                        self.expr(max_expr).span,
                        "`vdelay` needs a maximum of at least 1 (§11.4)",
                    ));
                }
                self.fcx().float_checks.push((span, e));
                (NodeKind::Vdelay(max), 3)
            }
        };
        let init = args[init_idx].expr;
        self.check_expr(init, Some(t))?;
        let init_arg = match consteval::eval(self, init) {
            Some(v) => InitArg::Const(v),
            None => InitArg::Init(init),
        };
        let arg_exprs: Vec<ExprId> = args.iter().map(|a| a.expr).collect();
        self.fcx().calls.push(NodeCall { expr: e, kind, args: arg_exprs, init: Some(init_arg), ty: t });
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
    };
    for (i, c) in fcx.calls.iter().enumerate() {
        r.call_of_expr.insert(c.expr, i);
    }
    for p in &fcx.pending {
        if let Some(n) = &p.name {
            r.let_names.insert(p.init, n.clone());
        }
    }
    // Fixpoint on the `let` rates: a look-back (`prev(y, 0.0)` before `let y`)
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
        for &(l, r) in &self.fcx.inputs {
            self.local_rates.insert(l, r);
        }
        let _ = self.pass_inner();
    }

    fn pass_inner(&mut self) -> RR<()> {
        for k in 0..self.fcx.pending.len() {
            let p = self.fcx.pending[k].clone();
            let mut rate = self.rate(p.init)?;
            if let Some(ann) = p.annotated {
                if self.final_pass && rate > ann {
                    let span = self.expr(p.init).span;
                    return Err(self.err(
                        Code::E0810,
                        span,
                        format!(
                            "cannot lower the rate: the initializer is `{}` but the annotation says `{}` (§11.3)",
                            rate.name(),
                            ann.name()
                        ),
                    ));
                }
                rate = ann;
            }
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
                annotated: p.annotated,
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
                    "`vdelay` interpolates and needs a float signal (`F32` / `F64`, §11.4)",
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
    /// `prev` / `delay` / `vdelay` and instances are `Sig`.
    fn rate(&mut self, e: ExprId) -> RR<FlowRate> {
        let expr = self.expr(e);
        let span = expr.span;
        let r = match &expr.kind {
            ExprKind::Lit(_) | ExprKind::Hole | ExprKind::Range { .. } => FlowRate::Const,
            ExprKind::Path(_) => match self.body.targets.get(&e).cloned() {
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
            ExprKind::If { cond, then, else_ } => {
                let mut r = self.rate(*cond)?;
                r = r.max(self.rate(*then)?);
                if let Some(el) = else_ {
                    r = r.max(self.rate(*el)?);
                }
                r
            }
            ExprKind::Match { scrutinee, arms } => {
                let sr = self.rate(*scrutinee)?;
                let mut r = sr;
                for arm in arms {
                    self.bind_pat_rates(arm.pat, sr);
                    if let Some(g) = arm.guard {
                        r = r.max(self.rate(g)?);
                    }
                    r = r.max(self.rate(arm.body)?);
                }
                r
            }
            ExprKind::Closure { .. } | ExprKind::Handle { .. } => FlowRate::Const,
            ExprKind::Binary { operands, .. } => {
                let mut r = FlowRate::Const;
                for &x in operands {
                    r = r.max(self.rate(x)?);
                }
                r
            }
            ExprKind::TupleIndex { base, .. } => self.rate(*base)?,
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
        for a in args {
            r = r.max(self.rate(a.expr)?);
        }
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
                                "non-rt function `{name}` can only be called at Init rate; mark it `rt` or pass Init-rate arguments (§11.5)"
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

    /// `prev` / `delay` / `vdelay` / instance calls (§11.4, §11.5, S-04, S-06).
    fn rate_node(&mut self, e: ExprId, i: usize) -> RR<FlowRate> {
        let call = self.fcx.calls[i].clone();
        let span = self.expr(e).span;
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
                                "this argument is `{}` rate but input `{}` of `{callee_name}` is `{}`; rates only go up (§11.3)",
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
            NodeKind::Prev | NodeKind::Delay(_) | NodeKind::Vdelay(_) => {
                let what = match call.kind {
                    NodeKind::Prev => "prev",
                    NodeKind::Delay(_) => "delay",
                    _ => "vdelay",
                };
                let arg = call.args[0];
                let ra = self.rate(arg)?;
                if self.final_pass && ra != FlowRate::Sig {
                    let aspan = self.expr(arg).span;
                    let ty = self.body.expr_types.get(&arg).map(|&t| self.display(t)).unwrap_or_default();
                    let mut d = Diagnostic::new(
                        Stage::Flow,
                        Code::E0813,
                        aspan,
                        format!(
                            "the first argument of `{what}` must be a `Sig` signal; this one is `{}` (§11.4)",
                            ra.name()
                        ),
                    )
                    .with_found(self.src(aspan));
                    if ra == FlowRate::Ctl {
                        let src = self.src(aspan);
                        d = d.with_note(
                            aspan,
                            format!("write `let ps: Sig[{ty}] = {src}` to promote it per sample, then delay `ps`"),
                        );
                    }
                    return Err(self.fail(d));
                }
                let (init_e, d_e) = match call.kind {
                    NodeKind::Prev => (call.args[1], None),
                    NodeKind::Delay(_) => (call.args[2], None),
                    _ => (call.args[3], Some(call.args[1])),
                };
                if let Some(d) = d_e {
                    self.rate(d)?;
                }
                let ri = self.rate(init_e)?;
                if self.final_pass && ri > FlowRate::Init {
                    let ispan = self.expr(init_e).span;
                    // The clock of a value is faster than its position (S-147).
                    return Err(self.err(
                        Code::E0815,
                        ispan,
                        format!(
                            "the `init` of `{what}` must be `Init` rate or a constant; this one is `{}` (§11.4)",
                            ri.name()
                        ),
                    ));
                }
                if self.final_pass {
                    let init = call.init.clone().unwrap_or(InitArg::Init(init_e));
                    let ty = self.body.expr_types.get(&e).copied().unwrap_or(call.ty);
                    let node = match call.kind {
                        NodeKind::Prev => {
                            let name = self.node_name(e, "prev");
                            Node::Prev { name, expr: e, arg, init, ty }
                        }
                        NodeKind::Delay(n) => {
                            let name = self.node_name(e, "delay");
                            Node::Delay { name, expr: e, arg, n, init, ty }
                        }
                        NodeKind::Vdelay(max) => {
                            let name = self.node_name(e, "vdelay");
                            Node::Vdelay { name, expr: e, arg, d: d_e.unwrap(), max, init, ty }
                        }
                        NodeKind::Instance(_) => unreachable!(),
                    };
                    self.push_node(node);
                }
                Ok(FlowRate::Sig)
            }
        }
    }

    /// `par i in a..b { e }` (§11.5): nodes of the body are nested in the `Par` node.
    fn rate_par(&mut self, e: ExprId, body: ExprId) -> RR<FlowRate> {
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
            ExprKind::Path(_) | ExprKind::Field { .. } => {
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
                        NodeKind::Prev | NodeKind::Delay(_) => {
                            self.mark(call.args[0], FlowRate::Sig);
                            self.mark(*call.args.last().unwrap(), FlowRate::Init);
                        }
                        NodeKind::Vdelay(_) => {
                            self.mark(call.args[0], FlowRate::Sig);
                            self.mark(call.args[1], FlowRate::Sig);
                            self.mark(call.args[3], FlowRate::Init);
                        }
                    }
                } else if self.fcx.sample_rate_calls.contains(&e) {
                    self.sample_rate_at = Some(self.sample_rate_at.map_or(ctx, |r| r.max(ctx)));
                } else {
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
        ExprKind::Cast { expr, .. } | ExprKind::Unary { expr, .. } => vec![*expr],
        ExprKind::Tuple(xs) | ExprKind::Array(xs) => xs.clone(),
        ExprKind::Repeat { elem, .. } => vec![*elem],
        ExprKind::Struct { fields, .. } => fields.iter().map(|(_, x)| *x).collect(),
        ExprKind::Block(b) => b.tail.into_iter().collect(),
        ExprKind::If { cond, then, else_ } => {
            let mut v = vec![*cond, *then];
            v.extend(*else_);
            v
        }
        ExprKind::Match { scrutinee, arms } => {
            let mut v = vec![*scrutinee];
            for arm in arms {
                v.extend(arm.guard);
                v.push(arm.body);
            }
            v
        }
        ExprKind::Binary { operands, .. } => operands.clone(),
        ExprKind::TupleIndex { base, .. } => vec![*base],
        ExprKind::Index { base, index } => vec![*base, *index],
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        ExprKind::Range { lo, hi } => vec![*lo, *hi],
        ExprKind::Par { body, .. } => vec![*body],
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Hole
        | ExprKind::Field { .. }
        | ExprKind::Closure { .. }
        | ExprKind::Handle { .. } => Vec::new(),
    }
}
