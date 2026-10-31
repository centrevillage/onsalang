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
//! - `read_at: HashMap<LocalId, FlowRate>` — the highest rate at which each
//!   local is read (inputs, `let`s, `par` variables, match bindings; S-05):
//!   instance arguments at the callee input's rate, the first argument of a
//!   delay (and `d` of `vdelay~`) at `Sig`, an `init` at `Init`. A local
//!   that is never read has no entry. The lowering stores an input or a
//!   `let` read above its own rate, and a constant `let` in the phases that
//!   read it.
//! - `output: ExprId` — the output expression (rate ≤ `Sig`, promoted).
//! - `complete` — `false` when checking stopped at a diagnostic (tables partial).
//!
//! The flow syntax of 0.3 (`at`, `^name`, `prev~`, the omitted `init`,
//! `if~` / `match~`) is read into these tables by [`map`] (W3-10, K-02).
//!
//! The parts are in a module each: `check` (the flow mode of the checker),
//! `consts` (the constant expressions), `rate` (the rate pass) and `reads`
//! (the state marking). The tables are here.

use std::collections::{HashMap, HashSet};

use onsa_diag::unsupported::{Feature, FlowForm};
use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{
    Arg, BinOp, CallKind, ExprId, ExprKind, Ident, Lit, Mode, PatId, PatKind, RangeEnd, RangeHead, StmtId, StmtKind,
    UnOp,
};

use crate::body::{BodyInfo, Checker, Frame, LocalId, R, Target};
use crate::consteval::{self, ConstValue};
use crate::def::FlowInput;
use crate::resolve::Entity;
use crate::ty::{FloatKind, Len, Rate, Ty, TyId};
use crate::{Analysis, DefId, Kind, Module};

#[path = "flow_map.rs"]
pub(crate) mod map;
use crate::flow_names::{Delay, SAMPLE_RATE};
mod check;
mod consts;
mod rate;
mod reads;

pub(crate) use rate::finish_flow;
use rate::{RStop, Rater};

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
    pub read_at: HashMap<LocalId, FlowRate>,
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
