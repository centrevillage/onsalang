//! Flow body checking (T3-1; spec §11.2–§11.5, §4.7 last bullet). A flow body
//! is checked with the function-body inference of `body.rs` in "flow mode",
//! then the walk of the clocks ([`clocks`]) gives every expression a clock
//! of [`crate::clock`], checks the flow rules, and collects the state nodes
//! for lowering (T3-5).
//!
//! # Output tables (`Analysis.flows[flow] = FlowInfo`)
//!
//! - `body: BodyInfo` — the typed body: `expr_types` (resolved), `locals`
//!   (inputs are `LocalKind::Param(Borrow)` locals in input order, `let`
//!   bindings are `LocalKind::Let`, `par` variables `LocalKind::Let`, match
//!   bindings `MatchBind`), `targets`, `pat_locals`, `instances` (generic
//!   instantiations used by the body, for monomorphization). Flow-instance
//!   calls (`saw~(f0)`), the delays `prev~` / `delay~` / `vdelay~` and
//!   `sample_rate()` have no `Target`; use `node_of` / `sample_rate_calls`.
//!   A feedback reference `^y` has the `Target::Local` of `y`.
//! - `clocks: ClockInfo` — `exprs`, the clock of every expression (§11.3),
//!   and `locals`, the clock of every local (inputs: declared, of
//!   [`FlowInput::api_clock`]; `let`s: the clock of the `let`; `par`
//!   variables: `Init`; match bindings: the clock of the scrutinee).
//! - `inputs: Vec<LocalId>` — locals of the inputs, in signature order.
//! - `lets: Vec<FlowLet>` — the top-level `let`s in source order. `state`
//!   is set when a local of the `let` is read at a stage that is not its own
//!   (an `Init` `let` read at `Block` / `sample`, a `Block` `let` read at
//!   `sample`; S-05, [`FlowInfo::stored`]): those become state fields.
//!   `let`s of `Clock::Const` are never state (they can be inlined).
//! - `nodes: Vec<PlanNode>` — the plan of the stateful nodes (R-91 (1),
//!   [`plan`]), flat and indexed by [`NodeId`]: the delays, the instance
//!   calls and the `par~`s, each with its [`Owner`] (a `let`, the output or
//!   a `par~`, by the tree of the body), its clock, the clocks its arguments
//!   are read at ([`ArgRead`], `lookback` of the first argument of a delay),
//!   the place of its fields, and its §11.6 names ([`plan`]'s `names`): the
//!   `let` name when the node is the whole initializer of a `let` of one
//!   name (`let y1 = prev~(^y)`, `let src = saw~(f0)`), otherwise
//!   `prev_0`, `delay_0`, `vdelay_0`, `<callee>_0`, `par_0`, numbered per
//!   kind in the `let`, the output or the `par~` that holds it in the order
//!   of the text (the outer call first), and its path after the scope of
//!   that part (`a.prev_0`, `_out.lp_0`, `m.par_0.lp_0`). [`FlowInfo::roots`] gives the nodes
//!   of an owner (of a `par~`, its `children`), [`FlowInfo::top`] those of
//!   the `let`s and the output. Empty when the flow is not `complete`.
//! - `node_of` — a call or `par~` expression → its node.
//! - `fields: Vec<Field>` — the fields of the `State` in the order of §12.4
//!   (S-05, S-06, [`plan`]): `_sample_rate`, the inputs and the locals of the
//!   `let`s [`FlowInfo::stored`] keeps, the fields of the nodes of each `let`
//!   and of the output, `_poisoned`, `_initialized`; a `par~` with state has
//!   the fields of its replica. The lowering reads their names by what they
//!   hold ([`FlowInfo::field`]) and gives them their Core types.
//! - `sample_rate_at: Option<ClockStage>` — the latest stage at which
//!   `sample_rate()` is read (`None`: never; `Init`: no state field needed;
//!   `Block` / `Tick`: store it, S-05). `sample_rate_calls` lists the calls.
//! - `read_at: HashMap<LocalId, BTreeSet<ClockStage>>` — the stages at which
//!   each local is read (inputs, `let`s, `par` variables, match bindings;
//!   S-05): each argument of a node at the stage of its clock
//!   ([`ArgRead::at`]: of an instance, the callee input's clock; the first
//!   argument and the `d` of a delay, the clock of the delay; an `init`,
//!   `Init`), the initializer of a constant `let` at each stage its locals
//!   are read at (at `Init` when none is read: a constant is read at the
//!   first stage). A local that is never read has no entry. The state keeps
//!   an input or a `let` read at a stage not its own ([`FlowInfo::stored`]);
//!   the lowering defines a constant `let` in each phase that reads it
//!   (§11.3).
//! - `output: ExprId` — the output expression (clock ≤ `sample`, promoted).
//! - `complete` — `false` when checking stopped at a diagnostic (tables partial).
//!
//! The parts are in a module each: `check` (the flow mode of the checker),
//! `consts` (the constant expressions), `clocks` (the walk of the clocks and
//! the checks of the flow rules), `loops` (the loops of the `let`s), `nodes`
//! (the record of the nodes), `plan` (the table of the nodes) and `reads`
//! (the state marking). The tables are here.

use std::collections::BTreeSet;

use onsa_diag::hash::HashMap;
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind, Ident, PatId, PatKind, RangeEnd, RangeHead, StmtId, StmtKind};
use serde::{Deserialize, Serialize};

use crate::body::{BodyInfo, Checker, Frame, LocalId, R, Target};
use crate::clock::{Clock, ClockName, ClockStage};
use crate::consteval::{self, ConstValue};
use crate::def::FlowInput;
use crate::ty::{FloatKind, Len, Ty, TyId};
use crate::{Analysis, DefId, Module};

use crate::flow_names::{Delay, SAMPLE_RATE};
mod check;
mod clocks;
mod consts;
mod loops;
mod nodes;
mod plan;
mod reads;
#[cfg(test)]
mod tests;

pub use plan::{Field, FieldOf, Kept, NodeId, Owner, Part, PlanKind, PlanNode};

pub(crate) use clocks::finish_flow;

/// A top-level `let` of a flow body.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowLet {
    pub pat: PatId,
    /// Locals bound by the pattern (one for `let y = ...`).
    pub locals: Vec<LocalId>,
    /// `Some` when the pattern is a single name.
    pub name: Option<String>,
    /// Type of the initializer (resolved).
    pub ty: TyId,
    pub clock: Clock,
    pub init: ExprId,
    pub span: Span,
    /// A local of it is read at a stage that is not its own: its locals
    /// become state fields ([`FlowInfo::stored`], S-05).
    pub state: bool,
}

/// The `init` argument of `prev~` / `delay~` / `vdelay~` (§11.4), or the
/// value of an omitted one (`nodes::default_init`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InitArg {
    /// A compile-time constant: no storage needed.
    Const(ConstValue),
    /// An `Init`-rate expression: stored in the state as `<name>.init` (S-06).
    Init(ExprId),
}

/// The clocks of the expressions and the locals of a flow body (§11.3).
/// The clocks of the nodes are in the plan ([`PlanNode`]).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ClockInfo {
    pub exprs: HashMap<ExprId, Clock>,
    pub locals: HashMap<LocalId, Clock>,
}

/// The clock of a delay or an instance call the walk of the clocks gives,
/// and the clocks its arguments are read at.
#[derive(Debug, Clone)]
pub(super) struct NodeClock {
    pub(super) clock: Clock,
    pub(super) args: Vec<ArgRead>,
}

/// An argument of a node and the clock of the place it is read at (§11.3,
/// §11.4): the first argument and the `d` of a delay at the clock of the
/// delay, an `init` at `init`, an argument of an instance at the clock of
/// its input. `lookback`: the value is read a tick later (the first
/// argument of a delay, §11.4), not as the node computes. The one place of
/// what a node reads (RF-8 (C)).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct ArgRead {
    pub expr: ExprId,
    pub at: Clock,
    pub lookback: bool,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FlowInfo {
    pub body: BodyInfo,
    pub clocks: ClockInfo,
    pub inputs: Vec<LocalId>,
    pub lets: Vec<FlowLet>,
    pub nodes: Vec<PlanNode>,
    pub node_of: HashMap<ExprId, NodeId>,
    pub(crate) roots: plan::Roots,
    pub fields: Vec<Field>,
    pub sample_rate_at: Option<ClockStage>,
    pub sample_rate_calls: Vec<ExprId>,
    pub read_at: HashMap<LocalId, BTreeSet<ClockStage>>,
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
    /// (its value is `nodes::default_init`).
    init: Option<InitArg>,
    init_expr: Option<ExprId>,
    ty: TyId,
}

impl NodeCall {
    /// The parts of a delay (§11.4) the walk and the plan read: its first
    /// argument, the `d` of a `vdelay~` (its second) and the written `init`.
    /// The one place of them.
    fn delay_parts(&self) -> (ExprId, Option<ExprId>, Option<ExprId>) {
        let Some(&first) = self.args.first() else { onsa_diag::internal::bug(None, "a delay with no argument") };
        let d = match self.kind {
            NodeKind::Delay(Delay::Variable, _) => self.args.get(1).copied(),
            NodeKind::Delay(..) | NodeKind::Instance(_) => None,
        };
        (first, d, self.init_expr)
    }
}

/// Flow-mode state of the [`Checker`].
#[derive(Debug, Default)]
pub(crate) struct FlowCx {
    /// Block nesting: `let` is allowed at depth 1 only.
    pub(crate) depth: u32,
    inputs: Vec<LocalId>,
    pending: Vec<PendingLet>,
    let_of_local: HashMap<LocalId, usize>,
    /// Nonzero while checking the first argument of a delay, instances included
    /// (a delay there is E0200, K-08).
    delay_arg: u32,
    calls: Vec<NodeCall>,
    /// `par` expression → (variable, from, to).
    pars: HashMap<ExprId, (LocalId, u32, u32)>,
    sample_rate_calls: Vec<ExprId>,
    output: Option<ExprId>,
}
