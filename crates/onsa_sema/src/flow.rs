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
//!   and `locals`, the clock of every local (inputs: the body's view of the
//!   declared one, [`FlowInput::body_clock`]; `let`s: the clock of the `let`; `par`
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
//!   are read at ([`ArgRead`]), the place of its fields, and its §11.6 names ([`plan`]'s `names`): the
//!   `let` name when the node is the whole initializer of a `let` of one
//!   name (`let y1 = prev~(^y)`, `let src = saw~(f0)`), otherwise
//!   `prev_0`, `delay_0`, `vdelay_0`, `<callee>_0`, `par_0`, numbered per
//!   kind in the `let`, the output or the `par~` that holds it in the order
//!   of the text (the outer call first), and its path after the scope of
//!   that part (`a.prev_0`, `_out.lp_0`, `m.par_0.lp_0`). [`FlowInfo::roots`] gives the nodes
//!   of an owner (of a `par~`, its `children`), [`FlowInfo::top`] those of
//!   the `let`s and the output. Empty when the flow is not `complete`.
//!   The walk of the table of the entries of the stages ([`plan`]'s
//!   `entries`, after every body) gives each instance its `runs` (the stages
//!   of its callee and the stage of the flow each runs in, S-1088), each flow
//!   its `stages` (its slow ticks and those of its callees) and `reads_time`
//!   (it or a callee reads `sample_tick()`); `out_stage` is the stage that
//!   makes the output.
//! - `node_of` — a call or `par~` expression → its node.
//! - `edges: Vec<Edge>` — who reads what, recorded with the nodes: a local
//!   or a node ([`Vertex`]) read by the innermost node, `let` or output
//!   around the read, `lookback` in the first argument of a delay (§11.4).
//! - `hoists: Vec<Hoist>` — the slow subexpressions read at a faster stage,
//!   evaluated at the stage of their clock into hidden fields (§11.3,
//!   [`hoist`]): chosen by the marking, which reads their parts at their
//!   stage, so `read_at` comes of the choice. [`FlowInfo::hoist_of`] gives
//!   the one of an expression. One in a conditional position whose
//!   conditions are decided at `init` or `block` is `guarded` (S-1157):
//!   the conditions on its path are read at its stage too.
//! - `checks`, `const_conds` — the computed constant expressions in a
//!   conditional position: those its conditions' stage evaluates for their
//!   panic ([`FlowInfo::check_of`], S-888 (c′)), and the conditions of each
//!   (W9-03).
//! - `fields: Vec<Field>` — the fields of the `State` in the order of §12.4
//!   (S-05, S-06, [`plan`]): `_sample_rate`, the inputs and the locals of the
//!   `let`s [`FlowInfo::stored`] keeps, the fields of the nodes of each `let`
//!   and of the output, the hoisted fields, `_poisoned`, `_initialized`; a
//!   `par~` with state has the fields of its replica. The lowering reads their places by what they
//!   hold ([`FlowInfo::field_at`]) and gives them their Core types.
//! - `sample_rate_at: Option<ClockStage>` — the latest stage at which
//!   `sample_rate()` is read (`None`: never; `Init`: no state field needed;
//!   `Block` / `Tick`: store it, S-05). `sample_rate_calls` lists the calls.
//! - `read_at: HashMap<LocalId, BTreeSet<ClockStage>>` — the stages at which
//!   each local is read (inputs, `let`s, `par` variables, match bindings;
//!   S-05): each argument of a node at the stage of its clock
//!   ([`ArgRead::at`]: of an instance, the callee input's clock; the first
//!   argument and the `d` of a delay, the clock of the delay; an `init`,
//!   `Init`), the parts of a hoisted subexpression at its stage, the
//!   initializer of a constant `let` at each stage its locals are read at
//!   (at `Init` when none is read: a constant is read at the first stage). A local that is never read has no entry. The state keeps
//!   an input or a `let` read at a stage not its own ([`FlowInfo::stored`]);
//!   the function of each stage defines the constant `let`s it reads
//!   ([`FlowInfo::consts_at`], §11.3).
//!
//! The lowering asks the plan what the function of each stage reads
//! ([`plan`]'s `stage`): its `let`s ([`FlowInfo::lets_at`]), its constants
//! and what it reads from the state ([`FlowInfo::from_state`]), and finds
//! a field at its place ([`FlowInfo::field_at`]).
//! - `output: ExprId` — the output expression (clock ≤ `sample`, promoted).
//! - `complete` — `false` when checking stopped at a diagnostic (tables partial).
//!
//! The parts are in a module each: `check` (the flow mode of the checker),
//! `consts` (the constant expressions), `clocks` (the walk of the clocks and
//! the checks of the flow rules), `hoist` (hoisting), `loops` (the loops of
//! the `let`s), `nodes` (the record of the nodes), `plan` (the table of the
//! nodes) and `reads` (the state marking). The tables are here.

use std::collections::{BTreeMap, BTreeSet};

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind, Ident, PatId, PatKind, RangeEnd, RangeHead, StmtId, StmtKind};
use serde::{Deserialize, Serialize};

use crate::body::{BodyInfo, Checker, Frame, LocalId, R, Target};
use crate::clock::{Clock, ClockStage, Ratio};
use crate::consteval::{self, ConstValue};
use crate::def::FlowInput;
use crate::ty::{FloatKind, IntKind, Len, Ty, TyId};
use crate::{Analysis, DefId, Module};

use crate::flow_names::Delay;
mod branching;
mod check;
mod clocks;
mod consts;
mod hoist;
mod lift;
mod loops;
mod nodes;
mod plan;
mod reads;
#[cfg(test)]
mod tests;

pub use branching::{Chain, Link, chain};
pub use hoist::{Cond, Hoist, HoistId};
pub use plan::{Edge, Field, FieldOf, Kept, NodeId, Owner, Part, PlanKind, PlanModifier, PlanNode, Run, Vertex};

pub(crate) use clocks::finish_flow;
pub(crate) use plan::entries::walk as walk_entries;

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
    /// The stage it is evaluated at, as a clock (§11.3, S-1196): its clock,
    /// but of a value of the parameter kinds alone, theirs (`let m = p at
    /// (sample / 4)`, `p` at `block`, is of `block`).
    pub stage: Clock,
    pub init: ExprId,
    pub span: Span,
    /// A local of it is read at a stage that is not its own: its locals
    /// become state fields ([`FlowInfo::stored`], S-05).
    pub state: bool,
}

impl FlowLet {
    /// The `let` binds no name (`let _ = e`, `let Pair { l: _, r: _ } = e`):
    /// a root of what is reached (§5.1, S-727), and the scope `_<m>` of its
    /// nodes (§11.6). The one test of it ([`binds_none`]).
    pub fn binds_none(&self) -> bool {
        binds_none(&self.locals)
    }
}

/// A `let` of the locals `locals` binds no name ([`FlowLet::binds_none`]).
fn binds_none(locals: &[LocalId]) -> bool {
    locals.is_empty()
}

/// The `init` argument of `prev~` / `delay~` / `vdelay~` (§11.4), or the
/// value of an omitted one (`nodes::default_init`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InitArg {
    /// A compile-time constant: no storage needed.
    Const(ConstValue),
    /// An `Init`-rate expression: stored in the state as `<name>.init` (S-06).
    Init(ExprId),
    /// The omitted `init` of a value type other than a number that satisfies
    /// `Default`: `T.default()` (§11.4, S-29), a constant made at `init` and
    /// at `reset` with no storage.
    Default,
}

/// The clocks of the expressions and the locals of a flow body (§11.3).
/// The clocks of the nodes are in the plan ([`PlanNode`]).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ClockInfo {
    pub exprs: HashMap<ExprId, Clock>,
    pub locals: HashMap<LocalId, Clock>,
    /// The stages of the expressions and the locals that differ from their
    /// clocks ([`ClockInfo::stage`]).
    pub stages: HashMap<ExprId, Clock>,
    pub local_stages: HashMap<LocalId, Clock>,
}

impl ClockInfo {
    /// The stage `e` is evaluated at, as a clock (§11.3, S-1196): of an
    /// expression decided by values of the parameter kinds alone, theirs,
    /// whatever clock an `at` gives it (`(n at sample) / m`, `m` and `n` at
    /// `block`, is of `block`); of one that reads a tick, its clock. Made
    /// once by the walk (`clocks::stages`).
    pub fn stage(&self, e: ExprId) -> Option<Clock> {
        self.stages.get(&e).or(self.exprs.get(&e)).copied()
    }

    /// The stage of the local `l` ([`ClockInfo::stage`]): of a local of a
    /// `let`, that of the `let`; else its clock.
    pub fn local_stage(&self, l: LocalId) -> Option<Clock> {
        self.local_stages.get(&l).or(self.locals.get(&l)).copied()
    }

    /// The stage of the local `l` ([`ClockInfo::local_stage`]); `None` of
    /// a constant or a local the walk gave no clock. The one place of the
    /// stage of a local ([`FlowInfo::own_stage`]).
    pub fn own_stage(&self, l: LocalId) -> Option<ClockStage> {
        self.local_stage(l).and_then(Clock::stage)
    }
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
/// its input. Which reads are a tick later is of [`FlowInfo::edges`]
/// (RF-8 (C)).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct ArgRead {
    pub expr: ExprId,
    pub at: Clock,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FlowInfo {
    pub body: BodyInfo,
    pub clocks: ClockInfo,
    pub inputs: Vec<LocalId>,
    pub lets: Vec<FlowLet>,
    pub nodes: Vec<PlanNode>,
    pub node_of: HashMap<ExprId, NodeId>,
    /// Who reads what (R-91 (1), RF-8 (C)): the edges of the reads of the
    /// body, each once, in the order of the text (a node before its
    /// arguments'); empty when the flow is not `complete`. `onsa graph` and
    /// the E0309 of a `let` not reached read them.
    pub edges: Vec<Edge>,
    pub(crate) roots: plan::Roots,
    /// The hoisted subexpressions (§11.3), in the order of their fields
    /// ([`hoist`]'s `table`); [`FlowInfo::hoist_of`] finds the one of an
    /// expression.
    pub hoists: Vec<Hoist>,
    pub(crate) hoisted: HashMap<ExprId, HoistId>,
    /// The computed constant expressions in a conditional position that
    /// the stage of their conditions evaluates for their panic (S-888
    /// (c′), [`FlowInfo::check_of`]).
    pub(crate) checks: HashMap<ExprId, ClockStage>,
    /// The largest computed constant expressions in a conditional position
    /// (of a Copy type), each with the conditions on its path: W9-03
    /// evaluates at compile time those under `Const` and evaluates no
    /// branch that is not taken (S-888 (c′)).
    pub const_conds: HashMap<ExprId, Cond>,
    pub fields: Vec<Field>,
    /// The place of each field in the struct that holds it, made once with
    /// the fields ([`FlowInfo::field_at`]).
    pub(crate) places: HashMap<FieldOf, u32>,
    /// The first port of the flow of a derived clock (§11.9,
    /// [`crate::def::FlowDef::derived_port`]): the Core makes no `process`,
    /// `process_inplace` and `render` of it, whose uses the check stops
    /// (E0200, E0810 from W10-01).
    pub derived_port: Option<Span>,
    /// The first port at `sample * N` ([`crate::def::FlowDef::burst_port`]),
    /// which the Core lowers in W7-16 U6b ([`FlowInfo::multirate_at`]).
    pub(crate) burst_port: Option<Span>,
    pub sample_rate_at: Option<ClockStage>,
    pub sample_rate_calls: Vec<ExprId>,
    /// The calls of `sample_tick()` (§11.4), which the Core reads from the
    /// counter of the phase (`_tick`, [`FlowInfo::counts_time`]).
    pub sample_tick_calls: Vec<ExprId>,
    /// The ticks of the body slower than its `sample` (§11.9), slowest
    /// first: of its inputs, `let`s, nodes and hoisted fields, and the slow
    /// stages its instances run the stages of their callees in
    /// ([`PlanNode::runs`], S-1088). The Core makes a function of each
    /// ([`FlowInfo::run_stage`]).
    pub stages: Vec<ClockStage>,
    /// It or a flow it calls, through flows, reads `sample_tick()` (§11.4,
    /// S-1129 (1)): its stages take the time. Made by the walk of the table
    /// ([`plan`]'s `entries`).
    pub reads_time: bool,
    /// The stage of the body that makes the output ([`FlowInfo::run_stage`]
    /// of [`crate::def::FlowDef::body_out_clock`], `sample` of one of no
    /// tick); none of a flow with no table.
    pub out_stage: Option<ClockStage>,
    pub read_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    /// The stages each binding of an arm of `match~` is read at in a body,
    /// not its guard (S-1131): where it has a place, which its arm chosen
    /// there writes.
    pub bound_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    /// The `match~`s of the body (§11.5, S-1131), whose arms the lowering
    /// chooses at each stage their bindings are read at (`bound_at`).
    pub tilde_matches: BTreeMap<ExprId, TildeMatch>,
    /// The bindings of a `match~` read in the first argument of a delay,
    /// which the end of `tick` reads (§11.4): of each replica of the `par~`s
    /// around it.
    pub store_bindings: HashSet<LocalId>,
    pub output: Option<ExprId>,
    pub complete: bool,
}

/// A `match~` of a flow body (§11.5): the bindings of each arm in the order
/// of the text, and the `par~`s around it, the outermost first.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TildeMatch {
    pub arms: Vec<Vec<LocalId>>,
    pub pars: Vec<NodeId>,
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
    /// 0 for `prev~`), `None` when the check does not compute it (held).
    Delay(Delay, Option<u32>),
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
    calls: Vec<NodeCall>,
    /// `par` expression → (variable, its first value, the number of the
    /// instances, the end of its range), §11.5.
    pars: HashMap<ExprId, (LocalId, u32, u32, RangeEnd)>,
    sample_rate_calls: Vec<ExprId>,
    sample_tick_calls: Vec<ExprId>,
    /// The clock of each `e at k` (§11.3), the N of a derived clock
    /// evaluated: what the walk of the clocks reads.
    at_clocks: HashMap<ExprId, Clock>,
    output: Option<ExprId>,
    /// The first error of the flow stage the check of the types found
    /// (§18.1): held, not reported, while the types are checked on, since a
    /// type error anywhere in the body comes first (R-329). The walk of the
    /// clocks compares it with its own by position (R-495).
    held: Option<Diagnostic>,
    /// The number of the diagnostics before the body was checked: more after
    /// it, and the check of the types reported an error of the body.
    diags_before: usize,
    /// A constant expression read a constant whose unit failed (§18.1,
    /// R-499): no plan is made, with no diagnostic.
    unread: bool,
    /// The chains of modifiers by their heads ([`ModifierChain`]).
    chains: HashMap<ExprId, ModifierChain>,
}

/// A chain of modifiers (§11.9) as the check of the types read it, by the
/// call of its head (`ModifierCall::head`): the one record of its rate and
/// its modifiers, which the walk, the marking and the plan read (D-15).
#[derive(Debug)]
pub(crate) struct ModifierChain {
    /// The sum of the ratios of its `.down~(N)` and `.up~(N)`, the frame its
    /// head runs in; none when an N is in error (§18.1: its rate is not
    /// known, so what reads it reports nothing).
    ratio: Option<Ratio>,
    /// The sum of the exponents of the N of its `.down~(N)` and `.up~(N)`,
    /// either way (§11.9, S-1089): counted once, here, and kept in the plan
    /// ([`PlanNode::size`]).
    size: u32,
    /// Its modifiers in the order they are written (the check reads the
    /// receiver first).
    mods: Vec<ChainModifier>,
    /// The E0200 of its first `.when~` or `.reset_if~` (W7-10), held when
    /// no N of it is in error.
    gate: Option<Diagnostic>,
}

/// A modifier of a [`ModifierChain`]: its call, its receiver, and what the
/// plan keeps of it.
#[derive(Debug)]
pub(crate) struct ChainModifier {
    call: ExprId,
    receiver: ExprId,
    plan: PlanModifier,
}

impl FlowCx {
    /// The calls of the nodes, and the calls of the modifiers of a chain
    /// whose head is one, each with its receiver (§11.9: the value of the
    /// chain is the output of its head, a node): the one set of the
    /// expressions that are nodes (D-15), which the marking and the
    /// hoisting read.
    fn node_exprs(&self) -> HashMap<ExprId, Option<ExprId>> {
        let mut out: HashMap<ExprId, Option<ExprId>> = self.calls.iter().map(|c| (c.expr, None)).collect();
        let chains = self.chains.iter().filter(|(h, _)| out.contains_key(h)).flat_map(|(_, c)| &c.mods);
        let mods: Vec<_> = chains.map(|m| (m.call, Some(m.receiver))).collect();
        out.extend(mods);
        out
    }
}
