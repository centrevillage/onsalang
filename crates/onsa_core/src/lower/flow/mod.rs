//! Flow lowering (T3-5; D-03 and `design/05-flow-lowering.md`; spec
//! §11.4–§11.6, §12.4). A flow becomes a `State` struct and the functions
//!
//! | function | contents |
//! |---|---|
//! | `init(cfg, sample_rate) -> State` | `_tick = 0` and the fields of a tick read faster at `T.default()`, `Init`-rate `let`s in order (state ones stored) and the `Init` hoisted fields (below), node initialisation, sub `init`s, `_poisoned = false`, `_initialized = true` last |
//! | `reset(inout s)` | `_tick = 0` and the fields of a tick read faster at `T.default()`, `prev` / `delay` / `vdelay` back to their `init` values, `w = 0`, sub `reset`s, `_poisoned = false` |
//! | `_reset_kept(inout s)` | of a flow a `.reset_if~` resets (§11.10): `reset` with no counter, no `_poisoned` and no condition or count of a `.when~`, sub `_reset_kept`s |
//! | `ctl(inout s, p: Params)` | `Ctl`-rate `let`s in order (those read at `Sig` stored) and the `Ctl` hoisted fields, sub `ctl`s with the sub's `Params` |
//! | `tick(inout s, [t], <Sig inputs>) -> out` | `Sig`-rate `let`s in order, the output, the stages of the callees run there ([`chain::entry`], [`phases::call_stage`]), then the stores of §11.4 in node order, the counter of a grid advanced last; the time `t` (and `t_hi`) of a stage that takes it (`FlowInfo::time_words`) |
//! | `tick_<N>(inout s, [t], <its inputs>)` | of each tick `sample / N` of the body (`FlowInfo::stages`, those of its callees too): as `tick`, the output of an output at `sample / N` (§11.9) |
//! | `ev_<k>(inout s, [t], <its event>) -> [Option]` | of each source of events of the body (`FlowInfo::events`, §11.11), an input at `event` or a call that gives one: as `tick`, run once for each event, by the caller or after the run of the call that gives it ([`chain`]); the event of the output or none, of those on the way to it (`FlowInfo::gives`) |
//! | `process(inout s, p, [input], inout output)` | none of a port of a derived clock; `input` and `output` one `Span` (planar `[Span; N]`) or the `In` and `Out` of more (§11.6); length check, `ctl` once, per sample: the time `t = s._tick` (and `t_hi`), the slower ticks due ([`phases::drive`]), read all inputs, `tick`, the time advanced ([`phases::advance`]), write all outputs |
//! | `process_inplace(inout s, p, inout output)` | `process` with the input made of the signals of `output` (they pair up) |
//! | `render` | `init`, `Buf.zeroed` outputs, one `process`, `Rendered` (interpreter only, D-08) |
//! | `params_default() -> Params` | the `@param` defaults, of the C API alone (§11.6, S-625) |
//!
//! The functions keep `cfg` and `params` of a flow with no `Config` or
//! `Params` (§11.6, S-112), as empty structs ([`implicit_params`]), as the C
//! API does (W10-02 changes it).
//!
//! # State fields (S-05, S-06)
//!
//! The plan names and orders them (`FlowInfo::fields`). In order:
//! `_sample_rate: F32` (when `sample_rate()` is read at `Ctl` or `Sig`),
//! `_tick: U32` (the counter of the phase, of a flow that counts the time,
//! `FlowInfo::counts_time`), inputs read above their own rate (by input
//! name), then for each top-level `let` in source order its own field
//! (when read above its rate) followed by the stateful nodes inside its
//! initializer in source order,
//! then the nodes of the output expression, then the hoisted fields
//! (`a._hoist_0: T`, §11.3, §12.4; of the `let`s in order, then of the
//! output; those of the body of a `par~` are in its replica), then
//! `_poisoned: Bool` and `_initialized: Bool` (both export-boundary marks,
//! spec §14.2 / S-27). A
//! node of the path `p` (§11.6: `a.prev_0`, `_out.lp_0`, or the name of the
//! `let` whose whole value it is) contributes `p: T` (`prev`), `p.buf: [T;
//! N]` + `p.w: U32` (`delay`; `[T; MAX + 1]` for `vdelay`), plus `p.init: T`
//! when its `init` argument is an `Init`-rate expression; an instance
//! contributes `p: Callee.State`; a `par` with stateful nodes or hoisted
//! fields contributes `p: [Flow.p.State; N]`, whose replica names its nodes
//! and fields without the scope (`saw_0`, `_hoist_0`). The bulk pointer of
//! §12.4 is not a Core field: the Core `State` is the whole value, and
//! [`crate::layout::flow_layout`]
//! describes the fast / bulk split (the C backend materialises the pointer
//! and the `jmp_buf`).
//!
//! # Where a value lives
//!
//! Every expression is lowered in the phase function of its rate. A local
//! (input or `let`) read in a later phase than its own is a state field there
//! (`local_override`); `Ctl` inputs are read from `p` in `ctl`, `Init`
//! inputs from `cfg` in `init`. `Const`-rate `let`s are recomputed in every
//! phase that reads them. A subexpression the plan hoisted
//! (`FlowInfo::hoist_of`, §11.3) is written to its field by the phase of
//! its stage ([`hoist::work`]: at its place in the faster `let` or the output
//! that holds it, S-1159; one with a `^name` at the end, S-1244), and read from the field by the
//! later phases ([`lower_flow_expr`]); one under a condition decided at
//! `init` or `block` is written under it (S-1157); one in the body of a
//! `par~` in each replica (S-1140). A stateful node is lowered on demand
//! when the expression containing it is lowered ([`lower_flow_expr`]), into a
//! temporary that is memoised in `expr_override` so the end-of-tick stores
//! see the same value. `prev` reads its stored value where it appears and
//! stores its argument at the end of `tick` (§11.4); `delay` / `vdelay`
//! read where they appear and store + advance at the end, in node order.
//!
//! # Modules
//!
//! This module holds the shared types and [`lower_flow`]; [`state`] the
//! nodes and their state fields, [`generated`] the builder of a generated
//! function, [`phases`] `init` / `reset` / `ctl` / `tick`, [`nodes`] the
//! stateful nodes inside an expression, [`hoist`] the stores of the hoisted
//! fields, [`boundary`] `process` /
//! `process_inplace` / `render` / `params_default`.

use std::collections::{BTreeSet, HashMap, HashSet};

use onsa_diag::Span;
use onsa_diag::unsupported::Feature;
use onsa_sema::DefId;
use onsa_sema::clock::{Clock, ClockStage, Ratio};
use onsa_sema::def::{DefKind, Fields, FlowDef, FlowFn, FlowInput, FlowTy, ParamInfo, ParamKey, ParamNumber};
use onsa_sema::flow::Counter;
use onsa_sema::flow::{
    Feed, Field, FieldOf, FlowInfo, InitArg, Kept, NodeId, Op, Out, Owner, Part, PlanKind, PlanNode, Port, Read, To,
};
use onsa_sema::ty::{BuiltinTy, Len, Ty as STy};
use onsa_syntax::ast::ExprId;

use super::body::{Binding, FnCx, Ret, bind_irrefutable, bind_tys, lower_expr, of_type, span_of};
use super::build::{
    after, assign, borrow, call, checked_binary, cmp, expr_stmt, field, float_lit, index, index_as, inout, lit,
    local_expr, materialize, payload, place_of, stmt, u32_lit,
};
use super::{GenericArg, Lowerer, R, Stop, core_mode, internal, stopped, unsupported};
use crate::ir::*;
use crate::layout::{FlowLayout, flow_layout};
use crate::prim::Prim;

mod boundary;
mod branches;
mod chain;
mod generated;
mod hoist;
mod nodes;
mod phases;
mod state;
#[cfg(test)]
mod tests;

use boundary::{gen_params_default, gen_process, gen_process_inplace, gen_render};
pub(crate) use branches::{tilde_if, tilde_match};
pub(crate) use generated::burst_ty;
use generated::{Gen, Replicas, init_value, range, replicas_place, ring_len, sfield, spread};
pub(crate) use hoist::HoistUses;
pub(crate) use nodes::lower_flow_expr;
use phases::{StageRun, call_stage, drive, gen_ctl, gen_init, gen_reset, gen_stage};
use state::state_fields;

/// The Core items generated for one flow.
#[derive(Debug, Clone)]
pub struct FlowFns {
    pub flow: DefId,
    pub state: TypeId,
    pub config: TypeId,
    pub params: TypeId,
    pub out: TypeId,
    pub init: FnId,
    pub reset: FnId,
    pub ctl: FnId,
    pub tick: FnId,
    /// The function of each tick of the body slower than its `sample`
    /// (`FlowInfo::stages`), slowest first.
    pub stages: Vec<(ClockStage, FnId)>,
    /// The function of the stage of each source of an event clock of the
    /// body (§11.11, `FlowInfo::events`), in their order.
    pub events: Vec<(ClockStage, FnId)>,
    /// `process`, `process_inplace` and `render`: none of a flow with a
    /// port of a derived clock (`FlowInfo::derived_port`), which runs as an
    /// instance only (§11.9), or at `event` ([`FlowDef::awaits_events`]).
    pub process: Option<FnId>,
    pub process_inplace: Option<FnId>,
    pub render: Option<FnId>,
    pub params_default: Option<FnId>,
    /// `<flow>._reset_kept(inout s)`, the reset of a `.reset_if~` (§11.10):
    /// made when a caller first lowers one of an instance of the flow
    /// ([`phases::ensure_reset_kept`]), not an entry.
    pub reset_kept: Option<FnId>,
}

impl FlowFns {
    /// Every function generated for the flow.
    pub fn generated(&self) -> impl Iterator<Item = FnId> {
        [self.init, self.reset, self.ctl, self.tick]
            .into_iter()
            .chain(self.process)
            .chain(self.reset_kept)
            .chain(self.render)
            .chain(self.stages.iter().chain(&self.events).map(|s| s.1))
            .chain(self.process_inplace)
            .chain(self.params_default)
    }

    /// The functions a host calls to run an instance of the flow (spec
    /// §11.6, §15.2): `init`, `reset`, `ctl`, `tick` and those of the
    /// slower ticks, `process` and the default of its parameters. The
    /// entries of a run of the flow for the reach ([`crate::reach`]): the C unit of an exported flow, the
    /// interpreter that runs a flow outside `onsa test`. `render` and
    /// `process_inplace` are not among them: the C unit does not give them
    /// (`render` needs `Buf`, D-08), and Onsa code that calls them reaches
    /// them as any call.
    pub fn entries(&self) -> impl Iterator<Item = FnId> {
        let ticks = self.stages.iter().map(|s| s.1);
        let fns = [self.init, self.reset, self.ctl, self.tick].into_iter().chain(self.process);
        fns.chain(ticks).chain(self.params_default)
    }

    /// The function of the stage `s`: `tick` of the `sample` of the body,
    /// that of a slower tick, or that of a source of events.
    pub(crate) fn stage_fn(&self, s: ClockStage) -> Option<FnId> {
        if s == ClockStage::SAMPLE {
            return Some(self.tick);
        }
        self.stages.iter().chain(&self.events).find(|x| x.0 == s).map(|x| x.1)
    }
}

/// A `block` input of a flow: its name, its Core type and its `@param` values (§11.7).
pub type BlockParam = (String, CTy, Option<ParamInfo>);
/// A `Sig` input of a flow: its name and its Core type.
pub type SigInput = (String, CTy);

/// Per-flow metadata kept on the [`Module`] for `onsa interface`, the
/// backends and the conformance tools.
#[derive(Debug, Clone)]
pub struct FlowMeta {
    /// Qualified flow name (`voice.voice`).
    pub name: String,
    pub fns: FlowFns,
    pub layout: FlowLayout,
    /// `Ctl` inputs with their `@param` metadata, in input order.
    pub params: Vec<BlockParam>,
    /// `Sig` inputs: name and value type.
    pub sig_inputs: Vec<SigInput>,
    /// Outputs: name, element type, planar channel count (§11.6).
    pub outputs: Vec<(String, CTy, Option<u32>)>,
    /// The flow's name in its heading: where a diagnostic of its API goes.
    pub name_span: Span,
    /// Of each type of its state (`State`, the replica of a `par~`), what
    /// is known of each of its fields, in their order.
    pub states: Vec<(TypeId, Vec<StateField>)>,
}

/// What is known of a field of a type of the state of a flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateField {
    /// Of the write position of a delay, the length `N` of its ring: every
    /// value of the field is below it (the stage of the bounds reads it, V-26).
    pub below: Option<u32>,
}

/// An input of the flow as its functions read it (§11.2, §11.6): its local,
/// its declaration, the stage of the function that reads it as the plan
/// says (`FlowInfo::run_stage`, R-91 (1)) and its place among the inputs of
/// that stage (its field of `Config` or `Params`).
#[derive(Debug, Clone)]
struct Input {
    local: onsa_sema::LocalId,
    decl: FlowInput,
    stage: ClockStage,
    at: u32,
}

/// The inputs of the flow `fd` of the plan `info`: the one place the
/// lowering reads their stages and their places. An input at `sample / N`
/// (a port of a derived clock, §11.9) is of the function of its tick; one
/// of no stage is an internal error.
fn inputs(info: &FlowInfo, fd: &FlowDef, span: Span) -> R<Vec<Input>> {
    if info.inputs.len() != fd.inputs.len() {
        return Err(internal(span, "a plan of another number of inputs than its flow"));
    }
    let mut count: HashMap<ClockStage, u32> = HashMap::new();
    let one = |(&local, decl): (&onsa_sema::LocalId, &FlowInput)| {
        let own = info.own_stage(local).ok_or_else(|| internal(decl.span, "an input of no stage"))?;
        let stage = info.run_stage(own);
        let next = count.entry(stage).or_default();
        let at = *next;
        *next += 1;
        Ok(Input { local, decl: decl.clone(), stage, at })
    };
    info.inputs.iter().zip(&fd.inputs).map(one).collect()
}

/// Every stage of the plan is of a function: those its locals are read at
/// and those of what the state keeps, of the hoisted fields and of the time
/// (the functions of the phases ask the plan of no other) are of `init`,
/// `ctl`, `tick`, a slower tick of `FlowInfo::stages` or a source of
/// `FlowInfo::events`. Another is an internal error.
fn check_stages(info: &FlowInfo, span: Span) -> R<()> {
    let kept = info.fields.iter().filter_map(|f| match f.of {
        FieldOf::Input(l) | FieldOf::Let(l) => Some(info.own_stage(l)),
        _ => None,
    });
    let hoisted = info.hoists.iter().map(|h| Some(h.stage));
    let time = info.time.keys().map(|&s| Some(s));
    let stages: BTreeSet<Option<ClockStage>> =
        kept.chain(hoisted).chain(time).chain(info.read_stages().map(Some)).collect();
    for s in stages {
        let s = info.run_stage(s.ok_or_else(|| internal(span, "a stored local with no stage"))?);
        let event = matches!(s, ClockStage::Event(src) if info.event(src).is_none());
        if event || s.slow_tick() && !info.stages.contains(&s) {
            return Err(internal(span, format!("no function of the stage {s:?}")));
        }
    }
    Ok(())
}

/// A replica scope: the state place the nodes of this scope live in.
#[derive(Debug, Clone)]
struct Scope {
    state: Expr,
}

/// Flow-mode state of a [`FnCx`] (one per generated function).
#[derive(Debug)]
pub struct FlowLowerCx<'b> {
    pub(crate) info: &'b FlowInfo,
    /// The calls of `sample_rate()` (`FlowInfo::sample_rate_calls`), each found at once (R-498).
    sample_rate_calls: HashSet<ExprId>,
    /// The calls of `sample_tick()` (`FlowInfo::sample_tick_calls`).
    sample_tick_calls: HashSet<ExprId>,
    /// The functions of the stages of its events ([`FlowFns::events`]).
    events: Vec<(ClockStage, FnId)>,
    pub(crate) now: StageCx,
}

/// What a [`FlowLowerCx`] holds of the stage whose values it makes: that of
/// its function.
#[derive(Debug)]
pub(crate) struct StageCx {
    stage: ClockStage,
    /// Sema local index → the expression to read instead (`s.r`, `p.fc`, `cfg.time`).
    pub(crate) local_override: HashMap<u32, Expr>,
    /// Node expression → its value once computed (a temporary).
    expr_override: HashMap<ExprId, Expr>,
    /// The instances whose work in the function is lowered (§11.3, S-1233),
    /// each once, with its value (of one read in it, [`nodes::instance`]).
    done: HashMap<NodeId, Option<Expr>>,
    /// The end of the stage is lowered (§11.3): what the delays store and
    /// the work of `FlowInfo::late` alone. Its readers ([`hoist::work`],
    /// [`nodes::delay_work`], [`phases::init_delay`], [`lower_flow_expr`]) rest
    /// on three things. What is late is in the first argument of a delay (a
    /// `^name` is nowhere else, E0801), which [`phases::end`] comes to with
    /// each node. The walk of the end does not go down into the first
    /// argument of a delay inside: that delay is a node of its own. No
    /// instance runs at the end: its arguments and conditions read no `^name`
    /// and no binding one chooses (E0801, S-1245), so it is in `done`.
    saving: bool,
    /// The work of a conditional position ([`hoist::placed`]).
    guards: Option<bool>,
    /// The locals at the head of the function ([`nodes::keep`]).
    heads: Vec<Stmt>,
    /// `sample_rate()`: the parameter in `init`, the state field elsewhere.
    sample_rate: Expr,
    /// The event of the function of the stage of a call, its parameter: the
    /// value of that call there ([`nodes::instance`]).
    source: Option<Expr>,
    /// Of that function, the `par~`s around the call (§11.11): it is of the
    /// replica that gave the event, takes their variables and makes no loop of them.
    pinned: Vec<NodeId>,
    /// Of a function that gives the event of the output of the flow or none
    /// and does not make it (`FlowInfo::gives`), where it puts what the stage
    /// it ticks gives it ([`chain`]).
    gave: Option<Gave>,
    /// The time of the function (§11.4, S-1129 (1), S-1217): its parameters
    /// `t` and `t_hi` of a stage that takes them (`FlowInfo::time_words`),
    /// the count of the outermost `sample` from `process`, which a caller
    /// passes to its callees ([`chain::child_time`]); empty elsewhere.
    time: Vec<Expr>,
    /// Innermost scope last.
    scopes: Vec<Scope>,
}

/// The local `__out` of the event a function gives (an `Option`, `None` at
/// its head), or of several (`FlowInfo::burst`: an array of them) with the
/// local of the place of the `next`, up after each the stage it ticks gave.
#[derive(Debug, Clone)]
struct Gave {
    out: Expr,
    next: Option<Expr>,
}

impl Gave {
    /// Where the next is put: past the array of no run, as it has one of each ([`FlowInfo::burst`]).
    fn place(&self, tys: &Types) -> R<Expr> {
        self.next.as_ref().map_or(Ok(self.out.clone()), |n| index(self.out.clone(), n.clone(), tys))
    }
}

impl FlowLowerCx<'_> {
    fn push_scope(&mut self, state: Expr) {
        self.now.scopes.push(Scope { state });
    }
}

/// What all generated functions of one flow share.
struct FlowShape {
    def: DefId,
    span: Span,
    flow: FlowDef,
    inputs: Vec<Input>,
    state_ty: TypeId,
    params_ty: TypeId,
    out_ty: TypeId,
    /// Core type of the value the body makes for the output: the `Option` of an event (§11.11).
    out_val: CTy,
    /// Boundary outputs: name, element type, planar count (§11.6).
    outputs: Vec<(String, CTy, Option<u32>)>,
    out_is_struct: bool,
}

impl<'a> Lowerer<'a> {
    /// Lower a flow once; its functions are reachable through the member
    /// defs (`fn_id`) and through [`Module::flows`]. A flow a type stops,
    /// and one that makes an instance of it, is reported once (S-67), and
    /// each use is [`super::FailKind::Stopped`].
    pub(crate) fn ensure_flow(&mut self, flow: DefId) -> R<FlowFns> {
        if let Some(f) = self.flow_fns.get(&flow) {
            return Ok(f.clone());
        }
        if self.stopped.contains(&Stop::Flow(flow)) {
            return Err(stopped(self.a.def(flow).span));
        }
        let def = self.a.def(flow).clone();
        let DefKind::Flow(fd) = &def.kind else { return Err(internal(def.span, "not a flow")) };
        if !self.flows_in_progress.insert(flow) {
            // The names stage reports the cycle (E0817, §11.5), which stops lowering.
            return Err(internal(def.span, "a flow that instantiates itself"));
        }
        let r = lower_flow(self, flow, fd.clone(), def.span);
        self.flows_in_progress.remove(&flow);
        let fns = r.map_err(|f| self.stop_unit(Stop::Flow(flow), def.span, f))?;
        self.flow_fns.insert(flow, fns.clone());
        Ok(fns)
    }
}

/// The `sample_rate()` the callee of the node `n` reads from the rate `sr`
/// of its caller (§11.9: 1/N in the body of `.down~(N)`, N times in that of
/// `.up~(N)`): divided or multiplied at each boundary, the outermost first,
/// as each part runs the one it wraps, so that a rate below the normal
/// floats rounds at each (once by the product it would not). The one place
/// of it.
fn child_rate(sr: &Expr, n: &PlanNode, span: Span, tys: &Types) -> R<Expr> {
    let mut rate = sr.clone();
    for b in n.bounds.iter().rev() {
        let Some(big) = b.ratio.n() else {
            return Err(internal(span, format!("the rate of a callee under a boundary of the ratio {:?}", b.ratio)));
        };
        let op = if b.ratio.slower_than_body() { BinOp::Div } else { BinOp::Mul };
        rate = checked_binary(op, rate, float_lit(sr.ty, big as f64, span, tys)?);
    }
    Ok(rate)
}

fn member(fd: &FlowDef, name: &str) -> Option<DefId> {
    fd.members.iter().find(|(n, _)| n == name).map(|(_, d)| *d)
}

/// The function `f` among the members of `fd`, by its role (§11.6), not its name.
fn generated_fn(a: &onsa_sema::Analysis, fd: &FlowDef, f: FlowFn) -> Option<DefId> {
    let mut ds = fd.members.iter().map(|&(_, d)| d);
    ds.find(|&d| matches!(&a.def(d).kind, DefKind::Fn(x) if x.flow_fn == Some(f)))
}

/// The type `t` among the members of `fd`, by its role (§11.6), not its name.
fn generated_type(a: &onsa_sema::Analysis, fd: &FlowDef, t: FlowTy) -> Option<DefId> {
    let mut ds = fd.members.iter().map(|&(_, d)| d);
    ds.find(|&d| matches!(&a.def(d).kind, DefKind::Struct(s) if s.flow_ty == Some(t)))
}

impl Lowerer<'_> {
    /// Write the fields of the state `id` of a flow, which `type_id` made
    /// opaque (its def has none, §11.6): the one write of a type after it is
    /// made, before its facts are read. The facts of the fields are filled
    /// for the layout of the state.
    fn set_state_fields(&mut self, id: TypeId, fields: Vec<(String, CTy)>, span: Span) -> R<()> {
        if self.m.has_facts(&TyKind::Struct(id)) {
            return Err(internal(span, format!("the fields of `{}` after its facts", self.m.ty(id).name)));
        }
        fields.iter().for_each(|&(_, t)| self.m.fill_facts(t));
        self.m.types[id.0 as usize].kind = TypeDefKind::Struct { fields };
        Ok(())
    }

    /// The Core type of the type `t` of `flow` (§11.6): of its def, or of a
    /// flow with no `Config` or `Params` (S-112), an empty struct of the
    /// name, which its functions take ([`implicit_params`]).
    pub(crate) fn flow_ty(&mut self, flow: DefId, t: FlowTy, span: Span) -> R<TypeId> {
        let Some(fd) = self.a.def(flow).as_flow() else { return Err(internal(span, "not a flow")) };
        if let Some(d) = generated_type(self.a, fd, t) {
            return self.named_ty(d, Vec::new(), span);
        }
        if t.input_clock().is_none() {
            return Err(internal(span, format!("flow without `{}`", t.name())));
        }
        if let Some(&id) = self.implicit_tys.get(&(flow, t)) {
            return Ok(id);
        }
        let name = format!("{}.{}", self.qual_name(flow), t.name());
        let id = self.new_type(name, TypeDefKind::Struct { fields: Vec::new() });
        self.implicit_tys.insert((flow, t), id);
        Ok(id)
    }
}

/// The parameters the function `member` a flow generates has in Core and not
/// in Onsa (§11.6, S-112): `cfg` of `init` and `render` of a flow with no
/// `Config`, `params` of `process`, `process_inplace` and `render` of one
/// with no `Params`, of the empty types of [`Lowerer::flow_ty`]. Their places
/// among the Core parameters, in order; none of another function.
pub(crate) fn implicit_params(lw: &mut Lowerer, member: DefId, span: Span) -> R<Vec<(usize, &'static str, TypeId)>> {
    let d = lw.a.def(member);
    let DefKind::Fn(f) = &d.kind else { return Ok(Vec::new()) };
    let slots: &[(usize, FlowTy)] = match f.flow_fn {
        Some(FlowFn::Init) => &[(0, FlowTy::Config)],
        Some(FlowFn::Process | FlowFn::ProcessInplace) => &[(1, FlowTy::Params)],
        Some(FlowFn::Render) => &[(0, FlowTy::Config), (1, FlowTy::Params)],
        Some(FlowFn::Reset) | None => return Ok(Vec::new()),
    };
    let flow = d.owner.ok_or_else(|| internal(span, "flow member without an owner"))?;
    let Some(fd) = lw.a.def(flow).as_flow() else { return Err(internal(span, "flow member without its flow")) };
    let lacking: Vec<_> = slots.iter().filter(|s| generated_type(lw.a, fd, s.1).is_none()).copied().collect();
    let param = |t: FlowTy| t.param_name().ok_or_else(|| internal(span, "a type no parameter takes"));
    lacking.into_iter().map(|(at, t)| Ok((at, param(t)?, lw.flow_ty(flow, t, span)?))).collect()
}

/// The Core items of the flow `flow` (§11.4–§11.6): its types, the ids of
/// its functions in their one order ([`flow_fns`], then `params_default`), the
/// functions ([`generate`]), its `SIZE` consts ([`layout_consts`]) and its
/// [`FlowMeta`].
fn lower_flow<'b>(lw: &mut Lowerer<'b>, flow: DefId, fd: FlowDef, span: Span) -> R<FlowFns> {
    let a: &'b onsa_sema::Analysis = lw.a;
    let Some(info) = a.flows.get(&flow) else { return Err(internal(span, "flow body was not checked")) };
    if !info.planned() {
        return Err(internal(span, "flow body has errors"));
    }
    // The binding stage (S-67): the inputs are locals of the body, and the output.
    let locals = info.body.locals.iter().map(|l| Binding { ty: l.ty, at: l.span, decl: l.span });
    bind_tys(lw, std::iter::once(Binding { ty: fd.out, at: span, decl: span }).chain(locals), &[], span)?;
    let state_ty = lw.flow_ty(flow, FlowTy::State, span)?;
    let config_ty = lw.flow_ty(flow, FlowTy::Config, span)?;
    let params_ty = lw.flow_ty(flow, FlowTy::Params, span)?;
    let out_ty = lw.flow_ty(flow, FlowTy::Rendered, span)?;
    let out_def = generated_type(a, &fd, FlowTy::Rendered).ok_or_else(|| internal(span, "flow without `Rendered`"))?;
    // The body makes an output at `sample * N` in an array of N (§11.9), one at `event` in an `Option` (§11.11).
    let out_val = lw.core_ty(fd.out, &[], span)?;
    let out_val = match (fd.out_len(), info.emit) {
        (Some(n), _) => lw.ty(TyKind::Array(out_val, n)),
        (None, Some(_)) => {
            let option = lw.named_ty(event_option(a, span)?.def, vec![GenericArg::Ty(out_val)], span)?;
            lw.ty(TyKind::Enum(option))
        }
        (None, None) => out_val,
    };
    let outputs = rendered_outputs(lw, out_def, span)?;
    let out_is_struct = matches!(lw.m.tys.kind(out_val), TyKind::Struct(_));

    check_stages(info, span)?;
    let inputs = inputs(info, &fd, span)?;
    // The fields of the state are the plan's (S-05, S-06, §12.4).
    let mut states = Vec::new();
    let fields = state_fields(lw, (flow, &mut states), &state::decls(info, &inputs), info, &info.fields)?;
    let (fields, known) = fields.into_iter().map(|(name, t, f)| ((name, t), f)).unzip();
    states.push((state_ty, known));
    lw.set_state_fields(state_ty, fields, span)?;

    let shape = FlowShape {
        def: flow,
        span,
        flow: fd.clone(),
        inputs,
        state_ty,
        params_ty,
        out_ty,
        out_val,
        outputs,
        out_is_struct,
    };
    let base = lw.qual_name(flow);
    let mut fns = flow_fns(lw, &shape, info, config_ty, &base)?;
    let (params, sig_inputs) = param_values(lw, &shape)?;
    // Of the C API alone, when every `block` input has a `default` (§11.7, §14.2, S-625).
    let defaults: Option<Vec<(CTy, ParamNumber)>> =
        params.iter().map(|(_, t, p)| Some((*t, p.as_ref()?.number(ParamKey::Default)?))).collect();
    fns.params_default = defaults.is_some().then(|| push_fn(lw, format!("{base}.params_default"), false, span));
    generate(lw, &shape, info, &fns, defaults)?;
    let layout = layout_consts(lw, &fd, state_ty, span);
    lw.m.flows.push(FlowMeta {
        name: base,
        fns: fns.clone(),
        layout,
        params,
        sig_inputs,
        outputs: shape.outputs.clone(),
        name_span: a.def(flow).name_span,
        states,
    });
    Ok(fns)
}

/// The boundary outputs of a flow, of the fields of its `Rendered` struct
/// `out_def` (`Buf[T]` / `[Buf[T]; N]`, §11.6): name, element type, planar count.
fn rendered_outputs(lw: &mut Lowerer, out_def: DefId, span: Span) -> R<Vec<(String, CTy, Option<u32>)>> {
    let a = lw.a;
    let mut outputs = Vec::new();
    if let DefKind::Struct(s) = &a.def(out_def).kind
        && let Fields::Named(fs) = &s.fields
    {
        for f in fs {
            let (elem, n) = match a.types.get(f.ty).clone() {
                STy::Builtin(BuiltinTy::Buf, args) => (args[0], None),
                STy::Array(buf, Len::Const(n)) => match a.types.get(buf).clone() {
                    STy::Builtin(BuiltinTy::Buf, args) => (args[0], Some(n)),
                    _ => return Err(internal(span, "Rendered field shape")),
                },
                _ => return Err(internal(span, "Rendered field shape")),
            };
            outputs.push((f.name.clone(), lw.core_ty(elem, &[], span)?, n));
        }
    }
    Ok(outputs)
}

/// The ids of the functions of the flow of `shape` (§11.6) in the order
/// they are made, the order of the Core and of the C (`ctl`, `tick`, those
/// of the slower ticks and of the events, then those of the members), in its
/// [`FlowFns`], of the names after `base`: `params_default` made after
/// the values of [`param_values`], no `_reset_kept` yet.
fn flow_fns(lw: &mut Lowerer, shape: &FlowShape, info: &FlowInfo, config_ty: TypeId, base: &str) -> R<FlowFns> {
    let (a, fd, span) = (lw.a, &shape.flow, shape.span);
    let need = |f: FlowFn| generated_fn(a, fd, f).ok_or_else(|| internal(span, format!("flow without {f:?}")));
    let ctl = push_fn(lw, format!("{base}.ctl"), true, span);
    let tick = push_fn(lw, format!("{base}.tick"), true, span);
    let mut stages = Vec::new();
    for &s in &info.stages {
        let n = match s {
            ClockStage::Tick(k) => k.n(),
            ClockStage::Init | ClockStage::Block | ClockStage::Event(_) => None,
        };
        let n = n.ok_or_else(|| internal(span, format!("a slower tick of the stage {s:?}")))?;
        stages.push((s, push_fn(lw, format!("{base}.tick_{n}"), true, span)));
    }
    let events = info.events.iter().enumerate();
    let events = events.map(|(k, p)| (ClockStage::Event(p.src), push_fn(lw, format!("{base}.ev_{k}"), true, span)));
    let events = events.collect();
    let init = lw.fn_id(need(FlowFn::Init)?, Vec::new(), span)?;
    let reset = lw.fn_id(need(FlowFn::Reset)?, Vec::new(), span)?;
    // None of a flow with a port of a derived clock: their uses are an E0200 (E0810 from W10-01),
    // nor with one at `event`, until W10-07.
    let made = |f: FlowFn| {
        let d = need(f)?;
        Ok((info.derived_port.is_none() && !fd.awaits_events(a.def(d))).then_some(d))
    };
    let mut id = |d: Option<DefId>| d.map(|d| lw.fn_id(d, Vec::new(), span)).transpose();
    let process = id(made(FlowFn::Process)?)?;
    let process_inplace = id(generated_fn(a, fd, FlowFn::ProcessInplace).filter(|_| process.is_some()))?;
    let render = id(made(FlowFn::Render)?)?;
    Ok(FlowFns {
        flow: shape.def,
        state: shape.state_ty,
        config: config_ty,
        params: shape.params_ty,
        out: shape.out_ty,
        init,
        reset,
        ctl,
        tick,
        stages,
        events,
        process,
        process_inplace,
        render,
        params_default: None,
        reset_kept: None,
    })
}

/// The `block` inputs of the flow of `shape` with their `@param` values,
/// and its `Sig` inputs, by name and Core type, made after the ids of
/// [`flow_fns`] ([`FlowMeta`]).
fn param_values(lw: &mut Lowerer, shape: &FlowShape) -> R<(Vec<BlockParam>, Vec<SigInput>)> {
    let a = lw.a;
    // The values of `@param`, read from the analysis in this one place (§11.7).
    let (mut params, mut sig_inputs) = (Vec::new(), Vec::new());
    for Input { decl: i, stage, .. } in &shape.inputs {
        let ty = lw.core_ty(i.ty, &[], i.span)?;
        match stage {
            ClockStage::Block => params.push((i.name.clone(), ty, a.param_info(i))),
            &ClockStage::SAMPLE => sig_inputs.push((i.name.clone(), ty)),
            ClockStage::Init | ClockStage::Event(_) | ClockStage::Tick(_) => {}
        }
    }
    Ok((params, sig_inputs))
}

/// The functions of the flow of `shape` (§11.4, §11.6): those of the phases
/// and the stages, with the check of the hoisted fields they write and read
/// ([`hoist::checked`]); `process`, `process_inplace` and `render`; and
/// `params_default` of `defaults`.
fn generate<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
    defaults: Option<Vec<(CTy, ParamNumber)>>,
) -> R<()> {
    hoist::checked(lw, info, |lw| {
        gen_init(lw, shape, info, fns)?;
        gen_reset(lw, shape, info, fns)?;
        gen_ctl(lw, shape, info, fns)?;
        let events = info.events.iter().map(|p| ClockStage::Event(p.src));
        for s in [ClockStage::SAMPLE].into_iter().chain(info.stages.iter().copied()).chain(events) {
            gen_stage(lw, shape, info, fns, s)?;
        }
        Ok(())
    })?;
    if fns.process.is_some() {
        gen_process(lw, shape, info, fns)?;
        gen_process_inplace(lw, shape, info, fns)?;
        gen_render(lw, shape, info, fns)?;
    }
    gen_params_default(lw, shape, info, fns, defaults)
}

/// The layout of the state `state_ty` of the flow `fd` and its `SIZE` /
/// `BULK_SIZE` consts (T3-6), those of its members.
fn layout_consts(lw: &mut Lowerer, fd: &FlowDef, state_ty: TypeId, span: Span) -> FlowLayout {
    let layout = flow_layout(&lw.m, state_ty, lw.bulk_threshold);
    for (name, value) in [("SIZE", layout.size), ("BULK_SIZE", layout.bulk_size)] {
        let Some(d) = member(fd, name) else { continue };
        let id = ConstId(lw.m.consts.len() as u32);
        let cname = lw.qual_name(d);
        lw.m.consts.push(ConstDef {
            name: cname,
            ty: Types::U32,
            init: lit(Types::U32, span, Lit::Int(value as i128)),
        });
        lw.const_ids.insert((d, Vec::new()), id);
    }
    layout
}

/// The `Option` of an event given out or none (§11.11).
fn event_option(a: &onsa_sema::Analysis, span: Span) -> R<onsa_sema::lang::LangEnum> {
    let l = &a.modules.lang;
    l.option().and_then(|d| l.of(d)).ok_or_else(|| internal(span, "an event with no `Option`"))
}

fn push_fn(lw: &mut Lowerer, name: String, rt: bool, span: Span) -> FnId {
    let id = FnId(lw.m.fns.len() as u32);
    lw.m.fns.push(FnDef {
        name,
        params: Vec::new(),
        ret: Types::UNIT,
        sret: false,
        rt,
        locals: Vec::new(),
        body: None,
        span,
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    });
    id
}
