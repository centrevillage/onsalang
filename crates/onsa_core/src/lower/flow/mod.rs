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
//! its stage ([`hoist::writes`]: at the place of the faster `let` that holds
//! it, those of the output last; S-1159), and read from the field by the
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
    Entry, Feed, Field, FieldOf, FlowInfo, InitArg, Kept, NodeId, Op, Out, Part, PlanKind, PlanNode, Read, To,
};
use onsa_sema::ty::{BuiltinTy, Len, Ty as STy};
use onsa_syntax::ast::ExprId;

use super::body::{FnCx, bind_irrefutable, lower_expr, of_type, span_of};
use super::build::{
    after, assign, borrow, call, checked_binary, cmp, expr_stmt, field, float_lit, index, index_as, inout, lit,
    local_expr, materialize, place_of, stmt, u32_lit,
};
use super::{Lowerer, R, core_mode, internal, unsupported};
use crate::ir::*;
use crate::layout::{FlowLayout, flow_layout_for};
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
use generated::{Gen, init_value, instance_args, replica_loop, ring_len, sfield, spread};
pub(crate) use hoist::HoistUses;
pub(crate) use nodes::lower_flow_expr;
use phases::{StageRun, call_stage, drive, gen_ctl, gen_init, gen_reset, gen_tick};
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
    /// `process`, `process_inplace` and `render`: none of a flow with a
    /// port of a derived clock (`FlowInfo::derived_port`), which runs as an
    /// instance only (§11.9).
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
            .chain(self.stages.iter().map(|s| s.1))
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
    /// or that of a slower tick.
    pub(crate) fn stage_fn(&self, s: ClockStage) -> Option<FnId> {
        if s == ClockStage::SAMPLE {
            return Some(self.tick);
        }
        self.stages.iter().find(|x| x.0 == s).map(|x| x.1)
    }
}

/// Per-flow metadata kept on the [`Module`] for `onsa interface`, the
/// backends and the conformance tools.
#[derive(Debug, Clone)]
pub struct FlowMeta {
    /// Qualified flow name (`voice.voice`).
    pub name: String,
    pub fns: FlowFns,
    pub layout: FlowLayout,
    /// `Ctl` inputs with their `@param` metadata, in input order.
    pub params: Vec<(String, Ty, Option<ParamInfo>)>,
    /// `Sig` inputs: name and value type.
    pub sig_inputs: Vec<(String, Ty)>,
    /// Outputs: name, element type, planar channel count (§11.6).
    pub outputs: Vec<(String, Ty, Option<u32>)>,
    /// The flow's name in its heading: where a diagnostic of its API goes.
    pub name_span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Phase {
    Init,
    Ctl,
    /// The function of a tick: `tick` of the `sample` of the body, or that
    /// of a slower one (`FlowInfo::stages`).
    Tick(Ratio),
}

impl Phase {
    /// The phase of `tick`.
    const SAMPLE: Phase = Phase::Tick(Ratio(0));

    /// The stage of the analysis whose values the function of the phase
    /// makes: the one place of the correspondence (D-03).
    fn stage(self) -> ClockStage {
        match self {
            Phase::Init => ClockStage::Init,
            Phase::Ctl => ClockStage::Block,
            Phase::Tick(k) => ClockStage::Tick(k),
        }
    }

    /// The phase whose function evaluates what is of the stage `s`, as the
    /// plan says (`FlowInfo::run_stage`, R-91 (1)).
    fn of(info: &FlowInfo, s: ClockStage) -> Phase {
        match info.run_stage(s) {
            ClockStage::Init => Phase::Init,
            ClockStage::Block => Phase::Ctl,
            ClockStage::Tick(k) => Phase::Tick(k),
        }
    }
}

/// An input of the flow as its functions read it (§11.2, §11.6): its local,
/// its declaration, the phase of its stage in the plan (of
/// `FlowInput::body_clock`) and its place among the inputs of that stage
/// (its field of `Config` or `Params`).
#[derive(Debug, Clone)]
struct Input {
    local: onsa_sema::LocalId,
    decl: FlowInput,
    phase: Phase,
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
    let mut count = [0u32; 3];
    let one = |(&local, decl): (&onsa_sema::LocalId, &FlowInput)| {
        let stage = info.own_stage(local);
        let phase = stage.map(|s| Phase::of(info, s));
        let k = match phase {
            Some(Phase::Init) => 0,
            Some(Phase::Ctl) => 1,
            Some(Phase::Tick(_)) => 2,
            None => return Err(internal(decl.span, format!("an input of the stage {stage:?}"))),
        };
        let (at, phase) = (count[k], phase.unwrap_or(Phase::SAMPLE));
        count[k] += 1;
        Ok(Input { local, decl: decl.clone(), phase, at })
    };
    info.inputs.iter().zip(&fd.inputs).map(one).collect()
}

/// Every stage of the plan is of a function: those its locals are read at
/// and those of what the state keeps, of the hoisted fields and of the time
/// (the functions of the phases ask the plan of no other) are of `init`,
/// `ctl`, `tick` or a slower tick of `FlowInfo::stages`. Another is an
/// internal error.
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
        if s.tick_slower_than(ClockStage::SAMPLE) && !info.stages.contains(&s) {
            return Err(internal(span, format!("no function of the stage {s:?}")));
        }
    }
    Ok(())
}

/// A replica scope: the state place the nodes of this scope live in, and
/// the arms of `match~` chosen in it or in one around it, whose bindings
/// are in their places ([`branches::choose`]).
#[derive(Debug, Clone)]
struct Scope {
    state: Expr,
    chosen: HashSet<(ExprId, usize)>,
}

/// Flow-mode state of a [`FnCx`] (one per generated function).
#[derive(Debug)]
pub struct FlowLowerCx<'b> {
    /// Sema local index → the expression to read instead (`s.r`, `p.fc`, `cfg.time`).
    pub local_override: HashMap<u32, Expr>,
    /// Node expression → its value once computed (a temporary).
    pub expr_override: HashMap<ExprId, Expr>,
    pub(crate) info: &'b FlowInfo,
    phase: Phase,
    /// `sample_rate()`: the parameter in `init`, the state field elsewhere.
    sample_rate: Expr,
    /// The calls of `sample_rate()` (`FlowInfo::sample_rate_calls`), each found at once (R-498).
    sample_rate_calls: HashSet<ExprId>,
    /// The calls of `sample_tick()` (`FlowInfo::sample_tick_calls`).
    sample_tick_calls: HashSet<ExprId>,
    /// The time of the function (§11.4, S-1129 (1), S-1217): its parameters
    /// `t` and `t_hi` of a stage that takes them (`FlowInfo::time_words`),
    /// the count of the outermost `sample` from `process`, which a caller
    /// passes to its callees ([`chain::child_time`]); empty elsewhere.
    time: Vec<Expr>,
    /// Innermost scope last.
    scopes: Vec<Scope>,
}

impl FlowLowerCx<'_> {
    /// A scope of `state` in the innermost, whose arms chosen it has.
    fn push_scope(&mut self, state: Expr) {
        let chosen = self.scopes.last().map(|s| s.chosen.clone()).unwrap_or_default();
        self.scopes.push(Scope { state, chosen });
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
    /// Core type of the flow's output value.
    out_val: Ty,
    /// Boundary outputs: name, element type, planar count (§11.6).
    outputs: Vec<(String, Ty, Option<u32>)>,
    out_is_struct: bool,
}

impl<'a> Lowerer<'a> {
    /// Lower a flow once; its functions are reachable through the member
    /// defs (`fn_id`) and through [`Module::flows`].
    pub(crate) fn ensure_flow(&mut self, flow: DefId) -> R<FlowFns> {
        if let Some(f) = self.flow_fns.get(&flow) {
            return Ok(f.clone());
        }
        let def = self.a.def(flow).clone();
        let DefKind::Flow(fd) = &def.kind else { return Err(internal(def.span, "not a flow")) };
        if !self.flows_in_progress.insert(flow) {
            // The names stage reports the cycle (E0817, §11.5), which stops lowering.
            return Err(internal(def.span, "a flow that instantiates itself"));
        }
        let r = lower_flow(self, flow, fd.clone(), def.span);
        self.flows_in_progress.remove(&flow);
        let fns = r?;
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
fn child_rate(sr: &Expr, n: &PlanNode, span: Span) -> R<Expr> {
    let mut rate = sr.clone();
    for b in n.bounds.iter().rev() {
        let Some(big) = b.ratio.n() else {
            return Err(internal(span, format!("the rate of a callee under a boundary of the ratio {:?}", b.ratio)));
        };
        let op = if b.ratio.slower_than_body() { BinOp::Div } else { BinOp::Mul };
        rate = checked_binary(op, rate, float_lit(&sr.ty, big as f64, span)?);
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
    /// The Core type of the type `t` of `flow` (§11.6): of its def, or of a
    /// flow with no `Config` or `Params` (S-112), an empty struct of the
    /// name, which its functions take ([`implicit_params`]).
    pub(crate) fn flow_ty(&mut self, flow: DefId, t: FlowTy, span: Span) -> R<TypeId> {
        let Some(fd) = self.a.def(flow).as_flow() else { return Err(internal(span, "not a flow")) };
        if let Some(d) = generated_type(self.a, fd, t) {
            return self.type_id(d, Vec::new(), span);
        }
        if t.input_clock().is_none() {
            return Err(internal(span, format!("flow without `{}`", t.name())));
        }
        if let Some(&id) = self.implicit_tys.get(&(flow, t)) {
            return Ok(id);
        }
        let id = TypeId(self.m.types.len() as u32);
        let name = format!("{}.{}", self.qual_name(flow), t.name());
        self.m.types.push(TypeDef { name, kind: TypeDefKind::Struct { fields: Vec::new() } });
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

fn lower_flow<'b>(lw: &mut Lowerer<'b>, flow: DefId, fd: FlowDef, span: Span) -> R<FlowFns> {
    let a: &'b onsa_sema::Analysis = lw.a;
    let Some(info) = a.flows.get(&flow) else { return Err(internal(span, "flow body was not checked")) };
    if !info.complete {
        return Err(internal(span, "flow body has errors"));
    }
    let need = |f: FlowFn| generated_fn(a, &fd, f).ok_or_else(|| internal(span, format!("flow without {f:?}")));
    let state_ty = lw.flow_ty(flow, FlowTy::State, span)?;
    let config_ty = lw.flow_ty(flow, FlowTy::Config, span)?;
    let params_ty = lw.flow_ty(flow, FlowTy::Params, span)?;
    let out_ty = lw.flow_ty(flow, FlowTy::Rendered, span)?;
    let out_def = generated_type(a, &fd, FlowTy::Rendered).ok_or_else(|| internal(span, "flow without `Rendered`"))?;
    // The body makes an output at `sample * N` in an array of N (§11.9).
    let out_val = lw.core_ty(fd.out, &[], span)?;
    let out_val = match fd.out_len() {
        Some(n) => Ty::Array(Box::new(out_val), n),
        None => out_val,
    };

    // Boundary outputs from the `Rendered` struct (`Buf[T]` / `[Buf[T]; N]` fields, §11.6).
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
    let out_is_struct = matches!(out_val, Ty::Struct(_));

    check_stages(info, span)?;
    let inputs = inputs(info, &fd, span)?;
    // The fields of the state are the plan's (S-05, S-06, §12.4).
    let fields = state_fields(lw, flow, &state::decls(info, &inputs), info, &info.fields)?;
    lw.m.types[state_ty.0 as usize].kind = TypeDefKind::Struct { fields };

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
    let ctl = push_fn(lw, format!("{base}.ctl"), true, span);
    let tick = push_fn(lw, format!("{base}.tick"), true, span);
    let mut stages = Vec::new();
    for &s in &info.stages {
        let n = match s {
            ClockStage::Tick(k) => k.n(),
            _ => None,
        };
        let n = n.ok_or_else(|| internal(span, format!("a slower tick of the stage {s:?}")))?;
        stages.push((s, push_fn(lw, format!("{base}.tick_{n}"), true, span)));
    }
    let init = lw.fn_id(need(FlowFn::Init)?, Vec::new(), span)?;
    let reset = lw.fn_id(need(FlowFn::Reset)?, Vec::new(), span)?;
    // None of a flow with a port of a derived clock: their uses are an E0200 (E0810 from W10-01).
    let made = |f: FlowFn| info.derived_port.is_none().then(|| need(f)).transpose();
    let mut id = |d: Option<DefId>| d.map(|d| lw.fn_id(d, Vec::new(), span)).transpose();
    let process = id(made(FlowFn::Process)?)?;
    let process_inplace = id(generated_fn(a, &fd, FlowFn::ProcessInplace).filter(|_| process.is_some()))?;
    let render = id(made(FlowFn::Render)?)?;
    // The values of `@param`, read from the analysis in this one place (§11.7).
    let (mut params, mut sig_inputs) = (Vec::new(), Vec::new());
    for Input { decl: i, phase, .. } in &shape.inputs {
        let ty = lw.core_ty(i.ty, &[], i.span)?;
        match phase {
            Phase::Ctl => params.push((i.name.clone(), ty, a.param_info(i))),
            &Phase::SAMPLE => sig_inputs.push((i.name.clone(), ty)),
            Phase::Init | Phase::Tick(_) => {}
        }
    }
    // Of the C API alone, when every `block` input has a `default` (§11.7, §14.2, S-625).
    let defaults: Option<Vec<(Ty, ParamNumber)>> =
        params.iter().map(|(_, t, p)| Some((t.clone(), p.as_ref()?.number(ParamKey::Default)?))).collect();
    let params_default = defaults.is_some().then(|| push_fn(lw, format!("{base}.params_default"), false, span));
    let fns = FlowFns {
        flow,
        state: state_ty,
        config: config_ty,
        params: params_ty,
        out: out_ty,
        init,
        reset,
        ctl,
        tick,
        stages,
        process,
        process_inplace,
        render,
        params_default,
        reset_kept: None,
    };

    hoist::checked(lw, info, |lw| {
        gen_init(lw, &shape, info, &fns)?;
        gen_reset(lw, &shape, info, &fns)?;
        gen_ctl(lw, &shape, info, &fns)?;
        for s in [ClockStage::SAMPLE].into_iter().chain(info.stages.iter().copied()) {
            gen_tick(lw, &shape, info, &fns, s)?;
        }
        Ok(())
    })?;
    if fns.process.is_some() {
        gen_process(lw, &shape, info, &fns)?;
        gen_process_inplace(lw, &shape, info, &fns)?;
        gen_render(lw, &shape, info, &fns)?;
    }
    gen_params_default(lw, &shape, info, &fns, defaults)?;

    // Layout and the `SIZE` / `BULK_SIZE` consts (T3-6).
    let layout = flow_layout_for(&lw.m, state_ty, lw.bulk_threshold, lw.ptr_size);
    for (name, value) in [("SIZE", layout.size), ("BULK_SIZE", layout.bulk_size)] {
        let Some(d) = member(&fd, name) else { continue };
        let id = ConstId(lw.m.consts.len() as u32);
        let cname = lw.qual_name(d);
        lw.m.consts.push(ConstDef { name: cname, ty: Ty::u32(), init: lit(Ty::u32(), span, Lit::Int(value as i128)) });
        lw.const_ids.insert((d, Vec::new()), id);
    }
    lw.m.flows.push(FlowMeta {
        name: base,
        fns: fns.clone(),
        layout,
        params,
        sig_inputs,
        outputs: shape.outputs.clone(),
        name_span: a.def(flow).name_span,
    });
    Ok(fns)
}

fn push_fn(lw: &mut Lowerer, name: String, rt: bool, span: Span) -> FnId {
    let id = FnId(lw.m.fns.len() as u32);
    lw.m.fns.push(FnDef {
        name,
        params: Vec::new(),
        ret: Ty::Unit,
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
