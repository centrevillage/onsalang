//! Flow lowering (T3-5; D-03 and `design/05-flow-lowering.md`; spec
//! §11.4–§11.6, §12.4). A flow becomes a `State` struct and the functions
//!
//! | function | contents |
//! |---|---|
//! | `init(cfg, sample_rate) -> State` | `Init`-rate `let`s in order (state ones stored), node initialisation, sub `init`s, `poisoned = false`, `initialized = true` last |
//! | `reset(inout s)` | `prev` / `delay` / `vdelay` back to their `init` values, `w = 0`, sub `reset`s, `poisoned = false` |
//! | `ctl(inout s, p: Params)` | `Ctl`-rate `let`s in order (those read at `Sig` stored), sub `ctl`s with the sub's `Params` |
//! | `tick(inout s, <Sig inputs>) -> out` | `Sig`-rate `let`s in order, the output, then the stores of §11.4 in node order |
//! | `process(inout s, p, <Span inputs>, inout <Span outputs>)` | length check, `ctl` once, per sample: read all inputs, `tick`, write all outputs |
//! | `process_inplace` | `process` with the same spans for the paired inputs and outputs |
//! | `render` | `init`, `Buf.zeroed` outputs, one `process`, `Out` (interpreter only, D-08) |
//! | `params_default() -> Params` | the `@param` defaults |
//!
//! # State fields (S-05, S-06)
//!
//! In order: `sample_rate: F32` (when `sample_rate()` is read at `Ctl` or
//! `Sig`), inputs read above their own rate (by input name), then for each
//! top-level `let` in source order its own field (when read above its rate)
//! followed by the stateful nodes inside its initializer in source order,
//! then the nodes of the output expression, then `poisoned: Bool` and
//! `initialized: Bool` (both export-boundary marks, spec §14.2 / S-27). A node
//! named `n` contributes `n: T` (`prev`), `n.buf: [T; N]` + `n.w: U32`
//! (`delay`; `[T; MAX + 1]` for `vdelay`), plus `n.init: T` when its `init`
//! argument is an `Init`-rate expression; an instance contributes
//! `n: Callee.State`; a `par` with stateful nodes contributes
//! `n: [Flow.n.State; N]`. The bulk pointer of §12.4 is not a Core field: the
//! Core `State` is the whole value, and [`crate::layout::flow_layout`]
//! describes the fast / bulk split (the C backend materialises the pointer
//! and the `jmp_buf`).
//!
//! # Where a value lives
//!
//! Every expression is lowered in the phase function of its rate. A local
//! (input or `let`) read in a later phase than its own is a state field there
//! (`local_override`); `Ctl` inputs are read from `p` in `ctl`, `Init`
//! inputs from `cfg` in `init`. `Const`-rate `let`s are recomputed in every
//! phase that reads them. A stateful node is lowered on demand when the
//! expression containing it is lowered ([`lower_flow_expr`]), into a
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
//! stateful nodes inside an expression, [`boundary`] `process` /
//! `process_inplace` / `render` / `params_default`.

use std::collections::{HashMap, HashSet};

use onsa_diag::Span;
use onsa_sema::DefId;
use onsa_sema::def::{DefKind, Fields, FlowDef};
use onsa_sema::flow::{FlowInfo, FlowRate, InitArg, Node};
use onsa_sema::ty::{BuiltinTy, Len, Rate, Ty as STy};
use onsa_syntax::ast::ExprId;

use super::body::{FnCx, bind_irrefutable, coerce, lower_expr};
use super::build::{
    assign, borrow, call, checked_binary, cmp, expr_stmt, field_by_name, float_lit, index, inout, lit, local_expr,
    materialize, stmt, u32_lit,
};
use super::{Lowerer, R, core_mode, internal};
use crate::ir::*;
use crate::layout::{FlowLayout, flow_layout_for};
use crate::prim::Prim;

mod boundary;
mod generated;
mod nodes;
mod phases;
mod state;

use boundary::{gen_params_default, gen_process, gen_process_inplace, gen_render};
use generated::{Gen, init_value, instance_args, member_params, replica_index, sfield};
pub(crate) use nodes::lower_flow_expr;
use phases::{gen_ctl, gen_init, gen_reset, gen_tick, store_nodes};
use state::{ast_span, flat_nodes, node_fields, node_has_state, nodes_in};

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
    pub process: FnId,
    pub process_inplace: Option<FnId>,
    pub render: FnId,
    pub params_default: Option<FnId>,
}

impl FlowFns {
    /// Every function generated for the flow.
    pub fn generated(&self) -> impl Iterator<Item = FnId> {
        [self.init, self.reset, self.ctl, self.tick, self.process, self.render]
            .into_iter()
            .chain(self.process_inplace)
            .chain(self.params_default)
    }

    /// The functions a host calls to run an instance of the flow (spec
    /// §11.6, §15.2): `init`, `reset`, `ctl`, `tick`, `process` and the
    /// default of its parameters. The entries of a run of the flow for the
    /// reach ([`crate::reach`]): the C unit of an exported flow, the
    /// interpreter that runs a flow outside `onsa test`. `render` and
    /// `process_inplace` are not among them: the C unit does not give them
    /// (`render` needs `Buf`, D-08), and Onsa code that calls them reaches
    /// them as any call.
    pub fn entries(&self) -> impl Iterator<Item = FnId> {
        [self.init, self.reset, self.ctl, self.tick, self.process].into_iter().chain(self.params_default)
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
    pub params: Vec<(String, Ty, Option<onsa_sema::def::ParamMeta>)>,
    /// `Sig` inputs: name and value type.
    pub sig_inputs: Vec<(String, Ty)>,
    /// Outputs: name, element type, planar channel count (§11.6).
    pub outputs: Vec<(String, Ty, Option<u32>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Phase {
    Init,
    Ctl,
    Tick,
}

impl Phase {
    fn of(rate: FlowRate) -> Phase {
        match rate {
            FlowRate::Const | FlowRate::Init => Phase::Init,
            FlowRate::Ctl => Phase::Ctl,
            FlowRate::Sig => Phase::Tick,
        }
    }
}

/// A replica scope: the state place the nodes of this scope live in.
#[derive(Debug, Clone)]
struct Scope {
    state: Expr,
}

/// Flow-mode state of a [`FnCx`] (one per generated function).
#[derive(Debug)]
pub struct FlowLowerCx<'b> {
    /// Sema local index → the expression to read instead (`s.r`, `p.fc`, `cfg.time`).
    pub local_override: HashMap<u32, Expr>,
    /// Node expression → its value once computed (a temporary).
    pub expr_override: HashMap<ExprId, Expr>,
    info: &'b FlowInfo,
    phase: Phase,
    /// Every stateful node by its call / `par` expression, at any depth.
    node_by_expr: HashMap<ExprId, Node>,
    /// `sample_rate()`: the parameter in `init`, the state field elsewhere.
    sample_rate: Expr,
    /// Innermost scope last.
    scopes: Vec<Scope>,
}

/// What all generated functions of one flow share.
struct FlowShape {
    def: DefId,
    span: Span,
    flow: FlowDef,
    /// Sema locals that live in the state (inputs and `let`s), with their field name.
    state_locals: HashMap<u32, String>,
    /// `Const`-rate `let`s (indices into `info.lets`) read in each phase.
    const_lets: HashMap<Phase, Vec<usize>>,
    sample_rate_field: bool,
    state_ty: TypeId,
    config_ty: TypeId,
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

fn member(fd: &FlowDef, name: &str) -> Option<DefId> {
    fd.members.iter().find(|(n, _)| n == name).map(|(_, d)| *d)
}

fn lower_flow<'b>(lw: &mut Lowerer<'b>, flow: DefId, fd: FlowDef, span: Span) -> R<FlowFns> {
    let a: &'b onsa_sema::Analysis = lw.a;
    let Some(info) = a.flows.get(&flow) else { return Err(internal(span, "flow body was not checked")) };
    if !info.complete {
        return Err(internal(span, "flow body has errors"));
    }
    let need = |name: &str| member(&fd, name).ok_or_else(|| internal(span, format!("flow without `{name}`")));
    let state_def = need("State")?;
    let config_def = need("Config")?;
    let params_def = need("Params")?;
    let out_def = need("Out")?;
    let state_ty = lw.type_id(state_def, Vec::new(), span)?;
    let config_ty = lw.type_id(config_def, Vec::new(), span)?;
    let params_ty = lw.type_id(params_def, Vec::new(), span)?;
    let out_ty = lw.type_id(out_def, Vec::new(), span)?;
    let out_val = lw.core_ty(fd.out, &[], span)?;

    // Boundary outputs from the `Out` struct (`Buf[T]` / `[Buf[T]; N]` fields, §11.6).
    let mut outputs = Vec::new();
    if let DefKind::Struct(s) = &a.def(out_def).kind
        && let Fields::Named(fs) = &s.fields
    {
        for f in fs {
            let (elem, n) = match a.types.get(f.ty).clone() {
                STy::Builtin(BuiltinTy::Buf, args) => (args[0], None),
                STy::Array(buf, Len::Const(n)) => match a.types.get(buf).clone() {
                    STy::Builtin(BuiltinTy::Buf, args) => (args[0], Some(n)),
                    _ => return Err(internal(span, "Out field shape")),
                },
                _ => return Err(internal(span, "Out field shape")),
            };
            outputs.push((f.name.clone(), lw.core_ty(elem, &[], span)?, n));
        }
    }
    let out_is_struct = matches!(out_val, Ty::Struct(_));

    // The highest rate each local is read at is the checker's (S-05).
    let reads = &info.read_at;

    // State fields in S-05 order.
    let mut state_locals: HashMap<u32, String> = HashMap::new();
    let mut fields: Vec<(String, Ty)> = Vec::new();
    let sample_rate_field = info.sample_rate_at.is_some_and(|r| r >= FlowRate::Ctl);
    if sample_rate_field {
        fields.push(("sample_rate".into(), Ty::Float(FloatKind::F32)));
    }
    for (l, input) in info.inputs.iter().zip(&fd.inputs) {
        let own = FlowRate::from_rate(input.rate);
        if reads.get(l).is_some_and(|&r| r > own) {
            state_locals.insert(l.0, input.name.clone());
            fields.push((input.name.clone(), lw.core_ty(input.ty, &[], input.span)?));
        }
    }
    let mut const_lets: HashMap<Phase, Vec<usize>> = HashMap::new();
    let mut nodes_done: HashSet<ExprId> = HashSet::new();
    for (k, l) in info.lets.iter().enumerate() {
        if l.rate == FlowRate::Const {
            let mut phases: Vec<Phase> =
                l.locals.iter().filter_map(|loc| reads.get(loc)).map(|&r| Phase::of(r)).collect();
            phases.sort_by_key(|p| *p as u8);
            phases.dedup();
            for p in phases {
                const_lets.entry(p).or_default().push(k);
            }
            continue;
        }
        for loc in &l.locals {
            let name = &info.body.locals[loc.0 as usize].name;
            if l.state {
                state_locals.insert(loc.0, name.clone());
                let ty = lw.core_ty(info.body.locals[loc.0 as usize].ty, &[], l.span)?;
                fields.push((name.clone(), ty));
            }
        }
        let init_span = ast_span(lw, flow, l.init)?;
        for n in nodes_in(lw, flow, &info.nodes, init_span)? {
            if nodes_done.insert(n.expr()) {
                node_fields(lw, flow, &n, &mut fields)?;
            }
        }
    }
    for n in &info.nodes {
        if nodes_done.insert(n.expr()) {
            node_fields(lw, flow, n, &mut fields)?;
        }
    }
    fields.push(("poisoned".into(), Ty::Bool));
    fields.push(("initialized".into(), Ty::Bool));
    lw.m.types[state_ty.0 as usize].kind = TypeDefKind::Struct { fields };

    let shape = FlowShape {
        def: flow,
        span,
        flow: fd.clone(),
        state_locals,
        const_lets,
        sample_rate_field,
        state_ty,
        config_ty,
        params_ty,
        out_ty,
        out_val,
        outputs,
        out_is_struct,
    };

    let base = lw.qual_name(flow);
    let ctl = push_fn(lw, format!("{base}.ctl"), true, span);
    let tick = push_fn(lw, format!("{base}.tick"), true, span);
    let init = lw.fn_id(need("init")?, Vec::new());
    let reset = lw.fn_id(need("reset")?, Vec::new());
    let process = lw.fn_id(need("process")?, Vec::new());
    let process_inplace = member(&fd, "process_inplace").map(|d| lw.fn_id(d, Vec::new()));
    let render = lw.fn_id(need("render")?, Vec::new());
    let params_default = member(&fd, "params_default").map(|d| lw.fn_id(d, Vec::new()));
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
        process,
        process_inplace,
        render,
        params_default,
    };

    gen_init(lw, &shape, info, &fns)?;
    gen_reset(lw, &shape, info, &fns)?;
    gen_ctl(lw, &shape, info, &fns)?;
    gen_tick(lw, &shape, info, &fns)?;
    gen_process(lw, &shape, info, &fns)?;
    gen_process_inplace(lw, &shape, info, &fns)?;
    gen_render(lw, &shape, info, &fns)?;
    gen_params_default(lw, &shape, info, &fns)?;

    // Layout and the `SIZE` / `BULK_SIZE` consts (T3-6).
    let layout = flow_layout_for(&lw.m, state_ty, lw.bulk_threshold, lw.ptr_size);
    for (name, value) in [("SIZE", layout.size), ("BULK_SIZE", layout.bulk_size)] {
        let Some(d) = member(&fd, name) else { continue };
        let id = ConstId(lw.m.consts.len() as u32);
        let cname = lw.qual_name(d);
        lw.m.consts.push(ConstDef { name: cname, ty: Ty::u32(), init: lit(Ty::u32(), span, Lit::Int(value as i128)) });
        lw.const_ids.insert(d, id);
    }
    let mut params = Vec::new();
    let mut sig_inputs = Vec::new();
    for i in &fd.inputs {
        let ty = lw.core_ty(i.ty, &[], i.span)?;
        match i.rate {
            Rate::Ctl => params.push((i.name.clone(), ty, i.param.clone())),
            Rate::Sig => sig_inputs.push((i.name.clone(), ty)),
            Rate::Init => {}
        }
    }
    lw.m.flows.push(FlowMeta {
        name: base,
        fns: fns.clone(),
        layout,
        params,
        sig_inputs,
        outputs: shape.outputs.clone(),
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
    });
    id
}
