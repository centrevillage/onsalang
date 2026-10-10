//! Flow lowering (T3-5; docs/implementation-tasks.md §1 D-03 and §3.5; spec
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

use std::collections::{HashMap, HashSet};

use onsa_diag::Span;
use onsa_diag::unsupported::Feature;
use onsa_sema::def::{DefKind, Fields, FlowDef};
use onsa_sema::flow::{FlowInfo, FlowRate, InitArg, Node};
use onsa_sema::ty::{BuiltinTy, Len, Rate, Ty as STy};
use onsa_sema::{DefId, Target};
use onsa_syntax::ast::{self, ExprId, ExprKind as AK};

use super::body::{FnCx, bind_irrefutable, coerce, field_by_name, index, lit, local_expr, lower_expr, stmt, u32_lit};
use super::{Lowerer, R, core_mode, internal, unsupported};
use crate::ir::*;
use crate::layout::{FlowLayout, flow_layout_for};
use crate::prim::Prim;

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
            return Err(unsupported(def.span, Feature::FlowSelfInstance, &[]));
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

    // Highest rate each local is read at (mirrors the checker's marking, S-05).
    let mut reads: HashMap<u32, FlowRate> = HashMap::new();
    {
        let m = a.ast(lw.pkg, a.def(flow).module).ok_or_else(|| internal(span, "module source not found"))?;
        let node_by_expr = flat_nodes(&info.nodes);
        let mut w = ReadWalk { a, ast: &m.parsed.ast, info, node_by_expr: &node_by_expr, reads: &mut reads };
        for l in &info.lets {
            w.walk(l.init, l.rate);
        }
        if let Some(out) = info.output {
            w.walk(out, FlowRate::Sig);
        }
    }

    // State fields in S-05 order.
    let mut state_locals: HashMap<u32, String> = HashMap::new();
    let mut fields: Vec<(String, Ty)> = Vec::new();
    let sample_rate_field = info.sample_rate_at.is_some_and(|r| r >= FlowRate::Ctl);
    if sample_rate_field {
        fields.push(("sample_rate".into(), Ty::Float(FloatKind::F32)));
    }
    for (l, input) in info.inputs.iter().zip(&fd.inputs) {
        let own = FlowRate::from_rate(input.rate);
        if reads.get(&l.0).is_some_and(|&r| r > own) {
            state_locals.insert(l.0, input.name.clone());
            fields.push((input.name.clone(), lw.core_ty(input.ty, &[], input.span)?));
        }
    }
    let mut const_lets: HashMap<Phase, Vec<usize>> = HashMap::new();
    let mut nodes_done: HashSet<ExprId> = HashSet::new();
    for (k, l) in info.lets.iter().enumerate() {
        if l.rate == FlowRate::Const {
            let mut phases: Vec<Phase> =
                l.locals.iter().filter_map(|loc| reads.get(&loc.0)).map(|&r| Phase::of(r)).collect();
            phases.sort_by_key(|p| *p as u8);
            phases.dedup();
            for p in phases {
                const_lets.entry(p).or_default().push(k);
            }
            continue;
        }
        for loc in &l.locals {
            let name = &info.body.locals[loc.0 as usize].name;
            let above = reads.get(&loc.0).is_some_and(|&r| r > l.rate);
            if l.state || above {
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

fn ast_span(lw: &Lowerer, flow: DefId, e: ExprId) -> R<Span> {
    let a = lw.a;
    let d = a.def(flow);
    let m = a.ast(lw.pkg, d.module).ok_or_else(|| internal(d.span, "module source not found"))?;
    Ok(m.parsed.ast.expr(e).span)
}

/// Top-level nodes whose expression lies inside `span`, in source order.
fn nodes_in(lw: &Lowerer, flow: DefId, nodes: &[Node], span: Span) -> R<Vec<Node>> {
    let mut out = Vec::new();
    for n in nodes {
        let s = ast_span(lw, flow, n.expr())?;
        if span.start <= s.start && s.end <= span.end {
            out.push(n.clone());
        }
    }
    Ok(out)
}

/// Every node at any depth, by its expression.
fn flat_nodes(nodes: &[Node]) -> HashMap<ExprId, Node> {
    fn go(nodes: &[Node], out: &mut HashMap<ExprId, Node>) {
        for n in nodes {
            out.insert(n.expr(), n.clone());
            if let Node::Par { nodes, .. } = n {
                go(nodes, out);
            }
        }
    }
    let mut out = HashMap::new();
    go(nodes, &mut out);
    out
}

/// Whether a node holds any state (a `par` of pure replicas has none).
fn node_has_state(n: &Node) -> bool {
    match n {
        Node::Par { nodes, .. } => nodes.iter().any(node_has_state),
        _ => true,
    }
}

/// The state fields of one node (S-06).
fn node_fields(lw: &mut Lowerer, flow: DefId, n: &Node, fields: &mut Vec<(String, Ty)>) -> R<()> {
    let span = ast_span(lw, flow, n.expr())?;
    match n {
        Node::Prev { name, init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            fields.push((name.clone(), t.clone()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        Node::Delay { name, n: len, init, ty, .. } | Node::Vdelay { name, max: len, init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
            fields.push((format!("{name}.buf"), Ty::Array(Box::new(t.clone()), len)));
            fields.push((format!("{name}.w"), Ty::u32()));
            if matches!(init, InitArg::Init(_)) {
                fields.push((format!("{name}.init"), t));
            }
        }
        Node::Instance { name, callee, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            fields.push((name.clone(), Ty::Struct(sub.state)));
        }
        Node::Par { name, from, to, nodes, .. } => {
            if !node_has_state(n) {
                return Ok(());
            }
            let mut inner = Vec::new();
            for sub in nodes {
                node_fields(lw, flow, sub, &mut inner)?;
            }
            let tname = format!("{}.{name}.State", lw.qual_name(flow));
            let id = TypeId(lw.m.types.len() as u32);
            lw.m.types.push(TypeDef { name: tname, kind: TypeDefKind::Struct { fields: inner } });
            fields.push((name.clone(), Ty::Array(Box::new(Ty::Struct(id)), to - from)));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------- read analysis

struct ReadWalk<'x> {
    a: &'x onsa_sema::Analysis,
    ast: &'x ast::Ast,
    info: &'x FlowInfo,
    node_by_expr: &'x HashMap<ExprId, Node>,
    reads: &'x mut HashMap<u32, FlowRate>,
}

impl ReadWalk<'_> {
    fn note(&mut self, l: u32, ctx: FlowRate) {
        let e = self.reads.entry(l).or_insert(ctx);
        if ctx > *e {
            *e = ctx;
        }
    }

    /// Mirror of the checker's `mark` (S-05): instance arguments are read
    /// at the callee input's rate, look-backs at `Sig`, `init`s at `Init`.
    fn walk(&mut self, e: ExprId, ctx: FlowRate) {
        let expr = self.ast.expr(e);
        if let Some(Target::Local(l)) = self.info.body.targets.get(&e) {
            self.note(l.0, ctx);
            return;
        }
        if let Some(n) = self.node_by_expr.get(&e).cloned() {
            match n {
                Node::Prev { arg, init, .. } | Node::Delay { arg, init, .. } => {
                    self.walk(arg, FlowRate::Sig);
                    if let InitArg::Init(i) = init {
                        self.walk(i, FlowRate::Init);
                    }
                }
                Node::Vdelay { arg, d, init, .. } => {
                    self.walk(arg, FlowRate::Sig);
                    self.walk(d, FlowRate::Sig);
                    if let InitArg::Init(i) = init {
                        self.walk(i, FlowRate::Init);
                    }
                }
                Node::Instance { callee, args, .. } => {
                    let inputs = self.a.def(callee).as_flow().map(|f| f.inputs.clone()).unwrap_or_default();
                    for (arg, input) in args.iter().zip(&inputs) {
                        self.walk(*arg, FlowRate::from_rate(input.rate));
                    }
                }
                Node::Par { body, .. } => self.walk(body, ctx),
            }
            return;
        }
        if self.info.sample_rate_calls.contains(&e) {
            return;
        }
        match &expr.kind {
            AK::Field { base, .. } => self.walk(*base, ctx),
            AK::Call { callee, args, .. } => {
                if let AK::Field { base, .. } = &self.ast.expr(*callee).kind
                    && self.info.body.expr_types.contains_key(base)
                {
                    self.walk(*base, ctx);
                }
                for a in args {
                    self.walk(a.expr, ctx);
                }
            }
            _ => {
                for c in children(expr) {
                    self.walk(c, ctx);
                }
            }
        }
    }
}

fn children(expr: &ast::Expr) -> Vec<ExprId> {
    match &expr.kind {
        // Lowering runs only on a package without diagnostics (S-59).
        AK::Error => onsa_diag::internal::bug(Some(expr.span), "lowering met a body a syntax error left unread"),
        AK::Paren(x) | AK::Move(x) | AK::Try(x) | AK::Unsafe(x) => vec![*x],
        AK::Cast { expr, .. } | AK::Unary { expr, .. } | AK::At { expr, .. } => vec![*expr],
        // `^y` has the `Target::Local` of `y`, which the walk reads first.
        AK::Feedback(_) => Vec::new(),
        AK::Tuple(xs) | AK::Array(xs) => xs.clone(),
        AK::Repeat { elem, .. } => vec![*elem],
        AK::Struct { fields, .. } => fields.iter().map(|(_, x)| *x).collect(),
        AK::Block(b) => b.tail.into_iter().collect(),
        AK::If { cond, then, else_, .. } => {
            let mut v = vec![*cond, *then];
            v.extend(*else_);
            v
        }
        AK::Match { scrutinee, arms, .. } => {
            let mut v = vec![*scrutinee];
            for arm in arms {
                v.extend(arm.guard);
                v.push(arm.body);
            }
            v
        }
        AK::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        AK::TupleIndex { base, .. } | AK::TypeArgs { base, .. } => vec![*base],
        AK::Index { base, index } => vec![*base, *index],
        AK::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        AK::Range(r) => vec![r.lo, r.hi],
        AK::Par { body, .. } => vec![*body],
        AK::Lit(_) | AK::Path(_) | AK::Hole | AK::Field { .. } | AK::Closure { .. } | AK::Handle { .. } => Vec::new(),
    }
}

// ---------------------------------------------------------------- small helpers

fn float_lit(ty: &Ty, v: f64, span: Span) -> R<Expr> {
    match ty {
        Ty::Float(FloatKind::F32) => Ok(lit(ty.clone(), span, Lit::F32(v as f32))),
        Ty::Float(FloatKind::F64) => Ok(lit(ty.clone(), span, Lit::F64(v))),
        Ty::Int(_) => Ok(lit(ty.clone(), span, Lit::Int(v as i128))),
        _ => Err(internal(span, "numeric literal of a non-numeric type")),
    }
}

fn binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let (ty, span) = (lhs.ty.clone(), lhs.span);
    Expr::new(ty, span, ExprKind::Binary { op, overflow: Overflow::Checked, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

fn cmp(op: CmpOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span;
    Expr::new(Ty::Bool, span, ExprKind::Cmp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

fn place_of(e: &Expr) -> R<Place> {
    e.as_place().ok_or_else(|| internal(e.span, "expected a place"))
}

fn assign(out: &mut Vec<Stmt>, target: &Expr, value: Expr) -> R<()> {
    let span = target.span;
    out.push(stmt(span, StmtKind::Assign(place_of(target)?, value)));
    Ok(())
}

fn expr_stmt(out: &mut Vec<Stmt>, e: Expr) {
    let span = e.span;
    out.push(stmt(span, StmtKind::Expr(e)));
}

fn call(fid: FnId, ret: Ty, span: Span, args: Vec<Arg>) -> Expr {
    Expr::new(ret, span, ExprKind::Call { fn_: fid, args })
}

fn borrow(e: Expr) -> Arg {
    Arg { mode: Mode::Borrow, expr: e }
}

fn inout(e: Expr) -> Arg {
    Arg { mode: Mode::Inout, expr: e }
}

/// `state.<name>` (dotted node field names are plain field names).
fn sfield(lw: &Lowerer, state: &Expr, name: &str, span: Span) -> R<Expr> {
    field_by_name(lw, state.clone(), name, span)
}

/// Parameters of a generated member as declared by sema (§11.6).
fn member_params(lw: &mut Lowerer, fd: &FlowDef, name: &str, span: Span) -> R<Vec<(String, Mode, Ty)>> {
    let d = member(fd, name).ok_or_else(|| internal(span, format!("flow without `{name}`")))?;
    let def = lw.a.def(d).clone();
    let DefKind::Fn(f) = &def.kind else { return Err(internal(span, "member is not a function")) };
    let mut out = Vec::new();
    for p in &f.params {
        out.push((p.name.clone(), core_mode(p.mode), lw.core_ty(p.ty, &[], p.span)?));
    }
    Ok(out)
}

/// A node's `init` value: a constant literal, or the `Init`-rate expression
/// (lowered in `init`; `reset` reads the stored copy).
fn init_value(lw: &mut Lowerer, cx: &mut FnCx, init: &InitArg, ty: &Ty, span: Span) -> R<Expr> {
    match init {
        InitArg::Const(v) => lw.const_value_expr(v, ty, span),
        InitArg::Init(e) => lower_expr(lw, cx, *e),
    }
}

fn sub_inputs(lw: &Lowerer, callee: DefId) -> Vec<onsa_sema::def::FlowInput> {
    lw.a.def(callee).as_flow().map(|f| f.inputs.clone()).unwrap_or_default()
}

/// Arguments of an instance call for the callee inputs of `rate`, lowered
/// in the current function and coerced to the input value types.
fn instance_args(lw: &mut Lowerer, cx: &mut FnCx, callee: DefId, args: &[ExprId], rate: Rate) -> R<Vec<Expr>> {
    let inputs = sub_inputs(lw, callee);
    let mut out = Vec::new();
    for (arg, input) in args.iter().zip(&inputs) {
        if input.rate != rate {
            continue;
        }
        let want = lw.core_ty(input.ty, &[], input.span)?;
        let e = lower_expr(lw, cx, *arg)?;
        out.push(coerce(lw, cx, e, &want, Mode::Borrow)?);
    }
    Ok(out)
}

/// The replica index of a `par` loop variable (`var - from`).
fn replica_index(cx: &FnCx, var: onsa_sema::LocalId, from: u32, span: Span) -> Expr {
    let v = local_expr(cx, LocalId(var.0), span);
    if from == 0 { v } else { binary(BinOp::Sub, v, u32_lit(span, from)) }
}

// ---------------------------------------------------------------- generated functions

/// A generated function under construction.
struct Gen<'b> {
    cx: FnCx<'b>,
    params: Vec<Param>,
    stmts: Vec<Stmt>,
    span: Span,
}

impl<'b> Gen<'b> {
    fn new(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, phase: Phase, ret: Ty) -> R<Gen<'b>> {
        let mut cx = FnCx::new(lw, shape.def, Vec::new(), &info.body, ret)?;
        cx.flow = Some(FlowLowerCx {
            local_override: HashMap::new(),
            expr_override: HashMap::new(),
            info,
            phase,
            node_by_expr: flat_nodes(&info.nodes),
            sample_rate: lit(Ty::Float(FloatKind::F32), shape.span, Lit::F32(0.0)),
            scopes: Vec::new(),
        });
        Ok(Gen { cx, params: Vec::new(), stmts: Vec::new(), span: shape.span })
    }

    fn flow(&mut self) -> &mut FlowLowerCx<'b> {
        self.cx.flow.as_mut().expect("flow context")
    }

    fn param(&mut self, name: &str, mode: Mode, ty: Ty) -> Expr {
        let l = self.cx.temp(name, ty.clone());
        self.params.push(Param { local: l, mode, ty });
        local_expr(&self.cx, l, self.span)
    }

    /// Bind a sema local as a parameter (its Core local already exists).
    fn param_local(&mut self, l: LocalId, mode: Mode) {
        let ty = self.cx.locals[l.0 as usize].ty.clone();
        self.params.push(Param { local: l, mode, ty });
    }

    /// Parameters as declared by sema for a member (§11.6), as expressions by name.
    fn member_params(&mut self, lw: &mut Lowerer, shape: &FlowShape, name: &str) -> R<HashMap<String, Expr>> {
        let mut out = HashMap::new();
        for (n, mode, ty) in member_params(lw, &shape.flow, name, self.span)? {
            let e = self.param(&n, mode, ty);
            out.insert(n, e);
        }
        Ok(out)
    }

    fn temp(&mut self, name: &str, ty: Ty) -> Expr {
        let l = self.cx.temp(name, ty);
        local_expr(&self.cx, l, self.span)
    }

    fn let_(&mut self, name: &str, value: Expr) -> Expr {
        let l = self.cx.temp(name, value.ty.clone());
        self.stmts.push(stmt(self.span, StmtKind::Let(l, value)));
        local_expr(&self.cx, l, self.span)
    }

    /// Overrides for locals that live in the state and are read in this
    /// phase at a rate above their own, and for `sample_rate()`.
    fn state_overrides(&mut self, lw: &mut Lowerer, shape: &FlowShape, info: &FlowInfo, state: &Expr) -> R<()> {
        let phase = self.flow().phase;
        for (&l, name) in &shape.state_locals {
            let own = info.local_rates.get(&onsa_sema::LocalId(l)).copied().unwrap_or(FlowRate::Sig);
            if Phase::of(own) != phase {
                let f = sfield(lw, state, name, self.span)?;
                self.flow().local_override.insert(l, f);
            }
        }
        if shape.sample_rate_field && phase != Phase::Init {
            let f = sfield(lw, state, "sample_rate", self.span)?;
            self.flow().sample_rate = f;
        }
        Ok(())
    }

    /// `Const`-rate `let`s read in this phase, recomputed as locals.
    fn const_lets(&mut self, lw: &mut Lowerer, shape: &FlowShape, info: &FlowInfo) -> R<()> {
        let phase = self.flow().phase;
        let Some(ks) = shape.const_lets.get(&phase) else { return Ok(()) };
        for &k in ks {
            let l = &info.lets[k];
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
        }
        Ok(())
    }

    /// The `let`s of `rate` in order; state ones are also stored.
    fn rate_lets(
        &mut self,
        lw: &mut Lowerer,
        shape: &FlowShape,
        info: &FlowInfo,
        rate: FlowRate,
        state: &Expr,
    ) -> R<()> {
        for l in info.lets.iter().filter(|l| l.rate == rate) {
            let v = lower_expr(lw, &mut self.cx, l.init)?;
            bind_irrefutable(lw, &mut self.cx, l.pat, v, &mut self.stmts)?;
            for loc in &l.locals {
                if let Some(name) = shape.state_locals.get(&loc.0) {
                    let f = sfield(lw, state, name, l.span)?;
                    let v = local_expr(&self.cx, LocalId(loc.0), l.span);
                    assign(&mut self.stmts, &f, v)?;
                }
            }
        }
        Ok(())
    }

    fn finish(self, lw: &mut Lowerer, fid: FnId, ret: Ty, rt: bool, value: Option<Expr>) {
        let fd = &mut lw.m.fns[fid.0 as usize];
        fd.params = self.params;
        fd.sret = ret.is_aggregate();
        fd.ret = ret;
        fd.rt = rt;
        fd.locals = self.cx.locals;
        fd.body = Some(Block { stmts: self.stmts, value: value.map(Box::new) });
    }
}

/// `init(cfg, sample_rate) -> State`.
fn gen_init<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let state_ty = Ty::Struct(shape.state_ty);
    let mut g = Gen::new(lw, shape, info, Phase::Init, state_ty.clone())?;
    let cfg = g.param("cfg", Mode::Borrow, Ty::Struct(shape.config_ty));
    let sr = g.param("sample_rate", Mode::Borrow, Ty::Float(FloatKind::F32));
    let s = g.temp("s", state_ty.clone());
    let span = g.span;
    g.stmts.push(stmt(
        span,
        StmtKind::Let(
            LocalId(s.as_place().map(|p| p.root()).unwrap().0),
            Expr::new(state_ty.clone(), span, ExprKind::Zeroed),
        ),
    ));
    g.flow().sample_rate = sr.clone();
    g.flow().scopes.push(Scope { state: s.clone() });
    if shape.sample_rate_field {
        let f = sfield(lw, &s, "sample_rate", span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.rate != Rate::Init {
            continue;
        }
        let from_cfg = field_by_name(lw, cfg.clone(), &input.name, input.span)?;
        g.flow().local_override.insert(l.0, from_cfg.clone());
        if shape.state_locals.contains_key(&l.0) {
            let f = sfield(lw, &s, &input.name, input.span)?;
            assign(&mut g.stmts, &f, from_cfg)?;
        }
    }
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, FlowRate::Init, &s)?;
    let nodes = info.nodes.clone();
    init_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s, &sr)?;
    let poisoned = sfield(lw, &s, "poisoned", span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    // S-27: the last store of `init`; a panic before it leaves the instance uninitialized.
    let initialized = sfield(lw, &s, "initialized", span)?;
    assign(&mut g.stmts, &initialized, lit(Ty::Bool, span, Lit::Bool(true)))?;
    g.finish(lw, fns.init, state_ty, false, Some(s));
    Ok(())
}

/// Node initialisation (§11.4): stores, buffers, sub `init`s, replicas.
fn init_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, nodes: &[Node], state: &Expr, sr: &Expr) -> R<()> {
    for n in nodes {
        let span = cx.ast.expr(n.expr()).span;
        match n {
            Node::Prev { name, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let v = init_value(lw, cx, init, &t, span)?;
                let v = super::body::materialize(cx, v, out, &format!("{name}.init"));
                if matches!(init, InitArg::Init(_)) {
                    assign(out, &sfield(lw, state, &format!("{name}.init"), span)?, v.clone())?;
                }
                assign(out, &sfield(lw, state, name, span)?, v)?;
            }
            Node::Delay { name, n: len, init, ty, .. } | Node::Vdelay { name, max: len, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
                let v = init_value(lw, cx, init, &t, span)?;
                let v = super::body::materialize(cx, v, out, &format!("{name}.init"));
                if matches!(init, InitArg::Init(_)) {
                    assign(out, &sfield(lw, state, &format!("{name}.init"), span)?, v.clone())?;
                }
                let buf = sfield(lw, state, &format!("{name}.buf"), span)?;
                let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
                assign(out, &buf, fill)?;
                assign(out, &sfield(lw, state, &format!("{name}.w"), span)?, u32_lit(span, 0))?;
            }
            Node::Instance { name, callee, args, .. } => {
                let sub = lw.ensure_flow(*callee)?;
                let fields = instance_args(lw, cx, *callee, args, Rate::Init)?;
                let cfg = Expr::new(Ty::Struct(sub.config), span, ExprKind::Struct { ty: sub.config, fields });
                let c = call(sub.init, Ty::Struct(sub.state), span, vec![borrow(cfg), borrow(sr.clone())]);
                assign(out, &sfield(lw, state, name, span)?, c)?;
            }
            Node::Par { name, var, from, to, nodes, .. } => {
                if !node_has_state(n) {
                    continue;
                }
                let arr = sfield(lw, state, name, span)?;
                let idx = replica_index(cx, *var, *from, span);
                let elem = index(arr, idx)?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                init_nodes(lw, cx, &mut body, nodes, &elem, sr)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
            }
        }
    }
    Ok(())
}

/// `reset(inout s)`.
fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Init, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let span = g.span;
    g.flow().scopes.push(Scope { state: s.clone() });
    let nodes = info.nodes.clone();
    reset_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    let poisoned = sfield(lw, &s, "poisoned", span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    g.finish(lw, fns.reset, Ty::Unit, true, None);
    Ok(())
}

fn reset_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, nodes: &[Node], state: &Expr) -> R<()> {
    for n in nodes {
        let span = cx.ast.expr(n.expr()).span;
        match n {
            Node::Prev { name, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let v = match init {
                    InitArg::Const(c) => lw.const_value_expr(c, &t, span)?,
                    InitArg::Init(_) => sfield(lw, state, &format!("{name}.init"), span)?,
                };
                assign(out, &sfield(lw, state, name, span)?, v)?;
            }
            Node::Delay { name, n: len, init, ty, .. } | Node::Vdelay { name, max: len, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
                let v = match init {
                    InitArg::Const(c) => lw.const_value_expr(c, &t, span)?,
                    InitArg::Init(_) => sfield(lw, state, &format!("{name}.init"), span)?,
                };
                let buf = sfield(lw, state, &format!("{name}.buf"), span)?;
                let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
                assign(out, &buf, fill)?;
                assign(out, &sfield(lw, state, &format!("{name}.w"), span)?, u32_lit(span, 0))?;
            }
            Node::Instance { name, callee, .. } => {
                let sub = lw.ensure_flow(*callee)?;
                let st = sfield(lw, state, name, span)?;
                expr_stmt(out, call(sub.reset, Ty::Unit, span, vec![inout(st)]));
            }
            Node::Par { name, var, from, to, nodes, .. } => {
                if !node_has_state(n) {
                    continue;
                }
                let arr = sfield(lw, state, name, span)?;
                let elem = index(arr, replica_index(cx, *var, *from, span))?;
                let mut body = Vec::new();
                reset_nodes(lw, cx, &mut body, nodes, &elem)?;
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
            }
        }
    }
    Ok(())
}

/// `ctl(inout s, p: Params)`.
fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Ctl, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let p = g.param("p", Mode::Borrow, Ty::Struct(shape.params_ty));
    g.flow().scopes.push(Scope { state: s.clone() });
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.rate != Rate::Ctl {
            continue;
        }
        let from_p = field_by_name(lw, p.clone(), &input.name, input.span)?;
        g.flow().local_override.insert(l.0, from_p.clone());
        if shape.state_locals.contains_key(&l.0) {
            let f = sfield(lw, &s, &input.name, input.span)?;
            assign(&mut g.stmts, &f, from_p)?;
        }
    }
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, FlowRate::Ctl, &s)?;
    let nodes = info.nodes.clone();
    ctl_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    g.finish(lw, fns.ctl, Ty::Unit, true, None);
    Ok(())
}

/// Sub `ctl`s with the sub's `Params` built from the `Ctl`-input arguments.
fn ctl_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, nodes: &[Node], state: &Expr) -> R<()> {
    for n in nodes {
        let span = cx.ast.expr(n.expr()).span;
        match n {
            Node::Instance { name, callee, args, .. } => {
                let sub = lw.ensure_flow(*callee)?;
                let fields = instance_args(lw, cx, *callee, args, Rate::Ctl)?;
                let params = Expr::new(Ty::Struct(sub.params), span, ExprKind::Struct { ty: sub.params, fields });
                let st = sfield(lw, state, name, span)?;
                expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(params)]));
            }
            Node::Par { name, var, from, to, nodes, .. } => {
                if !node_has_state(n) {
                    continue;
                }
                let arr = sfield(lw, state, name, span)?;
                let elem = index(arr, replica_index(cx, *var, *from, span))?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                ctl_nodes(lw, cx, &mut body, nodes, &elem)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
            }
            Node::Prev { .. } | Node::Delay { .. } | Node::Vdelay { .. } => {}
        }
    }
    Ok(())
}

/// `tick(inout s, <Sig inputs>) -> out`.
fn gen_tick<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let out_ty = shape.out_val.clone();
    let mut g = Gen::new(lw, shape, info, Phase::Tick, out_ty.clone())?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.rate == Rate::Sig {
            g.param_local(LocalId(l.0), Mode::Borrow);
        }
    }
    g.flow().scopes.push(Scope { state: s.clone() });
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, FlowRate::Sig, &s)?;
    let output = info.output.ok_or_else(|| internal(shape.span, "flow without an output expression"))?;
    let v = lower_expr(lw, &mut g.cx, output)?;
    let v = coerce(lw, &mut g.cx, v, &out_ty, Mode::Borrow)?;
    // Materialised before the stores so a `prev` inside the output reads first (§11.4).
    let out_local = g.let_("__out", v);
    let nodes = info.nodes.clone();
    store_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    g.finish(lw, fns.tick, out_ty, true, Some(out_local));
    Ok(())
}

/// End-of-tick stores (§11.4) in node order: `prev` saves its argument,
/// `delay` / `vdelay` write the argument at `w` and advance.
fn store_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, nodes: &[Node], state: &Expr) -> R<()> {
    for n in nodes {
        let span = cx.ast.expr(n.expr()).span;
        match n {
            Node::Prev { name, arg, .. } => {
                let v = lower_expr(lw, cx, *arg)?;
                assign(out, &sfield(lw, state, name, span)?, v)?;
            }
            Node::Delay { name, arg, n: len, .. } | Node::Vdelay { name, arg, max: len, .. } => {
                let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
                let v = lower_expr(lw, cx, *arg)?;
                let buf = sfield(lw, state, &format!("{name}.buf"), span)?;
                let w = sfield(lw, state, &format!("{name}.w"), span)?;
                assign(out, &index(buf, w.clone())?, v)?;
                let next = binary(BinOp::Rem, binary(BinOp::Add, w.clone(), u32_lit(span, 1)), u32_lit(span, len));
                assign(out, &w, next)?;
            }
            // Instances store inside their own `tick`; `par` replicas store at the
            // end of each iteration of the loop that computes them.
            Node::Instance { .. } | Node::Par { .. } => {}
        }
    }
    Ok(())
}

/// On-demand value of a stateful node, `sample_rate()` or `par` while an
/// expression of the flow body is lowered. `None`: not a flow construct.
pub(crate) fn lower_flow_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Option<Expr>> {
    let span = cx.ast.expr(e).span;
    let (phase, node, state) = {
        let f = cx.flow.as_ref().expect("flow context");
        if let Some(v) = f.expr_override.get(&e) {
            return Ok(Some(v.clone()));
        }
        if f.info.sample_rate_calls.contains(&e) {
            return Ok(Some(f.sample_rate.clone()));
        }
        let Some(node) = f.node_by_expr.get(&e).cloned() else { return Ok(None) };
        let state = f.scopes.last().ok_or_else(|| internal(span, "node outside a state scope"))?.state.clone();
        (f.phase, node, state)
    };
    let not_here = |what: &str| internal(span, format!("`{what}` evaluated outside `tick`"));
    let mut stmts = Vec::new();
    let value = match &node {
        Node::Prev { name, .. } => {
            if phase != Phase::Tick {
                return Err(not_here("prev"));
            }
            sfield(lw, &state, name, span)?
        }
        Node::Delay { name, .. } => {
            if phase != Phase::Tick {
                return Err(not_here("delay"));
            }
            let buf = sfield(lw, &state, &format!("{name}.buf"), span)?;
            let w = sfield(lw, &state, &format!("{name}.w"), span)?;
            index(buf, w)?
        }
        Node::Vdelay { name, d, max, ty, .. } => {
            if phase != Phase::Tick {
                return Err(not_here("vdelay"));
            }
            vdelay_read(lw, cx, &mut stmts, &state, name, *d, *max, *ty, span)?
        }
        Node::Instance { name, callee, args, .. } => {
            if phase != Phase::Tick {
                return Err(not_here("a flow instance"));
            }
            let sub = lw.ensure_flow(*callee)?;
            let ret = lw.m.fn_(sub.tick).ret.clone();
            let mut cargs = vec![inout(sfield(lw, &state, name, span)?)];
            cargs.extend(instance_args(lw, cx, *callee, args, Rate::Sig)?.into_iter().map(borrow));
            call(sub.tick, ret, span, cargs)
        }
        Node::Par { name, var, from, to, body, nodes, .. } => {
            let ty = lw.core_ty(cx.info.expr_types[&e], &[], span)?;
            let arr = cx.temp(name, ty.clone());
            stmts.push(stmt(span, StmtKind::Let(arr, Expr::new(ty.clone(), span, ExprKind::Zeroed))));
            let arr_e = local_expr(cx, arr, span);
            let idx = replica_index(cx, *var, *from, span);
            let elem_state = if node_has_state(&node) {
                index(sfield(lw, &state, name, span)?, idx.clone())?
            } else {
                state.clone()
            };
            cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem_state.clone() });
            let mut loop_body = Vec::new();
            let v = lower_expr(lw, cx, *body)?;
            assign(&mut loop_body, &index(arr_e.clone(), idx)?, v)?;
            if phase == Phase::Tick {
                store_nodes(lw, cx, &mut loop_body, nodes, &elem_state)?;
            }
            cx.flow.as_mut().unwrap().scopes.pop();
            let b = Block { stmts: loop_body, value: None };
            stmts.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
            arr_e
        }
    };
    // Memoise in a temporary: later references (end-of-tick stores) read the
    // same value. A `par` result is already a temporary.
    let result = if matches!(value.kind, ExprKind::Local(_)) {
        value
    } else {
        let tmp = cx.temp(node.name(), value.ty.clone());
        stmts.push(stmt(span, StmtKind::Let(tmp, value)));
        local_expr(cx, tmp, span)
    };
    cx.flow.as_mut().unwrap().expr_override.insert(e, result.clone());
    let ty = result.ty.clone();
    Ok(Some(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(result)) }))))
}

/// The read side of `vdelay` (§11.4), in the fixed operation order.
#[allow(clippy::too_many_arguments)]
fn vdelay_read(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    stmts: &mut Vec<Stmt>,
    state: &Expr,
    name: &str,
    d: ExprId,
    max: u32,
    ty: onsa_sema::ty::TyId,
    span: Span,
) -> R<Expr> {
    let t = lw.core_ty(ty, &[], span)?;
    let Ty::Float(kind) = t else { return Err(internal(span, "vdelay on a non-float")) };
    let len = max + 1;
    let mut let_ = |cx: &mut FnCx, n: &str, v: Expr| -> Expr {
        let l = cx.temp(&format!("{name}.{n}"), v.ty.clone());
        stmts.push(stmt(span, StmtKind::Let(l, v)));
        local_expr(cx, l, span)
    };
    let d_e = lower_expr(lw, cx, d)?;
    let d_e = let_(cx, "d", d_e);
    let one = float_lit(&t, 1.0, span)?;
    let maxf = float_lit(&t, max as f64, span)?;
    // dc = if d >= 1.0 { if d <= MAX { d } else { MAX } } else { 1.0 }   (NaN -> 1.0)
    let inner = Expr::new(
        t.clone(),
        span,
        ExprKind::IfExpr {
            cond: Box::new(cmp(CmpOp::Le, d_e.clone(), maxf.clone())),
            then: Block { stmts: Vec::new(), value: Some(Box::new(d_e.clone())) },
            else_: Block { stmts: Vec::new(), value: Some(Box::new(maxf)) },
        },
    );
    let dc = Expr::new(
        t.clone(),
        span,
        ExprKind::IfExpr {
            cond: Box::new(cmp(CmpOp::Ge, d_e.clone(), one.clone())),
            then: Block { stmts: Vec::new(), value: Some(Box::new(inner)) },
            else_: Block { stmts: Vec::new(), value: Some(Box::new(one.clone())) },
        },
    );
    let dc = let_(cx, "dc", dc);
    // k = dc.trunc_u32()
    let k = Expr::new(
        Ty::u32(),
        span,
        ExprKind::Prim {
            prim: Prim::TruncToInt { from: kind, to: IntKind::U32, sat: false },
            args: vec![borrow(dc.clone())],
        },
    );
    let k = let_(cx, "k", k);
    // f = dc - k.round_f32()
    let kf = Expr::new(
        t.clone(),
        span,
        ExprKind::Prim { prim: Prim::IntToFloat { from: IntKind::U32, to: kind }, args: vec![borrow(k.clone())] },
    );
    let f = let_(cx, "f", binary(BinOp::Sub, dc, kf));
    let buf = sfield(lw, state, &format!("{name}.buf"), span)?;
    let w = sfield(lw, state, &format!("{name}.w"), span)?;
    // a = buf[(w + L - k) % L]; b = buf[(w + L - k - 1) % L]
    let wlk = binary(BinOp::Sub, binary(BinOp::Add, w, u32_lit(span, len)), k);
    let wlk = let_(cx, "wlk", wlk);
    let a = index(buf.clone(), binary(BinOp::Rem, wlk.clone(), u32_lit(span, len)))?;
    let a = let_(cx, "a", a);
    let b = index(buf, binary(BinOp::Rem, binary(BinOp::Sub, wlk, u32_lit(span, 1)), u32_lit(span, len)))?;
    let b = let_(cx, "b", b);
    // y = ((1.0 - f) * a) + (f * b)
    let y = binary(BinOp::Add, binary(BinOp::Mul, binary(BinOp::Sub, one, f.clone()), a), binary(BinOp::Mul, f, b));
    Ok(y)
}

/// Channel `k` of a `Span` (only 0) / planar `[Span; N]` parameter, and the
/// number of its channels.
fn channel(e: &Expr, k: u32, span: Span) -> R<(Expr, u32)> {
    match &e.ty {
        Ty::Span(_) => Ok((e.clone(), 1)),
        Ty::Array(inner, n) if matches!(**inner, Ty::Span(_)) => Ok((index(e.clone(), u32_lit(span, k))?, *n)),
        _ => Err(internal(span, "length of a non-span")),
    }
}

fn len_of(s: Expr, span: Span) -> Expr {
    Expr::new(Ty::u32(), span, ExprKind::Prim { prim: Prim::Len, args: vec![borrow(s)] })
}

/// Length of a `Span` / planar `[Span; N]` parameter (the first channel).
fn span_len(e: &Expr, span: Span) -> R<Expr> {
    Ok(len_of(channel(e, 0, span)?.0, span))
}

/// The length of every channel of a `Span` / planar `[Span; N]` parameter
/// (R-22: the length check of `process` compares all of them).
fn channel_lens(e: &Expr, span: Span) -> R<Vec<Expr>> {
    let (_, n) = channel(e, 0, span)?;
    (0..n).map(|k| Ok(len_of(channel(e, k, span)?.0, span))).collect()
}

/// `process(inout s, params, <inputs>, inout <outputs>)` (§11.6).
fn gen_process<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Tick, Ty::Unit)?;
    let ps = g.member_params(lw, shape, "process")?;
    let span = g.span;
    let s = ps["s"].clone();
    let params = ps["params"].clone();
    let sig_inputs: Vec<(String, Ty)> = shape
        .flow
        .inputs
        .iter()
        .filter(|i| i.rate == Rate::Sig)
        .map(|i| Ok((i.name.clone(), lw.core_ty(i.ty, &[], i.span)?)))
        .collect::<R<_>>()?;
    // All spans, every channel of the planar ones, must have the same length (§11.6, R-22):
    // compared once, before any state moves (S-196); panic otherwise (poisoned at the export).
    let mut spans: Vec<Expr> = sig_inputs.iter().map(|(n, _)| ps[n].clone()).collect();
    spans.extend(shape.outputs.iter().map(|(n, _, _)| ps[n].clone()));
    let mut lens = Vec::new();
    for sp in &spans {
        lens.extend(channel_lens(sp, span)?);
    }
    let mut lens = lens.into_iter();
    let first = match lens.next() {
        Some(l) => l,
        // SPEC-GAP(S-407): no channel at all (no `sample` input, a `[T; 0]` output) gives no
        // length; channel 0 is read, which panics as an index out of range, as before R-22.
        None => span_len(spans.first().ok_or_else(|| internal(span, "flow without spans"))?, span)?,
    };
    let len = g.let_("len", first);
    let msg = lw.msg("span lengths differ");
    for other in lens {
        let bad = cmp(CmpOp::Ne, other, len.clone());
        let panic = Block {
            stmts: vec![stmt(span, StmtKind::Expr(Expr::new(Ty::Unit, span, ExprKind::Panic(msg))))],
            value: None,
        };
        g.stmts.push(stmt(span, StmtKind::If(bad, panic, Block::default())));
    }
    expr_stmt(&mut g.stmts, call(fns.ctl, Ty::Unit, span, vec![inout(s.clone()), borrow(params)]));
    // Sample loop: read every input, tick, write every output.
    let i = g.cx.temp("i", Ty::u32());
    let i_e = local_expr(&g.cx, i, span);
    let mut body = Vec::new();
    let mut tick_args = vec![inout(s.clone())];
    for (name, ty) in &sig_inputs {
        let sp = ps[name].clone();
        let v = match ty {
            Ty::Array(elem, n) => {
                let mut items = Vec::new();
                for c in 0..*n {
                    items.push(index(index(sp.clone(), u32_lit(span, c))?, i_e.clone())?);
                }
                let _ = elem;
                Expr::new(ty.clone(), span, ExprKind::Array(items))
            }
            _ => index(sp, i_e.clone())?,
        };
        let l = g.cx.temp(name, ty.clone());
        body.push(stmt(span, StmtKind::Let(l, v)));
        tick_args.push(borrow(local_expr(&g.cx, l, span)));
    }
    let v = call(fns.tick, shape.out_val.clone(), span, tick_args);
    let vl = g.cx.temp("v", shape.out_val.clone());
    body.push(stmt(span, StmtKind::Let(vl, v)));
    let v_e = local_expr(&g.cx, vl, span);
    for (name, _elem, planar) in &shape.outputs {
        let val = if shape.out_is_struct { field_by_name(lw, v_e.clone(), name, span)? } else { v_e.clone() };
        let sp = ps[name].clone();
        match planar {
            Some(n) => {
                for c in 0..*n {
                    let target = index(index(sp.clone(), u32_lit(span, c))?, i_e.clone())?;
                    assign(&mut body, &target, index(val.clone(), u32_lit(span, c))?)?;
                }
            }
            None => assign(&mut body, &index(sp, i_e.clone())?, val)?,
        }
    }
    g.stmts.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), len, Block { stmts: body, value: None })));
    g.finish(lw, fns.process, Ty::Unit, true, None);
    Ok(())
}

/// `process_inplace`: `process` with each paired span passed as input and output.
fn gen_process_inplace<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let Some(fid) = fns.process_inplace else { return Ok(()) };
    let mut g = Gen::new(lw, shape, info, Phase::Tick, Ty::Unit)?;
    let ps = g.member_params(lw, shape, "process_inplace")?;
    let span = g.span;
    let mut args = vec![inout(ps["s"].clone()), borrow(ps["params"].clone())];
    for (name, _, _) in &shape.outputs {
        args.push(borrow(ps[name].clone()));
    }
    for (name, _, _) in &shape.outputs {
        args.push(inout(ps[name].clone()));
    }
    expr_stmt(&mut g.stmts, call(fns.process, Ty::Unit, span, args));
    g.finish(lw, fid, Ty::Unit, true, None);
    Ok(())
}

/// `render(cfg, params, <inputs>, [frames], sample_rate) -> Out` (interpreter only).
fn gen_render<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let out_ty = Ty::Struct(shape.out_ty);
    let mut g = Gen::new(lw, shape, info, Phase::Tick, out_ty.clone())?;
    let ps = g.member_params(lw, shape, "render")?;
    let span = g.span;
    let st = g.let_(
        "s",
        call(
            fns.init,
            Ty::Struct(shape.state_ty),
            span,
            vec![borrow(ps["cfg"].clone()), borrow(ps["sample_rate"].clone())],
        ),
    );
    let sig_names: Vec<String> =
        shape.flow.inputs.iter().filter(|i| i.rate == Rate::Sig).map(|i| i.name.clone()).collect();
    let n = match sig_names.first() {
        Some(first) => span_len(&ps[first], span)?,
        None => ps["frames"].clone(),
    };
    let n = g.let_("n", n);
    let process_params = member_params(lw, &shape.flow, "process", span)?;
    let mut args = vec![inout(st), borrow(ps["params"].clone())];
    for name in &sig_names {
        args.push(borrow(ps[name].clone()));
    }
    let mut out_fields = Vec::new();
    for (name, elem, planar) in &shape.outputs {
        let zeroed = |n: Expr| {
            Expr::new(
                Ty::Buf(Box::new(elem.clone())),
                span,
                ExprKind::Prim { prim: Prim::BufZeroed, args: vec![borrow(n)] },
            )
        };
        let v = match planar {
            Some(c) => {
                let items = (0..*c).map(|_| zeroed(n.clone())).collect();
                Expr::new(Ty::Array(Box::new(Ty::Buf(Box::new(elem.clone()))), *c), span, ExprKind::Array(items))
            }
            None => zeroed(n.clone()),
        };
        let buf = g.let_(name, v);
        let want = process_params
            .iter()
            .find(|(pn, _, _)| pn == name)
            .map(|(_, _, t)| t.clone())
            .ok_or_else(|| internal(span, "output without a process parameter"))?;
        let as_span = coerce(lw, &mut g.cx, buf.clone(), &want, Mode::Inout)?;
        args.push(inout(as_span));
        out_fields.push(buf);
    }
    expr_stmt(&mut g.stmts, call(fns.process, Ty::Unit, span, args));
    let out = Expr::new(out_ty.clone(), span, ExprKind::Struct { ty: shape.out_ty, fields: out_fields });
    g.finish(lw, fns.render, out_ty, false, Some(out));
    Ok(())
}

/// `params_default() -> Params` from the `@param` defaults (§11.7).
fn gen_params_default<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let Some(fid) = fns.params_default else { return Ok(()) };
    let ty = Ty::Struct(shape.params_ty);
    let g = Gen::new(lw, shape, info, Phase::Init, ty.clone())?;
    let span = g.span;
    let mut fields = Vec::new();
    for i in shape.flow.inputs.iter().filter(|i| i.rate == Rate::Ctl) {
        let t = lw.core_ty(i.ty, &[], i.span)?;
        let d = i
            .param
            .as_ref()
            .and_then(|p| p.default)
            .ok_or_else(|| internal(span, "params_default without a default"))?;
        fields.push(float_lit(&t, d, i.span)?);
    }
    let v = Expr::new(ty.clone(), span, ExprKind::Struct { ty: shape.params_ty, fields });
    g.finish(lw, fid, ty, false, Some(v));
    Ok(())
}
