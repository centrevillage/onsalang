//! The phase functions of a flow (§11.4): `init`, `reset`, `ctl`, `tick`
//! and those of the slower ticks, each with the work of its nodes, and the
//! driver of the slower ticks ([`drive`]).

use super::*;
use onsa_sema::flow::EventFrom;

/// `init(cfg, sample_rate) -> State`.
pub(super) fn gen_init<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let state_ty = Ty::Struct(shape.state_ty);
    let mut g = Gen::new(lw, shape, info, ClockStage::Init, state_ty.clone())?;
    let [cfg, sr] = &g.member_params(lw, shape, FlowFn::Init)?[..] else {
        return Err(internal(g.span, "`init` with another number of parameters"));
    };
    let (cfg, sr) = (cfg.clone(), sr.clone());
    let s = g.temp("s", state_ty.clone());
    let span = g.span;
    g.stmts.push(stmt(
        span,
        StmtKind::Let(
            LocalId(s.as_place().map(|p| p.root()).unwrap().0),
            Expr::new(state_ty.clone(), span, ExprKind::Zeroed),
        ),
    ));
    g.flow().now.sample_rate = sr.clone();
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    if info.stored(Kept::SampleRate) {
        let f = sfield(lw, info, &s, FieldOf::SampleRate, span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    restart(lw, &mut g.cx, &mut g.stmts, &s)?;
    g.inputs_from(lw, shape, info, &cfg, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    end(lw, &mut g, info, &s)?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    // S-27: the last store of `init`; a panic before it leaves the instance uninitialized.
    let initialized = sfield(lw, info, &s, FieldOf::Initialized, span)?;
    assign(&mut g.stmts, &initialized, lit(Ty::Bool, span, Lit::Bool(true)))?;
    g.finish(lw, fns.init, state_ty, false, Some(s));
    Ok(())
}

/// The plan of the flow `cx` lowers.
fn plan<'b>(cx: &FnCx<'b>) -> &'b FlowInfo {
    cx.flow.as_ref().expect("flow context").info
}

/// The work of a phase function on one node, in the scope of the state
/// given ([`each_node`]).
type NodeWork<'f> = dyn FnMut(&mut Lowerer, &mut FnCx, &mut Vec<Stmt>, NodeId, &Expr) -> R<()> + 'f;

/// The stage of the function `cx` lowers.
fn stage(cx: &FnCx) -> ClockStage {
    cx.flow.as_ref().expect("flow context").now.stage
}

/// The work `f` of each of the nodes `ids` in the order of the table, in
/// the scope of `state`; after the work of a `par~` that holds state, its
/// children in a loop of its replicas, each in the scope of its element of
/// the state, if they have any.
fn each_node(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    ids: &[NodeId],
    state: &Expr,
    f: &mut NodeWork,
) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let span = cx.ast.expr(n.expr).span;
        f(lw, cx, out, id, state)?;
        let PlanKind::Par { children, state: true, .. } = &n.kind else { continue };
        let (r, elem) = replicas(lw, cx, id, state, span)?;
        let mut body = Vec::new();
        cx.flow.as_mut().unwrap().push_scope(elem.clone());
        each_node(lw, cx, &mut body, children, &elem, f)?;
        cx.flow.as_mut().unwrap().now.scopes.pop();
        if !body.is_empty() {
            r.each(cx, out, span, body);
        }
    }
    Ok(())
}

/// The initialisation of the delay `id` (§11.4) where it is written, or at
/// the end of `init` of one of `FlowInfo::late`.
pub(super) fn init_delay(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, name, at) = (cx.ast.expr(n.expr).span, &n.path, |p| FieldOf::Node(id, p));
    let state = &super::branches::here(cx, span)?.1;
    let late = |i: &InitArg| matches!(i, InitArg::Init(e) if info.late.contains(e));
    match &n.kind {
        PlanKind::Prev { init, .. } | PlanKind::Delay { init, .. } | PlanKind::Vdelay { init, .. }
            if late(init) != cx.flow.as_ref().expect("flow context").now.saving => {}
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let v = init_value(lw, init, &t, span, |lw, e| lower_expr(lw, cx, e))?;
            let v = materialize(cx, v, out, &format!("{name}.init"));
            if info.field(at(Part::Init)).is_some() {
                assign(out, &sfield(lw, info, state, at(Part::Init), span)?, v.clone())?;
            }
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
        }
        PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = ring_len(&n.kind, span)?;
            let v = init_value(lw, init, &t, span, |lw, e| lower_expr(lw, cx, e))?;
            let v = materialize(cx, v, out, &format!("{name}.init"));
            if info.field(at(Part::Init)).is_some() {
                assign(out, &sfield(lw, info, state, at(Part::Init), span)?, v.clone())?;
            }
            let buf = sfield(lw, info, state, at(Part::Buf), span)?;
            let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
            assign(out, &buf, fill)?;
            assign(out, &sfield(lw, info, state, at(Part::W), span)?, u32_lit(span, 0))?;
        }
        PlanKind::Instance { .. } | PlanKind::Par { .. } => return Err(internal(span, "the `init` of no delay")),
    }
    Ok(())
}

/// The `init` or the `ctl` of the instance `id` in the function of that
/// stage (§11.4), with the `Config` or the `Params` of its arguments.
pub(super) fn own_stage(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let span = cx.ast.expr(n.expr).span;
    let PlanKind::Instance { callee, .. } = n.kind else { return Err(internal(span, "a stage of no instance")) };
    // W7-21 U1: a chain of a callee with no table (in error) has no entries.
    // A chain of an instance (`PlanNode::chained_delay` is of a delay).
    if !n.chain.is_empty() && n.entries.is_empty() {
        return Err(internal(span, "a chain of an instance with no entries"));
    }
    let sub = lw.ensure_flow(callee)?;
    let fields = super::chain::inputs_of(lw, cx, out, id, state)?;
    let st = sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?;
    let arg = |ty| Expr::new(Ty::Struct(ty), span, ExprKind::Struct { ty, fields });
    if stage(cx) == ClockStage::Block {
        expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(arg(sub.params))]));
        return Ok(());
    }
    let sr = super::child_rate(&cx.flow.as_ref().expect("flow context").now.sample_rate, n, span)?;
    let c = call(sub.init, Ty::Struct(sub.state), span, vec![borrow(arg(sub.config)), borrow(sr)]);
    assign(out, &st, c)
}

/// The time of `init` and `reset` in the state `s` (§11.6, §11.9): the
/// counter of the phase and `_tick_hi` at 0, the one place that
/// writes it, then the fields written at a tick and read at a faster stage
/// at `T.default()` ([`defaults`], which alone a `.reset_if~` writes,
/// [`ensure_reset_kept`]).
fn restart(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, s: &Expr) -> R<()> {
    let (info, span) = (plan(cx), s.span);
    if info.counts_time() {
        assign(out, &sfield(lw, info, s, FieldOf::Tick, span)?, u32_lit(span, 0))?;
    }
    if info.wide() {
        assign(out, &sfield(lw, info, s, FieldOf::TickHi, span)?, u32_lit(span, 0))?;
    }
    defaults(lw, cx, out, &info.fields, s)
}

/// The fields of `fields` of the struct `state` that start at
/// `T.default()` (§11.3, S-1186, [`FlowInfo::starts_default`]) set to it,
/// written so and not left to the zeroed state (a hand-written `Default`),
/// and those of the replicas of a `par~` among them in a loop of them.
fn defaults(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, fields: &[Field], state: &Expr) -> R<()> {
    let (info, span) = (plan(cx), state.span);
    for f in fields {
        if info.starts_default(f.of) {
            let place = sfield(lw, info, state, f.of, span)?;
            let v = crate::lower::derived::default_value(lw, &place.ty, span)?;
            assign(out, &place, v)?;
        }
        let FieldOf::Node(id, Part::Own) = f.of else { continue };
        let PlanKind::Par { fields: inner, .. } = &info.node(id).kind else { continue };
        if !starts_default(info, inner) {
            continue;
        }
        let (r, elem) = replicas(lw, cx, id, state, span)?;
        let mut body = Vec::new();
        defaults(lw, cx, &mut body, inner, &elem)?;
        r.each(cx, out, span, body);
    }
    Ok(())
}

/// Whether one of `fields` starts at `T.default()`, in a replica too.
fn starts_default(info: &FlowInfo, fields: &[Field]) -> bool {
    fields.iter().any(|f| {
        info.starts_default(f.of)
            || matches!(f.of, FieldOf::Node(id, Part::Own)
                if matches!(&info.node(id).kind, PlanKind::Par { fields, .. } if starts_default(info, fields)))
    })
}

/// `reset(inout s)`.
pub(super) fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, ClockStage::Init, Ty::Unit)?;
    let span = g.span;
    let [s] = &g.member_params(lw, shape, FlowFn::Reset)?[..] else {
        return Err(internal(span, "`reset` with another number of parameters"));
    };
    let s = s.clone();
    g.flow().push_scope(s.clone());
    restart(lw, &mut g.cx, &mut g.stmts, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let work = &mut |lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id, s: &Expr| {
        reset_node(lw, cx, out, id, s, Keep::Hard)
    };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, work)?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    g.finish(lw, fns.reset, Ty::Unit, true, None);
    Ok(())
}

/// What a reset of an instance keeps (§11.9, §11.10): nothing (`reset`), or
/// its counters and the conditions and the counts of its guards
/// (`reset_if~`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Keep {
    Hard,
    Kept,
}

/// `<flow>._reset_kept(inout s)` of the flow `flow` (§11.10), made once when
/// a `.reset_if~` of an instance of it is first lowered: the fields of a
/// tick read faster at `T.default()` ([`defaults`]) and each node back to
/// its start ([`reset_node`] that keeps), of an instance its own (made
/// first, a tree of calls with no loop, E0817). No counter, no `_poisoned`.
pub(super) fn ensure_reset_kept(lw: &mut Lowerer, flow: DefId, span: Span) -> R<FnId> {
    let fns = lw.ensure_flow(flow)?;
    if let Some(f) = fns.reset_kept {
        return Ok(f);
    }
    let a: &onsa_sema::Analysis = lw.a;
    let info = a.flows.get(&flow).ok_or_else(|| internal(span, "an instance of no checked flow"))?;
    let at = a.def(flow).span;
    let f = super::push_fn(lw, format!("{}._reset_kept", lw.qual_name(flow)), true, at);
    lw.flow_fns.get_mut(&flow).into_iter().for_each(|x| x.reset_kept = Some(f));
    lw.m.flows.iter_mut().filter(|m| m.fns.flow == flow).for_each(|m| m.fns.reset_kept = Some(f));
    let mut g = Gen::of(lw, (flow, at), info, ClockStage::Init, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(fns.state));
    g.flow().push_scope(s.clone());
    defaults(lw, &mut g.cx, &mut g.stmts, &info.fields, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let work = &mut |lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id, s: &Expr| {
        reset_node(lw, cx, out, id, s, Keep::Kept)
    };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, work)?;
    g.finish(lw, f, Ty::Unit, true, None);
    Ok(f)
}

/// A node back to its value after `init` (§11.4), from the copy of its
/// `init` value the state `s` keeps; of an instance by `k` ([`Keep`]), and
/// of `reset` the condition and the count of each guard of its chain.
pub(super) fn reset_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, s: &Expr, k: Keep) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    match &n.kind {
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, s, at(Part::Init), span))?;
            assign(out, &sfield(lw, info, s, at(Part::Own), span)?, v)?;
        }
        PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = ring_len(&n.kind, span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, s, at(Part::Init), span))?;
            let buf = sfield(lw, info, s, at(Part::Buf), span)?;
            let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
            assign(out, &buf, fill)?;
            assign(out, &sfield(lw, info, s, at(Part::W), span)?, u32_lit(span, 0))?;
        }
        PlanKind::Instance { callee, .. } => {
            let st = sfield(lw, info, s, at(Part::Own), span)?;
            let f = match k {
                Keep::Kept => ensure_reset_kept(lw, *callee, span)?,
                Keep::Hard => lw.ensure_flow(*callee)?.reset,
            };
            expr_stmt(out, call(f, Ty::Unit, span, vec![inout(st)]));
        }
        PlanKind::Par { .. } => {}
    }
    // The condition and the count of each guard of its chain (§11.9: `reset`, not `reset_if~`).
    for g in (0..n.guards.len() as u32).filter(|_| k == Keep::Hard) {
        for (part, v) in [(Part::On(g), lit(Ty::Bool, span, Lit::Bool(false))), (Part::Count(g), u32_lit(span, 0))] {
            if info.field_at(at(part)).is_some() {
                assign(out, &sfield(lw, info, s, at(part), span)?, v)?;
            }
        }
    }
    // Up after a panic between its place and its store (S-1250).
    for part in n.late_flags().into_iter().filter(|_| k == Keep::Hard) {
        assign(out, &sfield(lw, info, s, at(part), span)?, lit(Ty::Bool, span, Lit::Bool(false)))?;
    }
    Ok(())
}

/// `ctl(inout s, p: Params)`.
pub(super) fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, ClockStage::Block, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let p = g.param("p", Mode::Borrow, Ty::Struct(shape.params_ty));
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    g.inputs_from(lw, shape, info, &p, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    end(lw, &mut g, info, &s)?;
    g.finish(lw, fns.ctl, Ty::Unit, true, None);
    Ok(())
}

/// The function of the stage `stage` (§11.4, §11.9): `tick(inout s, [t],
/// <Sig inputs>)` of the `sample` of the body, `tick_<N>(inout s, [t],
/// <its inputs>)` of a slower one, `ev_<k>(inout s, [t], [<its replica>],
/// <its event>)` of a source of events (§11.11), which [`drive`] or a caller
/// ([`super::chain::entry`]) calls through [`call_stage`]; the words of the
/// time `t`, `t_hi` of a stage that takes them (`FlowInfo::time_words`).
/// In order (§11.3, S-1233): its inputs the state keeps stored, its `let`s
/// and its work in the others ([`Gen::stage_lets`]), the output of the stage
/// that makes it (`FlowInfo::out_stage`), the stores of its nodes ([`end`]),
/// and last in `tick` the counter of the phase advanced when it is
/// the grid of the slower stages (`FlowInfo::counter`). Its value is the
/// output, or what the stage it ticks gave of it (`FlowInfo::gives`, of a
/// tick that gives several an array of them, `FlowInfo::burst`).
pub(super) fn gen_stage<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
    stage: ClockStage,
) -> R<()> {
    let span = shape.span;
    let fid = fns.stage_fn(stage).ok_or_else(|| internal(span, format!("no function of the stage {stage:?}")))?;
    let makes_out = info.out_stage == Some(stage);
    let gives = info.gives(stage) && !makes_out;
    // Several of a tick, which runs the stage of an `.up~` (an event ticks a stage once).
    let many = Some(info.burst).filter(|&n| gives && n > 1 && !matches!(stage, ClockStage::Event(_)));
    let out_ty = match many {
        Some(n) => Ty::Array(Box::new(shape.out_val.clone()), n),
        None if makes_out || gives => shape.out_val.clone(),
        None => Ty::Unit,
    };
    let mut g = Gen::new(lw, shape, info, stage, out_ty.clone())?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    for name in ["t", "t_hi"].into_iter().take(info.time_words(stage)) {
        let t = g.param(name, Mode::Borrow, Ty::u32());
        g.flow().now.time.push(t);
    }
    let inputs: Vec<&Input> = shape.inputs.iter().filter(|i| i.stage == stage).collect();
    for i in &inputs {
        g.param_local(LocalId(i.local.0), Mode::Borrow);
    }
    if let ClockStage::Event(src) = stage
        && let Some(EventFrom::Call(id)) = info.event(src).map(|p| p.from)
    {
        let t = g.cx.info.expr_types.get(&info.node(id).expr).copied();
        let t = t.ok_or_else(|| internal(span, "an event of no type"))?;
        let t = lw.core_ty(t, &[], span)?;
        for p in info.around(info.node(id).owner) {
            g.param_local(LocalId(range(info, p, span)?.0.0), Mode::Borrow);
            g.flow().now.pinned.push(p);
        }
        let v = g.param("ev", Mode::Borrow, t);
        g.flow().now.source = Some(v);
    }
    g.flow().events = fns.events.clone();
    g.flow().push_scope(s.clone());
    // S-1213: an input at `sample / N` is the argument of its tick,
    // kept until the next (an argument of a parameter kind too).
    for i in inputs {
        if let Some(of) = info.kept_field(i.local) {
            let v = local_expr(&g.cx, LocalId(i.local.0), i.decl.span);
            assign(&mut g.stmts, &sfield(lw, info, &s, of, i.decl.span)?, v)?;
        }
    }
    g.slots(info)?;
    g.state_overrides(lw, info, &s)?;
    let mut out = None;
    if gives {
        let Ty::Enum(ty) = shape.out_val else { return Err(internal(span, "an event given out in no `Option`")) };
        let none = ExprKind::Variant { ty, tag: super::event_option(lw.a, span)?.exit, fields: Vec::new() };
        let mut none = Expr::new(shape.out_val.clone(), span, none);
        if let Some(n) = many {
            none = Expr::new(out_ty.clone(), span, ExprKind::Repeat { elem: Box::new(none), n });
        }
        let gave = g.let_("__out", none);
        let next = many.map(|_| g.let_("__n", u32_lit(span, 0)));
        g.flow().now.gave = Some(super::Gave { out: gave.clone(), next });
        out = Some(gave);
    }
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    if makes_out {
        let output = info.output.ok_or_else(|| internal(span, "flow without an output expression"))?;
        let v = lower_expr(lw, &mut g.cx, output)?;
        let v = of_type(v, &out_ty)?;
        // Materialised before the stores so a `prev` inside the output reads first (§11.4).
        out = Some(g.let_("__out", v));
    }
    end(lw, &mut g, info, &s)?;
    if stage == ClockStage::SAMPLE && info.counter() == Counter::Tick {
        let t = sfield(lw, info, &s, FieldOf::Tick, span)?;
        assign(&mut g.stmts, &t, wrap_add(t.clone(), span))?;
    }
    g.finish(lw, fid, out_ty, true, out);
    Ok(())
}

/// The end of the stage (§11.3, §11.4): the stores and what of the stage is
/// evaluated with them ([`store_node`]); then the head of the function.
fn end<'b>(lw: &mut Lowerer<'b>, g: &mut Gen<'b>, info: &'b FlowInfo, s: &Expr) -> R<()> {
    g.flow().now.saving = true;
    let nodes: Vec<NodeId> = info.top().collect();
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, s, &mut store_node)?;
    let heads = std::mem::take(&mut g.flow().now.heads);
    g.stmts.splice(0..0, heads);
    Ok(())
}

/// A run of the stage `x` of a flow whose plan is `g` (§11.9, S-1088):
/// its function `f` of the result `ret` on `state`, with the words of the
/// time it takes cut from `time` (made in `lets`) and its inputs of that
/// stage, lowered.
pub(super) struct StageRun<'g> {
    pub g: &'g FlowInfo,
    pub f: FnId,
    pub ret: Ty,
    pub x: ClockStage,
    pub state: Expr,
    pub time: Vec<Expr>,
    pub lets: Vec<Stmt>,
    pub inputs: Vec<Expr>,
}

/// The call of the run `r`, after its `lets`: the one place that calls
/// the function of a stage of a flow, of `process` ([`drive`]) and of a
/// caller ([`super::chain::entry`]); the time cut to the words its stage
/// takes (`FlowInfo::time_words`).
pub(super) fn call_stage(r: StageRun, span: Span) -> R<Expr> {
    let time = r.time.get(..r.g.time_words(r.x)).ok_or_else(|| internal(span, "a stage of more time"))?;
    let time = time.iter().cloned().map(borrow);
    let args = [inout(r.state)].into_iter().chain(time).chain(r.inputs.into_iter().map(borrow)).collect();
    Ok(after(r.lets, call(r.f, r.ret, span, args)))
}

/// The statements of each stage of `runs` (slowest first, S-578, S-1079),
/// each run when the counter `c` is at the ticks of its stage, a multiple
/// of its N, so the first frame runs it and the tick does not depend on how
/// the host splits the frames (§11.9). The one drive of the stages of a
/// part: of `process` (`c` the counter of the phase of its state, a run of
/// [`call_stage`] of each stage; the runs j of an `.up~`, `c` the j, and
/// the grid of a `when~` of W7-10 too). The stage of `sample` runs at each.
pub(super) fn drive(runs: Vec<(ClockStage, Vec<Stmt>)>, c: &Expr, span: Span, out: &mut Vec<Stmt>) -> R<()> {
    for (stage, run) in runs {
        if stage == ClockStage::SAMPLE {
            out.extend(run);
            continue;
        }
        let mask = match stage {
            ClockStage::Tick(k) => k.made_n().and_then(|n| u32::try_from(n - 1).ok()),
            ClockStage::Init | ClockStage::Block | ClockStage::Event(_) => None,
        };
        let mask = mask.ok_or_else(|| internal(span, format!("no counter of the tick {stage:?}")))?;
        let low = checked_binary(BinOp::BitAnd, c.clone(), u32_lit(span, mask));
        let due = cmp(CmpOp::Eq, low, u32_lit(span, 0));
        out.push(stmt(span, StmtKind::If(due, Block { stmts: run, value: None }, Block::default())));
    }
    Ok(())
}

/// The time of the outermost advanced after its `tick` (§11.4, S-1217,
/// S-1211): the counter of the time alone ([`Counter::Process`]), then
/// `_tick_hi` when `_tick` goes round. The one place of it.
pub(super) fn advance(lw: &Lowerer, info: &FlowInfo, s: &Expr, span: Span, out: &mut Vec<Stmt>) -> R<()> {
    let t = || sfield(lw, info, s, FieldOf::Tick, span);
    if info.counter() == Counter::Process {
        assign(out, &t()?, wrap_add(t()?, span))?;
    }
    if info.wide() {
        let (hi, mut carry) = (sfield(lw, info, s, FieldOf::TickHi, span)?, Vec::new());
        assign(&mut carry, &hi, wrap_add(hi.clone(), span))?;
        let round = cmp(CmpOp::Eq, t()?, u32_lit(span, 0));
        out.push(stmt(span, StmtKind::If(round, Block { stmts: carry, value: None }, Block::default())));
    }
    Ok(())
}

/// `x +% 1` of a `U32`.
pub(super) fn wrap_add(x: Expr, span: Span) -> Expr {
    let (lhs, rhs) = (Box::new(x), Box::new(u32_lit(span, 1)));
    Expr::new(Ty::u32(), span, ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Wrap, lhs, rhs })
}

/// The end-of-tick store of a node (§11.4) in node order (S-1126, S-1154):
/// `prev` saves its argument, `delay` / `vdelay` write the argument at `w`
/// and advance; a `par~` that stores stores its replicas in a loop of its
/// own at its place in the order ([`each_node`]). Of a delay of another
/// stage, the work of this one in its first argument that reads a `^name`
/// (`FlowInfo::late`, S-1244).
///
/// They are the second phase of §11.4 (read all, then store all) with no
/// temporaries of their own: each node is read once where it is lowered
/// (memoised), a node of the body before all the stores, and a node first
/// lowered here (in the first argument of a delay) in the store of the
/// nearest delay around it, which the order (preorder, the outer first)
/// puts before the node's own store. So no read sees a store of this tick.
/// A change of the order of the stores (W7-06, W7-09) keeps that: the read
/// of a node first lowered here comes before its store.
fn store_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let Some(arg) = n.kind.stored() else { return Ok(()) };
    if info.node_stage(id) != Some(stage(cx)) {
        return if info.late.is_empty() { Ok(()) } else { super::hoist::walk(lw, cx, arg, out) };
    }
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    let ring = match n.kind {
        PlanKind::Prev { .. } => None,
        PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => Some(ring_len(&n.kind, span)?),
        PlanKind::Instance { .. } | PlanKind::Par { .. } => return Err(internal(span, "a store of no delay")),
    };
    // Evaluated while a guard stops it too (§11.10), stored of a tick it ran (its `_ran`).
    let ran = info.field_at(at(Part::Ran)).map(|_| sfield(lw, info, state, at(Part::Ran), span)).transpose()?;
    let v = lower_expr(lw, cx, arg)?;
    let v = if ran.is_some() { materialize(cx, v, out, "__store") } else { v };
    let mut store = Vec::new();
    match ring {
        None => assign(&mut store, &sfield(lw, info, state, at(Part::Own), span)?, v)?,
        Some(len) => {
            let buf = sfield(lw, info, state, at(Part::Buf), span)?;
            let w = sfield(lw, info, state, at(Part::W), span)?;
            assign(&mut store, &index(buf, w.clone())?, v)?;
            let one = checked_binary(BinOp::Add, w.clone(), u32_lit(span, 1));
            assign(&mut store, &w, checked_binary(BinOp::Rem, one, u32_lit(span, len)))?;
        }
    }
    match ran {
        Some(ran) => out.push(stmt(span, StmtKind::If(ran, Block { stmts: store, value: None }, Block::default()))),
        None => out.extend(store),
    }
    super::chain::stored(lw, cx, out, id, state)
}
