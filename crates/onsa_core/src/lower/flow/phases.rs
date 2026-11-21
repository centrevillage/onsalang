//! The phase functions of a flow (§11.4): `init`, `reset`, `ctl` and
//! `tick`, each with the work of its nodes.

use super::*;

/// `init(cfg, sample_rate) -> State`.
pub(super) fn gen_init<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let state_ty = Ty::Struct(shape.state_ty);
    let mut g = Gen::new(lw, shape, info, Phase::Init, state_ty.clone())?;
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
    g.flow().sample_rate = sr.clone();
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    if info.stored(Kept::SampleRate) {
        let f = sfield(lw, info, &s, FieldOf::SampleRate, span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    g.inputs_from(lw, shape, info, &cfg, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: Some(ClockStage::Init), loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut |lw, cx, out, id, s| {
        init_node(lw, cx, out, id, s, &sr)
    })?;
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

/// How a phase function walks the nodes ([`each_node`]).
#[derive(Clone, Copy)]
struct Walk {
    /// The stage the arms of the `match~`s around a node are chosen at
    /// before its work ([`super::branches::choose_arms`]), if the function
    /// chooses them.
    arms: Option<ClockStage>,
    /// Whether a `par~` of the children given, which holds state when the
    /// flag is set, has a loop of its replicas.
    loops: fn(&FlowInfo, &[NodeId], bool) -> bool,
}

/// A `par~` that holds state has a loop of its replicas, of no work too
/// (one of delays only in `ctl`).
fn held(_: &FlowInfo, _: &[NodeId], holds: bool) -> bool {
    holds
}

/// The work `f` of each of the nodes `ids` in the order of the table, in
/// the scope of `state`: the arms around a node chosen first; after the
/// work of a `par~`, its children in a loop of its replicas, each in the
/// scope of its element of the state.
fn each_node(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    ids: &[NodeId],
    state: &Expr,
    walk: Walk,
    f: &mut NodeWork,
) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let span = cx.ast.expr(n.expr).span;
        if let Some(s) = walk.arms {
            super::branches::choose_arms(lw, cx, &n.arms, s, state, out)?;
        }
        f(lw, cx, out, id, state)?;
        let PlanKind::Par { children, state: holds, .. } = &n.kind else { continue };
        if !(walk.loops)(info, children, *holds) {
            continue;
        }
        let r = replica_loop(cx, &n.kind, span)?;
        let elem = index(sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?, r.index(cx, span))?;
        let mut body = Vec::new();
        cx.flow.as_mut().unwrap().push_scope(elem.clone());
        each_node(lw, cx, &mut body, children, &elem, walk, f)?;
        cx.flow.as_mut().unwrap().scopes.pop();
        out.push(r.each(cx, span, body));
    }
    Ok(())
}

/// Node initialisation (§11.4): stores, buffers, sub `init`s.
fn init_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr, sr: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, name, at) = (cx.ast.expr(n.expr).span, &n.path, |p| FieldOf::Node(id, p));
    match &n.kind {
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
        PlanKind::Instance { callee, args, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            let fields = instance_args(lw, cx, *callee, args, Phase::Init, span)?;
            let cfg = Expr::new(Ty::Struct(sub.config), span, ExprKind::Struct { ty: sub.config, fields });
            let c = call(sub.init, Ty::Struct(sub.state), span, vec![borrow(cfg), borrow(sr.clone())]);
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, c)?;
        }
        PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// `reset(inout s)`.
pub(super) fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Init, Ty::Unit)?;
    let span = g.span;
    let [s] = &g.member_params(lw, shape, FlowFn::Reset)?[..] else {
        return Err(internal(span, "`reset` with another number of parameters"));
    };
    let s = s.clone();
    g.flow().push_scope(s.clone());
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: None, loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut reset_node)?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    g.finish(lw, fns.reset, Ty::Unit, true, None);
    Ok(())
}

/// A node back to its value after `init` (§11.4), from the copy of its
/// `init` value the state keeps.
fn reset_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    match &n.kind {
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, state, at(Part::Init), span))?;
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
        }
        PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = ring_len(&n.kind, span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, state, at(Part::Init), span))?;
            let buf = sfield(lw, info, state, at(Part::Buf), span)?;
            let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
            assign(out, &buf, fill)?;
            assign(out, &sfield(lw, info, state, at(Part::W), span)?, u32_lit(span, 0))?;
        }
        PlanKind::Instance { callee, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            let st = sfield(lw, info, state, at(Part::Own), span)?;
            expr_stmt(out, call(sub.reset, Ty::Unit, span, vec![inout(st)]));
        }
        PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// `ctl(inout s, p: Params)`.
pub(super) fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Ctl, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let p = g.param("p", Mode::Borrow, Ty::Struct(shape.params_ty));
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    g.inputs_from(lw, shape, info, &p, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: Some(ClockStage::Block), loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut ctl_node)?;
    g.finish(lw, fns.ctl, Ty::Unit, true, None);
    Ok(())
}

/// Sub `ctl`s with the sub's `Params` built from the `Ctl`-input arguments.
fn ctl_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let span = cx.ast.expr(n.expr).span;
    match &n.kind {
        PlanKind::Instance { callee, args, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            let fields = instance_args(lw, cx, *callee, args, Phase::Ctl, span)?;
            let params = Expr::new(Ty::Struct(sub.params), span, ExprKind::Struct { ty: sub.params, fields });
            let st = sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?;
            expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(params)]));
        }
        PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } | PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// `tick(inout s, <Sig inputs>) -> out`.
pub(super) fn gen_tick<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let out_ty = shape.out_val.clone();
    let mut g = Gen::new(lw, shape, info, Phase::Tick, out_ty.clone())?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    for i in shape.inputs.iter().filter(|i| i.phase == Phase::Tick) {
        g.param_local(LocalId(i.local.0), Mode::Borrow);
    }
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let output = info.output.ok_or_else(|| internal(shape.span, "flow without an output expression"))?;
    let v = lower_expr(lw, &mut g.cx, output)?;
    let v = of_type(v, &out_ty)?;
    // Materialised before the stores so a `prev` inside the output reads first (§11.4).
    let out_local = g.let_("__out", v);
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: None, loops: |info, children, _| stores(info, children) };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut store_node)?;
    g.finish(lw, fns.tick, out_ty, true, Some(out_local));
    Ok(())
}

/// The end-of-tick store of a node (§11.4) in node order: `prev` saves its
/// argument, `delay` / `vdelay` write the argument at `w` and advance; a
/// `par~` that stores ([`stores`]) stores its replicas in a loop of its own
/// at its place in the order ([`each_node`]).
///
/// They are the second phase of §11.4 (read all, then store all) with no
/// temporaries of their own: each node is read once where it is lowered
/// (memoised), a node of the body before all the stores, and a node first
/// lowered here (in the first argument of a delay) in the store of the
/// nearest delay around it, which the order (preorder, the outer first)
/// puts before the node's own store. So no read sees a store of this tick.
/// A change of the order of the stores (W7-06, W7-09) keeps that: the read
/// of a node first lowered here comes before its store.
// SPEC-GAP(S-1154): the stores (and their panics) are in the preorder of
// the table; S-1126 (1): after every `let` and the output of the body.
fn store_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let Some(arg) = stored_arg(&n.kind) else { return Ok(()) };
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    let ring = match n.kind {
        PlanKind::Prev { .. } => None,
        _ => Some(ring_len(&n.kind, span)?),
    };
    let v = lower_expr(lw, cx, arg)?;
    let Some(len) = ring else {
        return assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v);
    };
    let buf = sfield(lw, info, state, at(Part::Buf), span)?;
    let w = sfield(lw, info, state, at(Part::W), span)?;
    assign(out, &index(buf, w.clone())?, v)?;
    let next = checked_binary(BinOp::Rem, checked_binary(BinOp::Add, w.clone(), u32_lit(span, 1)), u32_lit(span, len));
    assign(out, &w, next)
}

/// The argument a node stores at the end of `tick` ([`store_node`]), the one
/// list of the nodes that store: a `prev` into its field, a `delay` /
/// `vdelay` into its ring; an instance stores in its own `tick`, a `par~` in
/// the loop of its replicas.
fn stored_arg(kind: &PlanKind) -> Option<ExprId> {
    match kind {
        PlanKind::Prev { arg, .. } | PlanKind::Delay { arg, .. } | PlanKind::Vdelay { arg, .. } => Some(*arg),
        PlanKind::Instance { .. } | PlanKind::Par { .. } => None,
    }
}

/// Whether the nodes `ids` store in `tick` ([`stored_arg`]), in a `par~`
/// of them too.
fn stores(info: &FlowInfo, ids: &[NodeId]) -> bool {
    ids.iter().any(|&id| match &info.node(id).kind {
        PlanKind::Par { children, .. } => stores(info, children),
        kind => stored_arg(kind).is_some(),
    })
}
