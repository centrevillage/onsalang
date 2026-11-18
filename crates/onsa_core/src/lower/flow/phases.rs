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
    g.flow().scopes.push(Scope { state: s.clone() });
    if info.stored(Kept::SampleRate) {
        let f = sfield(lw, info, &s, FieldOf::SampleRate, span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    g.inputs_from(lw, shape, info, &cfg, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.rate_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    init_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s, &sr)?;
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

/// Node initialisation (§11.4): stores, buffers, sub `init`s, replicas.
fn init_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, ids: &[NodeId], state: &Expr, sr: &Expr) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let (span, name, at) = (cx.ast.expr(n.expr).span, &n.path, |p| FieldOf::Node(id, p));
        match &n.kind {
            PlanKind::Prev { init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let v = init_value(lw, cx, init, &t, span)?;
                let v = materialize(cx, v, out, &format!("{name}.init"));
                if info.field(at(Part::Init)).is_some() {
                    assign(out, &sfield(lw, info, state, at(Part::Init), span)?, v.clone())?;
                }
                assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
            }
            PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = ring_len(&n.kind, span)?;
                let v = init_value(lw, cx, init, &t, span)?;
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
            PlanKind::Par { children, .. } => {
                if info.field(at(Part::Own)).is_none() {
                    continue;
                }
                let r = replica_loop(cx, &n.kind, span)?;
                let elem = index(sfield(lw, info, state, at(Part::Own), span)?, r.index(cx, span))?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                init_nodes(lw, cx, &mut body, children, &elem, sr)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                out.push(r.each(span, body));
            }
        }
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
    g.flow().scopes.push(Scope { state: s.clone() });
    let nodes: Vec<NodeId> = info.top().collect();
    reset_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    g.finish(lw, fns.reset, Ty::Unit, true, None);
    Ok(())
}

fn reset_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, ids: &[NodeId], state: &Expr) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
        match &n.kind {
            PlanKind::Prev { init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let v = match init {
                    InitArg::Const(c) => lw.const_value_expr(c, &t, span)?,
                    InitArg::Init(_) => sfield(lw, info, state, at(Part::Init), span)?,
                };
                assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
            }
            PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = ring_len(&n.kind, span)?;
                let v = match init {
                    InitArg::Const(c) => lw.const_value_expr(c, &t, span)?,
                    InitArg::Init(_) => sfield(lw, info, state, at(Part::Init), span)?,
                };
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
            PlanKind::Par { children, .. } => {
                if info.field(at(Part::Own)).is_none() {
                    continue;
                }
                let r = replica_loop(cx, &n.kind, span)?;
                let elem = index(sfield(lw, info, state, at(Part::Own), span)?, r.index(cx, span))?;
                let mut body = Vec::new();
                reset_nodes(lw, cx, &mut body, children, &elem)?;
                out.push(r.each(span, body));
            }
        }
    }
    Ok(())
}

/// `ctl(inout s, p: Params)`.
pub(super) fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Ctl, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let p = g.param("p", Mode::Borrow, Ty::Struct(shape.params_ty));
    g.flow().scopes.push(Scope { state: s.clone() });
    g.inputs_from(lw, shape, info, &p, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.rate_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    ctl_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    g.finish(lw, fns.ctl, Ty::Unit, true, None);
    Ok(())
}

/// Sub `ctl`s with the sub's `Params` built from the `Ctl`-input arguments.
fn ctl_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, ids: &[NodeId], state: &Expr) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let (span, own) = (cx.ast.expr(n.expr).span, FieldOf::Node(id, Part::Own));
        match &n.kind {
            PlanKind::Instance { callee, args, .. } => {
                let sub = lw.ensure_flow(*callee)?;
                let fields = instance_args(lw, cx, *callee, args, Phase::Ctl, span)?;
                let params = Expr::new(Ty::Struct(sub.params), span, ExprKind::Struct { ty: sub.params, fields });
                let st = sfield(lw, info, state, own, span)?;
                expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(params)]));
            }
            PlanKind::Par { children, .. } => {
                if info.field(own).is_none() {
                    continue;
                }
                let r = replica_loop(cx, &n.kind, span)?;
                let elem = index(sfield(lw, info, state, own, span)?, r.index(cx, span))?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                ctl_nodes(lw, cx, &mut body, children, &elem)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                out.push(r.each(span, body));
            }
            PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => {}
        }
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
    g.flow().scopes.push(Scope { state: s.clone() });
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.rate_lets(lw, info, &s)?;
    let output = info.output.ok_or_else(|| internal(shape.span, "flow without an output expression"))?;
    let v = lower_expr(lw, &mut g.cx, output)?;
    let v = of_type(v, &out_ty)?;
    // Materialised before the stores so a `prev` inside the output reads first (§11.4).
    let out_local = g.let_("__out", v);
    let nodes: Vec<NodeId> = info.top().collect();
    store_nodes(lw, &mut g.cx, &mut g.stmts, &nodes, &s)?;
    g.finish(lw, fns.tick, out_ty, true, Some(out_local));
    Ok(())
}

/// End-of-tick stores (§11.4) in node order: `prev` saves its argument,
/// `delay` / `vdelay` write the argument at `w` and advance.
pub(super) fn store_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, ids: &[NodeId], state: &Expr) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
        match &n.kind {
            PlanKind::Prev { arg, .. } => {
                let v = lower_expr(lw, cx, *arg)?;
                assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
            }
            PlanKind::Delay { arg, .. } | PlanKind::Vdelay { arg, .. } => {
                let len = ring_len(&n.kind, span)?;
                let v = lower_expr(lw, cx, *arg)?;
                let buf = sfield(lw, info, state, at(Part::Buf), span)?;
                let w = sfield(lw, info, state, at(Part::W), span)?;
                assign(out, &index(buf, w.clone())?, v)?;
                let next = checked_binary(
                    BinOp::Rem,
                    checked_binary(BinOp::Add, w.clone(), u32_lit(span, 1)),
                    u32_lit(span, len),
                );
                assign(out, &w, next)?;
            }
            // Instances store inside their own `tick`; `par` replicas store at the
            // end of each iteration of the loop that computes them.
            PlanKind::Instance { .. } | PlanKind::Par { .. } => {}
        }
    }
    Ok(())
}
