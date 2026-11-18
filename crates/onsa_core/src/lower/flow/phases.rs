//! The phase functions of a flow (§11.4): `init`, `reset`, `ctl` and
//! `tick`, each with the work of its nodes.

use super::*;

/// `init(cfg, sample_rate) -> State`.
pub(super) fn gen_init<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
        let f = sfield(lw, info, &s, FieldOf::SampleRate, span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.clock != Clock::Init {
            continue;
        }
        let from_cfg = field_by_name(lw, cfg.clone(), &input.name, input.span)?;
        g.flow().local_override.insert(l.0, from_cfg.clone());
        if shape.state_locals.contains_key(&l.0) {
            let f = sfield(lw, info, &s, FieldOf::Input(*l), input.span)?;
            assign(&mut g.stmts, &f, from_cfg)?;
        }
    }
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, ClockStage::Init, &s)?;
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
            PlanKind::Delay { n: len, init, ty, .. } | PlanKind::Vdelay { max: len, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = if matches!(n.kind, PlanKind::Vdelay { .. }) { *len + 1 } else { *len };
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
                let fields = instance_args(lw, cx, *callee, args, Clock::Init)?;
                let cfg = Expr::new(Ty::Struct(sub.config), span, ExprKind::Struct { ty: sub.config, fields });
                let c = call(sub.init, Ty::Struct(sub.state), span, vec![borrow(cfg), borrow(sr.clone())]);
                assign(out, &sfield(lw, info, state, at(Part::Own), span)?, c)?;
            }
            PlanKind::Par { var, from, to, children, .. } => {
                if info.field(at(Part::Own)).is_none() {
                    continue;
                }
                let arr = sfield(lw, info, state, at(Part::Own), span)?;
                let idx = replica_index(cx, *var, *from, span);
                let elem = index(arr, idx)?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                init_nodes(lw, cx, &mut body, children, &elem, sr)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
            }
        }
    }
    Ok(())
}

/// `reset(inout s)`.
pub(super) fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Init, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let span = g.span;
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
            PlanKind::Delay { n: len, init, ty, .. } | PlanKind::Vdelay { max: len, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = if matches!(n.kind, PlanKind::Vdelay { .. }) { *len + 1 } else { *len };
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
            PlanKind::Par { var, from, to, children, .. } => {
                if info.field(at(Part::Own)).is_none() {
                    continue;
                }
                let arr = sfield(lw, info, state, at(Part::Own), span)?;
                let elem = index(arr, replica_index(cx, *var, *from, span))?;
                let mut body = Vec::new();
                reset_nodes(lw, cx, &mut body, children, &elem)?;
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
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
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.clock != Clock::Block {
            continue;
        }
        let from_p = field_by_name(lw, p.clone(), &input.name, input.span)?;
        g.flow().local_override.insert(l.0, from_p.clone());
        if shape.state_locals.contains_key(&l.0) {
            let f = sfield(lw, info, &s, FieldOf::Input(*l), input.span)?;
            assign(&mut g.stmts, &f, from_p)?;
        }
    }
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, ClockStage::Block, &s)?;
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
                let fields = instance_args(lw, cx, *callee, args, Clock::Block)?;
                let params = Expr::new(Ty::Struct(sub.params), span, ExprKind::Struct { ty: sub.params, fields });
                let st = sfield(lw, info, state, own, span)?;
                expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(params)]));
            }
            PlanKind::Par { var, from, to, children, .. } => {
                if info.field(own).is_none() {
                    continue;
                }
                let arr = sfield(lw, info, state, own, span)?;
                let elem = index(arr, replica_index(cx, *var, *from, span))?;
                let mut body = Vec::new();
                cx.flow.as_mut().unwrap().scopes.push(Scope { state: elem.clone() });
                ctl_nodes(lw, cx, &mut body, children, &elem)?;
                cx.flow.as_mut().unwrap().scopes.pop();
                let b = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(LocalId(var.0), u32_lit(span, *from), u32_lit(span, *to), b)));
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
    for (l, input) in info.inputs.iter().zip(&shape.flow.inputs) {
        if input.clock == Clock::SAMPLE {
            g.param_local(LocalId(l.0), Mode::Borrow);
        }
    }
    g.flow().scopes.push(Scope { state: s.clone() });
    g.state_overrides(lw, shape, info, &s)?;
    g.const_lets(lw, shape, info)?;
    g.rate_lets(lw, shape, info, ClockStage::SAMPLE, &s)?;
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
            PlanKind::Delay { arg, n: len, .. } | PlanKind::Vdelay { arg, max: len, .. } => {
                let len = if matches!(n.kind, PlanKind::Vdelay { .. }) { *len + 1 } else { *len };
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
