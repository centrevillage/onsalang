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
                let v = materialize(cx, v, out, &format!("{name}.init"));
                if matches!(init, InitArg::Init(_)) {
                    assign(out, &sfield(lw, state, &format!("{name}.init"), span)?, v.clone())?;
                }
                assign(out, &sfield(lw, state, name, span)?, v)?;
            }
            Node::Delay { name, n: len, init, ty, .. } | Node::Vdelay { name, max: len, init, ty, .. } => {
                let t = lw.core_ty(*ty, &[], span)?;
                let len = if matches!(n, Node::Vdelay { .. }) { *len + 1 } else { *len };
                let v = init_value(lw, cx, init, &t, span)?;
                let v = materialize(cx, v, out, &format!("{name}.init"));
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
pub(super) fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
pub(super) fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
pub(super) fn gen_tick<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
pub(super) fn store_nodes(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, nodes: &[Node], state: &Expr) -> R<()> {
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
                let next = checked_binary(
                    BinOp::Rem,
                    checked_binary(BinOp::Add, w.clone(), u32_lit(span, 1)),
                    u32_lit(span, len),
                );
                assign(out, &w, next)?;
            }
            // Instances store inside their own `tick`; `par` replicas store at the
            // end of each iteration of the loop that computes them.
            Node::Instance { .. } | Node::Par { .. } => {}
        }
    }
    Ok(())
}
