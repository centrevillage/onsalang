//! The on-demand value of a stateful node, `sample_rate()` or `par` while
//! an expression of the flow body is lowered (called from the lowering of
//! bodies).

use super::*;

/// On-demand value of a stateful node, `sample_rate()` or `par` while an
/// expression of the flow body is lowered. `None`: not a flow construct.
pub(crate) fn lower_flow_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Option<Expr>> {
    let span = cx.ast.expr(e).span;
    let (stage, info, id, state) = {
        let f = cx.flow.as_ref().expect("flow context");
        if let Some(v) = f.now.expr_override.get(&e) {
            return Ok(Some(v.clone()));
        }
        if f.sample_rate_calls.contains(&e) {
            return Ok(Some(f.now.sample_rate.clone()));
        }
        // A hoisted subexpression of an earlier stage: its field (§11.3), of
        // the scope it is lowered in: the `State` (a `let` or the output
        // holds it), or the replica of the `par~` whose body does (S-1140);
        // `sample_tick()` of a slower tick too (S-1210). Before it, the work
        // of this stage in it ([`super::hoist::work`]).
        if let Some(h) = f.info.hoist_of(e).filter(|&h| f.info.hoist(h).stage < f.now.stage) {
            let scope = f.now.scopes.last().ok_or_else(|| internal(span, "a hoisted field outside the state"))?;
            let v = sfield(lw, f.info, &scope.state, FieldOf::Hoist(h), span)?;
            super::hoist::record(lw, h, span, false)?;
            let mut stmts = Vec::new();
            super::hoist::walk(lw, cx, e, &mut stmts)?;
            return Ok(Some(after(stmts, v)));
        }
        // The time of the root its caller passes to the function (§11.4,
        // S-1129 (1)), at every stage.
        if f.sample_tick_calls.contains(&e) {
            let t = f.now.time.first().cloned();
            return t.map(Some).ok_or_else(|| internal(span, "`sample_tick()` in a function with no time"));
        }
        let Some(&id) = f.info.node_of.get(&e) else {
            // A modifier of a chain is the output of its head (§11.9).
            let Some(&receiver) = f.info.modifiers.get(&e) else { return Ok(None) };
            return lower_expr(lw, cx, receiver).map(Some);
        };
        let state = f.now.scopes.last().ok_or_else(|| internal(span, "node outside a state scope"))?.state.clone();
        (f.now.stage, f.info, id, state)
    };
    let name = &info.node(id).path;
    // A node is read in the function of the stage the plan gives it, a
    // `par~` where its body is.
    let outside = || internal(span, format!("`{name}` evaluated outside the function of its tick"));
    let mut stmts = Vec::new();
    let value = match &info.node(id).kind {
        PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => {
            let n = info.node(id);
            let arg = n.kind.stored().filter(|_| info.node_stage(id) == Some(stage)).ok_or_else(outside)?;
            // At the end of the stage, done where the delay is written.
            if !cx.flow.as_ref().expect("flow context").now.saving {
                super::hoist::walk(lw, cx, arg, &mut stmts)?;
                saved_reads(lw, cx, &mut stmts, &info.node(id).saved, (name, info.node(id).owner))?;
            }
            // Of a chain, read by the ops of its entry (§11.10).
            if !n.chained_delay() {
                delay_value(lw, cx, &mut stmts, &state, id)?
            } else {
                let v = super::chain::entry(lw, cx, &mut stmts, id, &state)?;
                super::chain::opened(lw, cx, &mut stmts, id)?;
                v.ok_or_else(|| internal(span, format!("`{name}` read of an entry of no value")))?
            }
        }
        PlanKind::Instance { .. } => {
            let v = instance(lw, cx, &mut stmts, id, false)?.ok_or_else(outside)?;
            return Ok(Some(after(stmts, v)));
        }
        PlanKind::Par { body, .. } => {
            let (r, elem_state) = replicas(lw, cx, id, &state, span)?;
            let ty = lw.core_ty(cx.info.expr_types[&e], &[], span)?;
            let arr = cx.temp(name, ty.clone());
            stmts.push(stmt(span, StmtKind::Let(arr, Expr::new(ty.clone(), span, ExprKind::Zeroed))));
            let arr_e = local_expr(cx, arr, span);
            let idx = r.index(cx, span);
            cx.flow.as_mut().unwrap().push_scope(elem_state);
            let mut loop_body = Vec::new();
            let v = lower_expr(lw, cx, *body)?;
            assign(&mut loop_body, &index(arr_e.clone(), idx)?, v)?;
            cx.flow.as_mut().unwrap().now.scopes.pop();
            r.each(cx, &mut stmts, span, loop_body);
            arr_e
        }
    };
    // Memoise in a temporary: later references (end-of-tick stores) read the
    // same value. A `par` result is already a temporary.
    let result = if matches!(value.kind, ExprKind::Local(_)) {
        value
    } else {
        let tmp = cx.temp(name, value.ty.clone());
        stmts.push(stmt(span, StmtKind::Let(tmp, value)));
        local_expr(cx, tmp, span)
    };
    cx.flow.as_mut().unwrap().now.expr_override.insert(e, result.clone());
    let ty = result.ty.clone();
    Ok(Some(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(result)) }))))
}

/// The work of the instance `id` in the function of the stage (§11.3,
/// S-1233), lowered where it is first reached, once: its arguments and its
/// conditions, then its `init`, its `ctl` or the ops of its entry
/// ([`super::chain::entry`]); then its value, of one read in the function
/// (of a chain that deals, the array of its outermost boundary that deals,
/// §11.9). `early`: in the first argument of a delay, whose store reads the
/// value at the end of the stage.
pub(super) fn instance(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    id: NodeId,
    early: bool,
) -> R<Option<Expr>> {
    let now = &cx.flow.as_ref().expect("flow context").now;
    if let Some(v) = now.done.get(&id) {
        return Ok(v.clone());
    }
    let info = cx.flow.as_ref().expect("flow context").info;
    let (n, span) = (info.node(id), cx.ast.expr(info.node(id).expr).span);
    let (stage, state) = super::branches::here(cx, span)?;
    let value = match stage {
        ClockStage::Init | ClockStage::Block => super::phases::own_stage(lw, cx, out, id, &state).map(|()| None)?,
        ClockStage::Event(_) | ClockStage::Tick(_) => {
            let made = super::chain::entry(lw, cx, out, id, &state)?;
            let source = cx.flow.as_ref().expect("flow context").now.source.clone();
            match n.read {
                _ if info.node_stage(id) != Some(stage) => None,
                // The event, whose stage alone reads the call that gives it (§11.11).
                _ if source.is_some() => source,
                Read::Array(b) => Some(super::chain::dealt(lw, cx, out, id, &state, b, span)?),
                // Read where the stage of its callee that makes the output runs (S-1088).
                Read::Run => {
                    Some(made.ok_or_else(|| internal(span, format!("`{}` read of an entry of no value", n.path)))?)
                }
            }
        }
    };
    let value = match value {
        Some(v) if early => Some(keep(cx, out, (&n.path, n.owner), v)?),
        Some(v) if !matches!(v.kind, ExprKind::Local(_)) => {
            let tmp = cx.temp(&n.path, v.ty.clone());
            out.push(stmt(span, StmtKind::Let(tmp, v)));
            Some(local_expr(cx, tmp, span))
        }
        v => v,
    };
    cx.flow.as_mut().unwrap().now.done.insert(id, value.clone());
    Ok(value)
}

/// The work of the stage where the delay `id` is written and not read (§11.3,
/// S-1233): that in its first argument, its `d` and, in `init`, its `init`
/// (S-1242); of one in the first argument of a delay, read by the store of
/// that at the end of the stage, the conditions of its chain (S-1241).
pub(super) fn delay_work(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId) -> R<()> {
    let now = &cx.flow.as_ref().expect("flow context").now;
    let (info, stage, saving) = (cx.flow.as_ref().expect("flow context").info, now.stage, now.saving);
    let n = info.node(id);
    // Its store at the end of the stage does the rest of its first argument.
    if let Some(arg) = n.kind.stored().filter(|_| !saving) {
        super::hoist::walk(lw, cx, arg, out)?;
        if info.node_stage(id) == Some(stage) {
            saved_reads(lw, cx, out, &n.saved, (&n.path, n.owner))?;
        }
    }
    if let PlanKind::Vdelay { d, .. } = n.kind {
        super::hoist::walk(lw, cx, d, out)?;
    }
    if stage == ClockStage::Init {
        super::phases::init_delay(lw, cx, out, id)?;
    }
    if saving || !n.chained_delay() {
        return Ok(());
    }
    // Its entry of a stage of a condition slower than it, or the conditions alone.
    if info.node_stage(id) != Some(stage) {
        if cx.flow.as_mut().unwrap().now.done.insert(id, None).is_none() {
            let state = super::branches::here(cx, cx.ast.expr(n.expr).span)?.1;
            super::chain::entry(lw, cx, out, id, &state)?;
        }
        return Ok(());
    }
    let read = super::chain::ports_read(lw, cx, id)?;
    for (at, cond) in (0u32..).zip(&n.chain).filter_map(|(at, m)| Some((at, m.cond?))) {
        // One its entry of another stage reads.
        if !read.contains(&Port::Cond(at)) {
            super::hoist::walk(lw, cx, cond, out)?;
            continue;
        }
        let v = lower_expr(lw, cx, cond)?;
        let v = keep(cx, out, (&n.path, n.owner), v)?;
        cx.flow.as_mut().unwrap().now.expr_override.insert(cond, v);
    }
    super::chain::opened(lw, cx, out, id)
}

/// The reads `saved` of events in what the end of the stage evaluates, of the
/// delay or the hoisted part `of` by its path and its owner (S-1240, S-1249,
/// [`PlanNode::saved`]), as values of this place, after the work in it: each
/// once, where it is first reached, under no condition (a read of a field); of
/// a part in a `par` inside `of`, of each replica, in a loop over them.
pub(super) fn saved_reads(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    saved: &[ExprId],
    of: (&str, Owner),
) -> R<()> {
    for &e in saved {
        if cx.flow.as_ref().expect("flow context").now.expr_override.contains_key(&e) {
            continue;
        }
        let (info, span) = (cx.flow.as_ref().expect("flow context").info, cx.ast.expr(e).span);
        let owner = info.hoist_of(e).map_or(of.1, |h| info.hoist(h).owner);
        let mut loops = Vec::new();
        for p in info.around(owner).into_iter().skip(info.around(of.1).len()) {
            let state = super::branches::here(cx, span)?.1;
            let (r, elem) = replicas(lw, cx, p, &state, span)?;
            cx.flow.as_mut().unwrap().push_scope(elem);
            loops.push(r);
        }
        let mut body = Vec::new();
        let v = lower_expr(lw, cx, e)?;
        let v = keep(cx, &mut body, (of.0, owner), v)?;
        for r in loops.into_iter().rev() {
            cx.flow.as_mut().unwrap().now.scopes.pop();
            let inner = std::mem::take(&mut body);
            r.each(cx, &mut body, span, inner);
        }
        out.append(&mut body);
        cx.flow.as_mut().unwrap().now.expr_override.insert(e, v);
    }
    Ok(())
}

/// `v`, made in the scope of `owner` for `name`, as a value the end of the
/// stage reads: a `let` ([`super::chain::hold`]); in a `par~`, whose loop ends
/// before, the element of the replica of a local of the function.
fn keep(cx: &mut FnCx, out: &mut Vec<Stmt>, (name, owner): (&str, Owner), v: Expr) -> R<Expr> {
    let pars = cx.flow.as_ref().expect("flow context").info.around(owner);
    if pars.is_empty() {
        return Ok(super::chain::hold(cx, out, v, name));
    }
    let mut head = Vec::new();
    let place = replicas_place(cx, &mut head, &format!("__early.{name}"), v.ty.clone(), &pars, v.span)?;
    cx.flow.as_mut().unwrap().now.heads.append(&mut head);
    assign(out, &place, v)?;
    Ok(place)
}

/// The value of the delay `id` in the scope of the state `s` (§11.4): the field of
/// `prev`, `buf[w]` of `delay`, the read side of `vdelay` ([`vdelay_read`]).
pub(super) fn delay_value(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, s: &Expr, id: NodeId) -> R<Expr> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let span = cx.ast.expr(info.node(id).expr).span;
    let at = |p| FieldOf::Node(id, p);
    match &info.node(id).kind {
        PlanKind::Prev { .. } => sfield(lw, info, s, at(Part::Own), span),
        PlanKind::Delay { .. } => {
            let buf = sfield(lw, info, s, at(Part::Buf), span)?;
            index(buf, sfield(lw, info, s, at(Part::W), span)?)
        }
        PlanKind::Vdelay { d, max, ty, .. } => vdelay_read(lw, cx, out, s, id, *d, *max, *ty, span),
        PlanKind::Instance { .. } | PlanKind::Par { .. } => Err(internal(span, "the value of no delay")),
    }
}

/// The read side of `vdelay` (§11.4), in the fixed operation order.
#[allow(clippy::too_many_arguments)]
fn vdelay_read(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    stmts: &mut Vec<Stmt>,
    state: &Expr,
    id: NodeId,
    d: ExprId,
    max: u32,
    ty: onsa_sema::ty::TyId,
    span: Span,
) -> R<Expr> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let name = &info.node(id).path;
    let t = lw.core_ty(ty, &[], span)?;
    let Ty::Float(kind) = t else { return Err(internal(span, "vdelay on a non-float")) };
    let len = ring_len(&info.node(id).kind, span)?;
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
    // k = U32.trunc_from(dc)
    let k = Expr::new(
        Ty::u32(),
        span,
        ExprKind::Prim {
            prim: Prim::TruncToInt { from: kind, to: IntKind::U32, sat: false },
            args: vec![borrow(dc.clone())],
        },
    );
    let k = let_(cx, "k", k);
    // f = dc - T.round_from(k)
    let kf = Expr::new(
        t.clone(),
        span,
        ExprKind::Prim { prim: Prim::IntToFloat { from: IntKind::U32, to: kind }, args: vec![borrow(k.clone())] },
    );
    let f = let_(cx, "f", checked_binary(BinOp::Sub, dc, kf));
    let buf = sfield(lw, info, state, FieldOf::Node(id, Part::Buf), span)?;
    let w = sfield(lw, info, state, FieldOf::Node(id, Part::W), span)?;
    // a = buf[(w + L - k) % L]; b = buf[(w + L - k - 1) % L]
    let wlk = checked_binary(BinOp::Sub, checked_binary(BinOp::Add, w, u32_lit(span, len)), k);
    let wlk = let_(cx, "wlk", wlk);
    let a = index(buf.clone(), checked_binary(BinOp::Rem, wlk.clone(), u32_lit(span, len)))?;
    let a = let_(cx, "a", a);
    let b =
        index(buf, checked_binary(BinOp::Rem, checked_binary(BinOp::Sub, wlk, u32_lit(span, 1)), u32_lit(span, len)))?;
    let b = let_(cx, "b", b);
    // y = ((1.0 - f) * a) + (f * b)
    let y = checked_binary(
        BinOp::Add,
        checked_binary(BinOp::Mul, checked_binary(BinOp::Sub, one, f.clone()), a),
        checked_binary(BinOp::Mul, f, b),
    );
    Ok(y)
}
