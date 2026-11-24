//! The on-demand value of a stateful node, `sample_rate()` or `par` while
//! an expression of the flow body is lowered (called from the lowering of
//! bodies).

use super::*;

/// On-demand value of a stateful node, `sample_rate()` or `par` while an
/// expression of the flow body is lowered. `None`: not a flow construct.
pub(crate) fn lower_flow_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Option<Expr>> {
    let span = cx.ast.expr(e).span;
    let (phase, info, id, state) = {
        let f = cx.flow.as_ref().expect("flow context");
        if let Some(v) = f.expr_override.get(&e) {
            return Ok(Some(v.clone()));
        }
        if f.sample_rate_calls.contains(&e) {
            return Ok(Some(f.sample_rate.clone()));
        }
        // A hoisted subexpression of an earlier stage: its field (§11.3), of
        // the scope it is lowered in: the `State` (a `let` or the output
        // holds it), or the replica of the `par~` whose body does (S-1140);
        // `sample_tick()` of a slower tick too (S-1210).
        if let Some(h) = f.info.hoist_of(e).filter(|&h| f.info.hoist(h).stage < f.phase.stage()) {
            let scope = f.scopes.last().ok_or_else(|| internal(span, "a hoisted field outside the state"))?;
            let v = sfield(lw, f.info, &scope.state, FieldOf::Hoist(h), span)?;
            super::hoist::record(lw, h, span, false)?;
            return Ok(Some(v));
        }
        // The time of the root its caller passes to the function (§11.4,
        // S-1129 (1)), at every stage.
        if f.sample_tick_calls.contains(&e) {
            let t = f.time.first().cloned();
            return t.map(Some).ok_or_else(|| internal(span, "`sample_tick()` in a function with no time"));
        }
        let Some(&id) = f.info.node_of.get(&e) else {
            // A modifier of a chain is the output of its head (§11.9).
            let Some(&receiver) = f.info.modifiers.get(&e) else { return Ok(None) };
            return lower_expr(lw, cx, receiver).map(Some);
        };
        let state = f.scopes.last().ok_or_else(|| internal(span, "node outside a state scope"))?.state.clone();
        (f.phase, f.info, id, state)
    };
    let (name, at) = (&info.node(id).path, |p| FieldOf::Node(id, p));
    // A node is read in the function of the stage the plan gives it, a
    // `par~` where its body is.
    let here = match info.node(id).kind {
        PlanKind::Par { .. } => true,
        _ => info.node_stage(id) == Some(phase.stage()),
    };
    if !here {
        return Err(internal(span, format!("`{name}` evaluated outside the function of its tick")));
    }
    let mut stmts = Vec::new();
    let value = match &info.node(id).kind {
        // Of a chain, read by the ops of its entry (§11.10).
        PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => {
            match info.node(id).entry(phase.stage(), true) {
                Some(e) => {
                    let v = super::chain::entry(lw, cx, &mut stmts, id, &state, e)?;
                    v.ok_or_else(|| internal(span, format!("`{name}` read of an entry of no value")))?
                }
                None => delay_value(lw, cx, &mut stmts, &state, id)?,
            }
        }
        PlanKind::Instance { .. } => match info.node(id).read {
            // Of a chain that deals, the array of its outermost boundary that deals (§11.9),
            // after the ops of this stage that write it (the review of U6b, its high 1).
            Read::Array(b) => {
                if let Some(e) = info.node(id).entry(phase.stage(), true) {
                    super::chain::entry(lw, cx, &mut stmts, id, &state, e)?;
                }
                super::chain::dealt(lw, cx, &mut stmts, id, &state, b, span)?
            }
            // Read where the stage of its callee that makes the output runs (S-1088): its entry read.
            Read::Run => {
                let e = info.node(id).entry(phase.stage(), true);
                let e = e.ok_or_else(|| internal(span, format!("`{name}` read where its output is not made")))?;
                let v = super::chain::entry(lw, cx, &mut stmts, id, &state, e)?;
                v.ok_or_else(|| internal(span, format!("`{name}` read of an entry of no value")))?
            }
        },
        PlanKind::Par { body, .. } => {
            let r = replica_loop(cx, &info.node(id).kind, span)?;
            let ty = lw.core_ty(cx.info.expr_types[&e], &[], span)?;
            let arr = cx.temp(name, ty.clone());
            stmts.push(stmt(span, StmtKind::Let(arr, Expr::new(ty.clone(), span, ExprKind::Zeroed))));
            let arr_e = local_expr(cx, arr, span);
            let idx = r.index(cx, span);
            let elem_state = if info.field(at(Part::Own)).is_some() {
                index(sfield(lw, info, &state, at(Part::Own), span)?, idx.clone())?
            } else {
                state.clone()
            };
            cx.flow.as_mut().unwrap().push_scope(elem_state.clone());
            let mut loop_body = Vec::new();
            let v = lower_expr(lw, cx, *body)?;
            assign(&mut loop_body, &index(arr_e.clone(), idx)?, v)?;
            cx.flow.as_mut().unwrap().scopes.pop();
            stmts.push(r.each(cx, span, loop_body));
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
    cx.flow.as_mut().unwrap().expr_override.insert(e, result.clone());
    let ty = result.ty.clone();
    Ok(Some(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(result)) }))))
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
