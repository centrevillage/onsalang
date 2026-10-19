//! The on-demand value of a stateful node, `sample_rate()` or `par` while
//! an expression of the flow body is lowered (called from the lowering of
//! bodies).

use super::*;

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
    let f = let_(cx, "f", checked_binary(BinOp::Sub, dc, kf));
    let buf = sfield(lw, state, &format!("{name}.buf"), span)?;
    let w = sfield(lw, state, &format!("{name}.w"), span)?;
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
