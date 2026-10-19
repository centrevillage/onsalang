//! The boundary functions of a flow (§11.6, §11.7): `process`,
//! `process_inplace`, `render` and `params_default`.

use super::*;

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
pub(super) fn gen_process<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
            stmts: vec![stmt(
                span,
                StmtKind::Expr(Expr::new(Ty::Unit, span, ExprKind::Panic { msg, origin: PanicOrigin::Panic })),
            )],
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
pub(super) fn gen_process_inplace<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
) -> R<()> {
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
pub(super) fn gen_render<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
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
pub(super) fn gen_params_default<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
) -> R<()> {
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
