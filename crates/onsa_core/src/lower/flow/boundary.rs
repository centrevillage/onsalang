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

/// The signals of a parameter of `process` (§11.6): the fields of an `In`
/// or an `Out` in their order (that of the inputs and the outputs), or the
/// one `Span` / planar `[Span; N]` itself.
fn signals(lw: &Lowerer, group: &Expr) -> R<Vec<Expr>> {
    match &group.ty {
        Ty::Struct(id) => (0..lw.struct_fields(*id).len() as u32).map(|k| field(lw, group.clone(), k)).collect(),
        _ => Ok(vec![group.clone()]),
    }
}

/// The types of the parameters of `process`, made by [`gen_process`].
fn process_types(lw: &Lowerer, fns: &FlowFns) -> Vec<Ty> {
    lw.m.fn_(fns.process).params.iter().map(|p| p.ty.clone()).collect()
}

/// `process(inout s, params, [input], inout output)` (§11.6): `input` and
/// `output` one `Span` (planar `[Span; N]`) or the `In` and `Out` of more.
pub(super) fn gen_process<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Tick, Ty::Unit)?;
    let span = g.span;
    let (s, params, input, output) = match g.member_params(lw, shape, "process")?.as_slice() {
        [s, p, o] => (s.clone(), p.clone(), None, o.clone()),
        [s, p, i, o] => (s.clone(), p.clone(), Some(i.clone()), o.clone()),
        _ => return Err(internal(span, "`process` with another number of parameters")),
    };
    let sig_inputs: Vec<(String, Ty)> = shape
        .flow
        .inputs
        .iter()
        .filter(|i| i.clock == Clock::SAMPLE)
        .map(|i| Ok((i.name.clone(), lw.core_ty(i.ty, &[], i.span)?)))
        .collect::<R<_>>()?;
    let ins = input.as_ref().map(|i| signals(lw, i)).transpose()?.unwrap_or_default();
    let outs = signals(lw, &output)?;
    if ins.len() != sig_inputs.len() || outs.len() != shape.outputs.len() {
        return Err(internal(span, "`process` with another number of signals than the flow"));
    }
    // The fields of an `In` are read once, before the loop, as a `Span`
    // parameter is; those of an `Out` are written at their places.
    let ins: Vec<Expr> = match input.as_ref().map(|i| &i.ty) {
        Some(Ty::Struct(_)) => ins.into_iter().zip(&sig_inputs).map(|(e, (n, _))| g.let_(n, e)).collect(),
        _ => ins,
    };
    // All spans, every channel of the planar ones, must have the same length (§11.6, R-22):
    // compared once, before any state moves (S-196); panic otherwise (poisoned at the export).
    let mut lens = Vec::new();
    for sp in ins.iter().chain(&outs) {
        lens.extend(channel_lens(sp, span)?);
    }
    let mut lens = lens.into_iter();
    // A flow with no channel is an E0810 (§11.6, S-1110, S-407): the length is of a channel.
    let first = lens.next().ok_or_else(|| internal(span, "flow without channels"))?;
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
    for (sp, (name, ty)) in ins.into_iter().zip(&sig_inputs) {
        let v = match ty {
            Ty::Array(_, n) => {
                let mut items = Vec::new();
                for c in 0..*n {
                    items.push(index(index(sp.clone(), u32_lit(span, c))?, i_e.clone())?);
                }
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
    for (k, (sp, (_, _, planar))) in outs.into_iter().zip(&shape.outputs).enumerate() {
        let val = if shape.out_is_struct { field(lw, v_e.clone(), k as u32)? } else { v_e.clone() };
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

/// `process_inplace(inout s, params, inout output)`: `process` with the
/// input made of the signals of `output` in their order (§11.6: they pair
/// up by type, S-197, S-220).
pub(super) fn gen_process_inplace<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
) -> R<()> {
    let Some(fid) = fns.process_inplace else { return Ok(()) };
    let mut g = Gen::new(lw, shape, info, Phase::Tick, Ty::Unit)?;
    let span = g.span;
    let [s, params, output] = &g.member_params(lw, shape, "process_inplace")?[..] else {
        return Err(internal(span, "`process_inplace` with another number of parameters"));
    };
    let outs = signals(lw, output)?;
    let unpaired = || internal(span, "`process_inplace` whose output does not pair up with the input");
    let input = match process_types(lw, fns).as_slice() {
        [_, _, Ty::Struct(id), _] => {
            let id = *id;
            if lw.struct_fields(id).iter().map(|(_, t)| t).ne(outs.iter().map(|e| &e.ty)) {
                return Err(unpaired());
            }
            Expr::new(Ty::Struct(id), span, ExprKind::Struct { ty: id, fields: outs })
        }
        [_, _, t, _] => match outs.as_slice() {
            [one] if one.ty == *t => one.clone(),
            _ => return Err(unpaired()),
        },
        _ => return Err(unpaired()),
    };
    let args = vec![inout(s.clone()), borrow(params.clone()), borrow(input), inout(output.clone())];
    expr_stmt(&mut g.stmts, call(fns.process, Ty::Unit, span, args));
    g.finish(lw, fid, Ty::Unit, true, None);
    Ok(())
}

/// `render(cfg, params, [input], [frames], sample_rate) -> Rendered`
/// (interpreter only): `process` on zeroed `Buf`s, whose views it makes.
pub(super) fn gen_render<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let out_ty = Ty::Struct(shape.out_ty);
    let mut g = Gen::new(lw, shape, info, Phase::Tick, out_ty.clone())?;
    let span = g.span;
    // The third is `input` (views), or the `U32` `frames` of a flow with no `sample` input, as the
    // signature the types stage made reads (§11.6).
    let [cfg, params, third, sample_rate] = &g.member_params(lw, shape, "render")?[..] else {
        return Err(internal(span, "`render` with another number of parameters"));
    };
    let init = vec![borrow(cfg.clone()), borrow(sample_rate.clone())];
    let st = g.let_("s", call(fns.init, Ty::Struct(shape.state_ty), span, init));
    let input = (third.ty != Ty::u32()).then_some(third);
    let n = match input {
        Some(i) => span_len(signals(lw, i)?.first().ok_or_else(|| internal(span, "an `In` with no field"))?, span)?,
        None => third.clone(),
    };
    let n = g.let_("n", n);
    let mut args = vec![inout(st), borrow(params.clone())];
    args.extend(input.cloned().map(borrow));
    let mut out_fields = Vec::new();
    let mut views = Vec::new();
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
        // The views of the `Buf`s this function makes (of no expression of
        // the source, so of no record of the types stage).
        let view = match planar {
            Some(c) => {
                let one = |k: u32| span_of(&mut g.cx, index(buf.clone(), u32_lit(span, k))?, Mode::Inout);
                let items = (0..*c).map(one).collect::<R<Vec<_>>>()?;
                Expr::new(Ty::Array(Box::new(Ty::Span(Box::new(elem.clone()))), *c), span, ExprKind::Array(items))
            }
            None => span_of(&mut g.cx, buf.clone(), Mode::Inout)?,
        };
        views.push(view);
        out_fields.push(buf);
    }
    let output = match process_types(lw, fns).last() {
        Some(Ty::Struct(id)) => Expr::new(Ty::Struct(*id), span, ExprKind::Struct { ty: *id, fields: views }),
        _ => views.pop().filter(|_| views.is_empty()).ok_or_else(|| internal(span, "outputs of no `Out`"))?,
    };
    args.push(inout(output));
    expr_stmt(&mut g.stmts, call(fns.process, Ty::Unit, span, args));
    let out = Expr::new(out_ty.clone(), span, ExprKind::Struct { ty: shape.out_ty, fields: out_fields });
    g.finish(lw, fns.render, out_ty, false, Some(out));
    Ok(())
}

/// `params_default() -> Params` from the `@param` defaults (§11.7), of the
/// type of each `block` input.
pub(super) fn gen_params_default<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
    defaults: Option<Vec<(Ty, ParamNumber)>>,
) -> R<()> {
    let (Some(fid), Some(defaults)) = (fns.params_default, defaults) else { return Ok(()) };
    let ty = Ty::Struct(shape.params_ty);
    let g = Gen::new(lw, shape, info, Phase::Init, ty.clone())?;
    let span = g.span;
    let mut fields = Vec::new();
    for (t, d) in defaults {
        fields.push(lw.const_value_expr(&d.into(), &t, span)?);
    }
    let v = Expr::new(ty.clone(), span, ExprKind::Struct { ty: shape.params_ty, fields });
    g.finish(lw, fid, ty, false, Some(v));
    Ok(())
}
