//! The boundary functions of a flow (§11.6, §11.7): `process`,
//! `process_inplace`, `render` and `params_default`.

use super::*;

/// Channel `k` of a `Span` (only 0) / planar `[Span; N]` parameter, and the
/// number of its channels.
fn channel(e: &Expr, k: u32, span: Span, tys: &Types) -> R<(Expr, u32)> {
    match *tys.kind(e.ty) {
        TyKind::Span(_) => Ok((e.clone(), 1)),
        TyKind::Array(inner, n) if matches!(tys.kind(inner), TyKind::Span(_)) => {
            Ok((index(e.clone(), u32_lit(span, k), tys)?, n))
        }
        _ => Err(internal(span, "length of a non-span")),
    }
}

fn len_of(s: Expr, span: Span) -> Expr {
    Expr::new(Types::U32, span, ExprKind::Prim { prim: Prim::Len, args: vec![borrow(s)] })
}

/// Length of a `Span` / planar `[Span; N]` parameter (the first channel).
fn span_len(e: &Expr, span: Span, tys: &Types) -> R<Expr> {
    Ok(len_of(channel(e, 0, span, tys)?.0, span))
}

/// The length of every channel of a `Span` / planar `[Span; N]` parameter
/// (R-22: the length check of `process` compares all of them).
fn channel_lens(e: &Expr, span: Span, tys: &Types) -> R<Vec<Expr>> {
    let (_, n) = channel(e, 0, span, tys)?;
    (0..n).map(|k| Ok(len_of(channel(e, k, span, tys)?.0, span))).collect()
}

/// The signals of a parameter of `process` (§11.6): the fields of an `In`
/// or an `Out` in their order (that of the inputs and the outputs), or the
/// one `Span` / planar `[Span; N]` itself.
fn signals(lw: &Lowerer, group: &Expr) -> R<Vec<Expr>> {
    match *lw.m.tys.kind(group.ty) {
        TyKind::Struct(id) => (0..lw.struct_fields(id).len() as u32).map(|k| field(lw, group.clone(), k)).collect(),
        _ => Ok(vec![group.clone()]),
    }
}

/// `process` of a flow with no port of a derived clock ([`FlowFns::process`]).
fn process_of(fns: &FlowFns, span: Span) -> R<FnId> {
    fns.process.ok_or_else(|| internal(span, "a flow with no `process`"))
}

/// The types of the parameters of `process`, made by [`gen_process`].
fn process_types(lw: &Lowerer, process: FnId) -> Vec<CTy> {
    lw.m.fn_(process).params.iter().map(|p| p.ty).collect()
}

/// `process(inout s, params, [input], inout output)` (§11.6): `input` and
/// `output` one `Span` (planar `[Span; N]`) or the `In` and `Out` of more.
pub(super) fn gen_process<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, ClockStage::SAMPLE, Types::UNIT)?;
    let span = g.span;
    let (s, params, input, output) = match g.member_params(lw, shape, FlowFn::Process)?.as_slice() {
        [s, p, o] => (s.clone(), p.clone(), None, o.clone()),
        [s, p, i, o] => (s.clone(), p.clone(), Some(i.clone()), o.clone()),
        _ => return Err(internal(span, "`process` with another number of parameters")),
    };
    let sig_inputs: Vec<(String, CTy)> = (shape.inputs.iter().filter(|i| i.stage == ClockStage::SAMPLE))
        .map(|Input { decl: i, .. }| Ok((i.name.clone(), lw.core_ty(i.ty, &[], i.span)?)))
        .collect::<R<_>>()?;
    let ins = input.as_ref().map(|i| signals(lw, i)).transpose()?.unwrap_or_default();
    let outs = signals(lw, &output)?;
    if ins.len() != sig_inputs.len() || outs.len() != shape.outputs.len() {
        return Err(internal(span, "`process` with another number of signals than the flow"));
    }
    // The fields of an `In` are read once, before the loop, as a `Span`
    // parameter is; those of an `Out` are written at their places.
    let ins: Vec<Expr> = match input.as_ref().map(|i| lw.m.tys.kind(i.ty)) {
        Some(TyKind::Struct(_)) => ins.into_iter().zip(&sig_inputs).map(|(e, (n, _))| g.let_(n, e)).collect(),
        _ => ins,
    };
    // All spans, every channel of the planar ones, must have the same length (§11.6, R-22):
    // compared once, before any state moves (S-196); panic otherwise (poisoned at the export).
    let mut lens = Vec::new();
    for sp in ins.iter().chain(&outs) {
        lens.extend(channel_lens(sp, span, &lw.m.tys)?);
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
                StmtKind::Expr(Expr::new(
                    Types::UNIT,
                    span,
                    ExprKind::Panic { msg, origin: PanicOrigin::Panic, shown: Vec::new() },
                )),
            )],
            value: None,
        };
        g.stmts.push(stmt(span, StmtKind::If(bad, panic, Block::default())));
    }
    expr_stmt(&mut g.stmts, call(fns.ctl, Types::UNIT, span, vec![inout(s.clone()), borrow(params)]));
    // Sample loop: run the slower ticks due, read every input, tick, write every output. Its indices
    // are known in range (S-196): `i` is below the length every channel was
    // compared to, a channel `c` below the `N` of its type.
    let at = |base: &Expr, c: u32, tys: &Types| index_as(base.clone(), u32_lit(span, c), Bounds::Known, tys);
    let i = g.cx.temp("i", Types::U32);
    let i_e = local_expr(&g.cx, i, span);
    let mut body = Vec::new();
    // The time of the root (§11.4, S-1129 (1)): the counter of the phase, copied before the calls that move it.
    let mut time = Vec::new();
    let words = [("t", FieldOf::Tick), ("t_hi", FieldOf::TickHi)];
    for (name, of) in words.into_iter().take(info.most_time_words()) {
        let t = g.cx.temp(name, Types::U32);
        body.push(stmt(span, StmtKind::Let(t, sfield(lw, info, &s, of, span)?)));
        time.push(local_expr(&g.cx, t, span));
    }
    // The slower ticks due (S-578, S-1079): a run of the function of each on the state.
    let mut due = Vec::new();
    for &(x, f) in &fns.stages {
        let (state, time, ret) = (s.clone(), time.clone(), Types::UNIT);
        let run = StageRun { g: info, f, ret, x, state, time, lets: Vec::new(), inputs: Vec::new() };
        due.push((x, vec![stmt(span, StmtKind::Expr(call_stage(run, span)?))]));
    }
    if !due.is_empty() {
        drive(due, &sfield(lw, info, &s, FieldOf::Tick, span)?, span, &mut body)?;
    }
    let mut inputs = Vec::new();
    for (sp, &(ref name, ty)) in ins.into_iter().zip(&sig_inputs) {
        let v = match *lw.m.tys.kind(ty) {
            TyKind::Array(_, n) => {
                let mut items = Vec::new();
                for c in 0..n {
                    items.push(index_as(at(&sp, c, &lw.m.tys)?, i_e.clone(), Bounds::Known, &lw.m.tys)?);
                }
                Expr::new(ty, span, ExprKind::Array(items))
            }
            _ => index_as(sp, i_e.clone(), Bounds::Known, &lw.m.tys)?,
        };
        let l = g.cx.temp(name, ty);
        body.push(stmt(span, StmtKind::Let(l, v)));
        inputs.push(local_expr(&g.cx, l, span));
    }
    let (x, ret, lets) = (ClockStage::SAMPLE, shape.out_val, Vec::new());
    let v = call_stage(StageRun { g: info, f: fns.tick, ret, x, state: s.clone(), time, lets, inputs }, span)?;
    let vl = g.cx.temp("v", shape.out_val);
    body.push(stmt(span, StmtKind::Let(vl, v)));
    super::phases::advance(lw, info, &s, span, &mut body)?;
    let v_e = local_expr(&g.cx, vl, span);
    for (k, (sp, (_, _, planar))) in outs.into_iter().zip(&shape.outputs).enumerate() {
        let val = if shape.out_is_struct { field(lw, v_e.clone(), k as u32)? } else { v_e.clone() };
        match planar {
            Some(n) => {
                for c in 0..*n {
                    let target = index_as(at(&sp, c, &lw.m.tys)?, i_e.clone(), Bounds::Known, &lw.m.tys)?;
                    assign(&mut body, &target, at(&val, c, &lw.m.tys)?)?;
                }
            }
            None => assign(&mut body, &index_as(sp, i_e.clone(), Bounds::Known, &lw.m.tys)?, val)?,
        }
    }
    g.stmts.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), len, Block { stmts: body, value: None })));
    g.finish(lw, process_of(fns, span)?, Types::UNIT, true, None);
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
    let mut g = Gen::new(lw, shape, info, ClockStage::SAMPLE, Types::UNIT)?;
    let span = g.span;
    let [s, params, output] = &g.member_params(lw, shape, FlowFn::ProcessInplace)?[..] else {
        return Err(internal(span, "`process_inplace` with another number of parameters"));
    };
    let outs = signals(lw, output)?;
    let unpaired = || internal(span, "`process_inplace` whose output does not pair up with the input");
    let process = process_of(fns, span)?;
    let input = match process_types(lw, process).as_slice() {
        &[_, _, t, _] => match (lw.m.tys.kind(t), outs.as_slice()) {
            (&TyKind::Struct(id), _) => {
                if lw.struct_fields(id).iter().map(|&(_, t)| t).ne(outs.iter().map(|e| e.ty)) {
                    return Err(unpaired());
                }
                Expr::new(t, span, ExprKind::Struct { ty: id, fields: outs })
            }
            (_, [one]) if one.ty == t => one.clone(),
            _ => return Err(unpaired()),
        },
        _ => return Err(unpaired()),
    };
    let args = vec![inout(s.clone()), borrow(params.clone()), borrow(input), inout(output.clone())];
    expr_stmt(&mut g.stmts, call(process, Types::UNIT, span, args));
    g.finish(lw, fid, Types::UNIT, true, None);
    Ok(())
}

/// `render(cfg, params, [input], [frames], sample_rate) -> Rendered`
/// (interpreter only): `process` on zeroed `Buf`s, whose views it makes.
pub(super) fn gen_render<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let out_ty = lw.ty(TyKind::Struct(shape.out_ty));
    let mut g = Gen::new(lw, shape, info, ClockStage::SAMPLE, out_ty)?;
    let span = g.span;
    // The third is `input` (views), or the `U32` `frames` of a flow with no `sample` input, as the
    // signature the types stage made reads (§11.6).
    let [cfg, params, third, sample_rate] = &g.member_params(lw, shape, FlowFn::Render)?[..] else {
        return Err(internal(span, "`render` with another number of parameters"));
    };
    let init = vec![borrow(cfg.clone()), borrow(sample_rate.clone())];
    let state_ty = lw.ty(TyKind::Struct(shape.state_ty));
    let st = g.let_("s", call(fns.init, state_ty, span, init));
    let input = (third.ty != Types::U32).then_some(third);
    let n = match input {
        Some(i) => {
            let first = signals(lw, i)?.into_iter().next();
            span_len(&first.ok_or_else(|| internal(span, "an `In` with no field"))?, span, &lw.m.tys)?
        }
        None => third.clone(),
    };
    let n = g.let_("n", n);
    let mut args = vec![inout(st), borrow(params.clone())];
    args.extend(input.cloned().map(borrow));
    let mut out_fields = Vec::new();
    let mut views = Vec::new();
    for &(ref name, elem, planar) in &shape.outputs {
        let buf_ty = lw.ty(TyKind::Buf(elem));
        let zeroed = |n: Expr| Expr::new(buf_ty, span, ExprKind::Prim { prim: Prim::BufZeroed, args: vec![borrow(n)] });
        let v = match planar {
            Some(c) => {
                let items = (0..c).map(|_| zeroed(n.clone())).collect();
                Expr::new(lw.ty(TyKind::Array(buf_ty, c)), span, ExprKind::Array(items))
            }
            None => zeroed(n.clone()),
        };
        let buf = g.let_(name, v);
        // The views of the `Buf`s this function makes (of no expression of
        // the source, so of no record of the types stage).
        let view = match planar {
            Some(c) => {
                let mut items = Vec::new();
                for k in 0..c {
                    let one = index(buf.clone(), u32_lit(span, k), &lw.m.tys)?;
                    items.push(span_of(lw, &mut g.cx, one, Mode::Inout)?);
                }
                let view = lw.ty(TyKind::Span(elem));
                Expr::new(lw.ty(TyKind::Array(view, c)), span, ExprKind::Array(items))
            }
            None => span_of(lw, &mut g.cx, buf.clone(), Mode::Inout)?,
        };
        views.push(view);
        out_fields.push(buf);
    }
    let process = process_of(fns, span)?;
    let output = match process_types(lw, process).last().map(|&t| (t, lw.m.tys.kind(t))) {
        Some((t, &TyKind::Struct(id))) => Expr::new(t, span, ExprKind::Struct { ty: id, fields: views }),
        _ => views.pop().filter(|_| views.is_empty()).ok_or_else(|| internal(span, "outputs of no `Out`"))?,
    };
    args.push(inout(output));
    expr_stmt(&mut g.stmts, call(process, Types::UNIT, span, args));
    let out = Expr::new(out_ty, span, ExprKind::Struct { ty: shape.out_ty, fields: out_fields });
    let render = fns.render.ok_or_else(|| internal(span, "a flow with no `render`"))?;
    g.finish(lw, render, out_ty, false, Some(out));
    Ok(())
}

/// `params_default() -> Params` from the `@param` defaults (§11.7), of the
/// type of each `block` input.
pub(super) fn gen_params_default<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
    defaults: Option<Vec<(CTy, ParamNumber)>>,
) -> R<()> {
    let (Some(fid), Some(defaults)) = (fns.params_default, defaults) else { return Ok(()) };
    let ty = lw.ty(TyKind::Struct(shape.params_ty));
    let g = Gen::new(lw, shape, info, ClockStage::Init, ty)?;
    let span = g.span;
    let mut fields = Vec::new();
    for (t, d) in defaults {
        fields.push(lw.const_value_expr(&d.into(), t, span)?);
    }
    let v = Expr::new(ty, span, ExprKind::Struct { ty: shape.params_ty, fields });
    g.finish(lw, fid, ty, false, Some(v));
    Ok(())
}
