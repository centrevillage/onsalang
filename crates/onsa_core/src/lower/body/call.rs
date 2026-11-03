//! Lowering of function bodies: calls, the `target fn`s and the builtin
//! methods (T3-3).

use super::*;

// ---------------------------------------------------------------- calls

/// Lower call arguments against parameter types, coercing arrays / `Buf` to
/// `Span` (§5.3) and planar `[Span[T]; N]` arguments.
fn lower_args(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], params: &[(Mode, Ty)]) -> R<Vec<Arg>> {
    let mut out = Vec::new();
    for (a, (pm, pt)) in args.iter().zip(params) {
        let e = lower_expr(lw, cx, a.expr)?;
        let e = coerce(lw, cx, e, pt, *pm)?;
        out.push(Arg { mode: *pm, expr: e });
    }
    Ok(out)
}

pub(crate) fn coerce(lw: &mut Lowerer, cx: &mut FnCx, e: Expr, want: &Ty, mode: Mode) -> R<Expr> {
    // A planar literal has the type of the parameter, its elements their own (S-196): each converted below.
    let planar = matches!((want, &e.kind), (Ty::Array(el, _), ExprKind::Array(_)) if matches!(**el, Ty::Span(_)));
    if e.ty == *want && !planar {
        return Ok(e);
    }
    let span = e.span;
    match (want, &e.ty) {
        (Ty::Span(_), Ty::Array(..) | Ty::Buf(_)) => span_of(cx, e, mode),
        (Ty::Array(elem, n), Ty::Array(from, m)) if matches!(**elem, Ty::Span(_)) && n == m => {
            let n = *n;
            // Planar: `[a, b]` written in the argument, or an array of arrays / Bufs.
            if let ExprKind::Array(items) = e.kind {
                let mut out = Vec::new();
                for it in items {
                    out.push(coerce(lw, cx, it, elem, mode)?);
                }
                return Ok(Expr::new(want.clone(), span, ExprKind::Array(out)));
            }
            let _ = from;
            let base =
                if e.as_place().is_some() { e } else { return Err(unsupported(span, Feature::PlanarTemporary, &[])) };
            let mut out = Vec::new();
            for i in 0..n {
                let el = index(base.clone(), u32_lit(span, i))?;
                out.push(coerce(lw, cx, el, elem, mode)?);
            }
            Ok(Expr::new(want.clone(), span, ExprKind::Array(out)))
        }
        _ => Err(internal(
            span,
            format!(
                "cannot coerce `{}` to `{}`",
                crate::dump::type_name(&lw.m, &e.ty),
                crate::dump::type_name(&lw.m, want)
            ),
        )),
    }
}

pub(super) fn span_of(cx: &mut FnCx, e: Expr, mode: Mode) -> R<Expr> {
    let span = e.span;
    let elem = match &e.ty {
        Ty::Array(t, _) | Ty::Buf(t) => (**t).clone(),
        Ty::Span(_) => return Ok(e),
        _ => return Err(internal(span, "span of a non-sequence")),
    };
    let base = if e.as_place().is_some() {
        e
    } else {
        if mode == Mode::Inout {
            return Err(internal(span, "inout span of a temporary"));
        }
        // A temporary: bind it so the span has a place to point at.
        let t = cx.temp("__arr", e.ty.clone());
        let let_ = stmt(span, StmtKind::Let(t, e));
        let local = local_expr(cx, t, span);
        let sp = Expr::new(Ty::Span(Box::new(elem)), span, ExprKind::SpanOf(Box::new(local)));
        return Ok(Expr::new(
            sp.ty.clone(),
            span,
            ExprKind::Block(Block { stmts: vec![let_], value: Some(Box::new(sp)) }),
        ));
    };
    Ok(Expr::new(Ty::Span(Box::new(elem)), span, ExprKind::SpanOf(Box::new(base))))
}

pub(super) fn lower_call(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    callee: ExprId,
    args: &[ast::Arg],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let Some(target) = cx.info.targets.get(&e).cloned() else { return Err(internal(span, "call without a target")) };
    match target {
        Target::Fn { def, inst } => {
            let gargs = match inst {
                Some(i) => {
                    let inst = &cx.info.instances[i.0 as usize];
                    lw.generic_args(&inst.args, &cx.args, span)?
                }
                None => Vec::new(),
            };
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "call to a non-fn")) };
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, None, args, ty);
            }
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let cargs = lower_args(lw, cx, args, &params)?;
            let fid = lw.fn_id(def, gargs);
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::Method { def, inst } => {
            let gargs = match inst {
                Some(i) => {
                    let inst = &cx.info.instances[i.0 as usize];
                    lw.generic_args(&inst.args, &cx.args, span)?
                }
                None => Vec::new(),
            };
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "method target")) };
            let AK::Field { base, .. } = &cx.expr(callee).kind else { return Err(internal(span, "method call shape")) };
            let recv = lower_expr(lw, cx, *base)?;
            let self_mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, Some((recv, self_mode)), args, ty);
            }
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let mut cargs = vec![Arg { mode: self_mode, expr: recv }];
            cargs.extend(lower_args(lw, cx, args, &params)?);
            let fid = lw.fn_id(def, gargs);
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::BuiltinMethod { name, .. } => lower_builtin_method(lw, cx, e, callee, &name, args, ty),
        Target::Variant { index, .. } => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "variant call type")) };
            let id = *id;
            let fields = lw.enum_variants(id)[index as usize].1.clone();
            let params: Vec<(Mode, Ty)> = fields.into_iter().map(|t| (Mode::Borrow, t)).collect();
            let cargs = lower_args(lw, cx, args, &params)?;
            Ok(Expr::new(
                ty,
                span,
                ExprKind::Variant { ty: id, tag: index, fields: cargs.into_iter().map(|a| a.expr).collect() },
            ))
        }
        Target::Prelude(b) => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "prelude call type")) };
            let id = *id;
            let tag = match b {
                Builtin::Some | Builtin::Err => 1,
                Builtin::Ok => 0,
                _ => return Err(internal(span, "prelude call")),
            };
            let fields = lw.enum_variants(id)[tag as usize].1.clone();
            let params: Vec<(Mode, Ty)> = fields.into_iter().map(|t| (Mode::Borrow, t)).collect();
            let cargs = lower_args(lw, cx, args, &params)?;
            Ok(Expr::new(
                ty,
                span,
                ExprKind::Variant { ty: id, tag, fields: cargs.into_iter().map(|a| a.expr).collect() },
            ))
        }
        Target::Value => Err(unsupported(span, Feature::CallsThroughFnValues, &[])),
        _ => Err(internal(span, "call target")),
    }
}

fn sig_params(lw: &mut Lowerer, cx: &FnCx, f: &SFnDef, gargs: &[GenericArg], span: Span) -> R<Vec<(Mode, Ty)>> {
    let _ = cx;
    let mut out = Vec::new();
    for p in &f.params {
        out.push((core_mode(p.mode), lw.core_ty(p.ty, gargs, span)?));
    }
    Ok(out)
}

/// A call to a `target fn` of `std` (D-07): its row of the table, resolved
/// by sema ([`onsa_sema::Analysis::prims`], S-69 (2)), instantiated at the
/// type arguments of the call; `array.from_fn` is inlined. The receiver
/// `recv` of a method is its first operand, as its `self` takes it.
#[allow(clippy::too_many_arguments)]
fn lower_target_call(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    (def, f): (DefId, &SFnDef),
    gargs: &[GenericArg],
    recv: Option<(Expr, Mode)>,
    args: &[ast::Arg],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    // Sema stops a `target` declaration outside `std` (`UserTargets` of the
    // list of S-224) and records a row for each of std's.
    let Some(&row) = lw.a.prims.get(&def) else {
        return Err(internal(span, "a call to a `target` declaration without a row"));
    };
    if row == PrimRow::FromFn {
        return lower_from_fn(lw, cx, args, ty, span);
    }
    // The `Self` of a member first (`F32` of `F32.from_bits`), then the type
    // arguments, as sema reads them (`Scalar::of_use`).
    let own = match row_self(lw.a, def) {
        Some(t) => Some(GenericArg::Ty(lw.core_ty(t, gargs, span)?)),
        None => None,
    };
    let scalars: Vec<Scalar> = own.iter().chain(gargs).map(scalar).collect();
    // Sema reports the closed uses without a primitive (E0200); one through
    // a generic body is W5-07's (the `else` bodies).
    let Some(prim) = row.instantiate(&scalars) else {
        return Err(internal(span, "a `target` declaration without a primitive for its type arguments"));
    };
    let mut cargs = Vec::new();
    if let Some((recv, mode)) = recv {
        let Some(GenericArg::Ty(this)) = &own else { return Err(internal(span, "a `target` method of no type")) };
        cargs.push(Arg { mode, expr: coerce(lw, cx, recv, this, mode)? });
    }
    let params = sig_params(lw, cx, f, gargs, span)?;
    cargs.extend(lower_args(lw, cx, args, &params)?);
    Ok(Expr::new(ty, span, ExprKind::Prim { prim, args: cargs }))
}

/// A type argument of a row as Core has it, read as [`Scalar::of`] reads
/// sema's: by its head.
fn scalar(g: &GenericArg) -> Scalar {
    match g {
        GenericArg::Ty(Ty::Int(k)) => Scalar::Int(*k),
        GenericArg::Ty(Ty::Float(k)) => Scalar::Float(*k),
        _ => Scalar::Other,
    }
}

/// `array.from_fn(f)`: an array local filled by a loop; a closure argument is
/// inlined with its parameter bound to the index, a function item is called.
fn lower_from_fn(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], ty: Ty, span: Span) -> R<Expr> {
    let Ty::Array(elem, n) = &ty else { return Err(internal(span, "from_fn type")) };
    let (elem, n) = ((**elem).clone(), *n);
    let [farg] = args else { return Err(internal(span, "from_fn arity")) };
    let arr = cx.temp("__arr", ty.clone());
    let i = cx.temp("__i", Ty::u32());
    let mut body = Vec::new();
    let value = match &cx.expr(farg.expr).kind {
        AK::Closure { params, body: cbody, .. } => {
            let [p] = params.as_slice() else { return Err(internal(span, "from_fn closure arity")) };
            if let ast::ParamName::Ident(id) = &p.name {
                let l = cx.local_by_span(id.span)?;
                body.push(stmt(span, StmtKind::Let(l, local_expr(cx, i, span))));
            }
            cx.inline_depth += 1;
            let r = lower_block_expr(lw, cx, *cbody);
            cx.inline_depth -= 1;
            let blk = r?;
            body.extend(blk.stmts);
            match blk.value {
                Some(v) => *v,
                None => return Err(internal(span, "from_fn closure without a value")),
            }
        }
        _ => {
            let Some(Target::Fn { def, inst }) = cx.info.targets.get(&farg.expr).cloned() else {
                return Err(unsupported(span, Feature::FromFnValue, &[]));
            };
            let gargs = match inst {
                Some(ix) => lw.generic_args(&cx.info.instances[ix.0 as usize].args.clone(), &cx.args, span)?,
                None => Vec::new(),
            };
            let fid = lw.fn_id(def, gargs);
            Expr::new(
                elem.clone(),
                span,
                ExprKind::Call { fn_: fid, args: vec![Arg { mode: Mode::Borrow, expr: local_expr(cx, i, span) }] },
            )
        }
    };
    body.push(stmt(
        span,
        StmtKind::Assign(Place::Index(Box::new(Place::Local(arr)), Box::new(local_expr(cx, i, span)), span), value),
    ));
    let stmts = vec![
        stmt(span, StmtKind::Let(arr, Expr::new(ty.clone(), span, ExprKind::Zeroed))),
        stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), u32_lit(span, n), Block { stmts: body, value: None })),
    ];
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(local_expr(cx, arr, span))) })))
}

fn lower_builtin_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    callee: ExprId,
    name: &str,
    args: &[ast::Arg],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let assoc = name == "zeroed";
    let AK::Field { base, .. } = &cx.expr(callee).kind else { return Err(internal(span, "builtin method shape")) };
    let base = *base;
    let mut lowered_args = Vec::new();
    for a in args {
        lowered_args.push(lower_expr(lw, cx, a.expr)?);
    }
    let borrow = |e: Expr| Arg { mode: Mode::Borrow, expr: e };
    if assoc {
        let args = lowered_args.into_iter().map(borrow).collect();
        return Ok(Expr::new(ty, span, ExprKind::Prim { prim: Prim::BufZeroed, args }));
    }
    let recv = lower_expr(lw, cx, base)?;
    match &recv.ty {
        Ty::Array(..) | Ty::Span(_) | Ty::Buf(_) => lower_seq_method(lw, cx, recv, name, lowered_args, ty, span),
        &Ty::Enum(id) => lower_enum_method(lw, cx, id, recv, name, lowered_args, ty, span),
        other => Err(unsupported(span, Feature::Methods, &[name, &crate::dump::type_name(&lw.m, other)])),
    }
}

fn lower_seq_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    recv: Expr,
    name: &str,
    args: Vec<Expr>,
    ty: Ty,
    span: Span,
) -> R<Expr> {
    let seq_ty = crate::dump::type_name(&lw.m, &recv.ty);
    let borrow = |e: Expr| Arg { mode: Mode::Borrow, expr: e };
    let len_of = |cx: &mut FnCx, recv: Expr| -> R<Expr> {
        match &recv.ty {
            Ty::Array(_, n) => Ok(u32_lit(span, *n)),
            _ => {
                let s = span_of(cx, recv, Mode::Borrow)?;
                Ok(Expr::new(Ty::u32(), span, ExprKind::Prim { prim: Prim::Len, args: vec![borrow(s)] }))
            }
        }
    };
    let kind = match name {
        "len" => return len_of(cx, recv),
        "is_empty" => {
            let l = len_of(cx, recv)?;
            ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(l), rhs: Box::new(u32_lit(span, 0)) }
        }
        "slice" => {
            let s = span_of(cx, recv, Mode::Borrow)?;
            let mut a = vec![borrow(s)];
            a.extend(args.into_iter().map(borrow));
            ExprKind::Prim { prim: Prim::Slice, args: a }
        }
        "get" => {
            let s = span_of(cx, recv, Mode::Borrow)?;
            let mut a = vec![borrow(s)];
            a.extend(args.into_iter().map(borrow));
            ExprKind::Prim { prim: Prim::Get, args: a }
        }
        "fill" | "add_from" | "copy_from" => {
            let s = span_of(cx, recv, Mode::Inout)?;
            let mut a = vec![Arg { mode: Mode::Inout, expr: s }];
            for x in args {
                let x = match name {
                    "fill" => x,
                    _ => span_of(cx, x, Mode::Borrow)?,
                };
                a.push(borrow(x));
            }
            let prim = match name {
                "fill" => Prim::Fill,
                "add_from" => Prim::AddFrom,
                _ => Prim::CopyFrom,
            };
            ExprKind::Prim { prim, args: a }
        }
        _ => return Err(unsupported(span, Feature::Methods, &[name, &seq_ty])),
    };
    Ok(Expr::new(ty, span, kind))
}

#[allow(clippy::too_many_arguments)]
fn lower_enum_method(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    id: TypeId,
    recv: Expr,
    name: &str,
    args: Vec<Expr>,
    ty: Ty,
    span: Span,
) -> R<Expr> {
    let variants = lw.enum_variants(id);
    let is_option = variants.first().is_some_and(|(n, _)| n == "None");
    let (good, bad) = if is_option { (1u32, 0u32) } else { (0, 1) };
    let mut stmts = Vec::new();
    let tmp = materialize(cx, recv, &mut stmts, "__opt");
    let wrap = |stmts: Vec<Stmt>, e: Expr| -> Expr {
        if stmts.is_empty() {
            e
        } else {
            Expr::new(e.ty.clone(), span, ExprKind::Block(Block { stmts, value: Some(Box::new(e)) }))
        }
    };
    let kind = match name {
        "is_some" | "is_ok" | "is_none" | "is_err" => {
            let want = if matches!(name, "is_some" | "is_ok") { good } else { bad };
            return Ok(wrap(stmts, tag_test(lw, &tmp, want)?));
        }
        "unwrap" => {
            let msg = lw.msg(if is_option { "called `unwrap()` on `None`" } else { "called `unwrap()` on `Err`" });
            let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
            let bad_block = Block {
                stmts: Vec::new(),
                value: Some(Box::new(Expr::new(ty.clone(), span, ExprKind::Panic { msg, origin: PanicOrigin::Panic }))),
            };
            let mut arms = vec![(good, good_block), (bad, bad_block)];
            arms.sort_by_key(|(t, _)| *t);
            ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None }
        }
        "unwrap_or" => {
            let [d] = args.as_slice() else { return Err(internal(span, "unwrap_or arity")) };
            let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
            let bad_block = Block { stmts: Vec::new(), value: Some(Box::new(d.clone())) };
            let mut arms = vec![(good, good_block), (bad, bad_block)];
            arms.sort_by_key(|(t, _)| *t);
            ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None }
        }
        _ => return Err(unsupported(span, Feature::Methods, &[name, &crate::dump::type_name(&lw.m, &Ty::Enum(id))])),
    };
    Ok(wrap(stmts, Expr::new(ty, span, kind)))
}
