//! Lowering of function bodies: calls, the `target fn`s of std and the
//! methods of the compiler's table (T3-3).

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
        // A `FixedStr[N]` at a `Span[U8]`: its used part (§4.2).
        (Ty::Span(_), Ty::Struct(_)) => crate::lower::fixed_str::view(lw, cx, e),
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
            if e.as_place().is_none() {
                return Err(unsupported(span, Feature::PlanarTemporary, &[]));
            }
            // Its indices evaluated once (R-433); an `inout` argument is a
            // place, with no statements before it.
            let mut stmts = Vec::new();
            let base = materialize(cx, e, &mut stmts, "__planar");
            if mode == Mode::Inout && !stmts.is_empty() {
                return Err(unsupported(span, Feature::PlanarInoutIndex, &[]));
            }
            let mut out = Vec::new();
            for i in 0..n {
                let el = index(base.clone(), u32_lit(span, i))?;
                out.push(coerce(lw, cx, el, elem, mode)?);
            }
            Ok(after(stmts, Expr::new(want.clone(), span, ExprKind::Array(out))))
        }
        // An `rt fn` value where a `fn` is wanted (§8.1): W8-09 lowers function values.
        (Ty::FnPtr(_), Ty::FnPtr(_)) => Err(unsupported(span, Feature::FnValues, &[])),
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
        Target::Fn { def, of, inst } => {
            // `T.default()` at a type with no declaration (§6.3): no other
            // bound with members holds of it.
            if let Some(of) = of.map(|t| lw.core_ty(t, &cx.args, span)).transpose()?
                && let Some(value) = derived::structural_default(lw, &of, span)
            {
                return value;
            }
            let (def, gargs) = lw.instance_target(def, of, inst, cx, span)?;
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "call to a non-fn")) };
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, None, args, ty);
            }
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let cargs = lower_args(lw, cx, args, &params)?;
            let fid = lw.fn_id(def, gargs, span)?;
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::Method { def, of, inst } => {
            let (def, gargs) = lw.instance_target(def, of, inst, cx, span)?;
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "method target")) };
            let Some(base) = onsa_sema::receiver(cx.ast, callee) else {
                return Err(internal(span, "method call shape"));
            };
            let recv = lower_expr(lw, cx, base)?;
            let self_mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, Some((recv, self_mode)), args, ty);
            }
            // An array or a `Buf` receiver of a member of `Span[T]` is a
            // `Span` of it (§5.3), as `self` is declared.
            let this = match row_self(lw.a, def) {
                Some(t) => Some(lw.core_ty(t, &gargs, span)?),
                None => None,
            };
            let recv = match this {
                Some(this @ Ty::Span(_)) => coerce(lw, cx, recv, &this, self_mode)?,
                _ => recv,
            };
            let params = sig_params(lw, cx, f, &gargs, span)?;
            let mut cargs = vec![Arg { mode: self_mode, expr: recv }];
            cargs.extend(lower_args(lw, cx, args, &params)?);
            let fid = lw.fn_id(def, gargs, span)?;
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::BuiltinMethod { name, .. } => lower_builtin_method(lw, cx, e, callee, &name),
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
        Target::Panic => {
            let text = args.first().and_then(|a| cx.ast.panic_message(a));
            let Some(text) = text else { return Err(internal(span, "panic without its message")) };
            let msg = lw.msg(&text);
            Ok(Expr::new(ty, span, ExprKind::Panic { msg, origin: PanicOrigin::Panic }))
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
    let (prim, own) = row_prim(lw, def, row, gargs, span)?;
    let mut cargs = Vec::new();
    if let Some((recv, mode)) = recv {
        let Some(GenericArg::Ty(this)) = &own else { return Err(internal(span, "a `target` method of no type")) };
        cargs.push(Arg { mode, expr: coerce(lw, cx, recv, this, mode)? });
    }
    let params = sig_params(lw, cx, f, gargs, span)?;
    cargs.extend(lower_args(lw, cx, args, &params)?);
    Ok(Expr::new(ty, span, ExprKind::Prim { prim, args: cargs }))
}

/// The primitive of the row of a `target` declaration at `gargs`, and the
/// `Self` of a member.
fn row_prim(
    lw: &mut Lowerer,
    def: DefId,
    row: PrimRow,
    gargs: &[GenericArg],
    span: Span,
) -> R<(Prim, Option<GenericArg>)> {
    // The `Self` of a member first (`F32` of `F32.from_bits`), then the type
    // arguments, as sema reads them (`Scalar::of_use`).
    let own = match row_self(lw.a, def) {
        Some(t) => Some(GenericArg::Ty(lw.core_ty(t, gargs, span)?)),
        None => None,
    };
    let scalars: Vec<Scalar> = own.iter().chain(gargs).map(scalar).collect();
    // Sema reports the closed uses without a primitive (E0200). A use through
    // a generic body at such a type needs a user's number type, which this
    // version has not (`impl Num` is an E0200): the `else` bodies are not
    // called here (`tasks/phase2.md`, S-669).
    let Some(prim) = row.instantiate(&scalars) else {
        return Err(internal(span, "a `target` declaration without a primitive for its type arguments"));
    };
    Ok((prim, own))
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
            let Some(Target::Fn { def, of, inst }) = cx.info.targets.get(&farg.expr).cloned() else {
                return Err(unsupported(span, Feature::FromFnValue, &[]));
            };
            let (def, gargs) = lw.instance_target(def, of, inst, cx, span)?;
            let args = vec![Arg { mode: Mode::Borrow, expr: local_expr(cx, i, span) }];
            // A `target` declaration has no body to call (`F32.round_from`).
            let kind = match lw.a.prims.get(&def).copied() {
                Some(row) => ExprKind::Prim { prim: row_prim(lw, def, row, &gargs, span)?.0, args },
                None => ExprKind::Call { fn_: lw.fn_id(def, gargs, span)?, args },
            };
            Expr::new(elem.clone(), span, kind)
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

fn lower_builtin_method(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, callee: ExprId, name: &str) -> R<Expr> {
    let span = cx.expr(e).span;
    let Some(base) = onsa_sema::receiver(cx.ast, callee) else {
        return Err(internal(span, "builtin method shape"));
    };
    let recv = lower_expr(lw, cx, base)?;
    match &recv.ty {
        // The one method of the table of an array, `len` (§5.3; the others
        // are std's): its length.
        Ty::Array(_, n) => Ok(u32_lit(span, *n)),
        // The stand-in `()` of a receiver of a type lowering does not support
        // (`v.len()` of a `[Str; 2]`, S-67): its hole is used.
        other => Err(unsupported(span, Feature::Methods, &[name, &crate::dump::type_name(&lw.m, other)])),
    }
}
