//! Lowering of function bodies: calls and the `target fn`s of std (T3-3).

use super::*;

// ---------------------------------------------------------------- calls

/// Lower call arguments against parameter types: an argument passed as a
/// view (§5.3) is converted at its tails ([`lower_expr`]).
fn lower_args(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], params: &[(Mode, CTy)]) -> R<Vec<Arg>> {
    let mut out = Vec::new();
    for (a, &(pm, pt)) in args.iter().zip(params) {
        let e = lower_expr(lw, cx, a.expr)?;
        out.push(Arg { mode: pm, expr: of_type(e, pt, &lw.m.tys)? });
    }
    Ok(out)
}

/// `e` where a value of `want` goes and no view is recorded (an argument,
/// the input of an instance, the output of a flow): of that type, as the
/// types stage checked it, with no conversion.
pub(crate) fn of_type(e: Expr, want: CTy, tys: &Types) -> R<Expr> {
    match (tys.kind(want), tys.kind(e.ty)) {
        _ if e.ty == want => Ok(e),
        // An `rt fn` value where a `fn` is wanted (§8.1): W8-09 lowers function values.
        (TyKind::FnPtr(_), TyKind::FnPtr(_)) => Err(unsupported(e.span, Feature::FnValues, &[])),
        _ => Err(internal(e.span, "a value of another type than where it goes, with no view recorded")),
    }
}

pub(super) fn coerce(lw: &mut Lowerer, cx: &mut FnCx, e: Expr, want: CTy, mode: Mode) -> R<Expr> {
    if e.ty == want {
        return Ok(e);
    }
    let span = e.span;
    match (lw.m.tys.kind(want), lw.m.tys.kind(e.ty)) {
        (TyKind::Span(_), TyKind::Array(..) | TyKind::Buf(_)) => span_of(lw, cx, e, mode),
        // A `FixedStr[N]` at a `Span[U8]`: its used part (§4.2).
        (TyKind::Span(_), TyKind::Struct(_)) => crate::lower::fixed_str::view(lw, cx, e),
        (&TyKind::Array(elem, n), &TyKind::Array(_, m)) if lw.m.tys.is_planar(want) && n == m => {
            // Planar: an array of arrays / Bufs (a literal is converted by its elements, S-196),
            // a value that is no place bound to a temporary first, and the
            // indices of a place evaluated once (R-433); an `inout` argument
            // is a place, with no statements before it.
            let mut stmts = Vec::new();
            let base = materialize(cx, e, &mut stmts, "__planar", &lw.m.tys);
            if mode == Mode::Inout && !stmts.is_empty() {
                return Err(unsupported(span, Feature::PlanarInoutIndex, &[]));
            }
            let mut out = Vec::new();
            for i in 0..n {
                let el = index(base.clone(), u32_lit(span, i), &lw.m.tys)?;
                out.push(coerce(lw, cx, el, elem, mode)?);
            }
            Ok(after(stmts, Expr::new(want, span, ExprKind::Array(out))))
        }
        // A view the types stage recorded: of these types alone.
        _ => Err(internal(
            span,
            format!(
                "cannot convert `{}` to `{}`",
                crate::dump::type_name(&lw.m, e.ty),
                crate::dump::type_name(&lw.m, want)
            ),
        )),
    }
}

pub(crate) fn span_of(lw: &mut Lowerer, cx: &mut FnCx, e: Expr, mode: Mode) -> R<Expr> {
    let span = e.span;
    let elem = match *lw.m.tys.kind(e.ty) {
        TyKind::Array(t, _) | TyKind::Buf(t) => t,
        TyKind::Span(_) => return Ok(e),
        _ => return Err(internal(span, "span of a non-sequence")),
    };
    let view = lw.ty(TyKind::Span(elem));
    let base = if e.as_place().is_some() {
        e
    } else {
        if mode == Mode::Inout {
            return Err(internal(span, "inout span of a temporary"));
        }
        // A temporary: bind it so the span has a place to point at.
        let t = cx.temp("__arr", e.ty);
        let let_ = stmt(span, StmtKind::Let(t, e));
        let local = local_expr(cx, t, span);
        let sp = Expr::new(view, span, ExprKind::SpanOf(Box::new(local)));
        return Ok(Expr::new(sp.ty, span, ExprKind::Block(Block { stmts: vec![let_], value: Some(Box::new(sp)) })));
    };
    Ok(Expr::new(view, span, ExprKind::SpanOf(Box::new(base))))
}

pub(super) fn lower_call(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    callee: ExprId,
    args: &[ast::Arg],
    ty: CTy,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let Some(target) = cx.info.targets.get(&e).cloned() else { return Err(internal(span, "call without a target")) };
    match target {
        Target::Fn { def, of, inst } => {
            // `T.default()` at a type with no declaration (§6.3): no other
            // bound with members holds of it.
            if let Some(of) = of.map(|t| lw.core_ty(t, &cx.args, span)).transpose()?
                && let Some(value) = derived::structural_default(lw, of, span)
            {
                return value;
            }
            let (def, gargs) = lw.instance_target(def, of, inst, cx, span)?;
            let d = lw.a.def(def).clone();
            let DefKind::Fn(f) = &d.kind else { return Err(internal(span, "call to a non-fn")) };
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, None, args, ty);
            }
            let implicit = super::super::flow::implicit_params(lw, def, span)?;
            let params = sig_params(lw, f, &gargs, span)?;
            let mut cargs = lower_args(lw, cx, args, &params)?;
            for (at, _, id) in implicit {
                let empty = Expr::new(lw.ty(TyKind::Struct(id)), span, ExprKind::Struct { ty: id, fields: Vec::new() });
                cargs.insert(at, Arg { mode: Mode::Borrow, expr: empty });
            }
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
            // An array or a `Buf` receiver of a member of `Span[T]` is
            // converted as the types stage recorded it (§5.3).
            let recv = lower_expr(lw, cx, base)?;
            let self_mode = core_mode(f.self_mode.unwrap_or(ast::Mode::Borrow));
            if f.target {
                return lower_target_call(lw, cx, e, (def, f), &gargs, Some((recv, self_mode)), args, ty);
            }
            let params = sig_params(lw, f, &gargs, span)?;
            let mut cargs = vec![Arg { mode: self_mode, expr: recv }];
            cargs.extend(lower_args(lw, cx, args, &params)?);
            let fid = lw.fn_id(def, gargs, span)?;
            Ok(Expr::new(ty, span, ExprKind::Call { fn_: fid, args: cargs }))
        }
        Target::Variant { index, .. } => {
            let TyKind::Enum(id) = *lw.m.tys.kind(ty) else { return Err(internal(span, "variant call type")) };
            let fields = lw.enum_variants(id)[index as usize].1.clone();
            let params: Vec<(Mode, CTy)> = fields.into_iter().map(|t| (Mode::Borrow, t)).collect();
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
            Ok(Expr::new(ty, span, ExprKind::Panic { msg, origin: PanicOrigin::Panic, shown: Vec::new() }))
        }
        Target::Value => Err(unsupported(span, Feature::CallsThroughFnValues, &[])),
        _ => Err(internal(span, "call target")),
    }
}

fn sig_params(lw: &mut Lowerer, f: &SFnDef, gargs: &[GenericArg], span: Span) -> R<Vec<(Mode, CTy)>> {
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
    ty: CTy,
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
    let prim = row_prim(lw, def, row, gargs, span)?;
    let mut cargs = Vec::new();
    if let Some((recv, mode)) = recv {
        cargs.push(Arg { mode, expr: recv });
    }
    let params = sig_params(lw, f, gargs, span)?;
    cargs.extend(lower_args(lw, cx, args, &params)?);
    Ok(Expr::new(ty, span, ExprKind::Prim { prim, args: cargs }))
}

/// The primitive of the row of a `target` declaration at `gargs` (and the
/// `Self` of a member).
fn row_prim(lw: &mut Lowerer, def: DefId, row: PrimRow, gargs: &[GenericArg], span: Span) -> R<Prim> {
    // The `Self` of a member first (`F32` of `F32.from_bits`), then the type
    // arguments, as sema reads them (`Scalar::of_use`).
    let own = match row_self(lw.a, def) {
        Some(t) => Some(GenericArg::Ty(lw.core_ty(t, gargs, span)?)),
        None => None,
    };
    let scalars: Vec<Scalar> = own.iter().chain(gargs).map(|g| scalar(g, &lw.m.tys)).collect();
    // Sema reports the closed uses without a primitive (E0200). A use through
    // a generic body at such a type needs a user's number type, which this
    // version has not (`impl Num` is an E0200): the `else` bodies are not
    // called here (`tasks/phase2.md`, S-669).
    let Some(prim) = row.instantiate(&scalars) else {
        return Err(internal(span, "a `target` declaration without a primitive for its type arguments"));
    };
    Ok(prim)
}

/// A type argument of a row as Core has it, read as [`Scalar::of`] reads
/// sema's: by its head.
fn scalar(g: &GenericArg, tys: &Types) -> Scalar {
    match g {
        GenericArg::Ty(t) => crate::prim::scalar(tys.kind(*t)),
        _ => Scalar::Other,
    }
}

/// `array.from_fn(f)`: an array local filled by a loop; a closure argument is
/// inlined with its parameter bound to the index, a function item is called.
fn lower_from_fn(lw: &mut Lowerer, cx: &mut FnCx, args: &[ast::Arg], ty: CTy, span: Span) -> R<Expr> {
    let TyKind::Array(elem, n) = *lw.m.tys.kind(ty) else { return Err(internal(span, "from_fn type")) };
    let [farg] = args else { return Err(internal(span, "from_fn arity")) };
    let arr = cx.temp("__arr", ty);
    let i = cx.temp("__i", Types::U32);
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
                Some(row) => ExprKind::Prim { prim: row_prim(lw, def, row, &gargs, span)?, args },
                None => ExprKind::Call { fn_: lw.fn_id(def, gargs, span)?, args },
            };
            Expr::new(elem, span, kind)
        }
    };
    body.push(stmt(
        span,
        StmtKind::Assign(
            Place::Index(Box::new(Place::Local(arr)), Box::new(local_expr(cx, i, span)), span, Bounds::Checked),
            value,
        ),
    ));
    let stmts = vec![
        stmt(span, StmtKind::Let(arr, Expr::new(ty, span, ExprKind::Zeroed))),
        stmt(span, StmtKind::for_excluded(i, u32_lit(span, 0), u32_lit(span, n), Block { stmts: body, value: None })),
    ];
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(local_expr(cx, arr, span))) })))
}
