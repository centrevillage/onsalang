//! Lowering of function bodies: expressions (T3-3).

use super::*;

// ---------------------------------------------------------------- expressions

pub(crate) fn lower_expr(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Expr> {
    let hole = Hole::Expr(cx.module, e);
    if lw.holes.contains(&hole) {
        // An expression that uses an unsupported feature (S-67): a fresh
        // local of its type stands for it, so lowering reaches the next one.
        // A type lowering does not support has `()` in its place (its uses
        // are placeholders too). The Core is dropped (`lower_with`).
        let span = cx.expr(e).span;
        let (ty, stand_in) = placeholder_ty(lw, cx.sema_ty(e)?, &cx.args, span)?;
        lw.hole_spans.push(span);
        if stand_in {
            lw.stand_in_spans.push(span);
        }
        let l = cx.temp("__unsupported", ty);
        return Ok(local_expr(cx, l, span));
    }
    lower_expr_at(lw, cx, e).map_err(|f| at_hole(f, hole))
}

/// The Core type of a placeholder, and whether it stands in for a type
/// lowering does not support (then it is `()`).
pub(super) fn placeholder_ty(lw: &mut Lowerer, t: TyId, args: &[GenericArg], span: Span) -> R<(Ty, bool)> {
    match lw.core_ty(t, args, span) {
        Err(f) if f.kind == FailKind::Unsupported => Ok((Ty::Unit, true)),
        r => r.map(|t| (t, false)),
    }
}

fn lower_expr_at(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId) -> R<Expr> {
    let span = cx.expr(e).span;
    // Flow bodies (T3-5): stateful nodes, `sample_rate()` and `par` are
    // lowered by the flow lowering, not by the rules below.
    if cx.flow.is_some()
        && let Some(v) = super::flow::lower_flow_expr(lw, cx, e)?
    {
        return Ok(v);
    }
    let ty = lw.core_ty(cx.sema_ty(e)?, &cx.args, span)?;
    // Resolved names first (locals, consts, variants, builtin constants).
    if let Some(t) = cx.info.targets.get(&e).cloned()
        && !matches!(cx.expr(e).kind, AK::Call { .. })
    {
        return lower_target_value(lw, cx, e, t, ty);
    }
    let kind = match &cx.expr(e).kind {
        AK::Lit(l) => match l {
            ALit::Int { value, .. } => ExprKind::Lit(Lit::Int(*value as i128)),
            // The one conversion of a float literal (§2.4, R-20): the value
            // rounded once to the type; the types stage reported one out of
            // its range (E0408).
            ALit::Float { text } => {
                let value = |k: FloatKind| {
                    onsa_syntax::float_value(text, k.width()).map_err(|_| internal(span, "float literal out of range"))
                };
                match ty {
                    // Exact: the value is one of `F32` already.
                    Ty::Float(FloatKind::F32) => ExprKind::Lit(Lit::F32(value(FloatKind::F32)? as f32)),
                    Ty::Float(FloatKind::F64) => ExprKind::Lit(Lit::F64(value(FloatKind::F64)?)),
                    _ => return Err(internal(span, "float literal type")),
                }
            }
            ALit::Char(c) => ExprKind::Lit(Lit::Char(*c)),
            ALit::Bool(b) => ExprKind::Lit(Lit::Bool(*b)),
            ALit::Str(_) => return Err(unsupported(span, Feature::StrValues, &[])),
        },
        AK::Path(_) => return Err(internal(span, "unresolved path")),
        AK::Hole => return Err(internal(span, "typed hole")),
        // The names stage stops a `::[…]` with E0200 until W4-13.
        AK::TypeArgs { .. } => return Err(internal(span, "type arguments in an expression")),
        // Lowering runs only on a package without diagnostics, and a failed
        // item has a syntax diagnostic (S-59).
        AK::Error => onsa_diag::internal::bug(Some(span), "lowering met a body a syntax error left unread"),
        AK::Paren(inner) | AK::Move(inner) => return lower_expr(lw, cx, *inner),
        AK::Tuple(elems) => {
            if elems.is_empty() {
                ExprKind::Lit(Lit::Unit)
            } else {
                let mut out = Vec::new();
                for &x in elems {
                    out.push(lower_expr(lw, cx, x)?);
                }
                ExprKind::Tuple(out)
            }
        }
        AK::Array(elems) => {
            let mut out = Vec::new();
            for &x in elems {
                out.push(lower_expr(lw, cx, x)?);
            }
            ExprKind::Array(out)
        }
        AK::Repeat { elem, .. } => {
            let Ty::Array(_, n) = &ty else { return Err(internal(span, "repeat type")) };
            let n = *n;
            ExprKind::Repeat { elem: Box::new(lower_expr(lw, cx, *elem)?), n }
        }
        AK::Struct { fields, .. } => {
            let Ty::Struct(id) = &ty else { return Err(internal(span, "struct literal type")) };
            let id = *id;
            let defs = lw.struct_fields(id);
            let mut out = Vec::new();
            for (name, _) in &defs {
                let Some((_, v)) = fields.iter().find(|(n, _)| n.name == *name) else {
                    return Err(internal(span, "missing field"));
                };
                out.push(lower_expr(lw, cx, *v)?);
            }
            ExprKind::Struct { ty: id, fields: out }
        }
        AK::Block(b) => {
            let blk = lower_block(lw, cx, b, ty != Ty::Unit)?;
            if ty == Ty::Unit && blk.stmts.is_empty() { ExprKind::Lit(Lit::Unit) } else { ExprKind::Block(blk) }
        }
        AK::If { cond, then, else_, .. } => {
            let c = lower_expr(lw, cx, *cond)?;
            let t = lower_block_expr(lw, cx, *then)?;
            let el = match else_ {
                Some(el) => lower_block_expr(lw, cx, *el)?,
                None => Block::default(),
            };
            if ty == Ty::Unit {
                let s = stmt(span, StmtKind::If(c, drop_value(t), drop_value(el)));
                ExprKind::Block(Block { stmts: vec![s], value: None })
            } else {
                ExprKind::IfExpr { cond: Box::new(c), then: t, else_: el }
            }
        }
        AK::Match { scrutinee, arms, .. } => return lower_match(lw, cx, e, *scrutinee, arms, ty),
        AK::Closure { .. } => return Err(unsupported(span, Feature::Closures, &[])),
        // `e at k` is the value of `e` (§11.3): the clock is the flow
        // lowering's, from the rates of sema.
        AK::At { expr: inner, .. } => return lower_expr(lw, cx, *inner),
        // `^y` has the `Target::Local` of `y`, lowered above.
        AK::Feedback(_) => return Err(internal(span, "a feedback reference without its local")),
        AK::Handle { .. } => return Err(unsupported(span, Feature::EffectHandlers, &[])),
        AK::Unsafe(_) => return Err(unsupported(span, Feature::Unsafe, &[])),
        // Sema rejects `par` outside a flow body: lowering never sees one.
        AK::Par { .. } => return Err(internal(span, "`par` outside a flow")),
        &AK::Binary { op, op_span, lhs, rhs } => return lower_binary(lw, cx, e, (op, op_span), lhs, rhs, ty),
        AK::Cast { expr: inner, .. } => {
            let x = lower_expr(lw, cx, *inner)?;
            if x.ty == ty {
                return Ok(x);
            }
            ExprKind::Cast(Box::new(x))
        }
        AK::Unary { op, expr: inner } => {
            let x = lower_expr(lw, cx, *inner)?;
            match op {
                // A negative literal is a literal (`-128` fits `I8`; no run-time negation).
                // Sema decided which `-` belong to a literal (§4.7, S-227); every other
                // `-` negates a value and panics at `MIN` (`-(I32.MIN)`, `-(-2147483648)`, R-03).
                AUnOp::Neg if cx.info.neg_literals.contains(&e) => match &x.kind {
                    ExprKind::Lit(Lit::Int(v)) => ExprKind::Lit(Lit::Int(-v)),
                    ExprKind::Lit(Lit::F32(v)) => ExprKind::Lit(Lit::F32(-v)),
                    ExprKind::Lit(Lit::F64(v)) => ExprKind::Lit(Lit::F64(-v)),
                    _ => return Err(internal(span, "a negative literal whose operand did not lower to a literal")),
                },
                AUnOp::Neg => ExprKind::Unary(UnOp::Neg, Box::new(x)),
                AUnOp::Not => ExprKind::Unary(UnOp::Not, Box::new(x)),
            }
        }
        AK::Call { callee, args, .. } => return lower_call(lw, cx, e, *callee, args, ty),
        AK::Field { base, name } => {
            let b = lower_expr(lw, cx, *base)?;
            return field_by_name(lw, b, &name.name, span);
        }
        AK::TupleIndex { base, index, .. } => {
            let b = lower_expr(lw, cx, *base)?;
            return field(lw, b, *index);
        }
        AK::Index { base, index: i } => {
            let b = lower_expr(lw, cx, *base)?;
            let i = lower_expr(lw, cx, *i)?;
            // The whole `xs[i]`, not its base: the position of its panic
            // (§18.1, S-233).
            let mut x = index(b, i)?;
            x.span = span;
            return Ok(x);
        }
        AK::Try(inner) => return lower_try(lw, cx, *inner, ty, span),
        AK::Range(_) => return Err(internal(span, "range outside a loop head")),
    };
    Ok(Expr::new(ty, span, kind))
}

fn lower_target_value(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, t: Target, ty: Ty) -> R<Expr> {
    let span = cx.expr(e).span;
    if let Target::Local(l) = t
        && let Some(f) = &cx.flow
        && let Some(v) = f.local_override.get(&l.0)
    {
        return Ok(v.clone());
    }
    let kind = match t {
        Target::Local(l) => ExprKind::Local(LocalId(l.0)),
        Target::ConstParam(i) => match cx.args.get(i as usize) {
            Some(GenericArg::Const(n)) => ExprKind::Lit(Lit::Int(*n as i128)),
            _ => return Err(internal(span, "unbound const parameter")),
        },
        Target::Const(d) => ExprKind::Const(lw.const_id(d)?),
        Target::Variant { index, .. } => {
            let Ty::Enum(id) = &ty else { return Err(unsupported(span, Feature::VariantCtorValues, &[])) };
            ExprKind::Variant { ty: *id, tag: index, fields: Vec::new() }
        }
        Target::Prelude(Builtin::None) => {
            let Ty::Enum(id) = &ty else { return Err(internal(span, "None type")) };
            ExprKind::Variant { ty: *id, tag: 0, fields: Vec::new() }
        }
        Target::BuiltinConst { name, .. } => builtin_const(&ty, &name, span)?,
        Target::Fn { .. } | Target::Prelude(_) => return Err(unsupported(span, Feature::FnValues, &[])),
        Target::Method { .. } | Target::BuiltinMethod { .. } | Target::Value => {
            return Err(internal(span, "call target on a non-call"));
        }
    };
    Ok(Expr::new(ty, span, kind))
}

fn builtin_const(ty: &Ty, name: &str, span: Span) -> R<ExprKind> {
    Ok(match ty {
        Ty::Float(FloatKind::F32) => ExprKind::Lit(Lit::F32(match name {
            "PI" => std::f32::consts::PI,
            "MIN" => f32::MIN,
            "MAX" => f32::MAX,
            "EPSILON" => f32::EPSILON,
            "INFINITY" => f32::INFINITY,
            "NAN" => f32::NAN,
            _ => return Err(internal(span, "builtin constant")),
        })),
        Ty::Float(FloatKind::F64) => ExprKind::Lit(Lit::F64(match name {
            "PI" => std::f64::consts::PI,
            "MIN" => f64::MIN,
            "MAX" => f64::MAX,
            "EPSILON" => f64::EPSILON,
            "INFINITY" => f64::INFINITY,
            "NAN" => f64::NAN,
            _ => return Err(internal(span, "builtin constant")),
        })),
        Ty::Int(k) => {
            let (lo, hi) = k.range();
            ExprKind::Lit(Lit::Int(match name {
                "MIN" => lo,
                "MAX" => hi,
                "BITS" => k.bits() as i128,
                _ => return Err(internal(span, "builtin constant")),
            }))
        }
        _ => return Err(internal(span, "builtin constant type")),
    })
}

fn lower_binary(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    (op, op_span): (ABinOp, Span),
    lhs: ExprId,
    rhs: ExprId,
    ty: Ty,
) -> R<Expr> {
    let sp = cx.expr(e).span;
    let l = lower_expr(lw, cx, lhs)?;
    let r = lower_expr(lw, cx, rhs)?;
    let out = match op.group() {
        OpGroup::And | OpGroup::Or => {
            let lop = if op.group() == OpGroup::And { LogicOp::And } else { LogicOp::Or };
            Expr::new(Ty::Bool, sp, ExprKind::Logic { op: lop, lhs: Box::new(l), rhs: Box::new(r) })
        }
        OpGroup::Comparison => {
            let cop = match op {
                ABinOp::Eq => CmpOp::Eq,
                ABinOp::Ne => CmpOp::Ne,
                ABinOp::Lt => CmpOp::Lt,
                ABinOp::Le => CmpOp::Le,
                ABinOp::Gt => CmpOp::Gt,
                _ => CmpOp::Ge,
            };
            if l.ty.is_scalar() {
                Expr::new(Ty::Bool, sp, ExprKind::Cmp { op: cop, lhs: Box::new(l), rhs: Box::new(r) })
            } else if matches!(cop, CmpOp::Eq | CmpOp::Ne) {
                let f = super::eq::eq_fn(lw, &l.ty, op_span)?;
                let call = Expr::new(
                    Ty::Bool,
                    sp,
                    ExprKind::Call {
                        fn_: f,
                        args: vec![Arg { mode: Mode::Borrow, expr: l }, Arg { mode: Mode::Borrow, expr: r }],
                    },
                );
                if cop == CmpOp::Eq {
                    call
                } else {
                    Expr::new(Ty::Bool, sp, ExprKind::Unary(UnOp::Not, Box::new(call)))
                }
            } else {
                return Err(unsupported(op_span, Feature::OrderingAggregates, &[]));
            }
        }
        OpGroup::Additive | OpGroup::Multiplicative | OpGroup::Remainder | OpGroup::Bitwise => {
            let (bop, overflow) = match op {
                ABinOp::Add => (BinOp::Add, Overflow::Checked),
                ABinOp::Sub => (BinOp::Sub, Overflow::Checked),
                ABinOp::Mul => (BinOp::Mul, Overflow::Checked),
                ABinOp::Div => (BinOp::Div, Overflow::Checked),
                ABinOp::Rem => (BinOp::Rem, Overflow::Checked),
                ABinOp::WrapAdd => (BinOp::Add, Overflow::Wrap),
                ABinOp::WrapSub => (BinOp::Sub, Overflow::Wrap),
                ABinOp::WrapMul => (BinOp::Mul, Overflow::Wrap),
                ABinOp::SatAdd => (BinOp::Add, Overflow::Sat),
                ABinOp::SatSub => (BinOp::Sub, Overflow::Sat),
                ABinOp::SatMul => (BinOp::Mul, Overflow::Sat),
                ABinOp::BitAnd => (BinOp::BitAnd, Overflow::Checked),
                ABinOp::BitOr => (BinOp::BitOr, Overflow::Checked),
                ABinOp::BitXor => (BinOp::BitXor, Overflow::Checked),
                ABinOp::Shl => (BinOp::Shl, Overflow::Checked),
                ABinOp::Shr => (BinOp::Shr, Overflow::Checked),
                _ => unreachable!(),
            };
            let t = l.ty.clone();
            if bop == BinOp::Rem && t.is_float() {
                let Ty::Float(k) = t else { unreachable!() };
                Expr::new(
                    Ty::Float(k),
                    sp,
                    ExprKind::Prim {
                        prim: Prim::Math(MathFn::Fmod, k),
                        args: vec![Arg { mode: Mode::Borrow, expr: l }, Arg { mode: Mode::Borrow, expr: r }],
                    },
                )
            } else {
                Expr::new(t, sp, ExprKind::Binary { op: bop, overflow, lhs: Box::new(l), rhs: Box::new(r) })
            }
        }
    };
    if out.ty != ty {
        return Err(internal(sp, "binary operator type"));
    }
    Ok(out)
}

fn lower_try(lw: &mut Lowerer, cx: &mut FnCx, inner: ExprId, ty: Ty, span: Span) -> R<Expr> {
    let v = lower_expr(lw, cx, inner)?;
    // `?` leaves the innermost function (S-192), as `return` does.
    if cx.inline_depth > 0 {
        return Err(unsupported(span, Feature::TryInFromFn, &[]));
    }
    let Ty::Enum(id) = v.ty.clone() else { return Err(internal(span, "`?` on a non-enum")) };
    let variants = lw.enum_variants(id);
    let is_option = variants.first().is_some_and(|(n, _)| n == "None");
    let Ty::Enum(ret_id) = cx.ret.clone() else {
        return Err(internal(span, "`?` in a function without Option / Result"));
    };
    let mut stmts = Vec::new();
    let tmp = materialize(cx, v, &mut stmts, "__try");
    // Option: None -> return None; Some(x) -> x.   Result: Err(e) -> return Err(e); Ok(x) -> x.
    let (good, bad) = if is_option { (1, 0) } else { (0, 1) };
    let early = if is_option {
        Expr::new(cx.ret.clone(), span, ExprKind::Variant { ty: ret_id, tag: 0, fields: Vec::new() })
    } else {
        let err = payload(lw, tmp.clone(), 1, 0)?;
        Expr::new(cx.ret.clone(), span, ExprKind::Variant { ty: ret_id, tag: 1, fields: vec![err] })
    };
    let bad_block = Block { stmts: vec![stmt(span, StmtKind::Return(Some(early)))], value: None };
    let good_block = Block { stmts: Vec::new(), value: Some(Box::new(payload(lw, tmp.clone(), good, 0)?)) };
    let mut arms = vec![(good, good_block), (bad, bad_block)];
    arms.sort_by_key(|(t, _)| *t);
    let sw = Expr::new(ty.clone(), span, ExprKind::Switch { scrutinee: Box::new(tmp), arms, default: None });
    Ok(if stmts.is_empty() {
        sw
    } else {
        Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(sw)) }))
    })
}
