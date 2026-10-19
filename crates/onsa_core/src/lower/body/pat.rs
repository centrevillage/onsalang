//! Lowering of function bodies: patterns and `match` (T3-3).

use super::*;

// ---------------------------------------------------------------- patterns

/// Bind an irrefutable pattern (`let`, `for`, switch arms) to `value`.
pub(crate) fn bind_irrefutable(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, value: Expr, out: &mut Vec<Stmt>) -> R<()> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    match &p.kind {
        PatKind::Bind(_) => {
            let l = cx.pat_local(pat)?;
            out.push(stmt(span, StmtKind::Let(l, value)));
            Ok(())
        }
        PatKind::Wild => {
            push_expr_stmt(value, out);
            Ok(())
        }
        PatKind::Tuple(elems) => {
            let base = materialize(cx, value, out, "__tuple");
            for (i, &el) in elems.iter().enumerate() {
                let f = field(lw, base.clone(), i as u32)?;
                bind_irrefutable(lw, cx, el, f, out)?;
            }
            Ok(())
        }
        PatKind::Struct { fields, .. } => {
            let base = materialize(cx, value, out, "__struct");
            for (name, fp) in fields {
                let f = field_by_name(lw, base.clone(), &name.name, name.span)?;
                bind_irrefutable(lw, cx, *fp, f, out)?;
            }
            Ok(())
        }
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &value.ty)?;
            let base = materialize(cx, value, out, "__variant");
            for (i, &el) in elems.iter().enumerate() {
                let f = payload(lw, base.clone(), tag, i as u32)?;
                bind_irrefutable(lw, cx, el, f, out)?;
            }
            Ok(())
        }
        PatKind::Path(_) => {
            push_expr_stmt(value, out);
            Ok(())
        }
        PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Or(_) => {
            Err(internal(span, "refutable pattern in an irrefutable position"))
        }
    }
}

/// Constructor tag (and arity) of a ctor pattern path against an enum type.
fn ctor_of(lw: &mut Lowerer, cx: &FnCx, path: &ast::Path, ty: &Ty) -> R<(u32, usize)> {
    // Sema resolved the path already: a failure here is lowering's own.
    let entity = lw.a.resolve_path(cx.module, path).map_err(|e| {
        let d = e.into_diagnostic();
        internal(d.span, format!("pattern path does not resolve ({}: {})", d.code.as_str(), d.message))
    })?;
    let tag = match entity {
        Entity::Builtin(Builtin::None) | Entity::Builtin(Builtin::Ok) => 0,
        Entity::Builtin(Builtin::Some) | Entity::Builtin(Builtin::Err) => 1,
        Entity::Variant(_, i) => i,
        _ => return Err(internal(path.span, "pattern path is not a constructor")),
    };
    let Ty::Enum(id) = ty else { return Err(internal(path.span, "constructor pattern on a non-enum")) };
    let arity = lw.enum_variants(*id).get(tag as usize).map(|(_, f)| f.len()).unwrap_or(0);
    Ok((tag, arity))
}

fn is_irrefutable(cx: &FnCx, pat: PatId) -> bool {
    match &cx.ast.pat(pat).kind {
        PatKind::Wild | PatKind::Bind(_) => true,
        PatKind::Tuple(es) => es.iter().all(|&e| is_irrefutable(cx, e)),
        PatKind::Struct { fields, .. } => fields.iter().all(|(_, p)| is_irrefutable(cx, *p)),
        _ => false,
    }
}

fn pat_binds(cx: &FnCx, pat: PatId) -> bool {
    match &cx.ast.pat(pat).kind {
        PatKind::Bind(_) => true,
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => false,
        PatKind::Tuple(es) | PatKind::TupleStruct { elems: es, .. } | PatKind::Or(es) => {
            es.iter().any(|&e| pat_binds(cx, e))
        }
        PatKind::Struct { fields, .. } => fields.iter().any(|(_, p)| pat_binds(cx, *p)),
    }
}

/// Test of a refutable pattern against a place; `None` means "always matches".
fn pat_test(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr) -> R<Option<Expr>> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    let and = |a: Option<Expr>, b: Option<Expr>| match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => {
            Some(Expr::new(Ty::Bool, span, ExprKind::Logic { op: LogicOp::And, lhs: Box::new(a), rhs: Box::new(b) }))
        }
    };
    match &p.kind {
        PatKind::Wild | PatKind::Bind(_) => Ok(None),
        PatKind::Lit(l) | PatKind::Neg(l) => {
            let neg = matches!(p.kind, PatKind::Neg(_));
            let v = match (l, &place.ty) {
                (ALit::Int { value, .. }, Ty::Int(_)) => Lit::Int(if neg { -(*value as i128) } else { *value as i128 }),
                (ALit::Char(c), Ty::Char) => Lit::Char(*c),
                (ALit::Bool(b), Ty::Bool) => Lit::Bool(*b),
                (ALit::Str(_), _) => return Err(unsupported(span, Feature::StrPatterns, &[])),
                _ => return Err(internal(span, "literal pattern type")),
            };
            let rhs = lit(place.ty.clone(), span, v);
            Ok(Some(Expr::new(
                Ty::Bool,
                span,
                ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(place.clone()), rhs: Box::new(rhs) },
            )))
        }
        PatKind::Path(path) => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            Ok(Some(tag_test(lw, place, tag)?))
        }
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            let mut t = Some(tag_test(lw, place, tag)?);
            for (i, &el) in elems.iter().enumerate() {
                let sub = payload(lw, place.clone(), tag, i as u32)?;
                let st = pat_test(lw, cx, el, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Tuple(elems) => {
            let mut t = None;
            for (i, &el) in elems.iter().enumerate() {
                let sub = field(lw, place.clone(), i as u32)?;
                let st = pat_test(lw, cx, el, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Struct { fields, .. } => {
            let mut t = None;
            for (name, fp) in fields {
                let sub = field_by_name(lw, place.clone(), &name.name, name.span)?;
                let st = pat_test(lw, cx, *fp, &sub)?;
                t = and(t, st);
            }
            Ok(t)
        }
        PatKind::Or(alts) => {
            if alts.iter().any(|&a| pat_binds(cx, a)) {
                return Err(unsupported(span, Feature::OrPatternBindings, &[]));
            }
            let mut t: Option<Expr> = None;
            for &alt in alts {
                let st = pat_test(lw, cx, alt, place)?.unwrap_or_else(|| bool_lit(span, true));
                t = Some(match t {
                    None => st,
                    Some(prev) => Expr::new(
                        Ty::Bool,
                        span,
                        ExprKind::Logic { op: LogicOp::Or, lhs: Box::new(prev), rhs: Box::new(st) },
                    ),
                });
            }
            Ok(t)
        }
    }
}

pub(super) fn tag_test(lw: &Lowerer, place: &Expr, tag: u32) -> R<Expr> {
    let t = tag_of(lw, place.clone())?;
    let span = place.span;
    let rhs = lit(t.ty.clone(), span, Lit::Int(tag as i128));
    Ok(Expr::new(Ty::Bool, span, ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(t), rhs: Box::new(rhs) }))
}

/// Bindings of a (possibly refutable) pattern once it is known to match.
fn pat_bind(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr, out: &mut Vec<Stmt>) -> R<()> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    match &p.kind {
        PatKind::Bind(_) => {
            let l = cx.pat_local(pat)?;
            out.push(stmt(span, StmtKind::Let(l, place.clone())));
            Ok(())
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::Or(_) => Ok(()),
        PatKind::TupleStruct { path, elems } => {
            let (tag, _) = ctor_of(lw, cx, path, &place.ty)?;
            for (i, &el) in elems.iter().enumerate() {
                let sub = payload(lw, place.clone(), tag, i as u32)?;
                pat_bind(lw, cx, el, &sub, out)?;
            }
            Ok(())
        }
        PatKind::Tuple(elems) => {
            for (i, &el) in elems.iter().enumerate() {
                let sub = field(lw, place.clone(), i as u32)?;
                pat_bind(lw, cx, el, &sub, out)?;
            }
            Ok(())
        }
        PatKind::Struct { fields, .. } => {
            for (name, fp) in fields {
                let sub = field_by_name(lw, place.clone(), &name.name, name.span)?;
                pat_bind(lw, cx, *fp, &sub, out)?;
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------- match

pub(super) fn lower_match(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    scrutinee: ExprId,
    arms: &[ast::MatchArm],
    ty: Ty,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let scrut_ast = match &cx.expr(scrutinee).kind {
        AK::Move(inner) => *inner,
        _ => scrutinee,
    };
    let s = lower_expr(lw, cx, scrut_ast)?;
    let mut stmts = Vec::new();
    let place = materialize(cx, s, &mut stmts, "__match");
    let want = ty != Ty::Unit;
    // Fast path: every arm is a constructor (or a final catch-all) with
    // irrefutable sub-patterns and no guard -> `Switch`.
    let simple = matches!(place.ty, Ty::Enum(_))
        && arms.iter().all(|a| a.guard.is_none())
        && arms.iter().enumerate().all(|(i, a)| match &cx.ast.pat(a.pat).kind {
            PatKind::Path(_) => true,
            PatKind::TupleStruct { elems, .. } => elems.iter().all(|&p| is_irrefutable(cx, p)),
            PatKind::Wild | PatKind::Bind(_) => i == arms.len() - 1,
            _ => false,
        });
    if simple {
        let mut sw_arms = Vec::new();
        let mut default = None;
        for arm in arms {
            let mut b = Vec::new();
            match &cx.ast.pat(arm.pat).kind {
                PatKind::Wild | PatKind::Bind(_) => {
                    pat_bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = lower_block_expr(lw, cx, arm.body)?;
                    b.extend(body.stmts);
                    default = Some(Block { stmts: b, value: if want { body.value } else { None } });
                }
                _ => {
                    let path = match &cx.ast.pat(arm.pat).kind {
                        PatKind::Path(p) | PatKind::TupleStruct { path: p, .. } => p.clone(),
                        _ => unreachable!(),
                    };
                    let (tag, _) = ctor_of(lw, cx, &path, &place.ty)?;
                    pat_bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = lower_block_expr(lw, cx, arm.body)?;
                    b.extend(body.stmts);
                    let blk = Block { stmts: b, value: if want { body.value } else { None } };
                    if sw_arms.iter().any(|(t, _)| *t == tag) {
                        // A later arm for the same tag is unreachable; keep the first.
                        continue;
                    }
                    sw_arms.push((tag, blk));
                }
            }
        }
        let sw = Expr::new(ty.clone(), span, ExprKind::Switch { scrutinee: Box::new(place), arms: sw_arms, default });
        return Ok(if stmts.is_empty() {
            sw
        } else {
            Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(sw)) }))
        });
    }
    // General path: `if` chain with a `done` flag (guards may fall through).
    let done = cx.temp("__done", Ty::Bool);
    stmts.push(stmt(span, StmtKind::Let(done, bool_lit(span, false))));
    let result = if want { Some(cx.temp("__result", ty.clone())) } else { None };
    for arm in arms {
        let not_done = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(local_expr(cx, done, span))));
        // A pattern that uses an unsupported feature (S-67): the arm never
        // matches and binds nothing, so lowering reaches its guard and body.
        let pat_hole = Hole::Pat(cx.module, arm.pat);
        let placeholder = lw.holes.contains(&pat_hole);
        let test = if placeholder {
            let pat_span = cx.ast.pat(arm.pat).span;
            lw.hole_spans.push(pat_span);
            Some(bool_lit(pat_span, false))
        } else {
            pat_test(lw, cx, arm.pat, &place).map_err(|f| at_hole(f, pat_hole))?
        };
        let cond = match test {
            None => not_done,
            Some(t) => Expr::new(
                Ty::Bool,
                span,
                ExprKind::Logic { op: LogicOp::And, lhs: Box::new(not_done), rhs: Box::new(t) },
            ),
        };
        let mut inner = Vec::new();
        if !placeholder {
            pat_bind(lw, cx, arm.pat, &place, &mut inner)?;
        }
        let mut body_stmts = vec![stmt(span, StmtKind::Assign(Place::Local(done), bool_lit(span, true)))];
        let body = lower_block_expr(lw, cx, arm.body)?;
        let diverges = body.diverges();
        body_stmts.extend(body.stmts);
        match (result, body.value) {
            (Some(r), Some(v)) => body_stmts.push(stmt(span, StmtKind::Assign(Place::Local(r), *v))),
            (Some(_), None) if !diverges => return Err(internal(span, "match arm without a value")),
            (_, Some(v)) => push_expr_stmt(*v, &mut body_stmts),
            _ => {}
        }
        let body_block = Block { stmts: body_stmts, value: None };
        match arm.guard {
            Some(g) => {
                let gc = lower_expr(lw, cx, g)?;
                inner.push(stmt(span, StmtKind::If(gc, body_block, Block::default())));
            }
            None => inner.extend(body_block.stmts),
        }
        stmts.push(stmt(span, StmtKind::If(cond, Block { stmts: inner, value: None }, Block::default())));
    }
    // The general path gives no value yet (R-06): its result is assigned in
    // the arms but never declared. A `match` whose value is not used (a
    // statement, a `()` match) keeps this path; W8-06 lowers the value.
    if result.is_some() {
        return Err(unsupported(span, Feature::ValueMatch, &[]));
    }
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: None })))
}
