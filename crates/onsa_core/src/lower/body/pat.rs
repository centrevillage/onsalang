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
        PatKind::TupleStruct { elems, .. } => {
            let (tag, _) = ctor_of(lw, cx, pat, value.ty)?;
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

/// Constructor tag (and arity) of the ctor pattern `pat` against an enum
/// type: the tag the check recorded (`BodyInfo::pat_ctors`).
fn ctor_of(lw: &mut Lowerer, cx: &FnCx, pat: PatId, ty: CTy) -> R<(u32, usize)> {
    let span = cx.ast.pat(pat).span;
    let Some(&tag) = cx.info.pat_ctors.get(&pat) else { return Err(internal(span, "pattern without a constructor")) };
    let TyKind::Enum(id) = *lw.m.tys.kind(ty) else { return Err(internal(span, "constructor pattern on a non-enum")) };
    let arity = lw.enum_variants(id).get(tag as usize).map(|(_, f)| f.len()).unwrap_or(0);
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
pub(crate) fn pat_test(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr) -> R<Option<Expr>> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    // The tests of the parts that may fail, in the order of the text.
    let mut parts = Vec::new();
    match &p.kind {
        PatKind::Wild | PatKind::Bind(_) => Ok(None),
        PatKind::Lit(l) | PatKind::Neg(l) => {
            let neg = matches!(p.kind, PatKind::Neg(_));
            let v = match (l, lw.m.tys.kind(place.ty).clone()) {
                (ALit::Int { value, .. }, TyKind::Int(_)) => {
                    Lit::Int(if neg { -(*value as i128) } else { *value as i128 })
                }
                (ALit::Char(c), TyKind::Char) => Lit::Char(*c),
                (ALit::Bool(b), TyKind::Bool) => Lit::Bool(*b),
                // Of a `FixedStr[N]`, `==` to the value of the literal (§7, §4.2).
                (ALit::Str(text), TyKind::Struct(id)) => {
                    let rhs = Expr::new(place.ty, span, crate::lower::fixed_str::value(lw, cx, text, id, span)?);
                    return crate::lower::eq::eq_expr(lw, place.clone(), rhs, span, span).map(Some);
                }
                // A `Str` subject stopped the unit at its type.
                (ALit::Str(_), _) => return Err(internal(span, "a string pattern on a subject of no `FixedStr`")),
                _ => return Err(internal(span, "literal pattern type")),
            };
            let rhs = lit(place.ty, span, v);
            Ok(Some(Expr::new(
                Types::BOOL,
                span,
                ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(place.clone()), rhs: Box::new(rhs) },
            )))
        }
        PatKind::Path(_) => match cx.info.pat_consts.get(&pat).cloned() {
            Some(target) => const_test(lw, cx, target, place, span).map(Some),
            None => {
                let (tag, _) = ctor_of(lw, cx, pat, place.ty)?;
                Ok(Some(tag_test(lw, place, tag)?))
            }
        },
        PatKind::TupleStruct { elems, .. } => {
            let (tag, _) = ctor_of(lw, cx, pat, place.ty)?;
            parts.push(tag_test(lw, place, tag)?);
            for (i, &el) in elems.iter().enumerate() {
                let sub = payload(lw, place.clone(), tag, i as u32)?;
                parts.extend(pat_test(lw, cx, el, &sub)?);
            }
            Ok(balanced(LogicOp::And, parts, span))
        }
        PatKind::Tuple(elems) => {
            for (i, &el) in elems.iter().enumerate() {
                let sub = field(lw, place.clone(), i as u32)?;
                parts.extend(pat_test(lw, cx, el, &sub)?);
            }
            Ok(balanced(LogicOp::And, parts, span))
        }
        PatKind::Struct { fields, .. } => {
            for (name, fp) in fields {
                let sub = field_by_name(lw, place.clone(), &name.name, name.span)?;
                parts.extend(pat_test(lw, cx, *fp, &sub)?);
            }
            Ok(balanced(LogicOp::And, parts, span))
        }
        PatKind::Or(alts) => {
            if alts.iter().any(|&a| pat_binds(cx, a)) {
                return Err(unsupported(span, Feature::OrPatternBindings, &[]));
            }
            for &alt in alts {
                parts.push(pat_test(lw, cx, alt, place)?.unwrap_or_else(|| bool_lit(span, true)));
            }
            Ok(balanced(LogicOp::Or, parts, span))
        }
    }
}

/// The test of a constant of a pattern against a place: `==` to its value
/// (§7, S-185). A place of `Str` is none: its type stops the lowering first.
fn const_test(lw: &mut Lowerer, cx: &mut FnCx, target: Target, place: &Expr, span: Span) -> R<Expr> {
    let Target::Const { def, of, inst } = target else { return Err(internal(span, "pattern of no constant")) };
    let (def, gargs) = lw.instance_target(def, of, inst, cx, span)?;
    let rhs = Expr::new(place.ty, span, ExprKind::Const(lw.const_id(def, gargs, span)?));
    Ok(Expr::new(Types::BOOL, span, ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(place.clone()), rhs: Box::new(rhs) }))
}

pub(super) fn tag_test(lw: &Lowerer, place: &Expr, tag: u32) -> R<Expr> {
    let t = tag_of(lw, place.clone())?;
    let span = place.span;
    let rhs = lit(t.ty, span, Lit::Int(tag as i128));
    Ok(Expr::new(Types::BOOL, span, ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(t), rhs: Box::new(rhs) }))
}

/// Bindings of a (possibly refutable) pattern once it is known to match.
pub(crate) fn pat_bind(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr, out: &mut Vec<Stmt>) -> R<()> {
    let p = cx.ast.pat(pat);
    let span = p.span;
    match &p.kind {
        PatKind::Bind(_) => {
            let l = cx.pat_local(pat)?;
            out.push(stmt(span, StmtKind::Let(l, place.clone())));
            Ok(())
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) | PatKind::Or(_) => Ok(()),
        PatKind::TupleStruct { elems, .. } => {
            let (tag, _) = ctor_of(lw, cx, pat, place.ty)?;
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
    ty: CTy,
) -> R<Expr> {
    let scrut_ast = match &cx.expr(scrutinee).kind {
        AK::Move(inner) => *inner,
        _ => scrutinee,
    };
    let s = lower_expr(lw, cx, scrut_ast)?;
    lower_match_with(lw, cx, e, s, arms, ty, pat_bind, &mut |lw, cx, i| lower_block_expr(lw, cx, arms[i].body))
}

/// The test of the arm pattern `pat` against `place` (none: always), and
/// whether it binds. One that uses an unsupported feature (S-67) never
/// matches and binds nothing, so lowering reaches the guard and the body.
pub(crate) fn arm_test(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr) -> R<(Option<Expr>, bool)> {
    let hole = Hole::Pat(cx.module, pat);
    if !lw.holes.contains(&hole) {
        return Ok((pat_test(lw, cx, pat, place).map_err(|f| at_hole(f, hole))?, true));
    }
    let span = cx.ast.pat(pat).span;
    cx.placeholder = true;
    Ok((Some(bool_lit(span, false)), false))
}

/// The `match` `e` of the lowered scrutinee `s`, whose arm `i` has the body
/// `body(i)`, lowered after the bindings of its pattern by `bind`: of the
/// flow body too, whose hoisted fields its arms write (§11.3).
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_match_with(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    e: ExprId,
    s: Expr,
    arms: &[ast::MatchArm],
    ty: CTy,
    bind: fn(&mut Lowerer, &mut FnCx, PatId, &Expr, &mut Vec<Stmt>) -> R<()>,
    body: &mut dyn FnMut(&mut Lowerer, &mut FnCx, usize) -> R<Block>,
) -> R<Expr> {
    let span = cx.expr(e).span;
    let mut stmts = Vec::new();
    let place = materialize(cx, s, &mut stmts, "__match");
    let want = ty != Types::UNIT;
    // Fast path: every arm is a constructor (or a final catch-all) with
    // irrefutable sub-patterns and no guard -> `Switch`.
    let simple = matches!(lw.m.tys.kind(place.ty), TyKind::Enum(_))
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
        for (i, arm) in arms.iter().enumerate() {
            let mut b = Vec::new();
            match &cx.ast.pat(arm.pat).kind {
                PatKind::Wild | PatKind::Bind(_) => {
                    bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = body(lw, cx, i)?;
                    b.extend(body.stmts);
                    default = Some(Block { stmts: b, value: if want { body.value } else { None } });
                }
                _ => {
                    let (tag, _) = ctor_of(lw, cx, arm.pat, place.ty)?;
                    bind(lw, cx, arm.pat, &place, &mut b)?;
                    let body = body(lw, cx, i)?;
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
        let sw = Expr::new(ty, span, ExprKind::Switch { scrutinee: Box::new(place), arms: sw_arms, default });
        return Ok(if stmts.is_empty() {
            sw
        } else {
            Expr::new(ty, span, ExprKind::Block(Block { stmts, value: Some(Box::new(sw)) }))
        });
    }
    // General path: `if` chain with a `done` flag (guards may fall through).
    let done = cx.temp("__done", Types::BOOL);
    stmts.push(stmt(span, StmtKind::Let(done, bool_lit(span, false))));
    let result = if want { Some(cx.temp("__result", ty)) } else { None };
    for (i, arm) in arms.iter().enumerate() {
        let not_done = Expr::new(Types::BOOL, span, ExprKind::Unary(UnOp::Not, Box::new(local_expr(cx, done, span))));
        let (test, binds) = arm_test(lw, cx, arm.pat, &place)?;
        let cond = match test {
            None => not_done,
            Some(t) => Expr::new(
                Types::BOOL,
                span,
                ExprKind::Logic { op: LogicOp::And, lhs: Box::new(not_done), rhs: Box::new(t) },
            ),
        };
        let mut inner = Vec::new();
        if binds {
            bind(lw, cx, arm.pat, &place, &mut inner)?;
        }
        let mut body_stmts = vec![stmt(span, StmtKind::Assign(Place::Local(done), bool_lit(span, true)))];
        let body = body(lw, cx, i)?;
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
