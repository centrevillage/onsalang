//! The stores of the hoisted fields of a flow (§11.3, `FlowInfo::hoists`):
//! the function of a stage writes the fields of its stage, found in the
//! `let`s of the faster stages and in the output, and the functions of the
//! later stages read them ([`super::lower_flow_expr`]); a guarded one is
//! written under its conditions (S-1157). The plan chose and ordered them;
//! the lowering finds them by `FlowInfo::hoist_of` and judges nothing (D-15).

use onsa_sema::flow::{Hoist, HoistId};
use onsa_syntax::ast::{Ast, BinOp, ExprKind as AK};

use super::super::body::{lower_match_with, push_expr_stmt};
use super::branches::{Pick, choose};
use super::*;

#[cfg(test)]
mod tests;

/// [`work`] of the stage and in the scope the function is lowered in.
pub(super) fn walk(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, out: &mut Vec<Stmt>) -> R<()> {
    let (s, state) = super::branches::here(cx, cx.ast.expr(e).span)?;
    let info = cx.flow.as_ref().expect("flow context").info;
    work(lw, cx, info, e, s, &state, out)
}

/// The hoisted fields the functions of a flow write and read (§11.3), of
/// the flows being lowered, the innermost last ([`super::lower_flow`]):
/// every field one reads, one writes, or the lowering is in error (a
/// field read and never written would read its `T.default()`).
#[derive(Debug, Default)]
pub(crate) struct HoistUses {
    written: HashSet<HoistId>,
    read: Vec<(HoistId, Span)>,
}

/// That a function of the flow lowered writes (`write`) or reads at
/// `span` the hoisted field `h` ([`HoistUses`]).
pub(super) fn record(lw: &mut Lowerer, h: HoistId, span: Span, write: bool) -> R<()> {
    let u = lw.hoist_uses.last_mut().ok_or_else(|| internal(span, "a hoisted field outside a flow"))?;
    if write {
        u.written.insert(h);
    } else {
        u.read.push((h, span));
    }
    Ok(())
}

/// The functions of the flow of `info` made by `make`, then the check of
/// the fields they write and read ([`HoistUses`]).
pub(super) fn checked<'b>(
    lw: &mut Lowerer<'b>,
    info: &FlowInfo,
    make: impl FnOnce(&mut Lowerer<'b>) -> R<()>,
) -> R<()> {
    lw.hoist_uses.push(HoistUses::default());
    let made = make(lw);
    let u = lw.hoist_uses.pop().unwrap_or_default();
    made?;
    match u.read.iter().find(|(h, _)| !u.written.contains(h)) {
        Some(&(h, at)) => {
            Err(internal(at, format!("the hoisted field `{}` read and written by no function", info.hoist(h).path)))
        }
        None => Ok(()),
    }
}

/// The work of the stage `s` in `e`, read at another, into `out` in the
/// order of evaluation (§11.3, S-1233), in the scope of `state`: the fields
/// of `s` hoisted in it, the guarded ones (S-1157) under the conditions on
/// their paths (an `if` or `Switch` of the condition read at `s`, holding the
/// bindings of an arm); the constant expressions checked at `s`, for their
/// panic (S-888 (c′)); and the work of its nodes ([`super::nodes`]), their
/// arguments and conditions first. That of the body of a `par~` is of each
/// replica (S-1140), in a loop over them, in the struct of the replica. A
/// field of `s` is lowered, its parts with it; in a conditional position, one
/// of no guard before the conditions ([`placed`]). Where it is written, all
/// but the work of `FlowInfo::late`; at the end of the stage that alone.
pub(super) fn work(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    e: ExprId,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    let flow = &cx.flow.as_ref().expect("flow context").now;
    let (saving, guards) = (flow.saving, flow.guards);
    let now = info.late.contains(&e) == saving;
    let mine = |h: &Hoist| h.stage == s && guards.is_none_or(|g| g == h.guarded);
    if let Some(h) = info.hoist_of(e).filter(|&h| now && mine(info.hoist(h))) {
        let v = lower_expr(lw, cx, e)?;
        let f = sfield(lw, info, state, FieldOf::Hoist(h), info.hoist(h).span)?;
        record(lw, h, f.span, true)?;
        return assign(out, &f, v);
    }
    if let Some(c) = info.check_of(e) {
        if now && c == s && guards != Some(false) {
            push_expr_stmt(lower_expr(lw, cx, e)?, out);
        }
        return Ok(());
    }
    match (info.modifiers.get(&e), info.node_of.get(&e)) {
        (Some(&receiver), _) => return work(lw, cx, info, receiver, s, state, out),
        (None, Some(&id)) if info.node(id).kind.stored().is_some() => return super::nodes::delay_work(lw, cx, out, id),
        (None, Some(&id)) if matches!(info.node(id).kind, PlanKind::Instance { .. }) => {
            return if saving { Ok(()) } else { super::nodes::instance(lw, cx, out, id, true).map(drop) };
        }
        _ => {}
    }
    let at = (s, state);
    let under = |lw: &mut Lowerer, cx: &mut FnCx, x: ExprId| {
        let mut b = Vec::new();
        placed(lw, cx, true, [x], at, &mut b).map(|()| Block { stmts: b, value: None })
    };
    let ast = cx.ast;
    let span = ast.expr(e).span;
    match &ast.expr(e).kind {
        k if guards == Some(false) && !matches!(k, AK::Par { .. }) => {
            return ast.sub_exprs(e).into_iter().try_for_each(|x| work(lw, cx, info, x, s, state, out));
        }
        AK::If { cond, then, else_, tilde: None } => {
            placed(lw, cx, false, [*then].into_iter().chain(*else_), at, out)?;
            work(lw, cx, info, *cond, s, state, out)?;
            let t = under(lw, cx, *then)?;
            let f = match else_ {
                Some(x) => under(lw, cx, *x)?,
                None => Block::default(),
            };
            if !t.stmts.is_empty() || !f.stmts.is_empty() {
                let c = cond_value(lw, cx, info, *cond, s, state)?;
                out.push(stmt(span, StmtKind::If(c, t, f)));
            }
        }
        AK::Binary { op: op @ (BinOp::And | BinOp::Or), lhs, rhs, .. } => {
            placed(lw, cx, false, [*rhs], at, out)?;
            work(lw, cx, info, *lhs, s, state, out)?;
            let r = under(lw, cx, *rhs)?;
            if !r.stmts.is_empty() {
                let mut c = cond_value(lw, cx, info, *lhs, s, state)?;
                if *op == BinOp::Or {
                    c = Expr::new(Ty::Bool, span, ExprKind::Unary(UnOp::Not, Box::new(c)));
                }
                out.push(stmt(span, StmtKind::If(c, r, Block::default())));
            }
        }
        AK::Match { scrutinee, arms, tilde: None } => {
            let mut places = arms.iter().flat_map(|a| a.guard.into_iter().chain([a.body]));
            placed(lw, cx, false, places.clone(), at, out)?;
            work(lw, cx, info, *scrutinee, s, state, out)?;
            if !places.any(|x| has_writes(info, ast, x, s, saving)) {
                return Ok(());
            }
            // The arms with a guard take the general path of a `match`,
            // which gives no value (W8-06): the reading stage is E0200 too.
            if arms.iter().any(|a| a.guard.is_some()) {
                return Err(unsupported(span, Feature::ValueMatch, &[]));
            }
            let v = cond_value(lw, cx, info, *scrutinee, s, state)?;
            let m = lower_match_with(lw, cx, e, v, arms, Ty::Unit, &mut |lw, cx, i| under(lw, cx, arms[i].body))?;
            push_expr_stmt(m, out);
        }
        AK::If { tilde: Some(_), .. } => tilde_if_work(lw, cx, info, e, s, state, out)?,
        AK::Match { tilde: Some(_), .. } => tilde_match_work(lw, cx, info, e, s, state, out)?,
        AK::Par { body, .. } => {
            let Some(&id) = info.node_of.get(&e) else { return Err(internal(span, "a `par~` of no node")) };
            let r = replica_loop(cx, &info.node(id).kind, span)?;
            let elem = match info.field_at(FieldOf::Node(id, Part::Own)) {
                Some(_) => index(sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?, r.index(cx, span))?,
                None => state.clone(),
            };
            cx.flow.as_mut().unwrap().push_scope(elem.clone());
            let mut b = Vec::new();
            let done = work(lw, cx, info, *body, s, &elem, &mut b);
            cx.flow.as_mut().unwrap().now.scopes.pop();
            done?;
            if !b.is_empty() {
                out.push(r.each(cx, span, b));
            }
        }
        _ => {
            for x in ast.sub_exprs(e) {
                work(lw, cx, info, x, s, state, out)?;
            }
        }
    }
    Ok(())
}

/// [`work`] of the conditional positions `xs`, `guarded` under their
/// conditions: its fields of no guard are written before, by that not
/// `guarded` of the outermost, the fields read of a name alone (S-1197).
pub(super) fn placed(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    guarded: bool,
    xs: impl IntoIterator<Item = ExprId>,
    (s, state): (ClockStage, &Expr),
    out: &mut Vec<Stmt>,
) -> R<()> {
    let flow = cx.flow.as_mut().expect("flow context");
    let (info, outer) = (flow.info, flow.now.guards);
    if !guarded && outer.is_some() {
        return Ok(());
    }
    flow.now.guards = Some(guarded);
    let done = xs.into_iter().try_for_each(|x| work(lw, cx, info, x, s, state, out));
    cx.flow.as_mut().expect("flow context").now.guards = outer;
    done
}

/// The fields of `s` of the `if~` chain `e` ([`work`]), as it evaluates
/// them (S-1094): of its conditions, of a later one while the ones before
/// it are false (§11.3); then of every branch, under no more condition
/// (R-14). Nested from the last condition, in a loop.
fn tilde_if_work(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    e: ExprId,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    let chain = onsa_sema::flow::chain(cx.ast, e);
    placed(lw, cx, false, chain.links.iter().skip(1).map(|l| l.cond), (s, state), out)?;
    let mut conds = Vec::with_capacity(chain.links.len());
    for (k, l) in chain.links.iter().enumerate() {
        let mut b = Vec::new();
        match k {
            0 => work(lw, cx, info, l.cond, s, state, &mut b)?,
            _ => placed(lw, cx, true, [l.cond], (s, state), &mut b)?,
        }
        conds.push((l.cond, b));
    }
    let mut later = Vec::new();
    for (c, mut b) in conds.into_iter().rev() {
        if !later.is_empty() {
            let v = cond_value(lw, cx, info, c, s, state)?;
            let not = Expr::new(Ty::Bool, v.span, ExprKind::Unary(UnOp::Not, Box::new(v)));
            let then = Block { stmts: std::mem::take(&mut later), value: None };
            b.push(stmt(cx.ast.expr(c).span, StmtKind::If(not, then, Block::default())));
        }
        later = b;
    }
    out.extend(later);
    for x in chain.links.iter().map(|l| l.then).chain(chain.last) {
        work(lw, cx, info, x, s, state, out)?;
    }
    Ok(())
}

/// The work of `s` of the `match~` `e` ([`work`]), as it evaluates it
/// (S-1094, S-1131): of its scrutinee; of a guard, while the arms before it
/// are not taken and its pattern matches (§11.3); then of every arm body,
/// under no more condition (R-14), after the places of the bindings of `s`
/// ([`choose`], its arms to the last whose binding has one, or to the last
/// guard with a field). One of `FlowInfo::late` is chosen at the end of the
/// stage alone, and its bindings read there (E0801, S-1245).
fn tilde_match_work(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    e: ExprId,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    let (ast, span) = (cx.ast, cx.ast.expr(e).span);
    let (AK::Match { scrutinee, arms, .. }, Some(t)) = (&ast.expr(e).kind, info.tilde_matches.get(&e)) else {
        return Err(internal(span, "a `match~` the plan did not record"));
    };
    let saving = cx.flow.as_ref().unwrap().now.saving;
    placed(lw, cx, false, arms.iter().filter_map(|a| a.guard), (s, state), out)?;
    let mut bodies = Vec::new();
    for a in arms {
        work(lw, cx, info, a.body, s, state, &mut bodies)?;
    }
    let guards = arms.iter().rposition(|a| a.guard.is_some_and(|g| has_writes(info, ast, g, s, saving)));
    let guards = guards.map_or(0, |w| w + 1);
    let slots = &cx.flow.as_ref().unwrap().now.local_override;
    let bound = t.arms.iter().rposition(|b| b.iter().any(|b| slots.contains_key(&b.0))).map_or(0, |b| b + 1);
    // The stores after it read the bindings of one chosen at the end (of a slower delay in an arm).
    let read = if info.late.contains(&e) { saving } else { !bodies.is_empty() };
    let bound = if read { bound } else { 0 };
    if guards == 0 && bound == 0 {
        work(lw, cx, info, *scrutinee, s, state, out)?;
    } else {
        let pick = Pick { upto: guards.max(bound), eval: guards.saturating_sub(1).max(bound), write: true };
        choose(lw, cx, e, pick, s, state, out)?;
    }
    out.append(&mut bodies);
    Ok(())
}

/// Whether `e` holds a guarded field or a check of the stage `s`, of the
/// work of `FlowInfo::late` or not.
fn has_writes(info: &FlowInfo, ast: &Ast, e: ExprId, s: ClockStage, late: bool) -> bool {
    let guarded = info.hoist_of(e).map(|h| info.hoist(h)).filter(|h| h.guarded);
    let here = guarded.map(|h| h.stage).or(info.check_of(e));
    (here == Some(s) && info.late.contains(&e) == late)
        || ast.sub_exprs(e).into_iter().any(|x| has_writes(info, ast, x, s, late))
}

/// The value at the stage `s` of the condition `c` that guards fields of
/// `s`: its field, which [`work`] wrote before, when it is one of `s`;
/// else lowered, an earlier field read ([`super::lower_flow_expr`]). The
/// plan guards a field of `s` with conditions decided by `s` only (D-15).
pub(super) fn cond_value(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    c: ExprId,
    s: ClockStage,
    state: &Expr,
) -> R<Expr> {
    let x = cx.ast.without_parens(c);
    let span = cx.ast.expr(c).span;
    let late = |k: Clock| k.stage().is_some_and(|k| k > s);
    if info.clocks.exprs.get(&c).copied().is_some_and(late) {
        return Err(internal(span, "a field guarded by a condition decided after its stage"));
    }
    match info.hoist_of(x).filter(|&h| info.hoist(h).stage == s) {
        Some(h) => sfield(lw, info, state, FieldOf::Hoist(h), span),
        None => lower_expr(lw, cx, c),
    }
}
