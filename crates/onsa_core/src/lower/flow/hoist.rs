//! The stores of the hoisted fields of a flow (§11.3, `FlowInfo::hoists`):
//! the function of a stage writes the fields of its stage, found in the
//! `let`s of the faster stages and in the output, and the functions of the
//! later stages read them ([`super::lower_flow_expr`]); a guarded one is
//! written under its conditions (S-1157). The plan chose and ordered them;
//! the lowering finds them by `FlowInfo::hoist_of` and judges nothing (D-15).

use onsa_sema::flow::{Hoist, HoistId, Pos, positions};
use onsa_syntax::ast::{BinOp, ExprKind as AK};

use super::super::body::{arm_test, lower_match_with, push_expr_stmt};
use super::branches::{Pick, bind_read, choose};
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
/// but the work of `FlowInfo::late`, of whose fields what they read of events
/// (S-1249); at the end of the stage that alone.
pub(super) fn work(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    e: ExprId,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    work_of(lw, cx, info, e, s, state, out)?;
    let late = info.late.contains(&e) && !cx.flow.as_ref().expect("flow context").now.saving;
    match info.hoist_of(e).map(|h| info.hoist(h)).filter(|h| late && h.stage == s) {
        Some(h) => super::nodes::saved_reads(lw, cx, out, &h.saved, (&h.path, h.owner)),
        None => Ok(()),
    }
}

fn work_of(
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
    let mine = |h: &Hoist| h.stage == s && guards.is_none_or(|g| g == h.guarded) && h.arms.is_empty();
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
            ast.sub_exprs(e).into_iter().try_for_each(|x| work(lw, cx, info, x, s, state, out))?;
            return if matches!(k, AK::Match { .. }) { arm_writes(lw, cx, info, e, at, out) } else { Ok(()) };
        }
        // A condition and the positions it chooses: of an `if`, its branches
        // (the later `if` of a chain is the one in its `else`); of `&&` / `||`, its right.
        AK::If { tilde: None, .. } | AK::Binary { op: BinOp::And | BinOp::Or, .. } => {
            let mut parts = positions(ast, e);
            let Some((cond, Pos::Cond)) = parts.next() else {
                return Err(internal(span, "a choice with no condition"));
            };
            let chosen: Vec<ExprId> = parts.of_node().map(|(x, _)| x).collect();
            placed(lw, cx, false, chosen.iter().copied(), at, out)?;
            work(lw, cx, info, cond, s, state, out)?;
            let blocks = chosen.iter().map(|&x| under(lw, cx, x)).collect::<R<Vec<Block>>>()?;
            if blocks.iter().any(|b| !b.stmts.is_empty()) {
                let mut c = cond_value(lw, cx, info, cond, s, state)?;
                if matches!(ast.expr(e).kind, AK::Binary { op: BinOp::Or, .. }) {
                    c = Expr::new(Types::BOOL, span, ExprKind::Unary(UnOp::Not, Box::new(c)));
                }
                let mut blocks = blocks.into_iter();
                let (t, f) = (blocks.next().unwrap_or_default(), blocks.next().unwrap_or_default());
                out.push(stmt(span, StmtKind::If(c, t, f)));
            }
        }
        AK::Match { scrutinee, arms, tilde: None } => {
            let places: Vec<ExprId> = positions(ast, e).skip(1).map(|(x, _)| x).collect();
            placed(lw, cx, false, places.iter().copied(), at, out)?;
            work(lw, cx, info, *scrutinee, s, state, out)?;
            arm_writes(lw, cx, info, e, at, out)?;
            if !places.iter().any(|&x| info.writes_under(ast, x, s, saving)) {
                return Ok(());
            }
            // The arms with a guard take the general path of a `match`,
            // which gives no value (W8-06): the reading stage is E0200 too.
            if arms.iter().any(|a| a.guard.is_some()) {
                return Err(unsupported(span, Feature::ValueMatch, &[]));
            }
            let v = cond_value(lw, cx, info, *scrutinee, s, state)?;
            let m = lower_match_with(lw, cx, e, v, arms, Types::UNIT, bind_read, &mut |lw, cx, i| {
                under(lw, cx, arms[i].body)
            })?;
            push_expr_stmt(m, out);
        }
        AK::If { tilde: Some(_), .. } => tilde_if_work(lw, cx, info, e, s, state, out)?,
        AK::Match { tilde: Some(_), .. } => tilde_match_work(lw, cx, info, e, s, state, out)?,
        AK::Par { body, .. } => {
            let Some(&id) = info.node_of.get(&e) else { return Err(internal(span, "a `par~` of no node")) };
            Replicas::scoped(lw, cx, (id, state, span), out, |lw, cx, _, elem, b| {
                work(lw, cx, info, *body, s, elem, b)
            })?;
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
    let parts: Vec<(ExprId, Pos)> = positions(cx.ast, e).collect();
    let of = |q: Pos| parts.iter().filter(move |&&(_, p)| p == q).map(|&(x, _)| x);
    placed(lw, cx, false, of(Pos::Choose), (s, state), out)?;
    let mut conds = Vec::with_capacity(parts.len() / 2);
    for &(c, p) in parts.iter().filter(|&&(_, p)| p != Pos::Always) {
        let mut b = Vec::new();
        match p {
            Pos::Cond => work(lw, cx, info, c, s, state, &mut b)?,
            _ => placed(lw, cx, true, [c], (s, state), &mut b)?,
        }
        conds.push((c, b));
    }
    let mut later = Vec::new();
    for (c, mut b) in conds.into_iter().rev() {
        if !later.is_empty() {
            let v = cond_value(lw, cx, info, c, s, state)?;
            let not = Expr::new(Types::BOOL, v.span, ExprKind::Unary(UnOp::Not, Box::new(v)));
            let then = Block { stmts: std::mem::take(&mut later), value: None };
            b.push(stmt(cx.ast.expr(c).span, StmtKind::If(not, then, Block::default())));
        }
        later = b;
    }
    out.extend(later);
    for x in of(Pos::Always) {
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
    let parts: Vec<(ExprId, Pos)> = positions(ast, e).collect();
    let of = |q: Pos| parts.iter().filter(move |&&(_, p)| p == q).map(|&(x, _)| x);
    placed(lw, cx, false, of(Pos::Choose), (s, state), out)?;
    let mut bodies = Vec::new();
    for x in of(Pos::Always) {
        work(lw, cx, info, x, s, state, &mut bodies)?;
    }
    let guards = arms.iter().rposition(|a| a.guard.is_some_and(|g| info.writes_under(ast, g, s, saving)));
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
    arm_writes(lw, cx, info, e, (s, state), out)?;
    out.append(&mut bodies);
    Ok(())
}

/// The fields of `s` of the reads of bindings of arms whose first `match` /
/// `match~` is `m` (`Hoist::arms`, S-1247), of the work of the walk now (its
/// guards, `FlowInfo::late`): each written when the patterns of its arms
/// match their scrutinees, under no other condition. In a guard of `match~`
/// a binding is the value of the pattern, not its place.
fn arm_writes(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    m: ExprId,
    at: (ClockStage, &Expr),
    out: &mut Vec<Stmt>,
) -> R<()> {
    let flow = &cx.flow.as_ref().expect("flow context").now;
    let (saving, guards) = (flow.saving, flow.guards);
    let ours = |h: &&Hoist| {
        h.arms.first().is_some_and(|a| a.0 == m)
            && h.stage == at.0
            && guards.is_none_or(|g| g == h.guarded)
            && info.late.contains(&h.expr) == saving
    };
    for (i, h) in info.hoists.iter().enumerate().filter(|(_, h)| ours(h)) {
        let bound = h.arms.iter().filter_map(|&(m, k)| info.tilde_matches.get(&m).map(|t| &t.arms[k as usize]));
        let overrides = &mut cx.flow.as_mut().expect("flow context").now.local_override;
        let held: Vec<_> = bound.flatten().filter_map(|b| overrides.remove_entry(&b.0)).collect();
        let written = arm_write(lw, cx, info, (HoistId(i as u32), h), at);
        cx.flow.as_mut().expect("flow context").now.local_override.extend(held);
        out.extend(written?);
    }
    Ok(())
}

/// The write of the field `h` of [`arm_writes`]: the scrutinee of each of its
/// arms (of the first, its value at `s`, [`cond_value`]), tested by the
/// pattern, its bindings bound, the next in it.
fn arm_write(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    info: &FlowInfo,
    (id, h): (HoistId, &Hoist),
    (s, state): (ClockStage, &Expr),
) -> R<Vec<Stmt>> {
    let mut levels = Vec::with_capacity(h.arms.len());
    for (k, &(m, arm)) in h.arms.iter().enumerate() {
        let AK::Match { scrutinee, arms, .. } = &cx.ast.expr(m).kind else {
            return Err(internal(h.span, "the arm of a read of a binding of no `match`"));
        };
        let (pat, span) = (arms[arm as usize].pat, cx.ast.expr(*scrutinee).span);
        let v = if k == 0 { cond_value(lw, cx, info, *scrutinee, s, state)? } else { lower_expr(lw, cx, *scrutinee)? };
        let mut before = Vec::new();
        let place = materialize(cx, v, &mut before, "__arm");
        let (test, binds) = arm_test(lw, cx, pat, &place)?;
        let mut inner = Vec::new();
        if binds {
            bind_read(lw, cx, pat, &place, &mut inner)?;
        }
        levels.push((span, before, test, inner));
    }
    let f = sfield(lw, info, state, FieldOf::Hoist(id), h.span)?;
    record(lw, id, f.span, true)?;
    let mut body = Vec::new();
    assign(&mut body, &f, lower_expr(lw, cx, h.expr)?)?;
    for (span, mut before, test, mut inner) in levels.into_iter().rev() {
        inner.append(&mut body);
        match test {
            Some(t) => before.push(stmt(span, StmtKind::If(t, Block { stmts: inner, value: None }, Block::default()))),
            None => before.append(&mut inner),
        }
        body = before;
    }
    Ok(body)
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
