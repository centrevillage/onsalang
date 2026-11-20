//! `if~` and `match~` in `tick` (§11.5, S-110, R-14, S-1094): every branch
//! evaluated, one chosen; and the choice of an arm of `match~` at a stage,
//! which writes the places of its bindings (S-1131). Their parts of a
//! slower stage are written by [`super::hoist`].

use onsa_sema::flow::chain;
use onsa_syntax::ast::{ExprKind as AK, MatchArm, PatId};

use super::super::body::{arm_test, drop_value, lower_block_expr, pat_bind, push_expr_stmt};
use super::hoist::{cond_value, writes};
use super::*;

/// The `if~` chain `e` of the type `ty`, in one block: the conditions from
/// the first to the one that holds (S-1094), giving the number of its link
/// (the number of links of none); then every branch ([`every`]). One loop
/// over the chain.
pub(crate) fn tilde_if(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, ty: Ty) -> R<Expr> {
    let span = cx.ast.expr(e).span;
    let chain = chain(cx.ast, e);
    let Some(last) = chain.last else { return Err(internal(span, "an `if~` with no `else`")) };
    let mut conds = Vec::with_capacity(chain.links.len());
    for l in &chain.links {
        conds.push(lower_expr(lw, cx, l.cond)?);
    }
    let mut taken = u32_lit(span, conds.len() as u32);
    for (k, c) in conds.into_iter().enumerate().rev() {
        let then = value(u32_lit(span, k as u32));
        taken = Expr::new(Ty::u32(), span, ExprKind::IfExpr { cond: Box::new(c), then, else_: value(taken) });
    }
    let mut stmts = Vec::new();
    let taken = materialize(cx, taken, &mut stmts, "__taken");
    let bodies: Vec<ExprId> = chain.links.iter().map(|l| l.then).chain([last]).collect();
    every(lw, cx, &bodies, taken, ty, stmts, span)
}

/// The `match~` `e` of the type `ty`, in one block: the choice of its arm
/// among all ([`choose`]), then every arm body ([`every`]).
pub(crate) fn tilde_match(lw: &mut Lowerer, cx: &mut FnCx, e: ExprId, ty: Ty) -> R<Expr> {
    let span = cx.ast.expr(e).span;
    let AK::Match { arms, .. } = &cx.ast.expr(e).kind else { return Err(internal(span, "no `match~`")) };
    let (s, state) = here(cx, span)?;
    let mut stmts = Vec::new();
    let all = Pick { upto: arms.len(), eval: arms.len(), write: false };
    let taken = choose(lw, cx, e, all, s, &state, &mut stmts)?;
    let bodies: Vec<ExprId> = arms.iter().map(|a| a.body).collect();
    every(lw, cx, &bodies, taken, ty, stmts, span)
}

fn value(v: Expr) -> Block {
    Block { stmts: Vec::new(), value: Some(Box::new(v)) }
}

/// The stage of the function lowered and the state of its innermost scope.
fn here(cx: &FnCx, span: Span) -> R<(ClockStage, Expr)> {
    let f = cx.flow.as_ref().ok_or_else(|| internal(span, "a branching outside a flow"))?;
    let scope = f.scopes.last().ok_or_else(|| internal(span, "a branching outside the state"))?;
    Ok((f.phase.stage(), scope.state.clone()))
}

/// After `stmts`, every one of `bodies` in the order of the text, each in a
/// temporary (R-14: the state in each goes on); the value of the one of the
/// number `taken`, of the type `ty` (the last of a number past them).
fn every(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    bodies: &[ExprId],
    taken: Expr,
    ty: Ty,
    mut stmts: Vec<Stmt>,
    span: Span,
) -> R<Expr> {
    let mut values = Vec::with_capacity(bodies.len());
    for &x in bodies {
        let b = lower_block_expr(lw, cx, x)?;
        if ty == Ty::Unit {
            push_expr_stmt(Expr::new(Ty::Unit, span, ExprKind::Block(drop_value(b))), &mut stmts);
            continue;
        }
        let Some(t) = b.value.as_ref().map(|v| v.ty.clone()) else {
            return Err(internal(cx.ast.expr(x).span, "a branch of an `if~` or `match~` with no value"));
        };
        values.push(materialize(cx, Expr::new(t, span, ExprKind::Block(b)), &mut stmts, "__branch"));
    }
    let mut chosen = values.pop();
    for (k, v) in values.into_iter().enumerate().rev() {
        let cond = Box::new(cmp(CmpOp::Eq, taken.clone(), u32_lit(span, k as u32)));
        let else_ = chosen.map(value).unwrap_or_default();
        chosen = Some(Expr::new(ty.clone(), span, ExprKind::IfExpr { cond, then: value(v), else_ }));
    }
    Ok(Expr::new(ty, span, ExprKind::Block(Block { stmts, value: chosen.map(Box::new) })))
}

/// What a [`choose`] looks at: the patterns of the arms before `upto`, the
/// guards of those before `eval` (whether each is taken), and with `write`
/// the fields of their guards.
#[derive(Debug, Clone, Copy)]
pub(super) struct Pick {
    pub(super) upto: usize,
    pub(super) eval: usize,
    pub(super) write: bool,
}

/// The arm of the `match~` `m` taken at the stage `s` in the scope of
/// `state`, into `out` (S-1094: its scrutinee, then the patterns and guards
/// from the first to the one taken); its number in a local, that of the
/// arms for none. With `pick.write` the fields of `s` of the scrutinee and
/// of each guard are written before them, a guard's under the arms before
/// not taken and its pattern (§11.3, [`writes`]). Then the place of each
/// binding of an arm before `pick.eval` that has one in the function: the
/// value of its pattern of the arm taken, else the default of its type
/// (§11.5); those arms are chosen in the scope.
pub(super) fn choose(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    m: ExprId,
    pick: Pick,
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<Expr> {
    let (ast, span) = (cx.ast, cx.ast.expr(m).span);
    let info = cx.flow.as_ref().ok_or_else(|| internal(span, "a `match~` outside a flow"))?.info;
    let (AK::Match { scrutinee, arms, .. }, Some(t)) = (&ast.expr(m).kind, info.tilde_matches.get(&m)) else {
        return Err(internal(span, "a `match~` the plan did not record"));
    };
    if pick.write {
        writes(lw, cx, info, *scrutinee, s, state, out)?;
    }
    let v = cond_value(lw, cx, info, *scrutinee, s, state)?;
    let place = materialize(cx, v, out, "__match");
    let none = u32_lit(span, arms.len() as u32);
    let taken = cx.temp("__arm", Ty::u32());
    out.push(stmt(span, StmtKind::Let(taken, none.clone())));
    let taken = local_expr(cx, taken, span);
    let mut binds = vec![false; arms.len()];
    for (i, arm) in arms.iter().enumerate().take(pick.upto) {
        // In the guard, a binding is the value of the pattern, not its place.
        let flow = cx.flow.as_mut().unwrap();
        let held: Vec<_> = t.arms[i].iter().filter_map(|b| flow.local_override.remove_entry(&b.0)).collect();
        let tested = test_arm(lw, cx, arm, (i, &taken, &place), pick, (s, state));
        cx.flow.as_mut().unwrap().local_override.extend(held);
        let (test, then);
        (test, binds[i], then) = tested?;
        let open = cmp(CmpOp::Eq, taken.clone(), none.clone());
        let cond = match test {
            None => open,
            Some(t) => {
                Expr::new(Ty::Bool, span, ExprKind::Logic { op: LogicOp::And, lhs: Box::new(open), rhs: Box::new(t) })
            }
        };
        out.push(stmt(span, StmtKind::If(cond, then, Block::default())));
    }
    for (i, (arm, bound)) in arms.iter().zip(&t.arms).enumerate().take(pick.eval) {
        let overrides = &cx.flow.as_ref().unwrap().local_override;
        let slots: Vec<(LocalId, Expr)> =
            bound.iter().filter_map(|b| overrides.get(&b.0).map(|p| (LocalId(b.0), p.clone()))).collect();
        if slots.is_empty() || !binds[i] {
            continue;
        }
        let (mut then, mut else_) = (Vec::new(), Vec::new());
        bind_read(lw, cx, arm.pat, &place, &mut then)?;
        for (b, slot) in slots {
            let ty = cx.locals[b.0 as usize].ty.clone();
            assign(&mut then, &slot, local_expr(cx, b, span))?;
            assign(&mut else_, &slot, crate::lower::derived::default_value(lw, &ty, span)?)?;
        }
        let is = cmp(CmpOp::Eq, taken.clone(), u32_lit(span, i as u32));
        out.push(stmt(span, StmtKind::If(is, Block { stmts: then, value: None }, Block { stmts: else_, value: None })));
    }
    if let Some(scope) = cx.flow.as_mut().unwrap().scopes.last_mut() {
        scope.chosen.extend((0..pick.eval).map(|i| (m, i)));
    }
    Ok(taken)
}

/// The test of the pattern of the arm `i` against `place` (none: always),
/// whether it binds ([`arm_test`]), and what its arm does where it holds:
/// its bindings, the fields of `s` of
/// its guard (with `pick.write`), and, of an arm before `pick.eval`, its
/// number into `taken` where its guard holds.
fn test_arm(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    arm: &MatchArm,
    (i, taken, place): (usize, &Expr, &Expr),
    pick: Pick,
    (s, state): (ClockStage, &Expr),
) -> R<(Option<Expr>, bool, Block)> {
    let info = cx.flow.as_ref().unwrap().info;
    let span = cx.ast.pat(arm.pat).span;
    let (test, binds) = arm_test(lw, cx, arm.pat, place)?;
    let mut then = Vec::new();
    if binds && arm.guard.is_some() {
        bind_read(lw, cx, arm.pat, place, &mut then)?;
    }
    if let (true, Some(g)) = (pick.write, arm.guard) {
        writes(lw, cx, info, g, s, state, &mut then)?;
    }
    if i < pick.eval {
        let set = vec![stmt(span, StmtKind::Assign(place_of(taken)?, u32_lit(span, i as u32)))];
        match arm.guard {
            Some(g) => {
                let c = cond_value(lw, cx, info, g, s, state)?;
                then.push(stmt(span, StmtKind::If(c, Block { stmts: set, value: None }, Block::default())));
            }
            None => then.extend(set),
        }
    }
    Ok((test, binds, Block { stmts: then, value: None }))
}

/// The bindings of `pat` against `place` into `out`, each then read for
/// nothing (a use, as of S-288): a guard or the places read some only.
fn bind_read(lw: &mut Lowerer, cx: &mut FnCx, pat: PatId, place: &Expr, out: &mut Vec<Stmt>) -> R<()> {
    let from = out.len();
    pat_bind(lw, cx, pat, place, out)?;
    let bound: Vec<_> = out[from..]
        .iter()
        .filter_map(|s| if let StmtKind::Let(l, _) = s.kind { Some((l, s.span)) } else { None })
        .collect();
    out.extend(bound.into_iter().map(|(l, at)| stmt(at, StmtKind::Expr(local_expr(cx, l, at)))));
    Ok(())
}

/// The arms `arms` of the `match~`s around a node (outer first), chosen at
/// the stage `s` in the scope of `state` before its arguments of `s` are
/// lowered ([`choose`]): each that has a binding with a place in the
/// function and was not chosen in the scope or one around it (S-1131).
pub(super) fn choose_arms(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    arms: &[(ExprId, u32)],
    s: ClockStage,
    state: &Expr,
    out: &mut Vec<Stmt>,
) -> R<()> {
    for &(m, a) in arms {
        let flow = cx.flow.as_ref().unwrap();
        let Some(t) = flow.info.tilde_matches.get(&m) else {
            return Err(internal(cx.ast.expr(m).span, "a `match~` the plan did not record"));
        };
        let a = a as usize;
        let chosen = flow.scopes.last().is_some_and(|x| x.chosen.contains(&(m, a)));
        if chosen || !t.arms[a].iter().any(|b| flow.local_override.contains_key(&b.0)) {
            continue;
        }
        choose(lw, cx, m, Pick { upto: a + 1, eval: a + 1, write: false }, s, state, out)?;
    }
    Ok(())
}
