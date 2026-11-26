//! The field reads of the bindings of arms (§11.3, S-1247 (1)): "フィールド・組の要素の読みは、条件によらず、守りを付けずに刻みごとに読む（腕の束縛（`match~` のガードの中の束縛も）を根にする読みは、
//! 外の条件によらず、その腕のパターンが合う刻みに読む）". A read of a field of a binding of an arm of a `match` (the binding of an arm of a `match~` read in a guard, too) is a field of the type of the read, like the read of a field of a name
//! (S-1197, `hoist::free`), and it is written at the ticks of the object at which the pattern of its arm matches, whatever stands round the `match` (a condition, an arm before, a guard), and read where it is reached. A `match` whose
//! object is a binding (or a field of one) of an arm goes on from the pattern of that arm: the chain of patterns from the outside. Before the first tick and after a `reset_if~` it holds the default of the type of the read, not
//! the field of the default of the object (`events::event_part`: such a read is no part under a guard, so it has its default). The binding of an arm of a `match~` read in its body is not here (it has a place of its own, S-1131, and `walk` reads it).

use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{ExprId, ExprKind};

use super::expr::{Frame, LOW_STACK, Stop};
use super::flow::{Clock, Known};
use super::hoist::{field_of, seen_of, stage_of, walk, with_index};
use super::sema_view::Body;
use super::value::Value;

/// The local that `e`, a name or a field or an element of one (and so on), starts at, past parentheses.
fn chain_root(body: &Body, e: ExprId) -> Option<LocalId> {
    let e = body.ast.without_parens(e);
    let name = if body.names(e) { e } else { field_of(body, e)? };
    match body.target(name) {
        Ok(Target::Local(l)) => Some(*l),
        _ => None,
    }
}

/// Is `e`, a read of a field of the local `l` that is bound within `root`, the read of a binding of an arm that is written at the ticks where the pattern matches (not one of a block's `let`, and not one in the body of an arm of a `match~`)?
pub(super) fn arm_rooted(body: &Body, root: ExprId, e: ExprId, l: LocalId) -> bool {
    let at = body.ast.expr(e).span;
    let within = |x: ExprId| {
        let s = body.ast.expr(x).span;
        s.file == at.file && s.start <= at.start && at.end <= s.end
    };
    fn binder(body: &Body, x: ExprId, l: LocalId, within: &dyn Fn(ExprId) -> bool) -> Option<bool> {
        if let ExprKind::Match { arms, tilde, .. } = &body.ast.expr(x).kind {
            for arm in arms {
                if body.pat_locals(arm.pat).is_ok_and(|ls| ls.contains(&l)) {
                    return Some(tilde.is_none() || arm.guard.is_some_and(within));
                }
            }
        }
        body.ast.sub_exprs(x).into_iter().find_map(|y| binder(body, y, l, within))
    }
    binder(body, root, l, &within).unwrap_or(false)
}

/// The `match` `m` that `free` meets: when its object is a name (or a field of one) that the tick `here` made, its arms are read from the value of the object.
pub(super) fn from_free(
    f: &mut Frame,
    known: &Known,
    (root, top): (ExprId, ExprId),
    m: ExprId,
    here: Clock,
) -> Result<(), Stop> {
    let body = f.body;
    let ExprKind::Match { scrutinee, .. } = &body.ast.expr(m).kind else { return Ok(()) };
    let stop = |fault| Stop { fault, at: body.ast.expr(m).span };
    // An object that is computed is a part that `walk` makes where the `match` is reached (`descend`), and one that an arm binds is read by that arm (`scan`, or `walk` for the body of a `match~`).
    let object = chain_root(&body, *scrutinee).filter(|l| known.contains_key(l) && !body.bound_within(*l, top));
    if object.is_none()
        || !matches!(here, Clock::Event(_))
        || stage_of(&body, known, root, *scrutinee).map_err(stop)? != here
    {
        return Ok(());
    }
    let v = f.eval(*scrutinee)?;
    arm_reads(f, known, root, m, &v, here)
}

/// The arms of the `match` `m`, whose object has the value `v` at the tick `here`: each whose pattern matches writes the reads of its bindings (the guard, and the body of a `match` but not of a `match~`), whatever arm is taken.
pub(super) fn arm_reads(
    f: &mut Frame,
    known: &Known,
    root: ExprId,
    m: ExprId,
    v: &Value,
    here: Clock,
) -> Result<(), Stop> {
    let body = f.body;
    let ExprKind::Match { scrutinee, arms, tilde } = &body.ast.expr(m).kind else { return Ok(()) };
    let span = body.ast.expr(m).span;
    let stop = |fault| Stop { fault, at: span };
    // The events only: a tick has no read of a slower value in a faster expression (E0815), so a read of its own tick is where it is reached.
    if !matches!(here, Clock::Event(_)) {
        return Ok(());
    }
    if f.low_stack() {
        return Err(stop(LOW_STACK));
    }
    let sc = seen_of(&body, known, root, *scrutinee).map_err(stop)?;
    if sc.stage != here {
        return Ok(());
    }
    let ty = body.ty(*scrutinee).map_err(stop)?;
    for arm in arms {
        let own = body.pat_locals(arm.pat).map_err(stop)?;
        if own.is_empty() || !f.arm(arm.pat, v, ty, None, span)? {
            continue;
        }
        let mut inner = known.clone();
        inner.extend(own.iter().map(|l| (*l, sc)));
        for x in arm.guard.into_iter().chain(tilde.is_none().then_some(arm.body)) {
            scan(f, &inner, root, x, &own, here)?;
        }
    }
    Ok(())
}

/// The reads in `e` of a field of one of `roots` (the bindings of an arm that is bound now): each is made and kept, and a `match` in it whose object is one of them goes on from its own arms.
fn scan(f: &mut Frame, known: &Known, root: ExprId, e: ExprId, roots: &[LocalId], here: Clock) -> Result<(), Stop> {
    let body = f.body;
    let stop = |fault| Stop { fault, at: body.ast.expr(e).span };
    if f.low_stack() {
        return Err(stop(LOW_STACK));
    }
    if field_of(&body, e).is_some_and(|n| matches!(body.target(n), Ok(Target::Local(l)) if roots.contains(l))) {
        return walk(f, known, root, e, here, Clock::Const);
    }
    if let ExprKind::Par { var, body: inner, .. } = &body.ast.expr(e).kind {
        let inside = with_index(&body, known, var.span).map_err(stop)?;
        return f.replicate(e, |_: &()| 0, |f| scan(f, &inside, root, *inner, roots, here)).map(drop);
    }
    for x in body.ast.sub_exprs(e) {
        scan(f, known, root, x, roots, here)?;
    }
    if let ExprKind::Match { scrutinee, .. } = &body.ast.expr(e).kind {
        if chain_root(&body, *scrutinee).is_some_and(|l| roots.contains(&l)) {
            let v = f.eval(*scrutinee)?;
            arm_reads(f, known, root, e, &v, here)?;
        }
    }
    Ok(())
}
