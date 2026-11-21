//! Hoisting (§11.3): "コンパイラは各式を、部分式も含めて、その値と評価されるかどうかが決まる最も遅い段で評価する". The `let`s and the output
//! of a stage are made in `flow::stage`; this is the other half: the parts of a `let` (or of the output) that are of a slower clock than the
//! `let` itself, which a stage before the one of the `let` evaluates, once, whether the value is read or not. The part is the largest one of
//! the stage that is Copy (S-1046 (a): a part that is not Copy is read where it is written, and the Copy parts in it are hoisted by
//! the same rule; Copy is the checker's judgement of §4.6), and it is not a name, a literal, `sample_rate()` or `sample_tick()` (they have a
//! place already, or none, §11.3). The value is kept, so the `let` reads it where it is written and does not make it again (`Frame::hoisted`;
//! the field of the state of §11.6).
//!
//! The stage a part is made at is [`stage_of`] (S-1196: the stage its values decide, `at` seen through, when they are of the parameter kinds alone), and the
//! clock a condition is decided by is its clock with `at` counted (S-1166: `(d != 0) at sample`, and the name of `let g = (d != 0) at sample`, are `sample`).
//!
//! The walk goes down with a *guard*: the fastest of the clocks of the conditions on the way (S-1157 (D'): the condition of an `if`, the object
//! of a `match` and the patterns and guards of the arms up to the one, the left side of `&&` / `||`). The stage that makes a part is the
//! fastest of its clock and its guard, and a constant-clock part (a `panic("…")`) is made by the stage of its guard when it has one, else it
//! stays where it is written (W9-03 makes it at compile time, E0419). A condition that a stage decides (its stage is not after it) is
//! evaluated here, and only the branch, the arm (its bindings made) or the right side that it takes is walked, so a part that the condition
//! does not take is not made (a constant condition is decided at a stage only when a part that the stage makes is under it, as the Core
//! does; else it is evaluated where it is reached); a condition of a later stage (`sample`, or a value that is not Copy, which the reader evaluates) stops the walk:
//! what is under it is evaluated where it is reached. An arm binding has the clock of the object of its `match`. The walk goes into the
//! operands, the arguments, the elements and the fields, the branches and the block expressions (a part that reads a name the block binds
//! is left where it is), and into the body of a `par~` once for each replica, with its index bound and clocked `init` (§11.5: the index is a
//! value of `init`; S-1140, provisional: each replica has a value of its own for each part of the body, kept by the replicas it is in).
//! The body is walked as the rest is, by the same guard and stages, and only when it has a part for the stage (a `par~` of a million replicas
//! that reads `x` only is not walked at `init`); a `par~` that is a part of the stage as a whole is made as a whole and not walked. A part that
//! reads a `^name` is left where it is (a feedback has the clock of the reader, §11.3). The order inside a stage is the order the parts are written (S-1159, provisional): `flow::stage` walks the `let`s in order and
//! each `let` from the left.

use onsa_diag::Span;
use onsa_sema::Target;
use onsa_syntax::ast::{BinOp, CallKind, ExprId, ExprKind, StmtKind};

use super::expr::{Frame, LOW_STACK, Stop};
use super::flow::{Clock, Known, Seen, clock_of};
use super::scalar::Fault;
use super::sema_view::{Body, Stage};

/// What has a place of its own or none, so it is not hoisted: a literal, a name, `sample_rate()` and `sample_tick()`, and a parenthesis
/// or an `at` over one.
fn atom(body: &Body, e: ExprId) -> bool {
    let ast = body.ast;
    match &ast.expr(e).kind {
        ExprKind::Lit(_) | ExprKind::Path(_) => true,
        ExprKind::Field { .. } => body.names(e),
        ExprKind::Paren(x) | ExprKind::At { expr: x, .. } => atom(body, *x),
        ExprKind::Unary { .. } => ast.negated_literal(e).is_some(),
        ExprKind::Call { .. } => body.time_call(e),
        _ => false,
    }
}

fn feedback(body: &Body, e: ExprId) -> bool {
    matches!(body.ast.expr(e).kind, ExprKind::Feedback(_))
        || body.ast.sub_exprs(e).into_iter().any(|x| feedback(body, x))
}

/// `panic("…")`: its value is of any type, so it is kept whatever the table says of it.
fn is_panic(body: &Body, e: ExprId) -> bool {
    matches!(body.ast.expr(e).kind, ExprKind::Call { .. }) && matches!(body.target(e), Ok(Target::Panic))
}

/// Does `x` (in the part `part`) read a local that has no clock in `known` and that `part` does not bind (a name of a block expression
/// that the walk has not made)? Such a part cannot be made before its own stage.
fn reads_unknown(body: &Body, known: &Known, part: ExprId, x: ExprId) -> bool {
    match &body.ast.expr(x).kind {
        ExprKind::Path(_) | ExprKind::Field { .. } if body.names(x) => {
            matches!(body.target(x), Ok(Target::Local(l)) if !known.contains_key(l) && !body.bound_within(*l, part))
        }
        _ => body.ast.sub_exprs(x).into_iter().any(|y| reads_unknown(body, known, part, y)),
    }
}

/// The stage `e` is made in (§11.3, S-1196): that of its values when they are of the parameter kinds alone (a constant, `init`, `block`),
/// whatever clock an `at` in it gives (`at` and a parenthesis are seen through, and so are the names of a `let` of such a value); the
/// clock of the expression when it reads a value of a tick (a delay, the output of an instance, a `sample` input: `(lf at sample) * 2.0`
/// is of `sample`). A conditional form (`if`, `match`, `&&` / `||`, and `if~` / `match~`) is made at the stage of the clock of its conditions
/// too, `at` counted ("条件に `at` を書いた式は、全体がパラメータの種類の値でも、条件が決まる段で選ぶ"), but a condition is made at its own stage:
/// `d != 0` of `(d != 0) at sample` is a part of `block`, and what `sample` decides is the choice.
pub(super) fn stage_of(body: &Body, known: &Known, root: ExprId, e: ExprId) -> Result<Clock, Fault> {
    use ExprKind as K;
    match &body.ast.expr(e).kind {
        // An instance, a delay and the builtin clocks of a flow: a call that has the clock of what it makes (as `clock_of` has it).
        K::Call { kind, .. } if matches!(kind, CallKind::Flow) || body.time_call(e) => clock_of(body, known, root, e),
        K::Par { var, body: inner, .. } => {
            let inside = with_index(body, known, var.span)?;
            stage_of(body, &inside, root, *inner)
        }
        K::At { expr, .. } => match stage_of(body, known, root, *expr)? {
            Clock::Sample => clock_of(body, known, root, e),
            parameter => Ok(parameter),
        },
        K::Path(_) | K::Field { .. } if body.names(e) => match body.target(e)? {
            Target::Local(l) => match known.get(l) {
                Some(seen) => Ok(seen.stage),
                None if body.bound_within(*l, root) => Ok(Clock::Const),
                None => Err(Fault::Internal("a local with no clock")),
            },
            _ => Ok(Clock::Const),
        },
        _ => {
            let mut stage = Clock::Const;
            for x in body.ast.sub_exprs(e) {
                stage = stage.max(stage_of(body, known, root, x)?);
            }
            for c in conditions(body, e) {
                stage = stage.max(clock_of(body, known, root, c)?);
            }
            Ok(stage)
        }
    }
}

/// The conditions of a conditional form (those that choose a position, and the first one of a chain of `if~`): the condition of an `if`,
/// the conditions of the chain of an `if~`, the left side of `&&` / `||`, the object and the guards of a `match` / `match~`.
fn conditions(body: &Body, e: ExprId) -> Vec<ExprId> {
    use ExprKind as K;
    match &body.ast.expr(e).kind {
        K::If { cond, tilde: None, .. } => vec![*cond],
        K::If { tilde: Some(_), .. } => {
            let mut out = Vec::new();
            let mut at = e;
            while let K::If { cond, else_, .. } = &body.ast.expr(at).kind {
                out.push(*cond);
                match else_ {
                    Some(rest) if matches!(body.ast.expr(*rest).kind, K::If { .. }) => at = *rest,
                    _ => break,
                }
            }
            out
        }
        K::Binary { op: BinOp::And | BinOp::Or, lhs, .. } => vec![*lhs],
        K::Match { scrutinee, arms, .. } => {
            std::iter::once(*scrutinee).chain(arms.iter().filter_map(|a| a.guard)).collect()
        }
        _ => Vec::new(),
    }
}

/// The clock a condition `c` is decided by: the clock of the expression it is, `at` counted (S-1166: `(d != 0) at sample`, and the name of
/// a `let g = (d != 0) at sample`, are decided at `sample`; §11.3: "条件が決まる段は、その条件を評価する段と、条件の式のクロック（`at` で
/// 付けたクロックを含む）の段のうち速い方"), and the stage of the reader (`sample`) for a value that is not Copy, which is not hoisted
/// (S-1046 (a)).
fn cond_clock(body: &Body, known: &Known, root: ExprId, c: ExprId) -> Result<Clock, Fault> {
    if !body.view.is_copy(body.ty_id(c)?) {
        return Ok(Clock::Sample);
    }
    clock_of(body, known, root, c)
}

/// The guard under a condition of the clock `cc`: the slower of the two. A constant condition is decided before `init` (S-888 (c'): W9-03
/// evaluates it at compile time and takes its branch as if `constexpr`, whose `block` part is then made at `block`), so it adds nothing.
fn after(guard: Clock, cc: Clock) -> Clock {
    guard.max(cc)
}

/// Does this stage decide the condition of `e` (an `if`, `&&` / `||` or `match`; the clock `cc`, the guard `g` counted in)? One that is not
/// after the stage is decided here. A constant condition is decided before `init` (S-888 (c')), but this evaluator reads its value where a
/// stage needs it: when a part that this stage makes is under it, in any branch, arm or right side (as the `has_writes` of the Core, which
/// does not look at which one is taken), and else it is evaluated where it is reached. Until W9-03 takes it at compile time (E0419 when it
/// panics), so a constant condition that panics does so at the stage where such a part is made, else where it is read.
fn decides(
    body: &Body,
    known: &Known,
    root: ExprId,
    e: ExprId,
    (cc, g): (Clock, Clock),
    here: Clock,
) -> Result<bool, Fault> {
    if g > here {
        return Ok(false);
    }
    if cc != Clock::Const {
        return Ok(true);
    }
    for (x, k, kg) in kids(body, known, root, e, g)?.into_iter().skip(1) {
        if makes(body, &k, root, x, here, kg)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Does the stage `here` make a part of `e` (or of the parts in it)? The walk of [`walk`] without the values and the conditions' truth.
fn makes(body: &Body, known: &Known, root: ExprId, e: ExprId, here: Clock, guard: Clock) -> Result<bool, Fault> {
    let clock = stage_of(body, known, root, e)?;
    if clock == Clock::Const && guard == Clock::Const {
        return Ok(false);
    }
    let made = clock.max(guard);
    if made < here {
        return Ok(false);
    }
    if made == here && kept(body, known, e)? {
        return Ok(true);
    }
    for (x, k, g) in kids(body, known, root, e, guard)? {
        if makes(body, &k, root, x, here, g)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The operands that are in a position that is not a condition: the parts `walk` goes on into (the conditional forms and the block
/// expression are walked by themselves; `if`, `if~`, `match` and `match~` are not here).
fn operands(body: &Body, e: ExprId) -> Vec<ExprId> {
    use ExprKind as K;
    let ast = body.ast;
    match &ast.expr(e).kind {
        K::Paren(x) | K::At { expr: x, .. } | K::Unary { expr: x, .. } | K::Cast { expr: x, .. } => vec![*x],
        K::TupleIndex { base, .. } => vec![*base],
        K::Field { base, .. } if !body.names(e) => vec![*base],
        K::Binary { op: BinOp::And | BinOp::Or, lhs, .. } => vec![*lhs],
        K::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        K::Index { base, index } => vec![*base, *index],
        K::Tuple(xs) | K::Array(xs) => xs.clone(),
        K::Repeat { elem, len } => vec![*elem, *len],
        K::Struct { fields, .. } => fields.iter().map(|(_, x)| *x).collect(),
        K::Call { callee, args, .. } => {
            let mut out = Vec::new();
            if let K::Field { base, .. } = &ast.expr(*callee).kind {
                // A method call has a receiver that is a value; `util.lp~(x)` has a module (no type) before the name.
                if !body.names(*callee) && body.ty_id(*base).is_ok() {
                    out.push(*base);
                }
            }
            out.extend(args.iter().map(|a| a.expr));
            out
        }
        _ => Vec::new(),
    }
}

/// Whether a part that a stage makes is kept: Copy (or a `panic`), and none of an atom, a feedback and a part that reads what is not made.
fn kept(body: &Body, known: &Known, e: ExprId) -> Result<bool, Fault> {
    let copy = body.view.is_copy(body.ty_id(e)?) || is_panic(body, e);
    Ok(copy && !atom(body, e) && !feedback(body, e) && !reads_unknown(body, known, e, e))
}

/// The clocks of the names in scope in the body of a `par~` whose variable is written at `at`: the index is of `init` (§11.5).
fn with_index(body: &Body, known: &Known, at: Span) -> Result<Known, Fault> {
    let mut inside = known.clone();
    inside.insert(body.par_var(at)?, Seen::both(Clock::Init));
    Ok(inside)
}

/// The chain of an `if~` (`tilde` is on the head only; the later `if`s of `else if` are in it): the `(condition, branch)` of each link
/// in the order written and the `else`. The condition of a link is of the select side (the later ones only until a true one, S-1094
/// (1)); the branches are all evaluated, so they are not under a condition (§11.3).
fn tilde_chain(body: &Body, head: ExprId) -> Result<(Vec<(ExprId, ExprId)>, ExprId), Fault> {
    let (ast, mut at, mut links) = (body.ast, head, Vec::new());
    loop {
        let ExprKind::If { cond, then, else_, .. } = &ast.expr(at).kind else {
            return Err(Fault::Internal("not an `if~`"));
        };
        links.push((*cond, *then));
        let Some(rest) = *else_ else { return Err(Fault::Internal("an `if~` with no `else`")) };
        if !matches!(ast.expr(rest).kind, ExprKind::If { .. }) {
            return Ok((links, rest));
        }
        at = rest;
    }
}

/// A child of an expression with the clocks of the names in scope there and the guard on the way to it.
type Kid = (ExprId, Known, Clock);

/// The children of `e` with the guard on the way to each and the clocks of the names that are in scope there (an arm binding has the
/// clock of the object): the operands, and for a conditional form its branches, arms and right side under the conditions up to them.
/// This is the walk of [`walk`] without the values, for the stage a place is in.
fn kids(body: &Body, known: &Known, root: ExprId, e: ExprId, guard: Clock) -> Result<Vec<Kid>, Fault> {
    use ExprKind as K;
    let own = |xs: Vec<ExprId>| xs.into_iter().map(|x| (x, known.clone(), guard)).collect::<Vec<_>>();
    Ok(match &body.ast.expr(e).kind {
        K::If { cond, then, else_, tilde: None } => {
            let g = after(guard, cond_clock(body, known, root, *cond)?);
            let mut out = own(vec![*cond]);
            out.extend([*then].into_iter().chain(*else_).map(|x| (x, known.clone(), g)));
            out
        }
        K::If { tilde: Some(_), .. } => {
            // The first condition and every branch are not under a condition; each later condition is under those before it.
            let (links, last) = tilde_chain(body, e)?;
            let (mut out, mut g) = (Vec::new(), guard);
            for (c, then) in links {
                out.push((c, known.clone(), g));
                out.push((then, known.clone(), guard));
                g = after(g, cond_clock(body, known, root, c)?);
            }
            out.push((last, known.clone(), guard));
            out
        }
        K::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
            let g = after(guard, cond_clock(body, known, root, *lhs)?);
            vec![(*lhs, known.clone(), guard), (*rhs, known.clone(), g)]
        }
        K::Match { scrutinee, arms, tilde: None } => {
            let sc = seen_of(body, known, root, *scrutinee)?;
            let mut acc = after(guard, cond_clock(body, known, root, *scrutinee)?);
            let mut out = own(vec![*scrutinee]);
            for arm in arms {
                let mut inner = known.clone();
                for l in body.pat_locals(arm.pat)? {
                    inner.insert(l, sc);
                }
                let mut at_body = acc;
                if let Some(g) = arm.guard {
                    out.push((g, inner.clone(), acc));
                    at_body = after(acc, cond_clock(body, &inner, root, g)?);
                }
                out.push((arm.body, inner, at_body));
                acc = at_body;
            }
            out
        }
        K::Match { scrutinee, arms, tilde: Some(_) } => {
            // The side that selects goes first, under the object and the guards before it; the bodies are not under a condition (the arms of a
            // `match~` are not condition positions, §11.3). The guard sees the clock of the object; the body binds the clock of the object
            // and of the guards from the first arm to its own, the fastest of them (S-1131).
            // (A binding is of the clock the choice is decided by, here: `at` in the object or a guard makes the binding of that clock, the
            // stage included, which is more than S-1196 asks for a `match~`; no case reads the difference.)
            let sc = seen_of(body, known, root, *scrutinee)?;
            let mut acc = after(guard, cond_clock(body, known, root, *scrutinee)?);
            let (mut out, mut bound) = (own(vec![*scrutinee]), clock_of(body, known, root, *scrutinee)?);
            for arm in arms {
                let locals = body.pat_locals(arm.pat)?;
                if let Some(g) = arm.guard {
                    let mut seen = known.clone();
                    seen.extend(locals.iter().map(|l| (*l, sc)));
                    out.push((g, seen.clone(), acc));
                    let gc = cond_clock(body, &seen, root, g)?;
                    (acc, bound) = (after(acc, gc), bound.max(gc));
                }
                let mut inner = known.clone();
                inner.extend(locals.iter().map(|l| (*l, Seen::both(bound))));
                out.push((arm.body, inner, guard));
            }
            out
        }
        K::Block(b) => {
            let inits = b.stmts.iter().filter_map(|s| match &body.ast.stmt(*s).kind {
                StmtKind::Let { init, .. } => Some(*init),
                _ => None,
            });
            own(inits.chain(b.tail).collect())
        }
        K::Par { var, body: inner, .. } => vec![(*inner, with_index(body, known, var.span)?, guard)],
        _ => own(operands(body, e)),
    })
}

/// The clock of the part of `root` (a `let` of the body; `known` as in [`pre`]) that holds `at` and that the stage of its clock
/// makes, as [`pre`] chooses it: the innermost, as a part of `init` in a part of `block` is made at `init`, and a part under a condition of
/// `block` is made at `block` whatever its own clock is. `None` when no part of `init` or `block` holds `at` (it is made with its `let`).
pub(super) fn part_clock(body: &Body, known: &Known, root: ExprId, at: Span) -> Result<Option<Clock>, Fault> {
    let holds = |x: ExprId| {
        let s = body.ast.expr(x).span;
        s.file == at.file && s.start <= at.start && at.end <= s.end
    };
    let (mut e, mut known, mut guard, mut found) = (root, known.clone(), Clock::Const, None);
    loop {
        let clock = stage_of(body, &known, root, e)?;
        if clock == Clock::Const && guard == Clock::Const {
            return Ok(found);
        }
        let made = clock.max(guard);
        if matches!(made, Clock::Init | Clock::Block) && kept(body, &known, e)? {
            found = Some(made);
        }
        match kids(body, &known, root, e, guard)?.into_iter().find(|(x, ..)| holds(*x)) {
            Some((x, k, g)) if g < Clock::Sample => (e, known, guard) = (x, k, g),
            _ => return Ok(found),
        }
    }
}

/// The parts of `e` (a `let` of the body, `root` its value; `known` the clocks of the locals before it) that the stage `at` makes, in the
/// order they are written: each is evaluated and kept in `f.hoisted`, and a panic of one is the panic of the stage.
pub(super) fn pre(f: &mut Frame, known: &Known, root: ExprId, e: ExprId, at: Stage) -> Result<(), Stop> {
    walk(f, known, root, e, Clock::from(at), Clock::Const)
}

fn walk(f: &mut Frame, known: &Known, root: ExprId, e: ExprId, here: Clock, guard: Clock) -> Result<(), Stop> {
    let body = f.body;
    let span = body.ast.expr(e).span;
    let stop = |fault| Stop { fault, at: span };
    if f.low_stack() {
        return Err(stop(LOW_STACK));
    }
    let clock = stage_of(&body, known, root, e).map_err(stop)?;
    if clock == Clock::Const && guard == Clock::Const {
        // A constant: where it is written (W9-03), and no part of it is of another stage.
        return Ok(());
    }
    let made = clock.max(guard);
    if made < here {
        // Made by a stage before: not again.
        return Ok(());
    }
    if made == here && kept(&body, known, e).map_err(stop)? {
        // The value of the call before is stale: made again by this stage (the parts it holds that a slower stage kept stay).
        let replicas = f.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default();
        f.hoisted.entry(e).or_default().remove(&replicas);
        let v = f.eval(e)?;
        f.hoisted.entry(e).or_default().insert(replicas, v);
        return Ok(());
    }
    descend(f, known, root, e, here, guard)
}

/// The parts inside `e`, which is not made by this stage as a whole: the conditions this stage decides are evaluated and the branch, arm or
/// right side they take is walked under them.
fn descend(f: &mut Frame, known: &Known, root: ExprId, e: ExprId, here: Clock, guard: Clock) -> Result<(), Stop> {
    use ExprKind as K;
    let body = f.body;
    let span = body.ast.expr(e).span;
    let stop = |fault| Stop { fault, at: span };
    match &body.ast.expr(e).kind {
        K::If { cond, then, else_, tilde: None } => {
            walk(f, known, root, *cond, here, guard)?;
            let cc = cond_clock(&body, known, root, *cond).map_err(stop)?;
            let g = guard.max(cc);
            if decides(&body, known, root, e, (cc, g), here).map_err(stop)? {
                let taken = if f.truth(*cond, span)? { Some(*then) } else { *else_ };
                if let Some(b) = taken {
                    walk(f, known, root, b, here, g)?;
                }
            }
            Ok(())
        }
        K::If { tilde: Some(_), .. } => {
            // The side that selects goes first, from the top: a condition is walked under those before it, and the walk of the
            // conditions ends at the first true one or at one that a later stage decides (what is under it is evaluated where
            // it is reached, as for a plain `if`). Then every branch, in the order written, not under any condition.
            let (links, last) = tilde_chain(&body, e).map_err(stop)?;
            let mut g = guard;
            for (n, (c, _)) in links.iter().enumerate() {
                walk(f, known, root, *c, here, g)?;
                let cc = cond_clock(&body, known, root, *c).map_err(stop)?;
                g = after(g, cc);
                let mut under = false;
                // A constant condition is decided at this stage only when a part that the stage makes is under it: a later condition.
                for (x, k, kg) in links[n + 1..].iter().map(|(x, _)| (*x, known.clone(), g)) {
                    under = under || makes(&body, &k, root, x, here, kg).map_err(stop)?;
                }
                if g > here || (cc == Clock::Const && !under) || f.truth(*c, span)? {
                    break;
                }
            }
            for (_, then) in &links {
                walk(f, known, root, *then, here, guard)?;
            }
            walk(f, known, root, last, here, guard)
        }
        K::Binary { op: op @ (BinOp::And | BinOp::Or), lhs, rhs, .. } => {
            walk(f, known, root, *lhs, here, guard)?;
            let cc = cond_clock(&body, known, root, *lhs).map_err(stop)?;
            let g = guard.max(cc);
            if decides(&body, known, root, e, (cc, g), here).map_err(stop)?
                && f.truth(*lhs, span)? == (*op == BinOp::And)
            {
                walk(f, known, root, *rhs, here, g)?;
            }
            Ok(())
        }
        K::Match { scrutinee, arms, tilde: None } => {
            walk(f, known, root, *scrutinee, here, guard)?;
            let sc = seen_of(&body, known, root, *scrutinee).map_err(stop)?;
            let cc = cond_clock(&body, known, root, *scrutinee).map_err(stop)?;
            let mut acc = guard.max(cc);
            if !decides(&body, known, root, e, (cc, acc), here).map_err(stop)? {
                return Ok(());
            }
            let v = f.eval(*scrutinee)?;
            let ty = body.ty(*scrutinee).map_err(stop)?;
            for arm in arms {
                let mut inner = known.clone();
                for l in body.pat_locals(arm.pat).map_err(stop)? {
                    inner.insert(l, sc);
                }
                if !f.arm(arm.pat, &v, ty, None, span)? {
                    continue;
                }
                let mut at_body = acc;
                if let Some(g) = arm.guard {
                    walk(f, &inner, root, g, here, acc)?;
                    at_body = acc.max(cond_clock(&body, &inner, root, g).map_err(stop)?);
                    if at_body > here {
                        return Ok(());
                    }
                    if !f.truth(g, span)? {
                        acc = at_body;
                        continue;
                    }
                }
                return walk(f, &inner, root, arm.body, here, at_body);
            }
            Ok(())
        }
        K::Match { scrutinee, arms, tilde: Some(_) } => {
            // The side that selects first (§11.5, S-1094 (1)): the object and then the patterns and guards from the top, as far as this stage
            // decides them (the clock of each is not after it), up to the first arm that the pattern and the guard choose. Then every body in the
            // order written, not under a condition. The bindings of an arm that the stage makes (the fastest clock of the object and of the guards
            // from the first arm to its own is not after it) are the parts of the object where the arm is taken and `T.default()` where it is
            // not (S-1131); a body that binds later than this stage is walked without them (what reads them is made by that stage).
            walk(f, known, root, *scrutinee, here, guard)?;
            let sc = seen_of(&body, known, root, *scrutinee).map_err(stop)?;
            let mut acc = guard.max(cond_clock(&body, known, root, *scrutinee).map_err(stop)?);
            let mut deciding = acc <= here;
            let (v, ty) = (if deciding { Some(f.eval(*scrutinee)?) } else { None }, body.ty(*scrutinee).map_err(stop)?);
            let (mut bound, mut taken, mut plan) =
                (clock_of(&body, known, root, *scrutinee).map_err(stop)?, None, Vec::new());
            for (n, arm) in arms.iter().enumerate() {
                let locals = body.pat_locals(arm.pat).map_err(stop)?;
                let mut seen = known.clone();
                seen.extend(locals.iter().map(|l| (*l, sc)));
                let gc = arm.guard.map(|g| cond_clock(&body, &seen, root, g)).transpose().map_err(stop)?;
                if let (true, None, Some(v)) = (deciding, &taken, &v) {
                    if f.arm(arm.pat, v, ty, None, span)? {
                        let mine = f.pat_values(arm.pat)?;
                        match arm.guard {
                            None => taken = Some((n, mine)),
                            Some(g) => {
                                walk(f, &seen, root, g, here, acc)?;
                                if gc.is_some_and(|c| c <= here) && f.truth(g, span)? {
                                    taken = Some((n, mine));
                                }
                            }
                        }
                    }
                }
                if let Some(c) = gc {
                    (acc, bound) = (acc.max(c), bound.max(c));
                    deciding = deciding && acc <= here;
                }
                let mut inner = known.clone();
                inner.extend(locals.iter().map(|l| (*l, Seen::both(bound))));
                plan.push((inner, deciding && bound <= here));
            }
            for (n, (arm, (inner, bound_here))) in arms.iter().zip(plan).enumerate() {
                if !bound_here {
                    walk(f, &inner, root, arm.body, here, guard)?;
                    continue;
                }
                let binds = match &taken {
                    Some((t, mine)) if *t == n => mine.clone(),
                    _ => f.default_values(arm.pat, span)?,
                };
                f.with_bindings(&[], binds, |f| walk(f, &inner, root, arm.body, here, guard))?;
            }
            Ok(())
        }
        K::Par { var, body: inner, .. } => {
            // The replicas in the order of the index, each with its index bound (as the evaluation of the `par~` does).
            // A body that has no part for this stage is not walked (a `par~` of a million replicas that only reads `x`).
            let inside = with_index(&body, known, var.span).map_err(stop)?;
            if makes(&body, &inside, root, *inner, here, guard).map_err(stop)? {
                f.replicate(e, |_: &()| 0, |f| walk(f, &inside, root, *inner, here, guard))?;
            }
            Ok(())
        }
        K::Block(b) => {
            for s in &b.stmts {
                if let StmtKind::Let { init, .. } = &body.ast.stmt(*s).kind {
                    walk(f, known, root, *init, here, guard)?;
                }
            }
            match b.tail {
                Some(t) => walk(f, known, root, t, here, guard),
                None => Ok(()),
            }
        }
        _ => {
            for x in operands(&body, e) {
                walk(f, known, root, x, here, guard)?;
            }
            Ok(())
        }
    }
}

/// What a name that stands for `e` is (a `let` of it, an arm binding of it as an object): the stage its value is made in (S-1196) and the clock
/// it is read at. A derived clock has no read clock here (an error only where a condition reads it).
pub(super) fn seen_of(body: &Body, known: &Known, root: ExprId, e: ExprId) -> Result<Seen, Fault> {
    let stage = stage_of(body, known, root, e)?;
    let read = match clock_of(body, known, root, e) {
        Ok(c) => Some(c),
        Err(Fault::Unavailable(_)) => None,
        Err(fault) => return Err(fault),
    };
    Ok(Seen { stage, read })
}
