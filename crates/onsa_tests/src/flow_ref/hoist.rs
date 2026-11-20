//! Hoisting (§11.3): "コンパイラは各式を、部分式も含めて、その値と評価されるかどうかが決まる最も遅い段で評価する". The `let`s and the output
//! of a stage are made in `flow::stage`; this is the other half: the parts of a `let` (or of the output) that are of a slower clock than the
//! `let` itself, which a stage before the one of the `let` evaluates, once, whether the value is read or not. The part is the largest one of
//! the stage that is Copy (S-1046 (a): a part that is not Copy is read where it is written, and the Copy parts in it are hoisted by
//! the same rule; Copy is the checker's judgement of §4.6), and it is not a name, a literal, `sample_rate()` or `sample_tick()` (they have a
//! place already, or none, §11.3). The value is kept, so the `let` reads it where it is written and does not make it again (`Frame::hoisted`;
//! the field of the state of §11.6).
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

use std::collections::HashMap;

use onsa_diag::Span;
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{BinOp, ExprId, ExprKind, StmtKind};

use super::expr::{Frame, LOW_STACK, Stop};
use super::flow::{Clock, clock_of};
use super::scalar::Fault;
use super::sema_view::{Body, Stage};

type Known = HashMap<LocalId, Clock>;

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

/// A parenthesis or an `at` takes nothing from the stage of the expression it holds (§11.3: "`at` は段を変えない").
fn strip(body: &Body, mut e: ExprId) -> ExprId {
    while let ExprKind::Paren(x) | ExprKind::At { expr: x, .. } = &body.ast.expr(e).kind {
        e = *x;
    }
    e
}

/// The stage of a condition `c`, as a clock: that of the expression it is (`at` and parentheses off), and the stage of the reader (`sample`) for
/// a value that is not Copy, which is not hoisted (S-1046 (a)).
fn cond_clock(body: &Body, known: &Known, root: ExprId, c: ExprId) -> Result<Clock, Fault> {
    let inner = strip(body, c);
    if !body.view.is_copy(body.ty_id(inner)?) {
        return Ok(Clock::Sample);
    }
    clock_of(body, known, root, inner)
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
    let clock = clock_of(body, known, root, e)?;
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
/// expression are walked by themselves; `if~` and `match~` give their condition and object only).
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
        K::If { cond, .. } => vec![*cond],
        K::Match { scrutinee, .. } => vec![*scrutinee],
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
    inside.insert(body.par_var(at)?, Clock::Init);
    Ok(inside)
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
        K::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
            let g = after(guard, cond_clock(body, known, root, *lhs)?);
            vec![(*lhs, known.clone(), guard), (*rhs, known.clone(), g)]
        }
        K::Match { scrutinee, arms, tilde: None } => {
            let sc = clock_of(body, known, root, *scrutinee)?;
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
        let clock = clock_of(body, &known, root, e)?;
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
    let clock = clock_of(&body, known, root, e).map_err(stop)?;
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
            let sc = clock_of(&body, known, root, *scrutinee).map_err(stop)?;
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
