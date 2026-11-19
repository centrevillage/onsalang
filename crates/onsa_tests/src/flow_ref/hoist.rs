//! Hoisting (§11.3): "コンパイラは各式を、部分式も含めて、その値と評価されるかどうかが決まる最も遅い段で評価する". The `let`s and the output
//! of a stage are made in `flow::stage`; this is the other half: the parts of a `let` (or of the output) that are of a slower clock than the
//! `let` itself, which a stage before the one of the `let` evaluates, once, whether the value is read or not. The part is the largest one of
//! the stage that is Copy (S-1046 (a): a part that is not Copy is read where it is written, and the Copy parts in it are hoisted by
//! the same rule), and it is not a name, a literal, `sample_rate()` or `sample_tick()` (they have a place already, or none, §11.3). The
//! value is kept, so the `let` reads it where it is written and does not make it again (`Frame::hoisted`; the field of the state of §11.6).
//!
//! This is the walk of the positions that are not conditions: it goes into the operands, the arguments, the elements and the fields, the
//! condition of an `if`, the object of a `match` and the left side of `&&` and `||`, and not into a branch, an arm, a guard or the right
//! side of `&&` / `||` (S-1157, the guarded parts: W7-05 U2), a block expression, or a `par~` (U3). A part that reads a `^name` is left where it
//! is (a feedback has the clock of the reader, §11.3). The constant clock is not hoisted (W9-03 makes it at compile time, E0419).
//! The order inside a stage is the order the parts are written (S-1159, provisional): `flow::stage` walks the `let`s in order and each
//! `let` from the left.

use std::collections::HashMap;

use onsa_diag::Span;
use onsa_sema::{LocalId, Ty};
use onsa_syntax::ast::{BinOp, ExprId, ExprKind};

use super::expr::{Frame, LOW_STACK, Stop};
use super::flow::{Clock, clock_of};
use super::scalar::Fault;
use super::sema_view::{Body, Stage, View};

/// Is a value of the clock `c` made in the stage `at`? The constant clock is not (W9-03 evaluates a constant expression at compile time, and
/// until then it stays where it is written, as the interpreter has it: a panic of it is not hoisted to `init`).
fn mine(c: Clock, at: Stage) -> bool {
    match at {
        Stage::Init => c == Clock::Init,
        Stage::Block => c == Clock::Block,
        Stage::Sample => false,
    }
}

/// Is the type Copy? A struct or an enum is taken as not Copy: its parts that are Copy are hoisted all the same, and that is all
/// that a stage of a panic can tell.
fn copy_ty(view: View, t: &Ty) -> bool {
    match t {
        Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit => true,
        Ty::Array(el, _) => copy_ty(view, view.ty(*el)),
        Ty::Tuple(ts) => ts.iter().all(|t| copy_ty(view, view.ty(*t))),
        _ => false,
    }
}

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

/// The operands that are in a position that is not a condition (see the top): the parts `pre` goes on into.
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

/// Whether a part of the clock of a stage is kept (see the top): Copy, and none of an atom and a feedback.
fn kept(body: &Body, e: ExprId) -> Result<bool, Fault> {
    Ok(body.ty(e).map(|t| copy_ty(body.view, t))? && !atom(body, e) && !feedback(body, e))
}

/// The clock of the part of `root` (a `let` of the body; `known` as in [`pre`]) that holds `at` and that the stage of its clock
/// makes, as [`pre`] chooses it: the innermost, as a part of `init` in a part of `block` is made at `init`. `None` when no part
/// of `init` or `block` holds `at` (it is made with its `let`).
pub(super) fn part_clock(
    body: &Body,
    known: &HashMap<LocalId, Clock>,
    root: ExprId,
    at: Span,
) -> Result<Option<Clock>, Fault> {
    let holds = |x: ExprId| {
        let s = body.ast.expr(x).span;
        s.file == at.file && s.start <= at.start && at.end <= s.end
    };
    let (mut e, mut found) = (root, None);
    loop {
        let clock = clock_of(body, known, root, e)?;
        if clock == Clock::Const {
            return Ok(found);
        }
        if matches!(clock, Clock::Init | Clock::Block) && kept(body, e)? {
            found = Some(clock);
        }
        match operands(body, e).into_iter().find(|&x| holds(x)) {
            Some(x) => e = x,
            None => return Ok(found),
        }
    }
}

/// The parts of `e` (a `let` of the body, `root` its value; `known` the clocks of the locals before it) that the stage `at` makes, in the
/// order they are written: each is evaluated and kept in `f.hoisted`, and a panic of one is the panic of the stage.
pub(super) fn pre(
    f: &mut Frame,
    known: &HashMap<LocalId, Clock>,
    root: ExprId,
    e: ExprId,
    at: Stage,
) -> Result<(), Stop> {
    let body = f.body;
    let here = |fault| Stop { fault, at: body.ast.expr(e).span };
    if f.low_stack() {
        return Err(here(LOW_STACK));
    }
    let clock = clock_of(&body, known, root, e).map_err(here)?;
    if mine(clock, at) {
        if kept(&body, e).map_err(here)? {
            // The value of the call before is stale: made again by this stage (the parts it holds that a slower stage kept stay).
            f.hoisted.remove(&e);
            let v = f.eval(e)?;
            f.hoisted.insert(e, v);
            return Ok(());
        }
    } else if clock < Clock::Block && at == Stage::Block && clock != Clock::Const {
        // Made at `init`: not again.
        return Ok(());
    } else if clock == Clock::Const {
        // A constant: where it is written (W9-03), and no part of it is of another stage.
        return Ok(());
    }
    for x in operands(&body, e) {
        pre(f, known, root, x, at)?;
    }
    Ok(())
}
