//! The rates (§11.9, §11.4): the chain of `.down~(N)` and `.up~(N)` that ends in a call of an instance (its head and the sum of the ratios of the
//! chain, S-566, S-567), the ratio of a derived clock `(sample / N)`, the ticks slower than `sample` a flow has stages for (S-578, S-1079, S-1088),
//! and the time an instance of a chain runs in (`sample_rate()` and `sample_tick()` are 1/N and N times, §11.4). A ratio is the exponent `r` of
//! the `2^r` of the clock over the `sample` of the body: `.down~(4)` is `-2`.

use std::collections::BTreeSet;
use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::flow_names::FlowBuiltin;
use onsa_syntax::ast::{CallKind, ClockRatio, ExprId, ExprKind, RatioOp};

use super::call::parts;
use super::expr::{Frame, LIMITS, LOW_STACK, Stop};
use super::flow::{Clock, Ctx, Inst, Known, Plans, Step, clock_of, join};
use super::hoist::{feedback, stage_of};
use super::scalar::Fault;
use super::sema_view::{Body, Called, View};
use super::state::SAVED;
use super::value::Value;

/// A chain of modifiers: the call of the instance it starts at (`lp~(x)` of `lp~(x).down~(2).up~(4)`) and the sum of its ratios.
pub(super) struct Chain {
    pub head: ExprId,
    pub ratio: i32,
}

/// The exponent of the N of a modifier or of a derived clock: a power of two that is 2 or more (E0808 stops the others in the checker).
fn exponent(body: &Body, n: ExprId) -> Result<i32, Fault> {
    match Frame::new(*body).eval(n).map_err(|stop| stop.fault)? {
        Value::Int(_, n, _) if n >= 2 && n.count_ones() == 1 => Ok(n.trailing_zeros() as i32),
        _ => Err(Fault::Unavailable("an N that is not a power of 2 of 2 or more")),
    }
}

/// The ratio of a derived clock written `at (sample / N)`: `-log2 N`. One of `sample * N` is a conversion flow's (U2b).
pub(super) fn derived(body: &Body, r: &ClockRatio) -> Result<i32, Fault> {
    match r.op {
        RatioOp::Div => exponent(body, r.n).map(|k| -k),
        RatioOp::Mul => Err(Fault::Unavailable("a clock of sample * N (conversion flows are U2b)")),
    }
}

/// The chain that the call `e` ends, if it is a modifier: `.down~(N)` and `.up~(N)` add `-log2 N` and `log2 N` (§11.9); `when~` and `reset_if~` are
/// W7-10's.
pub(super) fn chain_of(body: &Body, e: ExprId) -> Result<Option<Chain>, Fault> {
    let (mut at, mut ratio, mut seen) = (e, 0, false);
    while let Some((m, receiver)) = body.modifier(at) {
        let ExprKind::Call { args, .. } = &body.ast.expr(at).kind else { break };
        let n = args.first().ok_or(Fault::Internal("a modifier with no argument"))?.expr;
        ratio += match m.ratio_op() {
            Some(RatioOp::Div) => -exponent(body, n)?,
            Some(RatioOp::Mul) => exponent(body, n)?,
            None => return Err(Fault::Unavailable("a modifier of W7-10 (`when~`, `reset_if~`)")),
        };
        (at, seen) = (receiver, true);
    }
    Ok(seen.then_some(Chain { head: at, ratio }))
}

/// The arguments of the call `e`.
pub(super) fn args_of(body: &Body, e: ExprId) -> Vec<ExprId> {
    match &body.ast.expr(e).kind {
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        _ => Vec::new(),
    }
}

/// The N of the ratio `2^r` of a clock, `.down~(N)` or `.up~(N)` or `sample / N` (`r` is the sign of the direction and `log2 N` of the size): the one place of the
/// division of the time that every rate reads. A ratio over 40 is not told apart from 40 (the counter is 2^64 at most).
pub(super) fn n_of(ratio: i32) -> u64 {
    1u64 << ratio.unsigned_abs().min(40)
}

/// Does an instance of the rate `ratio` run at the time of its caller (a call with no modifier, or a chain whose ratios cancel)? S-1088: its ticks slower than
/// `sample` are then in the stages of its caller, at the same position; one of another rate has a time of its own, and its ticks are its own.
pub(super) fn at_callers_time(ratio: i32) -> bool {
    ratio == 0
}

/// Is the time `ctx` on a tick of `sample / N` (the ratio `r` < 0): when the counter is a multiple of N, the first frame included (§11.9).
pub(super) fn on_tick(ctx: Ctx, r: i32) -> bool {
    ctx.total() % n_of(r) == 0
}

/// The frames an instance of the rate `ratio` of the chain runs for a frame of its caller: one for `.down~(N)` (when the caller's tick is a multiple of N) and
/// none of the chain (ratio 0), N for `.up~(N)` (§11.9).
pub(super) fn frames(ratio: i32) -> u32 {
    if ratio > 0 { u32::try_from(n_of(ratio)).unwrap_or(0) } else { 1 }
}

/// The time the j-th frame of an instance of the rate `ratio` runs in, for the time `ctx` of its caller (§11.4): at 1/N of the rate and of the counter for
/// `.down~(N)` (its caller's counter is a multiple of N, so the instance's is the total of the caller / N, the digits over the `U32` kept), at N times the rate
/// and the counter `total * N + j` for `.up~(N)`.
pub(super) fn time_of(ctx: Ctx, ratio: i32, j: u32) -> Ctx {
    let n = n_of(ratio);
    match ratio {
        0 => ctx,
        ..0 => Ctx::at(ctx.sample_rate / n as f32, ctx.total() / n),
        _ => Ctx::at(ctx.sample_rate * n as f32, ctx.total().wrapping_mul(n).wrapping_add(u64::from(j))),
    }
}

/// The ticks slower than `sample` that the stages of a body are of, in the order they run: the larger N (the slower tick) first (§11.9, S-1079): those of the parts of each step that
/// a tick makes (the ticks of a delay, of an `at (sample / N)`, of a chain), and those of the instances the body calls at its own time (a call with
/// no modifier, or a chain of ratio 0: S-1088 puts their ticks in the stage of the caller). The ticks of an instance that a chain runs at another rate
/// are its own (its frame has them).
pub(super) fn slow_ticks(view: View, body: &Body, steps: &[Step], plans: &Plans) -> Result<Rc<[i32]>, Stop> {
    let mut all = BTreeSet::new();
    for s in steps {
        let at = body.ast.expr(s.init).span;
        let mut mine = BTreeSet::new();
        visit(view, body, &s.known, s.init, s.init, plans, &mut mine)?;
        // Not evaluated yet: a loop whose clock is one of the ticks (`let s = prev~(^s) + lf`). The spec has it tick with the clock that enters from
        // outside (§11.3), and a delay of a loop that ticked with `sample` would give another series without saying so. A loop that a tick enters only
        // under an `at` to `sample` (`let u = (lf at sample) + prev~(^u)`) ticks with `sample`, and is evaluated.
        if !mine.is_empty() && feedback(body, s.init) && slower(lenient(entering(body, &s.known, s.init, s.init), at)?)
        {
            return Err(Stop { fault: Fault::Unavailable("a loop of a tick slower than sample"), at });
        }
        all.extend(mine);
    }
    let mut ticks: Vec<i32> = all.into_iter().collect();
    ticks.sort_by_key(|r| std::cmp::Reverse(n_of(*r)));
    Ok(ticks.into())
}

/// Is `c` a tick slower than `sample`?
fn slower(c: Clock) -> bool {
    matches!(c.rooted(), Clock::Tick(r) if r < 0)
}

/// A clock the evaluator has not (`Unavailable`) is no clock here, as for the ticks of a part: the plan does not stop at what it does not read.
fn lenient(clock: Result<Clock, Fault>, at: Span) -> Result<Clock, Stop> {
    match clock {
        Err(Fault::Unavailable(_)) => Ok(Clock::Const),
        other => other.map_err(|fault| Stop { fault, at }),
    }
}

/// The clock a loop (an expression that reads a `^name`) ticks with (§11.3): that of what enters it from outside, by the rules of an expression with no loop. The
/// reads of the loop enter nothing, and a delay of one (`prev~(^s)`) has the clock of its first argument, so it enters what that has besides.
fn entering(body: &Body, known: &Known, root: ExprId, e: ExprId) -> Result<Clock, Fault> {
    if !feedback(body, e) {
        return clock_of(body, known, root, e);
    }
    match &body.ast.expr(e).kind {
        ExprKind::Feedback(_) => Ok(Clock::Const),
        ExprKind::At { .. } => clock_of(body, known, root, e),
        ExprKind::Call { kind: CallKind::Flow, args, .. } => match body.called(e)? {
            Called::Builtin(FlowBuiltin::Delay(_)) => {
                entering(body, known, root, args.get(SAVED).ok_or(Fault::Internal("a delay with no argument"))?.expr)
            }
            _ => clock_of(body, known, root, e),
        },
        _ => body.ast.sub_exprs(e).into_iter().try_fold(Clock::Const, |c, x| {
            join(c, entering(body, known, root, x)?).ok_or(Fault::Internal("clocks that do not join"))
        }),
    }
}

/// The slower ticks of `e` and of its parts into `out`.
fn visit(
    view: View,
    body: &Body,
    known: &Known,
    root: ExprId,
    e: ExprId,
    plans: &Plans,
    out: &mut BTreeSet<i32>,
) -> Result<(), Stop> {
    let at = body.ast.expr(e).span;
    let here = |fault| Stop { fault, at };
    if onsa_diag::stack::remaining().is_some_and(|left| left < LIMITS.reserve) {
        return Err(here(LOW_STACK));
    }
    // The clock `at` gives a part of `block` (`p at (sample / 4)`) is a tick too: a loop through it is not evaluated (above).
    let read = lenient(clock_of(body, known, root, e), at)?;
    let clocks = [stage_of(body, known, root, e).map_err(here)?, read];
    out.extend(clocks.into_iter().filter_map(|c| match c.rooted() {
        Clock::Tick(r) if r < 0 => Some(r),
        _ => None,
    }));
    let chain = chain_of(body, e).map_err(here)?;
    let own = at_callers_time(chain.as_ref().map_or(0, |c| c.ratio)).then_some(chain.as_ref().map_or(e, |c| c.head));
    if let Some(Ok(Called::Flow(def))) = own.map(|call| body.called(call)) {
        out.extend(Inst::planned(view, def, plans)?.slow.iter());
    }
    let inside = match &chain {
        Some(c) => args_of(body, c.head),
        None => parts(body, e),
    };
    inside.into_iter().try_for_each(|x| visit(view, body, known, root, x, plans, out))
}
