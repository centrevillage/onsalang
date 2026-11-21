//! The rates (§11.9, §11.4): the chain of `.down~(N)` and `.up~(N)` that ends in a call of an instance (its head and the sum of the ratios of the
//! chain, S-566, S-567), the ratio of a derived clock `(sample / N)`, the ticks slower than `sample` a flow has stages for (S-578, S-1079, S-1088),
//! and the time an instance of a chain runs in (`sample_rate()` and `sample_tick()` are 1/N and N times, §11.4). A ratio is the exponent `r` of
//! the `2^r` of the clock over the `sample` of the body: `.down~(4)` is `-2`.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use onsa_sema::flow_names::FlowBuiltin;
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{CallKind, ClockRatio, ExprId, ExprKind, PatId, RatioOp};

use super::call::parts;
use super::expr::{Frame, LIMITS, LOW_STACK, Stop};
use super::flow::{Clock, Ctx, Inst, Known, Plans, Seen, Step, clock_of, join};
use super::hoist::{feedback, stage_of};
use super::scalar::Fault;
use super::sema_view::{Body, Called, Stage, View, output_stage};
use super::state::SAVED;
use super::value::Value;
use onsa_sema::def::FlowDef;

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

/// The ratio of a derived clock written `at (sample / N)` or `(sample * N)`: `-log2 N` or `log2 N`.
pub(super) fn derived(body: &Body, r: &ClockRatio) -> Result<i32, Fault> {
    match r.op {
        RatioOp::Div => exponent(body, r.n).map(|k| -k),
        RatioOp::Mul => exponent(body, r.n),
    }
}

/// The ratio of the tick the output of a flow is declared at, as a caller reads it (§11.9): 0 for `sample`.
pub(super) fn out_ratio(decl: &FlowDef) -> Result<i32, Fault> {
    match output_stage(decl)? {
        Stage::Tick(m) => Ok(m),
        _ => Err(Fault::Unavailable("an output that is not at a tick")),
    }
}

/// How the argument of an input declared at the ratio `k` reaches an instance that runs at the ratio `r` of its chain (§11.9: a port is read in the frame of the call, `k + r`).
/// An input of `sample * 2^k` that a `.down~` chain runs gathers, from the 2^-r frames of its caller before the tick, their `2^(k + r)` values each (`per`: one for `sample`,
/// an array of them for `sample * 2^(k + r)`), in the order of time; one that no chain runs (`k + r > 0`) takes the array of `sample * N` the argument is; an input of `sample` of
/// `.up~(N)` takes one element of such an array at each run. Another form has no value in the spec.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Feed {
    Plain,
    Gather { frames: usize, per: usize },
    Each,
}

pub(super) fn feed(k: i32, r: i32) -> Result<Feed, Fault> {
    match (k, r) {
        (_, 0) | (..=0, ..0) => Ok(Feed::Plain),
        (1.., ..0) if k + r >= 0 => Ok(Feed::Gather { frames: n_of(r) as usize, per: n_of(k + r) as usize }),
        (0, 1..) => Ok(Feed::Each),
        (..0, 1..) if k + r <= 0 => Ok(Feed::Plain),
        _ => Err(Fault::Unavailable("an input of sample * N that the chain does not read at the sample of its caller")),
    }
}

/// What a call at the chain ratio `r` makes of an output declared at `m` (§11.9): the value itself (`sample * N` of no chain is the array the body made, and the output of a tick
/// of a `.down~` chain is the one the last tick made), the array that a `.up~(N)` chain makes of the N outputs of its runs, or the one that a `.down~` chain deals out, `per` elements
/// at a time, to the 2^-r frames after the tick (`Dealt`: the output of 2^m is a value of `sample * 2^(m + r)` in the frame of the call).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Out {
    Plain,
    All,
    Dealt { r: i32, per: usize },
}

pub(super) fn out_of(m: i32, r: i32) -> Result<Out, Fault> {
    match (m, r) {
        (1.., ..0) if m + r >= 0 => Ok(Out::Dealt { r, per: n_of(m + r) as usize }),
        (_, 0) | (..=0, ..0) => Ok(Out::Plain),
        (0, 1..) => Ok(Out::All),
        _ => Err(Fault::Unavailable("an output that the chain does not read at the sample of its caller")),
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

/// How many frames the time `ctx` is after the last tick of `sample / N` (the ratio `r` < 0): the counter modulo N, 0 on the tick (§11.9).
pub(super) fn phase(ctx: Ctx, r: i32) -> u64 {
    ctx.total() % n_of(r)
}

/// Is the time `ctx` on a tick of `sample / N` (the ratio `r` < 0): when the counter is a multiple of N, the first frame included (§11.9).
pub(super) fn on_tick(ctx: Ctx, r: i32) -> bool {
    phase(ctx, r) == 0
}

/// The ratio `2^m` of the clock a call of a flow reads at (the output's `m` and the chain's `r`, §11.9); `None` for what is not a call of a flow.
pub(super) fn call_ratio(body: &Body, e: ExprId) -> Result<Option<i32>, Fault> {
    let (head, r) = match chain_of(body, e)? {
        Some(chain) => (chain.head, chain.ratio),
        None => (e, 0),
    };
    if !matches!(body.ast.expr(head).kind, ExprKind::Call { kind: CallKind::Flow, .. }) {
        return Ok(None);
    }
    match body.called(head)? {
        Called::Flow(def) => Ok(Some(out_ratio(body.view.flow(def)?)? + r)),
        Called::Builtin(_) => Ok(None),
    }
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

/// The stage of the caller an instance of the ratio `r` of its chain runs the stage `x` of its body in (§11.9, S-1088): `min(x + r, 0)`, one rule for a call with no
/// modifier (`r` = 0: the same stage), for `.down~(N)` (a stage of the body is N times slower in the caller) and for `.up~(N)` (the stages faster than `sample / N` of the caller are in its `sample`).
pub(super) fn caller_stage(x: i32, r: i32) -> i32 {
    (x + r).min(0)
}

/// The stage of the caller that makes the output at `m` of an instance of the ratio `r`: the body makes it at its `sample` for a `sample * N`.
pub(super) fn out_stage(m: i32, r: i32) -> i32 {
    caller_stage(m.min(0), r)
}

/// The ticks slower than `sample` that the stages of a body are of, in the order they run: the larger N (the slower tick) first (§11.9, S-1079): the clock of each step, the clocks of its parts,
/// and the stage of the body of each instance it calls that is in this one (`caller_stage` of each of its slow ticks and of its `sample`, with the ratio of the chain it is called by).
pub(super) fn slow_ticks(view: View, body: &Body, steps: &[Step], plans: &Plans) -> Result<Rc<[i32]>, Stop> {
    let mut all = BTreeSet::new();
    for s in steps {
        all.extend(Some(s.clock).into_iter().filter_map(slow));
        visit(view, body, &s.known, s.init, s.init, plans, &mut all)?;
    }
    let mut ticks: Vec<i32> = all.into_iter().collect();
    ticks.sort_by_key(|r| std::cmp::Reverse(n_of(*r)));
    Ok(ticks.into())
}

/// The sets of the `lets` that read each other (§11.3: "互いに頼る `let`", a `^name` among the reads), each with whether it is a loop (more than one `let`, or one that reads itself), the ones read
/// by the others first: the strongly connected components of the graph of the reads, so that the clock of a loop is made once, after those of what enters it.
pub(super) fn components(body: &Body, lets: &[(PatId, ExprId)]) -> Result<Vec<(Vec<usize>, bool)>, Fault> {
    let mut owner = HashMap::new();
    for (i, l) in lets.iter().enumerate() {
        owner.extend(body.pat_locals(l.0)?.into_iter().map(|x| (x, i)));
    }
    fn reads(body: &Body, owner: &HashMap<LocalId, usize>, e: ExprId, out: &mut Vec<usize>) {
        if let (true, Ok(Target::Local(l))) = (body.names(e), body.target(e)) {
            out.extend(owner.get(l));
        }
        body.ast.sub_exprs(e).into_iter().for_each(|x| reads(body, owner, x, out));
    }
    let edges: Vec<Vec<usize>> = lets
        .iter()
        .map(|l| {
            let mut v = Vec::new();
            reads(body, &owner, l.1, &mut v);
            v
        })
        .collect();
    // Tarjan's, with the calls kept in a list (a flow may have thousands of `let`s).
    let n = lets.len();
    let (mut index, mut low, mut on) = (vec![usize::MAX; n], vec![0; n], vec![false; n]);
    let (mut path, mut found, mut next) = (Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut calls = vec![(root, 0)];
        while let Some(&(v, k)) = calls.last() {
            if k == 0 && index[v] == usize::MAX {
                (index[v], low[v], on[v]) = (next, next, true);
                next += 1;
                path.push(v);
            }
            match edges[v].get(k) {
                Some(&w) => {
                    let top = calls.len() - 1;
                    calls[top].1 += 1;
                    if index[w] == usize::MAX {
                        calls.push((w, 0));
                    } else if on[w] {
                        low[v] = low[v].min(index[w]);
                    }
                }
                None => {
                    calls.pop();
                    if let Some(&(parent, _)) = calls.last() {
                        low[parent] = low[parent].min(low[v]);
                    }
                    if low[v] == index[v] {
                        let mut part = Vec::new();
                        while let Some(w) = path.pop() {
                            on[w] = false;
                            part.push(w);
                            if w == v {
                                break;
                            }
                        }
                        part.sort_unstable();
                        let looped = part.len() > 1 || edges[v].contains(&v);
                        found.push((part, looped));
                    }
                }
            }
        }
    }
    Ok(found)
}

/// The clock the loop of the `members` of `lets` ticks with (§11.3): the fastest of what enters it from outside, by `entering`. A tick slower than `sample` is the clock of its steps (a delay in it counts
/// that tick); `None` for a loop that `sample` enters, whose steps have the clocks their operands give. A clock that the evaluator has not is `Unavailable`: it is not `sample`.
pub(super) fn ring_clock(
    body: &Body,
    known: &mut Known,
    lets: &[(PatId, ExprId)],
    members: &[usize],
) -> Result<Option<Clock>, Fault> {
    let mut inside = Vec::new();
    for i in members {
        inside.extend(body.pat_locals(lets[*i].0)?);
    }
    // A name of the loop enters nothing, but `(a at sample)` over one asks for a clock to be there: they are set again when the steps are clocked.
    known.extend(inside.iter().map(|l| (*l, Seen::both(Clock::Const))));
    let mut clock = Clock::Const;
    for i in members {
        let c = entering(body, known, lets[*i].1, lets[*i].1, &inside)?;
        clock = join(clock, c).ok_or(Fault::Internal("clocks that do not join"))?;
    }
    Ok(slow(clock).map(|_| clock.rooted()))
}

/// The ratio of a tick slower than `sample` that `c` is, if it is one.
fn slow(c: Clock) -> Option<i32> {
    match c.rooted() {
        Clock::Tick(r) if r < 0 => Some(r),
        _ => None,
    }
}

/// The clock a loop (an expression that reads a `^name`, or a name of the `inside` of its ring) ticks with (§11.3): that of what enters it from outside, by the rules of an
/// expression with no loop. The reads of the loop enter nothing, and a delay of one (`prev~(^s)`) has the clock of its first argument, so it enters what that has besides.
fn entering(body: &Body, known: &Known, root: ExprId, e: ExprId, inside: &[LocalId]) -> Result<Clock, Fault> {
    if !feedback(body, e) && !reads_inside(body, e, inside) {
        return clock_of(body, known, root, e);
    }
    match &body.ast.expr(e).kind {
        ExprKind::Feedback(_) => Ok(Clock::Const),
        ExprKind::At { .. } => clock_of(body, known, root, e),
        ExprKind::Call { kind: CallKind::Flow, args, .. } => match body.called(e)? {
            Called::Builtin(FlowBuiltin::Delay(_)) => entering(
                body,
                known,
                root,
                args.get(SAVED).ok_or(Fault::Internal("a delay with no argument"))?.expr,
                inside,
            ),
            _ => clock_of(body, known, root, e),
        },
        _ => body.ast.sub_exprs(e).into_iter().try_fold(Clock::Const, |c, x| {
            join(c, entering(body, known, root, x, inside)?).ok_or(Fault::Internal("clocks that do not join"))
        }),
    }
}

/// Does `e` read a name of the `inside` of a ring?
fn reads_inside(body: &Body, e: ExprId, inside: &[LocalId]) -> bool {
    matches!(body.target(e), Ok(Target::Local(l)) if body.names(e) && inside.contains(l))
        || body.ast.sub_exprs(e).into_iter().any(|x| reads_inside(body, x, inside))
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
    // The clock `at` gives a part of `block` (`p at (sample / 4)`) is a tick too (a loop it enters ticks with it, `ring_clock`).
    let read = clock_of(body, known, root, e).map_err(here)?;
    out.extend([stage_of(body, known, root, e).map_err(here)?, read].into_iter().filter_map(slow));
    let chain = chain_of(body, e).map_err(here)?;
    // The stages of an instance that is called here are stages of this one (`caller_stage`, at the ratio of the chain, 0 for no modifier).
    let (call, ratio) = chain.as_ref().map_or((e, 0), |c| (c.head, c.ratio));
    if let Ok(Called::Flow(def)) = body.called(call) {
        let body_ticks = Inst::planned(view, def, plans)?.slow;
        out.extend(body_ticks.iter().chain(&[0]).map(|x| caller_stage(*x, ratio)).filter(|s| *s < 0));
    }
    let inside = match &chain {
        Some(c) => args_of(body, c.head),
        None => parts(body, e),
    };
    inside.into_iter().try_for_each(|x| visit(view, body, known, root, x, plans, out))
}
