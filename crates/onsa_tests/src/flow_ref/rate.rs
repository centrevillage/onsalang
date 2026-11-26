//! The rates (§11.9, §11.4): the chain of `.down~(N)` and `.up~(N)` that ends in a call of an instance (its head and the list of its boundaries, one for each modifier, S-566, S-567, S-1207), the ratio of a derived clock `(sample / N)`, the ticks slower than `sample` a flow has stages for (S-578, S-1079, S-1088),
//! and the time an instance of a chain runs in (`sample_rate()` and `sample_tick()` are 1/N and N times, §11.4). A ratio is the exponent `r` of
//! the `2^r` of the clock over the `sample` of the body: `.down~(4)` is `-2`.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use onsa_sema::flow_names::{Delay, FlowBuiltin, Modifier};
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{CallKind, ClockRatio, ExprId, ExprKind, PatId, RatioOp};

use super::call::parts;
use super::expr::{Frame, LIMITS, LOW_STACK, Stop};
use super::flow::{Clock, Ctx, Inst, Known, Plans, Seen, Step, clock_of, join};
use super::hoist::{feedback, kids, stage_of};
use super::scalar::Fault;
use super::sema_view::{Body, Called, Stage, View, input_ratio, output_stage};
use super::value::Value;
use onsa_sema::def::FlowDef;

/// A chain of modifiers: the call of the instance it starts at (`lp~(x)` of `lp~(x).down~(2).when~(c)`) and each modifier, innermost first (a boundary each, S-1207, S-1209: a modifier wraps the whole on its left).
pub(super) struct Chain {
    pub head: ExprId,
    pub bounds: Vec<Bound>,
}

/// A modifier of a chain: `.down~(N)` and `.up~(N)` by the ratio they give, `.when~(c)` and `.reset_if~(c)` by their condition (they keep the rate, §11.9).
#[derive(Clone, Copy, Debug)]
pub(super) enum Bound {
    Rate(i32),
    When(ExprId),
    ResetIf(ExprId),
}

impl Bound {
    /// The condition of a `when~` or `reset_if~`.
    fn cond(self) -> Option<ExprId> {
        match self {
            Bound::When(c) | Bound::ResetIf(c) => Some(c),
            Bound::Rate(_) => None,
        }
    }

    fn ratio(self) -> i32 {
        match self {
            Bound::Rate(r) => r,
            Bound::When(_) | Bound::ResetIf(_) => 0,
        }
    }
}

impl Chain {
    /// The ratio of the ports of the call as its caller reads them (§11.9, the clock of the call): the sum of the ratios of the boundaries.
    pub(super) fn sum(&self) -> i32 {
        self.bounds.iter().map(|b| b.ratio()).sum()
    }

    /// The conditions of its `when~`s and `reset_if~`s, innermost first: parts of the call, as its head's arguments are.
    pub(super) fn conds(&self) -> impl Iterator<Item = ExprId> + '_ {
        self.bounds.iter().filter_map(|b| match b {
            Bound::When(c) | Bound::ResetIf(c) => Some(*c),
            Bound::Rate(_) => None,
        })
    }
}

/// The exponent of the N of a modifier or of a derived clock: a power of two that is 2 or more (E0808 stops the others in the checker).
fn exponent(body: &Body, n: ExprId) -> Result<i32, Fault> {
    match Frame::new(*body).eval(n).map_err(|stop| stop.fault)? {
        Value::Int(_, n, _) if (2..=1 << 31).contains(&n) && n.count_ones() == 1 => Ok(n.trailing_zeros() as i32),
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
        Stage::Event(_) => Ok(0),
        _ => Err(Fault::Unavailable("an output that is not at a tick")),
    }
}

/// Does an input declared at the ratio `k` (`sample * 2^k`) gather its values at an instance run by a chain of the ratio `r`? When `k > 0` and the chain is slower (§11.9): the body reads the `2^k` elements of the
/// stream of its argument (at the clock `q = k + r`) that came before the position of its tick, a window that the caller's ring keeps (S-578, S-1079). Any other input reads the stream where the run is in time.
pub(super) fn gathers(k: i32, r: i32) -> bool {
    k > 0 && r < 0
}

/// The one check of the length of a burst (§11.9): the stream of an input or output at the clock `q > 0` of a frame is `2^q` elements, wherever a boundary makes a burst or takes one apart (the input, the output, the
/// ring a gather stores). Another length is a fault of the evaluator, not of the program.
pub(super) fn counted(es: &[Value], q: i32) -> Result<(), Fault> {
    match q > 0 && es.len() as u64 == n_of(q) {
        true => Ok(()),
        false => Err(Fault::Internal("a burst that is not as long as the stream at its clock")),
    }
}

/// What the run `j` of an `.up~(N)` boundary (the ratio `r` > 0) takes of the input `v` of its frame (§11.9: the runs of a frame take the elements of the stream in time order) for the input of the part it wraps at `sample * 2^kp`:
/// the stream at the clock `q = kp + r` of a frame is a burst of `2^q` values for `q > 0`, which gives the `2^kp` elements from `j * 2^kp` (a burst) of a `sample * 2^kp`, or the element `j / 2^-kp` of a tick of `sample / 2^-kp` or `j`; any
/// other value is the one value that is read at the position.
pub(super) fn slice(kp: Option<i32>, r: i32, j: u32, v: &Value) -> Result<Value, Fault> {
    // An input that the caller makes at a later stage than this one (`Frame::feed`) is no value yet: the boundary that gathers it replaces it by its ring, or no run reads it (`run_head` checks).
    let Some(kp) = kp.filter(|kp| kp + r > 0 && !matches!(v, Value::Unit)) else { return Ok(v.clone()) };
    let Value::Burst(es) = v else { return Err(Fault::Internal("an input at `sample * N` that is not a burst")) };
    counted(es, kp + r)?;
    let (from, n) = if kp > 0 { ((j as usize) << kp, 1usize << kp) } else { ((j as usize) >> -kp, 1) };
    match (es.get(from..from + n), kp > 0) {
        (Some(part), true) => Ok(Value::Burst(part.to_vec())),
        (Some([one]), false) => Ok(one.clone()),
        _ => Err(Fault::Internal("a run that is not of the frame it takes from")),
    }
}

/// Does a call of an output declared at the ratio `m` deal its `2^m` elements to the frames after the tick of its chain of the ratio `r`? When `m > 0` and the chain is slower: the array of the tick is the caller's, and the
/// frames from the tick read it in order (§11.9, "配る出力は位置 c 〜 c + N − 1 の `sample` の刻みが順に読む").
pub(super) fn deals(m: i32, r: i32) -> bool {
    m > 0 && r < 0
}

/// The elements that the frame `phase` frames after the tick of a chain (the ratio `r` < 0) reads of the `2^m` it dealt (m > 0): `2^o` from `phase * 2^o` for `o = m + r >= 0`, and the one that the tick of
/// `sample / 2^-o` it is in has, `phase / 2^-o`, for `o < 0`.
pub(super) fn dealt(m: i32, r: i32, phase: u64) -> (usize, usize) {
    (((phase << m) >> -r) as usize, n_of((m + r).max(0)) as usize)
}

/// The elements of the output `v` of a body for an output declared at `m`: its `2^m` values for `sample * 2^m` (the array of the body), the one for another.
pub(super) fn elements(m: i32, v: &Value) -> Result<Vec<Value>, Fault> {
    match (m > 0, v) {
        (false, v) => Ok(vec![v.clone()]),
        (true, Value::Array(vs)) => Ok(vs.clone()),
        _ => Err(Fault::Internal("an output at `sample * N` that is not an array")),
    }
}

/// The chain that the call `e` ends, if it is a modifier (the record of the names stage, its head included, R-512): a boundary of `-log2 N` and of `log2 N` for each `.down~(N)` and `.up~(N)` (§11.9, S-1207), and the
/// condition of each `.when~(c)` and `.reset_if~(c)` (§11.10), innermost first.
pub(super) fn chain_of(body: &Body, e: ExprId) -> Result<Option<Chain>, Fault> {
    let Some((_, _, head)) = body.modifier(e) else { return Ok(None) };
    let (mut at, mut bounds) = (e, Vec::new());
    while let Some((m, receiver, _)) = body.modifier(at) {
        let ExprKind::Call { args, .. } = &body.ast.expr(at).kind else { break };
        let n = args.first().ok_or(Fault::Internal("a modifier with no argument"))?.expr;
        bounds.push(match m {
            Modifier::Down => Bound::Rate(-exponent(body, n)?),
            Modifier::Up => Bound::Rate(exponent(body, n)?),
            Modifier::When => Bound::When(n),
            Modifier::ResetIf => Bound::ResetIf(n),
        });
        at = receiver;
    }
    bounds.reverse();
    Ok(Some(Chain { head, bounds }))
}

/// The arguments of the call `e`.
pub(super) fn args_of(body: &Body, e: ExprId) -> Vec<ExprId> {
    match &body.ast.expr(e).kind {
        ExprKind::Call { args, .. } => args.iter().map(|a| a.expr).collect(),
        _ => Vec::new(),
    }
}

/// The N of the ratio `2^r` of a clock, `.down~(N)` or `.up~(N)` or `sample / N` (`r` is the sign of the direction and `log2 N` of the size): the one place of the
/// division of the time that every rate reads. `|r|` is 55 at most (the product of the ratios of the chains is 2^24 at most, which the check stops (E0808, S-1089); a clock of a port 31, `exponent`; the clock of a call is the sum of the two), so that the shift is whole.
pub(super) fn n_of(ratio: i32) -> u64 {
    1u64 << ratio.unsigned_abs()
}

/// How many frames the time `ctx` is after the last tick of `sample / N` (the ratio `r` < 0): the counter of the grid modulo N, 0 on the tick (§11.9).
pub(super) fn phase(ctx: Ctx, r: i32) -> u64 {
    ctx.grid % n_of(r)
}

/// Is the time `ctx` on a tick of `sample / N` (the ratio `r` < 0): when the counter of the grid is a multiple of N, the first frame included (§11.9).
pub(super) fn on_tick(ctx: Ctx, r: i32) -> bool {
    phase(ctx, r) == 0
}

/// The time the j-th frame of an instance of the rate `ratio` runs in, for the time `ctx` of its caller (§11.4): at 1/N of the rate and of the counter for
/// `.down~(N)` (its caller's counter is a multiple of N, so the instance's is the total of the caller / N, the digits over the `U32` kept), at N times the rate
/// and the counter `total * N + j` for `.up~(N)`. The counter of the grid is made of the caller's in the same way (§11.9), the time of a `when~` too.
pub(super) fn time_of(ctx: Ctx, ratio: i32, j: u32) -> Ctx {
    let n = n_of(ratio);
    let (time, grid) = match ratio {
        0 => return ctx,
        ..0 => (Ctx::at(ctx.sample_rate / n as f32, ctx.total() / n), ctx.grid / n),
        _ => (
            Ctx::at(ctx.sample_rate * n as f32, ctx.total().wrapping_mul(n).wrapping_add(u64::from(j))),
            ctx.grid.wrapping_mul(n).wrapping_add(u64::from(j)),
        ),
    };
    time.with_grid(grid)
}

/// The stage of the caller an instance of the ratio `r` of its chain runs the stage `x` of its body in (§11.9, S-1088): `min(x + r, 0)`, one rule for a call with no
/// modifier (`r` = 0: the same stage), for `.down~(N)` (a stage of the body is N times slower in the caller) and for `.up~(N)` (the stages faster than `sample / N` of the caller are in its `sample`).
pub(super) fn caller_stage(x: i32, r: i32) -> i32 {
    (x + r).min(0)
}

/// The stage of the body of an instance that makes its output at `m`: its `sample` for a `sample * N`, the tick of the output for a slower one.
pub(super) fn body_out_stage(m: i32) -> i32 {
    m.min(0)
}

/// A part of a chain (§11.9, S-1207): the head (the part 0) or the head wrapped by the first `b` modifiers (the part `b`, `ratio` the ratio of the modifier that wraps the part `b - 1`). Each is made once, by `levels`, and read by what runs the chain.
#[derive(Debug)]
pub(super) struct Level {
    pub ratio: i32,
    /// The exponent of each input of the head (`None` for the parameter kinds) and of the output as the caller of this part reads them (`sample * 2^k`): those of the part inside, plus `ratio`.
    pub ins: Vec<Option<i32>>,
    pub out: i32,
    /// The inputs of the part inside that this boundary gathers (a ring of its own), and whether it deals the output of the part inside (an array of its own): `gathers`, `deals`.
    pub gathers: Vec<usize>,
    pub deals: bool,
    /// The stages of the caller of this part that it runs in, the slowest first (`caller_stage` of those inside, the stage a ring is written at, the stage it deals at; of the last part, the stage a condition is read in too, `Guard::at`), and the stage it makes its output in.
    pub stages: Vec<i32>,
    pub made: i32,
    /// Of a `.when~(c)` and a `.reset_if~(c)`: its condition and the tick it is read at.
    pub guard: Option<Guard>,
}

impl Level {
    /// The `.when~(c)` that makes this part, if one does.
    pub(super) fn when(&self) -> Option<Guard> {
        self.guard.filter(|g| g.kind == Modifier::When)
    }

    /// The `.reset_if~(c)` that makes this part, if one does.
    pub(super) fn reset(&self) -> Option<Guard> {
        self.guard.filter(|g| g.kind == Modifier::ResetIf)
    }

    /// The stage of the caller of this part that a work of the part inside at its stage `x` is in (§11.9, §11.10): `caller_stage` out of a boundary, and at least W out of a `when~` (it runs the slower ticks inside in its W).
    pub(super) fn outer(&self, x: i32) -> i32 {
        self.when().map_or(caller_stage(x, self.ratio), |w| x.max(w.w))
    }
}

/// A `.when~(c)` or a `.reset_if~(c)` of a chain (§11.10, S-1209): of a `.when~`, `w` is the clock W as its part reads it, the output of the part inside when that is slower than P (`sample` here) and P else; of a
/// `.reset_if~`, the tick R of the condition (`reset_level`). `at` is the stage of the caller the condition is read in (`levels`); `port` is the port of the parts (`Level::ins`) of a condition that a boundary outside
/// gathers, which the part reads from there instead (`gathered`).
#[derive(Clone, Copy, Debug)]
pub(super) struct Guard {
    pub kind: Modifier,
    pub cond: ExprId,
    pub w: i32,
    pub at: i32,
    pub port: Option<usize>,
    /// A `.reset_if~(c)` whose condition is an event: it is read and puts the part back at the stage of that event, not at a tick of the caller (`Frame::reset_on_event`).
    pub ev: bool,
}

/// The clock of a condition in the caller (§11.3, its `at` included) and whether it is a value of a tick (its stage: a value of the parameter kinds with an `at` is not, §11.3).
#[derive(Clone, Copy, Debug)]
pub(super) struct CondClock {
    pub clock: Clock,
    pub tick: bool,
}

/// The expressions of the ports of the parts of a chain (`Level::ins`): the arguments `args` of its head, then the condition of each modifier that has one, innermost first.
pub(super) fn port_exprs(args: impl IntoIterator<Item = ExprId>, levels: &[Level]) -> Vec<ExprId> {
    args.into_iter().chain(levels.iter().filter_map(|l| l.guard.map(|g| g.cond))).collect()
}

/// The tick of the condition of the clock `clock` of a modifier of a part whose output is at `out`, as the part reads it (§11.10): the clock moved in by the ratios `outside` the modifier (not cut at 0), and for `sample_tick()` alone
/// (with values of the parameter kinds too; the clock W of the body that wrote it, §11.4) and a value of the parameter kinds W (the output, if slower than P), the caller's `sample` where W is faster ("W が `sample * N` なら、本体の `sample` の 1 刻みに 1 回").
pub(super) fn cond_tick(clock: Clock, out: i32, outside: &[Bound]) -> i32 {
    let outside: i32 = outside.iter().map(|b| b.ratio()).sum();
    match clock {
        Clock::Tick(k) if clock != Clock::AMBIENT => k - outside,
        _ => out.min(0).min(-outside),
    }
}

/// Does a boundary of `outside` gather a port at `k` (moved out by each, as an input of the head is)? §11.10: "境界の内に書いた修飾子の条件は、同じクロックの頭の入力と同じ時点の値を読む（`sample_tick()` の他に刻みの値もイベントの値も読まない条件は W の周期の値で（§11.4）、境界の刻みより速い周期の値は頭の入力と
/// 同じに境界で集め、…）": the condition of a modifier is a port of its part where a boundary gathers it, else the caller reads it at its tick (`Guard::at`); a value of the parameter kinds (an `at` on one too, §11.3) is not a port.
fn gathered(k: i32, outside: &[Bound]) -> bool {
    outside.iter().scan(k, |k, b| Some((gathers(*k, b.ratio()), *k += b.ratio()).0)).any(|g| g)
}

/// The parts of a chain of the boundaries `bounds` (innermost first) of the flow `decl` that has the ticks `slow` of its own: `[head, ..]`, one more than the modifiers. `clock` gives the clock of the condition of
/// a modifier in the caller. The ports of each part (`ins`) are the inputs of the head, then one for the condition of each `when~` and `reset_if~` (innermost first, `gathered`): `None` where it has none, and in the parts inside it.
pub(super) fn levels(
    decl: &FlowDef,
    slow: &[i32],
    bounds: &[Bound],
    clock: &dyn Fn(ExprId) -> Result<CondClock, Fault>,
) -> Result<Rc<[Level]>, Fault> {
    let m = out_ratio(decl)?;
    let head = Level {
        ratio: 0,
        ins: decl.inputs.iter().map(input_ratio).collect(),
        out: m,
        gathers: Vec::new(),
        deals: false,
        stages: slow.iter().copied().chain([0]).collect(),
        made: body_out_stage(m),
        guard: None,
    };
    let (mut all, mut at_run) = (vec![head], Vec::new());
    for (i, &bound) in bounds.iter().enumerate() {
        let r = match bound {
            Bound::Rate(r) => r,
            Bound::When(cond) | Bound::ResetIf(cond) => {
                let (cc, outside) = (clock(cond)?, &bounds[i + 1..]);
                all.iter_mut().for_each(|l| l.ins.push(None));
                let prev = &all[all.len() - 1];
                // A condition that is an event is read at the stage of that event: the part has the stages and the output of the one inside.
                if let (Bound::ResetIf(_), Clock::Event(_)) = (bound, cc.clock) {
                    let mut part = reset_level(prev, cond, 0);
                    part.stages.clone_from(&prev.stages);
                    part.made = prev.made;
                    part.guard = part.guard.map(|g| Guard { ev: true, ..g });
                    all.push(part);
                    continue;
                }
                let tick = cond_tick(cc.clock, prev.out, outside);
                // SPEC-GAP(S-1227): a condition that mixes a signal and a value of the parameter kinds is a value of a tick, which a boundary gathers whole (provisional (1)).
                let mut part =
                    if let Bound::When(_) = bound { when_level(prev, cond) } else { reset_level(prev, cond, tick) };
                let n = part.ins.len() - 1;
                if let (true, Some(g)) = (cc.tick, part.guard.as_mut()) {
                    g.at = tick + outside.iter().map(|b| b.ratio()).sum::<i32>();
                    if gathered(tick, outside) {
                        (g.port, part.ins[n]) = (Some(n), Some(tick));
                    }
                }
                at_run.extend((!cc.tick).then_some(all.len()));
                all.push(part);
                continue;
            }
        };
        let prev = &all[all.len() - 1];
        let gathers: Vec<usize> =
            (0..prev.ins.len()).filter(|i| prev.ins[*i].is_some_and(|k| self::gathers(k, r))).collect();
        let deals = self::deals(prev.out, r);
        let ins: Vec<Option<i32>> = prev.ins.iter().map(|k| k.map(|k| k + r)).collect();
        let mut stages: BTreeSet<i32> = prev.stages.iter().map(|y| caller_stage(*y, r)).collect();
        stages.extend(gathers.iter().filter_map(|i| ins[*i]).map(|k| k.min(0)));
        stages.extend(deals.then_some(r));
        let made = if deals { r } else { caller_stage(prev.made, r) };
        let next = Level {
            ratio: r,
            ins,
            // The events a head gives are no stream: a boundary does not move their clock (§11.11, the position of an event is the one of the caller).
            out: if matches!(output_stage(decl), Ok(Stage::Event(_))) { 0 } else { prev.out + r },
            gathers,
            deals,
            stages: stages.into_iter().collect(),
            made,
            guard: None,
        };
        all.push(next);
    }
    // The stage of the caller each condition is read in. A value of a tick is an expression of the caller at its own clock there (`sample_tick()` alone at W, as with the `at` of W, S-1230 (G)): it is made at the tick of the body
    // that wrote it and kept, and the part reads the last one at the ticks it runs, which an outer `when~` may have moved off that grid (§11.4, §11.10: "同じクロックの頭の入力と同じ時点の値"). A value of the parameter kinds is
    // read at the run (§11.10): at its W (or R) moved out of the parts outside it as their stages are (`Level::outer`; a `reset_if~` keeps them).
    for b in at_run {
        let Some(mut g) = all[b].guard else { continue };
        g.at = all[b + 1..].iter().fold(g.w, |x, l| l.outer(x));
        all[b].guard = Some(g);
    }
    let top = all.len() - 1;
    let read = all.iter().filter_map(|l| l.guard.filter(|g| !g.ev).map(|g| g.at));
    let stages: BTreeSet<i32> = read.chain(all[top].stages.iter().copied()).collect();
    all[top].stages = stages.into_iter().collect();
    Ok(all.into())
}

/// The part that a `.when~(c)` makes of the part `inside` (§11.10, S-1209): the same ports and output; it reads `c` at W and runs the part at the ticks of P it holds for, so the stages of the part slower than W are run in W (their
/// grid counts the frames it ran), and its `sample` counts them. It makes its output, which it holds, at W. An input of the part slower than W is a stage of it too: the caller reads it at its own tick
/// (`feed`), and the part at the tick of its grid, in W (§11.10: "呼び出し側の値を、部品の中の刻みの時点で読む").
fn when_level(inside: &Level, cond: ExprId) -> Level {
    let w = inside.out.min(0);
    let mut part = Level {
        ratio: 0,
        ins: inside.ins.clone(),
        out: inside.out,
        gathers: Vec::new(),
        deals: false,
        stages: Vec::new(),
        made: w,
        guard: Some(Guard { kind: Modifier::When, cond, w, at: w, port: None, ev: false }),
    };
    // The stages the part runs in are those inside moved out by `outer` (the one rule of what a `when~` runs in W), W and the `sample`, and the tick of an input slower than W. The moving shows in no value (`run_when` does nothing in a stage slower than W, so a mutant of it passes the gate and `heavy_`); it is kept so that `stages` says what the part runs in.
    let slow = inside.ins.iter().flatten().copied().filter(|k| *k < w);
    let stages: BTreeSet<i32> = inside.stages.iter().map(|y| part.outer(*y)).chain([w, 0]).chain(slow).collect();
    part.stages = stages.into_iter().collect();
    part
}

/// The part that a `.reset_if~(c)` makes of the part `inside` (§11.10): the same ports, stages and output (made again at R where that is later), and the tick R of `c` (`cond_tick`), a stage of it (once a frame, before the
/// first run of an `.up~(N)`, for a value of the parameter kinds under one).
fn reset_level(inside: &Level, cond: ExprId, tick: i32) -> Level {
    let stages: BTreeSet<i32> = inside.stages.iter().copied().chain([tick]).collect();
    Level {
        ratio: 0,
        ins: inside.ins.clone(),
        out: inside.out,
        gathers: Vec::new(),
        deals: false,
        stages: stages.into_iter().collect(),
        made: inside.made.max(tick),
        guard: Some(Guard { kind: Modifier::ResetIf, cond, w: tick, at: tick, port: None, ev: false }),
    }
}

/// The time of the head of a chain that its caller runs at `ctx` (`init`, `block`; the run of a stage takes it from `time_of` boundary by boundary, §11.4).
pub(super) fn child_time(levels: &[Level], ctx: Ctx) -> Ctx {
    levels.iter().skip(1).rev().fold(ctx, |c, l| time_of(c, l.ratio, 0))
}

/// The ticks slower than `sample` that the stages of a body are of, in the order they run: the larger N (the slower tick) first (§11.9, S-1079): the clock of each step, the clocks of its parts,
/// and the stage of the body of each instance it calls that is in this one (`caller_stage` of each of its slow ticks and of its `sample`, moved out of each boundary of the chain it is called by, `levels`).
/// With them, the clock of the condition of each modifier of the body (`CondClock`, which `levels` reads).
pub(super) fn slow_ticks(view: View, body: &Body, steps: &[Step], plans: &Plans) -> Result<(Rc<[i32]>, Conds), Stop> {
    let (mut all, mut conds) = (BTreeSet::new(), HashMap::new());
    for s in steps {
        all.extend(Some(s.clock).into_iter().filter_map(slow));
        visit(view, body, &s.known, s.init, s.init, plans, &mut (&mut all, &mut conds))?;
    }
    let mut ticks: Vec<i32> = all.into_iter().collect();
    ticks.sort_by_key(|r| std::cmp::Reverse(n_of(*r)));
    Ok((ticks.into(), Rc::new(conds)))
}

/// The clock of the condition of each `.when~` and `.reset_if~` of a body, in the caller (`CondClock`), and of the delay at the head of a chain on one (its K).
pub(super) type Conds = Rc<HashMap<ExprId, CondClock>>;

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
        // The condition of a `reset_if~` is read at the stage of its clock, not where its chain is: it makes the chain no part of the loop the producer of its event is in (S-1250: `c = prev~(^c + 1).reset_if~(e >= 5)`, `e = prev~(^d)`,
        // `d = gen~(c)`), unless it reads a `^name` of its own.
        let apart: Vec<ExprId> = chain_of(body, e).ok().flatten().map_or_else(Vec::new, |c| {
            c.bounds
                .iter()
                .filter_map(|b| matches!(b, Bound::ResetIf(x) if !feedback(body, *x)).then_some(b.cond()))
                .flatten()
                .collect()
        });
        body.ast.sub_exprs(e).into_iter().filter(|x| !apart.contains(x)).for_each(|x| reads(body, owner, x, out));
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
    Ok(slow(clock).map(|_| clock.rooted()).or(matches!(clock, Clock::Event(_)).then_some(clock)))
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
        // A chain on a delay has the clock of the delay (`clock_of`): what enters its first argument.
        ExprKind::Call { kind: CallKind::Flow, .. } => match chain_of(body, e)?.map_or(e, |c| c.head) {
            call if matches!(body.called(call)?, Called::Builtin(FlowBuiltin::Delay(_))) => {
                let first = args_of(body, call).into_iter().nth(Delay::SAVED);
                entering(body, known, root, first.ok_or(Fault::Internal("a delay with no argument"))?, inside)
            }
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
    out: &mut (&mut BTreeSet<i32>, &mut HashMap<ExprId, CondClock>),
) -> Result<(), Stop> {
    let at = body.ast.expr(e).span;
    let here = |fault| Stop { fault, at };
    if onsa_diag::stack::remaining().is_some_and(|left| left < LIMITS.reserve) {
        return Err(here(LOW_STACK));
    }
    // The clock `at` gives a part of `block` (`p at (sample / 4)`) is a tick too (a loop it enters ticks with it, `ring_clock`).
    let read = clock_of(body, known, root, e).map_err(here)?;
    out.0.extend([stage_of(body, known, root, e).map_err(here)?, read].into_iter().filter_map(slow));
    let chain = chain_of(body, e).map_err(here)?;
    // The stages of an instance that is called here are stages of this one: those of the last part of its chain (`levels`; of the head alone for no modifier).
    let (call, bounds) = chain.as_ref().map_or((e, &[][..]), |c| (c.head, &c.bounds[..]));
    let tick = |c| Ok(matches!(stage_of(body, known, root, c)?, Clock::Tick(_)));
    let clock = |c| Ok(CondClock { clock: clock_of(body, known, root, c)?, tick: tick(c)? });
    // The clock K of a delay a chain is on is kept with them (§11.10: its W).
    let delay = |c: &&Chain| matches!(body.called(c.head), Ok(Called::Builtin(FlowBuiltin::Delay(_))));
    for c in chain.iter().flat_map(Chain::conds).chain(chain.iter().filter(delay).map(|c| c.head)) {
        out.1.insert(c, clock(c).map_err(here)?);
    }
    if let Ok(Called::Flow(def)) = body.called(call) {
        let body_ticks = Inst::planned(view, def, plans)?.slow;
        let parts = levels(view.flow(def).map_err(here)?, &body_ticks, bounds, &clock).map_err(here)?;
        out.0.extend(parts[parts.len() - 1].stages.iter().copied().filter(|s| *s < 0));
    }
    // The arms of a `match` see their bindings with the clocks the object and the guards give them (§11.5): a condition of a modifier that reads one is of that clock (`hoist::kids`).
    if matches!(body.ast.expr(e).kind, ExprKind::Match { .. }) {
        return kids(body, known, root, e, Clock::Const)
            .map_err(here)?
            .into_iter()
            .try_for_each(|(x, k, _)| visit(view, body, &k, root, x, plans, out));
    }
    let inside = match &chain {
        Some(c) => args_of(body, c.head).into_iter().chain(c.conds()).collect(),
        None => parts(body, e),
    };
    inside.into_iter().try_for_each(|x| visit(view, body, known, root, x, plans, out))
}
