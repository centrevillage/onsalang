//! The work of an instance in the stages of its caller (§11.9, S-1088,
//! S-1207, S-1214): [`PlanNode::entries`] and [`PlanNode::read`]. One walk
//! of the boundaries of its chain, inner first, each by one arm moving the
//! work of the part it wraps to the stages of the frame around it
//! ([`bounds::step`]): a `.down~` adds the rings it writes and the array it
//! deals, an `.up~` runs the work of each stage of the part in its N runs
//! ([`Op::Each`]). Each op is moved once: O(boundaries × stages × log
//! stages), 56 stages at most (S-1089).

use std::collections::BTreeMap;

use super::*;

/// The work of a part in each stage of the frame it is called in, slowest
/// first, each in its order (§11.9). A `.reset_if~` puts the part back
/// before its work in the stage of its tick ([`reset`]).
type Level = BTreeMap<ClockStage, Vec<Op>>;

/// The entries and the read of the instance `n` of the callee whose table
/// is `g`: each stage x of the body of `g` (its slow stages, then `sample`)
/// runs, that of `g.out_stage` into the array of the innermost boundary
/// that deals, else as the value; then the arm of each boundary.
pub(super) fn table(n: &PlanNode, g: &FlowInfo) -> (Vec<Entry>, Read) {
    let first = first_deal(n, 0);
    let out = |x| if Some(x) == g.out_stage { first.map_or(Out::Value, Out::Deal) } else { Out::None };
    let heads = g.stages.iter().copied().chain([ClockStage::SAMPLE]);
    let mut level: Level = heads.map(|x| (x, vec![Op::Run { body: x, out: out(x) }])).collect();
    let mut dealt = None;
    let (mut b, mut g) = (0u32, 0u32);
    // The chain inner first: each boundary by its arm, each guard by that of `.when~`.
    for at in 0..n.chain.len() as u32 {
        if let Some(bound) = n.bounds.get(b as usize).filter(|x| x.at == at) {
            level = arm(n, b, bound, level, &mut dealt);
            b += 1;
        } else if let Some(guard) = n.guards.get(g as usize).filter(|x| x.at == at) {
            level = when(n, g, guard, level, &mut dealt);
            g += 1;
        } else if let Some(m) = n.chain.get(at as usize).filter(|m| m.modifier == Modifier::ResetIf) {
            // The walk of the clocks gives the tick of each of a chain with no diagnostic.
            let Some(r) = m.reset else { onsa_diag::internal::bug(Some(m.name), "a `.reset_if~` of no tick") };
            level = reset(n, at, r, level, &mut dealt);
        }
    }
    // The outermost that deals is read from, unless an `.up~` outside it
    // widens its window: then the value is made of it ([`To::Value`]).
    let read = match dealt {
        Some(d) if !wider(n, d, n.bounds.len() as u32) => Read::Array(d),
        _ => Read::Run,
    };
    // Where the caller reads it: its output moved out of the outermost boundary.
    let read_at = n.bounds.last().and_then(|l| Some(bounds::step(ClockStage::Tick(l.out?), l.ratio)));
    let entries = level.into_iter().map(|(caller, ops)| {
        let mut writes = false;
        Op::walk(&ops, &mut |op| {
            writes |= match *op {
                _ if op.makes_value() => true,
                Op::Run { out: Out::Deal(b), .. }
                | Op::Hold { out: Out::Deal(b), .. }
                | Op::Deal { to: To::Array(b), .. } => read == Read::Array(b) && read_at == Some(caller),
                // A reset of the array read, before it is read (§11.10).
                Op::Reset { at } => {
                    matches!(read, Read::Array(b) if n.reset_parts(at).contains(&Part::Deal(b)))
                        && read_at == Some(caller)
                }
                _ => false,
            }
        });
        Entry { caller, read: writes, ops }
    });
    (entries.collect(), read)
}

/// Whether the window of the array of the boundary `to` of `n` (of the
/// value, of `to` the count of its boundaries) is wider than that of the
/// boundary `from` inside it: the ratios from `from` to `to` sum to more
/// than 0 (an `.up~` between widened it). The one test of it (D-15).
fn wider(n: &PlanNode, from: u32, to: u32) -> bool {
    let between = n.bounds.get(from as usize..to as usize).unwrap_or_default();
    between.iter().map(|b| i64::from(b.ratio.0)).sum::<i64>() > 0
}

/// The work of the part the boundary `b` of `n` wraps (`level`) in the
/// stages of the frame around it. Of a `.down~`, each stage moved
/// ([`bounds::step`] is one to one), then the rings it writes, by input,
/// then, of one that deals, at its tick: the copy of the array of the
/// boundary inside that last dealt (`dealt`) into its own, unless its
/// window is wider (that boundary wrote it), and the copy of its own to the
/// next that deals or the value when an `.up~` widens that window (not
/// past a modifier that takes it, [`taker`]: it ends there), after the
/// writer of its own, in each run j of that `.up~`. Of an `.up~`,
/// which gathers and deals nothing ([`bounds::bounds`]), the stages moved
/// to each stage of the frame in one [`Op::Each`], run each j at `sample`
/// and j = 0 alone at a slower one.
fn arm(n: &PlanNode, b: u32, bound: &PlanBound, level: Level, dealt: &mut Option<u32>) -> Level {
    let r = bound.ratio;
    if !r.slower_than_body() {
        let mut groups: BTreeMap<ClockStage, Vec<(ClockStage, Vec<Op>)>> = BTreeMap::new();
        level.into_iter().for_each(|(y, ops)| groups.entry(bounds::step(y, r)).or_default().push((y, ops)));
        let each = |(s, groups)| (s, vec![Op::Each { bound: b, once: s != ClockStage::SAMPLE, groups }]);
        return groups.into_iter().map(each).collect();
    }
    let mut next = Level::new();
    level.into_iter().for_each(|(y, ops)| next.entry(bounds::step(y, r)).or_default().extend(ops));
    for &(port, q) in &bound.gathers {
        let from = n.ring_of(b as usize + 1, port).map_or(Feed::Arg, Feed::Ring);
        next.entry(q).or_default().push(Op::Ring { bound: b, port, from });
    }
    if bound.deals {
        let into = dealt.filter(|&d| !wider(n, d, b)).map(|from| Op::Deal { to: To::Array(b), from, by: b });
        let to = (b + 1..).zip(&n.bounds[b as usize + 1..]).find(|c| c.1.deals).map(|c| c.0);
        // A modifier outside it that takes it copies it in its own frame: the window ends there.
        let held = taker(n, bound.at);
        let wide = wider(n, b, to.into_iter().chain(held).min().unwrap_or(n.bounds.len() as u32));
        let out = wide.then(|| Op::Deal { to: to.map_or(To::Value, To::Array), from: b, by: b });
        let copies: Vec<Op> = into.into_iter().chain(out).collect();
        if !copies.is_empty() {
            next.entry(ClockStage::Tick(r)).or_default().extend(copies);
        }
        *dealt = Some(b);
    }
    next
}

/// The work of the part the guard `g` of `n` wraps (`level`, of the frame
/// it is in) while it runs (§11.10, S-1209), in the stages of that frame:
/// its condition read at W, the stages of the part slower than W moved to
/// W and run at their ticks of the count of the ticks it ran, that of W
/// after them, each stage faster than W in its place guarded by the
/// condition W read last; the count goes on at the `sample` of the frame
/// when one is read (stages moved, or a ring or an array inside it). The
/// value of the part goes where its guard puts it: into the array of the
/// first boundary from the guard out that deals, else the value (the review
/// of the memo of W7-10 U3, its F1 and F2). Of a part that is not a burst it
/// is held: each op that writes there writes the held output instead
/// ([`held`]), an array of a boundary inside it the caller read too
/// (`dealt`), then [`Op::Hold`] puts it there; of a burst, that array is
/// copied there, which [`Op::Hold`] holds. Each
/// stage slower than W is in its own [`Op::When`]; all of it is the work of
/// the stage W, which a `.reset_if~` outside puts back before (S-1228).
fn when(n: &PlanNode, g: u32, guard: &PlanGuard, level: Level, dealt: &mut Option<u32>) -> Level {
    let (w, burst, nb) = (ClockStage::Tick(guard.w), burst(guard), n.inside(guard.at));
    // Where the value of the part goes; the array of a boundary inside it the caller
    // read is copied there of a burst, else held.
    let tob = first_deal(n, nb);
    let into_of = if burst { tob.map_or(To::Value, To::Array) } else { To::Held(g) };
    let read = dealt.take().and_then(|from| copy(n, from, nb, into_of));
    let counted =
        level.keys().any(|&y| y < w) || n.bounds[..nb as usize].iter().any(|b| b.deals || !b.gathers.is_empty());
    let guarded = |cond, due, ops: Vec<Op>, advance| Op::When {
        guard: g,
        cond,
        due,
        ops: ops.into_iter().map(|op| if burst { op } else { held(op, g, nb) }).collect(),
        advance,
    };
    let (mut next, mut slow, mut own) = (Level::new(), Vec::new(), Vec::new());
    for (y, ops) in level {
        match y.cmp(&w) {
            std::cmp::Ordering::Less => slow.push((y, ops)),
            std::cmp::Ordering::Equal => own = ops,
            std::cmp::Ordering::Greater => {
                let advance = counted && y == ClockStage::SAMPLE;
                next.insert(y, vec![guarded(CondRead::Kept, None, ops, advance)]);
            }
        }
    }
    let all: Vec<&Op> = own.iter().chain(slow.iter().flat_map(|s| &s.1)).chain(&read).collect();
    // A burst written into that array is held in it (§11.10).
    let into = |op: &&Op| writes(op, |op| outer(op, nb));
    let to = match tob {
        Some(b) if !burst || all.iter().any(into) => Out::Deal(b),
        _ => Out::Value,
    };
    let makes = read.is_some() || all.iter().any(into);
    own.extend(read);
    let advance = counted && w == ClockStage::SAMPLE;
    let mut at_w = Vec::new();
    if slow.is_empty() {
        at_w.push(guarded(CondRead::Read, None, own, advance));
    } else {
        // The read first, before the work of a stage of the part.
        at_w.push(guarded(CondRead::Read, None, Vec::new(), false));
        at_w.extend(slow.into_iter().map(|(y, ops)| guarded(CondRead::Local, Some(y), ops, false)));
        at_w.push(guarded(CondRead::Local, None, own, advance));
    }
    if makes {
        at_w.push(Op::Hold { guard: g, out: to });
    }
    next.insert(w, at_w);
    if counted && !next.contains_key(&ClockStage::SAMPLE) {
        let s = ClockStage::SAMPLE;
        next.insert(s, vec![guarded(CondRead::Kept, None, Vec::new(), true)]);
    }
    next
}

/// The work of the part the `.reset_if~` at `at` of `n` wraps (`level`)
/// with its reset at the tick `r` of its frame (§11.10, S-1228): first in
/// the stage `r`, before all the work the part has there (of a guard
/// inside it, its stages slower than its W too, run in the stage W); a
/// slower stage of the part, in a stage before, writes first and is reset
/// after. One that [`takes`] the array inside it the caller read (`dealt`)
/// copies it out after them, at the stage of the output of the part, in
/// each run of the `.up~` outside it (as [`when`] reads it; the review of
/// U3a, 3).
fn reset(n: &PlanNode, at: u32, r: Ratio, mut level: Level, dealt: &mut Option<u32>) -> Level {
    let nb = n.inside(at);
    let to = first_deal(n, nb).map_or(To::Value, To::Array);
    if let Some(op) = dealt.filter(|_| takes(n, at)).and_then(|from| copy(n, from, nb, to)) {
        *dealt = None;
        level.entry(ClockStage::Tick(bounds::reads_at(n.bounds[nb as usize].out))).or_default().push(op);
    }
    level.entry(ClockStage::Tick(r)).or_default().insert(0, Op::Reset { at });
    level
}

/// Whether the part the guard `guard` wraps is a burst (its output faster
/// than the `sample` of its frame), whose value [`when`] does not hold.
fn burst(guard: &PlanGuard) -> bool {
    guard.out.is_some_and(Ratio::faster_than_body)
}

/// The copy into `to` of the array of the boundary `from` a modifier with
/// `nb` boundaries inside it takes, by the window of `nb`; none when an
/// `.up~` between widens it (its arm copies it). Of [`when`] and [`reset`].
fn copy(n: &PlanNode, from: u32, nb: u32, to: To) -> Option<Op> {
    (!wider(n, from, nb)).then_some(Op::Deal { to, from, by: nb })
}

/// Whether the `.reset_if~` at `at` of `n` takes the array of a boundary
/// inside it ([`reset`]): an `.up~` outside it before the next that would
/// (a guard, a boundary that deals; the review of W7-10 U3a, 3: X).
fn takes(n: &PlanNode, at: u32) -> bool {
    let guard = n.guards.iter().map(|g| g.at).find(|&g| g > at);
    let before = |b: &&PlanBound| !b.deals && guard.is_none_or(|g| b.at < g);
    n.bounds.iter().filter(|b| b.at > at).take_while(before).any(|b| !b.ratio.slower_than_body())
}

/// Of the first modifier of `n` outside its place `at` that takes the
/// array of a boundary inside it (a guard, of a burst too, or a
/// `.reset_if~` that [`takes`] it), the count of the boundaries inside it ([`arm`]).
fn taker(n: &PlanNode, at: u32) -> Option<u32> {
    let takes = |&(a, m): &(u32, &PlanModifier)| {
        n.guards.iter().any(|g| g.at == a) || m.modifier == Modifier::ResetIf && takes(n, a)
    };
    (at + 1..).zip(&n.chain[at as usize + 1..]).find(takes).map(|(a, _)| n.inside(a))
}

/// Whether `op` or one in its groups and ops is one `of`.
fn writes(op: &Op, of: impl Fn(&Op) -> bool) -> bool {
    let mut makes = false;
    Op::walk(std::slice::from_ref(op), &mut |op| makes |= of(op));
    makes
}

/// The index of the first boundary of `n` from `from` out that deals.
fn first_deal(n: &PlanNode, from: u32) -> Option<u32> {
    (from..).zip(n.bounds.get(from as usize..).unwrap_or_default()).find(|b| b.1.deals).map(|b| b.0)
}

/// Whether `op` itself writes where the value of a part inside the boundary
/// `nb` goes: the value of the instance or the array of a boundary from `nb`
/// out (a run, a copy, the hold of a guard inside it).
fn outer(op: &Op, nb: u32) -> bool {
    op.makes_value()
        || matches!(*op, Op::Run { out: Out::Deal(b), .. } | Op::Hold { out: Out::Deal(b), .. }
            | Op::Deal { to: To::Array(b), .. } if b >= nb)
}

/// `op` with each op in it that writes where the value of the part the
/// guard `g` wraps goes ([`outer`] of the boundaries `nb` inside it) writing
/// its held output instead (§11.10).
fn held(op: Op, g: u32, nb: u32) -> Op {
    let all = |ops: Vec<Op>| ops.into_iter().map(|op| held(op, g, nb)).collect();
    let mine = outer(&op, nb);
    match op {
        Op::Run { body, .. } if mine => Op::Run { body, out: Out::Held(g) },
        Op::Deal { from, by, .. } if mine => Op::Deal { to: To::Held(g), from, by },
        Op::Hold { guard, .. } if mine => Op::Hold { guard, out: Out::Held(g) },
        Op::Each { bound, once, groups } => {
            Op::Each { bound, once, groups: groups.into_iter().map(|(y, ops)| (y, all(ops))).collect() }
        }
        Op::When { guard, cond, due, ops, advance } => Op::When { guard, cond, due, ops: all(ops), advance },
        op => op,
    }
}
