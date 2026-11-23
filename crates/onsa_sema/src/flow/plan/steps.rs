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
/// first: each op with its tag, the stage of the part it is of in that
/// frame (of the head, moved out of each `.down~` with it; of an op an arm
/// adds, the stage it puts it in). An op keeps the place of its stage among
/// those put in one stage, which `.reset_if~` reads ([`reset`], §11.10:
/// the slower stages write first). The entries have no tag.
type Level = BTreeMap<ClockStage, Vec<(ClockStage, Op)>>;

/// The entries and the read of the instance `n` of the callee whose table
/// is `g`: each stage x of the body of `g` (its slow stages, then `sample`)
/// runs, that of `g.out_stage` into the array of the innermost boundary
/// that deals, else as the value; then the arm of each boundary.
pub(super) fn table(n: &PlanNode, g: &FlowInfo) -> (Vec<Entry>, Read) {
    let first = (0u32..).zip(&n.bounds).find(|b| b.1.deals).map(|b| b.0);
    let out = |x| if Some(x) == g.out_stage { first.map_or(Out::Value, Out::Deal) } else { Out::None };
    let heads = g.stages.iter().copied().chain([ClockStage::SAMPLE]);
    let mut level: Level = heads.map(|x| (x, vec![(x, Op::Run { body: x, out: out(x) })])).collect();
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
            level = reset(n, at, r, level);
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
        let ops: Vec<Op> = ops.into_iter().map(|t| t.1).collect();
        let mut writes = false;
        Op::walk(&ops, &mut |op| {
            writes |= match *op {
                _ if op.makes_value() => true,
                Op::Run { out: Out::Deal(b), .. }
                | Op::Hold { out: Out::Deal(b), .. }
                | Op::Deal { to: To::Array(b), .. } => read == Read::Array(b) && read_at == Some(caller),
                // A reset of the array read, before it is read (§11.10).
                Op::Reset { at } | Op::Fire { at } => {
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
/// past a guard that holds a value: it ends there), after the writer of
/// its own, in each run j of that `.up~`. Of an `.up~`,
/// which gathers and deals nothing ([`bounds::bounds`]), the stages moved
/// to each stage of the frame in one [`Op::Each`], run each j at `sample`
/// and j = 0 alone at a slower one.
fn arm(n: &PlanNode, b: u32, bound: &PlanBound, level: Level, dealt: &mut Option<u32>) -> Level {
    let r = bound.ratio;
    if !r.slower_than_body() {
        let mut groups: BTreeMap<ClockStage, Vec<(ClockStage, Vec<Op>)>> = BTreeMap::new();
        let untag = |ops: Vec<(ClockStage, Op)>| ops.into_iter().map(|t| t.1).collect();
        level.into_iter().for_each(|(y, ops)| groups.entry(bounds::step(y, r)).or_default().push((y, untag(ops))));
        let each = |(s, groups)| (s, vec![(s, Op::Each { bound: b, once: s != ClockStage::SAMPLE, groups })]);
        return groups.into_iter().map(each).collect();
    }
    let mut next = Level::new();
    let moved = |ops: Vec<(ClockStage, Op)>| ops.into_iter().map(move |(t, op)| (bounds::step(t, r), op));
    level.into_iter().for_each(|(y, ops)| next.entry(bounds::step(y, r)).or_default().extend(moved(ops)));
    for &(input, q) in &bound.gathers {
        let from = n.ring_of(b as usize + 1, input).map_or(Feed::Arg, Feed::Ring);
        next.entry(q).or_default().push((q, Op::Ring { bound: b, input, from }));
    }
    if bound.deals {
        let into = dealt.filter(|&d| !wider(n, d, b)).map(|from| Op::Deal { to: To::Array(b), from, by: b });
        let to = (b + 1..).zip(&n.bounds[b as usize + 1..]).find(|c| c.1.deals).map(|c| c.0);
        // A guard outside it that holds a value (of a part that is not a burst) makes it in
        // its own frame ([`when`]): the window ends there.
        let held = n.guards.iter().find(|g| g.at > bound.at && !burst(g)).map(|g| inside(n, g));
        let wide = wider(n, b, to.into_iter().chain(held).min().unwrap_or(n.bounds.len() as u32));
        let out = wide.then(|| Op::Deal { to: to.map_or(To::Value, To::Array), from: b, by: b });
        let copies: Vec<Op> = into.into_iter().chain(out).collect();
        if !copies.is_empty() {
            let at = ClockStage::Tick(r);
            next.entry(at).or_default().extend(copies.into_iter().map(|op| (at, op)));
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
/// value of a part that is not a burst is held: each op that makes it
/// writes the held output instead ([`held`]), an array of a boundary inside
/// it the caller read too (`dealt`), then [`Op::Hold`] makes it; of a burst,
/// that array is copied into the array of the boundary just outside it or
/// the value, which [`Op::Hold`] holds. Each
/// stage slower than W keeps its tag in its own [`Op::When`] (where
/// `.reset_if~` goes between, [`reset`]).
fn when(n: &PlanNode, g: u32, guard: &PlanGuard, level: Level, dealt: &mut Option<u32>) -> Level {
    let (w, burst, nb) = (ClockStage::Tick(guard.w), burst(guard), inside(n, guard));
    // The array of a boundary inside it the caller read: of a burst copied where the
    // boundary just outside would (into its array, or the value), else held.
    let into_of = if burst { n.bounds.get(nb as usize).map_or(To::Value, |_| To::Array(nb)) } else { To::Held(g) };
    let read = dealt.take().filter(|&d| !wider(n, d, nb)).map(|from| (w, Op::Deal { to: into_of, from, by: nb }));
    let counted =
        level.keys().any(|&y| y < w) || n.bounds[..nb as usize].iter().any(|b| b.deals || !b.gathers.is_empty());
    let guarded = |cond, due, ops: Vec<(ClockStage, Op)>, advance| Op::When {
        guard: g,
        cond,
        due,
        ops: ops.into_iter().map(|t| if burst { t.1 } else { held(t.1, g) }).collect(),
        advance,
    };
    let (mut next, mut slow, mut own) = (Level::new(), Vec::new(), Vec::new());
    for (y, ops) in level {
        match y.cmp(&w) {
            std::cmp::Ordering::Less => slow.push((y, ops)),
            std::cmp::Ordering::Equal => own = ops,
            std::cmp::Ordering::Greater => {
                let advance = counted && y == ClockStage::SAMPLE;
                next.insert(y, vec![(y, guarded(CondRead::Kept, None, ops, advance))]);
            }
        }
    }
    // A burst dealt by the boundary just outside it is held in that array (§11.10).
    let into = |op: &Op| {
        matches!(*op, Op::Run { out: Out::Deal(b), .. } | Op::Hold { out: Out::Deal(b), .. }
            | Op::Deal { to: To::Array(b), .. } if b == nb)
    };
    let all = own.iter().chain(slow.iter().flat_map(|s| &s.1)).chain(&read);
    let all: Vec<&Op> = all.map(|t| &t.1).collect();
    let to = if burst && all.iter().any(|op| writes(op, into)) { Out::Deal(nb) } else { Out::Value };
    let makes = read.is_some() || to != Out::Value || all.iter().any(|op| writes(op, Op::makes_value));
    own.extend(read);
    let advance = counted && w == ClockStage::SAMPLE;
    let mut at_w = Vec::new();
    if slow.is_empty() {
        at_w.push((w, guarded(CondRead::Read, None, own, advance)));
    } else {
        // The read first, before any tag of a stage of the part.
        at_w.push((ClockStage::Init, guarded(CondRead::Read, None, Vec::new(), false)));
        at_w.extend(slow.into_iter().map(|(y, ops)| (y, guarded(CondRead::Local, Some(y), ops, false))));
        at_w.push((w, guarded(CondRead::Local, None, own, advance)));
    }
    if makes {
        at_w.push((w, Op::Hold { guard: g, out: to }));
    }
    next.insert(w, at_w);
    if counted && !next.contains_key(&ClockStage::SAMPLE) {
        let s = ClockStage::SAMPLE;
        next.insert(s, vec![(s, guarded(CondRead::Kept, None, Vec::new(), true))]);
    }
    next
}

/// The work of the part the `.reset_if~` at `at` of `n` wraps (`level`)
/// with its reset at the tick `r` of its frame (§11.10, the review of the
/// memo of W7-10, its high 1): at p0, in the stage `r` before the first op
/// of a stage as fast as `r` or faster, so that a slower stage at the same
/// place writes first and is reset after. When an op after p0 (in the
/// stage `r` or a faster one) runs work of a tick slower than `r` (a guard
/// moved it to its W, S-1209: [`Slower`]), the condition is read at p0
/// into its flag ([`Op::Arm`]), and the part is reset after that work: in
/// each list of ops after p0, of a stage, of a guard or of a run of an
/// `.up~`, after the last op that is or holds such work ([`Op::Fire`],
/// [`fire`]; the advisor's L, its stage 2, the rule of its chapter 3).
fn reset(n: &PlanNode, at: u32, r: Ratio, mut level: Level) -> Level {
    let (s, slower) = (ClockStage::Tick(r), Slower { n, at, r });
    let i = level.entry(s).or_default().iter().position(|t| t.0 >= s);
    let i = i.unwrap_or(level[&s].len());
    let from = |y| if y == s { i } else { 0 };
    let after = |(&y, ops): (&ClockStage, &Vec<(ClockStage, Op)>)| ops[from(y)..].iter().any(|t| slower.holds(&t.1));
    if !level.range(s..).any(after) {
        level.entry(s).or_default().insert(i, (s, Op::Reset { at }));
        return level;
    }
    for (&y, ops) in level.range_mut(s..) {
        let Some(last) = ops.iter().rposition(|t| slower.holds(&t.1)).filter(|&k| k >= from(y)) else { continue };
        ops[from(y)..].iter_mut().for_each(|t| fire(&slower, &mut t.1));
        // Its tag the later of `r` and that before it: the tags in their order.
        ops.insert(last + 1, (s.max(ops[last].0), Op::Fire { at }));
    }
    level.entry(s).or_default().insert(i, (s, Op::Arm { at }));
    level
}

/// The work of a tick slower than the tick `r` of the `.reset_if~` at `at`
/// of `n`, in the frame of the part it wraps (§11.10, S-1209): a guard's
/// stage `due` driven by its count, or a `.reset_if~` inside it, of a tick
/// slower than `r` when moved out of the boundaries between (their ratios
/// summed, not cut).
struct Slower<'a> {
    n: &'a PlanNode,
    at: u32,
    r: Ratio,
}

impl Slower<'_> {
    /// Whether `op` is such work.
    fn is(&self, op: &Op) -> bool {
        let (inner, k) = match *op {
            Op::When { guard, due: Some(ClockStage::Tick(y)), .. } => (self.n.guards[guard as usize].at, y),
            Op::Reset { at } | Op::Arm { at } | Op::Fire { at } => match self.n.chain[at as usize].reset {
                Some(k) => (at, k),
                None => return false,
            },
            _ => return false,
        };
        let between = self.n.bounds.iter().filter(|b| inner < b.at && b.at < self.at);
        i64::from(k.0) + between.map(|b| i64::from(b.ratio.0)).sum::<i64>() < i64::from(self.r.0)
    }

    /// Whether `op` is such work or one in its ops and groups is.
    fn holds(&self, op: &Op) -> bool {
        self.is(op)
            || match op {
                Op::Each { groups, .. } => groups.iter().flat_map(|g| &g.1).any(|op| self.holds(op)),
                Op::When { ops, .. } => ops.iter().any(|op| self.holds(op)),
                _ => false,
            }
    }
}

/// The [`Op::Fire`] of the `.reset_if~` of `slower` in the ops and the
/// groups of `op`, not such work itself: in each list, after the last op
/// that is or holds that work ([`reset`]).
fn fire(slower: &Slower, op: &mut Op) {
    let lists: Vec<&mut Vec<Op>> = match op {
        _ if slower.is(op) => return,
        Op::Each { groups, .. } => groups.iter_mut().map(|g| &mut g.1).collect(),
        Op::When { ops, .. } => vec![ops],
        _ => return,
    };
    for ops in lists {
        let Some(last) = ops.iter().rposition(|op| slower.holds(op)) else { continue };
        ops.iter_mut().for_each(|op| fire(slower, op));
        ops.insert(last + 1, Op::Fire { at: slower.at });
    }
}

/// Whether the part the guard `guard` wraps is a burst (its output faster
/// than the `sample` of its frame), whose value [`when`] does not hold.
fn burst(guard: &PlanGuard) -> bool {
    guard.out.is_some_and(Ratio::faster_than_body)
}

/// The count of the boundaries of `n` inside the guard `guard`: of the
/// boundary just outside it, its index.
fn inside(n: &PlanNode, guard: &PlanGuard) -> u32 {
    n.bounds.iter().filter(|b| b.at < guard.at).count() as u32
}

/// Whether `op` or one in its groups and ops is one `of`.
fn writes(op: &Op, of: impl Fn(&Op) -> bool) -> bool {
    let mut makes = false;
    Op::walk(std::slice::from_ref(op), &mut |op| makes |= of(op));
    makes
}

/// `op` with each op in it that makes the value of the instance writing the
/// held output of the guard `g` instead (§11.10): a run, a copy, the hold of
/// a guard inside it.
fn held(op: Op, g: u32) -> Op {
    let all = |ops: Vec<Op>| ops.into_iter().map(|op| held(op, g)).collect();
    match op {
        Op::Run { body, out: Out::Value } => Op::Run { body, out: Out::Held(g) },
        Op::Deal { to: To::Value, from, by } => Op::Deal { to: To::Held(g), from, by },
        Op::Hold { guard, out: Out::Value } => Op::Hold { guard, out: Out::Held(g) },
        Op::Each { bound, once, groups } => {
            Op::Each { bound, once, groups: groups.into_iter().map(|(y, ops)| (y, all(ops))).collect() }
        }
        Op::When { guard, cond, due, ops, advance } => Op::When { guard, cond, due, ops: all(ops), advance },
        op => op,
    }
}
