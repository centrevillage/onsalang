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

/// The work of a part in each stage of the frame it is called in, slowest first.
type Level = BTreeMap<ClockStage, Vec<Op>>;

/// The entries and the read of the instance `n` of the callee whose table
/// is `g`: each stage x of the body of `g` (its slow stages, then `sample`)
/// runs, that of `g.out_stage` into the array of the innermost boundary
/// that deals, else as the value; then the arm of each boundary.
pub(super) fn table(n: &PlanNode, g: &FlowInfo) -> (Vec<Entry>, Read) {
    let first = (0u32..).zip(&n.bounds).find(|b| b.1.deals).map(|b| b.0);
    let out = |x| if Some(x) == g.out_stage { first.map_or(Out::Value, Out::Deal) } else { Out::None };
    let heads = g.stages.iter().copied().chain([ClockStage::SAMPLE]);
    let mut level: Level = heads.map(|x| (x, vec![Op::Run { body: x, out: out(x) }])).collect();
    let mut dealt = None;
    for (b, bound) in (0u32..).zip(&n.bounds) {
        level = arm(n, b, bound, level, &mut dealt);
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
                Op::Run { out: Out::Value, .. } | Op::Deal { to: To::Value, .. } => true,
                Op::Run { out: Out::Deal(b), .. } | Op::Deal { to: To::Array(b), .. } => {
                    read == Read::Array(b) && read_at == Some(caller)
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
/// next that deals or the value when an `.up~` widens that window, after
/// the writer of its own, in each run j of that `.up~`. Of an `.up~`,
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
    for &(input, q) in &bound.gathers {
        let from = n.ring_of(b as usize + 1, input).map_or(Feed::Arg, Feed::Ring);
        next.entry(q).or_default().push(Op::Ring { bound: b, input, from });
    }
    if bound.deals {
        let into = dealt.filter(|&d| !wider(n, d, b)).map(|from| Op::Deal { to: To::Array(b), from, by: b });
        let to = (b + 1..).zip(&n.bounds[b as usize + 1..]).find(|c| c.1.deals).map(|c| c.0);
        let wide = wider(n, b, to.unwrap_or(n.bounds.len() as u32));
        let out = wide.then(|| Op::Deal { to: to.map_or(To::Value, To::Array), from: b, by: b });
        let copies: Vec<Op> = into.into_iter().chain(out).collect();
        if !copies.is_empty() {
            next.entry(ClockStage::Tick(r)).or_default().extend(copies);
        }
        *dealt = Some(b);
    }
    next
}
