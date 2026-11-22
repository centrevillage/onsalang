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
    let first = n.dealt_at();
    let out = |x| if Some(x) == g.out_stage { first.map_or(Out::Value, Out::Deal) } else { Out::None };
    let heads = g.stages.iter().copied().chain([ClockStage::SAMPLE]);
    let mut level: Level = heads.map(|x| (x, vec![Op::Run { body: x, out: out(x) }])).collect();
    let mut dealt = None;
    for (b, bound) in (0u32..).zip(&n.bounds) {
        level = arm(n, b, bound, level, &mut dealt);
    }
    let entries = level.into_iter().map(|(caller, ops)| {
        let mut read = false;
        Op::walk(&ops, &mut |op| read |= matches!(op, Op::Run { out: Out::Value, .. }));
        Entry { caller, read, ops }
    });
    (entries.collect(), dealt.map_or(Read::Run, Read::Array))
}

/// The work of the part the boundary `b` of `n` wraps (`level`) in the
/// stages of the frame around it. Of a `.down~`, each stage moved
/// ([`bounds::step`] is one to one), then the rings it writes, by input,
/// then the copy of the array of the boundary inside that last dealt
/// (`dealt`) at its tick. Of an `.up~`, which gathers and deals nothing
/// ([`bounds::bounds`]), the stages moved to each stage of the frame in
/// one [`Op::Each`], run each j at `sample` and j = 0 alone at a slower one.
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
        if let Some(from) = *dealt {
            next.entry(ClockStage::Tick(r)).or_default().push(Op::Deal { bound: b, from });
        }
        *dealt = Some(b);
    }
    next
}
