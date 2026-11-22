//! The boundaries of a chain of modifiers (§11.9, §11.10, S-1207, S-1214):
//! each `.down~(N)` and `.up~(N)` runs the whole part on its left as one
//! part, so the ports of that part are those of the head moved by the
//! ratios inside it, and it gathers and deals at them by the rule of one
//! `.down~` (§11.9). The one place of the judgement (D-15): the check of
//! E0816 and the plan ([`PlanNode::bounds`]) read it.

use super::*;
use crate::def::FlowDef;

/// The exponent of a declared clock (`sample * 2^k`); none of a parameter
/// kind and of a clock in error.
fn exponent(c: Clock) -> Option<Ratio> {
    match c {
        Clock::Tick(k) => Some(k),
        _ => None,
    }
}

/// The stage `s` of the caller of a part, moved out of a boundary of the
/// ratio `r` (§11.9): `Tick(min(s + r, 0))`, a stage faster than the
/// `sample` of its own caller being of that `sample` (an `.up~` runs it
/// there 2^r times); `init` and `block` as they are. The one rule of it.
pub(in crate::flow) fn step(s: ClockStage, r: Ratio) -> ClockStage {
    match s {
        ClockStage::Tick(k) => ClockStage::Tick(Ratio(k.0.saturating_add(r.0).min(0))),
        s => s,
    }
}

/// The boundaries of the chain `chain` of an instance of `f`, inner first
/// ([`PlanBound`]): of each modifier with a ratio (not `.when~` and
/// `.reset_if~`), the ports of the part it wraps, the inputs it gathers
/// with the stage of the ring, and whether it deals; no stage, which the
/// walk of the table adds. O(modifiers × inputs).
pub(in crate::flow) fn bounds<'a>(chain: impl IntoIterator<Item = &'a PlanModifier>, f: &FlowDef) -> Vec<PlanBound> {
    let mut ins: Vec<Option<Ratio>> = f.inputs.iter().map(|i| exponent(i.caller_clock())).collect();
    let mut out = exponent(f.out_clock);
    let mut list = Vec::new();
    for (at, m) in (0u32..).zip(chain) {
        // SPEC-GAP(S-1209): `.when~` and `.reset_if~` are no boundary; with `.up~`
        // in the chain too, the E0816 of a boundary that gathers comes first.
        let Some(r) = m.ratio else { continue };
        let fast = |k: Option<Ratio>| k.filter(|k| r.slower_than_body() && k.faster_than_body());
        let gathers = (0u32..).zip(&ins).filter_map(|(i, &k)| fast(k).map(|k| (i, step(ClockStage::Tick(k), r))));
        let gathers = gathers.collect();
        list.push(PlanBound { at, ratio: r, ins: ins.clone(), out, gathers, deals: fast(out).is_some() });
        let moved = |k: Option<Ratio>| k.map(|k| Ratio(k.0.saturating_add(r.0)));
        ins.iter_mut().for_each(|k| *k = moved(*k));
        out = moved(out);
    }
    list
}
