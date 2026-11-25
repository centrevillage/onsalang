//! The twins of the events of a flow (`twin_event.rs`, W7-11 U2-e2): for the programs of fixed seeds, `fa` and `fb` (a part in a named flow, a value moved into a `let`, the whole in a flow) give the same outputs on the
//! evaluator, a twin that is made different is caught by its asserts, and a `reset` gives back the first run. The interpreter is compared with the evaluator by the tests that wait for U2 (E0200 of the lowering, S-564).

use std::collections::BTreeSet;

use super::twin_event::{Ran, cover, covers, make, run};
use super::twin_tests::heavy_seeds;

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks.
const GATE: [u64; 37] = [
    0, 1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 17, 19, 20, 21, 22, 23, 24, 25, 26, 31, 33, 34, 36, 37, 38, 41, 47, 50, 52,
    54, 66, 81, 133, 156, 196, 308,
];

/// The seeds are run, and each program is evaluated whole: every test is evaluated, an assert held, and no program is left out.
fn check(seeds: &[u64]) -> Ran {
    assert!(!seeds.is_empty(), "no seed was run");
    let r = run(seeds.to_vec(), false, false);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert_eq!(r.programs, seeds.len(), "{r:?}");
    assert!(r.tests >= 3 * r.programs && r.asserts > 0 && r.evaluated == r.tests, "nothing was asserted: {r:?}");
    r
}

#[test]
fn the_twins_of_the_gate_seeds_agree_on_the_evaluator() {
    println!("{:?}", check(&GATE));
}

#[test]
fn the_gate_seeds_hold_every_form_every_wrap_and_the_move_into_a_let_of_each_form_that_has_one() {
    let got: BTreeSet<String> = GATE.iter().flat_map(|s| covers(*s)).collect();
    let missing: Vec<_> = cover().difference(&got).cloned().collect();
    assert!(missing.is_empty(), "the seeds of the gate do not hold {missing:?}: choose them again");
}

#[test]
fn a_twin_that_gives_one_more_is_caught_by_its_asserts_in_every_seed_of_the_gate() {
    let r = run(GATE.to_vec(), true, false);
    let missed: Vec<_> = GATE.iter().filter(|s| !r.bad.iter().any(|m| m.starts_with(&format!("seed {s}:")))).collect();
    assert!(missed.is_empty(), "the mutant is not caught in {missed:?}");
}

#[test]
fn every_program_of_the_gate_has_a_twin_that_is_written_another_way() {
    let same: Vec<_> = GATE.iter().filter(|s| make(**s, false).1.len() < 2).collect();
    assert!(same.is_empty(), "the twin of {same:?} is the program itself");
}

#[test]
fn the_twins_of_the_gate_seeds_agree_in_the_interpreter() {
    let r = run(GATE.to_vec(), false, true);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert!(r.lowered == r.programs && r.compared == r.tests && r.compared > 0, "not all were run again: {r:?}");
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_event_twins_on_the_evaluator() {
    println!("{:?}", check(&heavy_seeds(300)));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_first_seeds_hold_everything_and_these_are_the_ones_to_choose_the_gate_from() {
    let (mut left, mut chosen) = (cover(), Vec::new());
    for s in 0..600u64 {
        let tags = covers(s);
        if tags.iter().any(|t| left.contains(t)) {
            chosen.push(s);
            left.retain(|t| !tags.contains(t));
        }
    }
    println!("chosen {chosen:?}");
    assert!(left.is_empty(), "the first 600 seeds do not hold {left:?}");
}
