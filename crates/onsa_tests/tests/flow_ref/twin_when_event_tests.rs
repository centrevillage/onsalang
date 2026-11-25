//! The twins of the reads of an event and of a `when~` with an event (`twin_when_event.rs`, W7-11 U3/e): for the programs of fixed seeds, `fa` and `fb` give the same outputs on the evaluator, a twin that is made different is
//! caught by its asserts, and the interpreter is compared with the evaluator for the reads and for the programs with a `when~` of an event (S-563).

use std::collections::BTreeSet;

use super::twin_when_event::{Ran, cover, has_when, make, run, tag_of};

/// Two seeds for each form (the form of a seed is its number modulo the forms, the numbers to compare with come from the seed).
const GATE: [u64; 20] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];

fn check(seeds: &[u64]) -> Ran {
    let r = run(seeds.to_vec(), false, false);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert_eq!(r.programs, seeds.len(), "{r:?}");
    assert!(r.tests >= r.programs && r.evaluated == r.tests, "nothing was asserted: {r:?}");
    r
}

fn seeds(when: bool) -> Vec<u64> {
    GATE.iter().copied().filter(|s| has_when(*s) == when).collect()
}

#[test]
fn the_twins_of_the_reads_and_the_levels_of_an_event_agree_on_the_evaluator() {
    println!("{:?}", check(&GATE));
}

#[test]
fn the_gate_seeds_hold_every_form() {
    let got: BTreeSet<&str> = GATE.iter().map(|s| tag_of(*s)).collect();
    assert_eq!(got, cover());
}

#[test]
fn a_twin_that_gives_one_more_is_caught_by_its_asserts_in_every_seed_of_the_gate() {
    let r = run(GATE.to_vec(), true, false);
    let missed: Vec<_> = GATE.iter().filter(|s| !r.bad.iter().any(|m| m.starts_with(&format!("seed {s}:")))).collect();
    assert!(missed.is_empty(), "the mutant is not caught in {missed:?}");
}

#[test]
fn every_program_has_a_twin_that_is_written_another_way() {
    let same: Vec<_> = GATE.iter().filter(|s| make(**s, false).matches("fb").count() == 0).collect();
    assert!(same.is_empty(), "{same:?}");
}

#[test]
fn the_twins_of_the_reads_agree_in_the_interpreter() {
    let r = run(seeds(false), false, true);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert!(r.lowered == r.programs && r.compared == r.tests && r.compared > 0, "not all were run again: {r:?}");
}

#[test]
fn the_twins_of_a_when_of_an_event_agree_in_the_interpreter() {
    let r = run(seeds(true), false, true);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert!(r.lowered == r.programs && r.compared == r.tests && r.compared > 0, "not all were run again: {r:?}");
}
