//! The twins of a `reset_if~` of an event (`twin_reset_event.rs`, W7-11 U2r/e): for the programs of fixed seeds, `fa` and `fb` give the same outputs on the evaluator, a twin that is made different is caught by its
//! asserts, and the interpreter is compared with the evaluator by the test that waits for U2r (E0200 of the lowering, S-562).

use std::collections::BTreeSet;

use super::twin_reset_event::{Ran, cover, make, run, tag_of};

/// Three seeds for each form (the form of a seed is its number modulo the forms, the numbers to compare with come from the seed).
const GATE: [u64; 27] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26];

fn check(seeds: &[u64]) -> Ran {
    let r = run(seeds.to_vec(), false, false);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert_eq!(r.programs, seeds.len(), "{r:?}");
    assert!(r.tests >= r.programs && r.evaluated == r.tests, "nothing was asserted: {r:?}");
    r
}

#[test]
fn the_twins_of_a_reset_by_an_event_agree_on_the_evaluator() {
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
fn the_twins_of_the_gate_seeds_agree_in_the_interpreter() {
    let r = run(GATE.to_vec(), false, true);
    assert!(r.bad.is_empty(), "{}", r.bad.join("\n\n"));
    assert!(r.lowered == r.programs && r.compared == r.tests && r.compared > 0, "not all were run again: {r:?}");
}
