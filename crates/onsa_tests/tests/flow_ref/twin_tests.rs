//! The twins of `if~` (W7-20 U1): `fa` with `if~` and `fb` written as §11.5 defines it (each branch in a `let` before, then a
//! plain `if` that selects) give the same outputs, for the programs of fixed seeds, on the evaluator and in the interpreter.
//! The gate has 8 seeds and checks that they hold every form of `COVER`; the `heavy_` test runs 200 (or `ONSA_FLOW_GEN=lo..hi`).

use std::collections::BTreeSet;

use super::twin::{Stats, make, run};

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks. A tag is of
/// what the program holds (a condition that a guard replaces gives none).
const GATE: [u64; 8] = [1, 4, 8, 9, 12, 84, 142, 149];
/// The forms the seeds of the gate hold: chains of each length, a chain in a chain, a guarded division, a state in the first
/// condition, every wrap, and the kinds of branch and condition (`par~`, a delay with a start, `block` and `init`, a `par~` index).
const COVER: &str = "chain2 chain3 chain4 nested guard state_cond wrap_direct wrap_let wrap_twice wrap_half wrap_prev \
    wrap_delay wrap_par delay_init prev_init scale shift ifnest par inst guarded init_in block_div ki_gt n_gt or idx_div \
    shift_idx acc_idx idx_k";
const FAMILY: &str = "if_twins";

/// The seeds run, and what they came to: nothing is run without a failure, and what the generator made is all evaluated,
/// printed and run again (the numbers of the evaluator and of the interpreter are the same, and are not 0).
fn check(seeds: Vec<u64>) -> Stats {
    assert!(!seeds.is_empty(), "no seed was run");
    let (s, bad) = run(seeds.clone(), FAMILY, false);
    assert!(bad.is_empty(), "{}", bad.join("\n\n"));
    assert_eq!(s.programs, seeds.len(), "{s:?}");
    assert!(s.tests >= s.programs && s.asserts > 0 && s.compared_asserts > 0, "nothing was asserted: {s:?}");
    assert_eq!((s.evaluated, s.compared), (s.tests, s.tests), "a test was not evaluated or not compared: {s:?}");
    s
}

#[test]
fn the_twins_of_the_gate_seeds_agree_on_the_evaluator_and_in_the_interpreter() {
    let s = check(GATE.to_vec());
    println!("{s:?}");
}

#[test]
#[should_panic(expected = "no seed was run")]
fn a_run_of_no_seed_fails() {
    check(Vec::new());
}

#[test]
fn the_gate_seeds_hold_every_form_of_the_table_of_what_is_covered() {
    let held: BTreeSet<&str> = GATE.iter().flat_map(|s| make(*s, false).1).collect();
    let missing: Vec<_> = COVER.split_whitespace().filter(|t| !held.contains(t)).collect();
    assert!(missing.is_empty(), "the seeds of the gate do not hold {missing:?}: choose them again");
}

#[test]
fn a_twin_that_selects_the_next_branch_is_caught_in_every_seed_of_the_gate() {
    // `rot` makes `fb` select the branch after the one `fa` takes: the asserts of the twins have to fail (the interpreter is
    // not run on the mutant).
    let (s, bad) = run(GATE.to_vec(), FAMILY, true);
    let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
    assert_eq!((s.programs, caught), (GATE.len(), GATE.len()), "{bad:?}");
}

/// The seeds of `heavy_`: `ONSA_FLOW_GEN=<lo>..<hi>` runs a range again (what a failure tells how to).
fn heavy_seeds() -> Vec<u64> {
    let Ok(range) = std::env::var("ONSA_FLOW_GEN") else { return (0..200).collect() };
    let (lo, hi) = range.split_once("..").expect("ONSA_FLOW_GEN is <lo>..<hi>");
    (lo.parse().expect("a number")..hi.parse().expect("a number")).collect()
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_if_twins() {
    let s = check(heavy_seeds());
    println!("{s:?}");
}
