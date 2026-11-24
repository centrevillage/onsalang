//! The twins of a modifier inside a block (W7-10 U3ae/t; S-1209): `x.when~(a).up~(N).down~(N)` and a named flow that holds the
//! part inside the block, `w~(a).up~(N).down~(N)`, for the programs of fixed seeds (`twin_wrap.rs`). The seeds of the gate hold
//! every form of `COVER`; the `heavy_` tests run more (`ONSA_FLOW_GEN=lo..hi` runs a range again).
//!
//! Three things hold them. The checker passes every program and the interpreter holds its asserts (a twin that the interpreter
//! does not hold is a failure of the interpreter or of the generator), and a mutant of the twin (a condition that `fb` passes
//! the other way round) is caught by the asserts: both run today. The evaluator gives what the interpreter gives (`twin::run`:
//! it evaluates every test and the interpreter is compared with it), since W7-10 U3ae.

use super::twin::{Family, run};
use super::twin_tests::{check, heavy_seeds};
use super::twin_when_tests::{assert_covered, assert_held, interpreter_failures, shown};
use super::twin_wrap::make;

const WRAP: Family = ("wrap_twins", make);

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks. Each gives a
/// mutant that the asserts catch.
const GATE: [u64; 15] = [0, 1, 2, 3, 4, 5, 8, 9, 11, 14, 19, 27, 31, 32, 118];
/// The forms the seeds of the gate hold: every head, both ratios, a block inside a block, a modifier outside, and for each head
/// one of each of the last two; one to three modifiers inside, both kinds and the four orders of two, and every kind of condition
/// (a signal and its opposite, a `block` and an `init` value, a signal slower than the clock, a `block` value with an `at`).
const COVER: &str = "h_slot h_tk h_acc h_lp n_2 n_4 nest out_mod in_1 in_2 in_3 in_when in_reset when_reset reset_when when_when \
    reset_reset c_sig c_not c_block c_init c_sig_slow c_at_sample c_at_slow nest_slot nest_tk nest_acc nest_lp out_slot out_tk out_acc out_lp \
    nest_out nest_n4";

#[test]
fn the_flows_of_the_gate_seeds_pass_the_checker_and_the_twins_hold_in_the_interpreter() {
    assert_held(make, &GATE, false);
}

#[test]
fn the_gate_seeds_hold_every_form_of_the_table_of_what_is_covered() {
    assert_covered(make, &GATE, COVER);
}

#[test]
fn a_mutant_of_the_twin_is_caught_by_its_asserts_in_the_interpreter() {
    assert_held(make, &GATE, true);
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_wrap_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make, heavy_seeds(500), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_wrap_mutants_in_the_interpreter() {
    // A mutant of a seed is caught in most programs, not all (a head with no state, such as `tk`, ignores a modifier, and a
    // condition that `fb` negates may hold in the same frames in the grid): about one in five is not (184 of the first 1000), at most one in four.
    let seeds = heavy_seeds(300);
    let (ran, bad) = interpreter_failures(make, seeds.clone(), true);
    let uncaught = bad.iter().filter(|m| m.contains("is not caught")).count();
    assert!(
        ran > 0 && uncaught == bad.len() && uncaught * 4 <= seeds.len(),
        "{uncaught} of {}: {}",
        seeds.len(),
        shown(&bad)
    );
}

#[test]
fn the_twins_of_a_block_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(GATE.to_vec(), WRAP));
}

#[test]
fn a_mutant_of_the_twin_of_a_block_is_caught_by_the_evaluator() {
    // The interpreter is not run on a mutant: the evaluator has to evaluate every test, and an assert fails in each program.
    let (s, bad) = run(GATE.to_vec(), WRAP, true);
    let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
    assert_eq!((s.programs, caught), (GATE.len(), GATE.len()), "{bad:?}");
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_wrap_twins() {
    println!("{:?}", check(heavy_seeds(200), WRAP));
}
