//! The twins of a `sample_tick()` alone in the condition of a modifier (W7-10 S1230/t; S-1230 (G); `twin_time.rs`): the condition and the one with the `at` of its clock (`time_at`), and
//! the condition and the port of that clock of a flow that holds the part (`time_port`), for the programs of fixed seeds. The seeds of the gate hold every form of `COVER_AT` and
//! `COVER_PORT`; the `heavy_` tests run more (`ONSA_FLOW_GEN=lo..hi` runs a range again). A twin holds in the interpreter and on the evaluator only where they read the time as §11.4
//! says (S-1230 (G)): the tests `..._hold_...` and `..._agree_...` are the ones that need it, and the tests of the mutants (a condition of another time, `% 3 == 1`) and of the forms
//! do not.

use super::twin::{Family, Maker, run};
use super::twin_tests::{check, heavy_seeds};
use super::twin_time::{make_at, make_port};
use super::twin_when_tests::{assert_covered, assert_held, interpreter_failures, shown};

const AT: Family = ("time_at_twins", make_at);
const PORT: Family = ("time_port_twins", make_port);

/// The seeds of the gate: chosen again when a change of the generator moves what they make and the table of what is covered breaks. Each gives a mutant that the asserts catch; the seeds
/// 2 13 55 (`at`) and 27 (`port`) are the ones where the time that a part stopped from outside reads is not the time of the frame of its tick (they differ before S-1230 (G)).
const GATE_AT: [u64; 5] = [2, 13, 55, 3, 12];
const GATE_PORT: [u64; 3] = [27, 26, 16];
/// The forms the seeds of the gate hold: every head, a `when~` and a `reset_if~` of the time, the three writings of the time (bare, with an `init` value, with a `block` value), every
/// shape of the part (a block, a block before it, a block after it, a boundary slower than W so that the condition is gathered, no `.up~` so that the part is slower than the body, the last
/// for `at` only), a `when~` and a `reset_if~` outside the block, both ratios; and for `at` a modifier inside the block as well. The seeds of the gate are few (the time of the gate); `port` holds
/// the shapes after the block and with the boundary slower than W, and the others are in the `heavy_` tests.
const COVER_AT: &str = "h_tk h_acc h_slot k_when k_reset t_plain t_init t_block s_block s_before s_after s_ring s_down out_when out_reset inside n_2 n_4";
const COVER_PORT: &str = "h_tk h_acc h_slot k_when k_reset t_plain t_init s_after s_ring out_when out_reset n_2 n_4";

fn forms(make: Maker, seeds: &[u64], cover: &str) {
    assert_covered(make, seeds, cover);
}

#[test]
fn the_gate_seeds_of_the_time_twins_hold_every_form_of_the_tables_of_what_is_covered() {
    forms(make_at, &GATE_AT, COVER_AT);
    forms(make_port, &GATE_PORT, COVER_PORT);
}

#[test]
fn the_time_alone_and_the_time_with_the_at_of_its_clock_hold_in_the_interpreter() {
    assert_held(make_at, &GATE_AT, false);
}

#[test]
fn the_time_alone_and_the_time_as_a_port_of_its_clock_hold_in_the_interpreter() {
    assert_held(make_port, &GATE_PORT, false);
}

#[test]
fn a_mutant_of_the_time_twins_is_caught_by_the_asserts_in_the_interpreter() {
    assert_held(make_at, &GATE_AT, true);
    assert_held(make_port, &GATE_PORT, true);
}

#[test]
fn the_time_twins_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(GATE_AT.to_vec(), AT));
    println!("{:?}", check(GATE_PORT.to_vec(), PORT));
}

#[test]
fn a_mutant_of_the_time_twins_is_caught_by_the_evaluator() {
    // The interpreter is not run on a mutant: the evaluator has to evaluate every test, and an assert fails in each program.
    for (seeds, family) in [(GATE_AT.to_vec(), AT), (GATE_PORT.to_vec(), PORT)] {
        let (s, bad) = run(seeds.clone(), family, true);
        let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
        assert_eq!((s.programs, caught), (seeds.len(), seeds.len()), "{bad:?}");
    }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_time_at_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make_at, heavy_seeds(500), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_time_port_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make_port, heavy_seeds(500), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_time_twin_mutants_in_the_interpreter() {
    // A mutant of a seed is caught in most programs, not all (a head with no state, such as `tk`, ignores a modifier, and a condition of another time may hold at the same ticks): about one in four is not (136 of the first 600 seeds for `at`, 142 for `port`), at most one in three.
    for make in [make_at as Maker, make_port] {
        let seeds = heavy_seeds(300);
        let (ran, bad) = interpreter_failures(make, seeds.clone(), true);
        let uncaught = bad.iter().filter(|m| m.contains("is not caught")).count();
        assert!(
            ran > 0 && uncaught == bad.len() && uncaught * 3 <= seeds.len(),
            "{uncaught} of {}: {}",
            seeds.len(),
            shown(&bad)
        );
    }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_time_twins() {
    println!("{:?}", check(heavy_seeds(200), AT));
    println!("{:?}", check(heavy_seeds(200), PORT));
}
