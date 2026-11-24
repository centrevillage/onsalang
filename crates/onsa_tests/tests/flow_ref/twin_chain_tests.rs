//! Chains made at random with no twin, and the forms that the break side found the evaluator wrong on (W7-10 (P)/t; `twin_chain.rs`): the
//! evaluator and the interpreter give the same outputs for the programs of fixed seeds. The seeds of the gate hold every form of `COVER`; the
//! `heavy_` test runs more (`ONSA_FLOW_GEN=lo..hi` runs a range again).

use super::twin::Family;
use super::twin_chain::{make, make_fixed};
use super::twin_tests::{check, heavy_seeds};
use super::twin_when_tests::assert_covered;

const CHAINS: Family = ("chains", make);
const FIXED: Family = ("fixed_forms", make_fixed);

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks.
/// 938: a condition gathered by two boundaries, whose ring the evaluator finds from the outermost (the break side of W7-10 (P), its 1).
const GATE: [u64; 5] = [0, 2, 6, 7, 938];
/// The forms the seeds of the gate hold: every head, the time alone as the condition of a `when~` or a `reset_if~`, also in a block that a `when~`
/// outside it stops (`f2_time_in_block_stopped`), a modifier inside a block and outside it, both kinds, a modifier before and after another.
const COVER: &str = "h_tk h_acc h_slot c_time f2_time_in_block_stopped in_block r_in_block r_has_when r_in_when r_has_up r_in_up \
    r_has_down r_in_down c_block c_sig c_at m_up2 m_down4 stacked";

#[test]
fn the_random_chains_of_the_gate_seeds_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(GATE.to_vec(), CHAINS));
}

#[test]
fn the_gate_seeds_of_the_random_chains_hold_every_form_of_the_table_of_what_is_covered() {
    assert_covered(make, &GATE, COVER);
}

/// The forms that killed the mutants M10 and M16 of the evaluator (they stay alive in the other tests of the gate).
#[test]
fn the_forms_that_killed_two_mutants_of_the_evaluator_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(vec![0, 1], FIXED));
}

/// The F2 forms: a `sample_tick()` in a modifier inside a block that a `when~` outside it stops reads the time kept at the last tick of the grid
/// of `sample / n` of the body that wrote it (§11.4, S-1230 (G)), not the time of the frame of its own tick, and not the time rounded to the ratio of the block.
#[test]
fn the_time_in_a_block_that_a_when_stops_is_read_alike_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(vec![2, 3], FIXED));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_chains() {
    println!("{:?}", check(heavy_seeds(600), CHAINS));
}
