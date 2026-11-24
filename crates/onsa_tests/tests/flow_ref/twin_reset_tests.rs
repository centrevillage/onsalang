//! The twins of `reset_if~` (W7-10 U2e/t; S-1209): `X.reset_if~(false)` and `X.when~(true)` put in anywhere, a condition slower
//! than W and the time, `reset_if~(a).reset_if~(b)` and `reset_if~(a || b)`, for the programs of fixed seeds (`twin_reset.rs`).
//! The seeds of the gate hold every form of `COVER`; the `heavy_` tests run more (`ONSA_FLOW_GEN=lo..hi` runs a range again).
//!
//! Three things hold them. The checker passes every program and the interpreter holds its asserts (a twin that the interpreter
//! does not hold is a failure of the interpreter or of the generator), and a mutant of each twin is caught by the asserts: both
//! run today. The evaluator gives what the interpreter gives (`twin::run`: it evaluates every test and the interpreter is
//! compared with it): these wait for the evaluator to have a modifier inside a block and a `when~` of a burst under an `.up~` (W7-10 U3ae).
//! The checker and the interpreter pass the programs of every seed once U3a is in (the tests that run them are marked `W7-10 U3a` until then).

use super::twin::{Family, run};
use super::twin_reset::{chains, exotic_count, make, make_exotic};
use super::twin_tests::{check, heavy_seeds};
use super::twin_when_tests::{analysis, assert_covered, assert_held, interpreter_failures, shown};

const RESET: Family = ("reset_twins", make);
const EXOTIC: Family = ("reset_exotic", make_exotic);

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks. Each gives a
/// mutant that the asserts catch. The forms the breaker of U2e found the evaluator wrong on (a head with a `when~` inside and a
/// `sample_tick()` condition, `h_outer_tick`; `sample_tick()` at a W slower than `sample`, `c_tick_slow`) are in `COVER`. W7-10 U3a/t2
/// chose the seeds again: the twin `slowc` is not made inside a block (a `sample_tick()` there is gathered, and a slower value is read
/// at its own tick), and the twin `atid` was added.
const GATE: [u64; 11] = [339, 1934, 46, 1336, 2426, 177, 17, 117, 20, 25, 87];
/// The seeds of the twin `atid` at a place inside a block (`at_blk`), as in twin_when_tests.rs: they fail until U3a keeps an `at`
/// on a parameter kind from making a ring.
const AT_BLOCK: [u64; 3] = [95, 194, 247];
/// The forms the seeds of the gate hold: every head (a slow stage that writes a field, a slow input, the time as the input, a
/// burst, a head with a `when~` of its own inside whose part has a slow input: `h_outer`, with a `sample_tick()` condition:
/// `h_outer_tick`), the three twins, a `when~` inside and outside a `reset_if~` (also with a slow head), a `.up~` and a `.down~`
/// inside and outside it, two and three `reset_if~`, the kinds of condition of a `reset_if~` (a value at W, a `block` or `init`
/// value, a signal slower than W, a `block` value `at` a slower clock, the time alone: `==` and `>=`, at W of `sample` and slower)
/// and of the one put in (a literal, a `block` or `init` value, `at`), a condition slower than W under a `when~`, the places the
/// one is put in at, the rates.
const COVER: &str = "h_slot h_sl h_sltk h_tk h_acc h_lp h_dws h_mk2 h_mk4 h_outer h_outer_tick k_rid k_slowc k_rmerge r_1 r_2 \
    r_3 r_has_when r_slow_has_when r_in_when r_has_up r_in_up r_has_down r_in_down r_has_two_when c_at c_slower c_slowk c_tick \
    c_tick_eq c_tick_ge c_tick_slow c_tick_fast c_block c_init c_lit c_not c_and c_or f_lit f_block f_init f_both f_at t_lit \
    t_block t_init t_both t_or_sig ins_front ins_mid ins_end ins_two double_when m_down2 m_down4 m_down8 m_up2 stacked o_plain \
    o_burst o_slow w_slow w_pos w_p r_in_block blk burst_up k_atid c_at_sample";
/// The seeds of the gate for the matrix of `exotic`, and what they hold: the forms of the breaker's two highs (a state given back
/// before a slow stage wrote, a deal array read before it was given back) and the head with a `when~` inside.
const EXOTIC_GATE: [u64; 6] = [344, 527, 1098, 1404, 1779, 2082];
const EXOTIC_COVER: &str = "h_tk h_slot h_sl h_mk2 h_mk4 h_outer r_1 r_2 r_3 r_has_when r_slow_has_when r_in_when r_has_up r_in_up r_has_down \
    r_in_down r_has_two_when r_deal_up f_block t_block o_plain o_burst o_slow ins_front ins_mid ins_end len_3 len_4 r_in_block";

#[test]
fn the_flows_of_the_gate_seeds_pass_the_checker_and_the_twins_hold_in_the_interpreter() {
    assert_held(make, &GATE, false);
    assert_held(make_exotic, &EXOTIC_GATE, false);
}

#[test]
fn the_gate_seeds_hold_every_form_of_the_table_of_what_is_covered() {
    assert_covered(make, &GATE, COVER);
    assert_covered(make_exotic, &EXOTIC_GATE, EXOTIC_COVER);
    assert_covered(make, &AT_BLOCK, "k_atid c_at_sample at_blk");
}

#[test]
fn a_value_of_a_parameter_kind_with_an_at_inside_a_block_is_the_value_in_the_interpreter() {
    assert_held(make, &AT_BLOCK, false);
    assert_held(make, &AT_BLOCK, true);
}

#[test]
fn a_mutant_of_each_twin_is_caught_by_its_asserts_in_the_interpreter() {
    assert_held(make, &GATE, true);
    assert_held(make_exotic, &EXOTIC_GATE, true);
}

/// Every chain of up to `len` modifiers over the heads: the checker passes (and lowers) every one, a `reset_if~` with an `.up~` and
/// then a `.down~` outside it and a `when~` of a burst with an `.up~` outside it too (they were E0200 until U3a). How many
/// there are, and what is wrong.
fn matrix(len: usize) -> (usize, Vec<String>) {
    let (mut made, mut wrong) = (0, Vec::new());
    for (what, src) in chains(len) {
        match analysis(&src) {
            Ok(()) => made += 1,
            Err(e) => wrong.push(format!("{what}: {}", e.lines().next().unwrap_or_default())),
        }
    }
    (made, wrong)
}

#[test]
fn the_checker_passes_every_chain_of_up_to_three_modifiers_the_forms_that_u2b_stopped_too() {
    let (made, wrong) = matrix(3);
    assert!(wrong.is_empty() && made > 260, "{made} made: {}", wrong.join("\n"));
}

#[test]
#[ignore = "W7-10 U3ae: S-1209"]
fn the_twins_of_reset_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(GATE.to_vec(), RESET));
    println!("{:?}", check(EXOTIC_GATE.to_vec(), EXOTIC));
}

#[test]
#[ignore = "W7-10 U3ae: S-1209"]
fn a_mutant_of_a_twin_of_reset_is_caught_by_the_evaluator() {
    // The interpreter is not run on a mutant: the evaluator has to evaluate every test, and an assert fails in each program.
    for (family, seeds) in [(RESET, GATE.to_vec()), (EXOTIC, EXOTIC_GATE.to_vec())] {
        let (s, bad) = run(seeds.clone(), family, true);
        let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
        assert_eq!((s.programs, caught), (seeds.len(), seeds.len()), "{bad:?}");
    }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_reset_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make, heavy_seeds(500), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_reset_mutants_in_the_interpreter() {
    // A mutant of a seed is caught in most programs, not all (a head with no state ignores a `reset_if~` that always holds, and
    // the twin of `rmerge` with `&&` differs only where the two conditions differ): at most one in four is not.
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
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_reset_exotic_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make_exotic, 0..exotic_count(), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_checker_passes_every_chain_of_up_to_four_modifiers() {
    let (made, wrong) = matrix(4);
    assert!(wrong.is_empty() && made > 1100, "{made} made: {:?}", &wrong[..wrong.len().min(5)]);
}

#[test]
#[ignore = "W7-10 U3ae: S-1209"]
fn many_reset_twins_on_the_evaluator() {
    // Becomes `heavy_reset_twins` (the gate item `heavy` runs it) when the evaluator runs the modifiers inside a block and
    // the `when~` of a burst under an `.up~` (W7-10 U3ae).
    println!("{:?}", check(heavy_seeds(200), RESET));
    println!("{:?}", check((0..exotic_count()).collect(), EXOTIC));
}
