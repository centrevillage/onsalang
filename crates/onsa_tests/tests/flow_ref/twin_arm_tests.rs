//! The twins of a chain of `when~` and `reset_if~` on a delay that is the object of a `match~` whose binding a slower flow gathers
//! (W7-10 close/t; `twin_arm.rs`). The checker passes every program, the interpreter holds the asserts of the twins and a mutant
//! of each is caught by them, and the evaluator gives what the interpreter gives (`twin::run`). The evaluator once evaluated such a
//! chain twice in a frame, so a `when~` with a `reset_if~` of a slow tick inside it counted its ticks twice; the seeds of the gate
//! hold that form (`slow_in_when`, at least three of them: the ones that a change of the evaluator is tried on).

use super::twin::Family;
use super::twin_arm::{arm_count, make_arm};
use super::twin_tests::{check, heavy_seeds};
use super::twin_when_tests::{assert_covered, assert_held, interpreter_failures, shown};

const ARM: Family = ("arm_twins", make_arm);

/// The seeds of the gate: the case of the wrap `w`, the head `h` and the chain `i` is `w * 3 * 399 + h * 399 + i`; an even seed has
/// the mutant that negates a condition, an odd one the mutant that does not use the chain. Chosen again when `ARM_COVER` breaks or
/// a mutant is not caught. The four that hold `slow_in_when`, the form of the finding: 44 is `prev~(xv).reset_if~(c4).when~(true)`,
/// 449 `delay~` with `reset_if~(c8).when~(cb)`, 2088 `vdelay~` with `when~(c).reset_if~(c4).when~(true)` in a `par~` and 1241 `prev~`
/// with `reset_if~(c4).when~(true)` in a `par~`.
const ARM_GATE: [u64; 8] = [44, 449, 2088, 1241, 400, 802, 10, 83];
const ARM_COVER: &str = "h_prev h_delay h_vdelay a_match a_par len_1 len_2 len_3 slow_in_when r_slow4 r_slow8 w_sig w_block w_true \
    r_sig r_block reset_then_when when_then_reset";

#[test]
fn the_arm_twins_of_the_gate_hold_in_the_interpreter_and_the_seeds_hold_every_form() {
    assert_held(make_arm, &ARM_GATE, false);
    assert_covered(make_arm, &ARM_GATE, ARM_COVER);
    let slow = ARM_GATE.iter().filter(|s| make_arm(**s, false).1.contains("slow_in_when")).count();
    assert!(slow >= 3, "{slow} seeds of the gate hold a slow reset_if~ inside a when~: choose them again");
}

#[test]
fn a_mutant_of_the_arm_twin_is_caught_by_its_asserts_in_the_interpreter() {
    assert_held(make_arm, &ARM_GATE, true);
}

#[test]
fn the_arm_twins_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(ARM_GATE.to_vec(), ARM));
}

#[test]
fn a_mutant_of_the_arm_twin_is_caught_by_the_evaluator() {
    let (s, bad) = super::twin::run(ARM_GATE.to_vec(), ARM, true);
    let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
    assert_eq!((s.programs, caught), (ARM_GATE.len(), ARM_GATE.len()), "{bad:?}");
}

/// Every eleventh case of the matrix (11 is prime to the counts of the wraps, the heads and the chains, so all of them come), or the
/// seeds of `ONSA_FLOW_GEN` (`0..2394` is the matrix, about two minutes with the evaluator).
fn seeds() -> Vec<u64> {
    if std::env::var_os("ONSA_FLOW_GEN").is_some() { heavy_seeds(0) } else { (0..arm_count()).step_by(11).collect() }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_arm_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make_arm, seeds(), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_arm_mutants_in_the_interpreter() {
    // A mutant is caught in most cases, not all (a chain that a caller's condition does not show: at most one in five is not).
    let seeds = seeds();
    let (ran, bad) = interpreter_failures(make_arm, seeds.clone(), true);
    let uncaught = bad.iter().filter(|m| m.contains("is not caught")).count();
    assert!(
        ran > 0 && uncaught == bad.len() && uncaught * 5 <= seeds.len(),
        "{uncaught} of {}: {}",
        seeds.len(),
        shown(&bad)
    );
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_arm_twins() {
    println!("{:?}", check(seeds(), ARM));
}
