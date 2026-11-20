//! The twins of `if~` (W7-20 U1): `fa` with `if~` and `fb` written as §11.5 defines it (each branch in a `let` before, then a
//! plain `if` that selects) give the same outputs, for the programs of fixed seeds, on the evaluator and in the interpreter.
//! The gate has 8 seeds and checks that they hold every form of `COVER`; the `heavy_` test runs 200 (or `ONSA_FLOW_GEN=lo..hi`).

use std::collections::BTreeSet;

use super::twin::{Family, Stats, make, run};
use super::twin_match;

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks. A tag is of
/// what the program holds (a condition that a guard replaces gives none).
const GATE: [u64; 8] = [327, 380, 409, 3621, 4009, 4975, 5372, 5904];
/// The forms the seeds of the gate hold: chains of each length, a chain in a chain, a guarded division, a state in the first
/// condition, every wrap, and the kinds of branch and condition (`par~`, a delay with a start, `block` and `init`, a `par~` index,
/// a `match~`, also in a `par~`).
const COVER: &str = "chain2 chain3 chain4 nested guard state_cond wrap_direct wrap_let wrap_twice wrap_half wrap_prev \
    wrap_delay wrap_par delay_init prev_init scale shift ifnest par inst guarded init_in block_div ki_gt n_gt or idx_div \
    shift_idx acc_idx idx_k match_in_if par_match_in_if";
const IF: Family = ("if_twins", make);
const MATCH: Family = ("match_twins", twin_match::make);

/// The seeds run, and what they came to: nothing is run without a failure, and what the generator made is all evaluated,
/// printed and run again (the numbers of the evaluator and of the interpreter are the same, and are not 0).
fn check(seeds: Vec<u64>, family: Family) -> Stats {
    assert!(!seeds.is_empty(), "no seed was run");
    let (s, bad) = run(seeds.clone(), family, false);
    assert!(bad.is_empty(), "{}", bad.join("\n\n"));
    assert_eq!(s.programs, seeds.len(), "{s:?}");
    assert!(s.tests >= s.programs && s.asserts > 0 && s.compared_asserts > 0, "nothing was asserted: {s:?}");
    assert_eq!((s.evaluated, s.compared), (s.tests, s.tests), "a test was not evaluated or not compared: {s:?}");
    s
}

#[test]
fn the_twins_of_the_gate_seeds_agree_on_the_evaluator_and_in_the_interpreter() {
    let s = check(GATE.to_vec(), IF);
    println!("{s:?}");
}

#[test]
#[should_panic(expected = "no seed was run")]
fn a_run_of_no_seed_fails() {
    check(Vec::new(), IF);
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
    let (s, bad) = run(GATE.to_vec(), IF, true);
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
    let s = check(heavy_seeds(), IF);
    println!("{s:?}");
}

const MATCH_GATE: [u64; 13] = [63, 101, 303, 426, 657, 1078, 1678, 1680, 2390, 2429, 2448, 2896, 2944];
/// The forms of the `match~` the seeds hold: the kinds of scrutinee and their clocks, the patterns, the guards (what they read,
/// and a clock for each arm), the kinds of body (an `if~`, a `match~` and a `par~` of them in an arm), and every wrap (also the
/// `par~`, whose index the scrutinee, the guards and the bodies read).
const MATCH_COVER: &str = "int i32 arr gt bool wide opt mode tup pt state scr_init scr_block scr_sample or_pat bind_pat lit_pat \
    wild_pat g_init g_block g_sample g_bind g_mixed acc_b prev_b delay_b par_b mulx ifp ifk ifh prev_init delay_init gsum shift \
    wrap_direct wrap_let wrap_twice wrap_half wrap_prev wrap_delay hd bind_state struct_bind_state staged_guard_false late_clock \
    nif nmatch parm wrap_par idx g_idx acc_i bind_arg cond_bind par_nif par_nmatch par_prev_b par_delay_b par_struct_bind_state parm_state par_parm";
/// The forms that the mutants of the compiler need, which two seeds of the gate hold at least (so that choosing the seeds again
/// for another form does not drop the only seed that catches one): a state that reads a binding of an arm that may not be
/// taken (and one of a struct with a default, derived or written), a staged body after an arm whose guard may be false, a
/// binding after a guard faster than the scrutinee, a binding read by a delay in a `par~` (the places of the bindings are of a
/// copy each; also a `par~` in an arm, and one in a `par~`).
const MATCH_TWICE: &str =
    "bind_state struct_bind_state staged_guard_false late_clock par_prev_b par_delay_b parm_state";

#[test]
fn the_twins_of_match_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(MATCH_GATE.to_vec(), MATCH));
}

#[test]
fn the_match_seeds_of_the_gate_hold_every_form_of_the_table_of_what_is_covered() {
    let held: Vec<_> = MATCH_GATE.iter().map(|s| twin_match::make(*s, false).1).collect();
    let count = |t: &str| held.iter().filter(|h| h.contains(t)).count();
    let missing: Vec<_> = MATCH_COVER.split_whitespace().filter(|t| count(t) == 0).collect();
    assert!(missing.is_empty(), "the seeds of the gate do not hold {missing:?}: choose them again");
    let once: Vec<_> = MATCH_TWICE.split_whitespace().filter(|t| count(t) < 2).collect();
    assert!(once.is_empty(), "two seeds of the gate have to hold {once:?}: choose them again");
}

#[test]
fn a_twin_whose_unselected_bindings_are_not_the_defaults_is_caught_by_the_seeds_of_the_gate() {
    // The mutant of `fb` gives a binding that is not taken 1 and not 0: only a state that reads it shows the difference, and
    // an assert fails there (and nothing else fails: the program is still read and evaluated). That is about one program in
    // five (321 of the first 1500), so of the seeds of the gate (not chosen for it) four at least have to be caught.
    let (s, bad) = run(MATCH_GATE.to_vec(), MATCH, true);
    let all_asserts = bad.iter().all(|m| m.contains("does not hold"));
    assert!(all_asserts && bad.len() >= 4, "{} of {} caught: {bad:?}", bad.len(), s.programs);
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_match_twins() {
    println!("{:?}", check(heavy_seeds(), MATCH));
}
