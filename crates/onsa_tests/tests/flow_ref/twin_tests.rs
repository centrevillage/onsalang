//! The twins of `if~` (W7-20 U1): `fa` with `if~` and `fb` written as §11.5 defines it (each branch in a `let` before, then a
//! plain `if` that selects) give the same outputs, for the programs of fixed seeds, on the evaluator and in the interpreter.
//! The gate has 8 seeds and checks that they hold every form of `COVER`; the `heavy_` test runs 200 (or `ONSA_FLOW_GEN=lo..hi`).

use std::collections::BTreeSet;

use super::shrink::{
    DIVISION, INTERNAL, LIMITS, MISSING_PANIC, OUT_OF_STAGES, UNEXPECTED_PANIC, class_of, shrink, without_a_line,
};
use super::twin::{Family, Stats, make, run};
use super::twin_match;
use super::twin_pan;

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
fn heavy_seeds(count: u64) -> Vec<u64> {
    let Ok(range) = std::env::var("ONSA_FLOW_GEN") else { return (0..count).collect() };
    let (lo, hi) = range.split_once("..").expect("ONSA_FLOW_GEN is <lo>..<hi>");
    (lo.parse().expect("a number")..hi.parse().expect("a number")).collect()
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_if_twins() {
    let s = check(heavy_seeds(200), IF);
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
    println!("{:?}", check(heavy_seeds(200), MATCH));
}

// The panics by stage (U3, the family P): the forms written by hand, whose panics are derived from the spec, and the programs of
// the seeds, whose panics are held to what the plan allows. Both are run in the evaluator and the interpreter.

/// The seeds of the gate for the panics: chosen again when a change of the generator moves what they make and `PAN_COVER` or
/// `PAN_TWICE` break.
const PAN_GATE: [u64; 12] = [151, 209, 472, 486, 575, 626, 1229, 1255, 1328, 1350, 1397, 1429];
/// The forms the seeds hold: chains and `match~`es, nested, on each kind of scrutinee; the divisions (by an input of each clock
/// and by a binding), in a body, in an argument of `block`, in a condition after the first and in a guard after another (a guard
/// of `sample` before it too), a guarded chain, a short circuit (`&&`, `||`) whose right side divides, by the clock of its left
/// side (`x`) or by another, a plain `if` that guards its division and one that does not, a division of an outer binding in a
/// guard, an argument of `block` that divides by a binding in a `match~` whose scrutinee is a binding, and one that divides by a binding
/// of an outer arm where a scrutinee or a guard of `sample` is before it.
const PAN_COVER: &str = "if match nested_if nested_match scr_k scr_n scr_ku scr_b body_div state_div block_div d_k d_n d_b c_x c_eq0 \
    c_lt2 c_ne c_div c_gdiv c_and_x c_or_x c_and_clk c_or_clk plain_guarded plain_bad late_cond_div late_guard_div sample_then_div \
    guard_chain outer_guard if_cond_b block_arg_b block_arg_late";
/// The forms that the mutants need, which two seeds of the gate hold at least: a division in a body (also of a state, and of an
/// argument of `block`) that is evaluated whether its arm is taken or not, in a condition after the first and in a guard after
/// another (one of `sample` before it too), a plain `if` that does not guard its division, a division of an outer binding, a
/// scrutinee that is one, the nest of the arms chosen from the outside in, each short circuit.
const PAN_TWICE: &str = "late_cond_div late_guard_div sample_then_div plain_bad outer_guard body_div state_div block_div scr_b \
    block_arg_b block_arg_late c_and_x c_or_x c_and_clk c_or_clk";

/// The programs run: no failure, and what was counted is not nothing (scenes that panic and scenes that do not, a panic at each
/// stage, and scenes where a division that is surely evaluated divides by zero, which have to panic), all compared.
fn pan_check(progs: Vec<(Option<u64>, twin_pan::Prog, BTreeSet<&'static str>)>) -> twin_pan::Stats {
    // A form written by hand (it has no seed) has no plan to say which division is sure, and no `init` panic.
    let (n, by_plan) = (progs.len(), progs.iter().all(|p| p.0.is_some()));
    let (s, bad) = twin_pan::run(progs);
    assert!(bad.is_empty(), "{}", bad.join("\n\n"));
    let stages = &s.by_stage[usize::from(!by_plan)..];
    let counted =
        s.programs == n && s.panicked > 0 && s.quiet > 0 && (s.surely > 0 || !by_plan) && stages.iter().all(|&c| c > 0);
    assert!(counted && s.compared == s.scenes, "something was not run: {s:?}");
    s
}

fn pan_progs(seeds: Vec<u64>) -> Vec<(Option<u64>, twin_pan::Prog, BTreeSet<&'static str>)> {
    seeds
        .into_iter()
        .map(|s| {
            let (p, t) = twin_pan::make(s);
            (Some(s), p, t)
        })
        .collect()
}

#[test]
fn the_panics_of_the_forms_written_by_hand_are_where_the_spec_derives_them() {
    let s = pan_check(twin_pan::fixed());
    println!("{s:?}");
}

#[test]
fn the_panics_of_the_gate_seeds_are_by_their_plans_and_the_same_in_the_interpreter() {
    println!("{:?}", pan_check(pan_progs(PAN_GATE.to_vec())));
}

#[test]
fn the_panic_seeds_of_the_gate_hold_every_form_of_the_table_of_what_is_covered() {
    let held: Vec<_> = PAN_GATE.iter().map(|s| twin_pan::make(*s).1).collect();
    let count = |t: &str| held.iter().filter(|h| h.contains(t)).count();
    let missing: Vec<_> = PAN_COVER.split_whitespace().filter(|t| count(t) == 0).collect();
    assert!(missing.is_empty(), "the seeds of the gate do not hold {missing:?}: choose them again");
    let once: Vec<_> = PAN_TWICE.split_whitespace().filter(|t| count(t) < 2).collect();
    assert!(once.is_empty(), "two seeds of the gate have to hold {once:?}: choose them again");
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_panic_stages() {
    println!("{:?}", pan_check(pan_progs(heavy_seeds(150))));
}

#[test]
fn a_shrink_keeps_the_kind_of_the_failure_and_stops_at_its_limit() {
    // A fake failure of a text: it fails in the class `bad` while it holds the line BAD, and in another class with fewer than 5 lines.
    let src: String =
        (0..30).map(|i| if i == 17 { "BAD".to_string() } else { format!("line {i}") }).collect::<Vec<_>>().join("\n");
    let fails = |s: &String| s.contains("BAD").then_some(if s.lines().count() < 5 { "other" } else { "bad" });
    let (small, tries) = shrink(src.clone(), "bad", LIMITS, |s: &String| without_a_line(s), fails);
    assert_eq!((small.lines().count(), small.contains("BAD"), tries < LIMITS.0), (5, true, true), "{small}");
    let (cut, tries) = shrink(src, "bad", (4, LIMITS.1), |s: &String| without_a_line(s), fails);
    assert_eq!((tries, cut.lines().count()), (4, 26), "four candidates were tried and taken");
}

#[test]
fn a_failure_is_of_the_kind_its_message_says_and_a_broken_core_is_not_a_division() {
    let kinds = [
        (format!("scene n1_k0_ki0_f2: {UNEXPECTED_PANIC}: no division"), UNEXPECTED_PANIC),
        (format!("scene n1_k0_ki0_f2: {MISSING_PANIC}: a division"), MISSING_PANIC),
        (format!("scene n1_k0_ki0_f2: {OUT_OF_STAGES}: at Block"), OUT_OF_STAGES),
        ("p.onsa: internal error: internal lowering error: a field".to_string(), INTERNAL),
        ("p.onsa: \"n0_init\": fa.process(..) (line 9): division by zero".to_string(), DIVISION),
        ("something else".to_string(), "other"),
    ];
    for (msg, kind) in kinds {
        assert_eq!(class_of(&msg), kind, "{msg}");
    }
}

#[test]
fn the_smaller_plans_of_a_panic_program_are_smaller_and_a_failing_one_is_shrunk() {
    // What ends a shrink: every smaller plan is less (`size`), for the plans of 300 seeds.
    for seed in 0..300 {
        let plan = twin_pan::make(seed).0.plan;
        let more: Vec<_> =
            twin_pan::smaller_plans(&plan).iter().filter(|p| p.size() >= plan.size()).map(|p| p.size()).collect();
        assert!(more.is_empty(), "seed {seed}: a plan of {} has smaller plans of {more:?}", plan.size());
    }
    // A program that is held to a lie (no panic at all) fails in a scene; it is shrunk to that scene and a smaller plan.
    let (seed, tags, mut prog) = (0, twin_pan::make(0).1, twin_pan::make(0).0);
    prog.hand = Some(|_| None);
    let full = prog.src().lines().count();
    let (stats, bad) = twin_pan::run(vec![(Some(seed), prog, tags)]);
    assert!(stats.panicked > 0 && bad.len() == 1, "{stats:?} {bad:?}");
    let (kind, shrunk) = (
        bad[0].contains(&format!("failure `{UNEXPECTED_PANIC}`")),
        bad[0].split_once("tries:\n").map(|(_, p)| p.lines().count()),
    );
    assert!(kind && shrunk.is_some_and(|n| n < full / 2), "{kind} {shrunk:?} of {full}: {}", bad[0]);
}
