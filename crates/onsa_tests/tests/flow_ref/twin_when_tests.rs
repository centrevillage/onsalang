//! The twins of `when~` (W7-10 U1e/t; S-1209): `X.when~(true)` and `X`, `x.down~(N).when~(c)` and `x.when~(c).down~(N)`,
//! `x.when~(a).when~(b)` and `x.when~(a && b)`, made from seeds (`twin_when.rs`). The seeds of the gate hold every form of
//! `COVER`; the `heavy_` tests run more (`ONSA_FLOW_GEN=lo..hi` runs a range again).
//!
//! Three things hold them. The checker passes every program and the interpreter holds its asserts (a twin that the interpreter
//! does not hold is a failure of the interpreter or of the generator), and a mutant of each twin is caught by the asserts: both
//! run today. The evaluator gives what the interpreter gives (`twin::run`: it evaluates every test and the interpreter is
//! compared with it): these wait for the evaluator to have `when~` (W7-10 U1e).

use std::collections::BTreeSet;

use onsa_driver::{Loaded, PackageInput, TestOptions, TestRun, analyze_loaded, lower_core, run_tests};

use super::twin::{Family, Maker, run};
use super::twin_tests::{check, heavy_seeds};
use super::twin_when::{chains, exotic_count, make, make_exotic};

const WHEN: Family = ("when_twins", make);
const EXOTIC: Family = ("when_exotic", make_exotic);

/// The seeds of the gate: chosen again when a change of the generator moves what they make and `COVER` breaks. Each gives a
/// mutant that the asserts catch.
const GATE: [u64; 8] = [1, 2, 3, 30, 54, 61, 261, 339];
/// The forms the seeds of the gate hold: every head, every twin, every modifier, the places a `when~` that always holds is put
/// in, the clocks W the conditions are read at and the kinds of condition, a burst and a slow output, a `when~` between an
/// `.up~` and a `.down~`, a `when~` that deals a burst head out, two `.up~` and a `.down~`.
const COVER: &str = "h_slot h_tk h_acc h_lp h_dws h_mk2 h_mk4 k_id k_commute k_merge m_down2 m_down4 m_down8 m_up2 len_2 len_3 len_4 len_5 \
    when_1 when_2 when_3 o_plain o_burst o_slow w_p w_slow w_pos c_sig c_sig_slow c_block c_init c_lit c_not c_and c_or t_lit \
    t_block t_init t_both t_or_sig ins_front ins_end ins_mid ins_two double_when deal_when in_block stacked";
/// The seeds of the gate for the matrix of `exotic`, and what they hold: a stack of blocks with the `when~` in it and at its end.
const EXOTIC_GATE: [u64; 6] = [6, 54, 58, 89, 367, 414];
const EXOTIC_COVER: &str =
    "h_tk h_slot stacked in_block ins_front ins_mid ins_end t_lit t_block o_plain o_burst o_slow len_3 len_4";

/// The tests of a program run in the interpreter (name and failure), or why the program does not run: the checker's
/// diagnostics (a form that U1 keeps as E0200 is one), or an error of the lowering.
pub fn interpreted(src: &str) -> Result<Vec<(String, Option<String>)>, String> {
    let src = src.to_string();
    onsa_diag::stack::run(move || {
        let mut loaded = Loaded::from_input(PackageInput::single_file("when.onsa", &src)).map_err(|e| e.to_string())?;
        let analyzed = analyze_loaded(&mut loaded).map_err(|e| e.render(&loaded.sources))?;
        if !analyzed.diagnostics.is_empty() {
            return Err(onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        }
        let module = lower_core(&analyzed).map_err(|e| e.render(&loaded.sources))?;
        match run_tests(&loaded.sources, &module, &TestOptions::default()) {
            Ok(TestRun::Ran(r)) => {
                Ok(r.tests.into_iter().map(|t| (t.name.clone(), t.message().map(str::to_string))).collect())
            }
            Ok(TestRun::Unsupported(d)) => Err(onsa_diag::to_text(&loaded.sources, &d)),
            Ok(TestRun::NoMatch) => Err("no test was selected".to_string()),
            Err(e) => Err(e.render(&loaded.sources)),
        }
    })
}

/// The checker's verdict on a program: the first diagnostic or error of the lowering, if any.
pub fn analysis(src: &str) -> Result<(), String> {
    let src = src.to_string();
    onsa_diag::stack::run(move || {
        let mut loaded = Loaded::from_input(PackageInput::single_file("when.onsa", &src)).map_err(|e| e.to_string())?;
        let analyzed = analyze_loaded(&mut loaded).map_err(|e| e.render(&loaded.sources))?;
        if !analyzed.diagnostics.is_empty() {
            return Err(onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        }
        lower_core(&analyzed).map(|_| ()).map_err(|e| e.render(&loaded.sources))
    })
}

/// The seeds of a family run in the interpreter alone: the number of tests that ran, and a message for each seed that is wrong
/// (the program does not run; or, for a mutant (`rot`), no assert fails, and otherwise one does).
pub fn interpreter_failures(make: Maker, seeds: impl IntoIterator<Item = u64>, rot: bool) -> (usize, Vec<String>) {
    let (mut bad, mut ran) = (Vec::new(), 0);
    for seed in seeds {
        let (src, tags) = make(seed, rot);
        match interpreted(&src) {
            Err(why) => bad.push(format!("seed {seed} {tags:?}: it does not run: {why}\n{src}")),
            Ok(tests) => {
                ran += tests.len();
                let failed: Vec<_> =
                    tests.iter().filter_map(|(n, m)| m.as_ref().map(|m| format!("{n}: {m}"))).collect();
                let wrong = if tests.len() != 2 {
                    Some("it has not two tests")
                } else if rot && failed.is_empty() {
                    Some("the mutant of the twin is not caught")
                } else if !rot && !failed.is_empty() {
                    Some("the twins differ")
                } else {
                    None
                };
                bad.extend(wrong.map(|w| format!("seed {seed} {tags:?}: {w}: {failed:?}\n{src}")));
            }
        }
    }
    (ran, bad)
}

/// The first three failures, with how many there are.
pub fn shown(bad: &[String]) -> String {
    format!(
        "{} failures, the first three:\n{}",
        bad.len(),
        bad.iter().take(3).cloned().collect::<Vec<_>>().join("\n\n")
    )
}

pub fn assert_held(make: Maker, seeds: &[u64], rot: bool) {
    assert!(!seeds.is_empty(), "no seed was run");
    let (ran, bad) = interpreter_failures(make, seeds.iter().copied(), rot);
    assert!(bad.is_empty() && ran == 2 * seeds.len(), "{ran} tests ran. {}", shown(&bad));
}

pub fn assert_covered(make: Maker, seeds: &[u64], cover: &str) {
    let held: BTreeSet<&str> = seeds.iter().flat_map(|s| make(*s, false).1).collect();
    let missing: Vec<_> = cover.split_whitespace().filter(|t| !held.contains(t)).collect();
    assert!(missing.is_empty(), "the seeds of the gate do not hold {missing:?}: choose them again");
}

#[test]
fn the_flows_of_the_gate_seeds_pass_the_checker_and_the_twins_hold_in_the_interpreter() {
    assert_held(make, &GATE, false);
    assert_held(make_exotic, &EXOTIC_GATE, false);
}

#[test]
fn the_gate_seeds_hold_every_form_of_the_table_of_what_is_covered() {
    assert_covered(make, &GATE, COVER);
    assert_covered(make_exotic, &EXOTIC_GATE, EXOTIC_COVER);
}

#[test]
fn a_mutant_of_each_twin_is_caught_by_its_asserts_in_the_interpreter() {
    assert_held(make, &GATE, true);
    assert_held(make_exotic, &EXOTIC_GATE, true);
}

#[test]
fn the_chains_the_generator_leaves_out_are_the_ones_that_u1_does_not_run() {
    // Every chain of up to 3 modifiers over every head, with the condition at W and with an `init` one: the checker passes (and
    // lowers) exactly what the generator makes, and says E0200 of what it leaves out.
    let (mut made, mut left, mut wrong) = (0, 0, Vec::new());
    for cond in ["sig", "ci"] {
        for (what, src, gated) in chains(3, cond) {
            let verdict = analysis(&src);
            let e0200 = verdict.as_ref().is_err_and(|e| e.contains("E0200"));
            match (gated, &verdict) {
                (None, Ok(())) => made += 1,
                (Some("in_block" | "burst_under_up"), Err(_)) if e0200 => left += 1,
                _ => {
                    let first = verdict.map_err(|e| e.lines().next().unwrap_or_default().to_string());
                    wrong.push(format!("{what} ({gated:?}): {first:?}"));
                }
            }
        }
    }
    assert!(wrong.is_empty() && made > 100 && left > 30, "{made} made, {left} left out: {}", wrong.join("\n"));
}

#[test]
fn the_twins_of_when_agree_on_the_evaluator_and_in_the_interpreter() {
    println!("{:?}", check(GATE.to_vec(), WHEN));
    println!("{:?}", check(EXOTIC_GATE.to_vec(), EXOTIC));
}

#[test]
fn a_mutant_of_a_twin_of_when_is_caught_by_the_evaluator() {
    // The interpreter is not run on a mutant: the evaluator has to evaluate every test, and an assert fails in each program.
    for (family, seeds) in [(WHEN, GATE.to_vec()), (EXOTIC, EXOTIC_GATE.to_vec())] {
        let (s, bad) = run(seeds.clone(), family, true);
        let caught = bad.iter().filter(|m| m.contains("does not hold")).count();
        assert_eq!((s.programs, caught), (seeds.len(), seeds.len()), "{bad:?}");
    }
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_when_twins_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make, heavy_seeds(500), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_when_mutants_in_the_interpreter() {
    // A mutant of a seed is caught in most programs, not all (the twin of `merge` with `||` differs only where the two
    // conditions differ): at most one in five is not.
    let seeds = heavy_seeds(300);
    let (ran, bad) = interpreter_failures(make, seeds.clone(), true);
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
fn heavy_when_exotic_in_the_interpreter() {
    let (ran, bad) = interpreter_failures(make_exotic, 0..exotic_count(), false);
    assert!(bad.is_empty() && ran > 0, "{}", shown(&bad));
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_chains_the_generator_leaves_out_of_up_to_five_modifiers_are_stopped() {
    let mut wrong = Vec::new();
    for cond in ["sig", "ci"] {
        for (what, src, gated) in chains(5, cond) {
            let verdict = analysis(&src);
            let e0200 = verdict.as_ref().is_err_and(|e| e.contains("E0200"));
            let right = match gated {
                None => verdict.is_ok(),
                Some(_) => e0200,
            };
            if !right {
                wrong.push(format!(
                    "{what} ({gated:?}): {:?}",
                    verdict.map_err(|e| e.lines().next().unwrap_or_default().to_string())
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{} wrong: {:?}", wrong.len(), &wrong[..wrong.len().min(5)]);
}

#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_when_twins() {
    println!("{:?}", check(heavy_seeds(200), WHEN));
    println!("{:?}", check((0..exotic_count()).collect(), EXOTIC));
}
