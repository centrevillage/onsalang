//! The event stages of the reference evaluator on the cases of W7-11 U2/t (`tests/spec/flow_semantics/event_*.onsa`): every `test` of them runs on the evaluator and its asserts hold, whether or not the case lowers (the
//! interpreter is compared with the evaluator from U2, in `flow_ref.rs`, which waits for the list of things pending and the data of the cases). Two tests are not evaluated and are named below with the reason.

use onsa_driver::PackageInput;
use onsa_tests::case::repo_root;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Verdict, run_case};

const CASES: &[&str] = &[
    "tests/spec/flow_semantics/event_stage_values.onsa",
    "tests/spec/flow_semantics/event_hoist_values.onsa",
    "tests/spec/flow_semantics/event_part_values.onsa",
    "tests/spec/flow_semantics/event_saved_values.onsa",
    "tests/spec/flow_semantics/event_saved_branch_values.onsa",
];

/// The tests of the cases that the evaluator does not read (the start of their names).
const KNOWN: &[(&str, &str)] = &[
    // The walk of a case has no `render` with the struct `In { x, t }` of two `sample` inputs (`Skip::Layout`).
    ("vdelay~ reads its length d as the last event", "layout"),
    // The same: `render` with `f.In { x, y }`.
    ("a read selected by a condition with ^k is the value of the end of the stage", "layout"),
];

fn run_file(path: &str) -> Vec<String> {
    let src = std::fs::read_to_string(repo_root().join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
    let path = path.to_string();
    onsa_diag::stack::run(move || {
        let input = PackageInput::single_file(path.clone(), src);
        let run = run_case(input, &Wrappers::default()).unwrap_or_else(|e| panic!("{path}: not read: {e}"));
        assert!(!run.tests.is_empty(), "{path}: no test");
        let mut bad = Vec::new();
        for t in &run.tests {
            let known = KNOWN.iter().find(|(name, _)| t.name.starts_with(name));
            let said = match &t.verdict {
                Verdict::Ok => String::new(),
                Verdict::Failed(m) => m.clone(),
                Verdict::Skipped(s) => format!("{s:?}").to_lowercase(),
                Verdict::Unavailable(why) => format!("unavailable: {why}"),
            };
            match (known, said.is_empty()) {
                (None, true) => {}
                (Some((_, expected)), false) if said.contains(expected) => {}
                _ => bad.push(format!("{path}: \"{}\": {said:?} (known: {known:?})", t.name)),
            }
        }
        bad
    })
}

#[test]
fn the_event_cases_of_u2_run_on_the_evaluator() {
    let bad: Vec<String> = CASES.iter().flat_map(|p| run_file(p)).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}
