//! The event stages of the reference evaluator on the cases of W7-11 U2/t and U3/t (`tests/spec/flow_semantics/event_*.onsa`): every `test` of them runs on the evaluator and its asserts hold, whether or not the case lowers (the
//! interpreter is compared with the evaluator from U2, in `flow_ref.rs`, which waits for the list of things pending and the data of the cases).

use onsa_driver::PackageInput;
use onsa_tests::case::repo_root;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::walk::{Verdict, run_case};

// `event_reset_delay_values.onsa` and `event_reset_more_values.onsa` are not here: they check the outputs with `same(a.out, [..])`, a function of `Span` arguments that a loop makes (the interpreter is its host, and the case has to lower first, W7-11 U2r).
const CASES: &[&str] = &[
    "tests/spec/flow_semantics/event_read_values.onsa",
    "tests/spec/flow_semantics/event_condition_values.onsa",
    "tests/spec/flow_semantics/event_when_values.onsa",
    "tests/spec/flow_semantics/event_reset_values.onsa",
    "tests/spec/flow_semantics/event_saved_match_values.onsa",
    "tests/spec/flow_semantics/event_stage_values.onsa",
    "tests/spec/flow_semantics/event_hoist_values.onsa",
    "tests/spec/flow_semantics/event_part_values.onsa",
    "tests/spec/flow_semantics/event_saved_values.onsa",
    "tests/spec/flow_semantics/event_saved_branch_values.onsa",
    "tests/spec/flow_semantics/event_saved_deferred_values.onsa",
    "tests/spec/flow_semantics/event_saved_modified_values.onsa",
    "tests/spec/flow_semantics/event_saved_inner_delay_values.onsa",
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
            let said = match &t.verdict {
                Verdict::Ok => String::new(),
                Verdict::Failed(m) => m.clone(),
                Verdict::Skipped(s) => format!("{s:?}").to_lowercase(),
                Verdict::Unavailable(why) => format!("unavailable: {why}"),
            };
            if !said.is_empty() {
                bad.push(format!("{path}: \"{}\": {said:?}", t.name));
            }
        }
        bad
    })
}

#[test]
fn the_event_cases_of_u2_and_u3_run_on_the_evaluator() {
    let bad: Vec<String> = CASES.iter().flat_map(|p| run_file(p)).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}
