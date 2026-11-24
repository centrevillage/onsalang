//! The flows with an event in their head in the commands of `onsa` (W7-11 U1a/t; spec §11.2, §11.11, §18.1, `spec/tools.md` §4; S-560, S-564, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - `check` reads a package whose flows have an event input or an event output, and a flow that calls one, with no diagnostic (the event clock is found and the heads and the bodies are right, U1a). `check` does not
//!   say E0200: a form that does not run is E0200 in the commands that go on to the Core (`build`, `test`), in `onsa graph` and in `onsa interface`, at the word `event` of the head.
//! - Until a form that runs is open (W7-11 U2; the tests are named `until_w7_11_u2` for that) the three commands end with 1 and E0200 and nothing else, and none of them goes on to run the package.
//! - A package with a mistake of the clock in a flow with an event (E0815: the events of two inputs in one sum) has that diagnostic and no E0200, in every command: the check stops what goes on to the Core.
//!
//! The texts are written from the spec; none is taken from the output of the compiler. A diagnostic is a line `<file>:<line>:<col>: error[<code>]: <message>` of the text output, and only the code and the line
//! are read (the spec does not fix the column or the message).

use crate::test_support::{Dir, Out, run};

const PLAIN: &str = "pub flow plain(x: F32 at sample) -> F32 at sample {\n  x\n}\n\n";
const TEST: &str = "\ntest \"reads\" {\n  assert 1 + 1 == 2\n}\n";

/// The `(code, line)` of every diagnostic line of the text output of a command.
fn errors(out: &Out) -> Vec<(String, u64)> {
    let mut found = Vec::new();
    for line in out.stdout.lines().chain(out.stderr.lines()) {
        let Some((place, rest)) = line.split_once(": error[") else { continue };
        let code = rest.split(']').next().expect("a code").to_string();
        let mut parts = place.rsplitn(3, ':');
        let _column = parts.next();
        let row: u64 = parts.next().and_then(|n| n.parse().ok()).unwrap_or_else(|| panic!("no line in {line:?}"));
        found.push((code, row));
    }
    found
}

fn package(tag: &str, flows: &str) -> (Dir, String) {
    let src = format!("{PLAIN}{flows}{TEST}");
    let d = Dir::pkg(tag);
    d.write("main.onsa", &src);
    (d, src)
}

/// `check` reads the package with no diagnostic; `test`, `graph <flow>` and `interface` end with 1 and E0200 only, at
/// the lines of `at` (the heads that have an event; the text of each line has `at event`).
fn assert_stops_at_the_gate(tag: &str, flows: &str, graph_of: &str, at: &[u64]) {
    let (d, src) = package(tag, flows);
    let check = run(d.root(), &["check"]);
    assert_eq!(check.code, 0, "{tag}: check: {}{}", check.stdout, check.stderr);
    assert!(errors(&check).is_empty(), "{tag}: check: {}{}", check.stdout, check.stderr);
    for args in [vec!["test"], vec!["graph", graph_of], vec!["interface"]] {
        let out = run(d.root(), &args);
        let found = errors(&out);
        assert_eq!(out.code, 1, "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
        assert!(!found.is_empty(), "{tag}: {args:?}: no diagnostic: {}{}", out.stdout, out.stderr);
        assert!(found.iter().all(|(code, _)| code == "E0200"), "{tag}: {args:?}: {found:?}");
        assert_eq!(found[0].1, at[0], "{tag}: {args:?}: the first E0200 is at the head of the event flow: {found:?}");
        for (_, row) in &found {
            let text = src.lines().nth(*row as usize - 1).expect("a line of the source");
            assert!(text.contains("at event"), "{tag}: {args:?}: E0200 at {row}, a line with no event: {text:?}");
        }
        assert!(!out.stdout.contains("internal error") && !out.stderr.contains("internal error"), "{tag}: {args:?}");
    }
}

#[test]
fn a_flow_with_an_event_input_is_checked_and_stopped_at_the_gate_until_w7_11_u2() {
    let flows = "pub flow with_event_in(m: U32 at event) -> U32 at sample {\n  m\n}\n";
    assert_stops_at_the_gate("event_in", flows, "with_event_in", &[5]);
}

#[test]
fn a_flow_with_an_event_output_is_checked_and_stopped_at_the_gate_until_w7_11_u2() {
    let flows = "pub flow with_event_out(x: F32 at sample) -> U32 at event {\n  if x > 0.5 {\n    Some(1)\n  } else {\n    None\n  }\n}\n";
    assert_stops_at_the_gate("event_out", flows, "with_event_out", &[5]);
}

/// A flow with no event in its head that calls a flow with an event output (and one that gives an event input to the call of a flow): it is read by `check`, and the commands stop at the head of the callee.
#[test]
fn a_caller_of_event_flows_is_checked_and_stopped_at_the_gate_until_w7_11_u2() {
    let flows = "\
flow det(x: F32 at sample) -> U32 at event {
  if x > 0.5 {
    Some(1)
  } else {
    None
  }
}

flow acc(e: U32 at event) -> U32 at sample {
  let n = prev~(^n) + e
  n
}

pub flow caller(x: F32 at sample) -> U32 at sample {
  acc~(det~(x))
}
";
    assert_stops_at_the_gate("event_caller", flows, "caller", &[5]);
}

/// The clock of an event is wrong (`a + b`, the events of two inputs): the diagnostic is E0815, the only one, in `check` and in each command that goes on, and none of them says E0200.
#[test]
fn an_error_of_the_clock_in_an_event_flow_is_the_only_diagnostic_until_w7_11_u2() {
    let flows = "pub flow mix(a: F32 at event, b: F32 at event) -> F32 at sample {\n  a + b\n}\n";
    let (d, _) = package("event_mix", flows);
    for args in [vec!["check"], vec!["test"], vec!["graph", "mix"], vec!["interface"]] {
        let out = run(d.root(), &args);
        assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(errors(&out), vec![("E0815".to_string(), 6)], "{args:?}: {}{}", out.stdout, out.stderr);
    }
}
