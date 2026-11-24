//! The flows with an event in their head in the commands of `onsa` (W7-11 U1a/t and U2g/t; spec §11.2, §11.9, §11.11, §18.1, `spec/tools.md` §1 and §4; S-560, S-564, S-67, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - `check` reads a package whose flows have an event input or an event output, and a flow that calls one, with no diagnostic (the event clock is found and the heads and the bodies are right, U1a). The error of a form that
//!   does not run is E0200 at the uses of the generated functions and at the marks `@export` in `check` (`e0200_event_boundary_*.onsa`); this file has the commands that go on to the Core.
//! - Until a form that runs is open (W7-11 U2; the tests that stop there are named `until_w7_11_u2`) `test` and `dump --core` end with 1 and E0200 and nothing else, for each flow with an event in its head of the package
//!   (every item of the own package is reached, so a flow that nothing calls is reached too), at the word `event` of the head; a flow that only calls them is at the head of the callee, and one place is one error (S-67).
//!   None of them goes on to run the package.
//! - `onsa graph <flow>` stops at E0200 only when the flow it draws has an event (in its head, or a call of an event output in its body); a flow with no event is drawn beside the event flows of the package. `onsa interface` is not
//!   stopped: the flows with an event are in its list and E0200 is not said.
//! - A package with a mistake of the clock in a flow with an event (E0815: the events of two inputs in one sum) has that diagnostic and no E0200, in every command: the check stops what goes on to the Core.
//!
//! Not written here: a flow with an event in a package that is a dependency (a dependency other than `std` is E0200 of the manifest in this version, §15.3, and `std` has no flow with an event), so the form "the own package does
//! not use it, `test` goes on" and "the own package calls it, E0200 at the head in the file of the dependency" has no input yet.
//!
//! The texts are written from the spec; none is taken from the output of the compiler. A diagnostic is a line `<file>:<line>:<col>: error[<code>]: <message>` of the text output, and only the code and the line
//! are read (the spec does not fix the column or the message).

use crate::test_support::{Dir, Out, run};

const PLAIN: &str = "pub flow plain(x: F32 at sample) -> F32 at sample {\n  x\n}\n\n";
const TEST: &str = "\ntest \"reads\" {\n  assert 1 + 1 == 2\n}\n";

const EVENT_IN: &str = "pub flow with_event_in(m: U32 at event) -> U32 at sample {\n  m\n}\n";
const EVENT_OUT: &str = "pub flow with_event_out(x: F32 at sample) -> U32 at event {\n  if x > 0.5 {\n    Some(1)\n  } else {\n    None\n  }\n}\n";
/// A flow that calls an event output and reads it at `sample`: no event in its head.
const READS_OUT: &str = "pub flow reads_out(x: F32 at sample) -> U32 at sample {\n  with_event_out~(x) at sample\n}\n";
/// A flow that gives the event of an output to an event input (`acc`) and one that calls it: the head of `acc` has an event.
const ACC: &str = "flow acc(e: U32 at event) -> U32 at sample {\n  let n = prev~(^n) + e\n  n\n}\n";
const CALLS_ACC: &str = "pub flow calls_acc(x: F32 at sample) -> U32 at sample {\n  acc~(with_event_out~(x))\n}\n";

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

fn package(tag: &str, flows: &[&str]) -> (Dir, String) {
    let src = format!("{PLAIN}{}{TEST}", flows.join("\n"));
    let d = Dir::pkg(tag);
    d.write("main.onsa", &src);
    (d, src)
}

/// The line (from 1) of the first line of `src` that starts with `head`.
fn line_of(src: &str, head: &str) -> u64 {
    let at = src.lines().position(|l| l.starts_with(head)).unwrap_or_else(|| panic!("no line {head:?} in\n{src}"));
    at as u64 + 1
}

fn assert_checks(tag: &str, d: &Dir) {
    let check = run(d.root(), &["check"]);
    assert_eq!(check.code, 0, "{tag}: check: {}{}", check.stdout, check.stderr);
    assert!(errors(&check).is_empty(), "{tag}: check: {}{}", check.stdout, check.stderr);
}

/// The command ends with 1 and E0200 only, one at the line of each head of `heads` (the text of the line starts with that head) and no other, and it does not run the package.
fn assert_stops_at(tag: &str, d: &Dir, src: &str, args: &[&str], heads: &[&str]) {
    let out = run(d.root(), args);
    let mut want: Vec<(String, u64)> = heads.iter().map(|h| ("E0200".to_string(), line_of(src, h))).collect();
    want.sort_by_key(|w| w.1);
    assert_eq!(out.code, 1, "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
    assert_eq!(errors(&out), want, "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
    for (_, row) in &want {
        let text = src.lines().nth(*row as usize - 1).expect("a line of the source");
        assert!(text.contains("at event"), "{tag}: {args:?}: E0200 at {row}, a line with no event: {text:?}");
    }
    assert!(!out.stdout.lines().any(|l| l.starts_with("test ")), "{tag}: {args:?}: a test ran: {}", out.stdout);
    assert!(!out.stdout.contains("internal error") && !out.stderr.contains("internal error"), "{tag}: {args:?}");
}

/// `check` is clean, and `test` and `dump --core` stop at the heads `heads`.
fn assert_checked_and_stopped(tag: &str, flows: &[&str], heads: &[&str]) {
    let (d, src) = package(tag, flows);
    assert_checks(tag, &d);
    let dir = d.arg();
    assert_stops_at(tag, &d, &src, &["test"], heads);
    assert_stops_at(tag, &d, &src, &["dump", "--core", &dir], heads);
}

// ---------------------------------------------------------------- one flow with an event: the stop is at its head

#[test]
fn a_flow_with_an_event_input_is_checked_and_stopped_at_its_head_until_w7_11_u2() {
    assert_checked_and_stopped("event_in", &[EVENT_IN], &["pub flow with_event_in"]);
}

#[test]
fn a_flow_with_an_event_output_is_checked_and_stopped_at_its_head_until_w7_11_u2() {
    assert_checked_and_stopped("event_out", &[EVENT_OUT], &["pub flow with_event_out"]);
}

/// A flow with no event in its head that calls a flow with an event output: it is read by `check`, and the stop is at the head of the callee, once (the callee is an item of the package, and the caller reaches it too).
#[test]
fn a_caller_of_an_event_output_is_stopped_once_at_the_head_of_the_callee_until_w7_11_u2() {
    assert_checked_and_stopped("event_caller", &[EVENT_OUT, READS_OUT], &["pub flow with_event_out"]);
}

// ---------------------------------------------------------------- each flow with an event is its own stop

/// The two flows with an event of the package, and the one that nothing calls, are two errors, at the head of each (the own package is the root of the lowering, so a flow no test and no flow calls is reached too).
#[test]
fn each_flow_with_an_event_in_the_package_is_its_own_stop_until_w7_11_u2() {
    assert_checked_and_stopped(
        "event_two",
        &[EVENT_IN, EVENT_OUT],
        &["pub flow with_event_in", "pub flow with_event_out"],
    );
}

/// An event output that a flow gives to an event input of another flow and the caller of both: the heads of the two flows, each once (the caller has no event in its head).
#[test]
fn a_chain_of_event_flows_is_one_stop_at_each_head_until_w7_11_u2() {
    assert_checked_and_stopped("event_chain", &[EVENT_OUT, ACC, CALLS_ACC], &["pub flow with_event_out", "flow acc"]);
}

/// Three flows with an event in their heads and the flows that call them: three errors, in the order of the lines.
#[test]
fn many_flows_with_an_event_are_as_many_stops_until_w7_11_u2() {
    let more = "pub flow second_in(m: U32 at event, k: U32 at event) -> U32 at sample {\n  m\n}\n";
    assert_checked_and_stopped(
        "event_many",
        &[EVENT_OUT, READS_OUT, EVENT_IN, more],
        &["pub flow with_event_out", "pub flow with_event_in", "pub flow second_in"],
    );
}

// ---------------------------------------------------------------- a flow with an event is in `onsa graph` only where it is drawn

/// The flow that is drawn has no event: the graph comes out (exit 0, a DOT text), whether or not the package has flows with an event (`plain` and the caller that reads an output at `sample` are the same drawing as without them).
#[test]
fn a_flow_with_no_event_is_drawn_in_a_package_that_has_flows_with_an_event() {
    let (d, _) = package("graph_beside", &[EVENT_IN, EVENT_OUT]);
    let out = run(d.root(), &["graph", "plain"]);
    assert_eq!(out.code, 0, "graph plain: {}{}", out.stdout, out.stderr);
    assert!(errors(&out).is_empty(), "graph plain: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("digraph") && out.stdout.contains("x: F32 at sample"), "graph plain: {}", out.stdout);
}

/// The flows that are drawn have an event in the head (an input, an output), or call an event output in the body: E0200 only, at the head of the flow with the event.
#[test]
fn graph_of_a_flow_with_an_event_is_stopped_at_its_head_until_w7_11_u2() {
    let (d, src) = package("graph_event", &[EVENT_IN, EVENT_OUT, READS_OUT]);
    assert_checks("graph_event", &d);
    for (flow, head) in [
        ("with_event_in", "pub flow with_event_in"),
        ("with_event_out", "pub flow with_event_out"),
        ("reads_out", "pub flow with_event_out"),
    ] {
        assert_stops_at(flow, &d, &src, &["graph", flow], &[head]);
    }
}

// ---------------------------------------------------------------- `onsa interface` is not stopped

#[test]
fn interface_lists_the_flows_with_an_event_and_does_not_stop() {
    let (d, _) = package("interface_event", &[EVENT_IN, EVENT_OUT, READS_OUT]);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "interface: {}{}", out.stdout, out.stderr);
    assert!(errors(&out).is_empty(), "interface: {}{}", out.stdout, out.stderr);
    for name in ["plain", "with_event_in", "with_event_out", "reads_out"] {
        assert!(out.stdout.contains(name), "interface: no {name}: {}", out.stdout);
    }
    assert!(
        !out.stdout.contains("E0200") && !out.stderr.contains("internal error"),
        "interface: {}{}",
        out.stdout,
        out.stderr
    );
}

// ---------------------------------------------------------------- another diagnostic is the only one

/// The clock of an event is wrong (`a + b`, the events of two inputs): the diagnostic is E0815, the only one, in `check` and in each command that goes on, and none of them says E0200. A right flow with an event next to it
/// is not E0200 either (the check stops what goes on to the Core).
#[test]
fn an_error_of_the_clock_in_an_event_flow_is_the_only_diagnostic_until_w7_11_u2() {
    let mix = "pub flow mix(a: F32 at event, b: F32 at event) -> F32 at sample {\n  a + b\n}\n";
    for (tag, flows) in [("event_mix", vec![mix]), ("event_mix_beside", vec![EVENT_IN, mix, EVENT_OUT])] {
        let (d, src) = package(tag, &flows);
        let at = line_of(&src, "  a + b");
        let dir = d.arg();
        for args in
            [vec!["check"], vec!["test"], vec!["graph", "mix"], vec!["interface"], vec!["dump", "--core", dir.as_str()]]
        {
            let out = run(d.root(), &args);
            assert_eq!(out.code, 1, "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
            assert_eq!(errors(&out), vec![("E0815".to_string(), at)], "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
        }
    }
}
