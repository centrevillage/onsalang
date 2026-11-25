//! The flows with an event in their head in the commands of `onsa` (W7-11 U1a/t, U2g/t and U2/t; spec §11.2, §11.9, §11.11, §18.1, `spec/tools.md` §1 and §4; S-560, S-564, S-67, Q-09): what the case files in
//! `tests/spec/flow_clock/` and `tests/spec/flow_semantics/event_*.onsa` cannot pin.
//!
//! - `check` reads a package whose flows have an event input or an event output, and a flow that calls one, with no diagnostic (the event clock is found and the heads and the bodies are right, U1a). The error of a form that
//!   does not run is E0200 at the uses of the generated functions and at the marks `@export` in `check` (`e0200_event_boundary_*.onsa`); this file has the commands that go on to the Core.
//! - From W7-11 U2 the forms in a straight line run: a producer, a receiver, a flow that gives or takes an event, a delay of an event, a `let` and the `at` of an event, one event given to two inputs. `test` and `dump --core`
//!   go on (the package is run, a test that calls them gives the values of the case files); `onsa graph` draws them (a `let` of an event is `名前: 型 at event`, `spec/tools.md` §1.1), and `onsa interface` has the size of the
//!   state of each (§12.4).
//! - The forms that are E0200 after U2 (`rules` of the table of the work, until W7-17 and U2r): a call with a modifier whose callee has an event port, a modifier whose condition is an event, a built-in delay of an event with a
//!   modifier, an event in a `par~`, an `if~` or a `match~`, a source that ticks by itself (`let d = fwd~(prev~(^d))`, on the path of the output, off it, and in a loop of two). Each is one E0200 for the flow that has the
//!   form, at a place in that flow (the spec fixes the code and says that it is where the form is found, §18.1; so only the lines of the flow are asked), in `test`, `dump --core` and `graph <that flow>`; the flows that run
//!   in the same package are not stopped (`graph` of one is drawn), and the tests do not run.
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
/// A flow that shows the events as a `let`, and two inputs of events.
const DRAWN: &str = "pub flow drawn(x: F32 at sample) -> U32 at sample {\n  let d = with_event_out~(x)\n  acc~(d)\n}\n";
const SECOND_IN: &str =
    "pub flow second_in(m: U32 at event, k: U32 at event) -> U32 at sample {\n  (m at sample) + k\n}\n";

/// The flows that run after U2.
const RUNNING: [&str; 7] = [EVENT_IN, EVENT_OUT, READS_OUT, ACC, CALLS_ACC, DRAWN, SECOND_IN];

// ---- the forms that are E0200 after U2: each is one flow
const FWD: &str = "flow fwd(m: U32 at event) -> U32 at event {\n  Some(m)\n}\n";
const LP: &str = "flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5\n}\n";
const MODDED: &str =
    "pub flow modded(x: F32 at sample) -> U32 at sample {\n  acc~(with_event_out~(x)).when~(true)\n}\n";
const EVENT_COND: &str = "pub flow event_cond(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).reset_if~(d != 0)\n}\n";
const ROOTLESS_ON: &str =
    "pub flow rootless_on(x: F32 at sample) -> U32 at sample {\n  let d = fwd~(prev~(^d))\n  acc~(d)\n}\n";
const ROOTLESS_OFF: &str = "pub flow rootless_off(x: F32 at sample) -> U32 at sample {\n  let d = fwd~(prev~(^d))\n  let _ = acc~(d)\n  0\n}\n";
const ROOTLESS_LOOP: &str = "pub flow rootless_loop(x: F32 at sample) -> U32 at sample {\n  let a = fwd~(prev~(^b))\n  let b = fwd~(a)\n  acc~(b)\n}\n";
/// The forms with an event in the head of their own flow, so that nothing but the flow itself is needed.
const DELAY_MODIFIER: &str =
    "pub flow delay_modifier(m: U32 at event, c: Bool at block) -> U32 at sample {\n  prev~(m).reset_if~(c)\n}\n";
const PAR_EVENT: &str = "pub flow par_event(m: U32 at event) -> U32 at sample {\n  let ys = par~ i in 0 ..< 2 {\n    prev~(m)\n  }\n  ys[0] + ys[1]\n}\n";
const IF_EVENT: &str = "pub flow if_event(m: U32 at event, c: Bool at sample) -> U32 at sample {\n  if~ c {\n    prev~(m)\n  } else {\n    0\n  }\n}\n";
const MATCH_EVENT: &str = "pub flow match_event(m: U32 at event, k: U32 at sample) -> U32 at sample {\n  match~ k {\n    0 => prev~(m),\n    _ => 0,\n  }\n}\n";

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

/// The lines (from 1) of the flow `name` of `src`: its `flow` line and its closing `}`.
fn flow_lines(src: &str, name: &str) -> (u64, u64) {
    let head = format!("flow {name}(");
    let start = src
        .lines()
        .position(|l| (l.starts_with("flow ") || l.starts_with("pub flow ")) && l.contains(&head))
        .unwrap_or_else(|| panic!("no flow {name} in\n{src}"));
    let end = src.lines().enumerate().skip(start).find(|(_, l)| *l == "}").map(|(i, _)| i).expect("a closing line");
    (start as u64 + 1, end as u64 + 1)
}

fn assert_checks(tag: &str, d: &Dir) {
    let check = run(d.root(), &["check"]);
    assert_eq!(check.code, 0, "{tag}: check: {}{}", check.stdout, check.stderr);
    assert!(errors(&check).is_empty(), "{tag}: check: {}{}", check.stdout, check.stderr);
}

fn assert_no_internal_error(tag: &str, args: &[&str], out: &Out) {
    assert!(!out.stdout.contains("internal error") && !out.stderr.contains("internal error"), "{tag}: {args:?}");
}

/// The command ends with 1 and E0200 only, one in the lines of each flow of `flows` and no other, and it does not run the package.
fn assert_stops_in(tag: &str, d: &Dir, src: &str, args: &[&str], flows: &[&str]) {
    let out = run(d.root(), args);
    let got = errors(&out);
    assert_eq!(out.code, 1, "{tag}: {args:?}: {}{}", out.stdout, out.stderr);
    assert!(got.iter().all(|(code, _)| code == "E0200"), "{tag}: {args:?}: only E0200: {}{}", out.stdout, out.stderr);
    for name in flows {
        let (a, b) = flow_lines(src, name);
        let n = got.iter().filter(|(_, row)| a <= *row && *row <= b).count();
        assert_eq!(n, 1, "{tag}: {args:?}: one E0200 in `{name}` (lines {a}-{b}): {}{}", out.stdout, out.stderr);
    }
    assert_eq!(got.len(), flows.len(), "{tag}: {args:?}: no E0200 elsewhere: {}{}", out.stdout, out.stderr);
    assert!(!out.stdout.lines().any(|l| l.starts_with("test ")), "{tag}: {args:?}: a test ran: {}", out.stdout);
    assert_no_internal_error(tag, args, &out);
}

/// `test`, `dump --core` and `graph <flow>` for each flow of `flows` stop in those flows only.
fn assert_each_stops(tag: &str, flows: &[&str], names: &[&str]) {
    let (d, src) = package(tag, flows);
    assert_checks(tag, &d);
    let dir = d.arg();
    assert_stops_in(tag, &d, &src, &["test"], names);
    assert_stops_in(tag, &d, &src, &["dump", "--core", &dir], names);
    for name in names {
        assert_stops_in(tag, &d, &src, &["graph", name], &[name]);
    }
    let out = run(d.root(), &["graph", "plain"]);
    assert_eq!(out.code, 0, "{tag}: graph plain: {}{}", out.stdout, out.stderr);
}

// ---------------------------------------------------------------- the forms that run

/// The package of the flows that run: `check` has no diagnostic, `test` passes (the test of the package, 1 passed), `dump --core` goes on, and no E0200 is said.
#[test]
#[ignore = "W7-11 U2: S-564, S-1234"]
fn a_package_of_flows_with_events_that_run_is_tested_and_lowered_u2() {
    let (d, _) = package("event_run", &RUNNING);
    assert_checks("event_run", &d);
    let out = run(d.root(), &["test"]);
    assert_eq!(out.code, 0, "test: {}{}", out.stdout, out.stderr);
    assert!(errors(&out).is_empty() && out.stdout.contains("1 passed, 0 failed"), "test: {}{}", out.stdout, out.stderr);
    assert_no_internal_error("event_run", &["test"], &out);
    let dir = d.arg();
    let core = run(d.root(), &["dump", "--core", &dir]);
    assert_eq!(core.code, 0, "dump --core: {}{}", core.stdout, core.stderr);
    assert!(errors(&core).is_empty(), "dump --core: {}{}", core.stdout, core.stderr);
    assert_no_internal_error("event_run", &["dump"], &core);
}

/// Each flow that runs is drawn alone (`onsa graph <flow>`), and `let` of an event is a node `名前: 型 at event`, the input of an event `名前: 型 at event`, the output of an event `out: 型 at event` (`spec/tools.md` §1.1).
#[test]
#[ignore = "W7-11 U2: S-564"]
fn graph_draws_the_flows_with_events_u2() {
    let (d, _) = package("event_graph", &RUNNING);
    for (flow, labels) in [
        ("with_event_in", &["m: U32 at event"][..]),
        ("with_event_out", &["out: U32 at event"][..]),
        ("reads_out", &["out: U32 at sample"][..]),
        ("acc", &["e: U32 at event"][..]),
        ("calls_acc", &["x: F32 at sample"][..]),
        ("drawn", &["d: U32 at event", "x: F32 at sample"][..]),
        ("second_in", &["m: U32 at event", "k: U32 at event"][..]),
    ] {
        let out = run(d.root(), &["graph", flow]);
        assert_eq!(out.code, 0, "graph {flow}: {}{}", out.stdout, out.stderr);
        assert!(
            errors(&out).is_empty() && out.stdout.contains("digraph"),
            "graph {flow}: {}{}",
            out.stdout,
            out.stderr
        );
        for label in labels {
            assert!(out.stdout.contains(label), "graph {flow}: no `{label}`: {}", out.stdout);
        }
    }
}

/// §12.4: the size of the state of a flow with events is known (`size: not available` is what a flow that the lowering stops at has).
#[test]
#[ignore = "W7-11 U2: S-564"]
fn interface_has_the_sizes_of_the_states_of_the_flows_that_run_u2() {
    let (d, _) = package("event_sizes", &RUNNING);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "interface: {}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
}

// ---------------------------------------------------------------- the forms that stay E0200 after U2

/// A built-in delay of an event with a modifier, and an event in a `par~`, an `if~` and a `match~`: each flow that has the form is one E0200 (their heads have an event, so they stop before U2 too).
#[test]
fn a_delay_with_a_modifier_and_events_in_par_and_branches_are_one_e0200_for_each_flow() {
    let names = ["delay_modifier", "par_event", "if_event", "match_event"];
    assert_each_stops("event_stay_inside", &[DELAY_MODIFIER, PAR_EVENT, IF_EVENT, MATCH_EVENT], &names);
}

/// A modifier on a call whose callee has an event port, a modifier whose condition is an event, and a source that ticks by itself (on the path of the output, off it, in a loop of two): one E0200 for the flow that has
/// the form. The flows that run in the same package (`acc`, `fwd`, `with_event_out`, `calls_acc`) are not stopped.
#[test]
#[ignore = "W7-11 U2: S-564"]
fn a_modifier_on_an_event_port_an_event_condition_and_a_source_with_no_root_are_one_e0200_for_each_flow_u2() {
    let flows = [EVENT_OUT, ACC, FWD, LP, CALLS_ACC, MODDED, EVENT_COND, ROOTLESS_ON, ROOTLESS_OFF, ROOTLESS_LOOP];
    let names = ["modded", "event_cond", "rootless_on", "rootless_off", "rootless_loop"];
    assert_each_stops("event_stay_calls", &flows, &names);
    let (d, _) = package("event_stay_calls_beside", &flows);
    let out = run(d.root(), &["graph", "calls_acc"]);
    assert_eq!(out.code, 0, "graph calls_acc: {}{}", out.stdout, out.stderr);
}

/// The forms that run and the forms that stay E0200 in one package: the stop is the flows that stay, and the flows that run are in the same package (`graph` of one is drawn).
#[test]
#[ignore = "W7-11 U2: S-564"]
fn flows_that_run_beside_a_flow_that_is_e0200_are_not_stopped_u2() {
    let flows = [EVENT_OUT, ACC, CALLS_ACC, DRAWN, MODDED];
    let (d, src) = package("event_beside", &flows);
    assert_checks("event_beside", &d);
    assert_stops_in("event_beside", &d, &src, &["test"], &["modded"]);
    for flow in ["calls_acc", "drawn", "acc"] {
        let out = run(d.root(), &["graph", flow]);
        assert_eq!(out.code, 0, "graph {flow}: {}{}", out.stdout, out.stderr);
    }
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
fn an_error_of_the_clock_in_an_event_flow_is_the_only_diagnostic() {
    let mix = "pub flow mix(a: F32 at event, b: F32 at event) -> F32 at sample {\n  a + b\n}\n";
    for (tag, flows) in [("event_mix", vec![mix]), ("event_mix_beside", vec![EVENT_IN, mix, EVENT_OUT])] {
        let (d, src) = package(tag, &flows);
        let at = src.lines().position(|l| l.starts_with("  a + b")).expect("the line") as u64 + 1;
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
