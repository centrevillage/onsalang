//! The flows with an event in their head in the commands of `onsa` (W7-11 U1a/t, U2g/t, U2/t and U2r/t; spec §11.2, §11.9, §11.10, §11.11, §18.1, `spec/tools.md` §1 and §4; S-560, S-562, S-564, S-67, Q-09): what the case files in
//! `tests/spec/flow_clock/` and `tests/spec/flow_semantics/event_*.onsa` cannot pin.
//!
//! - `check` reads a package whose flows have an event input or an event output, and a flow that calls one, with no diagnostic (the event clock is found and the heads and the bodies are right, U1a). The error of a form that
//!   does not run is E0200 at the uses of the generated functions and at the marks `@export` in `check` (`e0200_event_boundary_*.onsa`); this file has the commands that go on to the Core.
//! - From W7-11 U2 the forms in a straight line run: a producer, a receiver, a flow that gives or takes an event, a delay of an event, a `let` and the `at` of an event, one event given to two inputs. `test` and `dump --core`
//!   go on (the package is run, a test that calls them gives the values of the case files); `onsa graph` draws them (a `let` of an event is `名前: 型 at event`, `spec/tools.md` §1.1), and `onsa interface` has the size of the
//!   state of each (§12.4).
//! - From W7-11 U2r a chain of `reset_if~` only (one or more) runs when it has an event: a receiver whose condition is an event, a receiver that has an event port (a call of a flow with an event input, or an argument that is an
//!   event), and a built-in delay of an event (its condition is the event of its own or a kind `block`). The forms that are E0200 after U2r (until W7-17): a call with `when~`, `.down~` or `.up~` whose callee has an event port, a
//!   chain that has a `.reset_if~` at an event and a `when~`, `.down~` or `.up~`, or a `when~` at an event and a `.down~` or `.up~` (from U3 one with none of them runs), a source that ticks by itself (`let d = fwd~(prev~(^d))`, on the path of the output, off it, and in a loop
//!   of two). Each is one E0200 for the flow that has the form, at a place in that flow (the spec fixes the code and says that it is where the form is found, §18.1; so only the lines of the flow are asked), in `test`,
//!   `dump --core` and `graph <that flow>`; the flows that run in the same package are not stopped (`graph` of one is drawn), and the tests do not run.
//! - From W7-17 U6a an event in a `par~`, a `par`, an `if~` and a `match~` runs (in a replica and an arm, in a condition, a scrutinee and a guard); a chain that is E0200 elsewhere is E0200 in a replica and an arm too.
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
/// A chain that has an event condition and a `when~` (before or after the `reset_if~`), a `.down~`, or a call of an event port with a `.down~`: E0200 after U2r too.
const MIXED_WHEN: &str = "pub flow mixed_when(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).when~(c).reset_if~(d != 0)\n}\n";
const MIXED_DOWN: &str = "pub flow mixed_down(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(0.5).down~(2).reset_if~(d != 0) at sample\n}\n";
const PORT_DOWN: &str = "pub flow port_down(x: F32 at sample) -> U32 at sample {\n  let d = with_event_out~(x)\n  acc~(d).down~(2) at sample\n}\n";
const RESET_THEN_WHEN: &str = "pub flow reset_then_when(x: F32 at sample, c: Bool at sample) -> U32 at sample {\n  let d = with_event_out~(x)\n  acc~(d).reset_if~(d != 0).when~(c)\n}\n";
/// The forms of a chain of `reset_if~` only that has an event, which run after U2r (E0200 at U2).
const EVENT_COND: &str = "pub flow event_cond(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).reset_if~(d != 0)\n}\n";
const RESET_CHAIN: &str = "pub flow reset_chain(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).reset_if~(d != 0).reset_if~(d > 1)\n}\n";
const RESET_PART: &str = "pub flow reset_part(x: F32 at sample) -> U32 at sample {\n  let d = with_event_out~(x)\n  acc~(d).reset_if~(d != 0)\n}\n";
const DELAY_OWN: &str = "pub flow delay_own(m: U32 at event) -> U32 at sample {\n  prev~(m, 9).reset_if~(m == 0)\n}\n";
const ROOTLESS_ON: &str =
    "pub flow rootless_on(x: F32 at sample) -> U32 at sample {\n  let d = fwd~(prev~(^d))\n  acc~(d)\n}\n";
const ROOTLESS_OFF: &str = "pub flow rootless_off(x: F32 at sample) -> U32 at sample {\n  let d = fwd~(prev~(^d))\n  let _ = acc~(d)\n  0\n}\n";
const ROOTLESS_LOOP: &str = "pub flow rootless_loop(x: F32 at sample) -> U32 at sample {\n  let a = fwd~(prev~(^b))\n  let b = fwd~(a)\n  acc~(b)\n}\n";
/// The forms with an event in the head of their own flow, so that nothing but the flow itself is needed.
const DELAY_MODIFIER: &str =
    "pub flow delay_modifier(m: U32 at event, c: Bool at block) -> U32 at sample {\n  prev~(m).reset_if~(c)\n}\n";
const PAR_EVENT: &str = "pub flow par_event(m: U32 at event) -> U32 at sample {\n  let ys = par~ i in 0 ..< 2 {\n    prev~(m)\n  }\n  ys[0] + ys[1]\n}\n";
/// The makers of events in a `par~`, the parts of events in a `par` (one a delay stores), an event in a condition and a guard, and a level of an event in a `par~`.
const PAR_MAKER: &str = "pub flow par_maker(x: F32 at sample) -> U32 at sample {\n  let ys = par~ i in 0 ..< 2 {\n    par~ j in 1 ..= 3 {\n      acc~(with_event_out~(x + F32.round_from(i * j)))\n    }\n  }\n  ys[0][1] + ys[1][2]\n}\n";
const PAR_PARTS: &str = "pub flow par_parts(x: U32 at sample, m: U32 at event) -> U32 at sample {\n  let ys = par i in 0 ..< 2 {\n    x + ((m * i) at sample)\n  }\n  prev~((par i in 0 ..< 2 {\n    x + ((m * (i + 1)) at sample)\n  })[1]) + ys[1]\n}\n";
const COND_EVENT: &str = "pub flow cond_event(x: F32 at sample) -> F32 at sample {\n  if~ acc~(with_event_out~(x)) > 3 {\n    lp~(x)\n  } else {\n    prev~(x)\n  }\n}\n";
const GUARD_EVENT: &str = "pub flow guard_event(m: U32 at event) -> U32 at sample {\n  let y = match~ m {\n    n if m > 3 => prev~(n),\n    n => n,\n  }\n  y\n}\n";
/// The chains that stay E0200, in a replica, an arm and a condition.
const PAR_CHAIN: &str = "pub flow par_chain(x: F32 at sample) -> U32 at sample {\n  let ys = par~ i in 0 ..< 2 {\n    par~ j in 0 ..< 2 {\n      acc~(with_event_out~(x)).down~(2) at sample\n    }\n  }\n  ys[0][0]\n}\n";
const IF_CHAIN: &str = "pub flow if_chain(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if~ c {\n    lp~(x).when~(c).reset_if~(with_event_out~(x) != 0)\n  } else {\n    x\n  }\n}\n";
const COND_CHAIN: &str = "pub flow cond_chain(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if~ acc~(with_event_out~(x)).when~(c) > 3 {\n    prev~(x)\n  } else {\n    x\n  }\n}\n";
const MATCH_CHAIN: &str = "pub flow match_chain(x: F32 at sample, k: U32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  match~ k {\n    0 => lp~(0.5).when~(d != 0).down~(2) at sample,\n    _ => prev~(x),\n  }\n}\n";
const IF_EVENT: &str = "pub flow if_event(m: U32 at event, c: Bool at sample) -> U32 at sample {\n  if~ c {\n    prev~(m)\n  } else {\n    0\n  }\n}\n";
const MATCH_EVENT: &str = "pub flow match_event(m: U32 at event, k: U32 at sample) -> U32 at sample {\n  match~ k {\n    0 => prev~(m),\n    _ => 0,\n  }\n}\n";

/// A condition of a `when~` at an event (a level, W7-11 U3): the chain of `when~` and periodic `reset_if~` runs; a `.down~` in the chain, a `reset_if~` at an event with it and a part with an event port stay E0200 (W7-17).
const WHEN_LEVEL: &str = "pub flow when_level(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).when~(d != 0).reset_if~(c).when~(d < 9)\n}\n";
const WHEN_DELAY: &str = "pub flow when_delay(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  prev~(prev~(x).when~(d != 0))\n}\n";
const WHEN_DOWN: &str = "pub flow when_down(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(0.5).when~(d != 0).down~(2) at sample\n}\n";
const WHEN_MIXED: &str = "pub flow when_mixed(x: F32 at sample) -> F32 at sample {\n  let d = with_event_out~(x)\n  lp~(x).when~(d != 0).reset_if~(d > 1)\n}\n";
const WHEN_PORT: &str = "pub flow when_port(x: F32 at sample) -> U32 at sample {\n  let d = with_event_out~(x)\n  acc~(d).when~(d != 0)\n}\n";
const WHEN_PAR: &str = "pub flow when_par(x: F32 at sample) -> F32 at sample {\n  let on = with_event_out~(x) != 0\n  let ys = par~ i in 0 ..< 2 {\n    lp~(x).when~(on)\n  }\n  ys[0] + ys[1]\n}\n";

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
fn interface_has_the_sizes_of_the_states_of_the_flows_that_run_u2() {
    let (d, _) = package("event_sizes", &RUNNING);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "interface: {}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
}

// ---------------------------------------------------------------- the forms that stay E0200 after U2

/// A chain that stays E0200 elsewhere (a `when~` and a `.down~` on a part with an event port, a `when~` beside a `reset_if~` at an event, a `when~` at an event beside a `.down~`) is one E0200 in a replica (of two `par~`s) and an arm
/// of an `if~` and a `match~` too, and in the condition of an `if~`; the flows that run beside it are not stopped.
#[test]
fn a_chain_not_run_is_one_e0200_in_a_replica_and_an_arm_u6a() {
    let flows = [EVENT_OUT, ACC, LP, PAR_EVENT, PAR_MAKER, IF_EVENT, PAR_CHAIN, IF_CHAIN, COND_CHAIN, MATCH_CHAIN];
    assert_each_stops("event_stay_inside", &flows, &["par_chain", "if_chain", "cond_chain", "match_chain"]);
    let (d, _) = package("event_stay_inside_beside", &flows);
    for flow in ["par_event", "par_maker", "if_event"] {
        let out = run(d.root(), &["graph", flow]);
        assert_eq!(out.code, 0, "graph {flow}: {}{}", out.stdout, out.stderr);
    }
}

/// A `when~` or a `.down~` on a call whose callee has an event port, a chain that has an event condition and a `when~` or a `.down~` (before or after the `reset_if~`), and a source that ticks by itself (on the path of the
/// output, off it, in a loop of two): one E0200 for the flow that has the form (they stay E0200 after U2r, until W7-17). The flows that run in the same package (`acc`, `fwd`, `with_event_out`, `calls_acc`) are not stopped.
#[test]
fn a_mixed_chain_a_modifier_on_an_event_port_and_a_source_with_no_root_are_one_e0200_for_each_flow_u2() {
    let flows = [
        EVENT_OUT,
        ACC,
        FWD,
        LP,
        CALLS_ACC,
        MODDED,
        MIXED_WHEN,
        MIXED_DOWN,
        PORT_DOWN,
        RESET_THEN_WHEN,
        ROOTLESS_ON,
        ROOTLESS_OFF,
        ROOTLESS_LOOP,
    ];
    let names = [
        "modded",
        "mixed_when",
        "mixed_down",
        "port_down",
        "reset_then_when",
        "rootless_on",
        "rootless_off",
        "rootless_loop",
    ];
    assert_each_stops("event_stay_calls", &flows, &names);
    let (d, _) = package("event_stay_calls_beside", &flows);
    let out = run(d.root(), &["graph", "calls_acc"]);
    assert_eq!(out.code, 0, "graph calls_acc: {}{}", out.stdout, out.stderr);
}

/// The forms that run and the forms that stay E0200 in one package: the stop is the flows that stay, and the flows that run are in the same package (`graph` of one is drawn).
#[test]
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

// ---------------------------------------------------------------- a chain of `reset_if~` only that has an event (U2r)

/// The forms of a chain of `reset_if~` only that has an event (a periodic receiver with an event condition, two conditions on one event, a receiver that has an event port, a delay of an event with the event of its own or
/// a `block` condition): `check` has no diagnostic, `test` passes (1 passed), `dump --core` goes on, no E0200 is said and `interface` has the sizes of their states (§12.4).
#[test]
fn a_package_of_reset_if_chains_on_events_runs_u2r() {
    let mut flows = RUNNING.to_vec();
    flows.extend([LP, EVENT_COND, RESET_CHAIN, RESET_PART, DELAY_OWN, DELAY_MODIFIER]);
    let (d, _) = package("event_reset_run", &flows);
    assert_checks("event_reset_run", &d);
    let out = run(d.root(), &["test"]);
    assert_eq!(out.code, 0, "test: {}{}", out.stdout, out.stderr);
    assert!(errors(&out).is_empty() && out.stdout.contains("1 passed, 0 failed"), "test: {}{}", out.stdout, out.stderr);
    assert_no_internal_error("event_reset_run", &["test"], &out);
    let dir = d.arg();
    let core = run(d.root(), &["dump", "--core", &dir]);
    assert_eq!(core.code, 0, "dump --core: {}{}", core.stdout, core.stderr);
    assert!(errors(&core).is_empty(), "dump --core: {}{}", core.stdout, core.stderr);
    let interface = run(d.root(), &["interface"]);
    assert_eq!(interface.code, 0, "interface: {}{}", interface.stdout, interface.stderr);
    assert!(!interface.stdout.contains("not available"), "the size of the state is known: {}", interface.stdout);
}

/// The chains that run (U2r) beside the forms that stay E0200: the stop is the flows that stay (a `when~` before the `reset_if~`, a `.down~` before it, a `reset_if~` and then a `when~`), and the flows that run are in
/// the same package (`graph` of one is drawn).
#[test]
fn reset_if_chains_that_run_beside_a_mixed_chain_are_not_stopped_u2r() {
    let flows = [EVENT_OUT, ACC, LP, EVENT_COND, RESET_PART, MIXED_WHEN, MIXED_DOWN, RESET_THEN_WHEN];
    let (d, src) = package("event_reset_beside", &flows);
    assert_checks("event_reset_beside", &d);
    assert_stops_in("event_reset_beside", &d, &src, &["test"], &["mixed_when", "mixed_down", "reset_then_when"]);
    for flow in ["event_cond", "reset_part"] {
        let out = run(d.root(), &["graph", flow]);
        assert_eq!(out.code, 0, "graph {flow}: {}{}", out.stdout, out.stderr);
    }
}

/// An event in a `par~` (read from outside and made in it), a `par`, an `if~` and a `match~`: `check` has no diagnostic, `test` passes (1 passed), `dump --core` and `graph` go on, no E0200 is said and `interface` has the sizes
/// of their states (§12.4).
#[test]
fn a_package_of_events_in_replicas_and_arms_runs_u6a() {
    let names = ["par_event", "par_maker", "par_parts", "if_event", "cond_event", "match_event", "guard_event"];
    let forms = [PAR_EVENT, PAR_MAKER, PAR_PARTS, IF_EVENT, COND_EVENT, MATCH_EVENT, GUARD_EVENT];
    let flows = [&[EVENT_OUT, ACC, LP][..], &forms].concat();
    let (d, _) = package("event_inside_run", &flows);
    assert_checks("event_inside_run", &d);
    let dir = d.arg();
    let mut out = run(d.root(), &["test"]);
    assert!(out.code == 0 && out.stdout.contains("1 passed, 0 failed"), "test: {}{}", out.stdout, out.stderr);
    for args in
        [vec!["dump", "--core", dir.as_str()], vec!["interface"]].into_iter().chain(names.map(|n| vec!["graph", n]))
    {
        out = run(d.root(), &args);
        assert_eq!(out.code, 0, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(errors(&out).is_empty() && !out.stdout.contains("not available"), "{args:?}: {}", out.stdout);
        assert_no_internal_error("event_inside_run", &args, &out);
    }
}

/// A level of an event in the condition of a `when~` (U3): the chains that run are tested and drawn beside a `.down~` in the chain, a `reset_if~` at an event and a part with an event port, one E0200 each.
#[test]
fn the_levels_of_an_event_in_a_when_run_and_the_other_chains_stop_u3() {
    let runs = [EVENT_OUT, ACC, LP, WHEN_LEVEL, WHEN_DELAY, WHEN_PAR];
    let (d, _) = package("event_when_run", &runs);
    assert_checks("event_when_run", &d);
    let out = run(d.root(), &["test"]);
    assert_eq!(out.code, 0, "test: {}{}", out.stdout, out.stderr);
    assert!(errors(&out).is_empty() && out.stdout.contains("1 passed, 0 failed"), "test: {}{}", out.stdout, out.stderr);
    for flow in ["when_level", "when_delay", "when_par"] {
        let out = run(d.root(), &["graph", flow]);
        assert_eq!(out.code, 0, "graph {flow}: {}{}", out.stdout, out.stderr);
    }
    let stays = [EVENT_OUT, ACC, LP, WHEN_LEVEL, WHEN_DOWN, WHEN_MIXED, WHEN_PORT];
    assert_each_stops("event_when_stay", &stays, &["when_down", "when_mixed", "when_port"]);
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
