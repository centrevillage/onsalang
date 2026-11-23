//! A flow with a chain of `.down~(N)` and `.up~(N)` in the commands of `onsa` (W7-09 U3b/t; spec §11.9, §11.3, §11.6, §18.1,
//! `spec/tools.md` §1.1; S-566, S-1084, S-1139, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - The Core of a chain whose modifiers are all `.down~(N)` and whose boundaries gather and deal nothing, over a part that reads no `sample_tick()`, is W7-16 U6a1 (S-1207, S-1214): `build`,
//!   `dump --core` and `test` end with 0 and no internal error for it (W7-16 U6a1/t; the values are in `tests/spec/flow_semantics/down_chain_values.onsa`).
//! - A chain with an `.up~(N)` in it is lowered too (W7-16 U6b3; S-1207, S-1214, S-1217): `build`, `dump --core` and `test` end with 0 and no internal error, and the values of two of them with a part with a memory
//!   are those of the part run in time order (a delay of the boundary that gathers, none where none does; the other values are in `tests/spec/flow_semantics/up_chain_values.onsa`).
//! - `onsa graph` of such a flow: the label of the vertex of an instance with modifiers writes the kind and then the modifiers in the order
//!   they are written, with the N as a value, and the type and the clock of the value of the chain at the call side (S-1084, provisional
//!   reading (2): `lp_0 = lp~.down~(4): F32 at (sample / 4)`). No colour is added (the vertices keep the three of §1.1, and a tick has the black
//!   of `sample`), and the edge of the head argument is the edge of any call. The node whose `let` is a tick has the name of S-1139 (a)
//!   (`b.lp_0`, a node with no name of §1.1 whose label drops the qualification, drawn into the vertex of the `let` `b`).
//!
//! - A clock composed of the N of a port or a stage and those of the chain is `sample * N` or `sample / N` with the N a `U32`, 2^31 or less (S-1216): past it (`sample * 2^32`, `sample / 2^32`) is E0808 at
//!   `check`, every command stops with it and no internal error, with a note (the declared N and the path); exactly 2^31 is read by `check`, and a slow one is lowered by every command.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::sample_tick_commands::assert_lowers_and_passes;
use crate::slow_stage_commands::{assert_lowers, error_lines, package};
use crate::test_support::{Dir, diagnostics, doc_of, run, str_of};

const LP: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n\n";

/// Flows with a chain of `.down~(N)` whose ratio is not one, each in a form that `check` accepts (modifier_chain_clocks.onsa): the head has no input at `sample * N`, so no boundary gathers or deals,
/// and it reads no `sample_tick()`.
const BODIES: [&str; 3] = [
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  x * (lp~(p).down~(4) at sample)\n}\n",
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let y = lp~(p).down~(2).down~(2)\n  x * (y at sample)\n}\n",
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let a = p at (sample / 4)\n  let y = lp~(a).down~(4)\n  x * (y at sample)\n}\n",
];

/// Flows with an `.up~(N)` in the chain, each in a form that `check` accepts (modifier_rules.rs, the graph test below).
const UP_BODIES: [&str; 3] = [
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  x * (lp~(p).down~(4).up~(2) at sample)\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  lp~(x).down~(2).up~(2)\n}\n",
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let y = lp~(p).up~(2).down~(4)\n  x * (y at sample)\n}\n",
];

// ----------------------------------------------------------------------------- the gate of the Core

/// W7-16 U6a1 (S-1207, S-1214; the Core of a chain whose modifiers are all `.down~(N)` and that gathers and deals nothing, over a part that reads no time): `check` reads the flow, and `build`, `dump --core` and
/// `test` end with 0 and no internal error, and the test of the package runs. The values are in `tests/spec/flow_semantics/down_chain_values.onsa`.
#[test]
fn a_flow_with_a_down_chain_that_gathers_and_deals_nothing_is_lowered_by_build_dump_core_and_test() {
    for (k, body) in BODIES.iter().enumerate() {
        assert_lowers(&format!("chain_core_lowers_{k}"), &format!("{LP}{body}"), &[]);
    }
}

/// W7-16 U6b3 (S-1207, S-1214, S-1217; it was E0200 until then, Q-09): `check` reads the flows with a chain that has an `.up~(N)`, and `build`, `dump --core` and `test` end with 0 and no internal error, the test of
/// the package runs (the forms of `UP_BODIES`: an up with a down after it, a down with an up after it, and an up over a part with a `block` input).
#[test]
fn a_flow_with_an_up_chain_is_lowered_by_build_dump_core_and_test() {
    for (k, body) in UP_BODIES.iter().enumerate() {
        assert_lowers(&format!("chain_core_up_lowers_{k}"), &format!("{LP}{body}"), &[]);
    }
}

/// The values of two chains with an up over a part with a memory (`lp`, y = x / 2 + x[-1] / 2 in the frames of the part), with x = 1 2 3 4 5 6 (§11.9, S-1207): `.down~(2).up~(2)` gathers nothing (the part runs
/// at the run j = 0 of each frame, on the frame's own x): 0.5 1.5 2.5 3.5 4.5 5.5; `.up~(2).down~(2)` runs the part on the stream 2 frames late (0 0 1 2 3 4), in order: 0 0 0.5 1.5 2.5 3.5.
#[test]
fn an_up_chain_over_a_part_with_a_memory_gives_the_part_run_in_time_order() {
    let flows = format!(
        "{LP}pub flow du(x: F32 at sample) -> F32 at sample {{\n  lp~(x).down~(2).up~(2)\n}}\n\npub flow ud(x: F32 at sample) -> F32 at sample {{\n  lp~(x).up~(2).down~(2)\n}}\n\ntest \"up chains\" {{\n  let xs: [F32; 6] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]\n  var a: [F32; 6] = [-1.0; 6]\n  var b: [F32; 6] = [-1.0; 6]\n  var sa = du.init(8.0)\n  var sb = ud.init(8.0)\n  du.process(inout sa, xs.slice(0, 6), inout a)\n  ud.process(inout sb, xs.slice(0, 6), inout b)\n  assert a == [0.5, 1.5, 2.5, 3.5, 4.5, 5.5]\n  assert b == [0.0, 0.0, 0.5, 1.5, 2.5, 3.5]\n}}\n"
    );
    assert_lowers_and_passes("chain_core_up_values", &flows, "up chains");
}

/// A type with no `Default` through a chain with an up (§11.9, S-1214 補い, W7-21 U1): a chain `.down~(2).up~(2)` gathers and deals nothing, and an `.up~(N)` alone makes a bundle of the runs, so neither needs the
/// default of `NoDef` (a struct of a `F32` with no `Default`) or of `Char` (the bundle read by a port at `sample * 2`): `check` reads the package and `build`, `dump --core` and `test` end with 0 (a ring or an array that starts at `T.default()` would have no value to start at).
#[test]
fn an_output_with_no_default_through_a_down_and_an_up_and_through_an_up_is_built() {
    let flows = "pub struct NoDef {\n  f: F32,\n}\n\nflow mk(p: F32 at block) -> NoDef at sample {\n  NoDef { f: p }\n}\n\nflow mkc(c: Char at block) -> Char at sample {\n  c\n}\n\nflow two(x: Char at (sample * 2)) -> F32 at sample {\n  if x[0] == x[1] { 1.0 } else { 0.0 }\n}\n\npub flow through(p: F32 at block) -> F32 at sample {\n  let m = mk~(p).down~(2).up~(2)\n  m.f * 2.0\n}\n\npub flow bundle(c: Char at block) -> F32 at sample {\n  two~(mkc~(c).up~(2))\n}\n";
    assert_lowers("chain_core_up_nodef", flows, &[]);
}

/// `onsa interface` reads the signatures and the kinds, not the Core: the flow with a chain is listed, the command ends with 0 and no
/// internal error (the size of the state is W7-16's, so no text of it is read here; the state of a down chain is in `slow_stage_commands.rs`).
#[test]
fn interface_of_a_flow_with_a_chain_ends_with_zero() {
    for (k, body) in BODIES.iter().chain(UP_BODIES.iter()).enumerate() {
        let d = package(&format!("chain_interface_{k}"), &format!("{LP}{body}"), &[]);
        let out = run(d.root(), &["interface"]);
        assert_eq!(out.code, 0, "{body}: {}{}", out.stdout, out.stderr);
        assert!(
            !format!("{}{}", out.stdout, out.stderr).contains("internal error"),
            "{body}: {}{}",
            out.stdout,
            out.stderr
        );
        assert!(out.stdout.contains("pub flow f("), "{body}: the flow `f` is listed: {}", out.stdout);
    }
}

/// The forms of S-1216: a part whose output (`h`, `sample * 2^20`) an `.up~(4096)` makes `sample * 2^32` in the frame of a `.down~` that deals it, and that value itself; a constant given
/// to an input at `sample * 2^20` under an `.up~(4096)`; a stage of `sample / 512` and a slow input at `sample / 2^31` under a `.down~(2^24)`; and the slow input at `sample / 2^31` under a `.down~(2)`,
/// `sample / 2^32`, one past 2^31. Each is past `U32` and none is the product of the modifiers (S-1089).
const PAST_U32: [&str; 6] = [
    "flow h(x: U32 at sample) -> U32 at (sample * 1048576) {\n  let a: [U32; 1048576] = [x; 1048576]\n  a\n}\n\nflow r(x: U32 at (sample * 1048576)) -> U32 at sample {\n  x[0]\n}\n\n\
     pub flow f(x: U32 at sample) -> U32 at sample {\n  r~(h~(x).up~(4096).down~(4096))\n}\n",
    "flow h(x: U32 at sample) -> U32 at (sample * 1048576) {\n  let a: [U32; 1048576] = [x; 1048576]\n  a\n}\n\n\
     pub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).up~(4096)\n  x\n}\n",
    "flow h(x: U32 at (sample * 1048576)) -> U32 at sample {\n  x[0]\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).up~(4096)\n  x\n}\n",
    "flow h(x: U32 at sample) -> U32 at sample {\n  let c = prev~(^c at (sample / 512)) + 1\n  x + (c at sample)\n}\n\n\
     pub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).down~(16777216)\n  x\n}\n",
    "flow h(x: U32 at (sample / 2147483648)) -> U32 at sample {\n  x at sample\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).down~(16777216)\n  x\n}\n",
    "flow h(x: U32 at (sample / 2147483648)) -> U32 at sample {\n  x at sample\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).down~(2)\n  x\n}\n",
];

/// A clock composed in a chain past `U32` is E0808 (S-1216): `check`, `build`, `dump --core`, `test` and `interface` end with 1, with E0808 and nothing else (Q-09), and no command ends with an internal
/// error. Only the stop is pinned, no value.
#[test]
fn a_clock_composed_in_a_chain_past_u32_is_e0808_at_every_command() {
    for (k, flows) in PAST_U32.iter().enumerate() {
        let d = package(&format!("chain_past_u32_{k}"), flows, &[]);
        let dir = d.arg();
        let commands: [Vec<&str>; 5] = [
            vec!["check"],
            vec!["build", "--target", "host"],
            vec!["dump", "--core", dir.as_str()],
            vec!["test"],
            vec!["interface"],
        ];
        for args in commands {
            let out = run(d.root(), &args);
            let both = format!("{}{}", out.stdout, out.stderr);
            assert_eq!(out.code, 1, "{flows}: {args:?}: {both}");
            assert!(!both.contains("internal error"), "{flows}: {args:?}: {both}");
            let lines = error_lines(&both);
            assert!(!lines.is_empty() && lines.iter().all(|l| l.contains("error[E0808]")), "{flows}: {args:?}: {both}");
        }
    }
}

/// The E0808 of a clock composed past `U32` has a note (S-1216: "note に宣言の N と経路"; the words are not fixed by the spec, so only that a note is there is read), in each of the six forms
/// (`check --json`: every diagnostic is an E0808 and has a note).
#[test]
fn the_e0808_of_a_clock_composed_past_u32_has_a_note() {
    for (k, flows) in PAST_U32.iter().enumerate() {
        let d = package(&format!("chain_past_u32_note_{k}"), flows, &[]);
        let out = run(d.root(), &["check", "--json"]);
        assert_eq!(out.code, 1, "{flows}: {}{}", out.stdout, out.stderr);
        let doc = doc_of(&out);
        let ds = diagnostics(&doc);
        assert!(!ds.is_empty(), "{flows}: a diagnostic: {doc}");
        for dg in ds {
            assert_eq!(str_of(dg, "code"), "E0808", "{flows}: {doc}");
            let notes = dg["notes"].as_array().unwrap_or_else(|| panic!("{flows}: no `notes` array: {doc}"));
            assert!(!notes.is_empty(), "{flows}: a note with the declared N and the path: {doc}");
        }
    }
}

/// A slow input at `sample / 2^30` under a `.down~(2)` is of `sample / 2^31`, the largest N that a composed clock may have (S-1216): the package is lowered by every command, as the slow input at
/// `sample / 2^31` run by itself and by nothing is.
#[test]
fn a_slow_input_of_2_to_the_30_under_a_down_of_2_is_lowered() {
    let flows = "flow h(x: U32 at (sample / 1073741824)) -> U32 at sample {\n  x at sample\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).down~(2)\n  x\n}\n";
    assert_lowers("chain_slow_2_to_the_31", flows, &[]);
}

/// A clock composed to exactly `sample * 2^31` and `sample / 2^31` is read by `check` with no diagnostic (S-1216; the arrays are not made, so no `build`): the window of an output at `sample * 2^20` under
/// `.up~(2048).down~(2048)` of `U8` elements (an array of 2^31 bytes, a state that fits §4.1 only when it is no more than 2^32 - 1 bytes), the value of the same chain, a constant given to an input at
/// `sample * 2^30` under an `.up~(2)`, and the slow input at `sample / 2^30` under a `.down~(2)`.
#[test]
fn a_clock_composed_to_exactly_2_to_the_31_is_read_by_check() {
    let forms = [
        "flow h(x: U8 at sample) -> U8 at (sample * 1048576) {\n  let a: [U8; 1048576] = [x; 1048576]\n  a\n}\n\nflow r(x: U8 at (sample * 1048576)) -> U8 at sample {\n  x[0]\n}\n\n\
         pub flow f(x: U8 at sample) -> U8 at sample {\n  r~(h~(x).up~(2048).down~(2048))\n}\n",
        "flow h(x: U32 at sample) -> U32 at (sample * 1048576) {\n  let a: [U32; 1048576] = [x; 1048576]\n  a\n}\n\n\
         pub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).up~(2048)\n  x\n}\n",
        "flow h(x: U32 at (sample * 1073741824)) -> U32 at sample {\n  x[0]\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).up~(2)\n  x\n}\n",
        "flow h(x: U32 at (sample / 1073741824)) -> U32 at sample {\n  x at sample\n}\n\npub flow f(x: U32 at sample) -> U32 at sample {\n  let _ = h~(7).down~(2)\n  x\n}\n",
    ];
    for (k, flows) in forms.iter().enumerate() {
        let d = package(&format!("chain_exactly_2_to_the_31_{k}"), flows, &[]);
        let out = run(d.root(), &["check", "--json"]);
        assert_eq!(out.code, 0, "{flows}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "{flows}: {}", out.stdout);
    }
}

// ----------------------------------------------------------------------------- the graph

const GRAPH_SOURCE: &str = "\
const K: U32 = 4

pub flow lp(x: F32 at sample) -> F32 at sample {
  x * 0.5 + prev~(x) * 0.5
}

pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let b = lp~(p).down~(4)
  let c = lp~(p).down~(2).down~(K)
  let d = lp~(x).down~(2).up~(2)
  let e = lp~(p).down~(4).up~(2)
  let n = lp~(x)
  x * (b at sample) + (c at sample) + d + (e at sample) + n + (lp~(p).down~(8) at sample)
}
";

/// The statement of the vertex with the name `id` (the line that starts with `"id" [`).
fn vertex_line<'a>(dot: &'a str, id: &str) -> &'a str {
    let head = format!("\"{id}\" [");
    dot.lines()
        .map(str::trim)
        .find(|l| l.starts_with(&head))
        .unwrap_or_else(|| panic!("no vertex \"{id}\" in the graph:\n{dot}"))
}

/// The value of the attribute `key` of a statement (`key="…"`).
fn attr<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("{key}=\"");
    let at = line.find(&pat)? + pat.len();
    let rest = &line[at..];
    Some(&rest[..rest.find('"')?])
}

fn graph_of_f() -> String {
    let d = Dir::pkg("chain_graph");
    let file = d.file("m.onsa", GRAPH_SOURCE);
    let out = run(d.root(), &["graph", "f", &file]);
    assert_eq!(out.code, 0, "onsa graph f: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    out.stdout
}

/// The label of the vertex `id`, split at the first ` = ` into the name and the rest.
fn label_of<'a>(dot: &'a str, id: &str) -> (&'a str, &'a str) {
    let line = vertex_line(dot, id);
    let label = attr(line, "label").unwrap_or_else(|| panic!("no label in {line}"));
    label
        .split_once(" = ")
        .unwrap_or_else(|| panic!("the label of an instance is `名前 = 種類…: 型 at クロック`: {label}"))
}

/// S-1084 (2) (provisional, the form the work ticket gives): the label of the vertex of an instance with modifiers is the kind and the
/// modifiers in the order they are written with the N as a value, then the type and the clock of the value of the chain at the call side
/// (§11.9: `lp~(p).down~(4)` is a value of `sample / 4`). The name before the `=` is the name of the node (§11.6, S-1139 (a): the node of a
/// `let` that is a tick is `b.lp_0`, `_out.lp_0` in the output expression; as of the nodes with no name of `tools.md` §1.1 the label drops the
/// qualification: `lp_0 = lp~: …`), and a chain whose ratio is one is at `sample`.
#[test]
fn the_label_of_an_instance_with_modifiers_writes_the_modifiers_and_the_clock_of_the_chain() {
    let dot = graph_of_f();
    // SPEC-GAP(S-1084): `tools.md` §1.1 has no label for modifiers; the provisional form is `<name> = lp~.down~(4): F32 at (sample / 4)`.
    let cases = [
        ("b.lp_0", "lp~.down~(4): F32 at (sample / 4)"),
        ("c.lp_0", "lp~.down~(2).down~(4): F32 at (sample / 8)"),
        ("e.lp_0", "lp~.down~(4).up~(2): F32 at (sample / 2)"),
        ("_out.lp_0", "lp~.down~(8): F32 at (sample / 8)"),
    ];
    for (id, rest) in cases {
        let (name, got) = label_of(&dot, id);
        assert_eq!(got, rest, "the label of \"{id}\"");
        // S-1139 (a): the node of a `let` of a tick is named apart from the `let` (`b.lp_0`), so it is a node with no name of `tools.md`
        // §1.1, whose label drops the qualification (`lp_0 = …`, as `a.prev_0` of `let a = prev~(p at (sample / 4))` is `prev_0 = prev~`).
        let last = id.rsplit('.').next().unwrap();
        assert_eq!(name, last, "the name in the label of \"{id}\"");
    }
    // The `let` of the tick is a vertex of its own (`名前: 型 at クロック`), and the node is drawn into it.
    assert_eq!(attr(vertex_line(&dot, "b"), "label"), Some("b: F32 at (sample / 4)"), "the vertex of the `let` b");
    assert!(dot.lines().map(str::trim).any(|l| l.starts_with("\"b.lp_0\" -> \"b\"")), "no edge b.lp_0 -> b:\n{dot}");
    // The chain whose ratio is one is a `let` whose clock is `sample`, so the `let` names the node (§11.6: the `let` of a tick only is
    // qualified) and the clock is `sample`.
    let (name, got) = label_of(&dot, "d");
    assert_eq!((name, got), ("d", "lp~.down~(2).up~(2): F32 at sample"));
    // The call with no modifier keeps its label.
    let (name, got) = label_of(&dot, "n");
    assert_eq!((name, got), ("n", "lp~: F32 at sample"));
}

/// S-1084 (2): no colour is added. Every vertex is gray (`init` and a constant), blue (`block`) or black (`sample`), and the vertices of a tick
/// are black as `sample` is (§1.1); the edge of the head argument goes from the input to the node as the edge of any call does.
#[test]
fn a_chain_adds_no_colour_and_the_head_argument_has_its_edge() {
    let dot = graph_of_f();
    // SPEC-GAP(S-1084): `tools.md` §1.1 names the colours of `init`, `block` and `sample` only; the provisional reading (2) is that a tick is
    // black, as `sample` is, and no colour is added.
    for line in dot.lines().map(str::trim).filter(|l| l.starts_with('"') && l.contains(" [") && !l.contains("->")) {
        let colour = attr(line, "color").unwrap_or_else(|| panic!("a vertex has a colour: {line}"));
        assert!(
            colour.starts_with("gray") || colour.starts_with("grey") || colour == "blue" || colour == "black",
            "a colour of the three: {line}"
        );
    }
    for id in ["b.lp_0", "c.lp_0", "e.lp_0", "_out.lp_0", "d", "n"] {
        assert_eq!(attr(vertex_line(&dot, id), "color"), Some("black"), "the vertex \"{id}\" is black");
    }
    assert_eq!(attr(vertex_line(&dot, "p"), "color"), Some("blue"), "the `block` input is blue");
    for to in ["b.lp_0", "c.lp_0", "e.lp_0", "_out.lp_0"] {
        let edge = format!("\"p\" -> \"{to}\"");
        let line = dot
            .lines()
            .map(str::trim)
            .find(|l| l.starts_with(&edge))
            .unwrap_or_else(|| panic!("no edge {edge}:\n{dot}"));
        assert!(!line.contains("dashed"), "the edge of an argument is solid: {line}");
    }
    for to in ["d", "n"] {
        let edge = format!("\"x\" -> \"{to}\"");
        assert!(dot.lines().map(str::trim).any(|l| l.starts_with(&edge)), "no edge {edge}:\n{dot}");
    }
}
