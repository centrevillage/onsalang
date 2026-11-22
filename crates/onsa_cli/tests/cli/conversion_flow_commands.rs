//! A conversion flow in the commands of `onsa` (W7-09 U4a/t, W7-16 U5b2/t; spec §11.9, §11.6, §11.3, §18.1, `spec/tools.md` §1.1; S-566, S-567,
//! S-1078, S-1088, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - The Core of the ticks is W7-16. A flow with an input or an output at `sample / N` is lowered, and so is a call of it with no modifier (U5b2); so are the body of a conversion flow with a port at `sample * N` and a chain
//!   of `.down~(N)` that gathers or deals at its first boundary over it (U6a2, S-1207, S-1214: `build`, `dump --core` and `test` end with 0, and `onsa interface` writes the size of its state). `build`, `dump --core` and `test`
//!   stop at a package that has a call of a flow with a port at `sample * N` with no chain (a burst at the caller), a chain that gathers or deals past its first boundary or has an up (U6b), with E0200 and with nothing
//!   else (no internal error), on the file of the flow, while `check` reads it with no diagnostic. A chain of `.down~(N)` over a flow with an input at `sample / N` gathers and deals nothing and is lowered (W7-16 U6a1/t).
//! - `onsa interface` writes the heading of the flow with the clock of each port as the ratio (`sample / 4`, `sample * 2`): the
//!   text of the declaration, not the type that the body sees (the array of a port at `sample * N`).
//! - `onsa graph` of such a flow has a vertex for each port with the ratio in its label, the colours of the three clocks, and the
//!   edges of the values that are read (§1.1 draws an input as `名前: 型 at クロック`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::assert_lowers;
use crate::test_support::{Dir, diagnostics, doc_of, run};

const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

const FLOWS: &str = "\
flow dup2(x: F32 at sample) -> F32 at (sample * 2) {
  [x, x]
}

flow ramp4(lf: F32 at (sample / 4)) -> F32 at sample {
  lf at sample
}

flow avg4(x: F32 at sample) -> F32 at (sample / 4) {
  fold4~(x).down~(4)
}

flow fold4(x: F32 at (sample * 4)) -> F32 at sample {
  (x[0] + x[1] + x[2] + x[3]) * 0.25
}

";

/// Bodies that `check` accepts, each with a conversion flow that is declared and one that is run (the three kinds of port).
const BODIES: [&str; 4] = [
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  fold4~(x).down~(4) at sample\n}\n",
    "pub flow f(lf: F32 at (sample / 2)) -> F32 at sample {\n  dup2~(lf).down~(2)\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  ramp4~(avg4~(x))\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n",
];

fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

// ----------------------------------------------------------------------------- the Core of the ports

/// A package whose flows have a derived clock in a port is read by `check` with no diagnostic (the declarations, the calls and the chains are right, W7-09 U4a), and since W7-16 U6a2 `build`, `dump --core` and `test`
/// lower it (S-1207, S-1214: a body with a port at `sample * N` is lowered, a chain of `.down~(N)` gathers its input and deals its output at its first boundary, and `ramp4~(avg4~(x))` reads an output at `sample / 4`
/// of a flow that gathers) and run its test. The last body runs none of the flows (they are declared): they are in the package all the same.
#[test]
fn a_package_with_conversion_flows_is_lowered_by_build_dump_core_and_test() {
    for (k, body) in BODIES.iter().enumerate() {
        assert_lowers(&format!("conversion_core_lowers_{k}"), &format!("{FLOWS}{body}"), &[]);
    }
}

/// The callees of [`callers_of_derived_inputs`]: an input at `sample / 4` and one at `sample * 2`.
const CALLEES: &str = "\
flow slow4(g: F32 at (sample / 4)) -> F32 at sample {
  g at sample
}

flow fast2(g: F32 at (sample * 2)) -> F32 at sample {
  g[0] + g[1]
}
";

/// A flow with no port, `let` or node of a derived clock of its own that calls a flow with an input of a derived clock (a value
/// of `block`, of `init`, a constant or of `sample`, with no chain and in `.down~(2)`, and in `if~` and `par~`), each a flow of
/// its own: its node reads the argument at the tick of that input (§11.9). A `sample` value is not passed where it would be
/// made slower (E0815, §11.3). Returns the source and the number of flows that stay E0200 (after U6a2): each call of the callee `fast2` (a port at `sample * 2`) with no chain, which takes a burst at the caller (U6b), and in `if~`
/// and `par~`. The callee `fast2` itself and the calls of it in a `.down~(2)` (which gather its port at the caller's `sample`, W7-16 U6a2) are lowered, and so are the calls of `slow4` with no chain (U5b2); the calls of `slow4`
/// in a chain are not in this package (they are in the case of `a_caller_of_an_input_at_sample_over_n_with_a_down_chain_is_lowered`).
fn callers_of_derived_inputs() -> (String, usize) {
    let mut calls = Vec::new();
    let mut stay = 0;
    for callee in ["slow4", "fast2"] {
        for arg in ["p", "i", "1.0", "x"] {
            for down in [false, true] {
                let skip = if callee == "slow4" { down || arg == "x" } else { arg == "x" && !down };
                if skip {
                    continue;
                }
                stay += usize::from(callee == "fast2" && !down);
                calls.push(if down {
                    format!("x + ({callee}~({arg}).down~(2) at sample)")
                } else {
                    format!("x + {callee}~({arg})")
                });
            }
        }
        stay += if callee == "fast2" { 2 } else { 0 };
        calls.push(format!("if~ (p > 0.0) {{ {callee}~(p) }} else {{ x }}"));
        calls.push(format!("let ys = par~ k in 0..<2 {{ {callee}~(p) }}\n  ys[0] + ys[1]"));
    }
    let flows = calls.iter().enumerate().map(|(k, body)| {
        format!("flow c{k}(p: F32 at block, i: F32 at init, x: F32 at sample) -> F32 at sample {{\n  {body}\n}}\n")
    });
    (format!("{CALLEES}\n{}", flows.collect::<Vec<_>>().join("\n")), stay)
}

/// A flow that calls a flow with an input at `sample * 2` with no chain reads the argument at that tick (a burst of the caller), so that it stops at the gate of the Core (E0200 until W7-16 U6b, Q-09): `build`, `dump --core`
/// and `test` report one E0200 for each of those flows of the package and no internal error (W7-09 U4a/b #1: the gate saw the ports, `let`s and nodes of a flow and not the ticks its nodes read their arguments at), and
/// `check` reads the package with no diagnostic. The callee `fast2` itself, the calls of it in a `.down~(2)` (the input is gathered at the caller's `sample`, W7-16 U6a2), `slow4`, an input at `sample / 4`, and the
/// calls of it with no chain have no E0200 (W7-16 U5b2).
#[test]
fn a_caller_of_an_input_at_sample_times_with_no_chain_is_e0200_for_build_dump_core_and_test() {
    let (src, flows) = callers_of_derived_inputs();
    let d = Dir::bare("conversion_core_gate_callers");
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", &src);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 0, "check reads the flows: {}{}\n{src}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}\n{src}", out.stdout);
    let dir = d.arg();
    let commands: [(&str, Vec<&str>); 3] = [
        ("build", vec!["build", "--target", "host"]),
        ("dump --core", vec!["dump", "--core", dir.as_str()]),
        ("test", vec!["test"]),
    ];
    for (name, args) in commands {
        let out = run(d.root(), &args);
        let both = format!("{}{}", out.stdout, out.stderr);
        assert_eq!(out.code, 1, "{name}: {both}");
        assert!(!both.contains("internal error"), "{name}: {both}");
        let lines = error_lines(&both);
        assert!(lines.iter().all(|l| l.contains("error[E0200]")), "{name}: only E0200: {both}");
        assert_eq!(lines.len(), flows, "{name}: one E0200 for each flow that stays: {both}");
    }
}

/// The calls of a flow with an input at `sample / 4` with no chain (a value of `block`, of `init`, a constant, in `if~` and `par~`), with the callee, make a package that is lowered (W7-16 U5b2: the
/// argument is read at the tick of the input, a stage of the caller, §11.9) and runs its test.
#[test]
fn a_caller_of_an_input_at_sample_over_n_with_no_chain_is_lowered() {
    let mut calls = Vec::new();
    for arg in ["p", "i", "1.0"] {
        calls.push(format!("x + slow4~({arg})"));
    }
    calls.push("if~ (p > 0.0) { slow4~(p) } else { x }".to_string());
    calls.push("let ys = par~ k in 0..<2 { slow4~(p) }\n  ys[0] + ys[1]".to_string());
    let flows = calls.iter().enumerate().map(|(k, body)| {
        format!("flow c{k}(p: F32 at block, i: F32 at init, x: F32 at sample) -> F32 at sample {{\n  {body}\n}}\n")
    });
    let src = format!(
        "flow slow4(g: F32 at (sample / 4)) -> F32 at sample {{\n  g at sample\n}}\n\n{}",
        flows.collect::<Vec<_>>().join("\n")
    );
    assert_lowers("conversion_core_slow_callers", &src, &[]);
}

/// The calls of a flow with an input at `sample / 4` in a `.down~(2)` (a value of `block`, of `init`, a constant, in `if~` and `par~`) gather and deal nothing (the port is slower than the part): the package
/// is lowered and runs its test (W7-16 U6a1, S-1207).
#[test]
fn a_caller_of_an_input_at_sample_over_n_with_a_down_chain_is_lowered() {
    let mut calls = Vec::new();
    for arg in ["p", "i", "1.0"] {
        calls.push(format!("x + (slow4~({arg}).down~(2) at sample)"));
    }
    calls.push("if~ (p > 0.0) { slow4~(p).down~(2) at sample } else { x }".to_string());
    calls.push("let ys = par~ k in 0..<2 { slow4~(p).down~(2) at sample }\n  ys[0] + ys[1]".to_string());
    let flows = calls.iter().enumerate().map(|(k, body)| {
        format!("flow c{k}(p: F32 at block, i: F32 at init, x: F32 at sample) -> F32 at sample {{\n  {body}\n}}\n")
    });
    let src = format!(
        "flow slow4(g: F32 at (sample / 4)) -> F32 at sample {{\n  g at sample\n}}\n\n{}",
        flows.collect::<Vec<_>>().join("\n")
    );
    assert_lowers("conversion_core_slow_callers_down", &src, &[]);
}

// ----------------------------------------------------------------------------- the interface

const PORTS_SOURCE: &str = "\
pub flow g(lf: F32 at (sample / 4), x: F32 at (sample * 2), p: F32 at block) -> F32 at (sample * 2) {
  [(lf at sample) * p, x[1]]
}
";

/// The heading of the flow lists each port with its clock as the declaration has it, the ratio included: `onsa interface` reads
/// the signatures (§18 "シグネチャ") and the ratio is the clock of the port (the array that the body sees is not the type of the
/// port). The command ends with 0 and with no internal error.
#[test]
fn interface_lists_the_ratio_of_each_port_of_a_conversion_flow() {
    let d = Dir::pkg("conversion_interface");
    let file = d.file("m.onsa", PORTS_SOURCE);
    let out = run(d.root(), &["interface", &file]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    let lines: Vec<&str> = out.stdout.lines().map(str::trim).collect();
    let find = |start: &str| {
        *lines.iter().find(|l| l.starts_with(start)).unwrap_or_else(|| panic!("no line `{start}…`:\n{}", out.stdout))
    };
    assert!(find("lf: F32 at ").contains("sample / 4"), "the slow input: {}", find("lf: F32 at "));
    assert!(find("x: F32 at ").contains("sample * 2"), "the input at sample times: {}", find("x: F32 at "));
    assert_eq!(find("p: F32 at "), "p: F32 at block,", "the parameter keeps its clock");
    assert!(find(") -> F32 at ").contains("sample * 2"), "the output: {}", find(") -> F32 at "));
    assert!(!out.stdout.contains("[F32; 2] at"), "the port is not written as the array of the body: {}", out.stdout);
}

// ----------------------------------------------------------------------------- the graph

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

/// `spec/tools.md` §1.1: an input is an ellipse with `名前: 型 at クロック` and an output a double octagon with `out: 型 at クロック`; the
/// colours are those of `init`/constants (gray), `block` (blue) and `sample` (black); an edge goes from the value that is read to the
/// one that reads it. For a conversion flow the label of a port has the ratio of its clock. The colour of a tick is not fixed by §1.1
/// (S-1084 is open), so only that it is one of the three is asked, as in the graph of a chain.
#[test]
fn graph_of_a_conversion_flow_has_a_vertex_for_each_port_with_its_ratio() {
    let d = Dir::pkg("conversion_graph");
    let file = d.file("m.onsa", PORTS_SOURCE);
    let out = run(d.root(), &["graph", "g", &file]);
    assert_eq!(out.code, 0, "onsa graph g: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    let dot = out.stdout;

    // SPEC-GAP(S-1084): the clock of a derived port is written in the label as `sample / 4`; whether the parenthesis of the declaration
    // (`at (sample / 4)`) is kept is not written, so only the ratio is asked.
    for (id, name, ratio) in
        [("lf", "lf: F32 at ", "sample / 4"), ("x", "x: F32 at ", "sample * 2"), ("_out", "out: ", "sample * 2")]
    {
        let line = vertex_line(&dot, id);
        let label = attr(line, "label").unwrap_or_else(|| panic!("a label in {line}"));
        assert!(label.starts_with(name) && label.contains(ratio), "the label of \"{id}\": {label}");
    }
    assert_eq!(attr(vertex_line(&dot, "p"), "label"), Some("p: F32 at block"));
    assert_eq!(attr(vertex_line(&dot, "p"), "color"), Some("blue"), "the `block` input is blue");
    for id in ["lf", "x", "_out"] {
        let colour = attr(vertex_line(&dot, id), "color").unwrap_or_else(|| panic!("a colour for \"{id}\""));
        assert!(
            colour.starts_with("gray") || colour == "blue" || colour == "black",
            "a colour of the three for \"{id}\": {colour}"
        );
    }
    for from in ["lf", "x", "p"] {
        let edge = format!("\"{from}\" -> \"_out\"");
        let line = dot
            .lines()
            .map(str::trim)
            .find(|l| l.starts_with(&edge))
            .unwrap_or_else(|| panic!("no edge {edge}:\n{dot}"));
        assert!(!line.contains("dashed"), "the edge of a value that is read is solid: {line}");
    }
}
