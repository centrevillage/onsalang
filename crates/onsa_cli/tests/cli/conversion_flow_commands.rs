//! A conversion flow in the commands of `onsa` (W7-09 U4a/t, W7-16 U5b2/t; spec §11.9, §11.6, §11.3, §18.1, `spec/tools.md` §1.1; S-566, S-567,
//! S-1078, S-1088, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - The Core of the ticks is W7-16. A flow with an input or an output at `sample / N` is lowered, and so is a call of it with no modifier (U5b2); so are the body of a conversion flow with a port at `sample * N`, a chain
//!   of `.down~(N)` that gathers or deals over it (U6a2, U6b1, S-1207, S-1214: `build`, `dump --core` and `test` end with 0, and `onsa interface` writes the size of its state) and a call of a flow with a port or an output
//!   at `sample * N` with no chain, whose argument is a bundle of the caller, a `block` or `init` value or a constant (U6b2, S-1214 (3)), and a chain with an `.up~(N)`, also where its value is a bundle that a port at
//!   `sample * N` reads (U6b3). A chain of `.down~(N)` over a flow with an input at `sample / N` gathers and deals nothing and is lowered (W7-16 U6a1/t).
//! - `onsa interface` writes the heading of the flow with the clock of each port as the ratio (`sample / 4`, `sample * 2`): the
//!   text of the declaration, not the type that the body sees (the array of a port at `sample * N`).
//! - `onsa graph` of such a flow has a vertex for each port with the ratio in its label, the colours of the three clocks, and the
//!   edges of the values that are read (§1.1 draws an input as `名前: 型 at クロック`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::assert_lowers;
use crate::test_support::{Dir, run};

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

flow dup2(x: F32 at sample) -> F32 at (sample * 2) {
  [x, x + 1.0]
}
";

/// A flow with no port, `let` or node of a derived clock of its own that calls a flow with an input of a derived clock (a value
/// of `block`, of `init`, a constant or of `sample`, with no chain and in `.down~(2)`, and in `if~` and `par~`), each a flow of
/// its own: its node reads the argument at the tick of that input (§11.9). A `sample` value is not passed where it would be
/// made slower (E0815, §11.3). The callee `fast2` has a port at `sample * 2`: a call of it with no chain takes a bundle of the caller (U6b2; the 2 elements of a `block` or `init` value
/// or a constant are that value, S-1214 (3)), and so does the call with the output of `dup2` (a bundle) as the argument, in a `let`, through an alias and twice. The calls of it in a `.down~(2)` gather its port at the caller's `sample`
/// (W7-16 U6a2); the calls of `slow4` with no chain are lowered (U5b2) and the calls of `slow4` in a chain are in the case of `a_caller_of_an_input_at_sample_over_n_with_a_down_chain_is_lowered`.
fn callers_of_derived_inputs() -> String {
    let mut calls = Vec::new();
    for callee in ["slow4", "fast2"] {
        for arg in ["p", "i", "1.0", "x"] {
            for down in [false, true] {
                let skip = if callee == "slow4" { down || arg == "x" } else { arg == "x" && !down };
                if skip {
                    continue;
                }
                calls.push(if down {
                    format!("x + ({callee}~({arg}).down~(2) at sample)")
                } else {
                    format!("x + {callee}~({arg})")
                });
            }
        }
        calls.push(format!("if~ (p > 0.0) {{ {callee}~(p) }} else {{ x }}"));
        calls.push(format!("let ys = par~ k in 0..<2 {{ {callee}~(p) }}\n  ys[0] + ys[1]"));
    }
    calls.push("x + fast2~(dup2~(x))".to_string());
    calls.push("let u = dup2~(x)\n  let v = u\n  fast2~(v) + fast2~(u)".to_string());
    calls.push("if~ (p > 0.0) { fast2~(dup2~(x)) } else { x }".to_string());
    calls.push("let ys = par~ k in 0..<2 { fast2~(dup2~(x)) }\n  ys[0] + ys[1]".to_string());
    let flows = calls.iter().enumerate().map(|(k, body)| {
        format!("flow c{k}(p: F32 at block, i: F32 at init, x: F32 at sample) -> F32 at sample {{\n  {body}\n}}\n")
    });
    format!("{CALLEES}\n{}", flows.collect::<Vec<_>>().join("\n"))
}

/// A flow that calls a flow with an input at `sample * 2` with no chain takes a bundle of the caller: the argument of a `block` or `init` value or a constant is the 2 elements of that value, and the output of `dup2` is
/// the 2 elements of its frame (§11.9, S-1214 (3)). `check` reads the package with no diagnostic and `build`, `dump --core` and `test` lower it (W7-16 U6b2; it was E0200 until then: the gate saw the ports, `let`s and nodes of a
/// flow and not the ticks its nodes read their arguments at, W7-09 U4a/b #1) and run its test. The values are in `tests/spec/flow_semantics/bursts_values.onsa`.
#[test]
fn a_caller_of_an_input_at_sample_times_with_no_chain_is_lowered_by_build_dump_core_and_test() {
    assert_lowers("conversion_core_callers", &callers_of_derived_inputs(), &[]);
}

/// A bundle that an `.up~(N)` makes is read by a port at `sample * N` (W7-16 U6b3; it was E0200 until then; §11.9: "`.up~(N)` の出力は `sample * N` の値"): the call of `fast2` with the argument `thru~(p).up~(2)`, the
/// same in a `let` and in `if~`, are read by `check` with no diagnostic and lowered with the flow `ok` beside them, and the test of the package runs.
#[test]
fn a_bundle_made_by_an_up_is_lowered_by_build_dump_core_and_test() {
    let src = format!(
        "{CALLEES}\nflow thru(x: F32 at sample) -> F32 at sample {{\n  x\n}}\n\npub flow ok(p: F32 at block) -> F32 at sample {{\n  slow4~(p)\n}}\n\npub flow direct(p: F32 at block) -> F32 at sample {{\n  fast2~(thru~(p).up~(2))\n}}\n\npub flow in_let(p: F32 at block) -> F32 at sample {{\n  let u = thru~(p).up~(2)\n  fast2~(u)\n}}\n\npub flow in_if(p: F32 at block) -> F32 at sample {{\n  if~ (p > 0.0) {{ fast2~(thru~(p).up~(2)) }} else {{ 0.0 }}\n}}\n"
    );
    assert_lowers("conversion_core_up_burst", &src, &[]);
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

/// Flows whose output is at `sample * N`, `sample / N` and `sample`, with a chain in the body of two of them (W7-16 U7b/t; §11.9, §18.2).
const OUT_CLOCK_SOURCE: &str = "\
flow fold4(x: F32 at (sample * 4)) -> F32 at sample {
  (x[0] + x[1] + x[2] + x[3]) * 0.25
}

pub flow up(x: F32 at sample) -> F32 at (sample * 2) {
  [x, x]
}

pub flow avg4(x: F32 at sample) -> F32 at (sample / 4) {
  fold4~(x).down~(4)
}

pub flow plain(x: F32 at sample) -> F32 at sample {
  x
}

pub flow chain(x: F32 at sample) -> F32 at sample {
  fold4~(x).down~(4) at sample
}
";

/// `onsa interface --json` gives the clock of the output of a flow in the key `out_clock`, as `onsa interface` writes it after `-> F32 at ` of the
/// heading (§18.2 "シグネチャ", §11.9: the output of a conversion flow is at `sample * N` or `sample / N`, a flow with a chain has the clock of its own
/// output). The JSON is not fixed by the spec as a whole; what is checked is that the key is there for each flow, that it is the clock that the heading
/// of the text has (the text form is the one that the spec writes, S-1084), and that the derived ones are the ratios of the declarations.
#[test]
fn interface_json_gives_the_clock_of_the_output_of_a_flow() {
    let d = Dir::pkg("conversion_interface_out_clock");
    let file = d.file("m.onsa", OUT_CLOCK_SOURCE);
    let json = run(d.root(), &["interface", "--json", &file]);
    assert_eq!(json.code, 0, "{}{}", json.stdout, json.stderr);
    let doc: serde_json::Value = serde_json::from_str(&json.stdout).unwrap_or_else(|e| panic!("{e}:\n{}", json.stdout));
    let clocks: Vec<(String, String)> = doc["modules"][0]["items"]
        .as_array()
        .expect("items")
        .iter()
        .filter(|i| i["kind"] == "flow")
        .map(|i| {
            let name = i["name"].as_str().expect("name").to_string();
            let clock =
                i["out_clock"].as_str().unwrap_or_else(|| panic!("no `out_clock` of `{name}`: {i}")).to_string();
            (name, clock)
        })
        .collect();
    let names: Vec<&str> = clocks.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["fold4", "up", "avg4", "plain", "chain"], "the flows of the file, in order");
    // The heading of the text: `flow name(` … `) -> F32 at <clock>`.
    let text = run(d.root(), &["interface", &file]);
    assert_eq!(text.code, 0, "{}{}", text.stdout, text.stderr);
    let mut from_text: Vec<(String, String)> = Vec::new();
    for line in text.stdout.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("pub flow ").or_else(|| line.strip_prefix("flow ")) {
            from_text.push((rest.split('(').next().unwrap().to_string(), String::new()));
        } else if let Some(clock) = line.strip_prefix(") -> F32 at ") {
            from_text.last_mut().expect("a heading").1 = clock.to_string();
        }
    }
    assert_eq!(clocks, from_text, "the JSON has the clock of the heading of the text");
    let of = |name: &str| clocks.iter().find(|(n, _)| n == name).map(|(_, c)| c.as_str()).unwrap();
    assert!(of("up").contains("sample * 2"), "{clocks:?}");
    assert!(of("avg4").contains("sample / 4"), "{clocks:?}");
    assert_eq!(of("plain"), "sample");
    assert_eq!(of("chain"), "sample", "the chain inside does not change the clock of the output");
    assert_eq!(of("fold4"), "sample", "the input of a flow is at sample * 4, its output is not");
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
