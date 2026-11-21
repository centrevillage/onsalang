//! A flow with a chain of `.down~(N)` and `.up~(N)` in the commands of `onsa` (W7-09 U3b/t; spec §11.9, §11.3, §11.6, §18.1,
//! `spec/tools.md` §1.1; S-566, S-1084, S-1139, Q-09): what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - The Core of the ticks is W7-16, so `build`, `dump --core` and `test` stop at a flow that has a chain with E0200 and with nothing else
//!   (no internal error), on the file of the flow, while `check` reads it with no diagnostic and `onsa interface` ends with 0 (the size of
//!   the state, which W7-16 changes, is not pinned).
//! - `onsa graph` of such a flow: the label of the vertex of an instance with modifiers writes the kind and then the modifiers in the order
//!   they are written, with the N as a value, and the type and the clock of the value of the chain at the call side (S-1084, provisional
//!   reading (2): `lp_0 = lp~.down~(4): F32 at sample / 4`). No colour is added (the vertices keep the three of §1.1, and a tick has the black
//!   of `sample`), and the edge of the head argument is the edge of any call. The node whose `let` is a tick has the name of S-1139 (a)
//!   (`b.lp_0`, a node with no name of §1.1 whose label drops the qualification, drawn into the vertex of the `let` `b`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::test_support::{Dir, code_of, diagnostics, doc_of, run, span_of, test_json, tests_of};

const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

const LP: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n\n";

/// Flows with a chain whose ratio is not one, each in a form that `check` accepts (modifier_chain_clocks.onsa).
const BODIES: [&str; 3] = [
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  x * (lp~(p).down~(4) at sample)\n}\n",
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let y = lp~(p).down~(2).down~(2)\n  x * (y at sample)\n}\n",
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let a = p at (sample / 4)\n  let y = lp~(a).down~(4)\n  x * (y at sample)\n}\n",
];

fn source(body: &str) -> String {
    format!("{LP}{body}\ntest \"reads\" {{\n  assert 1 + 1 == 2\n}}\n")
}

fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

fn package(tag: &str, body: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", &source(body));
    d
}

// ----------------------------------------------------------------------------- the gate of the Core

/// W7-09 (the Core of the ticks is W7-16): `check` reads the flow with a chain, and `build`, `dump --core` and `test` stop at it with E0200
/// and nothing else, on the file of the flow (Q-09: what the spec has and this version does not carry is E0200, not a wrong output).
#[test]
fn a_flow_with_a_down_chain_is_e0200_for_build_dump_core_and_test() {
    for (k, body) in BODIES.iter().enumerate() {
        let d = package(&format!("chain_core_gate_{k}"), body);

        let out = run(d.root(), &["check", "--json"]);
        assert_eq!(out.code, 0, "{body}: check reads the flow: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "{body}: {}", out.stdout);

        let dir = d.arg();
        let commands: [(&str, Vec<&str>); 3] = [
            ("build", vec!["build", "--target", "host"]),
            ("dump --core", vec!["dump", "--core", dir.as_str()]),
            ("test", vec!["test"]),
        ];
        for (name, args) in commands {
            let out = run(d.root(), &args);
            assert_eq!(out.code, 1, "{body}: {name}: {}{}", out.stdout, out.stderr);
            let both = format!("{}{}", out.stdout, out.stderr);
            let lines = error_lines(&both);
            assert!(!lines.is_empty(), "{body}: {name}: an error line: {both}");
            for l in &lines {
                assert!(l.contains("error[E0200]"), "{body}: {name}: only E0200: {l}");
                assert!(l.contains("main.onsa:"), "{body}: {name}: E0200 is on the file of the flow: {l}");
            }
            assert!(!both.contains("internal error"), "{body}: {name}: {both}");
        }

        let (out, doc) = test_json(d.root(), &[]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        let ds = diagnostics(&doc);
        assert!(!ds.is_empty() && ds.iter().all(|x| code_of(x) == "E0200"), "{body}: {doc}");
        assert!(ds.iter().all(|x| span_of(&x["span"]).file == "main.onsa"), "{body}: {doc}");
        assert!(tests_of(&doc).is_empty(), "{body}: nothing is run: {doc}");
    }
}

/// `onsa interface` reads the signatures and the kinds, not the Core: the flow with a chain is listed, the command ends with 0 and no
/// internal error (the size of the state is W7-16's, so no text of it is read here).
#[test]
fn interface_of_a_flow_with_a_down_chain_ends_with_zero() {
    for (k, body) in BODIES.iter().enumerate() {
        let d = package(&format!("chain_interface_{k}"), body);
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
    // SPEC-GAP(S-1084): `tools.md` §1.1 has no label for modifiers; the provisional form is `<name> = lp~.down~(4): F32 at sample / 4`.
    let cases = [
        ("b.lp_0", "lp~.down~(4): F32 at sample / 4"),
        ("c.lp_0", "lp~.down~(2).down~(4): F32 at sample / 8"),
        ("e.lp_0", "lp~.down~(4).up~(2): F32 at sample / 2"),
        ("_out.lp_0", "lp~.down~(8): F32 at sample / 8"),
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
    assert_eq!(attr(vertex_line(&dot, "b"), "label"), Some("b: F32 at sample / 4"), "the vertex of the `let` b");
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
