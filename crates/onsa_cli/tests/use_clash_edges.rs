//! A `use` that takes a name that became E0304 or E0305 is no dependency (E0310), seen from the command line (spec
//! §15.1, §18.1; S-688, S-685, S-678, S-682; W4-03 U3d/t).
//!
//! What the spec fixes, and so what is checked here:
//! - a name that is E0304 or E0305 is an error name in its space (§18.1), and the `use` that takes it, the side
//!   that was reported and the side that was not, is not counted as a dependency (§15.1). So the modules that
//!   take each other through such a `use` are no cycle: the diagnostics are the E0304 or E0305 alone. The
//!   control of each form is the same modules with the name changed so that there is no clash, which is a cycle
//!   (E0310);
//! - the result does not depend on the order of the lines of two `use` of one name (the cyclic one first or
//!   last);
//! - the other names of the same `use` list that bind are counted (S-685): a list with a clashing name and a
//!   name that closes the cycle is a cycle. The spec leaves out the place of the E0310 of one cycle and
//!   which of the two errors of one unit is reported, so only the code E0310 is asked for;
//! - the candidate of S-663 (`use fx.a` to `use a`) is given when the `use` it adds closes no cycle, and a
//!   `use` that is E0304 does not close one; applying it leaves the E0304 and nothing else.
//!
//! The same cases, with the places of the marks, are `tests/spec/packages/clash_edge_*`.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause.

mod test_support;

use std::collections::BTreeSet;
use std::path::Path;

use serde_json::Value;
use test_support::*;

fn check_json(cwd: &Path) -> (Out, Value) {
    let out = run(cwd, &["check", "--json", "."]);
    let doc = doc_of(&out);
    (out, doc)
}

fn codes(doc: &Value) -> BTreeSet<String> {
    diagnostics(doc).iter().map(|d| str_of(d, "code").to_string()).collect()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|c| c.to_string()).collect()
}

fn f(name: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  1\n}}\n")
}

type Files = Vec<(&'static str, String)>;

fn package(tag: &str, files: &Files) -> Dir {
    let d = Dir::pkg(tag);
    for (file, text) in files {
        d.write(file, text);
    }
    d
}

/// A form: the files that clash, the codes they give (no E0310), and the control (the same with the name
/// changed so that nothing clashes), which is a cycle.
struct Form {
    tag: &'static str,
    clash: Files,
    codes: &'static [&'static str],
    control: Files,
}

fn forms() -> Vec<Form> {
    vec![
        Form {
            tag: "item_use",
            clash: vec![("a.onsa", format!("use b\n\n{}", f("b"))), ("b.onsa", format!("use a\n\n{}", f("g")))],
            codes: &["E0304"],
            control: vec![("a.onsa", format!("use b\n\n{}", f("bb"))), ("b.onsa", format!("use a\n\n{}", f("g")))],
        },
        Form {
            tag: "item_before_use",
            clash: vec![("a.onsa", format!("{}\nuse b\n", f("b"))), ("b.onsa", format!("use a\n\n{}", f("g")))],
            codes: &["E0304"],
            control: vec![("a.onsa", format!("{}\nuse b\n", f("bb"))), ("b.onsa", format!("use a\n\n{}", f("g")))],
        },
        Form {
            tag: "use_use_cyclic_first",
            clash: vec![
                ("a.onsa", format!("use b\nuse kp.b\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/b.onsa", f("k")),
            ],
            codes: &["E0304"],
            control: vec![
                ("a.onsa", format!("use b\nuse kp.bb\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/bb.onsa", f("k")),
            ],
        },
        Form {
            tag: "use_use_cyclic_last",
            clash: vec![
                ("a.onsa", format!("use kp.b\nuse b\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/b.onsa", f("k")),
            ],
            codes: &["E0304"],
            control: vec![
                ("a.onsa", format!("use kp.bb\nuse b\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/bb.onsa", f("k")),
            ],
        },
        Form {
            tag: "use_use_both_cyclic",
            clash: vec![
                ("a.onsa", format!("use b\nuse kp.b\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/b.onsa", format!("use a\n\n{}", f("k"))),
            ],
            codes: &["E0304"],
            control: vec![
                ("a.onsa", format!("use b\nuse kp.bb\n\n{}", f("f"))),
                ("b.onsa", format!("use a\n\n{}", f("g"))),
                ("kp/bb.onsa", format!("use a\n\n{}", f("k"))),
            ],
        },
        Form {
            tag: "prelude_enum",
            clash: vec![
                ("p.onsa", format!("use q.{{Option}}\n\n{}", f("f"))),
                ("q.onsa", "use p.{f}\n\npub enum Option {\n  Nothing,\n}\n".to_string()),
            ],
            codes: &["E0304"],
            control: vec![
                ("p.onsa", format!("use q.{{Choice}}\n\n{}", f("f"))),
                ("q.onsa", "use p.{f}\n\npub enum Choice {\n  Nothing,\n}\n".to_string()),
            ],
        },
        Form {
            tag: "builtin_type",
            clash: vec![
                ("p.onsa", format!("use q.{{F32}}\n\n{}", f("f"))),
                ("q.onsa", "use p.{f}\n\npub struct F32 {\n  v: I32,\n}\n".to_string()),
            ],
            codes: &["E0304"],
            control: vec![
                ("p.onsa", format!("use q.{{Gain}}\n\n{}", f("f"))),
                ("q.onsa", "use p.{f}\n\npub struct Gain {\n  v: I32,\n}\n".to_string()),
            ],
        },
        Form {
            tag: "builtin_flow",
            clash: vec![
                ("p.onsa", format!("use q.{{prev}}\n\n{}", f("f"))),
                ("q.onsa", format!("use p.{{f}}\n\n{}", f("prev"))),
            ],
            codes: &["E0304"],
            control: vec![
                ("p.onsa", format!("use q.{{past}}\n\n{}", f("f"))),
                ("q.onsa", format!("use p.{{f}}\n\n{}", f("past"))),
            ],
        },
        Form {
            tag: "child_module_namespace",
            clash: vec![
                ("c.onsa", format!("use a.sub\n\n{}", f("f"))),
                ("a.onsa", f("sub")),
                ("a/sub.onsa", format!("use c.{{f}}\n\n{}", f("g"))),
            ],
            codes: &["E0304"],
            control: vec![
                ("c.onsa", format!("use a.sub\n\n{}", f("f"))),
                ("a.onsa", f("other")),
                ("a/sub.onsa", format!("use c.{{f}}\n\n{}", f("g"))),
            ],
        },
        Form {
            tag: "flow_and_function",
            clash: vec![
                ("a.onsa", format!("use b.{{gain}}\n\n{}", f("f"))),
                (
                    "b.onsa",
                    "use a.{f}\n\npub flow gain(x: F32 at sample) -> F32 at sample {\n  x\n}\n\npub fn gain() -> F32 {\n  1.0\n}\n"
                        .to_string(),
                ),
            ],
            codes: &["E0305"],
            control: vec![
                ("a.onsa", format!("use b.{{gain}}\n\n{}", f("f"))),
                ("b.onsa", "use a.{f}\n\npub flow gain(x: F32 at sample) -> F32 at sample {\n  x\n}\n".to_string()),
            ],
        },
    ]
}

/// §15.1, §18.1, S-688: every form below has the diagnostics of its clash alone, and the same modules without the
/// clash are a cycle.
#[test]
fn a_use_of_a_name_that_clashed_is_no_dependency_and_the_control_is_a_cycle() {
    let mut problems = Vec::new();
    for form in forms() {
        let d = package(&format!("edge_{}", form.tag), &form.clash);
        let (out, doc) = check_json(d.root());
        if out.code != 1 || codes(&doc) != set(form.codes) {
            problems.push(format!("{}: want only {:?}, exit code 1: {}", form.tag, form.codes, doc["diagnostics"]));
        }
        let d = package(&format!("edge_{}_control", form.tag), &form.control);
        let (out, doc) = check_json(d.root());
        if out.code != 1 || !codes(&doc).contains("E0310") {
            problems.push(format!("{}: the control is a cycle: {}", form.tag, doc["diagnostics"]));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// §15.1, §18.1, S-688: with the E0304 on a `use` of an item of one module in the middle of a ring of three,
/// the ring is cut there and the diagnostics are the E0304 alone; the ring with the names right is a cycle.
#[test]
fn a_ring_of_three_is_cut_at_the_use_that_clashed() {
    let ring = |item: &str| -> Files {
        vec![
            ("a.onsa", format!("use b.{{gb}}\n\n{}", f("ga"))),
            ("b.onsa", format!("use c.{{gc}}\n\n{}", f("gb"))),
            ("c.onsa", format!("use a.{{ga}}\n\n{}\n{}", f("gc"), f(item))),
        ]
    };
    // `c` takes `ga`, and an item `ga` of `c` clashes with it
    let d = package("edge_ring_clash", &ring("ga"));
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0304"])), "{}", doc["diagnostics"]);
    let d = package("edge_ring_control", &ring("other"));
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1);
    assert!(codes(&doc).contains("E0310"), "{}", doc["diagnostics"]);
}

/// §15.1, S-685, S-688: the other names of the list that bind are counted. `use b.{y, x}` with an item `x` of its
/// own module takes `y`, which closes the cycle with the `use` of `b`: there is an E0310 (the place of it, and
/// whether the E0304 of the same unit is reported beside it, are not fixed). With only the clashing name in
/// the list, or with every name of the list clashing, there is the E0304 alone, one report for the `use`.
#[test]
fn the_names_of_a_list_that_bind_are_counted() {
    let b = format!("use a.{{f}}\n\n{}\n{}", f("x"), f("y"));
    let tail = format!("\n{}\n{}", f("f"), f("x"));
    let d =
        package("edge_list_other_closes", &vec![("a.onsa", format!("use b.{{y, x}}\n{tail}")), ("b.onsa", b.clone())]);
    let (out, doc) = check_json(d.root());
    assert_eq!(out.code, 1);
    let got = codes(&doc);
    assert!(got.contains("E0310"), "{}", doc["diagnostics"]);
    assert!(got.is_subset(&set(&["E0304", "E0310"])), "{}", doc["diagnostics"]);

    let d = package("edge_list_only_clash", &vec![("a.onsa", format!("use b.{{x}}\n{tail}")), ("b.onsa", b.clone())]);
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0304"])), "{}", doc["diagnostics"]);

    let tail_xy = format!("\n{}\n{}\n{}", f("f"), f("x"), f("y"));
    let d = package("edge_list_all_clash", &vec![("a.onsa", format!("use b.{{x, y}}\n{tail_xy}")), ("b.onsa", b)]);
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0304"])), "{}", doc["diagnostics"]);
    assert_eq!(diagnostics(&doc).len(), 1, "one report for the use: {}", doc["diagnostics"]);
}

/// §15.1, §18.1, S-682, S-688: `use fx.a` has the candidate that takes the package name off. The `use` it adds
/// depends on `a.sub`, which takes an item of `b` by a `use` that is E0304 (the item is written there too), so it
/// closes no cycle and the candidate is given (one candidate). Applying it leaves the E0304 of `a/sub.onsa`
/// and nothing else, and no candidate of that is left to apply: the loop stops there.
#[test]
fn the_candidate_that_closes_no_cycle_because_of_a_clash_is_given_and_the_loop_stops_at_the_clash() {
    let d = Dir::bare("edge_candidate");
    d.write("onsa.toml", "[package]\nname = \"fx\"\nedition = \"2026\"\n");
    d.write("b.onsa", &format!("use fx.a\n\n{}", f("g")));
    d.write("a/sub.onsa", &format!("use b.{{g}}\n\n{}", f("g")));
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0302", "E0304"])), "{}", doc["diagnostics"]);
    let e0302: Vec<&Value> = diagnostics(&doc).iter().filter(|x| str_of(x, "code") == "E0302").collect();
    assert_eq!(e0302.len(), 1);
    let fixes = array_of(e0302[0], "fixes");
    assert_eq!(fixes.len(), 1, "{}", doc["diagnostics"]);
    // apply the candidate: every edit replaces a span of `b.onsa` (one file here)
    let mut edits: Vec<(u64, u64, u64, u64, String)> = array_of(&fixes[0], "edits")
        .iter()
        .map(|e| {
            let sp = span_of(&e["span"]);
            assert_eq!(sp.file, "b.onsa");
            (sp.line, sp.col, sp.end_line, sp.end_col, str_of(e, "replace").to_string())
        })
        .collect();
    edits.sort();
    let text = std::fs::read_to_string(d.root().join("b.onsa")).unwrap();
    let mut lines: Vec<String> = text.lines().map(String::from).collect();
    for (line, col, end_line, end_col, rep) in edits.into_iter().rev() {
        assert_eq!(line, end_line, "a single-line edit");
        let l: Vec<char> = lines[line as usize - 1].chars().collect();
        let new: String = l[..col as usize - 1].iter().collect::<String>()
            + &rep
            + &l[end_col as usize - 1..].iter().collect::<String>();
        lines[line as usize - 1] = new;
    }
    d.write("b.onsa", &(lines.join("\n") + "\n"));
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0304"])), "{}", doc["diagnostics"]);
    assert_eq!(diagnostics(&doc).len(), 1, "{}", doc["diagnostics"]);
    assert!(array_of(&diagnostics(&doc)[0], "fixes").is_empty(), "{}", doc["diagnostics"]);
    assert_eq!(span_of(&diagnostics(&doc)[0]["span"]).file, "a/sub.onsa");
}

/// §15.1: the same shape with the name that clashes made right (the item `g` of `a/sub.onsa` renamed) is a cycle
/// through `a.sub`, so the candidate closes it and is not given (S-682): no candidate, and the cycle shows
/// when the name is written without `fx.`.
#[test]
fn the_same_candidate_is_left_out_when_the_use_does_close_a_cycle() {
    let d = Dir::bare("edge_candidate_control");
    d.write("onsa.toml", "[package]\nname = \"fx\"\nedition = \"2026\"\n");
    d.write("b.onsa", &format!("use fx.a\n\n{}", f("g")));
    d.write("a/sub.onsa", &format!("use b.{{g}}\n\n{}", f("other")));
    let (out, doc) = check_json(d.root());
    assert_eq!((out.code, codes(&doc)), (1, set(&["E0302"])), "{}", doc["diagnostics"]);
    assert!(array_of(&diagnostics(&doc)[0], "fixes").is_empty(), "{}", doc["diagnostics"]);
}

/// §15.1: `onsa explain E0310` runs; its text is not checked against the rule of this file (the text is a
/// placeholder in this version).
#[test]
fn explain_e0310_runs() {
    let d = Dir::bare("edge_explain");
    let out = run(d.root(), &["explain", "E0310"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("E0310"), "{}", out.stdout);
}
