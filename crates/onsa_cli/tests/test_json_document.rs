//! The document `onsa test --json` prints (spec §18.1, §18.2; S-215, S-233, R-162, S-241; W2-10).
//!
//! What the spec fixes, and so what is checked here:
//! - the standard output is one JSON object: the `diagnostics` array of `check --json` (an empty
//!   array when there is none) and a `tests` array of the results (§18.1). The spacing, the order
//!   of the keys and a key the reader does not know are not fixed, so no test forbids another key;
//! - a `tests` record has `module` (the module path, `dsp.voice` for `dsp/voice.onsa`), `name` (the
//!   value of the name, not its escaped text), `status` (`ok` or `failed`), and only a failed
//!   record has `failure`. The old `kind` key is gone (S-233). `failure` has `message`, `span` (the
//!   position of the expression that panicked, the whole statement for an `assert`, with the
//!   five keys of §18.1) and `calls` (always there). `calls` lists the positions of the calls from
//!   the place of the panic back to the body of the test, innermost first; its last element is in
//!   the body of the test, and when it is empty `span` is in the body of the test;
//! - `message` is promised for an `assert` (`assert <source of the expression>`) and for
//!   `panic(msg)` (`msg`) only. The wording of the panics the language raises is not fixed, so only
//!   that it is a string is checked;
//! - `span.file` is the path from the package root with `/`; a file of `std` or of a dependency is
//!   `<package name>/<path from its root>`, `std/dsp/test.onsa` for the test helpers (§18.1);
//! - `tests` is ordered by `module`, then `name`, as strings by code points (§18.1);
//! - when the checks stop the command (a diagnostic of the package, an E0200 that does not depend
//!   on the target, a manifest diagnostic) no test has run, and `tests` is an empty array (§18.1).
//!   The exit code is 1, or 2 for a diagnostic of `onsa.toml` (§18.2);
//! - `std.dsp.test.assert_near` fails with a panic at the position of its call (§11.8), so its
//!   failure is the call expression and `calls` is empty when the test calls it itself.
//!
//! The columns of a call position are checked at the start only: whether the position of a call
//! covers the callee alone or the whole call expression is not stated, and both start at the same
//! place for a call written `f(x)`.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use serde_json::Value;
use test_support::*;

fn pkg_run(tag: &str, files: &[(&str, &str)]) -> (Dir, Out, Value) {
    let d = Dir::pkg(tag);
    for (rel, text) in files {
        d.write(rel, text);
    }
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    (d, out, doc)
}

fn assert_call_starts(failure: &Value, want: &[(&str, u64, u64)]) {
    let got = call_spans(failure);
    assert_eq!(got.len(), want.len(), "calls: {failure}");
    for (g, (file, line, col)) in got.iter().zip(want) {
        assert_eq!((g.file.as_str(), g.line, g.col), (*file, *line, *col), "calls: {failure}");
        assert!(g.end_line > g.line || g.end_col > g.col, "a call position is not empty: {failure}");
    }
}

// ---------------------------------------------------------------- the document

const TWO_OK: &str = "test \"one\" {\n  assert 1 == 1\n}\n\ntest \"two\" {\n  assert 2 == 2\n}\n";

/// Spec §18.1: one object; `diagnostics` is an empty array when there is none; a record of an
/// `ok` test has `module`, `name` and `status` and no `failure`, and no `kind`.
#[test]
fn the_document_is_one_object_with_diagnostics_and_tests() {
    let (_d, out, doc) = pkg_run("doc_ok", &[("m.onsa", TWO_OK)]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let tests = tests_of(&doc);
    assert_eq!(tests.len(), 2, "{doc}");
    for (rec, name) in tests.iter().zip(["one", "two"]) {
        assert_eq!(str_of(rec, "module"), "m");
        assert_eq!(str_of(rec, "name"), name);
        assert_eq!(str_of(rec, "status"), "ok");
        assert!(rec.get("failure").is_none(), "an `ok` record has no `failure`: {rec}");
        assert!(rec.get("kind").is_none(), "the `kind` key is gone (S-233): {rec}");
    }
}

/// Spec §18.2: a failed test is exit code 1 and not a diagnostic: `diagnostics` stays empty, the
/// failure is in `tests`; the passing tests of the same run are `ok`.
#[test]
fn a_failed_test_is_a_record_and_not_a_diagnostic() {
    let src = format!("{TWO_OK}\ntest \"three\" {{\n  assert 1 == 2\n}}\n");
    let (_d, out, doc) = pkg_run("doc_fail", &[("m.onsa", &src)]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let status: Vec<&str> = tests_of(&doc).iter().map(|t| str_of(t, "status")).collect();
    // By name (§18.1): one, three, two (W2-10/i; the first version had the order of definition).
    assert_eq!(status, ["ok", "failed", "ok"], "{doc}");
    assert!(record(&doc, "m", "one").get("failure").is_none());
    let f = failure_of(record(&doc, "m", "three"));
    assert!(f["message"].is_string() && f["span"].is_object() && f["calls"].is_array(), "{f}");
}

/// Spec §18.1: `tests` is ordered by `module` then `name`, strings by code points, whatever the
/// order of the files and of the tests in them. `dsp` comes before `dsp.filter` (a prefix first),
/// capital letters before small ones, and a code point above the surrogates in UTF-16
/// (U+1F600) after one in the basic plane (U+FF5E): the order of code points, not of UTF-16 units.
#[test]
fn tests_are_ordered_by_module_then_name_by_code_points() {
    let t = |name: &str, body: &str| format!("test \"{name}\" {{\n  {body}\n}}\n");
    let top = [t("b", "assert 1 == 2"), t("a", "assert true")].join("\n");
    let dsp = t("z", "assert true");
    let voice = [
        t(r"\u{1f600}", "assert true"),
        t(r"\u{ff5e}", "assert true"),
        t(r"\u{e9}", "assert true"),
        t("z", "assert true"),
        t("a", "assert false"),
        t("Z", "assert true"),
    ]
    .join("\n");
    let filter = t("m", "assert true");
    let (_d, out, doc) = pkg_run(
        "order",
        &[("top.onsa", &top), ("dsp.onsa", &dsp), ("dsp/voice.onsa", &voice), ("dsp/filter.onsa", &filter)],
    );
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let want: Vec<(String, String)> = [
        ("dsp", "z"),
        ("dsp.filter", "m"),
        ("dsp.voice", "Z"),
        ("dsp.voice", "a"),
        ("dsp.voice", "z"),
        ("dsp.voice", "\u{e9}"),
        ("dsp.voice", "\u{ff5e}"),
        ("dsp.voice", "\u{1f600}"),
        ("top", "a"),
        ("top", "b"),
    ]
    .iter()
    .map(|(m, n)| (m.to_string(), n.to_string()))
    .collect();
    assert_eq!(identities(&doc), want, "{doc}");
}

// ---------------------------------------------------------------- when the checks stop the run

/// Spec §18.1: a diagnostic of the package stops the run before any test; `tests` is an empty
/// array and the diagnostic is in `diagnostics`; the exit code is 1.
#[test]
fn a_run_stopped_by_a_diagnostic_has_an_empty_tests_array() {
    for (what, broken, code) in [
        ("a name", "pub fn f() -> I32 {\n  y\n}\n", "E0302"),
        ("a syntax error", "pub fn f( {\n", ""),
        ("an unsupported feature", "target fn open() -> I32\n", "E0200"),
    ] {
        let (_d, out, doc) = pkg_run("stopped", &[("a.onsa", broken), ("m.onsa", TWO_OK)]);
        assert_eq!(out.code, 1, "{what}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).iter().any(|x| code.is_empty() || str_of(x, "code") == code), "{what}: {doc}");
        assert!(!diagnostics(&doc).is_empty(), "{what}: {doc}");
        assert!(tests_of(&doc).is_empty(), "{what}: no test has run: {doc}");
    }
}

/// Spec §18.1 and §18.2: a diagnostic that points into `onsa.toml` is exit code 2 and still prints
/// the document, with an empty `tests`.
#[test]
#[ignore = "W4-02"]
fn a_manifest_diagnostic_prints_the_document_with_an_empty_tests_array() {
    let d = Dir::bare("manifest");
    d.write("onsa.toml", "[package]\nname = \"demo\"\nedition = \"2026\"\nbogus = 1\n");
    d.write("m.onsa", TWO_OK);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1, "{doc}");
    assert_eq!(str_of(&ds[0], "code"), "E1102");
    assert_eq!(span_of(&ds[0]["span"]).file, "onsa.toml");
    assert!(tests_of(&doc).is_empty(), "{doc}");
}

// ---------------------------------------------------------------- failures: message, span, calls

const SHAPE: &str = "pub fn add(a: I32, b: I32) -> I32 {
  a + b
}

pub fn twice(a: I32) -> I32 {
  add(a, 2147483647)
}

test \"direct\" {
  assert add(1, 1) == 3
}

test \"nested\" {
  let y = twice(1)
  assert y == 0
}

test \"fine\" {
  assert twice(0) == 2147483647
}

test \"in the body\" {
  let xs: [I32; 2] = [1, 2]
  let i: U32 = 2
  assert xs[i] == 0
}
";

/// Spec §18.1: an `assert` that fails in the body of the test: `message` is `assert <source>`,
/// `span` is the whole statement (`assert` to the end of the expression), `calls` is empty.
#[test]
fn a_failed_assert_has_the_statement_as_its_span_and_no_calls() {
    let (d, out, doc) = pkg_run("shape", &[("m.onsa", SHAPE)]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "direct"));
    assert_eq!(str_of(f, "message"), "assert add(1, 1) == 3");
    assert_eq!(span_of(&f["span"]), span("m.onsa", 10, 3, 10, 24));
    assert!(array_of(f, "calls").is_empty(), "{f}");

    // The text line is `failed at <file>:<line>: <message>` with the same file, line and message.
    let text = run(d.root(), &["test", &d.arg()]);
    assert!(
        result_lines(&text).contains(&"test m \"direct\" failed at m.onsa:10: assert add(1, 1) == 3".to_string()),
        "{}",
        text.stdout
    );
}

/// Spec §18.1: a panic of the language inside the expression of an `assert` is the span of that
/// expression (`xs[i]`), not of the statement; the body of the test calls nothing, so `calls` is
/// empty. The wording of the message is not fixed.
#[test]
fn a_panic_in_the_body_has_the_expression_as_its_span_and_no_calls() {
    let (_d, _out, doc) = pkg_run("shape_body", &[("m.onsa", SHAPE)]);
    let f = failure_of(record(&doc, "m", "in the body"));
    assert!(f["message"].as_str().is_some_and(|m| !m.is_empty()), "{f}");
    assert_eq!(span_of(&f["span"]), span("m.onsa", 25, 10, 25, 15));
    assert!(array_of(f, "calls").is_empty(), "{f}");
}

/// Spec §18.1: a panic two calls deep: `span` is the expression that panicked, `calls` has the
/// call in `twice` (line 6) and then the call in the body of the test (line 14), innermost
/// first, and the last one is in the body of the test (lines 13 to 16).
#[test]
fn calls_list_the_call_sites_from_the_panic_back_to_the_test() {
    let (d, out, doc) = pkg_run("shape_nested", &[("m.onsa", SHAPE)]);
    let f = failure_of(record(&doc, "m", "nested"));
    assert!(f["message"].as_str().is_some_and(|m| !m.is_empty()), "{f}");
    assert_eq!(span_of(&f["span"]), span("m.onsa", 2, 3, 2, 8));
    assert_call_starts(f, &[("m.onsa", 6, 3), ("m.onsa", 14, 11)]);
    let last = call_spans(f).pop().unwrap();
    assert!((13..=16).contains(&last.line), "the last call is in the body of the test: {f}");

    // The text line is at the panic: the file and the line of `span`.
    let text = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1);
    let prefix = "test m \"nested\" failed at m.onsa:2: ";
    assert!(result_lines(&text).iter().any(|l| l.starts_with(prefix)), "{}", text.stdout);
    assert!(record(&doc, "m", "fine").get("failure").is_none());
}

/// Spec §18.1: the position of a call is a place in the file that holds the call: a call from the
/// body of a test into another module is in the file of the test, and the panic is in the other.
#[test]
fn calls_across_modules_name_the_file_of_each_position() {
    let util = "pub fn boom(n: I32) -> I32 {\n  n + 2147483647\n}\n";
    let user = "use util.{boom}\n\ntest \"cross\" {\n  let r = boom(1)\n  assert r == 0\n}\n";
    let (d, _out, doc) = pkg_run("cross", &[("util.onsa", util), ("m.onsa", user)]);
    let f = failure_of(record(&doc, "m", "cross"));
    assert_eq!(span_of(&f["span"]), span("util.onsa", 2, 3, 2, 17));
    assert_call_starts(f, &[("m.onsa", 4, 11)]);

    let text = run(d.root(), &["test", &d.arg()]);
    assert!(
        result_lines(&text).iter().any(|l| l.starts_with("test m \"cross\" failed at util.onsa:2: ")),
        "{}",
        text.stdout
    );
}

/// Spec §18.1 with a generic function: the panic is in the body of the generic function, and the
/// call is the one in the test, at the call and not at the instance.
#[test]
fn calls_through_a_generic_function() {
    let src = "pub fn first_of[T: Copy](xs: [T; 3], i: U32) -> T {
  xs[i]
}

test \"generic\" {
  let xs: [I32; 3] = [1, 2, 3]
  let v = first_of(xs, 3)
  assert v == 1
}
";
    let (_d, _out, doc) = pkg_run("generic", &[("m.onsa", src)]);
    let f = failure_of(record(&doc, "m", "generic"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 2, 3, 2, 8));
    assert_call_starts(f, &[("m.onsa", 7, 11)]);
}

/// Spec §18.1 with a branch and a loop in the called function: the position of the panic is the
/// multiplication in the branch, and the one call is in the test.
#[test]
fn calls_through_a_loop_and_a_branch() {
    let src = "pub fn fold(xs: [I32; 3], k: I32) -> I32 {
  var acc: I32 = k
  for x in xs {
    if x == 3 {
      acc = acc * k
    }
  }
  acc
}

test \"loop and branch\" {
  let xs: [I32; 3] = [1, 2, 3]
  let r = fold(xs, 65536)
  assert r == 0
}
";
    let (_d, _out, doc) = pkg_run("loop", &[("m.onsa", src)]);
    let f = failure_of(record(&doc, "m", "loop and branch"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 5, 13, 5, 20));
    assert_call_starts(f, &[("m.onsa", 13, 11)]);
}

/// Spec §18.1: a panic inside a function of `std` has a `span.file` of the form
/// `std/dsp/test.onsa`, and `calls` ends with the position of the call in the test. (`energy`
/// over a range past the end of the span panics in std's own code; the spec writes the
/// half-open range and not what happens past the end, see the report of W2-10/t.)
#[test]
fn a_panic_inside_std_is_in_a_file_of_std_with_the_call_in_the_test() {
    let src = "use std.dsp.test.{impulse, energy}

test \"std\" {
  let b = impulse(4)
  let e = energy(b, 0, 9)
  assert e == 1.0
}
";
    let (d, _out, doc) = pkg_run("std_fall", &[("m.onsa", src)]);
    let f = failure_of(record(&doc, "m", "std"));
    let sp = span_of(&f["span"]);
    assert_eq!(sp.file, "std/dsp/test.onsa", "{f}");
    let calls = call_spans(f);
    assert!(!calls.is_empty(), "a panic in std is reached by a call: {f}");
    let last = calls.last().unwrap();
    assert_eq!((last.file.as_str(), last.line, last.col), ("m.onsa", 5, 11), "{f}");

    let text = run(d.root(), &["test", &d.arg()]);
    let prefix = format!("test m \"std\" failed at std/dsp/test.onsa:{}: ", sp.line);
    assert!(result_lines(&text).iter().any(|l| l.starts_with(&prefix)), "{}", text.stdout);
}

/// Spec §11.8: a failing `assert_near` is a panic at the position of its call. Called by the test
/// itself, `calls` is empty and `span` is the call expression; called from a helper, `span` is the
/// call in the helper and `calls` has the call of the helper in the test.
#[test]
fn a_failed_assert_near_is_at_its_call() {
    let src = "use std.dsp.test.{assert_near}

fn close(a: F64, b: F64) {
  assert_near(a, b, 0.5)
}

test \"direct near\" {
  assert_near(1.0, 2.0, 0.5)
}

test \"via helper\" {
  close(1.0, 2.0)
}

test \"passes\" {
  assert_near(1.0, 1.25, 0.5)
  close(1.0, 1.25)
}
";
    let (_d, out, doc) = pkg_run("near", &[("m.onsa", src)]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "direct near"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 8, 3, 8, 29));
    assert!(array_of(f, "calls").is_empty(), "{f}");
    assert!(f["message"].as_str().is_some_and(|m| !m.is_empty()), "{f}");

    let f = failure_of(record(&doc, "m", "via helper"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 4, 3, 4, 25));
    assert_call_starts(f, &[("m.onsa", 12, 3)]);

    assert_eq!(str_of(record(&doc, "m", "passes"), "status"), "ok");
}

/// Spec §9.2 and §18.1: `panic(msg)` has `msg` as its `message`. (`panic` is in the prelude
/// per §15.1, and this version does not have it yet, E0302; W5-08.)
#[test]
#[ignore = "W5-08"]
fn the_message_of_a_panic_call_is_its_argument() {
    let src = "pub fn stop() -> I32 {
  panic(\"stop here\")
}

test \"explicit\" {
  panic(\"boom\")
}

test \"through a call\" {
  let n = stop()
  assert n == 0
}
";
    let (_d, out, doc) = pkg_run("panic_msg", &[("m.onsa", src)]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "explicit"));
    assert_eq!(str_of(f, "message"), "boom");
    assert_eq!(span_of(&f["span"]), span("m.onsa", 6, 3, 6, 16));
    assert!(array_of(f, "calls").is_empty(), "{f}");

    let f = failure_of(record(&doc, "m", "through a call"));
    assert_eq!(str_of(f, "message"), "stop here");
    assert_eq!(span_of(&f["span"]), span("m.onsa", 2, 3, 2, 21));
    assert_call_starts(f, &[("m.onsa", 10, 11)]);
}

// ---------------------------------------------------------------- --filter in the document

/// Spec §18.2: `--filter` selects the tests that run, and `tests` holds those only (a test that
/// did not run has no record).
#[test]
fn the_document_lists_the_selected_tests_only() {
    let d = Dir::pkg("filter_json");
    d.write("a.onsa", TWO_OK);
    d.write("b.onsa", TWO_OK);
    let (out, doc) = test_json(d.root(), &["--filter", "b \"t", &d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(identities(&doc), [("b".to_string(), "two".to_string())]);
    assert!(diagnostics(&doc).is_empty());
}

/// Spec §18.2: `--json` prints JSON at exit codes 0 and 1 only (and 2 for `onsa.toml`); the exit
/// code 2 of a filter with no match prints nothing on the standard output.
#[test]
fn json_prints_nothing_for_a_filter_with_no_match() {
    let d = Dir::pkg("filter_none");
    d.write("a.onsa", TWO_OK);
    let out = run(d.root(), &["test", "--json", "--filter", "nothing like it", &d.arg()]);
    assert_eq!(out.code, 2);
    assert_eq!(out.stdout, "");
}
