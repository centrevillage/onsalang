//! `onsa test` reports the E0200 of a `std` function that the interpreter does not run only for
//! a use that the tests it runs reach (spec §15.2, §18.2; S-242; W2-13).
//!
//! What the spec fixes, and so what is checked here:
//! - a `target` declaration of `std` that the target does not provide is E0200 at the use,
//!   when the use is reachable from an entry of the run, before the run starts (§15.2). The
//!   entries of `onsa test` are the tests that run, which `--filter` selects (§15.2, §18.2).
//!   Reachable means that the entry can follow it statically: the function it calls, the
//!   function it uses as a value, the flow whose instance it makes, the initializer of a
//!   `const` it reads, and so on in turn; whether the run passes it is not looked at (§15.2);
//! - the order of the checks of `onsa test` is: the errors of the check, the E0200 that does not
//!   depend on the target, the match of `--filter` (no match is a usage error, exit code 2), the
//!   E0200 that the selected tests reach, and the run. The command stops at the first stage
//!   that has an error (§18.2). The first two are on the whole package whatever is selected;
//! - when the command stops before the run, `tests` of the JSON document is an empty array and the
//!   diagnostics are in `diagnostics` (§18.1, §18.2);
//! - `onsa check` does not depend on the target, so it does not report this E0200 (§15.2).
//!
//! The helper that this version's interpreter does not run is `std.test.gen.u32` (`gen.*`, spec
//! §11.8; the generators are the helpers of `std.test` that no interpreter of this version runs,
//! see also `tests/spec/negative/test_unsupported_std.onsa`).
//!
//! Not written here: the shapes of reaching (a call chain, a `const` chain, a method, a closure,
//! a generic function, several modules), which are the cases `tests/spec/test/reach_*.onsa` and
//! `tests/spec/packages/reach_modules`, and the build side (`onsa build`), which has its own
//! entries (the exports). An empty `--filter` is the same as no filter (S-286 (e2); a package
//! with no tests then succeeds), which `test_identity.rs` checks. A file of the package given to
//! `onsa test` (S-286 (a), W4-02) is not written.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use serde_json::Value;
use test_support::*;

/// The line (from 1) of the line of `src` that ends with `tag`; exactly one.
fn line_of(src: &str, tag: &str) -> u64 {
    let hits: Vec<usize> =
        src.lines().enumerate().filter(|(_, l)| l.trim_end().ends_with(tag)).map(|(i, _)| i + 1).collect();
    assert_eq!(hits.len(), 1, "the tag {tag:?} is on one line of the source: {src}");
    hits[0] as u64
}

/// `(file, line)` of every diagnostic of `code` in the document.
fn positions(doc: &Value, code: &str) -> Vec<(String, u64)> {
    let mut v: Vec<(String, u64)> = diagnostics(doc)
        .iter()
        .filter(|x| str_of(x, "code") == code)
        .map(|x| {
            let s = span_of(&x["span"]);
            (s.file, s.line)
        })
        .collect();
    v.sort();
    v.dedup();
    v
}

fn codes(doc: &Value) -> Vec<String> {
    let mut v: Vec<String> = diagnostics(doc).iter().map(|x| str_of(x, "code").to_string()).collect();
    v.sort();
    v.dedup();
    v
}

/// A module with a function that uses a generator, tagged `use-a` at the use, and a test that
/// calls it.
const MODULE_A: &str = "use std.test.gen

pub fn digit(n: U32) -> U32 {
  let _ = gen.u32(0, n)   // use-a
  n
}

test \"uses a generator\" {
  assert digit(1) == 1
}
";

const MODULE_B: &str = "test \"plain\" {
  assert true
}

test \"plain too\" {
  assert (1 + 1) == 2
}
";

/// The package of the reaching test (module `a`) and two plain tests (module `b`).
fn reaching_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("a.onsa", MODULE_A);
    d.write("b.onsa", MODULE_B);
    d
}

const PLAIN_LINES: [&str; 2] = ["test b \"plain\" ok", "test b \"plain too\" ok"];

// ---------------------------------------------------------------- a use that no test reaches

/// A function that uses a generator and that no test calls.
const UNREACHED_USE: &str = "use std.test.gen

pub fn digit(n: U32) -> U32 {
  let _ = gen.u32(0, n)
  n
}

fn also_unused() -> U32 {
  digit(2)
}

test \"plain a\" {
  assert true
}
";

/// Spec §15.2: only a use that an entry reaches is E0200. Nothing here calls `digit`, so
/// `onsa test` runs the tests (exit code 0, the result lines of every test) without a diagnostic.
#[test]
fn a_use_that_no_test_reaches_is_not_e0200() {
    let d = Dir::pkg("unreached");
    d.write("a.onsa", UNREACHED_USE);
    d.write("b.onsa", MODULE_B);
    let root = d.arg();

    let out = run(d.root(), &["test", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200"), "{}", out.stdout);
    let mut want = vec!["test a \"plain a\" ok".to_string(), PLAIN_LINES[0].to_string(), PLAIN_LINES[1].to_string()];
    want.sort();
    assert_eq!(sorted_result_lines(&out), want, "{}", out.stdout);

    let (jout, doc) = test_json(d.root(), &[&root]);
    assert_eq!(jout.code, 0, "{}", jout.stdout);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    assert_eq!(
        identities(&doc),
        [
            ("a".to_string(), "plain a".to_string()),
            ("b".to_string(), "plain".to_string()),
            ("b".to_string(), "plain too".to_string())
        ]
    );
}

/// Spec §15.2, §18.2: a run that does not reach the E0200 still ends with the exit code of its
/// tests: a failed test is 1 with a result line, and no E0200 is on the output.
#[test]
fn a_failed_test_is_a_failure_and_not_an_e0200_when_the_use_is_not_reached() {
    let d = Dir::pkg("unreached_failed");
    d.write("a.onsa", &format!("{UNREACHED_USE}\ntest \"rings\" {{\n  assert 1 == 2\n}}\n"));
    let root = d.arg();
    let out = run(d.root(), &["test", &root]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200"), "{}", out.stdout);
    assert!(result_lines(&out).iter().any(|l| l.starts_with("test a \"rings\" failed at a.onsa:")), "{}", out.stdout);
    let (_, doc) = test_json(d.root(), &[&root]);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    assert_eq!(str_of(record(&doc, "a", "rings"), "status"), "failed");
}

/// A `const` whose initializer calls a function that uses a generator, and that no test reads,
/// next to one that a test reads.
const CONSTS: &str = "use std.test.gen

fn digit(n: U32) -> U32 {
  let _ = gen.u32(0, n)   // use-digit
  n
}

fn unread_digit(n: U32) -> U32 {
  let _ = gen.u32(1, n)   // use-unread
  n
}

const NOBODY_READS: U32 = unread_digit(7)

const OTHER: U32 = digit(8) + 1

const PLAIN: U32 = 2 + 3

test \"reads a plain const\" {
  assert PLAIN == 5
}
";

/// Spec §15.2 ("読む `const` の初期化式"): an initializer that no running test reaches is not
/// followed. The tests run (exit code 0), and the unread initializers are neither an E0200 nor
/// an internal error (exit code 101) of the evaluation of `const`s at compile time (§6.6).
#[test]
fn a_const_that_no_test_reads_is_not_followed() {
    let d = Dir::pkg("consts_unread");
    d.write("m.onsa", CONSTS);
    let root = d.arg();
    let out = run(d.root(), &["test", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(sorted_result_lines(&out), ["test m \"reads a plain const\" ok"], "{}", out.stdout);
}

/// The same package with a test that reads one of the `const`s: the E0200 is at the use in the
/// function the initializer calls (exit code 1), not an internal error (101), and the `const`
/// that no test reads adds nothing.
#[test]
fn a_const_that_a_test_reads_is_followed_to_its_use() {
    let d = Dir::pkg("consts_read");
    d.write("m.onsa", &format!("{CONSTS}\ntest \"reads a const with a generator\" {{\n  assert OTHER == 9\n}}\n"));
    let root = d.arg();
    let (out, doc) = test_json(d.root(), &[&root]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(positions(&doc, "E0200"), [("m.onsa".to_string(), line_of(CONSTS, "use-digit"))], "{doc}");
    assert_eq!(codes(&doc), ["E0200"], "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
}

// ---------------------------------------------------------------- a use that a test reaches

/// Spec §15.2, §18.1: the E0200 is at the use (the line of the generator, not the call in the
/// test), the command stops before it runs any test (exit code 1, no result line), and `tests`
/// is an empty array.
#[test]
fn a_reached_use_is_e0200_at_the_use_and_no_test_runs() {
    let d = reaching_package("reached");
    let root = d.arg();
    let line = line_of(MODULE_A, "use-a");

    let out = run(d.root(), &["test", &root]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("error[E0200]"), "{}", out.stdout);
    assert!(result_lines(&out).is_empty(), "no test runs: {}", out.stdout);

    let (jout, doc) = test_json(d.root(), &[&root]);
    assert_eq!(jout.code, 1);
    assert_eq!(positions(&doc, "E0200"), [("a.onsa".to_string(), line)], "{doc}");
    assert_eq!(codes(&doc), ["E0200"], "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
}

// ---------------------------------------------------------------- --filter chooses the entries

/// Spec §15.2, §18.2: the entries are the tests that `--filter` selects. The tests of module `b`
/// do not reach the generator, so selecting only them runs them (exit code 0, the lines of those
/// tests only); selecting the test that reaches it, or any set that has it, is the E0200.
#[test]
fn a_filter_makes_the_selected_tests_the_entries() {
    let d = reaching_package("filter_entries");
    let root = d.arg();
    let line = line_of(MODULE_A, "use-a");

    let only_b: &[(&str, &[&str])] = &[
        ("plain", &[PLAIN_LINES[0], PLAIN_LINES[1]]),
        ("plain too", &[PLAIN_LINES[1]]),
        ("b \"", &[PLAIN_LINES[0], PLAIN_LINES[1]]),
    ];
    for (filter, want_ok) in only_b {
        let out = run(d.root(), &["test", "--filter", filter, &root]);
        assert_eq!(out.code, 0, "--filter {filter:?}: {}{}", out.stdout, out.stderr);
        assert!(!out.stdout.contains("E0200"), "--filter {filter:?}: {}", out.stdout);
        let mut want: Vec<String> = want_ok.iter().map(|s| s.to_string()).collect();
        want.sort();
        assert_eq!(sorted_result_lines(&out), want, "--filter {filter:?}: {}", out.stdout);

        let (jout, doc) = test_json(d.root(), &["--filter", filter, &root]);
        assert_eq!(jout.code, 0, "--filter {filter:?}: {}", jout.stdout);
        assert!(diagnostics(&doc).is_empty(), "--filter {filter:?}: {doc}");
        assert!(tests_of(&doc).iter().all(|t| str_of(t, "module") == "b"), "--filter {filter:?}: {doc}");
    }

    // The selected set has the test that reaches the generator: the E0200, and nothing runs.
    for filter in ["uses a generator", "a \"uses", "", "uses", "s", "\""] {
        let out = run(d.root(), &["test", "--filter", filter, &root]);
        assert_eq!(out.code, 1, "--filter {filter:?}: {}{}", out.stdout, out.stderr);
        assert!(result_lines(&out).is_empty(), "--filter {filter:?}: {}", out.stdout);
        let (jout, doc) = test_json(d.root(), &["--filter", filter, &root]);
        assert_eq!(jout.code, 1, "--filter {filter:?}");
        assert_eq!(positions(&doc, "E0200"), [("a.onsa".to_string(), line)], "--filter {filter:?}: {doc}");
        assert!(tests_of(&doc).is_empty(), "--filter {filter:?}: {doc}");
    }
}

/// The reaching forms, each by its own test, in one module: a call, a call chain, a `const`, a
/// chain of `const`s, a method. Selecting one test reports the uses that this test reaches and no
/// other (spec §15.2, §18.2: the reach starts at the selected tests), and the plain test is not
/// held by any of them.
const FORMS: &str = "use std.test.gen

fn direct(n: U32) -> U32 {
  let _ = gen.u32(0, n)   // use-direct
  n
}

fn leaf(n: U32) -> U32 {
  let _ = gen.u32(1, n)   // use-chain
  n
}

fn mid(n: U32) -> U32 {
  leaf(n) + 1
}

fn top(n: U32) -> U32 {
  mid(n) + 1
}

fn for_const(n: U32) -> U32 {
  let _ = gen.u32(2, n)   // use-const
  n
}

const READ: U32 = for_const(3)

fn for_const_chain(n: U32) -> U32 {
  let _ = gen.u32(3, n)   // use-const-chain
  n
}

const LOW: U32 = for_const_chain(4)
const MIDDLE: U32 = LOW + 1
const HIGH: U32 = MIDDLE + 1

pub struct Dice {
  sides: U32,
}

impl Dice {
  pub fn roll(self) -> U32 {
    let _ = gen.u32(4, self.sides)   // use-method
    self.sides
  }
}

test \"d-direct\" {
  assert direct(1) == 1
}

test \"c-chain\" {
  assert top(1) == 3
}

test \"k-const\" {
  assert READ == 3
}

test \"n-constchain\" {
  assert HIGH == 6
}

test \"m-method\" {
  assert Dice { sides: 6 }.roll() == 6
}

test \"p-plain\" {
  assert true
}
";

/// `(filter, the tags of the uses that must be reported)`.
const FORM_FILTERS: &[(&str, &[&str])] = &[
    ("d-direct", &["use-direct"]),
    ("c-chain", &["use-chain"]),
    ("k-const", &["use-const"]),
    ("n-constchain", &["use-const-chain"]),
    ("m-method", &["use-method"]),
    // Two selected tests (`c-chain` and `n-constchain`): the uses of both and no other.
    ("chain", &["use-chain", "use-const-chain"]),
];

/// Spec §15.2, §18.2: the uses reported are exactly the ones the selected tests reach.
#[test]
fn the_uses_reported_are_the_ones_the_selected_tests_reach() {
    let d = Dir::pkg("forms");
    d.write("m.onsa", FORMS);
    let root = d.arg();

    for (filter, tags) in FORM_FILTERS {
        let (jout, doc) = test_json(d.root(), &["--filter", filter, &root]);
        assert_eq!(jout.code, 1, "--filter {filter:?}: {}", jout.stdout);
        let mut want: Vec<(String, u64)> = tags.iter().map(|t| ("m.onsa".to_string(), line_of(FORMS, t))).collect();
        want.sort();
        assert_eq!(positions(&doc, "E0200"), want, "--filter {filter:?}: {doc}");
        assert_eq!(codes(&doc), ["E0200"], "--filter {filter:?}: {doc}");
        assert!(tests_of(&doc).is_empty(), "--filter {filter:?}: {doc}");
    }

    // The plain test reaches none of them: it runs, and the other tests do not.
    let out = run(d.root(), &["test", "--filter", "p-plain", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(sorted_result_lines(&out), ["test m \"p-plain\" ok"], "{}", out.stdout);

    // With no filter, every test is an entry: all of the uses.
    let (jout, doc) = test_json(d.root(), &[&root]);
    assert_eq!(jout.code, 1);
    let mut all: Vec<(String, u64)> = ["use-direct", "use-chain", "use-const", "use-const-chain", "use-method"]
        .iter()
        .map(|t| ("m.onsa".to_string(), line_of(FORMS, t)))
        .collect();
    all.sort();
    assert_eq!(positions(&doc, "E0200"), all, "{doc}");
}

// ---------------------------------------------------------------- the order of the stages

/// Spec §18.2: the match of `--filter` comes before the E0200 that the selected tests reach. A
/// filter that selects nothing is a usage error (exit code 2, nothing on the standard output, the
/// reason on the standard error), though the package has a reached use that, with no filter or
/// with a filter that matches, is the E0200 (exit code 1).
#[test]
fn a_filter_without_a_match_comes_before_the_reach() {
    let d = reaching_package("nomatch_before_reach");
    let root = d.arg();
    for filter in ["nomatch", "Uses", "a  \"uses", "uses  a generator"] {
        for json in [false, true] {
            let mut args = vec!["test"];
            if json {
                args.push("--json");
            }
            args.extend(["--filter", filter, &root]);
            let out = run(d.root(), &args);
            assert_eq!(out.code, 2, "{args:?}: {}{}", out.stdout, out.stderr);
            assert_eq!(out.stdout, "", "{args:?}");
            assert!(!out.stderr.trim().is_empty(), "{args:?}");
        }
    }
}

/// Spec §18.2: the errors of the check come first, and the command stops there. The package has
/// the E0302 in a function no test calls, and a test that reaches a generator: the diagnostics are
/// the E0302 only, with the filter that selects the reaching test, the filter that selects
/// nothing (not the 2 of the usage error) and no filter. The E0200 of the reach is not reported.
#[test]
fn the_errors_of_the_check_come_before_the_reach() {
    let d = reaching_package("check_before_reach");
    d.write("c.onsa", "pub fn broken() -> I32 {\n  y\n}\n");
    let root = d.arg();
    for filter in [None, Some("uses a generator"), Some("nomatch"), Some("plain")] {
        let mut args = vec![];
        if let Some(f) = filter {
            args.extend(["--filter", f]);
        }
        args.push(&root);
        let (out, doc) = test_json(d.root(), &args);
        assert_eq!(out.code, 1, "{filter:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(codes(&doc), ["E0302"], "{filter:?}: {doc}");
        assert_eq!(positions(&doc, "E0302"), [("c.onsa".to_string(), 2)], "{filter:?}: {doc}");
        assert!(tests_of(&doc).is_empty(), "{filter:?}: {doc}");
    }
}

/// Spec §18.2: the E0200 that does not depend on the target is on the whole package, whatever the
/// filter selects, and it comes before the match of the filter and before the reach. Each source
/// is a feature this version does not provide for any target: a `target` declaration of the
/// package (§15.2) and a pattern on a `Str` (§7). The package also has a test that reaches a
/// generator, and the reached E0200 is not reported with it.
#[test]
fn an_e0200_that_does_not_depend_on_the_target_comes_before_the_filter_and_the_reach() {
    let cases: &[(&str, &str)] = &[
        ("target_decl", "target fn open() -> I32\n"),
        ("str_pattern", "fn pattern(s: Str) -> U32 {\n  match s {\n    \"abc\" => 1,\n    _ => 0,\n  }\n}\n"),
    ];
    for (tag, src) in cases {
        let d = reaching_package(tag);
        d.write("c.onsa", src);
        let root = d.arg();

        for filter in [None, Some("plain"), Some("uses a generator"), Some("nomatch")] {
            let mut args = vec![];
            if let Some(f) = filter {
                args.extend(["--filter", f]);
            }
            args.push(&root);
            let (out, doc) = test_json(d.root(), &args);
            assert_eq!(out.code, 1, "{tag} {filter:?}: {}{}", out.stdout, out.stderr);
            assert!(tests_of(&doc).is_empty(), "{tag} {filter:?}: {doc}");
            let e0200 = positions(&doc, "E0200");
            assert!(!e0200.is_empty() && e0200.iter().all(|(f, _)| f == "c.onsa"), "{tag} {filter:?}: {doc}");
        }
    }
}

// ---------------------------------------------------------------- onsa check

/// Spec §15.2: `onsa check` does not depend on the target, so it does not report this E0200
/// though a test reaches the generator: exit code 0 and no diagnostic.
#[test]
fn check_does_not_report_a_use_that_a_test_reaches() {
    let d = reaching_package("check_silent");
    let root = d.arg();
    let out = run(d.root(), &["check", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200"), "{}", out.stdout);
    let out = run(d.root(), &["check", "--json", &root]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}", out.stdout);
}
