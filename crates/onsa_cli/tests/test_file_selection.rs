//! Which tests `onsa test` selects and which diagnostics it prints when it is given a file of the
//! package (spec §15.1, §15.2, §18.2, §18.1, §11.8; S-286, S-311; W4-15, R-189).
//!
//! What the spec fixes, and so what is checked here:
//! - a file of the package given to `onsa test` selects the tests of the module of that file and
//!   no other: not the tests of the modules below it (`dsp/voice.onsa` for `dsp.onsa`), not the
//!   tests of a module of another path that has the same file name or the same test name. The
//!   whole package is gathered and resolved (`use` needs all of it), and the result is narrowed
//!   to the module of the file (§15.1, §18.2). The result lines and the `tests` of the JSON
//!   document both hold the selected tests only (§18.1, `spec/tools.md` §4);
//! - a directory that holds no `.onsa` of its own name is a module with no items (`a` and `a.b`
//!   for `a/b/c.onsa`), and the file below it still selects its own module `a.b.c` (§15.1);
//! - `--filter` narrows the selected tests further (§18.2). Its match is on the tests of the whole
//!   package, whatever file is given: a text that matches only outside the selected module runs no
//!   test and succeeds (exit code 0), and a text that matches nowhere is the usage error (exit
//!   code 2, nothing on the standard output, also with `--json`). The empty text is the same as
//!   no `--filter` (§18.2, S-311);
//! - no selected test (a file with no `test`) runs nothing and succeeds, exit code 0, with an
//!   empty `tests` array, unless a non-empty `--filter` matches nowhere (§18.2, S-286);
//! - the diagnostics that stop the run (a check error, an E0200 that does not depend on the
//!   target) are the ones of the whole package whatever file is given, so `test a.onsa` ends with
//!   the exit code 1 on an error in `c.onsa`, though `check a.onsa` prints only the diagnostics of
//!   `a.onsa` (§15.1, §18.2). They come before the match of `--filter` (§18.2);
//! - the E0200 of a `std` function that this version does not run is reported for a use that the
//!   selected tests reach, through other modules too, and not for a use that only the tests of
//!   another module reach (§15.2, §18.2). The match of `--filter` comes before this reach (§18.2);
//! - a test of another module that fails does not make the run fail, and a failing test of the
//!   given module does (exit code 1, §18.2);
//! - no file (the directory of the package, its `onsa.toml`, no path with the working directory
//!   inside the package) selects every test of the package (§15.1, §18.2).
//!
//! Not written here: two or more paths and the `tests/` of the root (`package_input.rs`,
//! `package_tests_dir.rs`), `--flows`, `--backends`, `--target`, `--seed`, a single file with no
//! manifest (`test_identity.rs`), the shapes of reaching (`test_reach.rs`), and the wording of a
//! diagnostic.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use std::path::Path;

use serde_json::Value;
use test_support::*;

/// `(module, name)` of a test.
type Id = (&'static str, &'static str);

/// The ids sorted the way the `tests` array is (module, then name; §18.1).
fn sorted_ids(ids: &[Id]) -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> = ids.iter().map(|(m, n)| (m.to_string(), n.to_string())).collect();
    v.sort();
    v
}

/// The result lines of passing tests, sorted.
fn ok_lines(ids: &[Id]) -> Vec<String> {
    let mut v: Vec<String> = ids.iter().map(|(m, n)| format!("test {m} \"{n}\" ok")).collect();
    v.sort();
    v
}

/// The source of a module with the given passing tests.
fn tests_src(names: &[&str]) -> String {
    names.iter().map(|n| format!("test \"{n}\" {{\n  assert 1 == 1\n}}\n")).collect::<Vec<_>>().join("\n")
}

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

fn file_arg(d: &Dir, rel: &str) -> String {
    d.root().join(rel).to_string_lossy().into_owned()
}

/// `onsa test [--filter f] <path>` in `cwd`, with the text and with `--json`: exit code 0, the
/// result lines and the `tests` records are exactly `ids`, and no diagnostic.
fn expect_selected(cwd: &Path, filter: Option<&str>, path: Option<&str>, ids: &[Id], label: &str) {
    let mut args: Vec<&str> = vec![];
    if let Some(f) = filter {
        args.extend(["--filter", f]);
    }
    if let Some(p) = path {
        args.push(p);
    }
    let out = run(cwd, &[&["test"], args.as_slice()].concat());
    assert_eq!(out.code, 0, "{label}: {}{}", out.stdout, out.stderr);
    assert_eq!(sorted_result_lines(&out), ok_lines(ids), "{label}: {}", out.stdout);

    let (jout, doc) = test_json(cwd, &args);
    assert_eq!(jout.code, 0, "{label}: {}{}", jout.stdout, jout.stderr);
    assert!(diagnostics(&doc).is_empty(), "{label}: {doc}");
    assert_eq!(identities(&doc), sorted_ids(ids), "{label}: {doc}");
    assert!(tests_of(&doc).iter().all(|t| str_of(t, "status") == "ok"), "{label}: {doc}");
}

/// A usage error: exit code 2, nothing on the standard output (also with `--json`), the reason on
/// the standard error (§18.2).
fn expect_usage_error(cwd: &Path, args: &[&str], label: &str) {
    for json in [false, true] {
        let mut a = vec!["test"];
        if json {
            a.push("--json");
        }
        a.extend_from_slice(args);
        let out = run(cwd, &a);
        assert_eq!(out.code, 2, "{label} {a:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(out.stdout, "", "{label} {a:?}");
        assert!(!out.stderr.trim().is_empty(), "{label} {a:?}");
    }
}

/// The run stops before any test: exit code 1, no result line, `tests` empty. The document is
/// returned.
fn stopped_doc(cwd: &Path, args: &[&str], label: &str) -> Value {
    let out = run(cwd, &[&["test"], args].concat());
    assert_eq!(out.code, 1, "{label}: {}{}", out.stdout, out.stderr);
    assert!(result_lines(&out).is_empty(), "{label}: no test runs: {}", out.stdout);
    let (jout, doc) = test_json(cwd, args);
    assert_eq!(jout.code, 1, "{label}: {}", jout.stdout);
    assert!(tests_of(&doc).is_empty(), "{label}: {doc}");
    doc
}

// ---------------------------------------------------------------- the tree of the main package

/// Every module of the main package and its tests. `a` and `a.b` have no item (no `a.onsa`, no
/// `a/b.onsa`); `lib` has an item and no test; `x` and `sub.x` have the same file name and the
/// same test name; four modules have a test `decays`.
const ALL: &[Id] = &[
    ("top", "decays"),
    ("top", "top only"),
    ("dsp", "decays"),
    ("dsp", "rings"),
    ("dsp.voice", "decays"),
    ("dsp.voice", "voice only"),
    ("dsp.filter", "decays"),
    ("x", "same"),
    ("x", "only x"),
    ("sub.x", "same"),
    ("sub.x", "only sub"),
    ("a.b.c", "deep"),
];

fn main_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("top.onsa", &tests_src(&["decays", "top only"]));
    d.write("dsp.onsa", &tests_src(&["decays", "rings"]));
    d.write("dsp/voice.onsa", &tests_src(&["decays", "voice only"]));
    d.write("dsp/filter.onsa", &tests_src(&["decays"]));
    d.write("x.onsa", &tests_src(&["same", "only x"]));
    d.write("sub/x.onsa", &tests_src(&["same", "only sub"]));
    d.write("a/b/c.onsa", &tests_src(&["deep"]));
    d.write("lib.onsa", "pub fn one() -> I32 {\n  1\n}\n");
    d
}

/// The tests of the module of each file of `ALL`.
const PER_FILE: &[(&str, &[Id])] = &[
    ("top.onsa", &[("top", "decays"), ("top", "top only")]),
    ("dsp.onsa", &[("dsp", "decays"), ("dsp", "rings")]),
    ("dsp/voice.onsa", &[("dsp.voice", "decays"), ("dsp.voice", "voice only")]),
    ("dsp/filter.onsa", &[("dsp.filter", "decays")]),
    ("x.onsa", &[("x", "same"), ("x", "only x")]),
    ("sub/x.onsa", &[("sub.x", "same"), ("sub.x", "only sub")]),
    ("a/b/c.onsa", &[("a.b.c", "deep")]),
];

// ---------------------------------------------------------------- 1. the module of the file

/// Spec §15.1, §18.2: a file selects the tests of its own module only. `dsp.onsa` does not select
/// `dsp/voice.onsa` or `dsp/filter.onsa` (a module below), `x.onsa` and `sub/x.onsa` do not lose
/// or take each other's tests (R-189), the four tests named `decays` stay separate, and
/// `a/b/c.onsa` under two modules with no item selects `a.b.c`. The path is given as an absolute
/// path and as a path relative to the working directory (the root); the text and the JSON agree.
#[test]
fn a_file_selects_the_tests_of_its_own_module_only() {
    let d = main_package("one_module");
    for (rel, ids) in PER_FILE {
        expect_selected(d.root(), None, Some(&file_arg(&d, rel)), ids, &format!("absolute {rel}"));
        expect_selected(d.root(), None, Some(rel), ids, &format!("relative {rel}"));
        expect_selected(d.root(), None, Some(&format!("./{rel}")), ids, &format!("dot-relative {rel}"));
    }
}

/// Spec §15.1: the working directory may be inside the package, and the file is then given
/// relative to it; the search for `onsa.toml` goes up from the file, and the module is the path
/// from the root of the package (`dsp.voice`), not from the working directory.
#[test]
fn a_file_given_from_a_directory_inside_the_package_selects_its_module() {
    let d = main_package("one_module_inside");
    let dsp = d.root().join("dsp");
    expect_selected(&dsp, None, Some("voice.onsa"), &[("dsp.voice", "decays"), ("dsp.voice", "voice only")], "voice");
    expect_selected(&dsp, None, Some("../dsp.onsa"), &[("dsp", "decays"), ("dsp", "rings")], "../dsp");
    expect_selected(&dsp, None, Some("../sub/x.onsa"), &[("sub.x", "same"), ("sub.x", "only sub")], "../sub/x");
}

/// Spec §15.1, §18.2 (the module of the file is a different module from the ones that share its
/// name or its prefix): a package where only the deepest file has tests, with a sibling at the
/// level of the item-less module. The file selects its module and the sibling's tests do not run.
#[test]
fn a_file_below_modules_with_no_item_selects_its_module() {
    let d = Dir::pkg("itemless");
    d.write("a/b/c.onsa", &tests_src(&["deep"]));
    d.write("a/d.onsa", &tests_src(&["sibling"]));
    d.write("z.onsa", &tests_src(&["deep"]));
    expect_selected(d.root(), None, Some("a/b/c.onsa"), &[("a.b.c", "deep")], "a/b/c");
    expect_selected(d.root(), None, Some("a/d.onsa"), &[("a.d", "sibling")], "a/d");
    expect_selected(d.root(), None, Some("z.onsa"), &[("z", "deep")], "z");
}

// ---------------------------------------------------------------- 2. --filter narrows further

/// Spec §18.2: `--filter` is laid over the selection of the file. The text is matched against the
/// full name text (`dsp "decays"`), so `dsp` matches the tests of three modules, and the file
/// keeps only its own. The empty text is no filter, so the file's own tests all stay.
#[test]
fn a_filter_narrows_the_tests_of_the_file() {
    let d = main_package("filter_narrows");
    let both_dsp: &[Id] = &[("dsp", "decays"), ("dsp", "rings")];
    let cases: &[(&str, &str, &[Id])] = &[
        ("dsp.onsa", "decays", &[("dsp", "decays")]),
        ("dsp.onsa", "rings", &[("dsp", "rings")]),
        ("dsp.onsa", "dsp", both_dsp),
        ("dsp.onsa", "dsp \"", both_dsp),
        ("dsp.onsa", "s", both_dsp),
        ("dsp.onsa", "", both_dsp),
        ("dsp/voice.onsa", "decays", &[("dsp.voice", "decays")]),
        ("dsp/voice.onsa", "voice only", &[("dsp.voice", "voice only")]),
        ("dsp/voice.onsa", "dsp", &[("dsp.voice", "decays"), ("dsp.voice", "voice only")]),
        ("top.onsa", "decays", &[("top", "decays")]),
        ("x.onsa", "same", &[("x", "same")]),
        ("sub/x.onsa", "same", &[("sub.x", "same")]),
        ("a/b/c.onsa", "deep", &[("a.b.c", "deep")]),
    ];
    for (rel, filter, ids) in cases {
        expect_selected(d.root(), Some(filter), Some(&file_arg(&d, rel)), ids, &format!("{rel} --filter {filter:?}"));
    }
    // The same filter with the directory runs the tests of every module that it matches, so it was
    // the file that did the narrowing above.
    expect_selected(
        d.root(),
        Some("decays"),
        Some(&d.arg()),
        &[("top", "decays"), ("dsp", "decays"), ("dsp.voice", "decays"), ("dsp.filter", "decays")],
        "whole package --filter decays",
    );
}

// ---------------------------------------------------------------- 3. the filter's match is on the package

/// Spec §18.2, S-311: a non-empty text that matches only tests outside the module of the file is
/// not a usage error (the match is on every test of the package); the run selects 0 tests and
/// succeeds: exit code 0, no result line, an empty `tests` array and no diagnostic.
#[test]
fn a_filter_that_matches_only_outside_the_file_runs_no_test_and_succeeds() {
    let d = main_package("filter_outside");
    let cases: &[(&str, &str)] = &[
        ("dsp.onsa", "voice only"),
        ("dsp.onsa", "dsp.voice"),
        ("dsp.onsa", "dsp.filter"),
        ("dsp.onsa", "top only"),
        ("dsp.onsa", "deep"),
        ("dsp/voice.onsa", "rings"),
        ("top.onsa", "a.b.c"),
        ("x.onsa", "only sub"),
        ("sub/x.onsa", "only x"),
    ];
    for (rel, filter) in cases {
        expect_selected(d.root(), Some(filter), Some(&file_arg(&d, rel)), &[], &format!("{rel} --filter {filter:?}"));
        let out = run(d.root(), &["test", "--filter", filter, &file_arg(&d, rel)]);
        assert!(result_lines(&out).is_empty(), "{rel} --filter {filter:?}: {}", out.stdout);
    }
}

/// Spec §18.2: a non-empty text that matches no test of the package is the usage error (exit
/// code 2, nothing on the standard output) whatever file is given, also when the file has no
/// test. The text is matched by code points and case sensitive, and the file name is not part of
/// the full name text.
#[test]
fn a_filter_that_matches_nowhere_is_a_usage_error_with_a_file() {
    let d = main_package("filter_nowhere");
    for rel in ["dsp.onsa", "dsp/voice.onsa", "lib.onsa", "a/b/c.onsa"] {
        for filter in ["nomatch", "Decays", "dsp.onsa", "\"decays\" ok", "decays \""] {
            expect_usage_error(d.root(), &["--filter", filter, &file_arg(&d, rel)], &format!("{rel} {filter:?}"));
        }
    }
}

// ---------------------------------------------------------------- 4. no selected test

/// Spec §18.2, S-286: a file that has no `test` selects 0 tests, and the run succeeds with
/// nothing run (exit code 0, no result line, an empty `tests` array), though the package has
/// tests in other modules. A filter that matches those tests in other modules does not change it.
#[test]
fn a_file_with_no_test_runs_nothing_and_succeeds() {
    let d = main_package("no_test");
    let lib = file_arg(&d, "lib.onsa");
    expect_selected(d.root(), None, Some(&lib), &[], "lib");
    expect_selected(d.root(), None, Some("lib.onsa"), &[], "relative lib");
    expect_selected(d.root(), Some("decays"), Some(&lib), &[], "lib --filter decays");
    expect_selected(d.root(), Some("dsp"), Some(&lib), &[], "lib --filter dsp");
    let out = run(d.root(), &["test", &lib]);
    assert!(result_lines(&out).is_empty(), "{}", out.stdout);
}

// ---------------------------------------------------------------- 5. the diagnostics that stop the run

const BROKEN: &str = "pub fn broken() -> I32 {\n  y\n}\n";

fn broken_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("a.onsa", &tests_src(&["fine a"]));
    d.write("b.onsa", &tests_src(&["fine b"]));
    d.write("dsp/voice.onsa", &tests_src(&["fine voice"]));
    d.write("c.onsa", BROKEN);
    d
}

/// Spec §15.1, §18.2: a check error in another module stops `onsa test` with the file given too:
/// exit code 1, the diagnostic of the other module, no test run, and `tests` empty. The error is
/// reported whether the filter selects a test of the file, a test outside it, or nothing (the
/// errors of the check come before the match of `--filter`: not the 2 of the usage error).
/// `onsa check` on the same file does not print it (only the diagnostics of the file), while
/// `onsa check` on the module with the error prints the same diagnostic as `onsa test` does.
#[test]
fn a_check_error_in_another_module_stops_the_run_and_check_does_not_show_it() {
    let d = broken_package("stop_check");
    for rel in ["a.onsa", "b.onsa", "dsp/voice.onsa"] {
        let f = file_arg(&d, rel);
        for filter in [None, Some("fine"), Some("fine b"), Some("nomatch")] {
            let mut args = vec![];
            if let Some(x) = filter {
                args.extend(["--filter", x]);
            }
            args.push(&f);
            let label = format!("{rel} {filter:?}");
            let doc = stopped_doc(d.root(), &args, &label);
            assert_eq!(codes(&doc), ["E0302"], "{label}: {doc}");
            assert_eq!(positions(&doc, "E0302"), [("c.onsa".to_string(), 2)], "{label}: {doc}");
        }

        // `check` on this file: nothing of the other module (its exit code then is S-636, not
        // looked at here).
        let out = run(d.root(), &["check", "--json", &f]);
        let doc = doc_of(&out);
        assert!(diagnostics(&doc).is_empty(), "check {rel}: {}", out.stdout);
    }
    // `check` on the module with the error: the same diagnostic as `test` gives.
    let out = run(d.root(), &["check", "--json", &file_arg(&d, "c.onsa")]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(positions(&doc_of(&out), "E0302"), [("c.onsa".to_string(), 2)], "{}", out.stdout);
}

/// Spec §18.2: the diagnostics that stop the run are all of the package, not those of one file:
/// two modules with an error, one of them the given file, both are reported, and so is the one
/// below a given file (`dsp/voice.onsa` for `dsp.onsa`).
#[test]
fn all_the_diagnostics_that_stop_the_run_are_printed_whatever_the_file() {
    let d = broken_package("stop_all");
    d.write("dsp.onsa", &format!("{}\n{BROKEN}", tests_src(&["fine dsp"])));
    d.write("dsp/voice.onsa", &format!("{}\n{BROKEN}", tests_src(&["fine voice"])));
    let want = vec![("c.onsa".to_string(), 2), ("dsp.onsa".to_string(), 6), ("dsp/voice.onsa".to_string(), 6)];
    for rel in ["a.onsa", "dsp.onsa", "dsp/voice.onsa", "c.onsa"] {
        let doc = stopped_doc(d.root(), &[&file_arg(&d, rel)], rel);
        assert_eq!(codes(&doc), ["E0302"], "{rel}: {doc}");
        assert_eq!(positions(&doc, "E0302"), want, "{rel}: {doc}");
    }
    // `check` shows the diagnostics of the given file only.
    let out = run(d.root(), &["check", "--json", &file_arg(&d, "dsp.onsa")]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(positions(&doc_of(&out), "E0302"), [("dsp.onsa".to_string(), 6)], "{}", out.stdout);
}

/// Spec §18.2, §15.2: an E0200 that does not depend on the target (a `target` declaration of the
/// package; a pattern on a `Str`) in another module stops the run with a file given as well, also
/// with a filter that matches nothing (it comes before the match), and `check` reports it for its
/// own module only.
#[test]
fn an_e0200_independent_of_the_target_in_another_module_stops_the_run() {
    let cases: &[(&str, &str)] = &[
        ("target_decl", "target fn open() -> I32\n"),
        ("str_pattern", "fn pattern(s: Str) -> U32 {\n  match s {\n    \"abc\" => 1,\n    _ => 0,\n  }\n}\n"),
    ];
    for (tag, src) in cases {
        let d = Dir::pkg(tag);
        d.write("a.onsa", &tests_src(&["fine a"]));
        d.write("b.onsa", &tests_src(&["fine b"]));
        d.write("c.onsa", src);
        // `onsa check` reports the declaration (the names stage) but not the pattern, which is the
        // E0200 of a feature of the lowering: only the first is compared with `check`.
        let want = if *tag == "target_decl" {
            let own = run(d.root(), &["check", "--json", &file_arg(&d, "c.onsa")]);
            assert_eq!(own.code, 1, "{tag}: {}{}", own.stdout, own.stderr);
            let w = positions(&doc_of(&own), "E0200");
            assert!(!w.is_empty() && w.iter().all(|(f, _)| f == "c.onsa"), "{tag}: {}", own.stdout);
            Some(w)
        } else {
            None
        };

        for filter in [None, Some("fine a"), Some("fine b"), Some("nomatch")] {
            let f = file_arg(&d, "a.onsa");
            let mut args = vec![];
            if let Some(x) = filter {
                args.extend(["--filter", x]);
            }
            args.push(&f);
            let label = format!("{tag} {filter:?}");
            let doc = stopped_doc(d.root(), &args, &label);
            assert_eq!(codes(&doc), ["E0200"], "{label}: {doc}");
            let got = positions(&doc, "E0200");
            match &want {
                Some(w) => assert_eq!(&got, w, "{label}: {doc}"),
                None => assert!(!got.is_empty() && got.iter().all(|(f, _)| f == "c.onsa"), "{label}: {doc}"),
            }
        }
        let check_a = run(d.root(), &["check", "--json", &file_arg(&d, "a.onsa")]);
        assert!(diagnostics(&doc_of(&check_a)).is_empty(), "{tag}: {}", check_a.stdout);
    }
}

// ---------------------------------------------------------------- 6. the reach of the selected tests

/// `lib` has a function that uses a generator (`std.test.gen.u32`, which this version's
/// interpreter does not run, so a use that a run reaches is E0200, §15.2) and a plain test; `t`
/// has a test that calls it through `use` and a plain one; `u` has a plain test; `own` has a
/// function with a use of its own and a test that calls it.
const LIB: &str = "use std.test.gen

pub fn digit(n: U32) -> U32 {
  let _ = gen.u32(0, n)   // use-lib
  n
}

test \"lib plain\" {
  assert true
}
";

const T: &str = "use lib.{digit}

test \"calls digit\" {
  assert digit(1) == 1
}

test \"t plain\" {
  assert true
}
";

const U: &str = "test \"u plain\" {
  assert true
}
";

const OWN: &str = "use std.test.gen

fn own_digit(n: U32) -> U32 {
  let _ = gen.u32(1, n)   // use-own
  n
}

test \"own reach\" {
  assert own_digit(1) == 1
}
";

fn reach_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("lib.onsa", LIB);
    d.write("t.onsa", T);
    d.write("u.onsa", U);
    d.write("own.onsa", OWN);
    d
}

/// Spec §15.2, §18.2: the entries are the tests of the selection. The tests of `lib`, `t` and
/// `own` reach the uses, and the file given selects which of them count: `u.onsa` and `lib.onsa`
/// run (exit code 0) though the tests of `t.onsa` (which call `lib.digit`) and `own.onsa` are in
/// the package, and with no file the uses of `lib` and `own` are both reported (regression).
#[test]
fn a_use_that_only_the_tests_of_another_module_reach_is_not_reported() {
    let d = reach_package("reach_other");
    expect_selected(d.root(), None, Some(&file_arg(&d, "u.onsa")), &[("u", "u plain")], "u");
    expect_selected(d.root(), None, Some(&file_arg(&d, "lib.onsa")), &[("lib", "lib plain")], "lib");
    // With no file: both uses, as the entries are every test.
    let doc = stopped_doc(d.root(), &[&d.arg()], "whole package");
    assert_eq!(
        positions(&doc, "E0200"),
        [("lib.onsa".to_string(), line_of(LIB, "use-lib")), ("own.onsa".to_string(), line_of(OWN, "use-own"))],
        "{doc}"
    );
}

/// Spec §15.2, §18.2: a test of the given file reaches the use of another module through the
/// function it calls (`t.onsa` calls `lib.digit`): the E0200 is at the use in `lib.onsa`, the use
/// of `own.onsa` (reached by a test not selected) is not reported, no test runs (also not the
/// plain test of `t`), and `tests` is empty. A test of the file that reaches its own use
/// (`own.onsa`) is the E0200 in the same file.
#[test]
fn a_use_that_a_selected_test_reaches_through_another_module_is_e0200() {
    let d = reach_package("reach_through");
    let doc = stopped_doc(d.root(), &[&file_arg(&d, "t.onsa")], "t");
    assert_eq!(positions(&doc, "E0200"), [("lib.onsa".to_string(), line_of(LIB, "use-lib"))], "{doc}");
    assert_eq!(codes(&doc), ["E0200"], "{doc}");

    let doc = stopped_doc(d.root(), &[&file_arg(&d, "own.onsa")], "own");
    assert_eq!(positions(&doc, "E0200"), [("own.onsa".to_string(), line_of(OWN, "use-own"))], "{doc}");
    assert_eq!(codes(&doc), ["E0200"], "{doc}");

    // `--filter` chooses among the tests of the file: only the plain one is an entry, so it runs.
    expect_selected(
        d.root(),
        Some("t plain"),
        Some(&file_arg(&d, "t.onsa")),
        &[("t", "t plain")],
        "t --filter t plain",
    );
    // The test that calls `digit` is selected by its name: the E0200 again.
    let doc = stopped_doc(d.root(), &["--filter", "calls digit", &file_arg(&d, "t.onsa")], "t --filter calls digit");
    assert_eq!(positions(&doc, "E0200"), [("lib.onsa".to_string(), line_of(LIB, "use-lib"))], "{doc}");
}

/// Spec §15.2, §18.2: the entries are the tests that run, and the filter's match is on the whole
/// package. A filter that matches a test outside the file selects 0 tests, so the file's tests
/// that reach a use are not entries: exit code 0, no E0200.
#[test]
fn a_filter_that_selects_no_test_of_the_file_leaves_no_entry_to_reach_from() {
    let d = reach_package("reach_no_entry");
    expect_selected(d.root(), Some("u plain"), Some(&file_arg(&d, "t.onsa")), &[], "t --filter u plain");
    expect_selected(d.root(), Some("lib plain"), Some(&file_arg(&d, "own.onsa")), &[], "own --filter lib plain");
}

/// Spec §18.2: the match of `--filter` comes before the E0200 that the selected tests reach. The
/// file's tests reach a use, and a filter that matches nowhere is still the usage error (exit
/// code 2, nothing on the standard output, the reason on the standard error), not the E0200
/// (exit code 1).
#[test]
fn a_filter_that_matches_nowhere_comes_before_the_reach_with_a_file() {
    let d = reach_package("reach_order");
    for rel in ["t.onsa", "own.onsa"] {
        for filter in ["nomatch", "Calls digit", "calls  digit"] {
            expect_usage_error(d.root(), &["--filter", filter, &file_arg(&d, rel)], &format!("{rel} {filter:?}"));
        }
    }
}

/// Spec §18.2: the errors of the check come before the reach, with a file given too: the package
/// has a check error in another module and the given file's test reaches a use, and only the
/// check error is reported.
#[test]
fn the_errors_of_the_check_come_before_the_reach_with_a_file() {
    let d = reach_package("reach_check_first");
    d.write("c.onsa", BROKEN);
    for filter in [None, Some("calls digit"), Some("nomatch")] {
        let f = file_arg(&d, "t.onsa");
        let mut args = vec![];
        if let Some(x) = filter {
            args.extend(["--filter", x]);
        }
        args.push(&f);
        let label = format!("{filter:?}");
        let doc = stopped_doc(d.root(), &args, &label);
        assert_eq!(codes(&doc), ["E0302"], "{label}: {doc}");
        assert_eq!(positions(&doc, "E0302"), [("c.onsa".to_string(), 2)], "{label}: {doc}");
    }
}

// ---------------------------------------------------------------- 7. a failure in another module

const FAILING: &str = "test \"breaks\" {\n  assert 1 == 2\n}\n";

fn failing_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("good.onsa", &tests_src(&["fine"]));
    d.write("bad.onsa", FAILING);
    d.write("dsp.onsa", &tests_src(&["fine dsp"]));
    d.write("dsp/voice.onsa", FAILING);
    d.write("empty.onsa", "pub fn one() -> I32 {\n  1\n}\n");
    d
}

/// Spec §18.2 (exit code 1 is the failure of a test that runs): a test that fails in a module
/// that was not selected does not run, so it is neither in the output nor in the exit code. A
/// file whose own tests pass ends with 0 though another module fails, `dsp.onsa` too though the
/// module below it fails, and a file with no test ends with 0.
#[test]
fn a_failure_in_another_module_does_not_fail_the_run() {
    let d = failing_package("fail_other");
    expect_selected(d.root(), None, Some(&file_arg(&d, "good.onsa")), &[("good", "fine")], "good");
    expect_selected(d.root(), None, Some(&file_arg(&d, "dsp.onsa")), &[("dsp", "fine dsp")], "dsp");
    expect_selected(d.root(), None, Some(&file_arg(&d, "empty.onsa")), &[], "empty");
    // A filter that matches the failing test of another module selects 0 tests: success.
    expect_selected(d.root(), Some("breaks"), Some(&file_arg(&d, "good.onsa")), &[], "good --filter breaks");
}

/// Spec §18.2, §18.1, §11.8: the failing module given as the file fails the run (exit code 1)
/// with its own failure only, in the text line and in the JSON record, and the other failing
/// module is not in the output; with no file both fail (regression).
#[test]
fn a_failure_in_the_given_module_fails_the_run_and_only_that_one_is_reported() {
    let d = failing_package("fail_given");
    for (rel, module) in [("bad.onsa", "bad"), ("dsp/voice.onsa", "dsp.voice")] {
        let out = run(d.root(), &["test", &file_arg(&d, rel)]);
        assert_eq!(out.code, 1, "{rel}: {}{}", out.stdout, out.stderr);
        assert_eq!(
            sorted_result_lines(&out),
            [format!("test {module} \"breaks\" failed at {rel}:2: assert 1 == 2")],
            "{rel}: {}",
            out.stdout
        );
        let (jout, doc) = test_json(d.root(), &[&file_arg(&d, rel)]);
        assert_eq!(jout.code, 1, "{rel}: {}", jout.stdout);
        assert!(diagnostics(&doc).is_empty(), "{rel}: {doc}");
        assert_eq!(identities(&doc), [(module.to_string(), "breaks".to_string())], "{rel}: {doc}");
        let f = failure_of(record(&doc, module, "breaks"));
        assert_eq!(span_of(&f["span"]).file, rel);
        assert_eq!(str_of(f, "message"), "assert 1 == 2");
    }
    // With a filter that keeps the test the same, and one that drops it (0 selected: success).
    let out = run(d.root(), &["test", "--filter", "breaks", &file_arg(&d, "bad.onsa")]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    expect_selected(d.root(), Some("fine"), Some(&file_arg(&d, "bad.onsa")), &[], "bad --filter fine");

    // No file: both fail, and the two good ones run.
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let (_, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(
        identities(&doc),
        sorted_ids(&[("bad", "breaks"), ("dsp", "fine dsp"), ("dsp.voice", "breaks"), ("good", "fine")]),
        "{doc}"
    );
}

// ---------------------------------------------------------------- 8. no file selects every test

/// Spec §15.1, §18.2 (regression, passes today): without a file, `onsa test` selects every test
/// of the package: the directory of the package, its `onsa.toml`, the root as `.`, and no path
/// with the working directory at the root or inside a directory of the package. A `--filter`
/// narrows them as it did before.
#[test]
fn no_file_selects_every_test_of_the_package() {
    let d = main_package("all_tests");
    let root = d.arg();
    let manifest = file_arg(&d, "onsa.toml");
    let dsp = d.root().join("dsp");
    let a_b = d.root().join("a/b");
    expect_selected(d.root(), None, Some(&root), ALL, "directory");
    expect_selected(d.root(), None, Some(&manifest), ALL, "onsa.toml");
    expect_selected(d.root(), None, Some("onsa.toml"), ALL, "relative onsa.toml");
    expect_selected(d.root(), None, Some("."), ALL, ".");
    expect_selected(d.root(), None, None, ALL, "no path at the root");
    expect_selected(&dsp, None, None, ALL, "no path inside dsp");
    expect_selected(&a_b, None, None, ALL, "no path inside a/b");

    let decays: &[Id] = &[("top", "decays"), ("dsp", "decays"), ("dsp.voice", "decays"), ("dsp.filter", "decays")];
    expect_selected(d.root(), Some("decays"), Some(&root), decays, "directory --filter");
    expect_selected(d.root(), Some("decays"), Some(&manifest), decays, "onsa.toml --filter");
    expect_selected(d.root(), Some("decays"), None, decays, "no path --filter");
    expect_selected(&dsp, Some("decays"), None, decays, "inside dsp --filter");
    expect_selected(d.root(), Some(""), Some(&root), ALL, "directory --filter empty");
}
