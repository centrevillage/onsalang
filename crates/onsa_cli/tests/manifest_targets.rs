//! The E0200 of the values of a target in `onsa.toml`, through the commands (spec §15.3, §18.1, §18.2;
//! S-154, S-824, S-825, S-827; R-166; W4-02 U3a).
//!
//! The cases in `tests/spec/manifest/` (`e0200_target_*`) check which line carries the E0200 in the
//! build of which target (the marker `#~ E0200 [t]`), that a default value is not reported, that a
//! case with such a marker does not stop `check` and `test`, and that every value of a target is
//! reported. What a marker cannot check is here:
//!
//! - the text of `onsa build --target t` for a target with unsupported values: the exit code is 2 and
//!   each report is an E0200 whose position is a line of `onsa.toml` (the value, the element of
//!   `provides`, the heading of `bind`);
//! - `check` and `test` of the same manifest are not stopped (exit code 0), whichever target has the
//!   value (§15.3 "未対応のターゲットがあっても、`check` と `test` は止まらない");
//! - the report together: `check` stops on the error that every command reports (here an E1103) and
//!   `build --target t` adds the E0200 of the target `t` to it, in one run (S-827, §18.1 "`--target` を取る
//!   コマンドは…まとめて報告する"); both end with exit code 2;
//! - the E0200 of another target is not reported by the build of `t`, and the default values build;
//! - `onsa explain E0200` names the values of the manifest this version does not support (§15.3 "診断の
//!   文面と `onsa explain E0200` で示す").
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use test_support::*;

/// A source with a function and a test, so that `check`, `test` and `build` all have something to read.
const SOURCE: &str = "pub fn f() -> I32 { 1 }

test \"f is one\" {
  assert f() == 1
}
";

fn package(tag: &str, manifest: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", SOURCE);
    d
}

/// The line (from 1) of the first line of the manifest that holds `needle`.
fn line_of(manifest: &str, needle: &str) -> usize {
    manifest
        .lines()
        .position(|l| l.contains(needle))
        .unwrap_or_else(|| panic!("no line holds {needle:?} in\n{manifest}"))
        + 1
}

/// The codes and the positions (`file:line`) of the diagnostics in the text output, sorted: a
/// diagnostic starts a line `<file>:<line>:<column>: error[<code>]: <message>` (`spec/tools.md` §4).
/// The diagnostics of one run are looked at as a set; the order of the report is not what is checked.
fn text_diagnostics(out: &Out) -> Vec<(String, String)> {
    let mut found: Vec<(String, String)> = out
        .stdout
        .lines()
        .chain(out.stderr.lines())
        .filter_map(|l| {
            let (head, rest) = l.split_once(": error[")?;
            let code = rest.split_once(']')?.0;
            let mut parts = head.rsplitn(3, ':');
            let _column = parts.next()?;
            let line = parts.next()?;
            let file = parts.next()?;
            Some((code.to_string(), format!("{file}:{line}")))
        })
        .collect();
    found.sort();
    found
}

fn at(code: &str, line: usize) -> (String, String) {
    (code.to_string(), format!("onsa.toml:{line}"))
}

/// One target `t` with an unsupported value in each kind of place: a key with a value (`kind`,
/// `main_frame`, `memory.bulk`), an element of an array (`"Fs"` of `provides`, on a line of its own) and a
/// table (the heading of `bind`).
const ALL_VALUES: &str = "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"exe\"
platform = \"host\"
main_frame = \"static\"
provides = [
  \"Alloc\",
  \"Fs\",
]

[targets.t.memory]
bulk = true

[targets.t.bind]
\"audio.device\" = \"daisy_hal.audio\"
";

/// §15.3 (the table, the paragraph on the values this version does not support), S-154, S-824, S-827,
/// R-166: the build of `t` reports an E0200 at the value of `kind`, `main_frame`, the element `"Fs"` of
/// `provides` (not `"Alloc"`), `memory.bulk = true` and the heading of `bind`, all in one run, in
/// `onsa.toml`; the exit code is 2 (§18.2).
#[test]
fn build_reports_every_unsupported_value_at_its_line_with_exit_code_2() {
    let d = package("targets_all", ALL_VALUES);
    let out = run(d.root(), &["build", "--target", "t", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let mut want: Vec<(String, String)> = [
        line_of(ALL_VALUES, "kind = "),
        line_of(ALL_VALUES, "main_frame"),
        line_of(ALL_VALUES, "\"Fs\""),
        line_of(ALL_VALUES, "bulk = true"),
        line_of(ALL_VALUES, "[targets.t.bind]"),
    ]
    .iter()
    .map(|&l| at("E0200", l))
    .collect();
    want.sort();
    assert_eq!(text_diagnostics(&out), want, "{}{}", out.stdout, out.stderr);
}

/// §15.3, S-154: the same manifest does not stop `check` or `test`: both end with exit code 0, `check
/// --json` has no diagnostic, and the test of the package runs and passes.
#[test]
fn check_and_test_are_not_stopped_by_the_unsupported_values_of_a_target() {
    let d = package("targets_not_stopped", ALL_VALUES);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(text_diagnostics(&out).is_empty(), "{}{}", out.stdout, out.stderr);
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}", out.stdout);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    assert_eq!(tests_of(&doc).len(), 1, "the test of the package ran: {doc}");
}

/// §15.3, S-154, S-824, S-827: the value of the target `u` is not the business of the build of `t`, and
/// the build of `u` reports it at the value (`lang = "js"`). The target `t` writes the
/// default values (S-825: `main_frame = "stack"`, `memory.bulk = false`, a `bind` with nothing in it,
/// `fp = "strict"`, `provides = ["Alloc"]`) and its build ends with exit code 0.
#[test]
fn the_value_of_another_target_is_not_reported_and_the_default_values_build() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"source\"
lang = \"c\"
platform = \"host\"
fp = \"strict\"
main_frame = \"stack\"
provides = [\"Alloc\"]

[targets.t.memory]
bulk = false

[targets.t.bind]

[targets.u]
kind = \"source\"
lang = \"js\"
platform = \"host\"
";
    let d = package("targets_other", manifest);
    let out = run(d.root(), &["build", "--target", "t", &d.arg()]);
    assert_eq!(out.code, 0, "the build of t: {}{}", out.stdout, out.stderr);
    assert!(text_diagnostics(&out).is_empty(), "{}{}", out.stdout, out.stderr);
    assert!(!format!("{}{}", out.stdout, out.stderr).contains("E0200"), "{}{}", out.stdout, out.stderr);
    let out = run(d.root(), &["build", "--target", "u", &d.arg()]);
    assert_eq!(out.code, 2, "the build of u: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "lang = \"js\""))],
        "{}{}",
        out.stdout,
        out.stderr
    );
}

/// §18.1 ("`--target` を取るコマンドは、そのターゲットに依る検査をマニフェストの検査と同じ回に行い、まとめて報告する"),
/// S-827: an error that every command reports (`edition = "2025"`, an E1103 on line 3) and the E0200 of
/// the target `t`: `check` stops on the E1103 alone, and `build --target t` reports both in one run.
/// Both end with exit code 2 (§18.2).
#[test]
fn build_reports_the_error_of_every_command_and_the_target_value_together() {
    let manifest = "[package]
name = \"demo\"
edition = \"2025\"

[targets.t]
kind = \"exe\"
platform = \"host\"
";
    let d = package("targets_together", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert_eq!(text_diagnostics(&out), vec![at("E1103", 3)], "check: {}{}", out.stdout, out.stderr);
    let out = run(d.root(), &["build", "--target", "t", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "kind = ")), at("E1103", 3)],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// The lines of the text of `explain` that start a list item and hold `word`.
fn items_with<'a>(text: &'a str, word: &str) -> Vec<&'a str> {
    text.lines().filter(|l| l.trim_start().starts_with("- ") && l.contains(word)).collect()
}

/// §15.3 ("どの値が未対応かは…診断の文面と `onsa explain E0200` で示す"), §18.1 (E0200: "どの機能が未対応かは
/// コンパイラの版で変わり、`onsa explain E0200` で示す"): the list of `explain E0200` has an item that names
/// each key of a target that this version reports as E0200 whatever its value (`fast_budget`,
/// `bulk_budget`) and the key `main_frame`. Only that the word is in an item of the list is checked; the
/// wording of the item is not fixed by the spec (the prose before the list names `main_frame` already,
/// so the item is looked for).
#[test]
fn explain_e0200_names_the_values_of_the_manifest() {
    let out = run(&std::env::temp_dir(), &["explain", "E0200"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    for word in ["main_frame", "fast_budget", "bulk_budget"] {
        assert!(!items_with(&out.stdout, word).is_empty(), "no item of the list names `{word}`:\n{}", out.stdout);
    }
}
