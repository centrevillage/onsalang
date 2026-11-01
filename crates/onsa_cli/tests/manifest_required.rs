//! The E1104 of the keys `onsa.toml` must have, and the escape of a value in the text of E1103 (spec
//! §15.3, §18.1, §18.2; S-99, S-597, S-827; W4-02 U2b2).
//!
//! The cases in `tests/spec/manifest/` (`e1104_*`) check which line carries which code (the marker
//! `#~`) for the four keys `name`, `edition`, `kind` and `lang` (`kind = "source"`), the pairs of
//! tables and keys that are not missing but wrong (E1103 only), and that all the errors of the
//! manifest are reported. What a marker cannot check is here:
//!
//! - the document of `check --json` and `test --json` for an E1104: the code, the file `onsa.toml`
//!   and the exit code 2 (§18.2); the candidate of the missing `edition` is one candidate whose edits
//!   are in `onsa.toml` and put `edition = "2026"` in it, and the manifest has no error after it;
//!   the missing `name` has no candidate (no value is known, S-597); without the table `[package]`
//!   the candidate of `edition` is applied and the E1104 of `name` is what is left;
//! - every command that reads the manifest stops on an E1104 before the source is read (§18.1);
//! - the value of a key written into the text of an E1103 (the output without `--json`) has its control
//!   characters and line breaks escaped, so a manifest cannot move the cursor or paint the terminal of
//!   the one who reads the report (the value of `name`, of the name of a target and of `kind`).
//!
//! The text of the diagnostics goes to the standard output (`spec/tools.md` §4); both streams are
//! looked at, because what the escape protects is the terminal.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use serde_json::Value;
use test_support::sweep::{apply_fix_texts, read_tree};
use test_support::*;

/// A source with a type error (E0401) and a flow, so that every command has something to read: a
/// command that reads it would report the E0401, and the manifest's error must come first.
const BAD_SOURCE: &str = "pub fn f() -> I32 {
  true
}

pub flow voice(x: F32 at sample) -> F32 at sample {
  x
}
";

/// A source with no error.
const GOOD_SOURCE: &str = "pub fn f() -> I32 { 1 }\n";

/// The one target every manifest of this file has; it is complete (`platform` is written).
const TARGET: &str = "[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\n";

fn package(tag: &str, manifest: &str, source: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", source);
    d
}

fn codes_of(ds: &[Value]) -> Vec<&str> {
    ds.iter().map(|d| str_of(d, "code")).collect()
}

/// `onsa check --json` of the package: the exit code is 2 and the document is returned.
fn check_json(d: &Dir) -> Value {
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    doc_of(&out)
}

/// The edits of a candidate (`fixes` entry): the file they are in and the text they put.
fn edits_of(fix: &Value) -> Vec<(String, String)> {
    array_of(fix, "edits")
        .iter()
        .map(|e| (str_of(&e["span"], "file").to_string(), str_of(e, "replace").to_string()))
        .collect()
}

/// §15.3 (`edition`: required), §18.1 (E1104; "値が決まるときはキーの挿入を修正候補にする"), S-597: the
/// missing `edition` is an E1104 at the heading of `[package]` (line 1) with one candidate, whose edits are
/// in `onsa.toml` and put `edition = "2026"`. The exit code is 2 (§18.2).
#[test]
fn the_missing_edition_has_one_candidate_that_puts_the_key_in_onsa_toml() {
    let manifest = format!("[package]\nname = \"demo\"\n\n{TARGET}");
    let d = package("required_edition", &manifest, GOOD_SOURCE);
    let doc = check_json(&d);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104"], "{doc}");
    assert_eq!(str_of(&ds[0]["span"], "file"), "onsa.toml", "{doc}");
    assert_eq!(int_of(&ds[0]["span"], "line"), 1, "the heading of [package]: {doc}");
    let fixes = array_of(&ds[0], "fixes");
    assert_eq!(fixes.len(), 1, "one candidate: the value is fixed (S-597): {doc}");
    let edits = edits_of(&fixes[0]);
    assert!(!edits.is_empty(), "{doc}");
    assert!(edits.iter().all(|(f, _)| f == "onsa.toml"), "the edits are in onsa.toml: {edits:?}");
    let put: String = edits.iter().map(|(_, r)| r.as_str()).collect();
    assert!(put.contains("edition = \"2026\""), "the candidate puts `edition = \"2026\"`: {edits:?}");
}

/// §18.1: the candidate applied once leaves a manifest without error: the check of the package is clean
/// (exit code 0), so the loop of repair stops (the edition is the only error).
#[test]
fn the_candidate_of_the_missing_edition_leaves_no_error() {
    let manifest = format!("[package]\nname = \"demo\"\n\n{TARGET}");
    let d = package("required_edition_fixed", &manifest, GOOD_SOURCE);
    let doc = check_json(&d);
    let fix = &array_of(&diagnostics(&doc)[0], "fixes")[0];
    let mut texts = read_tree(d.root());
    apply_fix_texts(&mut texts, fix);
    d.write("onsa.toml", &texts["onsa.toml"]);
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 0, "after the candidate: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}", out.stdout);
}

/// §15.3 (`name`: required), S-597: the missing `name` is an E1104 at the heading of `[package]` and no
/// value is known for it, so it has no candidate. The exit code is 2.
#[test]
fn the_missing_name_has_no_candidate() {
    let manifest = format!("[package]\nedition = \"2026\"\n\n{TARGET}");
    let d = package("required_name", &manifest, GOOD_SOURCE);
    let doc = check_json(&d);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104"], "{doc}");
    assert_eq!(str_of(&ds[0]["span"], "file"), "onsa.toml", "{doc}");
    assert_eq!(int_of(&ds[0]["span"], "line"), 1, "{doc}");
    assert_eq!(ds[0]["fixes"], Value::Array(vec![]), "no value is known for `name`: {doc}");
}

/// A target without `kind`, and one of `kind = "source"` without `lang`, have no candidate either (§15.3
/// `kind` and `lang` rows): each is an E1104 at its heading, line 5 and line 13 here (`staticlib` in
/// between needs no `lang`).
#[test]
fn the_missing_kind_and_lang_are_at_the_headings_and_have_no_candidate() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.a]
platform = \"host\"
lang = \"c\"

[targets.b]
kind = \"staticlib\"
platform = \"host\"

[targets.c]
kind = \"source\"
platform = \"host\"
";
    let d = package("required_kind_lang", manifest, GOOD_SOURCE);
    let doc = check_json(&d);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104", "E1104"], "{doc}");
    let lines: Vec<u64> = ds.iter().map(|d| int_of(&d["span"], "line")).collect();
    assert_eq!(lines, vec![5, 13], "the headings of `[targets.a]` and `[targets.c]`: {doc}");
    for d in ds {
        assert_eq!(str_of(&d["span"], "file"), "onsa.toml", "{doc}");
        assert_eq!(d["fixes"], Value::Array(vec![]), "no value is known: {d}");
    }
}

/// §15.3, §18.1, S-827: without the table `[package]` the keys `name` and `edition` are two E1104 (the
/// top of the manifest, line 1); the candidate of `edition` is the one candidate there is; applied, the
/// E1104 of `name` is what is left, and it has no candidate.
#[test]
fn without_the_package_table_name_and_edition_are_two_e1104_and_the_name_is_left_after_the_candidate() {
    let d = package("required_no_package", TARGET, GOOD_SOURCE);
    let doc = check_json(&d);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104", "E1104"], "{doc}");
    for e in ds {
        assert_eq!(str_of(&e["span"], "file"), "onsa.toml", "{doc}");
        assert_eq!(int_of(&e["span"], "line"), 1, "the top of the manifest: {doc}");
    }
    let with_fix: Vec<&Value> = ds.iter().filter(|e| !array_of(e, "fixes").is_empty()).collect();
    assert_eq!(with_fix.len(), 1, "one of the two (the edition) has a candidate: {doc}");
    let fixes = array_of(with_fix[0], "fixes");
    assert_eq!(fixes.len(), 1, "{doc}");
    let put: String = edits_of(&fixes[0]).iter().map(|(_, r)| r.clone()).collect();
    assert!(put.contains("edition = \"2026\""), "{put:?}");

    let mut texts = read_tree(d.root());
    apply_fix_texts(&mut texts, &fixes[0]);
    d.write("onsa.toml", &texts["onsa.toml"]);
    let doc = check_json(&d);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104"], "after the candidate only the `name` is left: {doc}");
    assert_eq!(ds[0]["fixes"], Value::Array(vec![]), "{doc}");
}

/// §15.3, §18.1: a key that is written with the wrong type is wrong, not missing: `edition = 2026` is an
/// E1103 and no E1104 (and `package = 1` the same), so there is no candidate that would insert a second
/// `edition`.
#[test]
fn a_key_of_the_wrong_type_is_not_missing_and_a_table_of_the_wrong_type_is_not_read() {
    let wrong_edition = format!("[package]\nname = \"demo\"\nedition = 2026\n\n{TARGET}");
    let d = package("required_wrong_edition", &wrong_edition, GOOD_SOURCE);
    let doc = check_json(&d);
    assert_eq!(codes_of(diagnostics(&doc)), vec!["E1103"], "{doc}");

    let package_int = format!("package = 1\n\n{TARGET}");
    let d = package("required_package_int", &package_int, GOOD_SOURCE);
    let doc = check_json(&d);
    assert_eq!(codes_of(diagnostics(&doc)), vec!["E1103"], "{doc}");
}

/// §18.1, §18.2: `test --json` prints the document with the E1104 too, exit code 2, `tests` empty (no
/// test has run, as with the other diagnostics of `onsa.toml`; the E0401 of the source is not read).
#[test]
fn test_json_prints_the_e1104_with_an_empty_tests_array() {
    let manifest = format!("[package]\nedition = \"2026\"\n\n{TARGET}");
    let d = package("required_test_json", &manifest, BAD_SOURCE);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1104"], "{doc}");
    assert_eq!(str_of(&ds[0]["span"], "file"), "onsa.toml", "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
}

/// §18.1, §18.2: every command that reads the manifest stops on the E1104 with exit code 2 before the
/// source is read: the E0401 of the source is not reported.
#[test]
fn every_command_stops_on_an_e1104_before_the_source() {
    let manifest = format!("[package]\nname = \"demo\"\n\n{TARGET}");
    let d = package("required_commands", &manifest, BAD_SOURCE);
    let dir = d.arg();
    let commands: [&[&str]; 5] = [
        &["check", &dir],
        &["test", &dir],
        &["interface", &dir],
        &["graph", "voice", &dir],
        &["build", "--target", "host", &dir],
    ];
    for args in commands {
        let out = run(d.root(), args);
        assert_eq!(out.code, 2, "onsa {args:?}: {}{}", out.stdout, out.stderr);
        let found: Vec<&str> = out
            .stdout
            .lines()
            .filter_map(|l| l.split_once(": error[").and_then(|(_, r)| r.split_once(']')).map(|(c, _)| c))
            .collect();
        assert_eq!(found, vec!["E1104"], "onsa {args:?}: {}{}", out.stdout, out.stderr);
    }
}

/// The control characters that may stay in the text of a report: the line break and the tab. Every
/// other one (ESC, BEL, CR, DEL, ...) is a way to write over the terminal.
fn stray_control(text: &str) -> Option<char> {
    text.chars().find(|c| c.is_control() && *c != '\n' && *c != '\t')
}

/// The text of `check` for the manifest has an E1103 on one line of the heading kind
/// (`<file>:<line>:<column>: error[E1103]: ...`), and no control character of the value is in either
/// stream, whatever the wording of the escape is (spec/tools.md §4: the text is for a person).
fn assert_value_is_escaped(tag: &str, manifest: &str) {
    let d = package(tag, manifest, GOOD_SOURCE);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "{tag}: {}{}", out.stdout, out.stderr);
    let headers = out.stdout.lines().filter(|l| l.contains(": error[E1103]: ")).count();
    assert_eq!(headers, 1, "{tag}: one E1103 line: {}{}", out.stdout, out.stderr);
    for (name, text) in [("standard output", &out.stdout), ("standard error", &out.stderr)] {
        assert_eq!(stray_control(text), None, "{tag}: a control character of the value in the {name}: {text:?}");
    }
}

/// S-99 (U2b1 低 2): the value of `name` is written into the message of its E1103; its ESC and line break
/// do not come out raw.
#[test]
fn the_value_of_name_is_escaped_in_the_text_of_its_e1103() {
    let manifest = format!("[package]\nname = \"a\\u001b[31mX\\nY\"\nedition = \"2026\"\n\n{TARGET}");
    assert_value_is_escaped("escape_name", &manifest);
}

/// The name of a target is written into its E1103 too (`[targets."a\u001bb"]`).
#[test]
fn the_name_of_a_target_is_escaped_in_the_text_of_its_e1103() {
    let manifest = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.\"a\\u001bb\"]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\n";
    assert_value_is_escaped("escape_target", manifest);
}

/// A value that is not in a closed list (`kind`) is written into its E1103 too.
#[test]
fn a_value_not_in_a_closed_list_is_escaped_in_the_text_of_its_e1103() {
    let manifest = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"d\\u001b[2Jl\\rl\"\nlang = \"c\"\nplatform = \"host\"\n";
    assert_value_is_escaped("escape_kind", manifest);
}
