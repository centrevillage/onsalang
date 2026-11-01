//! The E1103 of the values of `onsa.toml` through the commands: what its note shows, that it stops
//! every command before the source is read, and that the values the list names but this version
//! cannot build do not stop `check` and `test` (spec §15.3, §18.1, §18.2; S-83, S-99, S-154,
//! S-597, S-626, S-628, S-827; W4-02 U2b1).
//!
//! The cases in `tests/spec/manifest/` check which line carries which code (the marker `#~`), for
//! the types of the values, the closed lists, the shapes of the names, `prefix`, the version of std,
//! the budgets and the dependencies other than std (E0200). What a marker cannot check is here:
//!
//! - the note of an E1103: the values of the list when a value is not in a closed list, the
//!   version of the embedded std when a pin of std differs (the second line of `onsa --version`),
//!   and a note at all for `name = "std"` (the wording is not fixed). No fix candidate (S-597);
//! - a value error stops every command that reads the manifest before the source, with exit code 2
//!   (§18.1, §18.2), as an E1102 does (`manifest_diagnostics.rs`);
//! - `check` and `test` do not stop at a value that the lists name and this version cannot build
//!   (`kind = "clap"`, `lang = "js"`, ...): that is the E0200 of the build of the target (§15.3).
//!
//! The dependencies other than std (E0200 at the key) and their exit code are in
//! `package_model.rs`; they are not repeated here.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use serde_json::Value;
use test_support::*;

/// A source with a type error (E0401) and a flow, so that every command has something to read: a
/// command that reads it would report the E0401, and the manifest's error must come first.
const SOURCE: &str = "pub fn f() -> I32 {
  true
}

pub flow voice(x: F32 at sample) -> F32 at sample {
  x
}
";

/// The lines of a good manifest with one target `host`; every key is on its own line, and the keys
/// are all different, so a key names its line.
const LINES: [&str; 12] = [
    "[package]",
    "name = \"demo\"",
    "edition = \"2026\"",
    "",
    "[targets.host]",
    "kind = \"source\"",
    "lang = \"c\"",
    "platform = \"host\"",
    "fp = \"strict\"",
    "provides = []",
    "panic = \"trap\"",
    "panic_messages = true",
];

/// `main_frame` is the last key of the target.
const LAST: &str = "main_frame = \"stack\"";

/// The good manifest with the value of `key` replaced by `value` (TOML text), and the line (from 1)
/// of the key.
fn manifest_with(key: &str, value: &str) -> (String, u64) {
    let mut lines: Vec<String> = LINES.iter().map(|s| s.to_string()).collect();
    lines.push(LAST.to_string());
    let at = lines
        .iter()
        .position(|l| l.starts_with(&format!("{key} = ")))
        .unwrap_or_else(|| panic!("no key `{key}` in the manifest"));
    lines[at] = format!("{key} = {value}");
    (lines.join("\n") + "\n", at as u64 + 1)
}

fn package(tag: &str, manifest: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", SOURCE);
    d
}

fn codes_of(ds: &[Value]) -> Vec<&str> {
    ds.iter().map(|d| str_of(d, "code")).collect()
}

/// The messages of the notes of a diagnostic, joined.
fn notes_of(d: &Value) -> String {
    array_of(d, "notes").iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

/// `onsa check --json` of the package: the exit code and the document, which must have exactly one
/// E1103 in `onsa.toml` at `line`, without a fix candidate (S-597). Returns that diagnostic.
fn the_one_e1103(d: &Dir, line: u64) -> Value {
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1103"], "{doc}");
    let e = &ds[0];
    assert_eq!(str_of(&e["span"], "file"), "onsa.toml", "{doc}");
    assert_eq!(int_of(&e["span"], "line"), line, "the line of the value: {doc}");
    assert_eq!(e["fixes"], Value::Array(vec![]), "an E1103 has no fix candidate (S-597): {e}");
    e.clone()
}

/// `onsa --version` prints two lines, `onsa x.y.z` and `std x.y.z` (§18.2; S-626). The second
/// line without its word is the version of the embedded std.
fn embedded_std_version() -> String {
    let d = Dir::bare("values_version");
    let out = run(d.root(), &["--version"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let lines: Vec<&str> = out.stdout.lines().collect();
    assert_eq!(lines.len(), 2, "two lines: {:?}", out.stdout);
    assert!(lines[0].starts_with("onsa "), "the first line is the compiler's: {:?}", lines[0]);
    let v = lines[1].strip_prefix("std ").unwrap_or_else(|| panic!("the second line is `std x.y.z`: {:?}", lines[1]));
    assert!(!v.is_empty() && v.split('.').count() == 3, "x.y.z: {v:?}");
    v.to_string()
}

/// §18.1, S-597: a value that is not in a closed list is an E1103 at the value, and the note lists
/// the values of the list (`edition`, `kind`, `lang`, `fp`, `panic`, `main_frame`). The words are
/// looked for in the note, because the wording is not fixed.
#[test]
fn a_value_not_in_a_closed_list_has_the_values_of_the_list_in_its_note() {
    let cases: [(&str, &str, &[&str]); 6] = [
        ("edition", "\"2025\"", &["2026"]),
        ("kind", "\"dll\"", &["exe", "clap", "vst3", "au", "wasm-worklet", "staticlib", "source"]),
        ("lang", "\"rust\"", &["c", "js"]),
        ("fp", "\"relaxed\"", &["strict", "strict-ftz"]),
        ("panic", "\"abort\"", &["poison", "trap", "reset", "halt"]),
        ("main_frame", "\"heap\"", &["stack", "static"]),
    ];
    for (key, value, words) in cases {
        let (manifest, line) = manifest_with(key, value);
        let d = package(&format!("values_list_{key}"), &manifest);
        let e = the_one_e1103(&d, line);
        let n = notes_of(&e);
        for w in words {
            assert!(n.contains(w), "`{key} = {value}`: the value `{w}` of the list is not in the note: {n:?}");
        }
    }
}

/// §15.3, §18.1, S-83, S-626: a pin of std that is not the embedded version is an E1103 at the
/// value, and the note shows the embedded std version, the second line of `onsa --version`. The
/// pin that is that version is not reported (the exit code is 0).
#[test]
fn a_pin_of_std_that_differs_has_the_embedded_version_in_its_note() {
    let version = embedded_std_version();
    let manifest = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[dependencies]\nstd = \"9.9.9\"\n";
    let d = package("values_std_differs", manifest);
    let e = the_one_e1103(&d, 6);
    let n = notes_of(&e);
    assert!(n.contains(&version), "the embedded version {version:?} in the note: {n:?}");

    let good = format!("[package]\nname = \"demo\"\nedition = \"2026\"\n\n[dependencies]\nstd = \"{version}\"\n");
    let d = Dir::bare("values_std_matches");
    d.write("onsa.toml", &good);
    d.write("m.onsa", "pub fn f() -> I32 { 1 }\n");
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 0, "the pin that matches is not reported: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{}", out.stdout);
}

/// §15.3, S-628: `name = "std"` is an E1103 at the value, with a note (that `std` is the name of
/// the embedded standard library; the wording is not fixed) and no fix candidate.
#[test]
fn a_package_named_std_is_an_e1103_with_a_note() {
    let manifest = "[package]\nname = \"std\"\nedition = \"2026\"\n";
    let d = package("values_name_std", manifest);
    let e = the_one_e1103(&d, 2);
    assert!(!array_of(&e, "notes").is_empty(), "a note that says what `std` is: {e}");
}

/// §18.1, §18.2: the other commands that read the manifest stop at a wrong value too, with exit
/// code 2, and report the E1103 only: the E0401 of the source is not reached. `fp = "relaxed"` is
/// the value (§15.5: it cannot be set for a whole target).
#[test]
fn every_command_stops_on_a_wrong_value_before_the_source() {
    let (manifest, line) = manifest_with("fp", "\"relaxed\"");
    let d = package("values_commands", &manifest);
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
        assert_eq!(found, vec!["E1103"], "onsa {args:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains(&format!("onsa.toml:{line}:")), "onsa {args:?} at line {line}: {}", out.stdout);
    }
}

/// A target `name` with the lines of the good target, where the value of `over.0` is `over.1`
/// (when `over.0` is empty, no value is replaced), and `extra` after the lines.
fn target_with(name: &str, over: (&str, &str), extra: &str) -> String {
    let mut s = format!("\n[targets.{name}]\n");
    for l in LINES.iter().skip(5).chain([LAST].iter()) {
        let key = l.split(" = ").next().unwrap();
        if key == over.0 {
            s.push_str(&format!("{key} = {}\n", over.1));
        } else {
            s.push_str(l);
            s.push('\n');
        }
    }
    s.push_str(extra);
    s
}

/// A package with that manifest and a source with no error; `command` is run on it.
fn runs_clean(tag: &str, manifest: &str, commands: &[&str]) {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", "pub fn f() -> I32 { 1 }\n");
    for cmd in commands {
        let out = run(d.root(), &[cmd, &d.arg()]);
        assert_eq!(out.code, 0, "onsa {cmd}: {}{}", out.stdout, out.stderr);
    }
}

/// §15.3, §18.1, S-154, S-597: a value that a closed list names and this version cannot build
/// (every `kind` but `source`, `lang = "js"`, `fp = "strict-ftz"`, `main_frame = "static"`, the
/// panic modes) is not an error of the manifest's check: its E0200 is reported by the build of the
/// target (U3), so `check` and `test` go on. The cases of `tests/spec/manifest/` cannot hold this
/// form, because the runner builds every target of a case. The source here has an error too, so
/// that a command that stopped at the manifest would show as exit code 2 and no E0401.
#[test]
fn values_the_lists_name_and_the_build_cannot_do_do_not_stop_check_and_test() {
    let mut manifest = String::from("[package]\nname = \"demo\"\nedition = \"2026\"\n");
    for k in ["exe", "clap", "vst3", "au", "wasm-worklet", "staticlib"] {
        manifest.push_str(&target_with(&format!("t_{}", k.replace('-', "_")), ("kind", &format!("\"{k}\"")), ""));
    }
    manifest.push_str(&target_with("t_js", ("lang", "\"js\""), ""));
    manifest.push_str(&target_with("t_ftz", ("fp", "\"strict-ftz\""), ""));
    manifest.push_str(&target_with("t_static", ("main_frame", "\"static\""), ""));
    for p in ["poison", "reset", "halt"] {
        manifest.push_str(&target_with(&format!("t_{p}"), ("panic", &format!("\"{p}\"")), ""));
    }
    let d = package("values_unsupported", &manifest);
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    let doc = doc_of(&out);
    assert_eq!(codes_of(diagnostics(&doc)), vec!["E0401"], "the source is read, not the manifest's 2: {doc}");
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    runs_clean("values_unsupported_ok", &manifest, &["check", "test"]);
}

/// §15.3 table, S-827: a budget of 0 and a positive budget (`fast_budget`, `bulk_budget`) are not
/// errors of the manifest's check (a number of bytes, 0 or more). What this version does with the
/// keys is the build of the target (U3), so `check` and `test` go on.
#[test]
fn a_budget_of_zero_and_a_positive_budget_do_not_stop_check_and_test() {
    let mut manifest = String::from("[package]\nname = \"demo\"\nedition = \"2026\"\n");
    manifest.push_str(&target_with(
        "host",
        ("", ""),
        "\n[targets.host.memory]\nbulk = true\nfast_budget = 0\nbulk_budget = 262144\n",
    ));
    runs_clean("values_budgets", &manifest, &["check", "test"]);
}
