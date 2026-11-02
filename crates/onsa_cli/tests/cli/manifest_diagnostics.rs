//! The diagnostics of `onsa.toml` through the commands: the closed table of §15.3 (E1101, E1102,
//! the name of a target in E1103), that they are reported before any source is read, and the
//! exit code and the `--json` document (spec §15.3, §18.1, §18.2; S-99, S-166, S-597, S-639, S-828;
//! R-130; W4-02 U2a2).
//!
//! The cases in `tests/spec/manifest/` check which line carries which code (the marker `#~`).
//! What a marker cannot check is here, because a case with a marker may not have a source error:
//!
//! - a manifest with a diagnostic stops every command that reads the manifest before the source is
//!   read (§18.1), so the source's own error (the package here has an E0401) is never reported,
//!   and the exit code is 2 (§18.2), whichever way the package is named: the directory, a `.onsa`
//!   file of it (§15.1), and for `test`, `interface`, `graph` and `build --target`;
//! - `check --json` prints the document with the diagnostic: `span.file` is `onsa.toml` (§18.1);
//!   an E1102 has no fix candidate (S-597), and its note lists the keys the table can have (the
//!   names of the tables at the top, §18.1). The order of the names in the note is not fixed;
//! - an E1101 (not TOML) and the E1103 of a target's name stop the command too.
//!
//! `onsa test --json` (the `tests` array is empty) and the document of `check --json` for one
//! unknown key are in `test_json_document.rs` and `check_json_document.rs`.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

use crate::test_support;

use serde_json::Value;
use test_support::*;

/// A manifest with an unknown key in `[package]` (line 4) and an unknown top-level table
/// (line 6), and a target `host` that the commands with `--target` can name.
const MANIFEST: &str = "[package]
name = \"demo\"
edition = \"2026\"
colour = \"red\"

[bogus]
x = 1

[targets.host]
kind = \"source\"
lang = \"c\"
platform = \"host\"
fp = \"strict\"
provides = []
panic = \"trap\"
panic_messages = true
main_frame = \"stack\"
";

/// A source with a type error (E0401) and a flow, so that every command has something to read.
const SOURCE: &str = "pub fn f() -> I32 {
  true
}

pub flow voice(x: F32 at sample) -> F32 at sample {
  x
}
";

fn package(tag: &str, manifest: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", SOURCE);
    d
}

/// The codes and the positions (`file:line`) of the diagnostics in the text output, in order. A
/// diagnostic starts a line `<file>:<line>:<column>: error[<code>]: <message>` (`spec/tools.md` §4).
fn text_diagnostics(out: &Out) -> Vec<(String, String)> {
    out.stdout
        .lines()
        .filter_map(|l| {
            let (head, rest) = l.split_once(": error[")?;
            let code = rest.split_once(']')?.0;
            let mut parts = head.rsplitn(3, ':');
            let _column = parts.next()?;
            let line = parts.next()?;
            let file = parts.next()?;
            Some((code.to_string(), format!("{file}:{line}")))
        })
        .collect()
}

fn codes_of(ds: &[Value]) -> Vec<&str> {
    ds.iter().map(|d| str_of(d, "code")).collect()
}

/// §18.1: the unit is the manifest, every error in it is reported, and the source is not read: the
/// two E1102 are all there is, the E0401 of the source is not. §18.2: the exit code is 2.
#[test]
fn check_reports_the_unknown_key_and_table_and_stops_before_the_source() {
    let d = package("check_text", MANIFEST);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![("E1102".to_string(), "onsa.toml:4".to_string()), ("E1102".to_string(), "onsa.toml:6".to_string())],
        "{}",
        out.stdout
    );
}

/// §15.1, §18.1: a `.onsa` file of the package names the package; the manifest is read all the
/// same (every command that reads the manifest checks the whole of it before the source), so the
/// same two E1102 are reported and the source's E0401 is not.
#[test]
fn check_of_a_source_file_of_the_package_reports_the_manifest_too() {
    let d = package("check_file", MANIFEST);
    let file = format!("{}/m.onsa", d.arg());
    let out = run(d.root(), &["check", &file]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let codes: Vec<String> = text_diagnostics(&out).into_iter().map(|(c, _)| c).collect();
    assert_eq!(codes, vec!["E1102", "E1102"], "{}", out.stdout);
}

/// §18.1: the document of `check --json` has the E1102 with `span.file` = `onsa.toml`, no fix
/// candidate (S-597) and a note that lists the keys of the table (the names of the tables at the
/// top). The order of the listing is not fixed, so the names are looked for.
#[test]
fn check_json_has_the_e1102_in_onsa_toml_with_the_keys_of_the_table_in_a_note() {
    let d = package("check_json", MANIFEST);
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1102", "E1102"], "{doc}");
    for d in ds {
        assert_eq!(str_of(&d["span"], "file"), "onsa.toml", "{d}");
        assert_eq!(d["fixes"], Value::Array(vec![]), "an E1102 has no fix candidate (S-597): {d}");
    }
    let notes = |d: &Value| -> String {
        array_of(d, "notes").iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
    };
    // The key `colour` of `[package]`: line 4, and the keys of `[package]` in the note.
    assert_eq!(int_of(&ds[0]["span"], "line"), 4, "{doc}");
    let n = notes(&ds[0]);
    assert!(n.contains("name") && n.contains("edition"), "the keys of [package] in the note: {n:?}");
    // The table `[bogus]`: line 6, and the tables that can be at the top in the note.
    assert_eq!(int_of(&ds[1]["span"], "line"), 6, "{doc}");
    let n = notes(&ds[1]);
    for t in ["package", "dependencies", "export", "targets", "plugin"] {
        assert!(n.contains(t), "the table `{t}` in the note of the unknown table: {n:?}");
    }
}

/// §18.1, §18.2: the other commands that read the manifest stop at the same place with exit code
/// 2 and report the manifest's E1102 only: `test`, `interface`, `graph` and `build --target`.
#[test]
fn test_interface_graph_and_build_stop_on_the_manifest_with_exit_code_2() {
    let d = package("others", MANIFEST);
    let dir = d.arg();
    let commands: [&[&str]; 4] =
        [&["test", &dir], &["interface", &dir], &["graph", "voice", &dir], &["build", "--target", "host", &dir]];
    for args in commands {
        let out = run(d.root(), args);
        assert_eq!(out.code, 2, "onsa {args:?}: {}{}", out.stdout, out.stderr);
        let codes: Vec<String> = text_diagnostics(&out).into_iter().map(|(c, _)| c).collect();
        assert_eq!(codes, vec!["E1102", "E1102"], "onsa {args:?}: {}{}", out.stdout, out.stderr);
    }
}

/// §18.1: a manifest that is not TOML is an E1101, and the reading stops there: the unknown key
/// before the error is not reported (it was not read as a key). The source's error is not
/// reported either. The exit code is 2 and `--json` prints the document.
#[test]
fn a_manifest_that_is_not_toml_is_one_e1101_and_stops_the_command() {
    let d = package("e1101", "[package]\nname = \"demo\"\nedition = \"2026\"\ncolour = \"red\"\nx = = 1\n");
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    let ds = diagnostics(&doc);
    assert_eq!(codes_of(ds), vec!["E1101"], "{doc}");
    assert_eq!(str_of(&ds[0]["span"], "file"), "onsa.toml", "{doc}");
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
}

/// §15.3, §18.1, S-828: the name of a target that is not a `snake_case` identifier is an E1103 at
/// the heading, from the manifest's check, so `check` reports it and stops before the source; a
/// name that is one (`daisy_seed`) is not reported. The exit code is 2.
#[test]
fn the_name_of_a_target_is_checked_by_check_and_stops_before_the_source() {
    let mut manifest = String::from("[package]\nname = \"demo\"\nedition = \"2026\"\n\n");
    for (i, name) in ["\"../../esc\"", "Host", "daisy_seed"].iter().enumerate() {
        if i > 0 {
            manifest.push('\n');
        }
        manifest.push_str(&format!("[targets.{name}]\n"));
        manifest.push_str(
            "kind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nfp = \"strict\"\nprovides = []\n\
             panic = \"trap\"\npanic_messages = true\nmain_frame = \"stack\"\n",
        );
    }
    let d = package("e1103", &manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    // The headings are on lines 5 and 15 (`daisy_seed` at 25 is a good name).
    assert_eq!(
        text_diagnostics(&out),
        vec![("E1103".to_string(), "onsa.toml:5".to_string()), ("E1103".to_string(), "onsa.toml:15".to_string())],
        "{}",
        out.stdout
    );
}
