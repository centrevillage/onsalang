//! The `platform` of a target of `onsa.toml` and the report of the checks of a target together with the
//! errors of the manifest, through the commands (spec §15.2, §15.3, §18.1, §18.2; R-47, S-161, S-824,
//! S-827; W4-02 U3b).
//!
//! The cases in `tests/spec/manifest/` (`e1104_platform_*`, `e0200_platform_*`, `e1103_bind_*`) check
//! which line carries which code in the build of which target (the marker `#~ E1104 [t]`), which
//! targets need `platform`, which values of `platform` this version cannot tell, the cross
//! `staticlib`, and the form of the keys and the values of `bind`. What a marker cannot check is here:
//!
//! - a `staticlib` without `platform`: `check` and `test` end with exit code 0 and report nothing,
//!   and `build --target t` ends with exit code 2 with one E1104 at the heading of `[targets.t]`
//!   (§15.3 `platform` row, §18.1 "ターゲットに依る検査は、そのターゲットのビルドで行う");
//! - the target that does not need `platform` (`lang = "js"`, `wasm-worklet`) has no E1104 in its build,
//!   only the E0200 of the value this version does not support;
//! - the E0200 of a `platform` this version cannot tell has a note that shows the value `"host"` (S-824:
//!   "note にアーキテクチャと OS の表と `"host"`"); only that the note holds it is checked, the wording is
//!   not fixed;
//! - the E0200 of a cross `staticlib` has a note that shows `kind = "source"` and `lang = "c"` (§15.3
//!   paragraph on the toolchain);
//! - the report together: `build --target t` adds the checks of the target `t` that need no source (the
//!   `platform` of the target) to the errors that every command reports, in one run, and `check` of the
//!   same manifest reports only the errors that every command reports (S-827, §18.1 "`--target` を取る
//!   コマンドは…まとめて報告する"); both end with exit code 2 (§18.2);
//! - the values of `platform` that this version can tell build with exit code 0.
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

/// The text of both streams of a run, one line each.
fn all_lines(out: &Out) -> Vec<&str> {
    out.stdout.lines().chain(out.stderr.lines()).collect()
}

/// Whether `l` starts a diagnostic: `<file>:<line>:<column>: error[<code>]: <message>`
/// (`spec/tools.md` §4).
fn header_of(l: &str) -> Option<(String, String)> {
    let (head, rest) = l.split_once(": error[")?;
    let code = rest.split_once(']')?.0;
    let mut parts = head.rsplitn(3, ':');
    let _column = parts.next()?;
    let line = parts.next()?;
    let file = parts.next()?;
    Some((code.to_string(), format!("{file}:{line}")))
}

/// The codes and the positions (`file:line`) of the diagnostics in the text output, sorted. The
/// diagnostics of one run are looked at as a set; the order of the report is not what is checked.
fn text_diagnostics(out: &Out) -> Vec<(String, String)> {
    let mut found: Vec<(String, String)> = all_lines(out).into_iter().filter_map(header_of).collect();
    found.sort();
    found
}

fn at(code: &str, line: usize) -> (String, String) {
    (code.to_string(), format!("onsa.toml:{line}"))
}

/// The text of the note of the one diagnostic of `code` in the output: the lines from the first line
/// that starts with `note:` to the end of the diagnostic (the next header or the end). The wording of
/// the note is not fixed, so tests look for a word in it.
fn note_of(out: &Out, code: &str) -> String {
    let lines = all_lines(out);
    let start = lines
        .iter()
        .position(|l| header_of(l).is_some_and(|(c, _)| c == code))
        .unwrap_or_else(|| panic!("no {code} in\n{}{}", out.stdout, out.stderr));
    let block: Vec<&str> = lines[start + 1..].iter().copied().take_while(|l| header_of(l).is_none()).collect();
    let note = block
        .iter()
        .position(|l| l.trim_start().starts_with("note:"))
        .unwrap_or_else(|| panic!("the {code} has no `note:` line in\n{}{}", out.stdout, out.stderr));
    block[note..].join("\n")
}

fn build(d: &Dir, target: &str) -> Out {
    run(d.root(), &["build", "--target", target, &d.arg()])
}

/// §15.3 (`platform` row: required for `staticlib`, the build reports the E1104), §18.1, R-47, S-827:
/// a `staticlib` without `platform` does not stop `check` or `test` (exit code 0, no diagnostic, the
/// test of the package runs), and the build of `t` ends with exit code 2 with one E1104 at the heading
/// `[targets.t]`.
#[test]
fn a_staticlib_without_platform_is_an_e1104_of_its_build_only() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"staticlib\"
";
    let d = package("platform_missing", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 0, "check: {}{}", out.stdout, out.stderr);
    assert!(text_diagnostics(&out).is_empty(), "check: {}{}", out.stdout, out.stderr);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 0, "test: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "test: {doc}");
    assert_eq!(tests_of(&doc).len(), 1, "the test of the package ran: {doc}");
    let out = build(&d, "t");
    assert_eq!(out.code, 2, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E1104", line_of(manifest, "[targets.t]"))],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §15.3 (`platform` row: not needed for `lang = "js"` and `wasm-worklet`), R-47, S-154: the build of a
/// target that does not need `platform` reports only the E0200 of the value this version does not
/// support: `lang = "js"` and `kind = "wasm-worklet"`, each at its value, with exit code 2 (§18.2).
#[test]
fn a_target_that_needs_no_platform_has_no_e1104_in_its_build() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.j]
kind = \"source\"
lang = \"js\"

[targets.w]
kind = \"wasm-worklet\"
";
    let d = package("platform_not_needed", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 0, "check: {}{}", out.stdout, out.stderr);
    let out = build(&d, "j");
    assert_eq!(out.code, 2, "build j: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "lang = "))],
        "build j: {}{}",
        out.stdout,
        out.stderr
    );
    let out = build(&d, "w");
    assert_eq!(out.code, 2, "build w: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "wasm-worklet"))],
        "build w: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §15.3 (`platform` row), S-824: a `platform` this version cannot tell (a word that is not a triple, a
/// triple of an architecture it does not know, a triple of an OS it does not know) is one E0200 at the
/// value, whatever the number of fields, with exit code 2, and the note of the E0200 shows `"host"`.
/// `check` of the same manifest ends with exit code 0.
#[test]
fn an_unrecognised_platform_is_one_e0200_with_the_host_in_its_note() {
    for value in ["nonsense", "zz80-unknown-linux-gnu", "x86_64-unknown-zzos-gnu"] {
        let manifest = format!(
            "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"source\"
lang = \"c\"
platform = \"{value}\"
"
        );
        let d = package("platform_unknown", &manifest);
        let out = run(d.root(), &["check", &d.arg()]);
        assert_eq!(out.code, 0, "`{value}` check: {}{}", out.stdout, out.stderr);
        let out = build(&d, "t");
        assert_eq!(out.code, 2, "`{value}` build: {}{}", out.stdout, out.stderr);
        assert_eq!(
            text_diagnostics(&out),
            vec![at("E0200", line_of(&manifest, "platform = "))],
            "`{value}` build: {}{}",
            out.stdout,
            out.stderr
        );
        let note = note_of(&out, "E0200");
        assert!(note.contains("\"host\""), "`{value}`: the note shows `\"host\"`: {note:?}");
    }
}

/// §15.3 (the paragraph on the toolchain: "クロスの `platform` で外部のツールチェーンを要する `kind`…は、この版では
/// そのターゲットのビルドで E0200 になる（note で `kind = "source"` と `lang = "c"` を示す）"), S-161: a
/// `staticlib` for `thumbv7em-none-eabihf` is one E0200 at the value of `kind` in its build (exit code 2),
/// and its note shows the form that builds. `check` of the same manifest ends with exit code 0.
#[test]
fn a_cross_staticlib_is_an_e0200_whose_note_shows_the_source_form() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"staticlib\"
platform = \"thumbv7em-none-eabihf\"
";
    let d = package("platform_cross", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 0, "check: {}{}", out.stdout, out.stderr);
    let out = build(&d, "t");
    assert_eq!(out.code, 2, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "kind = "))],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
    let note = note_of(&out, "E0200");
    for word in ["kind = \"source\"", "lang = \"c\""] {
        assert!(note.contains(word), "the note shows `{word}`: {note:?}");
    }
}

/// §18.1 ("`--target` を取るコマンドは、そのうちソースを読まずに決まる検査（`platform` が要るか、そのプラットフォームを
/// 扱えるか）をマニフェストの検査と同じ回に行い、まとめて報告する"), S-827, R-47: an error that every
/// command reports (`edition = "2025"`, an E1103 on line 3) and a `staticlib` without `platform`: `check`
/// stops on the E1103 alone, and `build --target t` reports it with the E1104 of `[targets.t]` in one run.
/// Both end with exit code 2 (§18.2).
#[test]
fn build_reports_the_error_of_every_command_and_the_missing_platform_together() {
    let manifest = "[package]
name = \"demo\"
edition = \"2025\"

[targets.t]
kind = \"staticlib\"
";
    let d = package("platform_together", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "check: {}{}", out.stdout, out.stderr);
    assert_eq!(text_diagnostics(&out), vec![at("E1103", 3)], "check: {}{}", out.stdout, out.stderr);
    let out = build(&d, "t");
    assert_eq!(out.code, 2, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E1103", 3), at("E1104", line_of(manifest, "[targets.t]"))],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §18.1 (the same sentence), S-824, S-827: the E1103 of the error that every command reports, the E0200
/// of a `platform` this version cannot tell, and the E0200 of the unsupported `kind` of the same target
/// are three reports of one run of `build --target t`; `check` reports the E1103 alone.
#[test]
fn build_reports_the_error_of_every_command_and_the_checks_of_the_target_together() {
    let manifest = "[package]
name = \"demo\"
edition = \"2025\"

[targets.t]
kind = \"exe\"
platform = \"nonsense\"
";
    let d = package("platform_together_e0200", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "check: {}{}", out.stdout, out.stderr);
    assert_eq!(text_diagnostics(&out), vec![at("E1103", 3)], "check: {}{}", out.stdout, out.stderr);
    let out = build(&d, "t");
    assert_eq!(out.code, 2, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "kind = ")), at("E0200", line_of(manifest, "platform = ")), at("E1103", 3)],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §15.3 (`bind` row), §15.2, §18.1, S-824, S-827: a bad key of `bind` (an E1103 at the key, reported by
/// every command, so `check` ends with exit code 2) and the entry of the table (an E0200 at the heading
/// of `[targets.t.bind]`, reported by the build of `t`) are two reports of one run of `build --target t`.
#[test]
fn build_reports_the_bad_bind_key_and_the_bind_with_an_entry_together() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.t]
kind = \"source\"
lang = \"c\"
platform = \"host\"

[targets.t.bind]
\"Audio.device\" = \"daisy_hal.audio\"
";
    let d = package("platform_bind_together", manifest);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 2, "check: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E1103", line_of(manifest, "\"Audio.device\""))],
        "check: {}{}",
        out.stdout,
        out.stderr
    );
    let out = build(&d, "t");
    assert_eq!(out.code, 2, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", line_of(manifest, "[targets.t.bind]")), at("E1103", line_of(manifest, "\"Audio.device\""))],
        "build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §15.3 (`platform` row, the paragraph on the toolchain), S-824: the values of `platform` this version
/// can tell (`"x86_64-unknown-linux-gnu"` and `"thumbv7em-none-eabihf"` beside `"host"`) build a
/// `kind = "source"` target with `lang = "c"` with exit code 0 and no diagnostic. (The triple of the
/// host itself is not written: whether it is the host depends on the machine.)
#[test]
fn the_platforms_this_version_can_tell_build_a_c_source() {
    let manifest = "[package]
name = \"demo\"
edition = \"2026\"

[targets.a]
kind = \"source\"
lang = \"c\"
platform = \"host\"

[targets.b]
kind = \"source\"
lang = \"c\"
platform = \"x86_64-unknown-linux-gnu\"

[targets.c]
kind = \"source\"
lang = \"c\"
platform = \"thumbv7em-none-eabihf\"
";
    let d = package("platform_builds", manifest);
    for target in ["a", "b", "c"] {
        let out = build(&d, target);
        assert_eq!(out.code, 0, "build {target}: {}{}", out.stdout, out.stderr);
        assert!(text_diagnostics(&out).is_empty(), "build {target}: {}{}", out.stdout, out.stderr);
    }
}
