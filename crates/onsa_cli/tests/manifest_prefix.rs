//! The `prefix` of `[export]` in `onsa.toml`: it is needed by the build of a target when the package has an
//! `@export` item, and the E1104 for it comes after the check of the source, through the commands (spec
//! §14.2, §15.3, §18.1, §18.2; R-121, S-95, S-639, S-832; W4-02 U3c).
//!
//! The cases in `tests/spec/manifest/` (`e1104_prefix_*`) check which line carries the E1104 in the build of
//! which target (the marker `#~ E1104 [t]`), which package names give the candidate `prefix = "<package>_"`
//! and which give none, that the candidate is clean when it is applied, and the forms that need no `prefix`.
//! What a marker cannot check is here:
//!
//! - a package with an `@export` item and no `prefix`: `check` and `test` end with exit code 0 and report
//!   nothing, and `build --target t` ends with exit code 2 with one E1104 at the heading of `[export]` (at the
//!   top of `onsa.toml` when there is no `[export]`) (§14.2, §15.3 `[export]` row, §18.1);
//! - the check of the source comes first: a type error in the source ends `build --target t` with exit code
//!   1 and that error alone, with no E1104 (§18.1 "`build` がソースの検査を通った後に調べる（検査の誤りがあれば、
//!   それだけを出す）", S-832); a source can have a check error only where `check` also reports it, so a case
//!   cannot hold both markers;
//! - the errors of the manifest come first as well: an error that every command reports and an error in the
//!   value of the target end the build with exit code 2 before the source is read, so the E1104 (which needs the
//!   source to tell whether `prefix` is needed) is not in the report (§18.1 "ソースを読む前に…止まる");
//! - with `prefix = "demo_"` the build passes, and the names that the build writes start with `demo_`, not with
//!   the `onsa_` that was the default before (§14.2 "既定は無い", "C の名前は `prefix` と名前の最後の要素をつなげたもの");
//! - a package with no `@export` item and no `prefix` builds with exit code 0 (§14.2 "`@export` の項目が無い
//!   パッケージでは要らず").
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use test_support::*;

/// A source with an `@export` function and a test, so that `check`, `test` and `build` all have something
/// to read.
const EXPORTING: &str = "@export
pub fn f() -> I32 { 1 }

test \"f is one\" {
  assert f() == 1
}
";

/// A source with no `@export` item (a `pub` function and a `pub` flow are not exported without the attribute).
const NOT_EXPORTING: &str = "pub fn f() -> I32 { 1 }

pub flow gain(x: F32 at sample) -> F32 at sample { x * 0.5 }

test \"f is one\" {
  assert f() == 1
}
";

/// An `@export` function with a type error on line 2.
const EXPORTING_WITH_TYPE_ERROR: &str = "@export
pub fn f() -> I32 { true }
";

fn package(tag: &str, manifest: &str, source: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", manifest);
    d.write("m.onsa", source);
    d
}

/// A manifest of the package `name` with one target `t` that builds C, and `export` written between the
/// `[package]` table and the target (an empty string for no `[export]` table).
fn manifest(name: &str, edition: &str, export: &str, target_extra: &str) -> String {
    format!(
        "[package]
name = \"{name}\"
edition = \"{edition}\"

{export}[targets.t]
kind = \"source\"
lang = \"c\"
platform = \"host\"
{target_extra}"
    )
}

/// The line (from 1) of the first line of the manifest that holds `needle`.
fn line_of(manifest: &str, needle: &str) -> usize {
    manifest
        .lines()
        .position(|l| l.contains(needle))
        .unwrap_or_else(|| panic!("no line holds {needle:?} in\n{manifest}"))
        + 1
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
    let mut found: Vec<(String, String)> = out.stdout.lines().chain(out.stderr.lines()).filter_map(header_of).collect();
    found.sort();
    found
}

fn at(code: &str, file: &str, line: usize) -> (String, String) {
    (code.to_string(), format!("{file}:{line}"))
}

fn build(d: &Dir) -> Out {
    run(d.root(), &["build", "--target", "t", &d.arg()])
}

/// §14.2 ("`prefix` は、`@export` の項目を出すターゲットのビルドで必須で、既定は無い"), §15.3 (`[export]` row),
/// §18.1 (the E1104 is a check of the build; `check` and `test` are not stopped), S-639, S-832: with an `@export`
/// item and no `prefix`, `check` and `test` end with exit code 0 (the test of the package runs) and
/// `build --target t` ends with exit code 2 with one E1104, at the heading `[export]` or, with no `[export]`,
/// at the top of the manifest.
#[test]
fn a_missing_prefix_is_an_e1104_of_the_build_only() {
    for (tag, export) in [("heading", "[export]\n\n"), ("absent", "")] {
        let manifest = manifest("demo", "2026", export, "");
        let d = package(&format!("prefix_missing_{tag}"), &manifest, EXPORTING);
        let out = run(d.root(), &["check", &d.arg()]);
        assert_eq!(out.code, 0, "{tag}: check: {}{}", out.stdout, out.stderr);
        assert!(text_diagnostics(&out).is_empty(), "{tag}: check: {}{}", out.stdout, out.stderr);
        let (out, doc) = test_json(d.root(), &[&d.arg()]);
        assert_eq!(out.code, 0, "{tag}: test: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{tag}: test: {doc}");
        assert_eq!(tests_of(&doc).len(), 1, "{tag}: the test of the package ran: {doc}");
        let out = build(&d);
        let line = if export.is_empty() { 1 } else { line_of(&manifest, "[export]") };
        assert_eq!(out.code, 2, "{tag}: build: {}{}", out.stdout, out.stderr);
        assert_eq!(
            text_diagnostics(&out),
            vec![at("E1104", "onsa.toml", line)],
            "{tag}: build: {}{}",
            out.stdout,
            out.stderr
        );
    }
}

/// §18.1 ("`prefix` が要るかはソースを読まないと決まらないので、`build` がソースの検査を通った後に調べる（検査の誤りが
/// あれば、それだけを出す）"), S-832: the same package with a type error in the source (E0401 on line 2 of
/// `m.onsa`): `check` and `build --target t` both end with exit code 1 with that error alone, and the build has
/// no E1104.
#[test]
fn a_check_error_in_the_source_comes_before_the_missing_prefix() {
    let manifest = manifest("demo", "2026", "[export]\n\n", "");
    let d = package("prefix_source_error", &manifest, EXPORTING_WITH_TYPE_ERROR);
    let out = run(d.root(), &["check", &d.arg()]);
    assert_eq!(out.code, 1, "check: {}{}", out.stdout, out.stderr);
    assert_eq!(text_diagnostics(&out), vec![at("E0401", "m.onsa", 2)], "check: {}{}", out.stdout, out.stderr);
    let out = build(&d);
    assert_eq!(out.code, 1, "build: {}{}", out.stdout, out.stderr);
    assert_eq!(text_diagnostics(&out), vec![at("E0401", "m.onsa", 2)], "build: {}{}", out.stdout, out.stderr);
}

/// §18.1 (the same sentence, and "マニフェストを読む全てのコマンド…は、ソースを読む前にマニフェスト全体を検査し、誤りが
/// あれば終了コード 2 で止まる"), S-832: an error that every command reports (`edition = "2025"`, an E1103 on
/// line 3), and an error of the value of the target (an E0200 for a `platform` this version cannot tell), each
/// with a missing `prefix` and an `@export` item: `build --target t` ends with exit code 2 with that error
/// alone, with no E1104 (the source is not read, so whether `prefix` is needed is not known).
#[test]
fn an_error_of_the_manifest_comes_before_the_missing_prefix() {
    let wrong_edition = manifest("demo", "2025", "[export]\n\n", "");
    let d = package("prefix_manifest_error", &wrong_edition, EXPORTING);
    let out = build(&d);
    assert_eq!(out.code, 2, "edition: build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E1103", "onsa.toml", 3)],
        "edition: build: {}{}",
        out.stdout,
        out.stderr
    );
    let wrong_platform = manifest("demo", "2026", "[export]\n\n", "").replace("\"host\"", "\"nonsense\"");
    let d = package("prefix_target_error", &wrong_platform, EXPORTING);
    let out = build(&d);
    assert_eq!(out.code, 2, "platform: build: {}{}", out.stdout, out.stderr);
    assert_eq!(
        text_diagnostics(&out),
        vec![at("E0200", "onsa.toml", line_of(&wrong_platform, "platform = "))],
        "platform: build: {}{}",
        out.stdout,
        out.stderr
    );
}

/// §14.2 ("C の名前は `prefix` と名前の最後の要素をつなげたもの", "ヘッダ `<prefix><package>.h`"), §15.3 (`[export]`
/// row), R-121 (1), S-95: with `prefix = "demo_"` in the package `synth` the build ends with exit code 0 and
/// no diagnostic, the package header is `demo_synth.h` and declares `demo_f`, the flow header declares
/// `demo_gain_process`, and the default `onsa_` is not used for them (there is no `onsa_synth.h`, and no
/// `onsa_f` or `onsa_gain`; the runtime's own names start with `onsa_` and are not these).
#[test]
fn with_a_prefix_the_build_passes_and_the_names_start_with_it() {
    let source = "@export
pub fn f() -> I32 { 1 }

@export
pub flow gain(x: F32 at sample) -> F32 at sample { x * 0.5 }
";
    let manifest = manifest("synth", "2026", "[export]\nprefix = \"demo_\"\n\n", "");
    let d = package("prefix_written", &manifest, source);
    let out = build(&d);
    assert_eq!(out.code, 0, "build: {}{}", out.stdout, out.stderr);
    assert!(text_diagnostics(&out).is_empty(), "build: {}{}", out.stdout, out.stderr);
    let target = d.root().join("target").join("t");
    let read = |name: &str| {
        std::fs::read_to_string(target.join(name)).unwrap_or_else(|e| panic!("`{name}` is not in target/t: {e}"))
    };
    let package_header = read("demo_synth.h");
    assert!(package_header.contains("demo_f("), "demo_f is declared in demo_synth.h:\n{package_header}");
    assert!(!target.join("onsa_synth.h").exists(), "the default `onsa_` names the package header");
    let all: String = std::fs::read_dir(&target)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "h" || e == "c"))
        .map(|p| std::fs::read_to_string(p).unwrap())
        .collect();
    assert!(all.contains("demo_gain_process("), "demo_gain_process is declared:\n{all}");
    for default_name in ["onsa_f(", "onsa_gain"] {
        assert!(!all.contains(default_name), "`{default_name}` (the default prefix) is in the generated files");
    }
}

/// §14.2 ("生成するファイルの名前は `<prefix><package>` を幹にする: ヘッダ `<prefix><package>.h`、C のソース
/// `<prefix><package>.c`"), S-95 (4): the C source of the package `synth` with `prefix = "demo_"` is
/// `demo_synth.c`.
#[test]
#[ignore = "W10-02: the C source is written as onsa_<package>.c whatever the prefix (§14.2 names it <prefix><package>.c)"]
fn the_c_source_is_named_after_the_prefix() {
    let manifest = manifest("synth", "2026", "[export]\nprefix = \"demo_\"\n\n", "");
    let d = package("prefix_c_source_name", &manifest, EXPORTING);
    let out = build(&d);
    assert_eq!(out.code, 0, "build: {}{}", out.stdout, out.stderr);
    let target = d.root().join("target").join("t");
    assert!(target.join("demo_synth.c").exists(), "demo_synth.c is not in target/t");
    assert!(!target.join("onsa_synth.c").exists(), "onsa_synth.c is in target/t");
}

/// §14.2 ("`@export` の項目が無いパッケージでは要らず"), §15.3 (`[export]` row), S-639 (q1): a package with
/// no `@export` item builds with exit code 0 and no diagnostic without `prefix`: with no `[export]` table, and
/// with an empty `[export]` heading. (The names of the files it writes are not fixed, since there is no
/// prefix to put in front of the package name.)
#[test]
fn a_package_without_export_items_builds_without_a_prefix() {
    for (tag, export) in [("absent", ""), ("heading", "[export]\n\n")] {
        let manifest = manifest("demo", "2026", export, "");
        let d = package(&format!("prefix_not_needed_{tag}"), &manifest, NOT_EXPORTING);
        let out = build(&d);
        assert_eq!(out.code, 0, "{tag}: build: {}{}", out.stdout, out.stderr);
        assert!(text_diagnostics(&out).is_empty(), "{tag}: build: {}{}", out.stdout, out.stderr);
    }
}
