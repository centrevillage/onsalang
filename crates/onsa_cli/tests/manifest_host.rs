//! The host of the `platform` of a target of `onsa.toml`: which triple is the host, and what the E0200 of
//! a cross `staticlib` shows (spec §15.3 paragraph on the toolchain, §18.1; S-837, S-161; W4-02 U3d).
//!
//! The cases in `tests/spec/manifest/` (`e0200_platform_cross_staticlib_*`) check the line of the E0200 of
//! a cross `staticlib` for the triples that are the host on no machine. What a marker cannot check is here,
//! because it depends on the machine the compiler runs on:
//!
//! - the triple that `"host"` names is the host: a `kind = "staticlib"` target whose `platform` is that
//!   triple written out builds with exit code 0 and makes the archive (§15.3: "ホストの `platform` は、
//!   `"host"` と、`"host"` が指すトリプル…に字で一致するトリプルである"). The triple is read from the
//!   build of a `platform = "host"` target (`onsa_build.json`, the `platform` key);
//! - the E0200 of a cross `staticlib` has a note that shows the triple of the host (§15.3: "クロスの E0200 の
//!   note が示す"), for each of the three kinds of cross: the other OS on the same architecture
//!   (`aarch64-apple-ios`), the other spelling of one machine (`arm64-apple-darwin`) and the form with a
//!   versioned OS word (`aarch64-apple-darwin25.4.0`). Only that the note holds the triple is checked, the
//!   wording is not fixed.
//!
//! The archive of the host uses `cc` and `ar` of the PATH (§15.3). A host that builds no archive (an msvc
//! host, S-840, not decided) is not checked for the archive.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use std::path::Path;

use test_support::*;

const SOURCE: &str = "@export
pub fn f() -> I32 { 1 }
";

/// The manifest with the host target `a` (`kind = "source"`, `lang = "c"`, `platform = "host"`, which tells
/// the triple of the host), and `extra` after it.
fn manifest(extra: &str) -> String {
    format!(
        "[package]
name = \"demo\"
edition = \"2026\"

[export]
prefix = \"t_\"

[targets.a]
kind = \"source\"
lang = \"c\"
platform = \"host\"
{extra}"
    )
}

/// The `onsa_build.json` of the build of `target` in the default output directory.
fn build_report(d: &Dir, target: &str) -> serde_json::Value {
    let p = d.root().join("target").join(target).join("onsa_build.json");
    let text = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("no {}: {e}", p.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{} is not JSON ({e}): {text}", p.display()))
}

fn build(d: &Dir, target: &str) -> Out {
    run(d.root(), &["build", "--target", target, &d.arg()])
}

/// The triple of the host: the `platform` of the build of the `"host"` target `a` of `d` (the manifest of
/// `d` has the target `a` of `manifest`).
fn host_triple(d: &Dir) -> String {
    let out = build(d, "a");
    assert_eq!(out.code, 0, "build a: {}{}", out.stdout, out.stderr);
    let triple = str_of(&build_report(d, "a"), "platform").to_string();
    assert!(triple.contains('-'), "the host `platform` of the report is a triple: {triple:?}");
    triple
}

/// The diagnostics of the text output: the headers `file:line:column: error[CODE]` as `(code, file:line)`.
fn headers(out: &Out) -> Vec<(String, String)> {
    out.stdout
        .lines()
        .chain(out.stderr.lines())
        .filter_map(|l| {
            let (head, rest) = l.split_once(": error[")?;
            let code = rest.split_once(']')?.0.to_string();
            let mut parts = head.rsplitn(3, ':');
            let _column = parts.next()?;
            let line = parts.next()?;
            let file = parts.next()?;
            Some((code, format!("{file}:{line}")))
        })
        .collect()
}

/// The lines of the note of the one diagnostic: from the first line that starts with `note:` to the end.
fn note_lines(out: &Out) -> String {
    let all: Vec<&str> = out.stdout.lines().chain(out.stderr.lines()).collect();
    let start = all
        .iter()
        .position(|l| l.trim_start().starts_with("note:"))
        .unwrap_or_else(|| panic!("no `note:` line in\n{}{}", out.stdout, out.stderr));
    all[start..].join("\n")
}

fn line_of(manifest: &str, needle: &str) -> usize {
    manifest
        .lines()
        .position(|l| l.contains(needle))
        .unwrap_or_else(|| panic!("no line holds {needle:?} in\n{manifest}"))
        + 1
}

/// §15.3 ("ホストの `platform` は、`"host"` と、`"host"` が指すトリプルに字で一致するトリプルである"; "ホストの
/// `platform` では PATH の `cc` と `ar` を使う"), S-837 (1): the triple that `"host"` names, written out as
/// the `platform` of a `staticlib`, is the host. The build ends with exit code 0, reports no diagnostic,
/// names the same triple as its `platform`, and makes the archive that `onsa_build.json` names.
#[test]
fn the_triple_that_host_names_builds_a_staticlib_as_the_host() {
    let d = Dir::bare("host_triple_staticlib");
    d.write("m.onsa", SOURCE);
    d.write("onsa.toml", &manifest(""));
    let triple = host_triple(&d);
    d.write("onsa.toml", &manifest(&format!("\n[targets.s]\nkind = \"staticlib\"\nplatform = \"{triple}\"\n")));
    let out = build(&d, "s");
    assert_eq!(out.code, 0, "build s (platform = \"{triple}\"): {}{}", out.stdout, out.stderr);
    assert!(headers(&out).is_empty(), "build s: {}{}", out.stdout, out.stderr);
    let report = build_report(&d, "s");
    assert_eq!(str_of(&report, "platform"), triple, "{report}");
    assert_eq!(str_of(&report, "kind"), "staticlib", "{report}");
    if !triple.contains("msvc") {
        let archive = str_of(&report, "archive");
        assert!(archive.ends_with(".a"), "the archive of the report: {report}");
        assert!(Path::new(&d.root().join("target/s").join(archive)).is_file(), "no {archive} in target/s: {report}");
    }
}

/// §15.3 ("同じ機械を別の綴りで指すもの（`arm64-apple-darwin`）と、同じ機械の上の別の OS（`aarch64-apple-ios`）は
/// クロスである"; "クロスの E0200 の note が示す"), S-837 (1)·(B′), S-161: a `staticlib` whose `platform` is
/// another OS on the same architecture, another spelling of one machine, or the `-dumpmachine` form with a
/// versioned OS word, is one E0200 at the value of `kind` in its build (exit code 2), and the note shows the
/// triple of the host (the triple that the build of the `"host"` target reports).
#[test]
fn the_e0200_of_a_cross_staticlib_shows_the_triple_of_the_host_in_its_note() {
    let d = Dir::bare("cross_note");
    d.write("m.onsa", SOURCE);
    d.write("onsa.toml", &manifest(""));
    let host = host_triple(&d);
    for cross in ["aarch64-apple-ios", "arm64-apple-darwin", "aarch64-apple-darwin25.4.0"] {
        assert_ne!(cross, host, "the machine's triple is one of the triples written as cross");
        let extra = format!("\n[targets.x]\nkind = \"staticlib\"\nplatform = \"{cross}\"\n");
        d.write("onsa.toml", &manifest(&extra));
        let out = build(&d, "x");
        assert_eq!(out.code, 2, "`{cross}` build: {}{}", out.stdout, out.stderr);
        let at = format!("onsa.toml:{}", line_of(&manifest(&extra), "kind = \"staticlib\""));
        assert_eq!(headers(&out), vec![("E0200".to_string(), at)], "`{cross}` build: {}{}", out.stdout, out.stderr);
        let note = note_lines(&out);
        assert!(note.contains(&host), "`{cross}`: the note shows the host triple `{host}`: {note:?}");
    }
}
