//! The model of the package seen from the command line: `std` as an implicit dependency, the
//! version of the embedded std that `onsa --version` shows, the dependencies other than std that
//! this version does not take, and the modules of std that are the files under `std/` (spec §15.1,
//! §15.3, §19.1; S-83, S-160, R-88, R-80 (4); W4-01).
//!
//! What the spec fixes, and so what is checked here:
//! - `std` is an implicit dependency of every package, so it needs no entry in `[dependencies]`
//!   (a single file with no manifest too), and an empty `[dependencies]` table is the same (§15.3);
//! - the embedded std has a version, and `onsa --version` shows it (§15.3, S-160). The spec does
//!   not fix the shape of the output, so the checks read only a line that names `std` and carries
//!   a `major.minor.patch`. `std = "x.y.z"` with that version is a pin that matches, so the
//!   package checks with no diagnostic (a version that does not match is E1103, W4-02, not here);
//! - a dependency other than std is a feature of the second phase (§19.1): the manifest check
//!   reports E0200 at the entry, in `onsa.toml`, for every command, and the exit code is 2
//!   because the diagnostic points into `onsa.toml` (§15.3, §18.1, §18.2). A package name that is
//!   not declared is just a name that is not found (E0302, exit code 1);
//! - the modules of std have the paths of the files under `std/` by the rule of §15.1: the file
//!   `std/dsp/test.onsa` is the module `std.dsp.test`. Every file of `std/` that has a `pub` item
//!   is reached by `use std.<path>.{item}` with no diagnostic.
//!
//! Not written here: the version check and E1103 (W4-02), the head of a `use` and the names that
//! are visible (W4-03), the input of a package and its names (W4-14), the non-std dependencies
//! themselves (the second phase: source, version resolution, `onsa.lock`).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

mod test_support;

use std::path::{Path, PathBuf};

use test_support::*;

const MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n";

const USES_STD: &str = "use std.math.{sqrt}\n\npub fn root(x: F32) -> F32 {\n  sqrt(x)\n}\n";

/// A scratch package: `onsa.toml` is `MANIFEST` and the text after it, and `m.onsa` is `USES_STD`.
fn package(tag: &str, after_manifest: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", &format!("{MANIFEST}{after_manifest}"));
    d.write("m.onsa", USES_STD);
    d
}

fn check_json(d: &Dir) -> (Out, serde_json::Value) {
    let out = run(d.root(), &["check", "--json", &d.arg()]);
    let doc = doc_of(&out);
    (out, doc)
}

/// The first `major.minor.patch` in `text`: a run of digits and dots that is three numbers
/// between two dots.
fn first_version(text: &str) -> Option<String> {
    let mut run = String::new();
    for c in text.chars().chain(std::iter::once(' ')) {
        if c.is_ascii_digit() || c == '.' {
            run.push(c);
            continue;
        }
        let word = run.trim_matches('.');
        let parts: Vec<&str> = word.split('.').collect();
        if parts.len() == 3 && parts.iter().all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit())) {
            return Some(word.to_string());
        }
        run.clear();
    }
    None
}

/// The version of std that `onsa --version` shows. The spec fixes that the version is shown,
/// not the shape of the output, so this reads the first `major.minor.patch` after the word `std`
/// on a line that has it (a line such as `std 1.2.3` or `onsa 0.1.0 (std 1.2.3)`).
fn shown_std_version() -> String {
    let d = Dir::bare("version_cwd");
    let out = run(d.root(), &["--version"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let all = format!("{}{}", out.stdout, out.stderr);
    let mut versions = Vec::new();
    for line in all.lines() {
        let at = line.to_ascii_lowercase().find("std");
        if let Some(v) = at.and_then(|i| first_version(&line[i + 3..])) {
            versions.push(v);
        }
    }
    assert!(!versions.is_empty(), "`onsa --version` shows no line with `std` and a version after it: {all:?}");
    assert!(versions.iter().all(|v| *v == versions[0]), "different std versions: {versions:?}");
    versions[0].clone()
}

// ---------------------------------------------------------------- the version of the embedded std

/// Spec §15.3 (S-160): the version of the embedded std is shown by `onsa --version`.
#[test]
fn the_version_flag_shows_the_version_of_the_embedded_std() {
    let v = shown_std_version();
    // The same version at every run, from any working directory.
    let elsewhere = Dir::bare("version_elsewhere");
    let again = run(elsewhere.root(), &["--version"]);
    assert_eq!(again.code, 0);
    let again_text = format!("{}{}", again.stdout, again.stderr);
    assert!(again_text.contains(&v), "{again_text:?}");
}

/// Spec §15.3: `std = "x.y.z"` pins the std, and the embedded one is the version that
/// `onsa --version` shows, so that pin is accepted by every command that reads the package.
#[test]
fn a_pin_of_the_shown_std_version_is_accepted() {
    let v = shown_std_version();
    let d = package("pin_shown", &format!("\n[dependencies]\nstd = \"{v}\"\n"));
    let (out, doc) = check_json(&d);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
    let out = run(d.root(), &["test", &d.arg()]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
}

// ---------------------------------------------------------------- std as an implicit dependency

/// Spec §15.3: std needs no entry in `[dependencies]`, and an empty table is the same.
#[test]
fn std_is_used_with_no_entry_for_it() {
    for (tag, after) in [("no_table", ""), ("empty_table", "\n[dependencies]\n")] {
        let d = package(tag, after);
        let (out, doc) = check_json(&d);
        assert_eq!(out.code, 0, "{tag}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{tag}: {doc}");
        let out = run(d.root(), &["interface", &d.arg()]);
        assert_eq!(out.code, 0, "{tag}: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains("root"), "{tag}: {}", out.stdout);
    }
}

/// Spec §15.3: a single file with no manifest has std too, whether the file is named by a path or
/// found from the working directory.
#[test]
fn a_single_file_with_no_manifest_uses_std() {
    let d = Dir::bare("single");
    d.write("m.onsa", USES_STD);
    let out = run(d.root(), &["check", "--json", "m.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty());
}

/// Spec §15.1: a package name that is not declared is not found: it is not std, and it is not a
/// dependency of this package. The name is not found by a search over all the packages that the
/// compiler knows (R-88), so no entry in the manifest and no `std` entry make it visible.
#[test]
fn a_package_that_is_not_declared_is_not_found() {
    for (tag, after) in [("undeclared_no_table", ""), ("undeclared_empty_table", "\n[dependencies]\n")] {
        let d = package(tag, after);
        d.write("m.onsa", "use fx.{thing}\nuse std.math.{sqrt}\n\npub fn root(x: F32) -> F32 {\n  sqrt(x)\n}\n");
        let (out, doc) = check_json(&d);
        assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
        let ds = diagnostics(&doc);
        assert_eq!(ds.len(), 1, "{tag}: {doc}");
        assert_eq!(str_of(&ds[0], "code"), "E0302", "{tag}: {doc}");
        assert_eq!(span_of(&ds[0]["span"]).file, "m.onsa", "{tag}: {doc}");
        assert_eq!(span_of(&ds[0]["span"]).line, 1, "{tag}: {doc}");
    }
}

// ---------------------------------------------------------------- dependencies other than std

const FX: &str = "\n[dependencies]\nfx = \"1.0.0\"\n";

/// Spec §15.3, §18.1: a dependency other than std is E0200 in the manifest check, which every
/// command runs, at the entry (line 6 of the manifest `MANIFEST` + `FX`). The diagnostic points
/// into `onsa.toml`, so the exit code is 2 (§18.2) and `--json` still prints the document.
#[test]
#[ignore = "W4-02"]
fn a_dependency_other_than_std_is_e0200_in_the_manifest_for_every_command() {
    let d = package("dep_fx", FX);
    // `check --json`
    let (out, doc) = check_json(&d);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1, "{doc}");
    assert_eq!(str_of(&ds[0], "code"), "E0200", "{doc}");
    assert!(!str_of(&ds[0], "message").is_empty(), "{doc}");
    let s = span_of(&ds[0]["span"]);
    assert_eq!((s.file.as_str(), s.line), ("onsa.toml", 6), "{doc}");
    // `test --json`: no test has run
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1, "{doc}");
    assert_eq!(str_of(&ds[0], "code"), "E0200", "{doc}");
    assert!(tests_of(&doc).is_empty(), "{doc}");
    // the commands that read the package
    for args in [vec!["check"], vec!["test"], vec!["interface"], vec!["audit"]] {
        let mut a = args.clone();
        let arg = d.arg();
        a.push(&arg);
        let out = run(d.root(), &a);
        assert_eq!(out.code, 2, "{a:?}: {}{}", out.stdout, out.stderr);
    }
}

/// Spec §15.3: each dependency other than std is its own E0200, at its own entry. An entry for
/// std in the same table is not one of them (the pin is W4-02).
#[test]
#[ignore = "W4-02"]
fn each_dependency_other_than_std_has_its_own_e0200() {
    let d = package("dep_two", "\n[dependencies]\nfx = \"1.0.0\"\nstd = \"0.0.0\"\nfy = \"2.1.0\"\n");
    let (out, doc) = check_json(&d);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let e0200: Vec<_> = diagnostics(&doc).iter().filter(|x| str_of(x, "code") == "E0200").collect();
    assert_eq!(e0200.len(), 2, "{doc}");
    let lines: Vec<u64> = e0200.iter().map(|x| span_of(&x["span"]).line).collect();
    assert_eq!(lines, vec![6, 8], "{doc}");
    for x in e0200 {
        assert_eq!(span_of(&x["span"]).file, "onsa.toml", "{doc}");
    }
}

/// Spec §15.3: a dependency that the source uses is E0200 at the manifest as well: the entry is
/// a feature that this version does not take, whether the source names it or not. The exit code
/// is 2. (What the source does with the name, and so whether E0302 is also reported for it, is
/// not fixed.)
#[test]
#[ignore = "W4-02"]
fn a_dependency_other_than_std_that_is_used_is_e0200_as_well() {
    let d = package("dep_used", FX);
    d.write("m.onsa", "use fx.{thing}\n\npub fn one() -> I32 {\n  1\n}\n");
    let (out, doc) = check_json(&d);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let at_manifest = diagnostics(&doc)
        .iter()
        .filter(|x| str_of(x, "code") == "E0200" && span_of(&x["span"]).file == "onsa.toml")
        .count();
    assert_eq!(at_manifest, 1, "{doc}");
}

// ---------------------------------------------------------------- the modules of std are files

/// The `pub` items of a std file, by name: `pub [target] [rt] <kind> <name>`.
fn pub_item_names(text: &str) -> Vec<String> {
    const KINDS: [&str; 8] = ["fn", "struct", "enum", "trait", "const", "type", "flow", "effect"];
    let mut names = Vec::new();
    for line in text.lines() {
        let mut words = line.split_whitespace();
        if words.next() != Some("pub") {
            continue;
        }
        let mut word = words.next();
        while matches!(word, Some("target") | Some("rt")) {
            word = words.next();
        }
        if let (Some(kind), Some(name)) = (word, words.next()) {
            if KINDS.contains(&kind) {
                let name: String = name.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                if !name.is_empty() {
                    names.push(name);
                }
            }
        }
    }
    names
}

fn std_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir).expect("read std/").map(|e| e.unwrap().path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            std_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "onsa") {
            out.push(p);
        }
    }
}

/// The names of the prelude (spec §15.1): `use std.<module>.{Option}` for one of them is E0304,
/// so they are not taken here.
const PRELUDE: [&str; 12] =
    ["Option", "Result", "Some", "None", "Ok", "Err", "panic", "Alloc", "Block", "Copy", "Dup", "Show"];

/// Spec §15.1 (R-80 (4)): the path of a module of std is the path of its file under `std/`, so
/// each file with a `pub` item is reached by `use std.<path>.{item}` and the item is found. A
/// file that is added to `std/` is a module with no other registration.
#[test]
fn every_file_of_std_is_the_module_of_its_path() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let mut files = Vec::new();
    std_files(&root, &mut files);
    let mut reached: Vec<String> = Vec::new();
    for f in &files {
        let rel = f.strip_prefix(&root).unwrap().with_extension("");
        let path: Vec<String> = rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect();
        let module = path.join(".");
        let text = std::fs::read_to_string(f).unwrap();
        let Some(item) = pub_item_names(&text).into_iter().find(|n| !PRELUDE.contains(&n.as_str())) else {
            continue;
        };
        let d = Dir::bare(&format!("std_file_{}", reached.len()));
        d.write("m.onsa", &format!("use std.{module}.{{{item}}}\n"));
        let out = run(d.root(), &["check", "--json", "m.onsa"]);
        assert_eq!(out.code, 0, "use std.{module}.{{{item}}}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "use std.{module}.{{{item}}}: {}", out.stdout);
        reached.push(module);
    }
    // The modules that the spec names (§11.5, §11.8, §13.4, §17.3) are among them, and a
    // directory module and its child are both there (`std/dsp.onsa` and `std/dsp/test.onsa`).
    for want in ["math", "dsp", "dsp.test", "test"] {
        assert!(reached.iter().any(|m| m == want), "std.{want} is not reached: {reached:?}");
    }
}
