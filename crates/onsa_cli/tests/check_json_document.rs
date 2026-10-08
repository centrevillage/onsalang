//! The document `onsa check --json` prints, and the order and the file names of the diagnostics
//! in it, in JSON and in text (spec §18.1, `docs/onsa-tools.md` §4; S-213, S-215, S-234, W3-16).
//!
//! What the spec fixes, and so what is checked here:
//! - the standard output is one JSON object; the diagnostics are its `diagnostics` array, an empty
//!   array when there is none (S-215). The spacing and the line breaks of the text are not fixed
//!   and not read, and a reader skips keys it does not know, so no test forbids another key;
//! - a diagnostic has `code`, `message`, `span`, `fixes` and `notes`; the two arrays are there
//!   even when empty; a key with no value (`found`, the `span` of a note) is left out and never
//!   `null`; `found` is the source text of the range and is left out for an empty or blank range
//!   (S-213);
//! - `span.file`, in a diagnostic, an edit and a note alike, is the path from the package root
//!   (the directory of `onsa.toml`) with `/` between the parts; for an input with no manifest it
//!   is the path as it was passed, with its separators turned into `/` (S-234);
//! - `diagnostics` are ordered by the `file` string (code points), line, column, end line, end
//!   column, code and message, and the text output lists the diagnostics in the same order
//!   (S-234). The package is gathered by the root, so the order does not depend on the working
//!   directory, the order of the arguments or the locale.
//!
//! Not written here: `onsa test --json` (W2-10), the layout of the lines after the first line of
//! a diagnostic in the text output (not fixed), the shape of fix candidates (diagnostics_json.rs).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

/// A scratch directory; `pkg` has a manifest, `bare` has none.
struct Dir(PathBuf);

impl Dir {
    fn bare(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_check_json_doc_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn pkg(tag: &str) -> Dir {
        let d = Dir::bare(tag);
        d.write("onsa.toml", "[package]\nname = \"demo\"\nedition = \"2026\"\n");
        d
    }

    fn write(&self, rel: &str, text: &str) {
        let p = self.0.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, text).unwrap();
    }

    fn abs(&self, rel: &str) -> String {
        self.0.join(rel).to_string_lossy().into_owned()
    }

    fn root(&self) -> &Path {
        &self.0
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct Out {
    code: i32,
    stdout: String,
    stderr: String,
}

fn run_env(cwd: &Path, args: &[&str], env: &[(&str, &str)]) -> Out {
    let mut cmd = Command::new(ONSA);
    cmd.args(args).current_dir(cwd);
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run onsa");
    Out {
        code: out.status.code().unwrap_or_else(|| panic!("onsa {args:?} ended by a signal: {out:?}")),
        stdout: String::from_utf8(out.stdout).expect("utf-8 standard output"),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

fn run(cwd: &Path, args: &[&str]) -> Out {
    run_env(cwd, args, &[])
}

/// The whole standard output is one JSON value, and it is an object (§18.1). Nothing else may be
/// on the standard output: an array, or an object per line, does not parse as one value.
fn doc_of(out: &Out) -> Value {
    let v: Value = serde_json::from_str(&out.stdout)
        .unwrap_or_else(|e| panic!("the standard output is not one JSON value ({e}): {:?}", out.stdout));
    assert!(v.is_object(), "the document is not an object: {v}");
    v
}

fn diagnostics(doc: &Value) -> &Vec<Value> {
    doc.get("diagnostics")
        .unwrap_or_else(|| panic!("no `diagnostics` key: {doc}"))
        .as_array()
        .unwrap_or_else(|| panic!("`diagnostics` is not an array: {doc}"))
}

/// `onsa check --json <args>` run in `cwd`: the exit code and the document.
fn check_json(cwd: &Path, args: &[&str]) -> (i32, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out.code, doc)
}

fn code_of(d: &Value) -> &str {
    d["code"].as_str().expect("`code` is a string")
}

fn file_of(d: &Value) -> &str {
    d["span"]["file"].as_str().expect("`span.file` is a string")
}

fn int(v: &Value, k: &str) -> u64 {
    v.get(k).and_then(Value::as_u64).unwrap_or_else(|| panic!("no integer `{k}` in {v}"))
}

/// The sort key of §18.1: file string, line, column, end line, end column, code, message.
type Key = (String, u64, u64, u64, u64, String, String);

fn key(d: &Value) -> Key {
    let s = &d["span"];
    (
        file_of(d).to_string(),
        int(s, "line"),
        int(s, "col"),
        int(s, "end_line"),
        int(s, "end_col"),
        code_of(d).to_string(),
        d["message"].as_str().expect("`message` is a string").to_string(),
    )
}

fn assert_sorted(ds: &[Value]) {
    for w in ds.windows(2) {
        assert!(key(&w[0]) <= key(&w[1]), "out of order:\n  {}\nbefore\n  {}", w[0], w[1]);
    }
}

fn files(ds: &[Value]) -> Vec<&str> {
    ds.iter().map(file_of).collect()
}

/// Every `span.file` in a document: the diagnostics' own, the edits' and the notes'.
fn all_files(doc: &Value) -> Vec<String> {
    fn walk(v: &Value, out: &mut Vec<String>) {
        match v {
            Value::Object(o) => {
                if let Some(Value::Object(s)) = o.get("span") {
                    if let Some(Value::String(f)) = s.get("file") {
                        out.push(f.clone());
                    }
                }
                for x in o.values() {
                    walk(x, out);
                }
            }
            Value::Array(a) => a.iter().for_each(|x| walk(x, out)),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(&doc["diagnostics"], &mut out);
    out
}

fn has_null(v: &Value) -> bool {
    match v {
        Value::Null => true,
        Value::Array(a) => a.iter().any(has_null),
        Value::Object(o) => o.values().any(has_null),
        _ => false,
    }
}

/// `fn <name>() -> I32` whose body names `ident`, which is not defined: one E0302 at line 2,
/// column 3, for the identifier.
fn unresolved(name: &str, ident: &str) -> String {
    format!("pub fn {name}() -> I32 {{\n  {ident}\n}}\n")
}

// ---- the document ----------------------------------------------------------------------------

#[test]
fn no_diagnostic_gives_an_object_with_an_empty_diagnostics_array() {
    let d = Dir::bare("empty");
    d.write("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let (code, doc) = check_json(d.root(), &["ok.onsa"]);
    assert_eq!(code, 0);
    assert_eq!(diagnostics(&doc), &Vec::<Value>::new(), "`diagnostics` is there, and empty: {doc}");
}

#[test]
fn an_empty_package_gives_the_same_document_as_an_empty_file() {
    let d = Dir::pkg("empty_pkg");
    d.write("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    d.write("sub/inner.onsa", "pub fn g() -> I32 {\n  2\n}\n");
    let (code, doc) = check_json(d.root(), &["."]);
    assert_eq!(code, 0);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

#[test]
fn the_flag_may_come_after_the_paths() {
    let d = Dir::bare("flag_after");
    d.write("a.onsa", &unresolved("f", "zzz"));
    let out = run(d.root(), &["check", "a.onsa", "--json"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    assert_eq!(diagnostics(&doc_of(&out)).len(), 1);
}

#[test]
fn with_diagnostics_in_several_files_the_output_is_still_one_object() {
    let d = Dir::bare("one_object");
    d.write("a.onsa", &unresolved("f", "zzz"));
    d.write("b.onsa", &unresolved("g", "yyy"));
    d.write("c.onsa", &unresolved("h", "xxx"));
    let out = run(d.root(), &["check", "--json", "a.onsa", "b.onsa", "c.onsa"]);
    assert_eq!(out.code, 1, "{}", out.stderr);
    let doc = doc_of(&out); // fails for an array, and for an object per line or per file
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 3, "{doc}");
    assert!(ds.iter().all(|x| code_of(x) == "E0302"), "{doc}");
}

#[test]
fn a_check_with_an_unresolved_name_has_the_five_keys_of_a_diagnostic_and_a_message() {
    let d = Dir::bare("five_keys");
    d.write("a.onsa", &unresolved("f", "zzz"));
    let (code, doc) = check_json(d.root(), &["a.onsa"]);
    assert_eq!(code, 1);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1);
    let x = &ds[0];
    assert_eq!(code_of(x), "E0302");
    assert!(x["message"].as_str().is_some_and(|m| m.contains("zzz")), "the message names the identifier: {x}");
    assert_eq!(x["span"]["file"], "a.onsa");
    assert_eq!((int(&x["span"], "line"), int(&x["span"], "col")), (2, 3));
    assert_eq!((int(&x["span"], "end_line"), int(&x["span"], "end_col")), (2, 6));
    assert_eq!(x["found"], "zzz", "`found` is the source text of the range: {x}");
    assert!(x["fixes"].is_array(), "`fixes` is always there: {x}");
    assert!(x["notes"].is_array(), "`notes` is always there: {x}");
}

// ---- the keys that are always there, and the ones that are left out ----------------------------

/// Diagnostics of many codes, in a package: a candidate with edits, a candidate-free diagnostic,
/// a position-less note (E0020 for `;`), a positioned note (E0304), and a diagnostic whose range
/// is one character (E0001).
fn shape_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write(
        "mixed.onsa",
        "pub struct Pt {\n  x: U32,\n}\n\nimpl Pt {\n  pub fn norm(self) -> U32 { self.x }\n  \
         pub fn scale(inout self, k: U32) { self.x = self.x * k }\n}\n\npub fn missing_bang(inout p: Pt) {\n  \
         p.scale(2)\n}\n\npub fn extra_bang(p: Pt) -> U32 {\n  p.norm!()\n}\n\npub fn lower(x: i32) -> I32 {\n  x\n}\n",
    );
    d.write("dup.onsa", "pub fn twice() -> I32 {\n  1\n}\n\npub fn twice() -> I32 {\n  2\n}\n");
    d.write("semi.onsa", "pub fn g() -> I32 {\n  let a = 1;\n  a\n}\n");
    d.write("lex.onsa", "pub fn h() -> I32 {\n  1 $ 2\n}\n");
    d.write("names.onsa", &unresolved("k", "zzz"));
    d
}

#[test]
fn every_diagnostic_has_code_message_span_fixes_and_notes() {
    let d = shape_package("keys");
    let (code, doc) = check_json(d.root(), &["."]);
    assert_eq!(code, 1);
    let ds = diagnostics(&doc);
    let codes: Vec<&str> = ds.iter().map(code_of).collect();
    for want in ["E0001", "E0020", "E0302", "E0304", "E0713", "E0714"] {
        assert!(codes.contains(&want), "no {want} in {codes:?}");
    }
    for x in ds {
        let c = code_of(x);
        assert!(
            c.len() == 5 && c.starts_with('E') && c[1..].bytes().all(|b| b.is_ascii_digit()),
            "a code is E and four digits: {c}"
        );
        assert!(x["message"].as_str().is_some_and(|m| !m.is_empty()), "{c}: `message` is a non-empty string: {x}");
        for k in ["line", "col", "end_line", "end_col"] {
            assert!(int(&x["span"], k) >= 1, "{c}: {k} counts from 1: {x}");
        }
        assert!(x["span"]["file"].is_string(), "{c}: {x}");
        assert!(x["fixes"].is_array(), "{c}: `fixes` is there, empty or not: {x}");
        assert!(x["notes"].is_array(), "{c}: `notes` is there, empty or not: {x}");
    }
}

#[test]
fn an_empty_fixes_and_an_empty_notes_are_arrays_and_not_left_out() {
    // E0001 for `$` has no candidate (nothing to replace it with). Some diagnostic of the
    // package has no note at all: the lists are written out empty.
    let d = shape_package("empty_lists");
    let (_, doc) = check_json(d.root(), &["."]);
    let ds = diagnostics(&doc);
    let lex: Vec<&Value> = ds.iter().filter(|x| code_of(x) == "E0001").collect();
    assert_eq!(lex.len(), 1, "{doc}");
    assert_eq!(lex[0]["fixes"], Value::Array(vec![]), "{}", lex[0]);
    assert!(
        ds.iter().any(|x| x["notes"] == Value::Array(vec![])),
        "no diagnostic with `\"notes\": []` among {} diagnostics",
        ds.len()
    );
}

#[test]
fn no_value_is_null_a_key_with_no_value_is_left_out() {
    let d = shape_package("no_null");
    let (_, doc) = check_json(d.root(), &["."]);
    assert!(!has_null(&doc["diagnostics"]), "a `null` in the diagnostics: {}", doc["diagnostics"]);
    for x in diagnostics(&doc) {
        for n in x["notes"].as_array().unwrap() {
            if let Some(s) = n.get("span") {
                assert!(s.is_object(), "a note's `span` is an object or not there: {n}");
            }
        }
    }
}

#[test]
fn found_is_the_source_text_of_the_range_and_is_left_out_for_an_empty_or_blank_range() {
    let d = shape_package("found");
    let (_, doc) = check_json(d.root(), &["."]);
    let mut with_found = 0;
    for x in diagnostics(&doc) {
        let s = &x["span"];
        let text = std::fs::read_to_string(d.root().join(file_of(x))).expect("the file of the span");
        let a = offset(&text, int(s, "line"), int(s, "col"));
        let b = offset(&text, int(s, "end_line"), int(s, "end_col"));
        let range = &text[a..b];
        let blank = range.trim().is_empty();
        match x.get("found") {
            None => {
                assert!(blank, "{}: `found` is left out for a range that is not blank ({range:?}): {x}", code_of(x))
            }
            Some(f) => {
                assert!(!blank, "{}: `found` for an empty or blank range ({range:?}): {x}", code_of(x));
                assert_eq!(f.as_str(), Some(range), "{}: `found` is the source text of the range: {x}", code_of(x));
                with_found += 1;
            }
        }
    }
    assert!(with_found >= 4, "too few diagnostics with `found`: {with_found}");
}

/// The byte offset of the (1-based line, 1-based column in characters) position in `text`.
fn offset(text: &str, line: u64, col: u64) -> usize {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n').expect("a line past the end of the file") + 1;
    }
    let rest = &text[start..];
    let line_len = rest.find('\n').unwrap_or(rest.len());
    let mut chars = rest[..line_len].char_indices();
    match chars.nth(usize::try_from(col).unwrap() - 1) {
        Some((i, _)) => start + i,
        None => start + line_len,
    }
}

// ---- span.file -----------------------------------------------------------------------------------

fn nested_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    d.write("top.onsa", &unresolved("t", "tt"));
    d.write("sub/inner.onsa", &unresolved("i", "ii"));
    d.write("sub/deep/leaf.onsa", &unresolved("l", "ll"));
    d
}

fn sorted_files_of(doc: &Value) -> Vec<String> {
    let mut f: Vec<String> = diagnostics(doc).iter().map(|x| file_of(x).to_string()).collect();
    f.sort();
    f
}

const NESTED_FILES: [&str; 3] = ["sub/deep/leaf.onsa", "sub/inner.onsa", "top.onsa"];

#[test]
fn in_a_package_span_file_is_the_path_from_the_root_with_slashes() {
    let d = nested_package("root_rel");
    let (code, doc) = check_json(d.root(), &["."]);
    assert_eq!(code, 1);
    assert_eq!(sorted_files_of(&doc), NESTED_FILES, "{doc}");
}

#[test]
fn the_package_gives_the_same_document_however_it_is_named_and_from_wherever() {
    let d = nested_package("same_doc");
    let elsewhere = Dir::bare("same_doc_elsewhere");
    let parent = d.root().parent().unwrap();
    let name = d.root().file_name().unwrap().to_string_lossy().into_owned();
    let (c0, base) = check_json(d.root(), &["."]);
    assert_eq!(c0, 1);
    assert_eq!(sorted_files_of(&base), NESTED_FILES);
    let manifest = d.abs("onsa.toml");
    let root_abs = d.root().to_string_lossy().into_owned();
    let variants: Vec<(String, PathBuf, Vec<String>)> = vec![
        ("the absolute root from another directory".into(), elsewhere.root().to_path_buf(), vec![root_abs.clone()]),
        ("the relative root from its parent".into(), parent.to_path_buf(), vec![name.clone()]),
        ("`./` and the relative root".into(), parent.to_path_buf(), vec![format!("./{name}")]),
        ("the manifest, absolute".into(), elsewhere.root().to_path_buf(), vec![manifest.clone()]),
        ("the manifest, relative".into(), parent.to_path_buf(), vec![format!("{name}/onsa.toml")]),
        ("the root with a trailing slash".into(), elsewhere.root().to_path_buf(), vec![format!("{root_abs}/")]),
    ];
    for (what, cwd, args) in variants {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        let (c, doc) = check_json(&cwd, &a);
        assert_eq!(c, 1, "{what}");
        assert_eq!(
            doc["diagnostics"], base["diagnostics"],
            "{what}: the diagnostics differ from `check .` in the root"
        );
    }
}

#[test]
fn the_edits_and_the_notes_of_a_package_use_the_root_path_too() {
    let d = Dir::pkg("edits_notes");
    // E0713 (a candidate with an edit) and E0304 (a note with a position), both in a module in a
    // directory.
    d.write(
        "dsp/voice.onsa",
        "pub struct Pt {\n  x: U32,\n}\n\nimpl Pt {\n  pub fn scale(inout self, k: U32) { self.x = self.x * k }\n}\n\n\
         pub fn missing_bang(inout p: Pt) {\n  p.scale(2)\n}\n\npub fn twice() -> I32 {\n  1\n}\n\npub fn twice() -> I32 {\n  2\n}\n",
    );
    let elsewhere = Dir::bare("edits_notes_elsewhere");
    for (cwd, arg) in [(d.root().to_path_buf(), ".".to_string()), (elsewhere.root().to_path_buf(), d.abs(""))] {
        let (code, doc) = check_json(&cwd, &[&arg]);
        assert_eq!(code, 1);
        let ds = diagnostics(&doc);
        let codes: Vec<&str> = ds.iter().map(code_of).collect();
        assert!(codes.contains(&"E0713") && codes.contains(&"E0304"), "{codes:?}");
        let seen = all_files(&doc);
        assert!(seen.len() >= 4, "a diagnostic, an edit and a note have a span each: {seen:?}");
        for f in &seen {
            assert_eq!(f, "dsp/voice.onsa", "every span of the package is the path from the root");
        }
    }
}

#[test]
fn without_a_manifest_span_file_is_the_path_as_passed() {
    let d = Dir::bare("as_passed");
    d.write("rel/x.onsa", &unresolved("f", "zzz"));
    d.write("top.onsa", &unresolved("g", "yyy"));
    let abs = d.abs("rel/x.onsa");
    for (arg, want) in [
        ("rel/x.onsa".to_string(), "rel/x.onsa".to_string()),
        ("./rel/x.onsa".to_string(), "./rel/x.onsa".to_string()),
        ("top.onsa".to_string(), "top.onsa".to_string()),
        ("./top.onsa".to_string(), "./top.onsa".to_string()),
        (abs.clone(), abs.clone()),
    ] {
        let (code, doc) = check_json(d.root(), &[&arg]);
        assert_eq!(code, 1, "{arg}");
        let ds = diagnostics(&doc);
        assert_eq!(ds.len(), 1, "{arg}: {doc}");
        assert_eq!(file_of(&ds[0]), want, "{arg}");
    }
    // from another directory, a relative path stays relative to where it was passed
    let from_parent = format!("{}/top.onsa", d.root().file_name().unwrap().to_string_lossy());
    let (code, doc) = check_json(d.root().parent().unwrap(), &[&from_parent]);
    assert_eq!(code, 1);
    assert_eq!(file_of(&diagnostics(&doc)[0]), from_parent, "{doc}");
}

#[test]
fn without_a_manifest_the_edits_and_the_notes_use_the_passed_path_too() {
    let d = Dir::bare("as_passed_edits");
    d.write(
        "sub/m.onsa",
        "pub struct Pt {\n  x: U32,\n}\n\nimpl Pt {\n  pub fn scale(inout self, k: U32) { self.x = self.x * k }\n}\n\n\
         pub fn missing_bang(inout p: Pt) {\n  p.scale(2)\n}\n\npub fn twice() -> I32 {\n  1\n}\n\npub fn twice() -> I32 {\n  2\n}\n",
    );
    for arg in ["sub/m.onsa", "./sub/m.onsa"] {
        let (code, doc) = check_json(d.root(), &[arg]);
        assert_eq!(code, 1);
        let seen = all_files(&doc);
        assert!(seen.len() >= 4, "{seen:?}");
        for f in &seen {
            assert_eq!(f, arg, "every span repeats the path as it was passed");
        }
    }
}

#[test]
#[ignore = "W4-02"]
fn a_file_inside_a_package_is_named_by_the_root_path_and_only_its_diagnostics_are_printed() {
    // §15.1: the root is found above the file; the whole package is gathered and resolved, and
    // only the diagnostics of the given file are printed (R-47 fixes this in W4-02).
    let d = Dir::pkg("inside");
    d.write("a.onsa", "pub fn ga() -> I32 {\n  1\n}\n\npub fn bad_a() -> I32 {\n  zzz\n}\n");
    d.write("sub/b.onsa", "use a.{ga}\n\npub fn f() -> I32 {\n  ga() + yyy\n}\n");
    let sub = d.root().join("sub");
    for (cwd, arg) in [(sub.clone(), "b.onsa".to_string()), (d.root().to_path_buf(), d.abs("sub/b.onsa"))] {
        let (code, doc) = check_json(&cwd, &[&arg]);
        assert_eq!(code, 1);
        let ds = diagnostics(&doc);
        assert_eq!(ds.len(), 1, "only the given file's diagnostics (and `use a.{{ga}}` resolves): {doc}");
        assert_eq!((code_of(&ds[0]), file_of(&ds[0])), ("E0302", "sub/b.onsa"));
    }
}

#[test]
fn a_bare_manifest_in_the_working_directory_gives_the_same_document_as_the_root() {
    // §15.1, §18.1 (S-234, R-178): `onsa.toml` passed with no directory names the package in the
    // working directory; the document is that of `.` and `./onsa.toml`.
    let d = nested_package("bare_manifest");
    let (c0, base) = check_json(d.root(), &["."]);
    assert_eq!(c0, 1);
    assert_eq!(sorted_files_of(&base), NESTED_FILES);
    for arg in ["onsa.toml", "./onsa.toml"] {
        let (c, doc) = check_json(d.root(), &[arg]);
        assert_eq!(c, 1, "{arg}");
        assert_eq!(doc["diagnostics"], base["diagnostics"], "{arg}: the diagnostics differ from `check .`");
    }
}

#[cfg(windows)]
#[test]
fn separators_are_slashes_on_windows() {
    let d = Dir::bare("windows");
    d.write("sub/x.onsa", &unresolved("f", "zzz"));
    let (code, doc) = check_json(d.root(), &["sub\\x.onsa"]);
    assert_eq!(code, 1);
    assert_eq!(file_of(&diagnostics(&doc)[0]), "sub/x.onsa");
}

// ---- the order ----------------------------------------------------------------------------------

const ORDER_FILES: [&str; 5] = ["a.onsa", "a.onsa", "a/b.onsa", "a1.onsa", "a_c.onsa"];

fn order_package(tag: &str) -> Dir {
    let d = Dir::pkg(tag);
    // two diagnostics in a.onsa, then one in each of a/b.onsa, a1.onsa and a_c.onsa. The file
    // strings compare as `a.onsa` < `a/b.onsa` < `a1.onsa` < `a_c.onsa` (`.` 2E, `/` 2F, `1` 31,
    // `_` 5F); comparing the paths part by part would put `a/b.onsa` first.
    d.write("a.onsa", &format!("{}\n{}", unresolved("f1", "zzz"), unresolved("g1", "yyy")));
    d.write("a/b.onsa", &unresolved("f2", "qqq"));
    d.write("a1.onsa", &unresolved("f3", "ppp"));
    d.write("a_c.onsa", &unresolved("f4", "rrr"));
    d.write("clean.onsa", "pub fn ok() -> I32 {\n  1\n}\n");
    d
}

#[test]
fn the_diagnostics_of_a_package_are_ordered_by_the_file_string() {
    let d = order_package("pkg_order");
    let (code, doc) = check_json(d.root(), &["."]);
    assert_eq!(code, 1);
    let ds = diagnostics(&doc);
    assert_eq!(files(ds), ORDER_FILES, "{doc}");
    assert_sorted(ds);
}

#[test]
fn the_order_does_not_depend_on_the_locale() {
    let d = order_package("locale");
    let base = run_env(d.root(), &["check", "--json", "."], &[("LC_ALL", "C"), ("LANG", "C")]);
    let other = run_env(d.root(), &["check", "--json", "."], &[("LC_ALL", "en_US.UTF-8"), ("LANG", "en_US.UTF-8")]);
    let (a, b) = (doc_of(&base), doc_of(&other));
    assert_eq!(a, b);
    assert_eq!(files(diagnostics(&a)), ORDER_FILES, "{a}");
}

#[test]
fn files_passed_in_another_order_give_the_same_document() {
    // No manifest: the files are passed one by one. The order of the arguments does not matter;
    // the order is that of the file strings as they are printed.
    let d = Dir::bare("arg_order");
    d.write("a.onsa", &unresolved("f1", "zzz"));
    d.write("sub/b.onsa", &unresolved("f2", "yyy"));
    d.write("sub.onsa", &unresolved("f3", "xxx"));
    d.write("sub_c.onsa", &unresolved("f4", "www"));
    // `sub.onsa` < `sub/b.onsa` < `sub_c.onsa`, all after `a.onsa`
    let want = ["a.onsa", "sub.onsa", "sub/b.onsa", "sub_c.onsa"];
    for args in [
        ["a.onsa", "sub.onsa", "sub/b.onsa", "sub_c.onsa"],
        ["sub_c.onsa", "sub/b.onsa", "sub.onsa", "a.onsa"],
        ["sub/b.onsa", "a.onsa", "sub_c.onsa", "sub.onsa"],
    ] {
        let (code, doc) = check_json(d.root(), &args);
        assert_eq!(code, 1, "{args:?}");
        assert_eq!(files(diagnostics(&doc)), want, "{args:?}");
    }
}

#[test]
fn the_file_strings_are_compared_as_printed_so_dot_slash_comes_first() {
    let d = Dir::bare("dot_slash");
    d.write("a.onsa", &unresolved("f1", "zzz"));
    d.write("b.onsa", &unresolved("f2", "yyy"));
    d.write("c.onsa", &unresolved("f3", "xxx"));
    // `./b.onsa` < `a.onsa` < `c.onsa` ('.' is 2E, 'a' is 61)
    let (code, doc) = check_json(d.root(), &["c.onsa", "a.onsa", "./b.onsa"]);
    assert_eq!(code, 1);
    assert_eq!(files(diagnostics(&doc)), ["./b.onsa", "a.onsa", "c.onsa"], "{doc}");
}

#[test]
fn inside_a_file_the_order_is_by_position_and_not_by_stage_or_code() {
    // The first unit has a type error (a later stage than the lexical error of the second): the
    // output is still in the order of the source.
    let d = Dir::bare("by_position");
    d.write(
        "m.onsa",
        "pub fn a() -> I32 {\n  \"x\"\n}\n\npub fn b() -> I32 {\n  1 $ 2\n}\n\npub fn c() -> I32 {\n  zzz\n}\n",
    );
    let (code, doc) = check_json(d.root(), &["m.onsa"]);
    assert_eq!(code, 1);
    let ds = diagnostics(&doc);
    let got: Vec<(&str, u64)> = ds.iter().map(|x| (code_of(x), int(&x["span"], "line"))).collect();
    assert_eq!(got, [("E0401", 2), ("E0001", 6), ("E0302", 10)], "{doc}");
    assert_sorted(ds);
}

// No two units share a line: a declaration ends at its newline (§2.5), and the tokens after it on
// its line are of its unit (S-274). The order by column is checked by the unit test
// `the_order_is_the_file_string_then_the_position_then_code_and_message` of `onsa_diag`.

#[test]
fn the_diagnostics_are_in_the_documented_order_for_a_mixed_package() {
    // Whatever the files are, the list is non-decreasing in the key of §18.1, up to the
    // code point order of the file string. (The order of the file strings is in the ignored
    // tests above; this one holds for a package whose paths do not differ by `.`, `/`, `_`.)
    let d = Dir::pkg("sorted_mixed");
    d.write("b.onsa", &format!("{}\n{}", unresolved("f1", "zzz"), "pub fn g() -> I32 {\n  1 $ 2\n}\n"));
    d.write("a.onsa", &unresolved("f2", "yyy"));
    d.write("z.onsa", &unresolved("f3", "xxx"));
    let (code, doc) = check_json(d.root(), &["."]);
    assert_eq!(code, 1);
    let ds = diagnostics(&doc);
    assert_eq!(files(ds), ["a.onsa", "b.onsa", "b.onsa", "z.onsa"], "{doc}");
    assert_sorted(ds);
}

// ---- the text output ----------------------------------------------------------------------------

/// The head lines of the diagnostics in the text output: `<file>:<line>:<col>: error[<code>]: <message>`.
/// Other lines (the source, `note:` lines, candidates) are not read: their layout is not fixed.
fn text_heads(text: &str) -> Vec<(String, u64, u64, String, String)> {
    let mut out = Vec::new();
    for l in text.lines() {
        if l.starts_with(char::is_whitespace) {
            continue;
        }
        let Some(i) = l.find(": error[") else { continue };
        let (pos, rest) = (&l[..i], &l[i + ": error[".len()..]);
        let Some((code, message)) = rest.split_once("]: ") else { continue };
        let mut it = pos.rsplitn(3, ':');
        let (col, line, file) = (it.next().unwrap(), it.next().unwrap(), it.next().unwrap());
        out.push((
            file.to_string(),
            line.parse().unwrap(),
            col.parse().unwrap(),
            code.to_string(),
            message.to_string(),
        ));
    }
    out
}

#[test]
fn the_first_line_of_a_diagnostic_in_text_has_the_values_of_the_json_span() {
    let d = nested_package("text_head");
    let text = run(d.root(), &["check", "."]);
    assert_eq!(text.code, 1, "{}", text.stderr);
    assert!(text.stderr.is_empty() || !text.stderr.contains("error["), "diagnostics go to the standard output");
    let (_, doc) = check_json(d.root(), &["."]);
    let ds = diagnostics(&doc);
    let heads = text_heads(&text.stdout);
    assert_eq!(heads.len(), ds.len(), "{}", text.stdout);
    for (h, x) in heads.iter().zip(ds) {
        let s = &x["span"];
        assert_eq!(
            (h.0.as_str(), h.1, h.2, h.3.as_str(), h.4.as_str()),
            (file_of(x), int(s, "line"), int(s, "col"), code_of(x), x["message"].as_str().unwrap()),
            "text and JSON differ"
        );
    }
}

#[test]
fn the_text_lists_the_diagnostics_in_the_order_of_the_json() {
    let d = Dir::pkg("text_order");
    d.write("b.onsa", &format!("{}\n{}", unresolved("f1", "zzz"), "pub fn g() -> I32 {\n  1 $ 2\n}\n"));
    d.write("a.onsa", &unresolved("f2", "yyy"));
    d.write("sub/c.onsa", &unresolved("f3", "xxx"));
    let text = run(d.root(), &["check", "."]);
    let heads = text_heads(&text.stdout);
    let keys: Vec<(String, u64, u64, String)> = heads.into_iter().map(|h| (h.0, h.1, h.2, h.3)).collect();
    let (_, doc) = check_json(d.root(), &["."]);
    let want: Vec<(String, u64, u64, String)> = diagnostics(&doc)
        .iter()
        .map(|x| (file_of(x).to_string(), int(&x["span"], "line"), int(&x["span"], "col"), code_of(x).to_string()))
        .collect();
    assert_eq!(keys, want);
    let files: Vec<&str> = want.iter().map(|k| k.0.as_str()).collect();
    assert_eq!(files, ["a.onsa", "b.onsa", "b.onsa", "sub/c.onsa"]);
}

#[test]
fn the_text_orders_the_files_by_their_strings_too() {
    let d = order_package("text_file_order");
    let text = run(d.root(), &["check", "."]);
    assert_eq!(text.code, 1);
    let heads = text_heads(&text.stdout);
    let got: Vec<&str> = heads.iter().map(|h| h.0.as_str()).collect();
    assert_eq!(got, ORDER_FILES, "{}", text.stdout);
}

#[test]
fn the_text_uses_slashes_and_the_passed_path_without_a_manifest() {
    let d = Dir::bare("text_paths");
    d.write("sub/x.onsa", &unresolved("f", "zzz"));
    for arg in ["sub/x.onsa", "./sub/x.onsa"] {
        let text = run(d.root(), &["check", arg]);
        assert_eq!(text.code, 1);
        let heads = text_heads(&text.stdout);
        assert_eq!(heads.len(), 1, "{}", text.stdout);
        assert_eq!((heads[0].0.as_str(), heads[0].1, heads[0].2, heads[0].3.as_str()), (arg, 2, 3, "E0302"));
    }
}

#[test]
fn the_text_of_a_clean_package_has_no_diagnostic_and_the_exit_code_is_0() {
    let d = Dir::pkg("text_clean");
    d.write("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let text = run(d.root(), &["check", "."]);
    assert_eq!(text.code, 0, "{}{}", text.stdout, text.stderr);
    assert!(text_heads(&text.stdout).is_empty(), "{}", text.stdout);
}

// ---- when no document is printed ------------------------------------------------------------------

#[test]
fn an_input_error_prints_nothing_on_standard_output_with_json() {
    // §18.2: a 2 with no diagnostic (a missing file) prints no JSON; the text goes to standard error.
    let d = Dir::bare("missing");
    let out = run(d.root(), &["check", "--json", "no_such_file.onsa"]);
    assert_eq!(out.code, 2);
    assert_eq!(out.stdout, "", "standard output is empty");
    assert!(!out.stderr.is_empty(), "the reason is on standard error");
}

#[test]
#[ignore = "W4-02"]
fn a_manifest_diagnostic_is_a_document_with_exit_code_2_and_the_manifest_as_its_file() {
    // §18.1, §18.2: a diagnostic that points into `onsa.toml` (E1102 for an unknown key) is a
    // diagnostic like any other, with exit code 2, and `--json` prints the document for it.
    let d = Dir::bare("manifest");
    d.write("onsa.toml", "[package]\nname = \"demo\"\nedition = \"2026\"\nfoo = 1\n");
    d.write("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let out = run(d.root(), &["check", "--json", "."]);
    assert_eq!(out.code, 2, "{}", out.stderr);
    let doc = doc_of(&out);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1, "{doc}");
    assert_eq!((code_of(&ds[0]), file_of(&ds[0])), ("E1102", "onsa.toml"));
    assert_eq!(int(&ds[0]["span"], "line"), 4);
}

// ---- other commands with `--json` -----------------------------------------------------------------

/// `onsa interface --json <args>` run in `cwd`: the exit code and the document.
fn interface_json(cwd: &Path, args: &[&str]) -> (i32, Value) {
    let mut a = vec!["interface", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out.code, doc)
}

#[test]
fn interface_json_of_a_clean_package_has_an_empty_diagnostics_array_beside_its_result() {
    // §18.1: the output of every command with `--json` is one object with `diagnostics`, an empty
    // array when there is none. `onsa interface` adds its own keys to the same object.
    let d = Dir::pkg("iface_ok");
    d.write("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let (code, doc) = interface_json(d.root(), &["."]);
    assert_eq!(code, 0);
    assert_eq!(diagnostics(&doc), &Vec::<Value>::new(), "{doc}");
    assert_eq!(doc["package"], "demo", "{doc}");
    assert!(doc["modules"].is_array(), "{doc}");
}

#[test]
fn interface_json_with_diagnostics_is_the_document_of_check_and_exits_with_1() {
    let d = nested_package("iface_diags");
    let (code, doc) = interface_json(d.root(), &["."]);
    assert_eq!(code, 1);
    let (_, checked) = check_json(d.root(), &["."]);
    assert_eq!(doc["diagnostics"], checked["diagnostics"], "the diagnostics are those of `check --json`");
    assert_eq!(sorted_files_of(&doc), NESTED_FILES, "{doc}");
    assert_sorted(diagnostics(&doc));
}
