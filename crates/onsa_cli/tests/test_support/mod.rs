//! Shared by the `onsa test` integration tests (`test_identity.rs`, `test_json_document.rs`):
//! a scratch package, one run of the built `onsa`, and readers of the document `onsa test --json`
//! prints (spec §18.1) and of the result lines of the text output (`docs/onsa-tools.md` §4).

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

pub const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

/// A scratch directory; `pkg` has a manifest, `bare` has none.
pub struct Dir(pub PathBuf);

impl Dir {
    pub fn bare(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_test_cmd_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    pub fn pkg(tag: &str) -> Dir {
        let d = Dir::bare(tag);
        d.write("onsa.toml", "[package]\nname = \"demo\"\nedition = \"2026\"\n");
        d
    }

    pub fn write(&self, rel: &str, text: &str) {
        let p = self.0.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, text).unwrap();
    }

    pub fn root(&self) -> &Path {
        &self.0
    }

    /// The directory as an argument: `onsa test <root>` gathers the whole package.
    pub fn arg(&self) -> String {
        self.0.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub struct Out {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

/// One run of `onsa <args>` in `cwd`. A signal fails the test (the machine shows a crash dialog
/// for them, and no spec row ends a command by one).
pub fn run(cwd: &Path, args: &[&str]) -> Out {
    let out = Command::new(ONSA).args(args).current_dir(cwd).output().expect("run onsa");
    Out {
        code: out.status.code().unwrap_or_else(|| panic!("onsa {args:?} ended by a signal: {out:?}")),
        stdout: String::from_utf8(out.stdout).expect("utf-8 standard output"),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// The whole standard output is one JSON value, and it is an object (§18.1).
pub fn doc_of(out: &Out) -> Value {
    let v: Value = serde_json::from_str(&out.stdout)
        .unwrap_or_else(|e| panic!("the standard output is not one JSON value ({e}): {:?}", out.stdout));
    assert!(v.is_object(), "the document is not an object: {v}");
    v
}

pub fn array_of<'a>(doc: &'a Value, key: &str) -> &'a Vec<Value> {
    doc.get(key)
        .unwrap_or_else(|| panic!("no `{key}` key: {doc}"))
        .as_array()
        .unwrap_or_else(|| panic!("`{key}` is not an array: {doc}"))
}

pub fn diagnostics(doc: &Value) -> &Vec<Value> {
    array_of(doc, "diagnostics")
}

pub fn tests_of(doc: &Value) -> &Vec<Value> {
    array_of(doc, "tests")
}

pub fn str_of<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or_else(|| panic!("no string `{key}` in {v}"))
}

pub fn int_of(v: &Value, key: &str) -> u64 {
    v.get(key).and_then(Value::as_u64).unwrap_or_else(|| panic!("no integer `{key}` in {v}"))
}

/// `(module, name)` of every record of `tests`, in the order of the array.
pub fn identities(doc: &Value) -> Vec<(String, String)> {
    tests_of(doc).iter().map(|t| (str_of(t, "module").to_string(), str_of(t, "name").to_string())).collect()
}

/// `onsa test --json <args>` run in `cwd`: the output and its document.
pub fn test_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["test", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

/// The result lines of the text output: the lines that start with `test ` (the lines of a
/// diagnostic and a summary are not fixed, so they are left out).
pub fn result_lines(out: &Out) -> Vec<String> {
    out.stdout.lines().filter(|l| l.starts_with("test ")).map(str::to_string).collect()
}

/// The result lines, sorted (the order of the lines is not fixed for the text output).
pub fn sorted_result_lines(out: &Out) -> Vec<String> {
    let mut v = result_lines(out);
    v.sort();
    v
}

/// A `span` object: the five keys, each a number, lines and columns from 1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    pub file: String,
    pub line: u64,
    pub col: u64,
    pub end_line: u64,
    pub end_col: u64,
}

pub fn span_of(v: &Value) -> Span {
    let o = v.as_object().unwrap_or_else(|| panic!("`span` is not an object: {v}"));
    let int = |k: &str| -> u64 {
        o.get(k)
            .unwrap_or_else(|| panic!("`span` has no `{k}`: {v}"))
            .as_u64()
            .unwrap_or_else(|| panic!("`span.{k}` is not a non-negative integer: {v}"))
    };
    let file = o.get("file").and_then(Value::as_str).unwrap_or_else(|| panic!("`span.file` is not a string: {v}"));
    let s = Span {
        file: file.to_string(),
        line: int("line"),
        col: int("col"),
        end_line: int("end_line"),
        end_col: int("end_col"),
    };
    assert!(s.line >= 1 && s.col >= 1 && s.end_line >= 1 && s.end_col >= 1, "lines and columns count from 1: {v}");
    assert!((s.end_line, s.end_col) >= (s.line, s.col), "the end is before the start: {v}");
    s
}

pub fn span(file: &str, line: u64, col: u64, end_line: u64, end_col: u64) -> Span {
    Span { file: file.to_string(), line, col, end_line, end_col }
}

/// The record of `tests` for `(module, name)`; exactly one.
pub fn record<'a>(doc: &'a Value, module: &str, name: &str) -> &'a Value {
    let hits: Vec<&Value> =
        tests_of(doc).iter().filter(|t| str_of(t, "module") == module && str_of(t, "name") == name).collect();
    assert_eq!(hits.len(), 1, "records of {module:?} {name:?} in {doc}");
    hits[0]
}

/// The `failure` of a failed record: its `status` is `failed` and `failure` is an object.
pub fn failure_of(rec: &Value) -> &Value {
    assert_eq!(str_of(rec, "status"), "failed", "{rec}");
    let f = rec.get("failure").unwrap_or_else(|| panic!("a failed record has a `failure`: {rec}"));
    assert!(f.is_object(), "{rec}");
    f
}

/// The spans of `failure.calls`, innermost first.
pub fn call_spans(failure: &Value) -> Vec<Span> {
    array_of(failure, "calls")
        .iter()
        .map(|c| span_of(c.get("span").unwrap_or_else(|| panic!("a call has a `span`: {c}"))))
        .collect()
}
