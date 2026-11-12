//! The common harness of the integration tests of the `onsa` command (the modules of `main.rs`): a
//! scratch package, one run of the built `onsa`, and readers of the document `onsa test --json` prints
//! (spec §18.1) and of the result lines of the text output (`spec/tools.md` §4). The formatter called in
//! the process is in `fmt`, the sweeps of the `use` lines in `sweep`; a new test reads these and does not
//! write a harness of its own.

#![allow(dead_code)]

pub mod fmt;
pub mod sweep;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

pub const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

/// A scratch directory; `pkg` has a manifest, `bare` has none.
pub struct Dir(pub PathBuf);

impl Dir {
    pub fn bare(tag: &str) -> Dir {
        // A running number in the name: two tests of one process with the same tag (or a tag that is
        // the start of another) must not remove each other's directory.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_test_cmd_{}_{n}_{tag}", std::process::id()));
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

    /// Write the file `rel` (text or bytes; its directories made) and give its path as an argument.
    pub fn file(&self, rel: &str, bytes: &(impl AsRef<[u8]> + ?Sized)) -> String {
        let p = self.0.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, bytes).unwrap();
        p.to_string_lossy().into_owned()
    }

    /// The path of `rel` under the directory as an argument (nothing is written).
    pub fn path(&self, rel: &str) -> String {
        self.0.join(rel).to_string_lossy().into_owned()
    }

    /// The names of the entries of the directory itself, sorted.
    pub fn names(&self) -> Vec<String> {
        let mut v: Vec<String> = std::fs::read_dir(&self.0)
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        v.sort();
        v
    }
}

/// The directory goes when the test ends, a failing one too (the drop runs as the panic unwinds). A test
/// that took the permissions off the directory or a directory in it (`fmt_write.rs`) gets them back first.
impl Drop for Dir {
    fn drop(&mut self) {
        if std::fs::remove_dir_all(&self.0).is_ok() {
            return;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let sub = std::fs::read_dir(&self.0).into_iter().flatten().flatten().map(|e| e.path());
            for d in sub.filter(|p| p.is_dir()).chain([self.0.clone()]) {
                let _ = std::fs::set_permissions(&d, std::fs::Permissions::from_mode(0o755));
            }
        }
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// One run of `onsa <args>` in the directory of the test process (the paths of `args` are absolute).
pub fn onsa(args: &[&str]) -> Output {
    Command::new(ONSA).args(args).output().expect("run onsa")
}

/// The exit code of a run; a signal fails the test.
pub fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

/// The exit code (0 or 1) and the diagnostics of `onsa check --json <path>`.
pub fn check_coded(path: &str) -> (i32, Vec<Value>) {
    let out = onsa(&["check", "--json", path]);
    let c = code(&out);
    assert!(c == 0 || c == 1, "onsa check {path}: exit code {c} (stderr: {})", String::from_utf8_lossy(&out.stderr));
    let text = String::from_utf8(out.stdout).expect("utf-8 output");
    let v: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("no JSON ({e}): {text}"));
    (c, v["diagnostics"].as_array().unwrap_or_else(|| panic!("no `diagnostics` array: {v}")).clone())
}

/// The diagnostics of `onsa check --json <path>` (exit code 0 or 1).
pub fn check(path: &str) -> Vec<Value> {
    check_coded(path).1
}

/// The `code` of a diagnostic.
pub fn code_of(d: &Value) -> &str {
    str_of(d, "code")
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

/// One run of `onsa <args>` in `cwd` that is killed (and fails the test) when it has not ended in
/// `secs` seconds. For inputs that could make a command wait for ever, such as a FIFO in a tree.
pub fn run_limited(cwd: &Path, args: &[&str], secs: u64) -> Out {
    use std::process::Stdio;
    use std::time::{Duration, Instant};
    let mut child = Command::new(ONSA)
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run onsa");
    let start = Instant::now();
    loop {
        if child.try_wait().expect("wait for onsa").is_some() {
            break;
        }
        if start.elapsed() > Duration::from_secs(secs) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("onsa {args:?} did not end in {secs} seconds (killed)");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let out = child.wait_with_output().expect("collect the output of onsa");
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

/// The codes of the diagnostics of a document, as a set (to compare with [`set`]).
pub fn codes(doc: &Value) -> std::collections::BTreeSet<String> {
    diagnostics(doc).iter().map(|d| code_of(d).to_string()).collect()
}

pub fn set(items: &[&str]) -> std::collections::BTreeSet<String> {
    items.iter().map(|c| c.to_string()).collect()
}

/// The candidates of a diagnostic: `fixes`, written out even when empty (§18.1).
pub fn fixes_of(d: &Value) -> Vec<&Value> {
    array_of(d, "fixes").iter().collect()
}

/// The notes of a diagnostic: `notes`, written out even when empty (§18.1).
pub fn notes_of(d: &Value) -> Vec<&Value> {
    array_of(d, "notes").iter().collect()
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

/// A position of a `span`: (line, column), from 1, the column in characters (§18.1).
pub type Pos = (usize, usize);

/// One edit of a candidate (an entry of `edits`, §18.1): the file and the range of its `span`, and `replace`.
pub struct Edit {
    pub file: String,
    pub start: Pos,
    pub end: Pos,
    pub replace: String,
}

/// The edits of one candidate (a `fixes` entry), in the order of the document.
pub fn edits_of(fix: &Value) -> Vec<Edit> {
    let pos = |s: &Value, l: &str, c: &str| -> Pos {
        let get = |k: &str| usize::try_from(int_of(s, k)).unwrap();
        (get(l), get(c))
    };
    let edit = |e: &Value| Edit {
        file: str_of(&e["span"], "file").to_string(),
        start: pos(&e["span"], "line", "col"),
        end: pos(&e["span"], "end_line", "end_col"),
        replace: str_of(e, "replace").to_string(),
    };
    array_of(fix, "edits").iter().map(edit).collect()
}

/// The byte offset of a position in `text`. A position out of the text fails the test, as an error of the
/// output that a rounding would hide: the last position of a line is the column after its last character,
/// and that of a text that ends with a line break is the column 1 of the line after it.
pub fn offset(text: &str, (line, col): Pos) -> usize {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n').unwrap_or_else(|| panic!("line {line} is past the end of the text")) + 1;
    }
    let rest = &text[start..];
    let line_len = rest.find('\n').unwrap_or(rest.len());
    match rest[..line_len].char_indices().nth(col - 1) {
        Some((i, _)) => start + i,
        None => {
            assert_eq!(rest[..line_len].chars().count() + 1, col, "column {col} is past the end of line {line}");
            start + line_len
        }
    }
}

/// The text each edit replaces, in the order of the edits.
pub fn replaced_texts(text: &str, edits: &[Edit]) -> Vec<String> {
    edits.iter().map(|e| text[offset(text, e.start)..offset(text, e.end)].to_string()).collect()
}

/// `text` after the edits of one candidate, applied together (§18.1): edits that overlap fail the test, and
/// insertions at one place go in the order of the edits.
pub fn apply(text: &str, edits: &[Edit]) -> String {
    let mut spans: Vec<(usize, usize, &str)> =
        edits.iter().map(|e| (offset(text, e.start), offset(text, e.end), e.replace.as_str())).collect();
    spans.sort_by_key(|&(a, b, _)| (a, b));
    for w in spans.windows(2) {
        assert!(w[0].1 <= w[1].0, "edits of one candidate overlap: {:?} and {:?}", w[0], w[1]);
    }
    let mut out = text.to_string();
    for &(a, b, r) in spans.iter().rev() {
        out.replace_range(a..b, r);
    }
    out
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
