//! The nesting depth limit through the built `onsa` (spec §2.5, §18.1, §18.2; S-183, W3-14).
//!
//! The syntax tree may be 256 deep. Deeper input is E0006 (a syntax-stage diagnostic): `check`
//! reports it with exit code 1 and a JSON diagnostic, the process does not die of a stack overflow
//! (exit 101 or a signal), and `fmt` / `diff --ast` leave a file with a syntax diagnostic alone
//! (exit 2). Only the cases far from the limit are used: the spec does not say how many tree levels
//! one step costs, so the exact boundary is not tested. The inputs stay under 300 steps of
//! nesting, so even an implementation without the limit does not overflow its stack on them.
//!
//! The tests of the deep inputs follow `tests/pending.toml` while the limit is not there: as
//! long as the list holds the `diag-code` item `E0006`, the body must FAIL (the listed item must
//! still be pending), and it is removed together with the item (W3-14). A process that ends by a
//! signal fails the test either way.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

/// Steps of nesting in the deep inputs: well over 256 and under the 300 the machine tolerates.
const DEEP: usize = 290;
const DEEP_CALLS: usize = 280;
/// Steps in the inputs that must be accepted: well under 256 under any way of counting.
const SHALLOW: usize = 180;

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_nesting_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn onsa(args: &[&str]) -> Output {
    let out = Command::new(ONSA).args(args).output().expect("run onsa");
    // A signal (a stack overflow) is never an acceptable end, listed as pending or not.
    assert!(out.status.code().is_some(), "onsa {args:?} ended by a signal: {out:?}");
    out
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap()
}

fn text(out: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

// ---- inputs

fn paren(n: usize) -> String {
    format!("{}1{}", "(".repeat(n), ")".repeat(n))
}

fn sum_chain(n: usize) -> String {
    vec!["1"; n].join(" + ")
}

fn nest_if(n: usize) -> String {
    format!("{}1{}", "if c { ".repeat(n), " } else { 0 }".repeat(n))
}

fn else_if_chain(n: usize) -> String {
    let mut s = String::from("if x == 0 { 0 }");
    for i in 1..n {
        s.push_str(&format!(" else if x == {i} {{ {i} }}"));
    }
    s.push_str(" else { -1 }");
    s
}

fn option_type(n: usize) -> String {
    format!("{}I32{}", "Option[".repeat(n), "]".repeat(n))
}

/// One line: `pub fn <name>(<params>) -> I32 { <body> }`.
fn one_line(name: &str, params: &str, ret: &str, body: &str) -> String {
    format!("pub fn {name}({params}) -> {ret} {{ {body} }}\n")
}

// ---- JSON

fn diagnostics(out: &Output) -> Result<Vec<(String, u64)>, String> {
    let v: serde_json::Value = serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("`check --json` printed no JSON ({e}): {}", text(out)))?;
    // A bare array (today) or an object with `diagnostics` (S-215, W3-16).
    let all = match (&v, v.get("diagnostics")) {
        (serde_json::Value::Array(a), _) => a,
        (_, Some(serde_json::Value::Array(a))) => a,
        _ => return Err(format!("the JSON has no diagnostics: {v}")),
    };
    Ok(all
        .iter()
        .map(|d| {
            let code = d["code"].as_str().unwrap_or("?").to_string();
            let line = d["span"]["line"].as_u64().unwrap_or(0);
            (code, line)
        })
        .collect())
}

// ---- the pending protocol

/// Whether `tests/pending.toml` still lists the `diag-code` item `E0006`.
fn e0006_is_pending() -> bool {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let list = std::fs::read_to_string(root.join("tests/pending.toml")).unwrap();
    list.split("[[pending]]").any(|block| {
        let has = |line: &str| block.lines().any(|l| l.trim() == line);
        has("kind = \"diag-code\"") && has("target = \"E0006\"")
    })
}

/// Run a body that holds only while the limit exists. While E0006 is listed pending the body must
/// fail (the list is then right); once it is removed from the list the body must pass.
fn limit_test(what: &str, body: impl FnOnce() -> Result<(), String>) {
    let result = body();
    if e0006_is_pending() {
        assert!(
            result.is_err(),
            "{what}: the behaviour is there, but tests/pending.toml still lists the diag-code E0006: remove the item (W3-14)"
        );
    } else if let Err(e) = result {
        panic!("{what}: {e}");
    }
}

macro_rules! ensure {
    ($cond:expr, $($msg:tt)+) => {
        if !$cond {
            return Err(format!($($msg)+));
        }
    };
}

// ---- tests

/// Far from the limit, everything is accepted, with no diagnostic (so the limit is not too low).
#[test]
fn shallow_inputs_are_accepted() {
    let d = Dir::new("shallow");
    let files = [
        d.file("paren.onsa", &one_line("f", "", "I32", &paren(SHALLOW))),
        d.file("sum.onsa", &one_line("f", "", "I32", &sum_chain(SHALLOW))),
        d.file("if.onsa", &one_line("f", "c: Bool", "I32", &nest_if(50))),
        d.file("else_if.onsa", &one_line("f", "x: I32", "I32", &else_if_chain(100))),
        d.file("type.onsa", &one_line("f", &format!("x: {}", option_type(80)), "I32", "1")),
    ];
    for f in &files {
        let out = onsa(&["check", f]);
        assert_eq!(code(&out), 0, "check {f}: {}", text(&out));
        let out = onsa(&["check", "--json", f]);
        assert_eq!(code(&out), 0, "check --json {f}: {}", text(&out));
        assert_eq!(diagnostics(&out), Ok(vec![]), "check --json {f}: {}", text(&out));
    }
    // A long chain in the canonical form is left as it is by `fmt --check`.
    let canonical = d.file("canonical.onsa", &format!("pub fn f() -> I32 {{\n  {}\n}}\n", sum_chain(SHALLOW)));
    let out = onsa(&["fmt", "--check", &canonical]);
    assert_eq!(code(&out), 0, "fmt --check: {}", text(&out));
}

/// A deep input is a diagnostic: exit 1, E0006 in the JSON on the line of the unit, nothing else.
#[test]
fn deep_inputs_are_e0006() {
    limit_test("deep inputs", || {
        let d = Dir::new("deep");
        let inputs = [
            ("paren", one_line("f", "", "I32", &paren(DEEP))),
            ("sum", one_line("f", "", "I32", &sum_chain(DEEP))),
            ("if", one_line("f", "c: Bool", "I32", &nest_if(DEEP_CALLS))),
            ("else_if", one_line("f", "x: I32", "I32", &else_if_chain(DEEP))),
            ("type", one_line("f", &format!("x: {}", option_type(DEEP_CALLS)), "I32", "1")),
        ];
        for (name, src) in &inputs {
            let f = d.file(&format!("{name}.onsa"), src);
            let out = onsa(&["check", "--json", &f]);
            ensure!(code(&out) == 1, "{name}: check --json exits {} (want 1): {}", code(&out), text(&out));
            let diags = diagnostics(&out)?;
            ensure!(
                diags == vec![("E0006".to_string(), 1)],
                "{name}: diagnostics {diags:?} (want one E0006 on line 1)"
            );
            let out = onsa(&["check", &f]);
            ensure!(code(&out) == 1, "{name}: check exits {} (want 1)", code(&out));
            ensure!(text(&out).contains("E0006"), "{name}: the text output names no E0006: {}", text(&out));
        }
        Ok(())
    });
}

/// A unit with a deep part has one E0006; the other units are checked as usual (§18.1).
#[test]
fn units_are_independent() {
    limit_test("independent units", || {
        let d = Dir::new("units");
        let mut src = String::new();
        src.push_str(&one_line("a", "", "I32", &paren(DEEP))); // line 1: E0006
        src.push_str(&one_line("b", "", "I32", "1 + 1")); // line 2: fine
        src.push_str(&one_line("c", "", "I32", &sum_chain(DEEP))); // line 3: E0006
        src.push_str(&one_line("d", "", "I32", "missing")); // line 4: E0302
        // Two deep parts in one unit (the first is on the header's line): one E0006.
        src.push_str(&format!(
            "pub fn e() -> I32 {{ let a = {}\n  let b = {}\n  a + b\n}}\n",
            paren(DEEP),
            paren(DEEP)
        )); // lines 5-8: one E0006 on line 5
        let f = d.file("units.onsa", &src);
        let out = onsa(&["check", "--json", &f]);
        ensure!(code(&out) == 1, "check --json exits {} (want 1): {}", code(&out), text(&out));
        let mut diags = diagnostics(&out)?;
        diags.sort_by_key(|(_, line)| *line);
        let want: Vec<(String, u64)> =
            vec![("E0006".into(), 1), ("E0006".into(), 3), ("E0302".into(), 4), ("E0006".into(), 5)];
        ensure!(diags == want, "diagnostics {diags:?} (want {want:?})");
        Ok(())
    });
}

/// `fmt` and `diff --ast` do not touch or compare a file with a syntax diagnostic, E0006 included
/// (§18.2). The other files given with it are still formatted.
#[test]
fn fmt_leaves_a_deep_file_alone() {
    limit_test("fmt of a deep file", || {
        let d = Dir::new("fmt");
        let deep_src = one_line("f", "", "I32", &paren(DEEP));
        let deep = d.file("deep.onsa", &deep_src);
        let ok = d.file("ok.onsa", "pub fn f() -> I32 {\n  1\n}\n");
        // The author's newline after `{` makes the block multi-line; fmt keeps the
        // author's newlines (docs/onsa-tools.md §3.2).
        let ugly = d.file("ugly.onsa", "pub fn g()->I32{\n1\n}\n");

        let out = onsa(&["fmt", &deep]);
        ensure!(code(&out) == 2, "fmt exits {} (want 2): {}", code(&out), text(&out));
        ensure!(text(&out).contains("E0006"), "fmt names no E0006: {}", text(&out));
        ensure!(std::fs::read_to_string(&deep).unwrap() == deep_src, "fmt rewrote the deep file");

        let out = onsa(&["fmt", "--check", &deep]);
        ensure!(code(&out) == 2, "fmt --check exits {} (want 2): {}", code(&out), text(&out));

        let out = onsa(&["diff", "--ast", &ok, &deep]);
        ensure!(code(&out) == 2, "diff --ast exits {} (want 2): {}", code(&out), text(&out));

        let out = onsa(&["fmt", &deep, &ugly]);
        ensure!(code(&out) == 2, "fmt of two files exits {} (want 2): {}", code(&out), text(&out));
        ensure!(std::fs::read_to_string(&deep).unwrap() == deep_src, "fmt rewrote the deep file (two files)");
        ensure!(
            std::fs::read_to_string(&ugly).unwrap() == "pub fn g() -> I32 {\n  1\n}\n",
            "the other file was not formatted: {}",
            std::fs::read_to_string(&ugly).unwrap()
        );
        Ok(())
    });
}
