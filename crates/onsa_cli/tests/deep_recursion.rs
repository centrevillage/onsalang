//! A deep recursion in `onsa test` ends in an exit code, not a signal (W2-04/t,
//! rewritten for S-222 in W2-04/t2).
//!
//! Spec §12.5 (when the stack runs out): the interpreter (`onsa test`) and the
//! compile time evaluation (a `const` initializer, §6.6) have the same fixed
//! limit 128 for the depth of calls. The depth is counted from the entry of the
//! evaluation (the body of a `test`, one initializer) by the number of nested
//! calls, a call in a tail position included, and reading a `const` is not a
//! call: a `const` is evaluated from its own entry. A call beyond the limit is a
//! panic, and a panic of a compile time evaluation is E0419 at the position of
//! the expression (§6.6). Spec §9.2: a panic in a test fails that test. Spec
//! §18.2: a failed test is exit code 1 (`onsa test` found a problem), and the
//! other tests of the file run. The result lines are
//! `test <module> "<name>" ok` / `test <module> "<name>" failed at <file>:<line>:
//! <message>` (spec §9, the section of `test`); this file looks only for the
//! quoted name and the word at the end (`ok`) or after it (`failed`), not for the
//! module part or the message, which the spec does not fix for a depth panic.
//!
//! `dive(n)` from a test body makes n + 1 nested calls, so `dive(127)` is
//! depth 128 and passes, and `dive(128)` is depth 129 and fails. A far deep call
//! here is 300 levels (not more: the limit, not the stack, must end it), and a
//! shallow call is at most 50.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_deep_recursion_{}_{tag}", std::process::id()));
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
    Command::new(ONSA).args(args).output().expect("run onsa")
}

/// The exit code; a signal is a failure of the test, with the output.
fn code(args: &[&str]) -> (i32, String) {
    let out = onsa(args);
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    match out.status.code() {
        Some(c) => (c, text),
        None => panic!("onsa {args:?} ended by a signal ({:?}), not by an exit code:\n{text}", out.status),
    }
}

/// The result line of the test `name`: the line that holds `"<name>"` quoted.
fn line_of<'a>(text: &'a str, name: &str) -> &'a str {
    let quoted = format!("\"{name}\"");
    let mut hits = text.lines().filter(|l| l.contains(&quoted) && l.trim_start().starts_with("test "));
    let first = hits.next().unwrap_or_else(|| panic!("no result line for test {name:?} in:\n{text}"));
    assert!(hits.next().is_none(), "two result lines for test {name:?} in:\n{text}");
    first
}

fn assert_ok(text: &str, name: &str) {
    let line = line_of(text, name);
    assert!(line.trim_end().ends_with(" ok"), "test {name:?} should be ok: {line}");
}

fn assert_failed(text: &str, name: &str) {
    let line = line_of(text, name);
    assert!(line.contains(" failed"), "test {name:?} should be failed: {line}");
}

/// Each program: a shallow control, the deep test, a shallow test after it.
/// The names are `control`, `deep` and `after`.
fn program(defs: &str, shallow: &str, deep: &str) -> String {
    format!(
        "{defs}\n\ntest \"control\" {{\n{shallow}\n}}\n\ntest \"deep\" {{\n{deep}\n}}\n\ntest \"after\" {{\n{shallow}\n}}\n"
    )
}

const DIVE: &str = "fn dive(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    1 + dive(n - 1)
  }
}
";

const TAIL: &str = "fn dive_tail(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    dive_tail(n - 1)
  }
}
";

const MUTUAL: &str = "fn is_even(n: U32) -> Bool {
  if n == 0 {
    true
  } else {
    is_odd(n - 1)
  }
}

fn is_odd(n: U32) -> Bool {
  if n == 0 {
    false
  } else {
    is_even(n - 1)
  }
}
";

const GENERIC: &str = "fn hold[T: Copy](x: T, n: U32) -> T {
  if n == 0 {
    x
  } else {
    hold(x, n - 1)
  }
}
";

const METHOD: &str = "pub struct Counter {
  base: U32,
}

impl Counter {
  pub fn down(self, n: U32) -> U32 {
    if n == 0 {
      self.base
    } else {
      self.down(n - 1)
    }
  }
}
";

const INOUT: &str = "fn dive_inout(inout x: U32, n: U32) {
  if n > 0 {
    x = 1
    dive_inout(inout x, n - 1)
  }
}
";

/// (tag, definitions, body of the shallow tests, body of the test that calls at
/// the depth `d`: `d` levels, so `d + 1` nested calls for every shape).
fn shapes(d: u32) -> Vec<(&'static str, &'static str, &'static str, String)> {
    vec![
        ("direct", DIVE, "  assert dive(50) == 50", format!("  assert dive({d}) == {d}")),
        ("tail", TAIL, "  assert dive_tail(50) == 0", format!("  assert dive_tail({d}) == 0")),
        ("mutual", MUTUAL, "  assert is_even(50)", format!("  assert is_even({d}) == {}", d % 2 == 0)),
        (
            "generic",
            GENERIC,
            "  let x: F32 = 1.5\n  assert hold(x, 50) == 1.5",
            format!("  let x: F32 = 1.5\n  assert hold(x, {d}) == 1.5"),
        ),
        (
            "method",
            METHOD,
            "  let c = Counter { base: 4 }\n  assert c.down(50) == 4",
            format!("  let c = Counter {{ base: 4 }}\n  assert c.down({d}) == 4"),
        ),
        (
            "inout",
            INOUT,
            "  var x: U32 = 0\n  dive_inout(inout x, 50)\n  assert x == 1",
            format!("  var x: U32 = 0\n  dive_inout(inout x, {d})\n  assert x == 1"),
        ),
    ]
}

/// A recursion beyond the limit fails its test, the process ends by exit code
/// 1, and the tests before and after it run and pass (spec §12.5, §9.2, §18.2).
#[test]
fn a_deep_recursion_fails_the_test_and_exits_with_1() {
    let d = Dir::new("shapes");
    for (tag, defs, shallow, deep) in shapes(300) {
        let f = d.file(&format!("{tag}.onsa"), &program(defs, shallow, &deep));
        let (c, text) = code(&["test", &f]);
        assert_eq!(c, 1, "{tag}: a failed test is exit code 1:\n{text}");
        assert_ok(&text, "control");
        assert_failed(&text, "deep");
        assert_ok(&text, "after");
    }
}

/// The boundary of every shape: 128 nested calls (`n = 127`) pass, 129 (`n =
/// 128`) fail the test (spec §12.5: the limit is 128, the depth counted from
/// the body of the test, the tail call counted).
#[test]
fn the_limit_is_128_nested_calls_for_every_shape() {
    let d = Dir::new("boundary");
    for (tag, defs, shallow, deep) in shapes(127) {
        let f = d.file(&format!("{tag}_127.onsa"), &program(defs, shallow, &deep));
        let (c, text) = code(&["test", &f]);
        assert_eq!(c, 0, "{tag}: 128 nested calls pass:\n{text}");
        assert_ok(&text, "deep");
    }
    for (tag, defs, shallow, deep) in shapes(128) {
        let f = d.file(&format!("{tag}_128.onsa"), &program(defs, shallow, &deep));
        let (c, text) = code(&["test", &f]);
        assert_eq!(c, 1, "{tag}: 129 nested calls fail the test:\n{text}");
        assert_ok(&text, "control");
        assert_failed(&text, "deep");
        assert_ok(&text, "after");
    }
}

/// `--filter` runs one test of the file: the deep one is exit code 1, the
/// shallow ones 0 (spec §18.2: the filter is a part of the full name).
#[test]
fn filter_selects_the_deep_test_or_the_others() {
    let d = Dir::new("filter");
    let (_, defs, shallow, deep) = shapes(300).remove(0);
    let f = d.file("direct.onsa", &program(defs, shallow, &deep));
    let (c, text) = code(&["test", "--filter", "deep", &f]);
    assert_eq!(c, 1, "the deep test alone:\n{text}");
    assert_failed(&text, "deep");
    let (c, text) = code(&["test", "--filter", "control", &f]);
    assert_eq!(c, 0, "the control alone:\n{text}");
    assert_ok(&text, "control");
}

/// Several deep tests in one file: each fails, none ends the process, and the
/// tests between them pass (the depth count goes back with each test).
#[test]
fn several_deep_tests_in_one_file() {
    let d = Dir::new("several");
    let text = format!(
        "{DIVE}
test \"deep one\" {{
  assert dive(300) == 300
}}

test \"shallow one\" {{
  assert dive(127) == 127
}}

test \"deep two\" {{
  assert dive(128) == 128
}}

test \"shallow two\" {{
  var i: U32 = 0
  while i < 1000 {{
    assert dive(127) == 127
    i = i + 1
  }}
}}

test \"deep three\" {{
  assert dive(300) == 300
}}
"
    );
    let f = d.file("several.onsa", &text);
    let (c, out) = code(&["test", &f]);
    assert_eq!(c, 1, "{out}");
    for name in ["deep one", "deep two", "deep three"] {
        assert_failed(&out, name);
    }
    for name in ["shallow one", "shallow two"] {
        assert_ok(&out, name);
    }
}

/// A file whose recursion stays shallow passes: exit code 0 (the limit does not
/// turn a normal recursion into a failure).
#[test]
fn a_shallow_recursion_exits_with_0() {
    let d = Dir::new("shallow");
    for (tag, defs, shallow, _) in shapes(50) {
        let src = format!("{defs}\n\ntest \"shallow\" {{\n{shallow}\n}}\n");
        let f = d.file(&format!("{tag}.onsa"), &src);
        let (c, text) = code(&["test", &f]);
        assert_eq!(c, 0, "{tag}:\n{text}");
        assert_ok(&text, "shallow");
    }
}

/// `--json`: the deep failure is reported in JSON on standard output with exit
/// code 1 (spec §18.2: `--json` prints JSON at exit codes 0 and 1), not by a
/// signal.
#[test]
fn json_output_of_a_deep_recursion() {
    let d = Dir::new("json");
    let (_, defs, shallow, deep) = shapes(300).remove(0);
    let f = d.file("direct.onsa", &program(defs, shallow, &deep));
    let out = onsa(&["test", "--json", &f]);
    assert_eq!(out.status.code(), Some(1), "ended by {:?}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"deep\""), "the failed test is named in the JSON:\n{stdout}");
    assert!(stdout.contains("\"kind\""), "the spec adds a `kind` field to the diagnostic form:\n{stdout}");
}

// ------------------------------------------------------------------- `const`

/// A package `<name>` of one module `m`: the manifest, `m.onsa` with `body`,
/// and the exported function `m.read`. Returns the directory.
fn package(d: &Dir, name: &str, body: &str) -> String {
    let dir = d.0.join(name);
    std::fs::create_dir_all(&dir).unwrap();
    let manifest = format!(
        "[package]\nname = \"{name}\"\nedition = \"2026\"\n\n[export]\nprefix = \"p_\"\nfns = [\"m.read\"]\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"trap\"\nprovides = []\n"
    );
    std::fs::write(dir.join("onsa.toml"), manifest).unwrap();
    std::fs::write(dir.join("m.onsa"), body).unwrap();
    dir.to_string_lossy().into_owned()
}

/// `onsa build` of the package into its own output directory.
fn build(pkg: &str) -> (i32, String) {
    let out = format!("{pkg}/out");
    code(&["build", "--target", "host", "--out", &out, pkg])
}

/// A package whose only `const` is `C = dive(n)`, read by the exported function
/// and by one test.
fn const_package(d: &Dir, name: &str, n: u32) -> String {
    let body = format!(
        "{DIVE}
const C: U32 = dive({n})

pub fn read() -> U32 {{
  C
}}

test \"reads it\" {{
  assert read() == {n}
}}
"
    );
    package(d, name, &body)
}

/// A deep recursion in a `const` initializer: whatever else is decided, the
/// process ends by an exit code, never a signal (`code` fails on one) and never
/// 101 (an internal error). `onsa check` may or may not evaluate the constant
/// (S-222 leaves the command to W9-03); `onsa test` is exit code 1: either the
/// E0419 of the initializer or the failure of the test that reads it.
#[test]
fn a_deep_recursion_in_a_const_ends_by_an_exit_code() {
    let d = Dir::new("const");
    let src = format!(
        "{DIVE}
const DEEP: U32 = dive(300)

test \"uses the constant\" {{
  assert DEEP == 300
}}
"
    );
    let f = d.file("constdeep.onsa", &src);
    let (c, text) = code(&["check", &f]);
    assert!(matches!(c, 0..=2), "onsa check exited with {c}:\n{text}");
    let (c, text) = code(&["test", &f]);
    assert_eq!(c, 1, "onsa test:\n{text}");
}

/// The same initializer passes or fails the same way in `onsa test` and in
/// `onsa build` (spec §12.5: the interpreter and the compile time evaluation
/// have one limit, counted from the entry of the evaluation, in every build):
/// `dive(127)` is 128 nested calls and passes in both, `dive(128)` is 129 and
/// fails in both (exit code 1: a diagnostic, §18.2).
#[test]
fn a_const_passes_or_fails_the_same_in_test_and_in_build() {
    let d = Dir::new("const_agree");
    let ok = const_package(&d, "okpkg", 127);
    let (c, text) = code(&["test", &ok]);
    assert_eq!(c, 0, "test, 128 nested calls:\n{text}");
    let (c, text) = build(&ok);
    assert_eq!(c, 0, "build, 128 nested calls:\n{text}");

    let over = const_package(&d, "overpkg", 128);
    let (c, text) = code(&["test", &over]);
    assert_eq!(c, 1, "test, 129 nested calls:\n{text}");
    let (c, text) = build(&over);
    assert_eq!(c, 1, "build, 129 nested calls:\n{text}");
}

/// A `const` has one value wherever it is read, whichever test reads it first,
/// and under `--filter` (spec §12.5: a `const` is evaluated from its own entry;
/// §11.3: the same result however the expression is split). `C = dive(127)` is
/// 128 nested calls from its own entry; the readers are 100 deep, so a depth
/// inherited from the reader would be over the limit. This is the case of
/// W2-04/b (NOTES-W2-04-b.md, 1): the old result depended on the order.
#[test]
fn a_const_is_the_same_wherever_and_whenever_it_is_read() {
    let d = Dir::new("const_order");
    let defs = format!(
        "{DIVE}
const C: U32 = dive(127)

fn user(n: U32) -> U32 {{
  if n == 0 {{
    C
  }} else {{
    user(n - 1)
  }}
}}
"
    );
    let tests = [
        ("a deep user first", "  assert user(100) == 127"),
        ("b top level", "  assert C == 127"),
        ("c deep user again", "  assert user(100) == 127"),
        ("d user at the boundary", "  assert user(127) == 127"),
    ];
    let orders: [[usize; 4]; 6] = [[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [3, 2, 1, 0], [2, 3, 0, 1], [3, 0, 1, 2]];
    for (i, order) in orders.iter().enumerate() {
        let mut src = defs.clone();
        for &k in order {
            src.push_str(&format!("\ntest \"{}\" {{\n{}\n}}\n", tests[k].0, tests[k].1));
        }
        let f = d.file(&format!("order{i}.onsa"), &src);
        let (c, text) = code(&["test", &f]);
        assert_eq!(c, 0, "order {order:?}:\n{text}");
        for (name, _) in tests {
            assert_ok(&text, name);
        }
        // Each test alone, as a filter selects it: the same result.
        for (name, _) in tests {
            let (c, text) = code(&["test", "--filter", name, &f]);
            assert_eq!(c, 0, "order {order:?}, only {name:?}:\n{text}");
            assert_ok(&text, name);
        }
    }
}

/// The same program in a build: the exported function that reads the `const`
/// from a recursion 100 deep, and the test, in a package.
#[test]
fn a_const_read_from_a_deep_call_builds_and_tests() {
    let d = Dir::new("const_deep_build");
    let body = format!(
        "{DIVE}
const C: U32 = dive(127)

fn user(n: U32) -> U32 {{
  if n == 0 {{
    C
  }} else {{
    user(n - 1)
  }}
}}

pub fn read() -> U32 {{
  user(100)
}}

test \"reads it deep\" {{
  assert read() == 127
}}
"
    );
    let pkg = package(&d, "deepread", &body);
    let (c, text) = code(&["test", &pkg]);
    assert_eq!(c, 0, "{text}");
    let (c, text) = build(&pkg);
    assert_eq!(c, 0, "{text}");
}

/// A `const` that reads a `const` is not a call: a chain of 300 constants is
/// not 300 deep. The chain length stays at 300 (the evaluation of the chain
/// uses the stack of the evaluator, which the spec does not bound; 300 is
/// within what every build handles).
#[test]
fn a_chain_of_300_constants_is_not_a_deep_call() {
    let d = Dir::new("const_chain");
    let n = 300;
    let mut body = String::from("const L0: U32 = 1\n");
    for i in 1..n {
        body.push_str(&format!("const L{i}: U32 = L{} + 1\n", i - 1));
    }
    body.push_str(&format!(
        "\npub fn read() -> U32 {{\n  L{}\n}}\n\ntest \"the end of the chain\" {{\n  assert read() == {n}\n}}\n",
        n - 1
    ));
    let pkg = package(&d, "chain", &body);
    let (c, text) = code(&["test", &pkg]);
    assert_eq!(c, 0, "{text}");
    assert_ok(&text, "the end of the chain");
    let (c, text) = build(&pkg);
    assert_eq!(c, 0, "{text}");
}
