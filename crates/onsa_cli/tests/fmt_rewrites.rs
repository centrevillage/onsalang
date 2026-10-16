//! The rewrites of `onsa fmt` that change the program's tree, and the way it writes (W3-12/t, unit U1;
//! `spec/tools.md` §3.1, §3.3, §3.4 and §3.5; spec §0.2 (P2), §5.2, §6.1, §8.1, §11.4 and §18.2;
//! plan S-29, S-56, S-68 and S-100; the reviews R-78 and P-7).
//!
//! `spec/tools.md` §3.3 closes the list of the rewrites that change the AST. W3-12 does the first of
//! them and the redundant parentheses (unit U2, not here: no input of this file has a parenthesis that fmt
//! would take off); the user's decision of 2026-10-15 leaves `-> ()` and `uses {}` to the second phase and
//! takes back the `init` and the `move` (changed by W3-12/i, the second U1 fix):
//!
//! - the `return e` with a value in the tail position (§6.1): the end of the body of a function or an
//!   anonymous function, and the end of every branch of an `if` and every arm of a `match` that is there,
//!   down to the end. A `return` in a loop, a `return` that is not in the tail position (an early exit),
//!   and a `return` in the value of a `let` or in the condition of an `if` stay. A `return` without a
//!   value stays wherever it is (S-547, changed by W3-12/i, the third U1 fix: taking it off can change
//!   what `onsa check` says);
//! - `-> ()` and an empty `uses {}` (§6.1, §8.1) in a function, a method, a function type, a member of a
//!   trait and a declaration of an `extern` block (and, reading §6.1 as a whole, an operation of an
//!   effect and a function of a handler). `uses {Alloc}`, a `()` that is not the return type of a
//!   function and those of an anonymous function (S-546) stay. The second phase: the tests that take them
//!   off are ignored (`P2: …`), those that keep them run;
//! - (S-539 takes this one back: the `init` of `prev~`, `delay~` and `vdelay~` that equals the default
//!   value stays, and the tests of it say so;)
//! - (the user takes back this one too: the `move` in the returned position (§5.2) stays, `return move a`,
//!   `move a` at the end of a function and in the arms of a block that is there, as a `move` in a
//!   position where a value is consumed does; the tests of it say so.)
//!
//! Every test has the whole text of the input and of the expected output. **The expected texts are
//! worked out from the rules above and not taken from the output of `fmt`.** The output of today is
//! used for one thing: each expected text must be a file that `fmt --check` accepts (it is in the
//! canonical form of §3.2, so a mistake of the layout in a test shows at once).
//!
//! Before `fmt` runs, the input and the expected text are checked to have no diagnostic of the syntax
//! stage (a file with one is not rewritten, `onsa fmt` would end with 2, §18.2) and, where the spec
//! gives the form a meaning today, to pass `onsa check`. The trait declarations and the `extern`
//! blocks are `E0200` for `onsa check` (this version does not support them), so the cases with them are
//! checked for the syntax stage only. The output must be a fixed point (`fmt --check` ends with 0 and
//! another `fmt` changes nothing), and `onsa diff --ast <input> <output>` reports no difference
//! (§3.5: the same comparison, both sides rewritten).
//!
//! What is not here, and why:
//! - the redundant parentheses (U2);
//! - the check before writing that fails (the exit code 101): a correct `fmt` cannot make it, and the
//!   unit tests of the implementation do it. These tests keep the other side: the check must not stop
//!   a correct rewrite;
//! - whether `diff --ast` reports a difference of an ordinary comment or of a `//!` comment (S-534, a
//!   gap of the spec). No test compares two files that differ in a comment only;
//! - where a comment goes when an `init` of an element of a list is gone and the line holds a comment,
//!   or when an empty `uses {}` held a comment: §3.4 does not say, so the tests of these
//!   (`..._are_kept_once_and_in_order`) ask only what holds in every reading (the exit code 0, every
//!   comment text once and in its order, a fixed point, the same program). `return e // c` is `e // c`
//!   (S-538 (s2)): `a_return_without_a_value_stays_with_or_without_a_comment_...`;
//! - what the writing does with the mode of the file, with a symbolic link, with a read-only file and
//!   with a directory that cannot be written: the spec does not say, so no test fixes it. What the
//!   tests of the writing keep (S-56) is that no file but the given ones is left in the directory,
//!   that `--check` touches nothing, and that a changed file is a new file renamed over the name.
//!
//! The reproductions `tests/review-phase1/parent/r78.onsa` (R-78) and `p7.onsa` (P-7, the part of `fmt`) are
//! the tests `r78_...` and `p7_...`; the forms that `fmt` must keep as they are, in files of their own
//! that `onsa_cases` runs, are `tests/spec/fmt/rewrite_*.onsa`.
//!
//! Every test uses only the binary.

use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // The counter makes the directory the test's own even when two tests use the same tag.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_w312_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }

    /// The names of the entries of the directory, in order.
    fn names(&self) -> Vec<String> {
        let mut v: Vec<String> = std::fs::read_dir(&self.0)
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        v.sort();
        v
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

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// The lines joined, with one line break at the end of the file.
fn src(lines: &[&str]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

/// How much of the checking an input has to pass before `fmt` is asked about it.
#[derive(Clone, Copy, PartialEq)]
enum Level {
    /// No diagnostic of the syntax stage and `onsa check` ends with 0.
    Full,
    /// No diagnostic of the syntax stage (the form is E0200 or checked later for `onsa check`).
    Syntax,
}

/// A file before and after `onsa fmt`: the whole text of each.
struct Case {
    what: &'static str,
    input: String,
    expected: String,
    level: Level,
}

fn case(what: &'static str, input: &[&str], expected: &[&str]) -> Case {
    Case { what, input: src(input), expected: src(expected), level: Level::Full }
}

/// A file that `fmt` leaves as it is.
fn same(what: &'static str, text: &[&str]) -> Case {
    case(what, text, text)
}

impl Case {
    fn syntax_only(mut self) -> Case {
        self.level = Level::Syntax;
        self
    }
}

/// The text passes the syntax stage (`fmt --check` does not end with 2) and, at the level `Full`,
/// `onsa check` (exit code 0).
fn assert_valid(d: &Dir, name: &str, what: &str, which: &str, text: &str, level: Level) {
    let p = d.file(name, text);
    let out = onsa(&["fmt", "--check", &p]);
    assert_ne!(code(&out), 2, "{what}: the {which} text has a diagnostic of the syntax stage: {out:?}\n{text}");
    if level == Level::Full {
        let out = onsa(&["check", &p]);
        assert_eq!(code(&out), 0, "{what}: `onsa check` finds a problem in the {which} text: {out:?}\n{text}");
    }
}

/// The expected text is in the canonical form of `spec/tools.md` §3.2 (a check of the test itself).
fn assert_canonical(d: &Dir, name: &str, what: &str, text: &str) {
    let p = d.file(name, text);
    let out = onsa(&["fmt", "--check", &p]);
    assert_eq!(
        code(&out),
        0,
        "{what}: the expected text is not in the canonical form (a mistake of the test): {out:?}\n{text}"
    );
}

/// Runs `onsa fmt` on every input, expects the exit code 0 (the check before writing lets a correct
/// rewrite through), compares the whole text of each output, checks that the output is a fixed point,
/// that it still passes the check, and that `onsa diff --ast` sees the input and the output as the
/// same program. All the differences are reported together.
fn expect_fmt(tag: &str, cases: &[Case]) {
    assert!(!cases.is_empty(), "no case to run");
    let d = Dir::new(tag);
    for (i, c) in cases.iter().enumerate() {
        assert_valid(&d, &format!("e{i}.onsa"), c.what, "expected", &c.expected, c.level);
        assert_canonical(&d, &format!("k{i}.onsa"), c.what, &c.expected);
        assert_valid(&d, &format!("i{i}.onsa"), c.what, "input", &c.input, c.level);
    }
    let mut problems: Vec<String> = Vec::new();
    for (i, c) in cases.iter().enumerate() {
        let orig = d.file(&format!("orig{i}.onsa"), &c.input);
        let path = d.file(&format!("c{i}.onsa"), &c.input);
        let out = onsa(&["fmt", &path]);
        if code(&out) != 0 {
            problems.push(format!("{}: `onsa fmt` ends with {}: {out:?}", c.what, code(&out)));
            continue;
        }
        let got = read(&path);
        if got != c.expected {
            problems.push(format!("{}\n--- input\n{}--- expected\n{}--- got\n{got}", c.what, c.input, c.expected));
            continue;
        }
        let out = onsa(&["fmt", "--check", &path]);
        if code(&out) != 0 {
            problems.push(format!("{}: the output is not a fixed point of `fmt --check`: {out:?}", c.what));
        }
        let out = onsa(&["fmt", &path]);
        if code(&out) != 0 || read(&path) != got {
            problems.push(format!("{}: a second `fmt` changes the output or fails: {out:?}", c.what));
        }
        let out = onsa(&["diff", "--ast", &orig, &path]);
        if code(&out) != 0 {
            problems.push(format!(
                "{}: `diff --ast` reports a difference between the input and the output: {out:?}",
                c.what
            ));
        }
        if c.level == Level::Full {
            let out = onsa(&["check", &path]);
            if code(&out) != 0 {
                problems.push(format!("{}: the output no longer passes `onsa check`: {out:?}", c.what));
            }
        }
    }
    assert!(
        problems.is_empty(),
        "{} of {} files are not as expected:\n{}",
        problems.len(),
        cases.len(),
        problems.join("\n")
    );
}

/// The exit code and the whole output of `onsa diff --ast` on two texts.
fn diff_of(d: &Dir, tag: &str, a: &str, b: &str) -> (i32, String) {
    let pa = d.file(&format!("{tag}_a.onsa"), a);
    let pb = d.file(&format!("{tag}_b.onsa"), b);
    let out = onsa(&["diff", "--ast", &pa, &pb]);
    (code(&out), format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)))
}

// ---------------------------------------------------------------------------------------------------
// The `return` in the tail position (§6.1)
// ---------------------------------------------------------------------------------------------------

/// The end of the body of an anonymous function (§6.1: "関数と無名関数の本体の最後").
fn t_closures() -> Case {
    case(
        "return at the end of an anonymous function",
        &[
            "use std.array",
            "",
            "fn doubled() -> F32 {",
            "  let f = fn(x: F32) -> F32 {",
            "    return x * 2.0",
            "  }",
            "  f.(1.0)",
            "}",
            "",
            "fn one_line() -> F32 {",
            "  let f = fn(x: F32) -> F32 { return x * 2.0 }",
            "  f.(1.0)",
            "}",
            "",
            "fn argument() -> U32 {",
            "  let xs: [U32; 4] = array.from_fn(fn(i) { return i * 2 })",
            "  xs[3]",
            "}",
            "",
            "fn with_an_early_exit() -> I32 {",
            "  let g = fn(x: I32) -> I32 {",
            "    if x < 0 {",
            "      return 0",
            "    }",
            "    return x",
            "  }",
            "  g.(1)",
            "}",
            "",
            "fn in_a_loop() -> I32 {",
            "  var s = 0",
            "  for i in 0 ..< 3 {",
            "    let g = fn(y: I32) -> I32 {",
            "      return y + 1",
            "    }",
            "    s = s + g.(i)",
            "  }",
            "  s",
            "}",
        ],
        &[
            "use std.array",
            "",
            "fn doubled() -> F32 {",
            "  let f = fn(x: F32) -> F32 {",
            "    x * 2.0",
            "  }",
            "  f.(1.0)",
            "}",
            "",
            "fn one_line() -> F32 {",
            "  let f = fn(x: F32) -> F32 { x * 2.0 }",
            "  f.(1.0)",
            "}",
            "",
            "fn argument() -> U32 {",
            "  let xs: [U32; 4] = array.from_fn(fn(i) { i * 2 })",
            "  xs[3]",
            "}",
            "",
            "fn with_an_early_exit() -> I32 {",
            "  let g = fn(x: I32) -> I32 {",
            "    if x < 0 {",
            "      return 0",
            "    }",
            "    x",
            "  }",
            "  g.(1)",
            "}",
            "",
            "fn in_a_loop() -> I32 {",
            "  var s = 0",
            "  for i in 0 ..< 3 {",
            "    let g = fn(y: I32) -> I32 {",
            "      y + 1",
            "    }",
            "    s = s + g.(i)",
            "  }",
            "  s",
            "}",
        ],
    )
}

/// The end of every branch of an `if`, `else if` and `else` at the end of the body.
fn t_if_branches() -> Case {
    case(
        "return at the end of every branch of an if",
        &[
            "fn sign(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return -1",
            "  } else if x == 0 {",
            "    return 0",
            "  } else {",
            "    return 1",
            "  }",
            "}",
            "",
            "fn one_line(c: Bool) -> I32 {",
            "  if c { return 1 } else { return 2 }",
            "}",
            "",
            "fn after_statements(c: Bool, x: I32) -> I32 {",
            "  if c {",
            "    let y = x + 1",
            "    return y * 2",
            "  } else {",
            "    let z = x - 1",
            "    return z",
            "  }",
            "}",
            "",
            "fn one_branch_returns(c: Bool) -> I32 {",
            "  if c {",
            "    return 1",
            "  } else {",
            "    2",
            "  }",
            "}",
        ],
        &[
            "fn sign(x: I32) -> I32 {",
            "  if x < 0 {",
            "    -1",
            "  } else if x == 0 {",
            "    0",
            "  } else {",
            "    1",
            "  }",
            "}",
            "",
            "fn one_line(c: Bool) -> I32 {",
            "  if c { 1 } else { 2 }",
            "}",
            "",
            "fn after_statements(c: Bool, x: I32) -> I32 {",
            "  if c {",
            "    let y = x + 1",
            "    y * 2",
            "  } else {",
            "    let z = x - 1",
            "    z",
            "  }",
            "}",
            "",
            "fn one_branch_returns(c: Bool) -> I32 {",
            "  if c {",
            "    1",
            "  } else {",
            "    2",
            "  }",
            "}",
        ],
    )
}

/// The end of every arm of a `match` at the end of the body: the arm with a block and the arm that is an
/// expression (an `if` there is a branch to follow). The braces of the arm stay: only the `return` goes.
fn t_match_arms() -> Case {
    case(
        "return at the end of every arm of a match",
        &[
            "fn pick(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) => { return v },",
            "    None => { return 0 },",
            "  }",
            "}",
            "",
            "fn with_statements(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) if v > 0 => {",
            "      let w = v + 1",
            "      return w",
            "    },",
            "    Some(v) => { return -v },",
            "    None => {",
            "      return 0",
            "    },",
            "  }",
            "}",
            "",
            "fn expression_arms(o: Option[I32], c: Bool) -> I32 {",
            "  match o {",
            "    Some(v) => if c { return v } else { return 1 },",
            "    None => 0,",
            "  }",
            "}",
        ],
        &[
            "fn pick(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) => { v },",
            "    None => { 0 },",
            "  }",
            "}",
            "",
            "fn with_statements(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) if v > 0 => {",
            "      let w = v + 1",
            "      w",
            "    },",
            "    Some(v) => { -v },",
            "    None => {",
            "      0",
            "    },",
            "  }",
            "}",
            "",
            "fn expression_arms(o: Option[I32], c: Bool) -> I32 {",
            "  match o {",
            "    Some(v) => if c { v } else { 1 },",
            "    None => 0,",
            "  }",
            "}",
        ],
    )
}

/// The definition is recursive: an `if` in a `match` in an `if`, a `match` in a closure.
fn t_nested() -> Case {
    case(
        "return through nested branches",
        &[
            "fn nested(o: Option[I32], c: Bool) -> I32 {",
            "  if c {",
            "    match o {",
            "      Some(v) => {",
            "        if v > 0 {",
            "          return v",
            "        } else {",
            "          return -v",
            "        }",
            "      },",
            "      None => { return 0 },",
            "    }",
            "  } else {",
            "    return 1",
            "  }",
            "}",
            "",
            "fn deeper(c: Bool, d: Bool, e: Bool) -> I32 {",
            "  if c {",
            "    if d {",
            "      if e {",
            "        return 1",
            "      } else {",
            "        return 2",
            "      }",
            "    } else {",
            "      return 3",
            "    }",
            "  } else {",
            "    return 4",
            "  }",
            "}",
            "",
            "fn match_in_a_closure(o: Option[I32]) -> I32 {",
            "  let f = fn(p: Option[I32]) -> I32 {",
            "    match p {",
            "      Some(v) => { return v },",
            "      None => { return 0 },",
            "    }",
            "  }",
            "  return f.(o)",
            "}",
        ],
        &[
            "fn nested(o: Option[I32], c: Bool) -> I32 {",
            "  if c {",
            "    match o {",
            "      Some(v) => {",
            "        if v > 0 {",
            "          v",
            "        } else {",
            "          -v",
            "        }",
            "      },",
            "      None => { 0 },",
            "    }",
            "  } else {",
            "    1",
            "  }",
            "}",
            "",
            "fn deeper(c: Bool, d: Bool, e: Bool) -> I32 {",
            "  if c {",
            "    if d {",
            "      if e {",
            "        1",
            "      } else {",
            "        2",
            "      }",
            "    } else {",
            "      3",
            "    }",
            "  } else {",
            "    4",
            "  }",
            "}",
            "",
            "fn match_in_a_closure(o: Option[I32]) -> I32 {",
            "  let f = fn(p: Option[I32]) -> I32 {",
            "    match p {",
            "      Some(v) => { v },",
            "      None => { 0 },",
            "    }",
            "  }",
            "  f.(o)",
            "}",
        ],
    )
}

/// A `return` without a value stays, in the tail position too (S-547; §6.1: "`onsa fmt` は取り除かない").
/// The expected text of W3-12/t took them off.
fn t_valueless() -> Case {
    same(
        "return without a value in the tail position stays",
        &[
            "fn set_one(inout x: I32) {",
            "  x = 1",
            "  return",
            "}",
            "",
            "fn branches(c: Bool, inout x: I32) {",
            "  if c {",
            "    x = 1",
            "    return",
            "  } else {",
            "    x = 2",
            "    return",
            "  }",
            "}",
            "",
            "fn without_else(c: Bool, inout x: I32) {",
            "  x = 0",
            "  if c {",
            "    x = 1",
            "    return",
            "  }",
            "}",
            "",
            "fn in_a_match(o: Option[I32], inout x: I32) {",
            "  match o {",
            "    Some(v) => {",
            "      x = v",
            "      return",
            "    },",
            "    None => {",
            "      x = 0",
            "      return",
            "    },",
            "  }",
            "}",
            "",
            "fn early_and_last(c: Bool, inout x: I32) {",
            "  if c {",
            "    return",
            "  }",
            "  x = 2",
            "  return",
            "}",
        ],
    )
}

/// The body of a method of an `impl` (Full) and the default body of a member of a `trait` (a trait is
/// E0200 for `onsa check` today, so it is checked for the syntax stage only).
fn t_methods() -> Case {
    case(
        "return at the end of the methods of an impl",
        &[
            "struct Counter {",
            "  n: I32,",
            "}",
            "",
            "impl Counter {",
            "  fn get(self) -> I32 {",
            "    return self.n",
            "  }",
            "",
            "  fn bump(inout self) {",
            "    self.n = self.n + 1",
            "    return",
            "  }",
            "",
            "  fn clamp(self, hi: I32) -> I32 {",
            "    if self.n > hi {",
            "      return hi",
            "    } else {",
            "      return self.n",
            "    }",
            "  }",
            "}",
        ],
        &[
            "struct Counter {",
            "  n: I32,",
            "}",
            "",
            "impl Counter {",
            "  fn get(self) -> I32 {",
            "    self.n",
            "  }",
            "",
            "  fn bump(inout self) {",
            "    self.n = self.n + 1",
            "    return",
            "  }",
            "",
            "  fn clamp(self, hi: I32) -> I32 {",
            "    if self.n > hi {",
            "      hi",
            "    } else {",
            "      self.n",
            "    }",
            "  }",
            "}",
        ],
    )
}

/// The `return` without a value after `self.put!(x)` stays (S-547; without it the call would be the value
/// of the body, another program). The expected text of W3-12/t took it off.
fn t_trait_defaults() -> Case {
    case(
        "return at the end of the default body of a trait member",
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32)",
            "",
            "  fn twice(inout self, x: F32) {",
            "    self.put!(x)",
            "    self.put!(x)",
            "    return",
            "  }",
            "",
            "  fn size(self) -> U32 {",
            "    return 0",
            "  }",
            "",
            "  fn choose(self, c: Bool) -> U32 {",
            "    if c {",
            "      return 1",
            "    } else {",
            "      return 2",
            "    }",
            "  }",
            "}",
        ],
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32)",
            "",
            "  fn twice(inout self, x: F32) {",
            "    self.put!(x)",
            "    self.put!(x)",
            "    return",
            "  }",
            "",
            "  fn size(self) -> U32 {",
            "    0",
            "  }",
            "",
            "  fn choose(self, c: Bool) -> U32 {",
            "    if c {",
            "      1",
            "    } else {",
            "      2",
            "    }",
            "  }",
            "}",
        ],
    )
    .syntax_only()
}

/// The `return`s that are not in the tail position stay (§6.1: a loop, an early exit, the value of a
/// `let`, the condition of an `if`), in the same files as the `return` that goes.
fn t_stays_beside_the_last() -> Case {
    case(
        "returns that are not in the tail position stay, the last one goes",
        &[
            "fn first_big(xs: [I32; 4]) -> I32 {",
            "  for i in 0 ..< 4 {",
            "    if xs[i] > 9 {",
            "      return xs[i]",
            "    }",
            "  }",
            "  return -1",
            "}",
            "",
            "fn guard_clause(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return 0",
            "  }",
            "  return x * 2",
            "}",
            "",
            "fn drain(inout n: I32) -> I32 {",
            "  while n > 0 {",
            "    n = n - 1",
            "    return n",
            "  }",
            "  0",
            "}",
            "",
            "fn in_a_let(c: Bool) -> I32 {",
            "  let x = if c {",
            "    return 1",
            "  } else {",
            "    2",
            "  }",
            "  return x + 1",
            "}",
            "",
            "fn in_a_condition(c: Bool, d: Bool) -> I32 {",
            "  if d && (if c { return 1 } else { true }) {",
            "    return 2",
            "  } else {",
            "    return 3",
            "  }",
            "}",
            "",
            "fn loop_in_a_branch(c: Bool, n: I32) -> I32 {",
            "  if c {",
            "    for i in 0 ..< n {",
            "      if i == 3 {",
            "        return i",
            "      }",
            "    }",
            "    return -1",
            "  } else {",
            "    return 0",
            "  }",
            "}",
        ],
        &[
            "fn first_big(xs: [I32; 4]) -> I32 {",
            "  for i in 0 ..< 4 {",
            "    if xs[i] > 9 {",
            "      return xs[i]",
            "    }",
            "  }",
            "  -1",
            "}",
            "",
            "fn guard_clause(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return 0",
            "  }",
            "  x * 2",
            "}",
            "",
            "fn drain(inout n: I32) -> I32 {",
            "  while n > 0 {",
            "    n = n - 1",
            "    return n",
            "  }",
            "  0",
            "}",
            "",
            "fn in_a_let(c: Bool) -> I32 {",
            "  let x = if c {",
            "    return 1",
            "  } else {",
            "    2",
            "  }",
            "  x + 1",
            "}",
            "",
            "fn in_a_condition(c: Bool, d: Bool) -> I32 {",
            "  if d && (if c { return 1 } else { true }) {",
            "    2",
            "  } else {",
            "    3",
            "  }",
            "}",
            "",
            "fn loop_in_a_branch(c: Bool, n: I32) -> I32 {",
            "  if c {",
            "    for i in 0 ..< n {",
            "      if i == 3 {",
            "        return i",
            "      }",
            "    }",
            "    -1",
            "  } else {",
            "    0",
            "  }",
            "}",
        ],
    )
}

/// The `return` that is the value of a `return` in the tail position: when the outer `return` goes, the
/// value is at the end, so the inner `return` is in the tail position. A second `fmt` must not find
/// one more to take off (§18.2: the output is a fixed point), so one pass takes both.
fn t_return_in_the_value() -> Case {
    case(
        "a return in the value of the last return goes in one pass",
        &[
            "fn once(c: Bool) -> I32 {",
            "  return if c { return 1 } else { 2 }",
            "}",
            "",
            "fn several_lines(c: Bool) -> I32 {",
            "  return if c {",
            "    return 1",
            "  } else {",
            "    2",
            "  }",
            "}",
            "",
            "fn a_match(o: Option[I32]) -> I32 {",
            "  return match o {",
            "    Some(v) => { return v },",
            "    None => { 0 },",
            "  }",
            "}",
        ],
        &[
            "fn once(c: Bool) -> I32 {",
            "  if c { 1 } else { 2 }",
            "}",
            "",
            "fn several_lines(c: Bool) -> I32 {",
            "  if c {",
            "    1",
            "  } else {",
            "    2",
            "  }",
            "}",
            "",
            "fn a_match(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) => { v },",
            "    None => { 0 },",
            "  }",
            "}",
        ],
    )
}

/// A body or a branch that holds a `return` without a value only keeps it (S-547; the expected text of
/// W3-12/t left an empty pair of braces); the value of `return 1` on one line is the whole body.
fn t_left_empty() -> Case {
    case(
        "a body and a branch that hold a return without a value only",
        &[
            "fn nothing() {",
            "  return",
            "}",
            "",
            "fn nothing_on_a_line() { return }",
            "",
            "fn only_branch(c: Bool) {",
            "  if c {",
            "    return",
            "  }",
            "}",
            "",
            "fn one_value() -> I32 { return 1 }",
        ],
        &[
            "fn nothing() {",
            "  return",
            "}",
            "",
            "fn nothing_on_a_line() { return }",
            "",
            "fn only_branch(c: Bool) {",
            "  if c {",
            "    return",
            "  }",
            "}",
            "",
            "fn one_value() -> I32 { 1 }",
        ],
    )
}

/// The comments that §3.4 places: the comment of a line stays after the last code of the line, a line of
/// comment stays before the next element or before the closing bracket.
fn t_tail_return_comments() -> Case {
    case(
        "comments round the returns that go",
        &[
            "fn f(c: Bool) -> I32 {",
            "  if c {",
            "    // one",
            "    return 1 // first",
            "  } else {",
            "    // two",
            "    return 2",
            "    // end of the branch",
            "  }",
            "}",
            "",
            "fn g(inout x: I32) {",
            "  x = 1",
            "  // done",
            "  return",
            "}",
            "",
            "fn h(o: Option[I32]) -> I32 {",
            "  match o {",
            "    // a value",
            "    Some(v) => { return v }, // the value",
            "    None => {",
            "      return 0 // none",
            "    },",
            "  }",
            "}",
            "",
            "fn k() -> I32 {",
            "  let f = fn(x: I32) -> I32 { // closure",
            "    let y = x + 1",
            "    return y // result",
            "  }",
            "  f.(1)",
            "}",
        ],
        &[
            "fn f(c: Bool) -> I32 {",
            "  if c {",
            "    // one",
            "    1 // first",
            "  } else {",
            "    // two",
            "    2",
            "    // end of the branch",
            "  }",
            "}",
            "",
            "fn g(inout x: I32) {",
            "  x = 1",
            "  // done",
            "  return",
            "}",
            "",
            "fn h(o: Option[I32]) -> I32 {",
            "  match o {",
            "    // a value",
            "    Some(v) => { v }, // the value",
            "    None => {",
            "      0 // none",
            "    },",
            "  }",
            "}",
            "",
            "fn k() -> I32 {",
            "  let f = fn(x: I32) -> I32 { // closure",
            "    let y = x + 1",
            "    y // result",
            "  }",
            "  f.(1)",
            "}",
        ],
    )
}

/// A generic function and a closure in the argument of a call, with the `return` of the function and of
/// the closure in one pass.
fn t_generic_and_closure_argument() -> Case {
    case(
        "a generic function, a closure argument, and the returns of both",
        &[
            "use std.array",
            "",
            "fn id[T](x: T) -> T {",
            "  return x",
            "}",
            "",
            "fn choose[T](a: T, b: T, first: Bool) -> T {",
            "  if first {",
            "    return a",
            "  } else {",
            "    return b",
            "  }",
            "}",
            "",
            "fn doubled() -> [U32; 4] {",
            "  return array.from_fn(fn(i) { return i * 2 })",
            "}",
        ],
        &[
            "use std.array",
            "",
            "fn id[T](x: T) -> T {",
            "  x",
            "}",
            "",
            "fn choose[T](a: T, b: T, first: Bool) -> T {",
            "  if first {",
            "    a",
            "  } else {",
            "    b",
            "  }",
            "}",
            "",
            "fn doubled() -> [U32; 4] {",
            "  array.from_fn(fn(i) { i * 2 })",
            "}",
        ],
    )
}

fn tail_cases() -> Vec<Case> {
    vec![
        t_closures(),
        t_if_branches(),
        t_match_arms(),
        t_nested(),
        t_valueless(),
        t_methods(),
        t_trait_defaults(),
        t_stays_beside_the_last(),
        t_return_in_the_value(),
        t_left_empty(),
        t_tail_return_comments(),
        t_generic_and_closure_argument(),
    ]
}

#[test]
fn return_at_the_end_of_an_anonymous_function_is_taken_off() {
    expect_fmt("tail_closures", &[t_closures()]);
}

#[test]
fn return_at_the_end_of_every_branch_of_an_if_is_taken_off() {
    expect_fmt("tail_if", &[t_if_branches()]);
}

#[test]
fn return_at_the_end_of_every_arm_of_a_match_is_taken_off() {
    expect_fmt("tail_match", &[t_match_arms()]);
}

#[test]
fn return_through_nested_branches_is_taken_off() {
    expect_fmt("tail_nested", &[t_nested()]);
}

#[test]
fn return_without_a_value_in_the_tail_position_stays() {
    expect_fmt("tail_valueless", &[t_valueless()]);
}

#[test]
fn return_at_the_end_of_methods_and_of_default_bodies_of_a_trait_is_taken_off() {
    expect_fmt("tail_methods", &[t_methods(), t_trait_defaults()]);
}

#[test]
fn returns_in_a_loop_before_the_end_and_in_a_let_or_a_condition_stay() {
    expect_fmt("tail_stays", &[t_stays_beside_the_last()]);
}

#[test]
fn a_return_in_the_value_of_the_last_return_is_taken_off_in_one_pass() {
    expect_fmt("tail_in_value", &[t_return_in_the_value()]);
}

#[test]
fn a_body_or_branch_that_holds_only_a_return_without_a_value_keeps_it() {
    expect_fmt("tail_empty", &[t_left_empty()]);
}

#[test]
fn comments_round_the_returns_that_go_stay_where_the_rules_of_the_comments_put_them() {
    expect_fmt("tail_comments", &[t_tail_return_comments()]);
}

#[test]
fn the_returns_of_a_generic_function_and_of_a_closure_argument_are_taken_off() {
    expect_fmt("tail_generic", &[t_generic_and_closure_argument()]);
}

// ---------------------------------------------------------------------------------------------------
// `-> ()` and an empty `uses {}` (§6.1, §8.1): the second phase
// ---------------------------------------------------------------------------------------------------
//
// The user left the rewrite of `-> ()` and an empty `uses {}` to the second phase (2026-10-15): the tests
// that take them off are ignored (`P2: …`) and keep their expected texts for then; those that keep them
// run.

fn u_declarations() -> Case {
    case(
        "-> () and uses {} in the head of a function",
        &[
            "fn a() -> () {}",
            "",
            "fn b() -> I32 uses {} {",
            "  1",
            "}",
            "",
            "fn c() -> () uses {} {}",
            "",
            "fn d() uses {} {}",
            "",
            "fn e() -> () uses {Alloc} {}",
            "",
            "pub fn f[T](x: T) -> () {}",
            "",
            "rt fn g() -> () {}",
            "",
            "fn h(",
            "  inout total: I32,",
            "  b: I32,",
            ") -> () uses {} {",
            "  total = total + b",
            "}",
        ],
        &[
            "fn a() {}",
            "",
            "fn b() -> I32 {",
            "  1",
            "}",
            "",
            "fn c() {}",
            "",
            "fn d() {}",
            "",
            "fn e() uses {Alloc} {}",
            "",
            "pub fn f[T](x: T) {}",
            "",
            "rt fn g() {}",
            "",
            "fn h(",
            "  inout total: I32,",
            "  b: I32,",
            ") {",
            "  total = total + b",
            "}",
        ],
    )
}

fn u_function_types() -> Case {
    case(
        "-> () and uses {} in a function type",
        &[
            "type Callback = fn(F32) -> ()",
            "",
            "type Source = fn() -> F32 uses {}",
            "",
            "pub struct Shaper {",
            "  gain: F32,",
            "  on_tick: fn(F32) -> (),",
            "  curve: fn(F32) -> F32 uses {},",
            "  both: fn(F32) -> () uses {},",
            "  alloc: fn(F32) -> () uses {Alloc},",
            "}",
            "",
            "fn apply(f: fn(F32) -> (), g: fn() uses {}, x: F32) {",
            "  f.(x)",
            "}",
            "",
            "fn tick(x: F32) {}",
            "",
            "fn store() {",
            "  let h: fn(F32) -> () = tick",
            "  h.(1.0)",
            "}",
        ],
        &[
            "type Callback = fn(F32)",
            "",
            "type Source = fn() -> F32",
            "",
            "pub struct Shaper {",
            "  gain: F32,",
            "  on_tick: fn(F32),",
            "  curve: fn(F32) -> F32,",
            "  both: fn(F32),",
            "  alloc: fn(F32) uses {Alloc},",
            "}",
            "",
            "fn apply(f: fn(F32), g: fn(), x: F32) {",
            "  f.(x)",
            "}",
            "",
            "fn tick(x: F32) {}",
            "",
            "fn store() {",
            "  let h: fn(F32) = tick",
            "  h.(1.0)",
            "}",
        ],
    )
}

/// S-546 (a decision of the user, 2026-10-15; changed by W3-12/i, the U1 fix): in an anonymous function,
/// leaving out the result and the effects leaves them to the expected type or the body (§6.1, §8.1), so
/// `-> ()` and `uses {}` are annotations of their own and stay (`take(fn(x: I32) -> () { x })` is E0401
/// and stays so).
fn u_closures() -> Case {
    case(
        "-> () and uses {} in an anonymous function stay",
        &[
            "fn closures() -> I32 {",
            "  let a = fn(x: I32) -> () {}",
            "  let b = fn(x: I32) -> () uses {} {}",
            "  let c = fn(x: I32) -> I32 uses {} { x }",
            "  let d = fn(x: I32) uses {} {}",
            "  1",
            "}",
        ],
        &[
            "fn closures() -> I32 {",
            "  let a = fn(x: I32) -> () {}",
            "  let b = fn(x: I32) -> () uses {} {}",
            "  let c = fn(x: I32) -> I32 uses {} { x }",
            "  let d = fn(x: I32) uses {} {}",
            "  1",
            "}",
        ],
    )
}

/// The members of a trait and the declarations of an `extern` block (E0200 for `onsa check` today, so
/// the syntax stage only).
fn u_trait_and_extern() -> Case {
    case(
        "-> () and uses {} in the members of a trait and an extern block",
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32) -> ()",
            "",
            "  fn clear(inout self) -> () uses {}",
            "",
            "  fn size(self) -> U32 uses {}",
            "",
            "  fn both(self) -> () uses {Alloc}",
            "",
            "  fn reset(inout self) -> () {",
            "    self.clear!()",
            "  }",
            "}",
            "",
            "extern \"C\" lib \"m\" {",
            "  fn sinf(x: F32) -> F32 uses {}",
            "",
            "  fn reset() -> ()",
            "",
            "  fn both() -> () uses {}",
            "",
            "  rt fn tick() -> () uses {}",
            "}",
        ],
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32)",
            "",
            "  fn clear(inout self)",
            "",
            "  fn size(self) -> U32",
            "",
            "  fn both(self) uses {Alloc}",
            "",
            "  fn reset(inout self) {",
            "    self.clear!()",
            "  }",
            "}",
            "",
            "extern \"C\" lib \"m\" {",
            "  fn sinf(x: F32) -> F32",
            "",
            "  fn reset()",
            "",
            "  fn both()",
            "",
            "  rt fn tick()",
            "}",
        ],
    )
    .syntax_only()
}

/// What stays next to a `-> ()` that goes: `uses {Alloc}`, a `()` that is a type argument, a tuple,
/// a unit value.
fn u_stays_beside_the_removed() -> Case {
    case(
        "uses {Alloc}, a unit in a type argument and a unit value stay",
        &[
            "fn ok_unit() -> Result[(), Str] {",
            "  Ok(())",
            "}",
            "",
            "fn pair() -> (I32, I32) {",
            "  (1, 2)",
            "}",
            "",
            "fn alloc_unit() uses {Alloc} {}",
            "",
            "fn unit_value() -> () {",
            "  let u: () = ()",
            "}",
        ],
        &[
            "fn ok_unit() -> Result[(), Str] {",
            "  Ok(())",
            "}",
            "",
            "fn pair() -> (I32, I32) {",
            "  (1, 2)",
            "}",
            "",
            "fn alloc_unit() uses {Alloc} {}",
            "",
            "fn unit_value() {",
            "  let u: () = ()",
            "}",
        ],
    )
}

/// The methods of an `impl` are functions: the head is the head of a function.
fn u_methods() -> Case {
    case(
        "-> () and uses {} in the head of the methods of an impl",
        &[
            "pub struct Counter {",
            "  n: I32,",
            "}",
            "",
            "impl Counter {",
            "  pub fn clear(inout self) -> () uses {} {",
            "    self.n = 0",
            "  }",
            "",
            "  pub fn get(self) -> I32 uses {} {",
            "    self.n",
            "  }",
            "",
            "  fn nothing(self) -> () {}",
            "}",
        ],
        &[
            "pub struct Counter {",
            "  n: I32,",
            "}",
            "",
            "impl Counter {",
            "  pub fn clear(inout self) {",
            "    self.n = 0",
            "  }",
            "",
            "  pub fn get(self) -> I32 {",
            "    self.n",
            "  }",
            "",
            "  fn nothing(self) {}",
            "}",
        ],
    )
}

/// An operation of an `effect` and a function of a `handler` are signatures of functions too, and §6.1 says
/// "返り値が `()` の場合だけ `->` を省略（省略が唯一の書き方。`-> ()` と書いても受理し、`onsa fmt` が外す）". The
/// S-68 row of the plan names the positions function, anonymous function, function type, trait member and
/// extern declaration; these two are not in the list, so the test is a reading of §6.1 as a whole (an
/// effect and a handler are E0200 for `onsa check` today: the syntax stage only).
fn u_effect_and_handler() -> Case {
    case(
        "-> () in an effect operation and in a function of a handler",
        &[
            "pub effect Log {",
            "  fn info(msg: Str) -> ()",
            "",
            "  rt fn tick() -> ()",
            "}",
            "",
            "handler quiet_log: Log {",
            "  fn info(msg: Str) -> () {}",
            "",
            "  rt fn tick() -> () {}",
            "}",
        ],
        &[
            "pub effect Log {",
            "  fn info(msg: Str)",
            "",
            "  rt fn tick()",
            "}",
            "",
            "handler quiet_log: Log {",
            "  fn info(msg: Str) {}",
            "",
            "  rt fn tick() {}",
            "}",
        ],
    )
    .syntax_only()
}

/// The comment at the end of a line whose `-> ()` goes stays after the last code of the line (§3.4).
fn u_comments() -> Case {
    case(
        "the comment at the end of the line of a -> () that goes",
        &[
            "fn opens() -> () { // the head",
            "}",
            "",
            "fn lists(",
            "  a: I32,",
            ") -> () uses {} { // closes",
            "  let b = a",
            "}",
        ],
        &["fn opens() { // the head", "}", "", "fn lists(", "  a: I32,", ") { // closes", "  let b = a", "}"],
    )
}

fn u_trait_comment() -> Case {
    case(
        "the comment at the end of a trait member whose -> () goes",
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32) -> () // sink one sample",
            "",
            "  fn clear(inout self) -> () uses {} // empty it",
            "}",
        ],
        &[
            "trait Sink {",
            "  fn put(inout self, x: F32) // sink one sample",
            "",
            "  fn clear(inout self) // empty it",
            "}",
        ],
    )
    .syntax_only()
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn unit_return_type_and_empty_uses_are_taken_off_the_head_of_a_function() {
    expect_fmt("unit_decl", &[u_declarations()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn unit_return_type_and_empty_uses_are_taken_off_a_function_type() {
    expect_fmt("unit_types", &[u_function_types()]);
}

#[test]
fn unit_return_type_and_empty_uses_of_an_anonymous_function_stay() {
    expect_fmt("unit_closures", &[u_closures()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn unit_return_type_and_empty_uses_are_taken_off_the_methods_of_an_impl() {
    expect_fmt("unit_methods", &[u_methods()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn unit_return_type_is_taken_off_an_effect_operation_and_a_function_of_a_handler() {
    expect_fmt("unit_effect_handler", &[u_effect_and_handler()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn unit_return_type_and_empty_uses_are_taken_off_trait_members_and_extern_declarations() {
    expect_fmt("unit_trait_extern", &[u_trait_and_extern()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn uses_with_an_effect_and_a_unit_that_is_not_the_return_type_stay() {
    expect_fmt("unit_stays", &[u_stays_beside_the_removed()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn a_comment_at_the_end_of_the_line_of_a_unit_return_type_that_goes_stays_after_the_last_code() {
    expect_fmt("unit_comments", &[u_comments(), u_trait_comment()]);
}

// ---------------------------------------------------------------------------------------------------
// The `init` of `prev~`, `delay~` and `vdelay~` that is the default value (§11.4): it stays (S-539)
// ---------------------------------------------------------------------------------------------------
//
// S-539 (a decision of the user, 2026-10-15; changed by W3-12/i, the U1 fix): `onsa fmt` does not take
// off the `init` that equals the default value (S-29 is taken back). The syntax alone does not show that
// it can go: in `let y = prev~(^y, 0)` the literal is what gives `y` its type (without it, E0406), and
// the `0` of `prev~(x, 0)` for an `x: F32` is E0401, which taking it off would hide. Both `prev~(x)` and
// `prev~(x, 0.0)` are taken as they are written.

fn i_default() -> Case {
    same(
        "init that is 0 or 0.0 in prev~, delay~ and vdelay~ stays",
        &[
            "pub flow lag1(x: F32 at sample) -> F32 at sample {",
            "  prev~(x, 0.0)",
            "}",
            "",
            "pub flow lag_int(n: I32 at sample) -> I32 at sample {",
            "  prev~(n, 0)",
            "}",
            "",
            "pub flow echo(x: F32 at sample) -> F32 at sample {",
            "  delay~(x, 4, 0.0)",
            "}",
            "",
            "pub flow echo_var(x: F32 at sample, d: F32 at sample) -> F32 at sample {",
            "  vdelay~(x, d, 8, 0.0)",
            "}",
            "",
            "pub flow feedback(x: F32 at sample) -> F32 at sample {",
            "  let y = x + prev~(^y, 0.0)",
            "  y",
            "}",
        ],
    )
}

/// Another spelling of zero stays too (only §3.2 respells a number: `00.00` is `0.00`).
fn i_spellings_of_zero() -> Case {
    case(
        "init that is another spelling of zero stays",
        &[
            "pub flow a1(x: F32 at sample) -> F32 at sample {",
            "  prev~(x, 0e0)",
            "}",
            "",
            "pub flow a2(n: I32 at sample) -> I32 at sample {",
            "  prev~(n, 0x0_0)",
            "}",
            "",
            "pub flow a3(x: F32 at sample) -> F32 at sample {",
            "  prev~(x, 00.00)",
            "}",
        ],
        &[
            "pub flow a1(x: F32 at sample) -> F32 at sample {",
            "  prev~(x, 0e0)",
            "}",
            "",
            "pub flow a2(n: I32 at sample) -> I32 at sample {",
            "  prev~(n, 0x0_0)",
            "}",
            "",
            "pub flow a3(x: F32 at sample) -> F32 at sample {",
            "  prev~(x, 0.00)",
            "}",
        ],
    )
}

/// `false`, the default of a `Bool`, stays.
fn i_bool() -> Case {
    same(
        "init that is false stays",
        &[
            "pub flow lag_flag(b: Bool at sample) -> Bool at sample {",
            "  prev~(b, false)",
            "}",
            "",
            "pub flow echo_flag(b: Bool at sample) -> Bool at sample {",
            "  delay~(b, 3, false)",
            "}",
        ],
    )
    .syntax_only()
}

fn i_kept_lines() -> Vec<&'static str> {
    vec![
        "const ZERO: F32 = 0.0",
        "",
        "pub flow k1(x: F32 at sample) -> F32 at sample {",
        "  prev~(x, 1.0)",
        "}",
        "",
        "pub flow k2(x: F32 at sample, start: F32 at init) -> F32 at sample {",
        "  prev~(x, start)",
        "}",
        "",
        "pub flow k3(x: F32 at sample) -> F32 at sample {",
        "  prev~(x, -0.0)",
        "}",
        "",
        "pub flow k4(x: F32 at sample) -> F32 at sample {",
        "  prev~(x, ZERO)",
        "}",
        "",
        "pub flow k5(x: F32 at sample) -> F32 at sample {",
        "  delay~(x, 4, 0.5)",
        "}",
        "",
        "pub flow k6(x: F32 at sample, d: F32 at sample) -> F32 at sample {",
        "  vdelay~(x, d, 8, -0.0)",
        "}",
        "",
        "pub flow k7(n: I32 at sample) -> I32 at sample {",
        "  prev~(n, 1)",
        "}",
        "",
        "pub flow k8(b: Bool at sample) -> Bool at sample {",
        "  prev~(b, true)",
        "}",
        "",
        "pub flow k9(x: F32 at sample, start: F32 at init) -> F32 at sample {",
        "  delay~(x, 4, start)",
        "}",
        "",
        "pub flow lag(x: F32 at sample, start: F32 at init) -> F32 at sample {",
        "  prev~(x, start)",
        "}",
        "",
        "pub flow use_lag(x: F32 at sample) -> F32 at sample {",
        "  lag~(x, 0.0)",
        "}",
    ]
}

/// `1.0`, a name, `-0.0` and the argument of a flow of the user (a user's function has no default
/// argument, §11.4) stay: only the three built-ins have an `init` that can be left out.
fn i_kept() -> Case {
    same("init that is not the default stays", &i_kept_lines())
}

/// The `init` on its own line in the block form of the arguments stays, with its `,`.
fn i_block_form() -> Case {
    same(
        "init as an element of the block form stays",
        &[
            "pub flow block_args(x: F32 at sample) -> F32 at sample {",
            "  let z = delay~(",
            "    x,",
            "    4,",
            "    0.0, // silence",
            "  )",
            "  z",
            "}",
        ],
    )
}

/// The comment of the line of an `init` stays where it is.
fn i_comment() -> Case {
    same(
        "the comment at the end of the line of an init stays",
        &[
            "pub flow noted(x: F32 at sample) -> F32 at sample {",
            "  // the previous sample",
            "  let y = prev~(x, 0.0) // silence at first",
            "  y",
            "}",
        ],
    )
}

fn init_cases() -> Vec<Case> {
    vec![i_default(), i_bool(), i_spellings_of_zero(), i_kept(), i_block_form(), i_comment()]
}

#[test]
fn init_that_is_the_default_value_stays_in_prev_delay_and_vdelay() {
    expect_fmt("init_default", &[i_default()]);
}

#[test]
fn init_that_is_false_stays() {
    expect_fmt("init_bool", &[i_bool()]);
}

#[test]
fn init_that_is_another_spelling_of_zero_stays() {
    expect_fmt("init_spellings", &[i_spellings_of_zero()]);
}

#[test]
fn init_that_is_not_the_default_value_stays() {
    expect_fmt("init_kept", &[i_kept()]);
}

#[test]
fn init_on_its_own_line_of_the_block_form_stays() {
    expect_fmt("init_block", &[i_block_form()]);
}

#[test]
fn a_comment_at_the_end_of_the_line_of_an_init_stays() {
    expect_fmt("init_comment", &[i_comment()]);
}

// ---------------------------------------------------------------------------------------------------
// The `move` in the returned position (§5.2): it stays (W3-12, the user's decision of 2026-10-15)
// ---------------------------------------------------------------------------------------------------
//
// The user took back the rewrite of the returned `move` (changed by W3-12/i, the second U1 fix; U1/t had
// it taken off): `move K` of a constant `K` is E0711 for `onsa check`, and without the `move` it passes,
// but the syntax does not show whether a name is a local. `fmt` leaves every `move` as it is written; the
// `return` around it goes as any `return` in the tail position does.

fn m_returned() -> Case {
    case(
        "the move in the returned position stays, the return of the tail goes",
        &[
            "fn ret(move a: Buf[F32]) -> Buf[F32] {",
            "  return move a",
            "}",
            "",
            "fn tail(move a: Buf[F32]) -> Buf[F32] {",
            "  move a",
            "}",
            "",
            "fn arms(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c {",
            "    return move a",
            "  } else {",
            "    return move b",
            "  }",
            "}",
            "",
            "fn tail_arms(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c { move a } else { move b }",
            "}",
            "",
            "fn match_arms(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  match k {",
            "    0 => move a,",
            "    1 => { move b },",
            "    _ => {",
            "      return move a",
            "    },",
            "  }",
            "}",
        ],
        &[
            "fn ret(move a: Buf[F32]) -> Buf[F32] {",
            "  move a",
            "}",
            "",
            "fn tail(move a: Buf[F32]) -> Buf[F32] {",
            "  move a",
            "}",
            "",
            "fn arms(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c {",
            "    move a",
            "  } else {",
            "    move b",
            "  }",
            "}",
            "",
            "fn tail_arms(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c { move a } else { move b }",
            "}",
            "",
            "fn match_arms(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  match k {",
            "    0 => move a,",
            "    1 => { move b },",
            "    _ => {",
            "      move a",
            "    },",
            "  }",
            "}",
        ],
    )
}

/// An early `return move a` stays whole: the `return` is an early exit (§6.1) and the `move` stays.
fn m_early() -> Case {
    same(
        "move in an early return",
        &[
            "fn early(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c {",
            "    return move a",
            "  }",
            "  move b",
            "}",
        ],
    )
}

fn m_closure() -> Case {
    same(
        "move at the end of an anonymous function",
        &[
            "fn closure(move a: Buf[F32]) -> U32 uses {Alloc} {",
            "  let g = fn(move t: Buf[F32]) -> Buf[F32] { move t }",
            "  1",
            "}",
        ],
    )
}

fn m_kept_lines() -> Vec<&'static str> {
    vec![
        "pub struct Holder {",
        "  buf: Buf[F32],",
        "}",
        "",
        "fn take(move t: Buf[F32]) -> U32 uses {Alloc} {",
        "  t.len()",
        "}",
        "",
        "fn let_if(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {Alloc} {",
        "  let y = if c { move a } else { move b }",
        "  y",
        "}",
        "",
        "fn let_match(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {Alloc} {",
        "  let y = match k {",
        "    0 => move a,",
        "    _ => move b,",
        "  }",
        "  y",
        "}",
        "",
        "fn argument(move a: Buf[F32]) -> U32 uses {Alloc} {",
        "  take(move a)",
        "}",
        "",
        "fn assigned(move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {Alloc} {",
        "  var y = move a",
        "  y = move b",
        "  y",
        "}",
        "",
        "fn wrapped(move a: Buf[F32]) -> Holder uses {Alloc} {",
        "  Holder { buf: move a }",
        "}",
        "",
        "fn scrutinee(move o: Option[Buf[F32]]) -> U32 uses {Alloc} {",
        "  match move o {",
        "    Some(b) => { b.len() },",
        "    None => 0,",
        "  }",
        "}",
        "",
        "fn consumed_loop(move xs: [Buf[F32]; 2]) -> U32 uses {Alloc} {",
        "  var n = 0",
        "  for s in move xs {",
        "    n = n + s.len()",
        "  }",
        "  n",
        "}",
    ]
}

/// A `move` in a position where a value is consumed stays, in a file that also holds returned `move`s,
/// which stay too; the `return`s of the tail go.
fn m_beside_kept() -> Case {
    let mut input = m_kept_lines();
    input.extend([
        "",
        "fn returned(move a: Buf[F32]) -> Buf[F32] {",
        "  return move a",
        "}",
        "",
        "fn returned_holder(move a: Buf[F32]) -> Holder {",
        "  return Holder { buf: move a }",
        "}",
    ]);
    let mut expected = m_kept_lines();
    expected.extend([
        "",
        "fn returned(move a: Buf[F32]) -> Buf[F32] {",
        "  move a",
        "}",
        "",
        "fn returned_holder(move a: Buf[F32]) -> Holder {",
        "  Holder { buf: move a }",
        "}",
    ]);
    case("move in a consuming position and the returned one stay", &input, &expected)
}

fn m_kept() -> Case {
    same("move in a consuming position stays", &m_kept_lines())
}

fn move_cases() -> Vec<Case> {
    vec![m_returned(), m_early(), m_closure(), m_kept(), m_beside_kept()]
}

#[test]
fn move_in_the_returned_position_stays_and_the_return_around_it_goes() {
    expect_fmt("move_returned", &[m_returned()]);
}

#[test]
fn move_in_an_early_return_stays_with_the_return() {
    expect_fmt("move_early", &[m_early()]);
}

#[test]
fn move_at_the_end_of_an_anonymous_function_stays() {
    expect_fmt("move_closure", &[m_closure()]);
}

#[test]
fn move_in_a_consuming_position_stays() {
    expect_fmt("move_kept", &[m_kept()]);
}

#[test]
fn move_in_a_consuming_position_stays_in_a_file_that_has_returned_moves() {
    expect_fmt("move_beside", &[m_beside_kept()]);
}

/// The `move` of anything stays in the returned position: of a value that is not a place (§5.2: "`move`
/// needs a place", E0711 of `onsa check`), of a constant (E0711 too: it is no local), and of a place (a
/// name, a field, an element). The files with E0711 are checked for the syntax stage only.
#[test]
fn move_of_a_value_a_constant_and_a_place_stays() {
    expect_fmt(
        "move_any",
        &[
            same(
                "the move of a call and of a field of a call",
                &[
                    "struct H { b: Buf[F32] }",
                    "",
                    "fn g() -> Buf[F32] uses {Alloc} {",
                    "  Buf.zeroed(4)",
                    "}",
                    "",
                    "fn h() -> H uses {Alloc} {",
                    "  H { b: Buf.zeroed(4) }",
                    "}",
                    "",
                    "fn f(c: Bool) -> Buf[F32] uses {Alloc} {",
                    "  if c {",
                    "    return move g()",
                    "  }",
                    "  move h().b",
                    "}",
                ],
            )
            .syntax_only(),
            case(
                "the move of a constant",
                &["const K: I32 = 1", "", "fn f() -> I32 {", "  return move K", "}"],
                &["const K: I32 = 1", "", "fn f() -> I32 {", "  move K", "}"],
            )
            .syntax_only(),
            same(
                "the move of a name, of its field and of its element",
                &[
                    "struct H { b: Buf[F32] }",
                    "",
                    "fn f(move a: Buf[F32]) -> Buf[F32] {",
                    "  move a",
                    "}",
                    "",
                    "fn g(move a: H) -> Buf[F32] {",
                    "  move a.b",
                    "}",
                    "",
                    "fn h(move a: [Buf[F32]; 2]) -> Buf[F32] {",
                    "  move a[0]",
                    "}",
                ],
            )
            .syntax_only(),
        ],
    );
}

// ---------------------------------------------------------------------------------------------------
// Several rewrites in one place
// ---------------------------------------------------------------------------------------------------

fn x_combinations() -> Case {
    case(
        "several rewrites in one function",
        &[
            "fn all_of_them(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {} {",
            "  if c {",
            "    return move a",
            "  } else {",
            "    return move b",
            "  }",
            "}",
            "",
            "fn reset_all(inout x: I32) -> () uses {} {",
            "  x = 0",
            "  return",
            "}",
            "",
            "fn id[T](x: T) -> T uses {} {",
            "  return x",
            "}",
            "",
            "fn with_a_closure() -> U32 uses {} {",
            "  let g = fn(i: U32) -> U32 uses {} { return i * 2 }",
            "  return g.(2)",
            "}",
            "",
            "fn alloc_only(c: Bool, inout x: I32) -> () uses {Alloc} {",
            "  if c {",
            "    x = 1",
            "    return",
            "  } else {",
            "    x = 2",
            "    return",
            "  }",
            "}",
        ],
        &[
            "fn all_of_them(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {",
            "  if c {",
            "    move a",
            "  } else {",
            "    move b",
            "  }",
            "}",
            "",
            "fn reset_all(inout x: I32) {",
            "  x = 0",
            "}",
            "",
            "fn id[T](x: T) -> T {",
            "  x",
            "}",
            "",
            "fn with_a_closure() -> U32 {",
            // S-546: the empty `uses {}` of an anonymous function stays (changed by W3-12/i, the U1 fix).
            "  let g = fn(i: U32) -> U32 uses {} { i * 2 }",
            "  g.(2)",
            "}",
            "",
            "fn alloc_only(c: Bool, inout x: I32) uses {Alloc} {",
            "  if c {",
            "    x = 1",
            "  } else {",
            "    x = 2",
            "  }",
            "}",
        ],
    )
}

/// The example of the spec (§6.1) written with the `return` at the end, in a file with a `use`, and a public
/// function with a unit return type: the module in which the items are, and the `use` that brings the names.
/// `std.math.sum` is not in the std of this version (E0302), so the syntax stage only.
fn x_module() -> Case {
    case(
        "a use, public items and the rewrites in one module",
        &[
            "use std.math.{sum}",
            "",
            "pub fn mean[const N: U32](xs: [F64; N]) -> Option[F64] {",
            "  if xs.len() == 0 {",
            "    return None",
            "  }",
            "  return Some(sum(xs) / (xs.len() as F64))",
            "}",
            "",
            "pub fn total[const N: U32](xs: [F64; N]) -> F64 uses {} {",
            "  return sum(xs)",
            "}",
            "",
            "pub fn touch(inout x: F64) -> () uses {} {",
            "  x = x + 1.0",
            "  return",
            "}",
        ],
        &[
            "use std.math.{sum}",
            "",
            "pub fn mean[const N: U32](xs: [F64; N]) -> Option[F64] {",
            "  if xs.len() == 0 {",
            "    return None",
            "  }",
            "  Some(sum(xs) / (xs.len() as F64))",
            "}",
            "",
            "pub fn total[const N: U32](xs: [F64; N]) -> F64 {",
            "  sum(xs)",
            "}",
            "",
            "pub fn touch(inout x: F64) {",
            "  x = x + 1.0",
            "}",
        ],
    )
    .syntax_only()
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn rewrites_that_meet_in_one_function_are_all_done() {
    expect_fmt("combined", &[x_combinations()]);
}

// ---------------------------------------------------------------------------------------------------
// The reproductions R-78 (`tests/review-phase1/parent/r78.onsa`) and P-7 (`parent/p7.onsa`), with the
// expected texts worked out from the spec
// ---------------------------------------------------------------------------------------------------

/// The functions of `r78.onsa`, in their order. The comments of the file say what `fmt` has to make of each
/// (`fn unit_ret() {}`, `fn empty_uses() -> I32 { 1 }`, the `return` of the closure and of the branches
/// gone, `early` unchanged, `last` as it was). The comment on `pick` says "各腕を `v`、`0` にする": the
/// braces of the arms stay, because §3.3 changes the tree only by the closed list and a block is not a
/// bare expression in the tree, so the arms are `{ v }` and `{ 0 }`.
fn r78() -> Case {
    case(
        "the functions of r78.onsa",
        &[
            "fn unit_ret() -> () {}",
            "",
            "fn empty_uses() -> I32 uses {} { 1 }",
            "",
            "fn apply(f: fn(F32) -> (), x: F32) { f.(x) }",
            "",
            "fn set_one(inout x: I32) {",
            "  x = 1",
            "  return",
            "}",
            "",
            "fn closure() -> F32 {",
            "  let f = fn(x: F32) -> F32 { return x * 2.0 }",
            "  f.(1.0)",
            "}",
            "",
            "fn sign(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return -1",
            "  } else {",
            "    return 1",
            "  }",
            "}",
            "",
            "fn pick(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) => { return v },",
            "    None => { return 0 },",
            "  }",
            "}",
            "",
            "fn early(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return 0",
            "  }",
            "  x",
            "}",
            "",
            "fn last(x: I32) -> I32 {",
            "  let y = x + 1",
            "  return y",
            "}",
        ],
        &[
            "fn unit_ret() {}",
            "",
            "fn empty_uses() -> I32 { 1 }",
            "",
            "fn apply(f: fn(F32), x: F32) { f.(x) }",
            "",
            "fn set_one(inout x: I32) {",
            "  x = 1",
            "}",
            "",
            "fn closure() -> F32 {",
            "  let f = fn(x: F32) -> F32 { x * 2.0 }",
            "  f.(1.0)",
            "}",
            "",
            "fn sign(x: I32) -> I32 {",
            "  if x < 0 {",
            "    -1",
            "  } else {",
            "    1",
            "  }",
            "}",
            "",
            "fn pick(o: Option[I32]) -> I32 {",
            "  match o {",
            "    Some(v) => { v },",
            "    None => { 0 },",
            "  }",
            "}",
            "",
            "fn early(x: I32) -> I32 {",
            "  if x < 0 {",
            "    return 0",
            "  }",
            "  x",
            "}",
            "",
            "fn last(x: I32) -> I32 {",
            "  let y = x + 1",
            "  y",
            "}",
        ],
    )
}

/// The functions of `p7.onsa` as `fmt` sees them. Only `ret_move` changes: `return move a` is a `return` in
/// the tail position, which goes, and the `move` stays (the user took back S-100 on 2026-10-15; changed by
/// W3-12/i, the second U1 fix). The others are `move`s where a value is consumed or a function ends in
/// `if`/`match` without a `move`.
/// The file is not checked by `onsa check` (E0711 and E0703 are the modes of W4-09), so the syntax stage only.
fn p7() -> Case {
    let head = |name: &'static str| -> String {
        format!("fn {name}(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {{Alloc}} {{")
    };
    let keep: Vec<String> = vec![
        head("pick_let"),
        "  let y = if c { a } else { b }".into(),
        "  y".into(),
        "}".into(),
        "".into(),
        head("pick_let_moved"),
        "  let y = if c { move a } else { move b }".into(),
        "  y".into(),
        "}".into(),
        "".into(),
        head("pick_tail"),
        "  if c { a } else { b }".into(),
        "}".into(),
        "".into(),
        "fn pick_match(k: I32, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {Alloc} {".into(),
        "  let y = match k {".into(),
        "    0 => move a,".into(),
        "    _ => move b,".into(),
        "  }".into(),
        "  y".into(),
        "}".into(),
        "".into(),
        "fn take(move t: Buf[F32]) -> U32 uses {Alloc} { t.len() }".into(),
        "".into(),
        "fn pick_arg(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> U32 uses {Alloc} {".into(),
        "  take(if c { a } else { b })".into(),
        "}".into(),
        "".into(),
        "fn pick_arg_moved(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> U32 uses {Alloc} {".into(),
        "  take(if c { move a } else { move b })".into(),
        "}".into(),
        "".into(),
    ];
    let tail: Vec<String> = vec![
        "".into(),
        "fn workaround(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {Alloc} {".into(),
        "  var y: Buf[F32] = Buf.zeroed(0)".into(),
        "  if c { y = move a } else { y = move b }".into(),
        "  y".into(),
        "}".into(),
    ];
    let join = |mid: &[&str]| -> String {
        let mut v: Vec<&str> = keep.iter().map(String::as_str).collect();
        v.extend_from_slice(mid);
        v.extend(tail.iter().map(String::as_str));
        src(&v)
    };
    Case {
        what: "the functions of p7.onsa",
        input: join(&["fn ret_move(move a: Buf[F32]) -> Buf[F32] {", "  return move a", "}"]),
        expected: join(&["fn ret_move(move a: Buf[F32]) -> Buf[F32] {", "  move a", "}"]),
        level: Level::Syntax,
    }
}

/// Every case of this file in one test of `diff --ast`: the input and the expected text are the same program
/// (§3.5: both sides get the rewrites of §3.3 first), in both orders. The cases that take off `-> ()` and
/// `uses {}` (the second phase: `u_*` but `u_closures`, `x_*`, `r78`) are not here: those are no rewrites of
/// W3-12, and `diff --ast` tells them apart.
fn all_cases() -> Vec<Case> {
    let mut v = tail_cases();
    v.push(u_closures());
    v.extend(init_cases());
    v.extend(move_cases());
    v.push(p7());
    v
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn the_rewrites_in_a_module_with_a_use_and_public_items_are_all_done() {
    expect_fmt("module", &[x_module()]);
}

#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn r78_the_extra_information_of_r78_onsa_is_taken_off_as_its_comments_say() {
    expect_fmt("r78", &[r78()]);
}

#[test]
fn p7_the_return_of_p7_onsa_is_taken_off_and_every_move_stays() {
    expect_fmt("p7", &[p7()]);
}

#[test]
fn diff_ast_sees_a_file_and_its_rewritten_form_as_the_same_program() {
    let d = Dir::new("diff_same");
    let mut wrong = Vec::new();
    for (i, c) in all_cases().into_iter().enumerate() {
        for (k, (a, b)) in [(&c.input, &c.expected), (&c.expected, &c.input)].into_iter().enumerate() {
            let (rc, report) = diff_of(&d, &format!("p{i}_{k}"), a, b);
            if rc != 0 {
                wrong.push(format!("{} (order {k}): exit code {rc}: {report}", c.what));
            }
        }
    }
    assert!(wrong.is_empty(), "the rewritten form of a file is reported as a difference:\n{}", wrong.join("\n"));
}

// ---------------------------------------------------------------------------------------------------
// `diff --ast` still tells apart what is not a rewrite of §3.3 (they pass whether or not fmt rewrites)
// ---------------------------------------------------------------------------------------------------

fn flow_with(init: &str) -> String {
    src(&["pub flow f(x: F32 at sample) -> F32 at sample {", &format!("  {init}"), "}"])
}

#[test]
fn diff_ast_tells_apart_what_the_rewrites_of_fmt_keep() {
    let d = Dir::new("diff_apart");
    let mut wrong = Vec::new();
    let mut apart = |what: &str, a: String, b: String| {
        let (rc, report) = diff_of(&d, &format!("a{}", what.len()), &a, &b);
        if rc != 1 {
            wrong.push(format!("{what}: exit code {rc}, expected 1: {report}"));
        }
        let (rc, report) = diff_of(&d, &format!("b{}", what.len()), &b, &a);
        if rc != 1 {
            wrong.push(format!("{what} (reversed): exit code {rc}, expected 1: {report}"));
        }
    };
    // §11.4: only a literal equal to the default can be left out.
    apart("init 1.0 against no init", flow_with("prev~(x, 1.0)"), flow_with("prev~(x)"));
    apart("init -0.0 against no init", flow_with("prev~(x, -0.0)"), flow_with("prev~(x)"));
    apart("init 0.5 against 0.0", flow_with("delay~(x, 4, 0.5)"), flow_with("delay~(x, 4, 0.0)"));
    // §11.4: a user's flow has no default argument.
    apart(
        "the argument of a user's flow against none",
        src(&["pub flow g(x: F32 at sample) -> F32 at sample {", "  lag~(x, 0.0)", "}"]),
        src(&["pub flow g(x: F32 at sample) -> F32 at sample {", "  lag~(x)", "}"]),
    );
    // §8.1: only an empty `uses {}` is the same as none.
    apart("uses {Alloc} against none", src(&["fn a() uses {Alloc} {}"]), src(&["fn a() {}"]));
    // §5.2: a `move` in a consuming position is the mark that E0711 asks for.
    apart(
        "move in a let against none",
        src(&["fn a(move x: Buf[F32]) -> Buf[F32] {", "  let y = move x", "  y", "}"]),
        src(&["fn a(move x: Buf[F32]) -> Buf[F32] {", "  let y = x", "  y", "}"]),
    );
    apart(
        "move in an argument against none",
        src(&["fn a(move x: Buf[F32]) -> U32 {", "  take(move x)", "}"]),
        src(&["fn a(move x: Buf[F32]) -> U32 {", "  take(x)", "}"]),
    );
    apart(
        "move in a struct literal against none",
        src(&["fn a(move x: Buf[F32]) -> Holder {", "  Holder { buf: move x }", "}"]),
        src(&["fn a(move x: Buf[F32]) -> Holder {", "  Holder { buf: x }", "}"]),
    );
    // §5.2: the `move` in the returned position is no rewrite of W3-12 (the user's decision of 2026-10-15).
    apart(
        "a returned move against none",
        src(&["fn a(move x: Buf[F32]) -> Buf[F32] {", "  move x", "}"]),
        src(&["fn a(move x: Buf[F32]) -> Buf[F32] {", "  x", "}"]),
    );
    // §6.1: a `return` that is not in the tail position is an early exit.
    apart(
        "return in a loop against none",
        src(&["fn a(n: I32) -> I32 {", "  for i in 0 ..< n {", "    return i", "  }", "  0", "}"]),
        src(&["fn a(n: I32) -> I32 {", "  for i in 0 ..< n {", "    i", "  }", "  0", "}"]),
    );
    apart(
        "return in the value of a let against none",
        src(&["fn a(c: Bool) -> I32 {", "  let x = if c {", "    return 1", "  } else {", "    2", "  }", "  x", "}"]),
        src(&["fn a(c: Bool) -> I32 {", "  let x = if c {", "    1", "  } else {", "    2", "  }", "  x", "}"]),
    );
    // S-547: a `return` without a value is no rewrite of §3.3.
    apart(
        "a return without a value at the end against none",
        src(&["fn a(inout x: I32) {", "  x = 1", "  return", "}"]),
        src(&["fn a(inout x: I32) {", "  x = 1", "}"]),
    );
    apart(
        "an early return against a value at the end",
        src(&["fn a(c: Bool) -> I32 {", "  if c {", "    return 1", "  }", "  2", "}"]),
        src(&["fn a(c: Bool) -> I32 {", "  if c {", "    1", "  }", "  2", "}"]),
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

// ---------------------------------------------------------------------------------------------------
// W3-12/i, the second U1 fix: a comment in the range of the rewrite of a `return` (S-536 (1), S-538 (s2))
// ---------------------------------------------------------------------------------------------------

/// S-538 (s2), the user's decision of 2026-10-15: a comment at the end of a line belongs to the last code of
/// the line. In `return e // c` the last code is the end of `e`, which stays: the `return` goes (`e // c`).
/// A `return` without a value stays with or without a comment (S-547), and `diff --ast` tells a file with
/// it from the one without it (it is no rewrite of §3.3).
#[test]
fn a_return_without_a_value_stays_with_or_without_a_comment_and_one_with_a_value_goes() {
    expect_fmt(
        "return_comment",
        &[
            case(
                "a return without a value and a comment at the end of its line",
                &[
                    "fn a(inout x: I32) {",
                    "  x = 1 // first",
                    "  return // done",
                    "}",
                    "",
                    "fn b(c: Bool, inout x: I32) {",
                    "  if c {",
                    "    x = 1",
                    "    return // one",
                    "  } else {",
                    "    x = 2",
                    "    return",
                    "  }",
                    "}",
                    "",
                    "fn d(inout x: I32) {",
                    "  x = 1",
                    "  return",
                    "  return // last",
                    "}",
                ],
                &[
                    "fn a(inout x: I32) {",
                    "  x = 1  // first",
                    "  return // done",
                    "}",
                    "",
                    "fn b(c: Bool, inout x: I32) {",
                    "  if c {",
                    "    x = 1",
                    "    return // one",
                    "  } else {",
                    "    x = 2",
                    "    return",
                    "  }",
                    "}",
                    "",
                    "fn d(inout x: I32) {",
                    "  x = 1",
                    "  return",
                    "  return // last",
                    "}",
                ],
            ),
            case(
                "a return with a value and a comment at the end of its line",
                &[
                    "fn e(x: I32) -> I32 {",
                    "  return x + 1 // next",
                    "}",
                    "",
                    "fn f(c: Bool) -> I32 {",
                    "  if c {",
                    "    return 1 // one",
                    "  } else {",
                    "    return 2",
                    "  }",
                    "}",
                ],
                &[
                    "fn e(x: I32) -> I32 {",
                    "  x + 1 // next",
                    "}",
                    "",
                    "fn f(c: Bool) -> I32 {",
                    "  if c {",
                    "    1 // one",
                    "  } else {",
                    "    2",
                    "  }",
                    "}",
                ],
            ),
        ],
    );
    let d = Dir::new("return_comment_diff");
    let (rc, report) = diff_of(
        &d,
        "kept",
        &src(&["fn a(inout x: I32) {", "  x = 1", "  return // done", "}"]),
        &src(&["fn a(inout x: I32) {", "  x = 1", "}"]),
    );
    assert_eq!(rc, 1, "a `return` without a value is no rewrite of §3.3 (S-547): {report}");
}

/// S-547 (W3-12/b2 1 and 2): `tests/spec/fmt/rewrite_valueless_return_kept.onsa` has the `return`s without a
/// value after dead code that `onsa check` rejects (E0401, its markers) and that fmt took off or stopped on
/// (exit code 101). The cases harness does not ask fmt about a file with markers, so this test does: the
/// file is canonical, and `onsa check` says the same before and after `onsa fmt`.
#[test]
fn the_files_of_the_returns_without_a_value_are_canonical() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/spec/fmt/");
    let d = Dir::new("valueless_files");
    for name in ["rewrite_valueless_return_kept.onsa", "rewrite_tail_return_kept.onsa"] {
        let text = read(&format!("{root}{name}"));
        let p = d.file(name, &text);
        let before = onsa(&["check", &p]);
        let out = onsa(&["fmt", &p]);
        assert_eq!(code(&out), 0, "{name}: {out:?}");
        assert_eq!(read(&p), text, "{name}: fmt changed the file");
        let after = onsa(&["check", &p]);
        assert_eq!((code(&before), &before.stdout), (code(&after), &after.stdout), "{name}");
    }
    let marked = read(&format!("{root}rewrite_valueless_return_kept.onsa"));
    let p = d.file("marked.onsa", &marked);
    let out = onsa(&["check", &p]);
    let errors = String::from_utf8_lossy(&out.stdout).matches("error[E0401]").count();
    assert_eq!((code(&out), errors), (1, marked.matches("//~ E0401").count()), "{out:?}");
}

// ---------------------------------------------------------------------------------------------------
// W3-12/i U1 fix: an empty `uses {}` before another `uses` (W3-12/b 1), and the comments in and out of
// the range of a rewrite of `-> ()` and `uses {}` (S-536 (1), W3-12/b 2; those that take them off are of
// the second phase)
// ---------------------------------------------------------------------------------------------------

/// W3-12/b 1: §8.1 and §11.4 put a `uses` after the result of a function type on that function type, so
/// an empty `uses {}` before another `uses` is what keeps the second one on the function: without it,
/// `take(make())` would be E0401. `fmt` leaves it, and `diff --ast` tells the two programs apart.
#[test]
fn an_empty_uses_before_another_uses_stays() {
    expect_fmt(
        "uses_before_uses",
        &[
            same(
                "the result of a function",
                &[
                    "fn make() -> fn() -> I32 uses {} uses {Alloc} {",
                    "  fn() -> I32 { 1 }",
                    "}",
                    "",
                    "fn take(f: fn() -> I32) -> I32 {",
                    "  f()",
                    "}",
                    "",
                    "fn go() -> I32 uses {Alloc} {",
                    "  take(make())",
                    "}",
                ],
            ),
            same(
                "the result of an anonymous function",
                &[
                    "fn go() -> I32 uses {Alloc} {",
                    "  let m = fn() -> fn() -> I32 uses {} uses {Alloc} {",
                    "    fn() -> I32 { 1 }",
                    "  }",
                    "  let f = m()",
                    "  f()",
                    "}",
                ],
            ),
            same("a type alias", &["type Maker = fn() -> fn() -> I32 uses {} uses {Alloc}"]),
        ],
    );
    let d = Dir::new("uses_before_uses_diff");
    let (rc, report) = diff_of(
        &d,
        "inner",
        &src(&["fn f() -> fn() uses {} uses {Alloc} {}"]),
        &src(&["fn f() -> fn() uses {Alloc} {}"]),
    );
    assert_eq!(rc, 1, "`diff --ast` sees the `uses {{Alloc}}` of the function and of its result as one: {report}");
}

/// W3-12/b 1: of two empty rows in a row, both go in one pass.
#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn two_empty_uses_in_a_row_both_go() {
    expect_fmt(
        "uses_uses",
        &[case(
            "two empty rows: both go in one pass",
            &["type Maker = fn() -> fn() -> I32 uses {} uses {}"],
            &["type Maker = fn() -> fn() -> I32"],
        )],
    );
}

/// S-536 (1): with a comment in the range of a rewrite (between its tokens, or in the gap of a line break
/// that would go with them) its tokens stay; the `-> ()` and the `uses {}` that share such a gap both stay,
/// in one pass (W3-12/b 2). A comment out of the range (after a line end, at the edge of a list) stays on
/// its line and the tokens go.
#[test]
#[ignore = "P2: 第 2 期、`-> ()` と `uses {}` の除去は W3-12 から外した（利用者の決定、2026-10-15）"]
fn a_comment_in_the_range_of_a_rewrite_keeps_its_tokens_and_one_out_of_it_stays_on_its_line() {
    expect_fmt(
        "s536_range",
        &[
            same("a type alias", &["type T = fn(F32) -> () // c", "  uses {}"]),
            same("a type alias, a line of a comment", &["type T = fn(F32) -> ()", "  // c", "  uses {}"]),
            same("a head", &["fn h() -> () // c", "  uses {} {}"]),
            same("a parameter", &["fn p(f: fn(F32) -> () // c", "  uses {}) {}"]),
            same("a field", &["struct S {", "  a: fn(F32) -> () // c", "    uses {},", "}"]),
            same("a member of a trait", &["trait T {", "  fn a(self) -> () // c", "    uses {}", "}"]).syntax_only(),
            same(
                "a member of an extern block",
                &["extern \"C\" lib \"m\" {", "  fn e(x: F64) -> () // c", "    uses {}", "}"],
            )
            .syntax_only(),
            same("an operation of an effect", &["effect E {", "  fn op(x: F32) -> () // c", "    uses {}", "}"])
                .syntax_only(),
            case(
                "a comment between `->` and `()`: the `uses {}` after it goes",
                &["type T = fn(F32) -> // c", "  () uses {}"],
                &["type T = fn(F32) -> // c", "  ()"],
            ),
            case(
                "a comment after the edge of a list",
                &["struct S {", "  a: fn(F32) -> () // c", "}"],
                &["struct S {", "  a: fn(F32), // c", "}"],
            ),
            case(
                "a comment after a line end",
                &["trait T {", "  fn a(self) -> () // c", "  fn b(self)", "}"],
                &["trait T {", "  fn a(self) // c", "  fn b(self)", "}"],
            )
            .syntax_only(),
        ],
    );
}

// ---------------------------------------------------------------------------------------------------
// What no reading of §3.4 can decide: the tests keep what holds in every reading
// ---------------------------------------------------------------------------------------------------

/// Runs `fmt` on one input and checks what holds whatever the place of the comments is: the exit code 0, a
/// fixed point, every comment text once and in its order, the same program for `diff --ast`.
fn expect_comments_kept(tag: &str, text: &str, comments: &[&str]) {
    let d = Dir::new(tag);
    let orig = d.file("orig.onsa", text);
    let path = d.file("a.onsa", text);
    let out = onsa(&["check", &path]);
    assert_eq!(code(&out), 0, "the input does not pass `onsa check`: {out:?}\n{text}");
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let got = read(&path);
    let mut from = 0;
    for c in comments {
        assert_eq!(got.matches(c).count(), 1, "the comment `{c}` is not in the output once:\n{got}");
        let at = got.find(c).unwrap();
        assert!(at >= from, "the comment `{c}` is out of its order:\n{got}");
        from = at;
    }
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "the output is not a fixed point: {out:?}\n{got}");
    let out = onsa(&["diff", "--ast", &orig, &path]);
    assert_eq!(code(&out), 0, "`diff --ast` reports a difference: {out:?}\n{got}");
    let out = onsa(&["check", &path]);
    assert_eq!(code(&out), 0, "the output does not pass `onsa check`: {out:?}\n{got}");
}

#[test]
fn comments_of_a_statement_that_goes_are_kept_once_and_in_order() {
    // The statement `return` has gone and its comment is on its line (or on a line of its own after it):
    // where it goes is not in §3.4 (a gap of the spec), the comment is.
    expect_comments_kept(
        "gone_statement",
        &src(&[
            "fn a(inout x: I32) {",
            "  x = 1 // first",
            "  return // second",
            "}",
            "",
            "fn b(c: Bool, inout x: I32) {",
            "  if c {",
            "    x = 1",
            "    return // third",
            "  } else {",
            "    x = 2",
            "    return // fourth",
            "  }",
            "}",
            "",
            "fn c() {",
            "  return // fifth",
            "}",
        ]),
        &["// first", "// second", "// third", "// fourth", "// fifth"],
    );
}

#[test]
fn comments_of_an_init_that_goes_from_a_list_are_kept_once_and_in_order() {
    // The `init` is an element on a line of its own and the comment is on that line: where the comment goes
    // when the element has gone is not in §3.4 (a gap of the spec).
    expect_comments_kept(
        "gone_init",
        &src(&[
            "pub flow a(x: F32 at sample) -> F32 at sample {",
            "  let z = delay~(",
            "    x, // the signal",
            "    4, // samples",
            "    0.0, // silence",
            "  )",
            "  z",
            "}",
            "",
            "pub flow b(x: F32 at sample) -> F32 at sample {",
            "  let z = prev~(",
            "    x,",
            "    // quiet",
            "    0.0,",
            "  )",
            "  z",
            "}",
        ]),
        &["// the signal", "// samples", "// silence", "// quiet"],
    );
}

#[test]
fn a_comment_in_an_empty_uses_is_kept_once() {
    // Whether an empty `uses {}` that holds a comment goes with the comment or stays is not in §3.4.
    expect_comments_kept(
        "gone_uses",
        &src(&["fn a() -> I32 uses {", "  // nothing", "} {", "  1", "}"]),
        &["// nothing"],
    );
}

#[test]
fn spellings_of_a_negative_zero_integer_init_are_kept_or_taken_off_without_failing() {
    // `-0` is a prefix `-` and the literal `0`: whether it is "a literal equal to the default" is not in
    // §11.4 (a gap of the spec). Either way `fmt` writes the file, keeps a fixed point and the same program.
    let d = Dir::new("neg_zero");
    let text = src(&["pub flow a(n: I32 at sample) -> I32 at sample {", "  prev~(n, -0)", "}"]);
    let orig = d.file("orig.onsa", &text);
    let path = d.file("a.onsa", &text);
    let out = onsa(&["fmt", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let out = onsa(&["fmt", "--check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let out = onsa(&["diff", "--ast", &orig, &path]);
    assert_eq!(code(&out), 0, "{out:?}");
    let out = onsa(&["check", &path]);
    assert_eq!(code(&out), 0, "{out:?}");
}

// ---------------------------------------------------------------------------------------------------
// The way `fmt` writes (S-56): a temporary file and a rename, so nothing is left in the directory
// ---------------------------------------------------------------------------------------------------

const ROUGH: &str = "fn f(a: I32) -> I32 {\n  let x = 0XaB + a\n  return x\n}\n";
const ROUGH_OUT: &str = "fn f(a: I32) -> I32 {\n  let x = 0xAB + a\n  x\n}\n";
const FINE: &str = "fn g() -> I32 {\n  3\n}\n";
const BROKEN: &str = "fn h() -> I32 {\n  let a = 1;\n  a\n}\n";

#[test]
fn fmt_leaves_no_file_but_the_ones_it_was_given() {
    let d = Dir::new("no_leftover");
    let a = d.file("a.onsa", ROUGH);
    let b = d.file("b.onsa", FINE);
    let c = d.file("c.onsa", BROKEN);
    let before = d.names();
    let out = onsa(&["fmt", &a, &b, &c]);
    assert_eq!(code(&out), 2, "the file with the syntax error ends the command with 2: {out:?}");
    assert_eq!(d.names(), before, "no temporary file is left, and none is made for a file that is not written");
    assert_eq!(read(&a), ROUGH_OUT);
    assert_eq!(read(&b), FINE);
    assert_eq!(read(&c), BROKEN);
}

#[test]
fn fmt_of_a_file_alone_leaves_no_other_file() {
    let d = Dir::new("no_leftover_alone");
    let a = d.file("a.onsa", ROUGH);
    let before = d.names();
    let out = onsa(&["fmt", &a]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(d.names(), before);
    assert_eq!(read(&a), ROUGH_OUT);
    let out = onsa(&["fmt", &a]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(d.names(), before, "a second fmt, with nothing to change, leaves nothing either");
}

#[test]
fn fmt_check_changes_nothing_and_leaves_no_file() {
    let d = Dir::new("check_nothing");
    let a = d.file("a.onsa", ROUGH);
    let b = d.file("b.onsa", FINE);
    let c = d.file("c.onsa", BROKEN);
    let before = d.names();
    let stamp = |p: &str| {
        let m = std::fs::metadata(p).unwrap();
        (m.ino(), m.mtime(), m.mtime_nsec(), m.len())
    };
    let (sa, sb, sc) = (stamp(&a), stamp(&b), stamp(&c));
    let out = onsa(&["fmt", "--check", &a, &b, &c]);
    // A file to reformat is 1 and a syntax error is 2: a command with both ends with 2, the heavier (plan
    // S-261; changed by W3-12/i U1b, a decision of the parent: the test of W3-12/t took 1 or 2).
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(d.names(), before);
    assert_eq!((read(&a), read(&b), read(&c)), (ROUGH.to_string(), FINE.to_string(), BROKEN.to_string()));
    assert_eq!((stamp(&a), stamp(&b), stamp(&c)), (sa, sb, sc), "`fmt --check` does not touch the files");
    let out = onsa(&["fmt", "--check", &a, &b]);
    assert_eq!(code(&out), 1, "a file that would change ends `fmt --check` with 1: {out:?}");
    assert_eq!(d.names(), before);
    assert_eq!((read(&a), stamp(&a)), (ROUGH.to_string(), sa));
}

#[test]
fn fmt_writes_a_new_file_and_leaves_the_old_one_whole() {
    // S-56: the file is written to a temporary file and renamed over the name. A second name of the old
    // file (a hard link) shows it: the new text is under the name that was formatted, and the old file is
    // still the old text, never half written.
    let d = Dir::new("rename");
    let a = d.file("a.onsa", ROUGH);
    let link = d.0.join("link.onsa");
    std::fs::hard_link(&a, &link).unwrap();
    let old_ino = std::fs::metadata(&a).unwrap().ino();
    let out = onsa(&["fmt", &a]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_eq!(read(&a), ROUGH_OUT);
    assert_ne!(std::fs::metadata(&a).unwrap().ino(), old_ino, "the formatted file is a new file renamed over the name");
    assert_eq!(std::fs::read_to_string(&link).unwrap(), ROUGH, "the old file is not changed");
    assert_eq!(d.names(), vec!["a.onsa".to_string(), "link.onsa".to_string()]);
}
