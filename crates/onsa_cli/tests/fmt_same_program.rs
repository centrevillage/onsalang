//! `onsa fmt` writes what it formats, and `onsa diff --ast` agrees that it is the same program
//! (W3-11/t, unit U5; `spec/tools.md` §3.1, §3.2, §3.3, §3.4 and §3.5, spec §2.1, §2.4, §6.1 and §18.2;
//! plan S-56 and the review R-204).
//!
//! `onsa fmt` parses its output again before it writes, and compares it with the input: the AST with the
//! rewrites of §3.3 done on both sides, the doc comments, and the text of the ordinary comments in their
//! order (§3.5). A different output is a bug of `fmt`: the file is not written and the command ends with
//! the internal error 101. The failure itself cannot be made by a correct `fmt`, so it is not tested here
//! (the unit tests of the implementation do it). What these tests keep is the other side: **the check
//! must not stop a correct `fmt`**. Every change that `fmt` is allowed to make is made, in the shapes
//! that a comparison written too strictly would refuse, and the file must be written (exit code 0).
//!
//! What `fmt` changes without changing the program (§3.3, §3.2, §3.4):
//! - the `return` of the last statement of the body of a function, with the value (§3.3, §6.1) -- the
//!   other places of the tail position, the anonymous functions and the other rewrites of §3.3 are
//!   tested in `fmt_rewrites.rs` (W3-12), not here;
//! - the spelling of a number (§2.4, §3.2): the case of the prefix, the exponent and the hexadecimal
//!   digits, the `+` of an exponent, the `_`, the zeros in front of the integer part of a float;
//! - the white space, the line breaks, the indentation, the blank lines, and the `,` at the end of the
//!   elements of a list (§3.2);
//! - the place of a comment and the column of the comments at the end of consecutive lines (§3.4), the
//!   line break of a file in CR LF (§2.5, §3.2).
//!
//! What is here, and not in the other files of `fmt_*.rs`: the **combinations** of the changes (a
//! function that has a spelling to change and a `return` to take off; a `return` with a comment on its
//! line, with a line of a comment in front of it, or with an early `return` in the same body; the
//! spelling in a pattern, a `const` and the arguments of an attribute; a list that is closed up and a
//! `return` that is taken off in one call; the doc comments at every place that spec §2.1 lets them
//! stand, with the white space round them changed; a generic function, a `use`, a closure and a `par`).
//! The numbers in one place (`fmt_spellings_columns_ranges.rs`, `tests/spec/fmt/numeric_*.onsa`), the
//! places of the comments (`fmt_comments.rs`, `tests/spec/fmt/comments_places.onsa`), the lists
//! (`fmt_lines_lists.rs`) and the many files (`fmt_many_files.rs`) are not repeated.
//!
//! `onsa diff --ast` uses the same comparison of the trees, so it reports no difference between a file and
//! what `fmt` made of it (§3.5). It compares the structure alone (S-534 (a3), the user's decision of
//! 2026-10-15; the AST has no doc comments, D-02): a difference in a doc comment, its text or the
//! declaration it stands on, is no difference for it (changed by W3-12/i, the second U1 fix; the tests of
//! W3-11/t had it reported). The form of the report is not fixed by the spec (`spec/tools.md` §3.5
//! shows the exit code and the item that differs): the tests look at the exit code and at the name of the
//! declaration in the output.
//!
//! Every test has the whole text of the input and of the expected output. The expected texts are worked
//! out from the rules above and not taken from the output of `fmt`. Before `fmt` runs, the input and
//! the expected text are checked to have no diagnostic of the syntax stage (a file with one is not
//! rewritten, `onsa fmt` would end with 2, §18.2) and to pass `onsa check`. The output must be a fixed
//! point (`fmt --check` ends with 0 and another `fmt` changes nothing).
//!
//! What is not here, and why:
//! - the spaces at the end of the text of a comment and of a doc comment: the spec does not say whether
//!   `fmt` takes them off (S-532 (a), recorded; the doc comment has the same question). The tests with
//!   such a comment (`..._loose`) ask the exit code 0, a fixed point and the rest of the file as
//!   expected; the trailing white space of a line is not compared. What matters for the check is that
//!   either way `fmt` writes the file;
//! - the difference of two files that differ only in an ordinary comment: whether `diff --ast` reports
//!   it is a gap of the spec (S-534).
//!
//! Every test uses only the binary.

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
        let d = std::env::temp_dir().join(format!("onsa_fmt_u5_{}_{n}_{tag}", std::process::id()));
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

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// Everything the command wrote, the standard output and the standard error.
fn all_text(out: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// The lines joined, with one line break at the end of the file.
fn src(lines: &[&str]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

/// The text with the white space at the end of every line taken off.
fn trim_lines(text: &str) -> String {
    text.lines().map(str::trim_end).collect::<Vec<_>>().join("\n")
}

/// A file before and after `onsa fmt`: the whole text of each.
struct Case {
    what: &'static str,
    input: String,
    expected: String,
    /// The white space at the end of a line is not compared (a comment that ends in a blank, see the top).
    loose: bool,
    /// The change includes the `return` of the last statement of a function (§3.3), which `diff --ast`
    /// does not yet see as the same program.
    ret: bool,
}

fn case(what: &'static str, input: &[&str], expected: &[&str]) -> Case {
    Case { what, input: src(input), expected: src(expected), loose: false, ret: false }
}

fn text(what: &'static str, input: &str, expected: &str) -> Case {
    Case { what, input: input.to_string(), expected: expected.to_string(), loose: false, ret: false }
}

impl Case {
    /// The change takes off the `return` of the last statement of a function.
    fn ret(mut self) -> Case {
        self.ret = true;
        self
    }

    fn loose(mut self) -> Case {
        self.loose = true;
        self
    }
}

/// The text passes the syntax stage (`fmt --check` does not end with 2) and `onsa check` (exit code 0).
fn assert_valid(d: &Dir, name: &str, what: &str, which: &str, text: &str) {
    let p = d.file(name, text);
    let out = onsa(&["fmt", "--check", &p]);
    assert_ne!(code(&out), 2, "{what}: the {which} text has a diagnostic of the syntax stage: {out:?}");
    let out = onsa(&["check", &p]);
    assert_eq!(code(&out), 0, "{what}: `onsa check` finds a problem in the {which} text: {out:?}\n{text}");
}

/// Runs `onsa fmt` on every input (one command, so the files are written one after the other), expects
/// the exit code 0 (the check before writing lets a correct rewrite through), compares the whole text of
/// each output, and checks that the output is a fixed point.
fn expect_fmt(tag: &str, cases: &[Case]) {
    assert!(!cases.is_empty(), "no case to run");
    let d = Dir::new(tag);
    for (i, c) in cases.iter().enumerate() {
        assert_valid(&d, &format!("e{i}.onsa"), c.what, "expected", &c.expected);
        assert_valid(&d, &format!("i{i}.onsa"), c.what, "input", &c.input);
    }
    let paths: Vec<String> = cases.iter().enumerate().map(|(i, c)| d.file(&format!("c{i}.onsa"), &c.input)).collect();
    let mut args = vec!["fmt"];
    args.extend(paths.iter().map(String::as_str));
    let out = onsa(&args);
    assert_eq!(code(&out), 0, "onsa fmt must write the files (101 is the check before writing): {out:?}");
    let mut wrong = Vec::new();
    for (c, path) in cases.iter().zip(&paths) {
        let got = read(path);
        let same = if c.loose { trim_lines(&got) == trim_lines(&c.expected) } else { got == c.expected };
        if !same {
            wrong.push(format!("{}\n--- input\n{}--- expected\n{}--- got\n{got}", c.what, c.input, c.expected));
        }
    }
    assert!(wrong.is_empty(), "{} of {} files are not as expected:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    for (c, path) in cases.iter().zip(&paths) {
        let written = read(path);
        let out = onsa(&["fmt", "--check", path]);
        assert_eq!(code(&out), 0, "{}: the output is not a fixed point of fmt --check: {out:?}", c.what);
        let out = onsa(&["fmt", path]);
        assert_eq!(code(&out), 0, "{}: {out:?}", c.what);
        assert_eq!(read(path), written, "{}: a second fmt changes the output", c.what);
    }
}

/// The exit code and the whole output of `onsa diff --ast` on two texts.
fn diff_of(d: &Dir, tag: &str, a: &str, b: &str) -> (i32, String) {
    let pa = d.file(&format!("{tag}_a.onsa"), a);
    let pb = d.file(&format!("{tag}_b.onsa"), b);
    let out = onsa(&["diff", "--ast", &pa, &pb]);
    (code(&out), all_text(&out))
}

// ---------------------------------------------------------------------------------------------------
// The cases. Each is used by a test of `fmt` and, in the list `PAIRS`, by a test of `diff --ast`.
// ---------------------------------------------------------------------------------------------------

/// A function with a spelling to change and a `return` to take off, in the same body (§2.4, §3.3).
fn c_return_and_spellings() -> Case {
    case(
        "a spelling to change and the last return in one function",
        &[
            "fn f(a: I32) -> I32 {",
            "  let x = 0XaB + 1__000",
            "  return x + a",
            "}",
            "",
            "fn g(a: F64) -> F64 {",
            "  return a * 01.5 + 1E+3",
            "}",
        ],
        &[
            "fn f(a: I32) -> I32 {",
            "  let x = 0xAB + 1_000",
            "  x + a",
            "}",
            "",
            "fn g(a: F64) -> F64 {",
            "  a * 1.5 + 1e3",
            "}",
        ],
    )
    .ret()
}

/// The `return` has a comment at the end of its line (§3.4: the comment stays after the last code of
/// the line, one space after it when no column is to be kept).
fn c_return_comment_at_end() -> Case {
    case(
        "return with a comment at the end of its line",
        &[
            "fn f1() -> I32 {",
            "  return 1 // c",
            "}",
            "",
            "fn f2(a: I32) -> I32 {",
            "  let b = a + 1",
            "  return b      // c2",
            "}",
            "",
            "fn f3(a: I32) -> I32 {",
            "  return a + 1// c3",
            "}",
        ],
        &[
            "fn f1() -> I32 {",
            "  1 // c",
            "}",
            "",
            "fn f2(a: I32) -> I32 {",
            "  let b = a + 1",
            "  b // c2",
            "}",
            "",
            "fn f3(a: I32) -> I32 {",
            "  a + 1 // c3",
            "}",
        ],
    )
    .ret()
}

/// Lines of comments in front of the `return` (they stay in front of the element that follows, §3.4).
fn c_return_comment_before() -> Case {
    case(
        "return with lines of comments in front of it",
        &[
            "fn f(a: I32) -> I32 {",
            "  let b = a + 1",
            "        // before",
            "  return b",
            "}",
            "",
            "fn g(a: I32) -> I32 {",
            "  let b = a + 1",
            "  // one",
            "  // two",
            "",
            "",
            "  // three",
            "  return b",
            "}",
        ],
        &[
            "fn f(a: I32) -> I32 {",
            "  let b = a + 1",
            "  // before",
            "  b",
            "}",
            "",
            "fn g(a: I32) -> I32 {",
            "  let b = a + 1",
            "  // one",
            "  // two",
            "",
            "  // three",
            "  b",
            "}",
        ],
    )
    .ret()
}

/// An early `return` (not in the tail position, §6.1) stays, and the last one is taken off.
fn c_early_returns() -> Case {
    case(
        "early returns stay, the last one goes",
        &[
            "fn f(a: I32) -> I32 {",
            "if a<0 {",
            "    return 0",
            "}",
            "  for i in 0..<3 {",
            "        if i==a {",
            "      return i",
            "        }",
            "  }",
            "return   a",
            "}",
        ],
        &[
            "fn f(a: I32) -> I32 {",
            "  if a < 0 {",
            "    return 0",
            "  }",
            "  for i in 0 ..< 3 {",
            "    if i == a {",
            "      return i",
            "    }",
            "  }",
            "  a",
            "}",
        ],
    )
    .ret()
}

/// A method in an `impl` with a doc comment at a wrong indentation, a `return` to take off, and a
/// struct whose last field has no `,` (§2.1: a member of an `impl` takes a doc comment).
fn c_impl_docs_and_return() -> Case {
    case(
        "a method with a doc comment and a return, in an impl",
        &[
            "struct P {",
            "  x: F32,",
            "  y: F32",
            "}",
            "",
            "impl P {",
            "      /// Reads x.",
            "  pub fn get_x(self) -> F32 {",
            "        return self.x",
            "  }",
            "",
            "",
            "/// Makes one.",
            "  pub fn new(x:F32,y:F32)->P{",
            "      return P{x:x,y:y}",
            "  }",
            "}",
        ],
        &[
            "struct P {",
            "  x: F32,",
            "  y: F32,",
            "}",
            "",
            "impl P {",
            "  /// Reads x.",
            "  pub fn get_x(self) -> F32 {",
            "    self.x",
            "  }",
            "",
            "  /// Makes one.",
            "  pub fn new(x: F32, y: F32) -> P {",
            "    P { x: x, y: y }",
            "  }",
            "}",
        ],
    )
    .ret()
}

/// The spellings in a `const`, in the patterns of a `match`, and in the arguments of an attribute, next
/// to a `return` that is taken off; the attribute of a flow input is moved to a line of its own in the
/// block form (§3.2).
fn c_spellings_in_places_and_return() -> Case {
    case(
        "spellings in a const, a pattern and an attribute, and a return",
        &[
            "const LIMIT: I32 = 1__000",
            "",
            "const GAIN: F32 = 01.5",
            "",
            "fn pick(a: I32) -> I32 {",
            "  let r = match a {",
            "    0XFF | 0B1_0 => LIMIT,",
            "    1__0 => 1_,",
            "    _ => 0,",
            "  }",
            "  return r",
            "}",
            "",
            "flow g(",
            "  @param(min: 0.0, max: 1E+1, default: 05.0) level: F32 at block,",
            "  x: F32 at sample,",
            ") -> F32 at sample {",
            "  x * level",
            "}",
        ],
        &[
            "const LIMIT: I32 = 1_000",
            "",
            "const GAIN: F32 = 1.5",
            "",
            "fn pick(a: I32) -> I32 {",
            "  let r = match a {",
            "    0xFF | 0b1_0 => LIMIT,",
            "    1_0 => 1,",
            "    _ => 0,",
            "  }",
            "  r",
            "}",
            "",
            "flow g(",
            "  @param(min: 0.0, max: 1e1, default: 5.0)",
            "  level: F32 at block,",
            "  x: F32 at sample,",
            ") -> F32 at sample {",
            "  x * level",
            "}",
        ],
    )
    .ret()
}

/// The `,` that is put in the block form and taken off the one-line form, the blank lines, the white
/// space and the `return` in one function.
fn c_commas_blank_lines_and_return() -> Case {
    case(
        "commas, blank lines, white space and a return",
        &[
            "fn add(a: I32, b: I32) -> I32 {",
            "  a + b",
            "}",
            "",
            "fn  f(",
            "a: I32,",
            "b: I32",
            ") -> I32 {",
            "",
            "",
            "",
            "let x=add(a,b,)",
            "",
            "",
            "return   x + 1_",
            "",
            "",
            "",
            "}",
        ],
        &[
            "fn add(a: I32, b: I32) -> I32 {",
            "  a + b",
            "}",
            "",
            "fn f(",
            "  a: I32,",
            "  b: I32,",
            ") -> I32 {",
            "  let x = add(a, b)",
            "",
            "  x + 1",
            "}",
        ],
    )
    .ret()
}

/// Tabs and an indentation that does not match, with a `return` in front of a name.
fn c_tabs_and_return() -> Case {
    text(
        "tabs, odd indentation and a return",
        "fn f(a: I32) -> I32 {\n\tlet r = if a > 0 {\n\t\t\t1\n\t} else {\n\t\t2\n\t}\n\t\treturn   r\n}\n",
        "fn f(a: I32) -> I32 {\n  let r = if a > 0 {\n    1\n  } else {\n    2\n  }\n  r\n}\n",
    )
    .ret()
}

/// A file in CR LF (spec §2.5): a comment line, a comment at the end of the `return` line, the output in
/// LF. The text of a comment does not hold the CR.
fn c_crlf_comments_and_return() -> Case {
    text(
        "a file in CR LF with comments and a return",
        "fn f(a: I32) -> I32 {\r\n  // line\r\n  return a // c\r\n}\r\n",
        "fn f(a: I32) -> I32 {\n  // line\n  a // c\n}\n",
    )
    .ret()
}

/// Comments in a call of the block form and in a continuation, with a `return` taken off in front of the
/// call and in front of the operand.
fn c_comments_in_lists_and_continuations() -> Case {
    case(
        "comments inside a list and a continuation under a return",
        &[
            "fn add(a: I32, b: I32) -> I32 {",
            "  a + b",
            "}",
            "",
            "fn f(a: I32) -> I32 {",
            "  let s = add(",
            "    a, // first",
            "    a // second",
            "  )",
            "  // keep",
            "  return add(",
            "    s, // c1",
            "    1__0 // c2",
            "  )",
            "}",
            "",
            "fn g(a: I32, b: I32) -> I32 {",
            "  let c = a +   // plus",
            "  b",
            "  return c * // times",
            "b",
            "}",
        ],
        &[
            "fn add(a: I32, b: I32) -> I32 {",
            "  a + b",
            "}",
            "",
            "fn f(a: I32) -> I32 {",
            "  let s = add(",
            "    a, // first",
            "    a, // second",
            "  )",
            "  // keep",
            "  add(",
            "    s,   // c1",
            "    1_0, // c2",
            "  )",
            "}",
            "",
            "fn g(a: I32, b: I32) -> I32 {",
            "  let c = a + // plus",
            "    b",
            "  c * // times",
            "    b",
            "}",
        ],
    )
    .ret()
}

/// A comment that ends in blanks (a space, a tab), on a line of its own and after code, and the
/// code of the line also ends in blanks. Whether `fmt` takes the blanks off the comment is not decided
/// (S-532 (a)), so only the exit code 0, the fixed point and the rest are asked.
fn c_comment_trailing_blanks_loose() -> Case {
    text(
        "comments that end in a space or a tab, and a return",
        "fn f(a: I32) -> I32 {   \n  // alone   \n  let b = a + 1   // note   \n  let c = b\n  return c\t// tab\t\n}\n",
        "fn f(a: I32) -> I32 {\n  // alone\n  let b = a + 1 // note\n  let c = b\n  c // tab\n}\n",
    )
    .ret()
    .loose()
}

/// A doc comment at every place that spec §2.1 lets one stand (a struct and its fields, an enum and its
/// variants, a flow and its inputs, a `const`, a `type`), with the white space round them changed: the
/// indentation, a blank line that stays (one), two that become one, the braces and the lists.
fn c_docs_at_every_target() -> Case {
    case(
        "doc comments at the items, the fields, the variants and the inputs",
        &[
            "/// A point.",
            "pub  struct Pt{",
            "    /// The x.",
            "  x:F32,",
            "",
            " /// The y.",
            "  y:F32",
            "}",
            "",
            "",
            "/// The modes.",
            "pub enum  Mode {",
            "/// Off.",
            "Off,",
            "        /// On.",
            "On( I32 ,I32 )",
            "}",
            "/// A gain.",
            "pub flow gain(",
            "          /// The input.",
            "x:F32 at sample,",
            "/// The level.",
            "level:F32  at block",
            ")->F32 at sample{",
            "x*level",
            "}",
            "",
            "   /// The limit.",
            "const LIMIT: I32 = 16",
            "",
            "/// An alias.",
            "type Idx = U32",
        ],
        &[
            "/// A point.",
            "pub struct Pt {",
            "  /// The x.",
            "  x: F32,",
            "",
            "  /// The y.",
            "  y: F32,",
            "}",
            "",
            "/// The modes.",
            "pub enum Mode {",
            "  /// Off.",
            "  Off,",
            "  /// On.",
            "  On(I32, I32),",
            "}",
            "/// A gain.",
            "pub flow gain(",
            "  /// The input.",
            "  x: F32 at sample,",
            "  /// The level.",
            "  level: F32 at block,",
            ") -> F32 at sample {",
            "  x * level",
            "}",
            "",
            "/// The limit.",
            "const LIMIT: I32 = 16",
            "",
            "/// An alias.",
            "type Idx = U32",
        ],
    )
}

/// A doc comment with a blank line, a plain comment and an attribute between it and the item (spec
/// §2.1: it still belongs to the item), and the attribute that stands on a line of its own.
fn c_doc_before_blank_comment_attribute() -> Case {
    case(
        "a doc comment, a blank line, a comment and an attribute before an item",
        &["   /// Doc.", "", "", "// plain", "@repr(c) pub struct Q{x:F32}"],
        &["/// Doc.", "", "// plain", "@repr(c)", "pub struct Q { x: F32 }"],
    )
}

/// A doc comment that ends in blanks, on an item and on a field (S-532 (a) asks the same of a doc comment
/// as of a comment: the spec does not say), and the code round it changes.
fn c_doc_trailing_blanks_loose() -> Case {
    text(
        "doc comments that end in a space or a tab",
        "/// Gain.   \nfn  h(a:I32)->I32{\nreturn a\n}\n\npub struct R {\n  /// Field\t\n  x: I32,\n}\n",
        "/// Gain.\nfn h(a: I32) -> I32 {\n  a\n}\n\npub struct R {\n  /// Field\n  x: I32,\n}\n",
    )
    .ret()
    .loose()
}

/// A `use` with a `,` at the end, a generic function and a function that takes the square root, with the
/// `return` taken off.
fn c_module_generic_and_return() -> Case {
    case(
        "a use list, a generic function, an import and a return",
        &[
            "use  std.math.{ sqrt , }",
            "",
            "pub fn hyp(a:F32,b:F32)->F32{",
            "return sqrt(a*a+b*b)",
            "}",
            "",
            "fn same[T](x:T)->T{",
            "return x",
            "}",
        ],
        &[
            "use std.math.{sqrt}",
            "",
            "pub fn hyp(a: F32, b: F32) -> F32 {",
            "  sqrt(a * a + b * b)",
            "}",
            "",
            "fn same[T](x: T) -> T {",
            "  x",
            "}",
        ],
    )
    .ret()
}

/// A closure in the argument of a call, with the `return` of the function taken off after it.
fn c_closure_and_return() -> Case {
    case(
        "a closure in a call and a return",
        &[
            "use std.array",
            "",
            "fn f() -> U32 {",
            "  let xs: [U32; 4] = array.from_fn(fn(i){i*2})",
            "  return xs[3]",
            "}",
        ],
        &[
            "use std.array",
            "",
            "fn f() -> U32 {",
            "  let xs: [U32; 4] = array.from_fn(fn(i) { i * 2 })",
            "  xs[3]",
            "}",
        ],
    )
    .ret()
}

/// A flow with a `par` and no `return` (a flow body has no `return` to take off): the white space and
/// the line breaks of the head and the body.
fn c_par_flow() -> Case {
    case(
        "a par in a flow",
        &[
            "flow bank(x: F32 at sample) -> F32 at sample {",
            "  let v=par i in 0..<4{",
            "      x*2.0",
            "  }",
            "  v[0]",
            "}",
        ],
        &[
            "flow bank(x: F32 at sample) -> F32 at sample {",
            "  let v = par i in 0 ..< 4 {",
            "    x * 2.0",
            "  }",
            "  v[0]",
            "}",
        ],
    )
}

fn all_cases() -> Vec<Case> {
    vec![
        c_return_and_spellings(),
        c_return_comment_at_end(),
        c_return_comment_before(),
        c_early_returns(),
        c_impl_docs_and_return(),
        c_spellings_in_places_and_return(),
        c_commas_blank_lines_and_return(),
        c_tabs_and_return(),
        c_crlf_comments_and_return(),
        c_comments_in_lists_and_continuations(),
        c_comment_trailing_blanks_loose(),
        c_docs_at_every_target(),
        c_doc_before_blank_comment_attribute(),
        c_doc_trailing_blanks_loose(),
        c_module_generic_and_return(),
        c_closure_and_return(),
        c_par_flow(),
    ]
}

// ---------------------------------------------------------------------------------------------------
// `onsa fmt` writes: the check before writing lets the correct rewrites through (R-204, S-56).
// ---------------------------------------------------------------------------------------------------

#[test]
fn a_return_and_a_spelling_in_one_function_are_written() {
    expect_fmt("ret_spell", &[c_return_and_spellings()]);
}

#[test]
fn a_return_with_a_comment_at_the_end_of_its_line_is_written() {
    expect_fmt("ret_comment_end", &[c_return_comment_at_end()]);
}

#[test]
fn a_return_with_lines_of_comments_in_front_of_it_is_written() {
    expect_fmt("ret_comment_before", &[c_return_comment_before()]);
}

#[test]
fn early_returns_next_to_the_last_return_are_written() {
    expect_fmt("ret_early", &[c_early_returns()]);
}

#[test]
fn a_method_with_a_doc_comment_and_a_return_is_written() {
    expect_fmt("ret_impl", &[c_impl_docs_and_return()]);
}

#[test]
fn spellings_in_a_const_a_pattern_and_an_attribute_next_to_a_return_are_written() {
    expect_fmt("spell_places", &[c_spellings_in_places_and_return()]);
}

#[test]
fn commas_blank_lines_and_white_space_with_a_return_are_written() {
    expect_fmt("commas_blank", &[c_commas_blank_lines_and_return()]);
}

#[test]
fn tabs_and_odd_indentation_with_a_return_are_written() {
    expect_fmt("tabs", &[c_tabs_and_return()]);
}

#[test]
fn a_crlf_file_with_comments_and_a_return_is_written_in_lf() {
    expect_fmt("crlf", &[c_crlf_comments_and_return()]);
}

#[test]
fn comments_in_lists_and_continuations_under_a_return_are_written() {
    expect_fmt("comments_lists", &[c_comments_in_lists_and_continuations()]);
}

#[test]
fn comments_that_end_in_blanks_are_written_loose() {
    expect_fmt("comment_blanks", &[c_comment_trailing_blanks_loose()]);
}

#[test]
fn doc_comments_at_every_target_with_the_white_space_round_them_changed_are_written() {
    expect_fmt("docs_targets", &[c_docs_at_every_target()]);
}

#[test]
fn a_doc_comment_before_a_blank_line_a_comment_and_an_attribute_is_written() {
    expect_fmt("doc_attr", &[c_doc_before_blank_comment_attribute()]);
}

#[test]
fn doc_comments_that_end_in_blanks_are_written_loose() {
    expect_fmt("doc_blanks", &[c_doc_trailing_blanks_loose()]);
}

#[test]
fn a_use_list_a_generic_function_and_a_return_are_written() {
    expect_fmt("module_generic", &[c_module_generic_and_return()]);
}

#[test]
fn a_closure_in_a_call_and_a_return_are_written() {
    expect_fmt("closure", &[c_closure_and_return()]);
}

#[test]
fn a_par_in_a_flow_is_written() {
    expect_fmt("par", &[c_par_flow()]);
}

/// All of them in one command: the files are written one after the other, and a check that fails for
/// one stops no other (and a loose case and a strict case do not disturb each other).
#[test]
fn all_the_cases_in_one_command_are_written() {
    expect_fmt("all", &all_cases());
}

// ---------------------------------------------------------------------------------------------------
// `onsa fmt --check`: a file that differs by the `return` only is "would reformat", not an internal error.
// ---------------------------------------------------------------------------------------------------

#[test]
fn fmt_check_of_a_file_that_differs_by_the_last_return_only_reports_it_with_1() {
    let d = Dir::new("check_ret");
    let with_return = src(&["fn f(a: I32) -> I32 {", "  let b = a + 1", "  return b", "}"]);
    let p = d.file("r.onsa", &with_return);
    let out = onsa(&["fmt", "--check", &p]);
    assert_eq!(code(&out), 1, "a file that fmt would change ends with 1, not with the 101 of the check: {out:?}");
    let report = all_text(&out);
    assert!(report.contains(&format!("would reformat {p}")), "`would reformat <path>` in the output: {out:?}");
    assert_eq!(read(&p), with_return, "--check writes nothing");
    // The same file in the form that fmt writes is accepted.
    let canonical = src(&["fn f(a: I32) -> I32 {", "  let b = a + 1", "  b", "}"]);
    let q = d.file("c.onsa", &canonical);
    let out = onsa(&["fmt", "--check", &q]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert!(!all_text(&out).contains("would reformat"), "{out:?}");
}

/// The files that differ from their formatted form in one of the allowed ways only: each is "would
/// reformat" with 1, none stops with 101 or 2, and none is written.
#[test]
fn fmt_check_of_every_case_is_1_and_writes_nothing() {
    let d = Dir::new("check_all");
    let cases = all_cases();
    for (i, c) in cases.iter().enumerate() {
        let p = d.file(&format!("k{i}.onsa"), &c.input);
        let out = onsa(&["fmt", "--check", &p]);
        assert_eq!(code(&out), 1, "{}: {out:?}", c.what);
        assert!(all_text(&out).contains(&format!("would reformat {p}")), "{}: {out:?}", c.what);
        assert_eq!(read(&p), c.input, "{}: --check writes nothing", c.what);
    }
}

// ---------------------------------------------------------------------------------------------------
// Several files (§3.1): one file is rewritten, one is refused, one is already in the normal form.
// ---------------------------------------------------------------------------------------------------

#[test]
fn a_file_with_a_return_a_file_with_a_syntax_error_and_a_normal_file_in_one_command() {
    let d = Dir::new("many");
    let ret_in = src(&["fn  a( ) -> I32 {", " let x = 0XFF", " return x", "}"]);
    let ret_out = src(&["fn a() -> I32 {", "  let x = 0xFF", "  x", "}"]);
    let bad = src(&["fn b() -> I32 {", "  let a = 1;", "  return a", "}"]);
    let normal = src(&["fn c() -> I32 {", "  3", "}"]);
    let a = d.file("a.onsa", &ret_in);
    let b = d.file("b.onsa", &bad);
    let c = d.file("c.onsa", &normal);
    for (what, text) in [("a", &ret_out), ("c", &normal)] {
        assert_valid(&d, &format!("v_{what}.onsa"), what, "expected", text);
    }
    let out = onsa(&["fmt", &a, &b, &c]);
    assert_eq!(code(&out), 2, "the syntax diagnostic of one file ends the command with 2, not 101: {out:?}");
    assert_eq!(read(&a), ret_out, "the file with the return is rewritten");
    assert_eq!(read(&b), bad, "the file with the syntax diagnostic is not written");
    assert_eq!(read(&c), normal, "the normal file stays");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("b.onsa") && stdout.contains("error[E0020]"),
        "the diagnostic of the refused file: {out:?}"
    );
    // The order of the files does not matter.
    let out = onsa(&["fmt", &c, &b, &a]);
    assert_eq!(code(&out), 2, "{out:?}");
    assert_eq!(read(&a), ret_out);
}

// ---------------------------------------------------------------------------------------------------
// `onsa diff --ast` (§3.5): the same comparison, so no difference between a file and its formatted form.
// ---------------------------------------------------------------------------------------------------

/// Every pair (input, expected) of the cases for which `keep` is true is "no difference" (exit code 0), in
/// both orders.
fn expect_no_difference(tag: &str, keep: impl Fn(&Case) -> bool) {
    let d = Dir::new(tag);
    let mut wrong = Vec::new();
    for (i, c) in all_cases().iter().enumerate().filter(|(_, c)| keep(c)) {
        for (k, (a, b)) in [(&c.input, &c.expected), (&c.expected, &c.input)].into_iter().enumerate() {
            let (rc, report) = diff_of(&d, &format!("p{i}_{k}"), a, b);
            if rc != 0 {
                wrong.push(format!("{} (order {k}): exit code {rc}: {report}", c.what));
            }
        }
    }
    assert!(wrong.is_empty(), "the formatted form of a file is reported as a difference:\n{}", wrong.join("\n"));
}

/// The cases without the `return` (the doc comments, the white space, the `par`) and the cases that no
/// comparison of a comment or of a doc comment can tell apart.
#[test]
fn a_file_and_its_formatted_form_without_a_return_are_not_a_difference() {
    expect_no_difference("same_no_ret", |c| !c.ret && !c.loose);
}

/// The input and the output of every case that takes a `return` off (§3.3): the same program.
#[test]
fn a_file_and_its_formatted_form_with_the_last_return_taken_off_are_not_a_difference() {
    expect_no_difference("same_ret", |c| c.ret && !c.loose);
}

#[test]
fn the_last_return_and_its_value_alone_are_not_a_difference() {
    let d = Dir::new("ret_alone");
    let with_return = src(&["fn f() -> I32 {", "  return 1", "}"]);
    let without = src(&["fn f() -> I32 {", "  1", "}"]);
    for (k, (a, b)) in [(&with_return, &without), (&without, &with_return)].into_iter().enumerate() {
        let (rc, report) = diff_of(&d, &format!("alone{k}"), a, b);
        assert_eq!(rc, 0, "`return 1` against `1` (order {k}): {report}");
    }
    // The same function with its return and a comment on the same line, in both files (the comment is the
    // same, so it is not a difference whether or not `diff --ast` compares the comments).
    let (rc, report) = diff_of(
        &d,
        "alone_c",
        &src(&["fn f() -> I32 {", "  return 1 // c", "}"]),
        &src(&["fn f() -> I32 {", "  1 // c", "}"]),
    );
    assert_eq!(rc, 0, "`return 1 // c` against `1 // c`: {report}");
}

/// What `diff --ast` must still tell apart: the other `return`s (§6.1: not in the tail position it is an
/// early exit), another value, another declaration.
#[test]
fn a_return_that_is_not_the_last_statement_or_has_another_value_is_a_difference() {
    let d = Dir::new("ret_diff");
    let early = src(&[
        "fn f(a: I32) -> I32 {",
        "  for i in 0 ..< 3 {",
        "    if i == a {",
        "      return i",
        "    }",
        "  }",
        "  7",
        "}",
    ]);
    let no_exit = src(&[
        "fn f(a: I32) -> I32 {",
        "  for i in 0 ..< 3 {",
        "    if i == a {",
        "      i",
        "    }",
        "  }",
        "  7",
        "}",
    ]);
    let (rc, report) = diff_of(&d, "early", &early, &no_exit);
    assert_eq!(rc, 1, "an early `return` is not removed: {report}");
    let one = src(&["fn f() -> I32 {", "  return 1", "}"]);
    let two = src(&["fn f() -> I32 {", "  return 2", "}"]);
    let (rc, report) = diff_of(&d, "values", &one, &two);
    assert_eq!(rc, 1, "`return 1` against `return 2`: {report}");
    let (rc, report) = diff_of(&d, "values_plain", &one, &src(&["fn f() -> I32 {", "  2", "}"]));
    assert_eq!(rc, 1, "`return 1` against `2`: {report}");
}

// ---------------------------------------------------------------------------------------------------
// Doc comments: `diff --ast` compares the structure alone (S-534 (a3)), so a different text of a doc
// comment is no difference, a different place neither.
// ---------------------------------------------------------------------------------------------------

/// Two files that differ in a doc comment only: `diff --ast` reports no difference (the declaration
/// `name` is not named).
fn expect_no_doc_difference(tag: &str, name: &str, a: &str, b: &str) {
    let d = Dir::new(tag);
    for (k, (x, y)) in [(a, b), (b, a)].into_iter().enumerate() {
        let (rc, report) = diff_of(&d, &format!("d{k}"), x, y);
        assert_eq!(rc, 0, "{tag} (order {k}): only a doc comment differs: {report}\n{x}\n{y}");
        assert!(!report.contains(name), "{tag} (order {k}): the declaration `{name}` is not named: {report}");
    }
}

const DOC_ITEM: &str = "fn gain_curve() -> I32 {\n  1\n}\n";

#[test]
fn a_doc_comment_of_another_text_on_an_item_is_no_difference() {
    expect_no_doc_difference(
        "doc_item",
        "gain_curve",
        &format!("/// One.\n{DOC_ITEM}"),
        &format!("/// Two.\n{DOC_ITEM}"),
    );
}

#[test]
fn a_doc_comment_of_another_text_on_a_field_is_no_difference() {
    expect_no_doc_difference(
        "doc_field",
        "Zeta",
        "struct Zeta {\n  /// One.\n  x: F32,\n}\n",
        "struct Zeta {\n  /// Two.\n  x: F32,\n}\n",
    );
}

#[test]
fn a_doc_comment_of_another_text_on_a_variant_is_no_difference() {
    expect_no_doc_difference(
        "doc_variant",
        "Omega",
        "enum Omega {\n  /// One.\n  A,\n  B,\n}\n",
        "enum Omega {\n  /// Two.\n  A,\n  B,\n}\n",
    );
}

#[test]
fn a_doc_comment_of_another_text_on_a_flow_input_is_no_difference() {
    expect_no_doc_difference(
        "doc_input",
        "mixer",
        "flow mixer(\n  /// One.\n  x: F32 at sample,\n) -> F32 at sample {\n  x\n}\n",
        "flow mixer(\n  /// Two.\n  x: F32 at sample,\n) -> F32 at sample {\n  x\n}\n",
    );
}

#[test]
fn a_doc_comment_of_another_text_on_a_member_of_an_impl_is_no_difference() {
    expect_no_doc_difference(
        "doc_member",
        "Sigma",
        "struct Sigma {\n  x: F32,\n}\n\nimpl Sigma {\n  /// One.\n  pub fn get(self) -> F32 {\n    self.x\n  }\n}\n",
        "struct Sigma {\n  x: F32,\n}\n\nimpl Sigma {\n  /// Two.\n  pub fn get(self) -> F32 {\n    self.x\n  }\n}\n",
    );
}

#[test]
fn a_doc_comment_of_a_few_lines_that_loses_a_line_is_no_difference() {
    expect_no_doc_difference(
        "doc_lines",
        "gain_curve",
        &format!("/// One.\n/// Two.\n{DOC_ITEM}"),
        &format!("/// One.\n{DOC_ITEM}"),
    );
}

/// A doc comment on one file and none on the other is no difference for `diff --ast`, and neither is a
/// doc comment that stands before the next declaration (S-534 (a3); the check of `onsa fmt` before it
/// writes still sees them, `spec/tools.md` §3.5).
#[test]
fn a_doc_comment_that_is_added_or_moved_to_another_declaration_is_no_difference() {
    let d = Dir::new("doc_moved");
    let two = |doc_on_first: bool| {
        let (a, b) = if doc_on_first { ("/// Doc.\n", "") } else { ("", "/// Doc.\n") };
        format!("{a}fn first_one() -> I32 {{\n  1\n}}\n\n{b}fn second_one() -> I32 {{\n  2\n}}\n")
    };
    let (rc, report) = diff_of(&d, "moved", &two(true), &two(false));
    assert_eq!(rc, 0, "the doc comment belongs to the other function: {report}");
    let bare = "fn first_one() -> I32 {\n  1\n}\n\nfn second_one() -> I32 {\n  2\n}\n";
    let (rc, report) = diff_of(&d, "added", &two(true), bare);
    assert_eq!(rc, 0, "a doc comment is added: {report}");
}

/// The same doc comment with other blank lines or other white space round it is one program: a blank line
/// between a doc comment and its declaration, an ordinary comment between them (spec §2.1: "間に空行、`//`、
/// 属性があってもよい"), and the indentation do not change what the doc comment belongs to.
#[test]
fn a_doc_comment_with_other_blank_lines_round_it_is_not_a_difference() {
    let d = Dir::new("doc_same");
    let tight = "/// Doc.\nfn gain_curve() -> I32 {\n  1\n}\n";
    let (rc, report) = diff_of(&d, "blank", tight, "/// Doc.\n\nfn gain_curve() -> I32 {\n  1\n}\n");
    assert_eq!(rc, 0, "a blank line between the doc comment and the declaration: {report}");
    let (rc, report) = diff_of(&d, "indent", tight, "   /// Doc.\nfn   gain_curve( )->I32{\n1\n}\n");
    assert_eq!(rc, 0, "the indentation and the white space: {report}");
}
