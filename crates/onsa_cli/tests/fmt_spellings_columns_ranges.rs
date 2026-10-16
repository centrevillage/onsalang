//! What `onsa fmt` writes for the spelling of a number, the column of `=` and the spaces round a range
//! symbol, and how `onsa diff --ast` compares the numbers (W3-11/t, unit U1; `spec/tools.md`
//! §3.2, §3.5, spec §2.4, §18.2; plan S-334, S-62, S-126, S-07, S-89, S-122).
//!
//! The case files in `tests/spec/fmt/` pin that the canonical files are a fixed point of `fmt` and
//! that the programs mean what they say. These tests pin what `fmt` writes: which spelling, which
//! column, which spaces, by the whole text of the output, and that a second `fmt` and `fmt --check`
//! leave it alone (§18.2: a canonical file is not changed by another `fmt`).
//!
//! The rules, from `spec/tools.md` §3.2:
//! - the spaces: one space on each side of `..<` and `..=`, and the ends keep the spaces of their own
//!   operators (`lo + 1 ..< hi - 1`);
//! - the numbers: the prefix (`0x` `0b`) and the exponent (`e`) in small letters, no `+` in an
//!   exponent, the digits of a hexadecimal in capitals, a `_` between two digits and one at a time, no
//!   extra zeros in front of the integer part of a float; nothing else changes (the zeros in front of
//!   an exponent, at the end of a fraction and in front of a hexadecimal stay);
//! - the column: the `=` of consecutive one-line `let` and `var` lines (a `let` with a type and a `let`
//!   that takes a tuple apart too) are in one column; a blank line, a statement of more than one
//!   line, a `let` with an attribute and any other statement cut it, a line with only a comment does not.
//!
//! §3.5: `onsa diff --ast` compares the numbers by value, not by spelling.
//!
//! The readings of plan S-503 (an integer literal and a float literal are two kinds, and a float is
//! compared by its exact decimal value, not rounded) and S-504 (the canonical spelling is made from the
//! digits, and a `_` stays only between two digits that stay) are pinned too.
//!
//! What is not here: the places of the comments, the line breaks of the writer and the indentation
//! (U3, U4), and the alignment of the comments at the end of a line.
//!
//! Every test uses only the binary (`onsa fmt`, `onsa diff --ast`). Expected texts are written from the
//! spec; none is taken from the output of the compiler.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // The counter makes the directory the test's own even when two tests use the same tag.
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_u1_{}_{n}_{tag}", std::process::id()));
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

/// The lines joined, with one line break at the end of the file.
fn src(lines: &[&str]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

/// `(what, input, expected output)`: the whole text of a file before and after `onsa fmt`.
type Case = (&'static str, String, String);

/// Runs `onsa fmt` on every input (one command, so the files are written one after the other), compares
/// the whole text of each output, and checks that the output is a fixed point: `fmt --check` ends with 0
/// and another `fmt` does not change the file.
fn expect_fmt(tag: &str, cases: &[Case]) {
    assert!(!cases.is_empty(), "no case to run");
    let d = Dir::new(tag);
    let paths: Vec<String> =
        cases.iter().enumerate().map(|(i, (_, input, _))| d.file(&format!("c{i}.onsa"), input)).collect();
    let mut args = vec!["fmt"];
    args.extend(paths.iter().map(String::as_str));
    let out = onsa(&args);
    assert_eq!(code(&out), 0, "onsa fmt: {out:?}");
    let mut wrong = Vec::new();
    for ((what, input, expected), path) in cases.iter().zip(&paths) {
        let got = read(path);
        if &got != expected {
            wrong.push(format!("{what}\n--- input\n{input}--- expected\n{expected}--- got\n{got}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {} files are not as expected:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    for ((what, _, expected), path) in cases.iter().zip(&paths) {
        let mut args = vec!["fmt", "--check"];
        args.push(path);
        let out = onsa(&args);
        assert_eq!(code(&out), 0, "{what}: the output is not a fixed point of fmt --check: {out:?}");
        let out = onsa(&["fmt", path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(&read(path), expected, "{what}: a second fmt changes the output");
    }
}

// ---- the spelling of a number ---------------------------------------------------------------------

/// A literal as the tail expression of a function.
fn lit_case(what: &'static str, input: &str, expected: &str) -> Case {
    (
        what,
        src(&["fn f() -> I32 {", &format!("  {input}"), "}"]),
        src(&["fn f() -> I32 {", &format!("  {expected}"), "}"]),
    )
}

fn lits(what: &'static str, table: &[(&str, &str)]) -> Vec<Case> {
    table.iter().map(|(i, e)| lit_case(what, i, e)).collect()
}

#[test]
fn the_prefix_and_the_exponent_are_written_in_small_letters() {
    let table = [
        ("0XFF", "0xFF"),
        ("0B1010", "0b1010"),
        ("0Xff", "0xFF"),
        ("1E3", "1e3"),
        ("2.5E-3", "2.5e-3"),
        ("1.5E3", "1.5e3"),
        ("0b1010", "0b1010"),
        ("1e3", "1e3"),
        ("2.5e-3", "2.5e-3"),
    ];
    expect_fmt("small", &lits("small letters", &table));
}

#[test]
fn the_plus_of_an_exponent_goes() {
    let table = [
        ("1e+3", "1e3"),
        ("1E+3", "1e3"),
        ("2.5e+0", "2.5e0"),
        ("2.5E+2", "2.5e2"),
        ("1e+0", "1e0"),
        ("1e-3", "1e-3"),
        ("1E-3", "1e-3"),
    ];
    expect_fmt("plus", &lits("the plus of an exponent", &table));
}

#[test]
fn the_digits_of_a_hexadecimal_are_written_in_capitals() {
    let table = [
        ("0xff", "0xFF"),
        ("0xDeadBeef", "0xDEADBEEF"),
        ("0xabcdef", "0xABCDEF"),
        ("0xFf", "0xFF"),
        ("0XaBc", "0xABC"),
        ("0xDEAD_beef", "0xDEAD_BEEF"),
        ("0xFF", "0xFF"),
        ("0b1010", "0b1010"),
    ];
    expect_fmt("hexdigits", &lits("hexadecimal digits", &table));
}

#[test]
fn the_e_of_a_hexadecimal_is_a_digit_and_not_an_exponent() {
    // §2.4: only a decimal float has an exponent, so the `e` of `0x1e3` is a digit (483), the `+` of
    // `0x1e+3` is the operator of a sum (`0x1e` and 3), and the `E` of `0x1E3` is not an exponent either.
    let table = [("0x1e3", "0x1E3"), ("0xe", "0xE"), ("0x1E3", "0x1E3"), ("0x1e+3", "0x1E + 3"), ("0xe+1", "0xE + 1")];
    expect_fmt("hexe", &lits("the e of a hexadecimal", &table));
}

#[test]
fn an_underscore_stands_between_two_digits_and_only_one_at_a_time() {
    let table = [
        ("1__000", "1_000"),
        ("1_", "1"),
        ("0x_1F", "0x1F"),
        ("1_000_", "1_000"),
        ("0b_101", "0b101"),
        ("0x__1__F__", "0x1_F"),
        ("0x1__F", "0x1_F"),
        ("0_", "0"),
        ("0xFF_", "0xFF"),
        ("0xDEAD__BEEF", "0xDEAD_BEEF"),
        ("0b_1__0_", "0b1_0"),
        ("1_000", "1_000"),
        ("1_0_0", "1_0_0"),
        ("0x1_F", "0x1_F"),
    ];
    expect_fmt("underscore", &lits("underscores of an integer", &table));
}

#[test]
fn the_underscores_of_a_float_follow_the_same_rule() {
    let table = [
        ("1__0.5", "1_0.5"),
        ("0.5_", "0.5"),
        ("1_0.5_", "1_0.5"),
        ("1.5__0", "1.5_0"),
        ("1e1__0", "1e1_0"),
        ("1_0.0_5", "1_0.0_5"),
        ("1e1_0", "1e1_0"),
    ];
    expect_fmt("floatunderscore", &lits("underscores of a float", &table));
}

#[test]
fn the_extra_zeros_in_front_of_the_integer_part_of_a_float_go() {
    let table = [
        ("01.5", "1.5"),
        ("007.25", "7.25"),
        ("00.5", "0.5"),
        ("010.0", "10.0"),
        ("00e0", "0e0"),
        ("01e2", "1e2"),
        ("000.0", "0.0"),
        ("0010.0", "10.0"),
        ("01.5E+2", "1.5e2"),
        ("0.5", "0.5"),
        ("0.0", "0.0"),
        ("0e0", "0e0"),
        ("10.0", "10.0"),
    ];
    expect_fmt("zeros", &lits("zeros of a float", &table));
}

#[test]
fn a_float_is_written_from_its_digits_and_keeps_a_underscore_only_between_two_digits_that_stay() {
    // Plan S-504: the `_` next to the point, the `e` or the sign of an exponent is between no two
    // digits and goes, and so does the `_` after a zero in front of the integer part that goes.
    let table = [
        ("1_.5", "1.5"),
        ("1_e3", "1e3"),
        ("1e_3", "1e3"),
        ("1e+_3", "1e3"),
        ("1e-_3", "1e-3"),
        ("1.5_e3", "1.5e3"),
        ("01_0.5", "1_0.5"),
        ("0_1.5", "1.5"),
        ("0_0_1_0.5", "1_0.5"),
        ("0_0.5", "0.5"),
    ];
    expect_fmt("digits", &lits("a float made from its digits", &table));
    same_values("digitsvalue", &[("1_.5", "1.5"), ("1e+_3", "1e3"), ("01_0.5", "10.5"), ("0_1.5", "1.5")]);
}

#[test]
fn a_spelling_that_is_not_in_the_rule_stays() {
    // The zeros in front of an exponent, at the end of a fraction and in front of a hexadecimal or a
    // binary number are not changed (spec/tools.md §3.2 names the extra zeros of the integer part
    // only), and a canonical spelling stays.
    let table = [
        ("1e03", "1e03"),
        ("1e-03", "1e-03"),
        ("1.0e003", "1.0e003"),
        ("1.500", "1.500"),
        ("0.50", "0.50"),
        ("1.0e0", "1.0e0"),
        ("0.0e0", "0.0e0"),
        ("0x00FF", "0x00FF"),
        ("0x0000_00FF", "0x0000_00FF"),
        ("0b0101", "0b0101"),
        ("0xDEAD_BEEF", "0xDEAD_BEEF"),
        ("1_000", "1_000"),
        ("100", "100"),
        ("0", "0"),
        ("1.0", "1.0"),
    ];
    expect_fmt("stays", &lits("an unchanged spelling", &table));
}

#[test]
fn the_zeros_that_stay_stay_when_the_rest_of_the_number_changes() {
    let table = [
        ("1e+03", "1e03"),
        ("1E+03", "1e03"),
        ("1.0e+03", "1.0e03"),
        ("1.500E+03", "1.500e03"),
        ("0x00ff", "0x00FF"),
        ("0X0F_ff", "0x0F_FF"),
        ("0B0000_0101", "0b0000_0101"),
        ("1.500E3", "1.500e3"),
    ];
    expect_fmt("mixed", &lits("a changed number with zeros that stay", &table));
}

#[test]
fn a_number_is_written_in_the_spelling_of_fmt_in_every_place() {
    let cases: Vec<Case> = vec![
        lit_case("a minus in front of a hexadecimal", "-0X80", "-0x80"),
        lit_case("a minus in front of a float", "-1E+3", "-1e3"),
        lit_case("a minus in front of underscores", "-1__0", "-1_0"),
        lit_case("a minus in front of zeros", "-01.5", "-1.5"),
        lit_case("an argument", "g(0XFF, 1E3)", "g(0xFF, 1e3)"),
        lit_case("a sum and a product", "a+0XFF*1E3", "a + 0xFF * 1e3"),
        lit_case("a struct literal", "P { x: 1E3, y: 0Xff }", "P { x: 1e3, y: 0xFF }"),
        lit_case("an array literal", "[1e+3, 25E-1, 01.5]", "[1e3, 25e-1, 1.5]"),
        lit_case("a repeated element and its length", "[0XFF; 0B100]", "[0xFF; 0b100]"),
        lit_case("a tuple", "(0B101, 7E0)", "(0b101, 7e0)"),
        lit_case("an argument with a _ at the end", "g(1_)", "g(1)"),
        (
            "a constant",
            src(&["const A: U32 = 0XFF", "const B: F32 = 1E+3"]),
            src(&["const A: U32 = 0xFF", "const B: F32 = 1e3"]),
        ),
        (
            "the length of an array in a type",
            src(&["fn f(xs: [F32; 0X10]) -> [U32; 1__0] {", "  g(xs)", "}"]),
            src(&["fn f(xs: [F32; 0x10]) -> [U32; 1_0] {", "  g(xs)", "}"]),
        ),
        (
            "the literals of a match",
            src(&[
                "fn f(v: I32) -> I32 {",
                "  match v {",
                "    0X1f => 1,",
                "    -0X_10 => 2,",
                "    1__000 => 3,",
                "    0xa | 0Xb => 4,",
                "    _ => 0,",
                "  }",
                "}",
            ]),
            src(&[
                "fn f(v: I32) -> I32 {",
                "  match v {",
                "    0x1F => 1,",
                "    -0x10 => 2,",
                "    1_000 => 3,",
                "    0xA | 0xB => 4,",
                "    _ => 0,",
                "  }",
                "}",
            ]),
        ),
        (
            "a literal inside an enumerator",
            src(&[
                "fn f(o: Option[U32]) -> U32 {",
                "  match o {",
                "    Some(0xff) => 1,",
                "    None => 0,",
                "  }",
                "}",
            ]),
            src(&[
                "fn f(o: Option[U32]) -> U32 {",
                "  match o {",
                "    Some(0xFF) => 1,",
                "    None => 0,",
                "  }",
                "}",
            ]),
        ),
        (
            "the ends of a range",
            src(&["fn f() {", "  for i in 0X1 ..< 1__3 {", "    g(i)", "  }", "}"]),
            src(&["fn f() {", "  for i in 0x1 ..< 1_3 {", "    g(i)", "  }", "}"]),
        ),
    ];
    expect_fmt("places", &cases);
}

#[test]
fn text_that_looks_like_a_number_but_is_not_one_stays() {
    // A string, a comment, a name and the index of a tuple are not numeric literals.
    let input = src(&[
        "pub fn f(t: (I32, I32)) -> I32 {",
        "  // 0XFF 1E+3 1__000 stay in a comment",
        "  let x0xff = t.0",
        "  show(\"0XFF 1E+3 1__000 {x0xff}\", x0xff + t.1)",
        "}",
    ]);
    expect_fmt("notnumbers", &[("not literals", input.clone(), input)]);
}

// ---- the spaces round a range symbol --------------------------------------------------------------

/// A `for` with the head `head` in a function whose other lines are canonical.
fn for_head(head: &str) -> String {
    src(&[
        "fn f(n: U32, lo: U32, hi: U32, xs: [U32; 3]) -> U32 {",
        "  var c: U32 = 0",
        &format!("  for i in {head} {{"),
        "    c = c + 1",
        "  }",
        "  c",
        "}",
    ])
}

fn par_head(head: &str) -> String {
    src(&[
        "pub flow f(x: F32 at sample) -> [F32; 3] at sample {",
        &format!("  par i in {head} {{"),
        "    x",
        "  }",
        "}",
    ])
}

fn heads(what: &'static str, table: &[(&str, &str)], make: fn(&str) -> String) -> Vec<Case> {
    table.iter().map(|(i, e)| (what, make(i), make(e))).collect()
}

#[test]
fn a_range_without_spaces_gets_one_space_on_each_side() {
    let table =
        [("0..<n", "0 ..< n"), ("lo..<hi", "lo ..< hi"), ("1..<4", "1 ..< 4"), ("f(lo)..<g(hi)", "f(lo) ..< g(hi)")];
    expect_fmt("tight", &heads("the half-open range", &table, for_head));
}

#[test]
fn a_range_with_the_spaces_in_another_way_gets_one_space_on_each_side() {
    // A space on one side only, two spaces, a tab (§2.5: the spaces are U+0020 and the tab).
    let table = [
        ("0 ..<n", "0 ..< n"),
        ("0..< n", "0 ..< n"),
        ("0  ..<  n", "0 ..< n"),
        ("0 ..<  n", "0 ..< n"),
        ("0   ..<n", "0 ..< n"),
        ("0\t..<\tn", "0 ..< n"),
        ("0 \t..< \tn", "0 ..< n"),
    ];
    expect_fmt("loose", &heads("the half-open range", &table, for_head));
}

#[test]
fn a_range_with_one_space_on_each_side_is_not_changed() {
    let table = [("0 ..< n", "0 ..< n"), ("lo + 1 ..< hi - 1", "lo + 1 ..< hi - 1"), ("-4 ..< 4", "-4 ..< 4")];
    expect_fmt("canonical", &heads("a canonical head", &table, for_head));
}

#[test]
fn the_ends_of_a_range_keep_the_spaces_of_their_operators() {
    let table = [
        ("lo+1..<hi-1", "lo + 1 ..< hi - 1"),
        ("lo + 1..<hi - 1", "lo + 1 ..< hi - 1"),
        ("0..<n+1", "0 ..< n + 1"),
        ("0 ..<n+1", "0 ..< n + 1"),
        ("n*2..<n*2+3", "n * 2 ..< n * 2 + 3"),
        ("0..<n/2", "0 ..< n / 2"),
        ("n%2..<n", "n % 2 ..< n"),
        ("lo+1  ..<  hi-1", "lo + 1 ..< hi - 1"),
    ];
    expect_fmt("operators", &heads("the ends with operators", &table, for_head));
}

#[test]
fn the_ends_that_are_not_names_keep_their_own_form() {
    let table = [
        ("-4..<4", "-4 ..< 4"),
        ("xs[0]..<xs[1]", "xs[0] ..< xs[1]"),
        ("0..<xs[2]", "0 ..< xs[2]"),
        ("1_0..<1_3", "1_0 ..< 1_3"),
    ];
    expect_fmt("ends", &heads("the ends of other forms", &table, for_head));
}

#[test]
fn the_closed_range_gets_the_same_spaces() {
    let table = [
        ("1..=n", "1 ..= n"),
        ("1 ..=n", "1 ..= n"),
        ("1..= n", "1 ..= n"),
        ("0  ..=  n", "0 ..= n"),
        ("0\t..=\tn", "0 ..= n"),
        ("lo+1..=hi-1", "lo + 1 ..= hi - 1"),
        ("-2..=2", "-2 ..= 2"),
        ("1 ..= n", "1 ..= n"),
    ];
    expect_fmt("closed", &heads("the closed range", &table, for_head));
}

#[test]
fn the_head_of_a_par_gets_the_same_spaces() {
    let table = [
        ("1..<4", "1 ..< 4"),
        ("1 ..<4", "1 ..< 4"),
        ("1  ..<  4", "1 ..< 4"),
        ("0..=3", "0 ..= 3"),
        ("0 ..=  3", "0 ..= 3"),
        ("0..<N+1", "0 ..< N + 1"),
        ("2..<N", "2 ..< N"),
        ("1 ..< 4", "1 ..< 4"),
    ];
    expect_fmt("par", &heads("the head of a par", &table, par_head));
}

#[test]
fn a_range_in_a_nested_block_gets_the_spaces_too() {
    let input = src(&[
        "fn f(c: Bool, n: U32) -> U32 {",
        "  var t: U32 = 0",
        "  if c {",
        "    for i in 0..<n {",
        "      for j in i+1..<n {",
        "        t = t + j",
        "      }",
        "    }",
        "  } else {",
        "    for k in 1..=n {",
        "      t = t + k",
        "    }",
        "  }",
        "  t",
        "}",
    ]);
    let expected = src(&[
        "fn f(c: Bool, n: U32) -> U32 {",
        "  var t: U32 = 0",
        "  if c {",
        "    for i in 0 ..< n {",
        "      for j in i + 1 ..< n {",
        "        t = t + j",
        "      }",
        "    }",
        "  } else {",
        "    for k in 1 ..= n {",
        "      t = t + k",
        "    }",
        "  }",
        "  t",
        "}",
    ]);
    expect_fmt("nested", &[("two loops in a branch", input, expected)]);
}

// ---- the column of `=` ----------------------------------------------------------------------------

/// The lines `indent` + the left side padded to the longest + ` = ` + the right side: the column of
/// `=` of spec/tools.md §3.2 (one space after the longest left side).
fn col(indent: &str, rows: &[(&str, &str)]) -> Vec<String> {
    let w = rows.iter().map(|(l, _)| l.len()).max().unwrap();
    rows.iter().map(|(l, r)| format!("{indent}{l:<w$} = {r}")).collect()
}

/// A function `fn f() {` whose body is `lines`.
fn in_fn(lines: &[String]) -> String {
    let mut all = vec!["fn f() {".to_string()];
    all.extend(lines.iter().cloned());
    all.push("}".to_string());
    all.join("\n") + "\n"
}

fn s(x: &str) -> String {
    x.to_string()
}

#[test]
fn consecutive_lets_are_put_in_one_column() {
    // The text of the expected output, written out once so that the rule can be read in it.
    let literal = src(&["fn f() {", "  let a   = 1", "  let bcd = 2", "  let ef  = 3", "}"]);
    assert_eq!(in_fn(&col("  ", &[("let a", "1"), ("let bcd", "2"), ("let ef", "3")])), literal);
    let input = src(&["fn f() {", "  let a = 1", "  let bcd = 2", "  let ef = 3", "}"]);
    // The longest left side is in the middle, at the start and at the end.
    let middle = in_fn(&col("  ", &[("let ab", "1"), ("let abcdef", "2"), ("let abc", "3")]));
    let first = in_fn(&col("  ", &[("let abcdef", "1"), ("let ab", "2"), ("let abc", "3")]));
    let last = in_fn(&col("  ", &[("let ab", "1"), ("let abc", "2"), ("let abcdef", "3")]));
    expect_fmt(
        "column",
        &[
            ("three lets", input, literal),
            (
                "the longest in the middle",
                src(&["fn f() {", "  let ab = 1", "  let abcdef = 2", "  let abc = 3", "}"]),
                middle,
            ),
            ("the longest first", src(&["fn f() {", "  let abcdef = 1", "  let ab = 2", "  let abc = 3", "}"]), first),
            ("the longest last", src(&["fn f() {", "  let ab = 1", "  let abc = 2", "  let abcdef = 3", "}"]), last),
        ],
    );
}

#[test]
fn vars_are_in_the_column_and_the_extra_spaces_go() {
    let aligned = in_fn(&col("  ", &[("var a", "1"), ("var bcd", "2")]));
    let mixed = in_fn(&col("  ", &[("var a", "1"), ("let bcd", "2"), ("var ef", "3")]));
    let tabs = in_fn(&col("  ", &[("let a", "1"), ("let bcd", "2")]));
    expect_fmt(
        "vars",
        &[
            ("two vars", src(&["fn f() {", "  var a = 1", "  var bcd = 2", "}"]), aligned.clone()),
            ("a var between lets", src(&["fn f() {", "  var a = 1", "  let bcd = 2", "  var ef = 3", "}"]), mixed),
            (
                "extra spaces in front of the =",
                src(&["fn f() {", "  var a        = 1", "  var bcd      = 2", "}"]),
                aligned,
            ),
            ("a tab in front of the =", src(&["fn f() {", "  let a\t= 1", "  let bcd\t\t= 2", "}"]), tabs),
        ],
    );
}

#[test]
fn a_let_with_a_type_and_a_let_that_takes_a_tuple_apart_are_in_the_column() {
    let typed =
        in_fn(&col("  ", &[("let a: F32", "1.0"), ("let bcd", "2.0"), ("var e: U8", "3"), ("let (x, y)", "p")]));
    // The width is that of the text fmt writes (`let (x, y)`), not of the text that was written.
    let tuple = in_fn(&col("  ", &[("let (x, y)", "p"), ("let cc", "q")]));
    let types_only = in_fn(&col("  ", &[("let a: F32", "1.0"), ("let b: U8", "2")]));
    let nested_tuple = in_fn(&col("  ", &[("let ((a, b), c)", "p"), ("let d", "q")]));
    expect_fmt(
        "typed",
        &[
            (
                "typed, var, tuple",
                src(&["fn f() {", "  let a: F32 = 1.0", "  let bcd = 2.0", "  var e: U8 = 3", "  let (x, y) = p", "}"]),
                typed,
            ),
            ("a tuple written close", src(&["fn f() {", "  let (x,y) = p", "  let cc = q", "}"]), tuple),
            ("only lets with a type", src(&["fn f() {", "  let a: F32 = 1.0", "  let b: U8 = 2", "}"]), types_only),
            ("a tuple in a tuple", src(&["fn f() {", "  let ((a, b), c) = p", "  let d = q", "}"]), nested_tuple),
        ],
    );
}

#[test]
fn a_line_with_only_a_comment_does_not_cut_the_column() {
    let one = {
        let c = col("  ", &[("let a", "1"), ("let bcd", "2"), ("let ef", "3")]);
        in_fn(&[c[0].clone(), s("  // note"), c[1].clone(), s("  // two"), s("  // lines"), c[2].clone()])
    };
    expect_fmt(
        "comment",
        &[(
            "comment lines between lets",
            src(&[
                "fn f() {",
                "  let a = 1",
                "  // note",
                "  let bcd = 2",
                "  // two",
                "  // lines",
                "  let ef = 3",
                "}",
            ]),
            one,
        )],
    );
}

#[test]
fn a_blank_line_cuts_the_column() {
    let g1 = col("  ", &[("let a", "1"), ("let bcd", "2")]);
    let g2 = col("  ", &[("let ef", "3"), ("let g", "4")]);
    let expected = in_fn(&[g1[0].clone(), g1[1].clone(), s(""), g2[0].clone(), g2[1].clone()]);
    expect_fmt(
        "blank",
        &[(
            "two groups",
            src(&["fn f() {", "  let a = 1", "  let bcd = 2", "", "  let ef = 3", "  let g = 4", "}"]),
            expected,
        )],
    );
}

#[test]
fn a_statement_of_more_than_one_line_cuts_the_column() {
    let g1 = col("  ", &[("let a", "1"), ("let bcd", "2")]);
    let g2 = col("  ", &[("let ef", "3"), ("let g", "4")]);
    let expected = in_fn(&[
        g1[0].clone(),
        g1[1].clone(),
        s("  let c = if flag {"),
        s("    1"),
        s("  } else {"),
        s("    2"),
        s("  }"),
        g2[0].clone(),
        g2[1].clone(),
    ]);
    let input = src(&[
        "fn f() {",
        "  let a = 1",
        "  let bcd = 2",
        "  let c = if flag {",
        "    1",
        "  } else {",
        "    2",
        "  }",
        "  let ef = 3",
        "  let g = 4",
        "}",
    ]);
    expect_fmt("multiline", &[("a let with a block between the groups", input, expected)]);
}

#[test]
fn any_other_statement_cuts_the_column() {
    let g1 = col("  ", &[("var t", "0"), ("let bcd", "2")]);
    let g2 = col("  ", &[("let e", "3"), ("let fgh", "4")]);
    let assigned = in_fn(&[g1[0].clone(), g1[1].clone(), s("  t = t + bcd"), g2[0].clone(), g2[1].clone()]);
    let called = in_fn(&[g1[0].clone(), g1[1].clone(), s("  g(t)"), g2[0].clone(), g2[1].clone()]);
    expect_fmt(
        "other",
        &[
            (
                "an assignment",
                src(&[
                    "fn f() {",
                    "  var t = 0",
                    "  let bcd = 2",
                    "  t = t + bcd",
                    "  let e = 3",
                    "  let fgh = 4",
                    "}",
                ]),
                assigned,
            ),
            (
                "a call",
                src(&["fn f() {", "  var t = 0", "  let bcd = 2", "  g(t)", "  let e = 3", "  let fgh = 4", "}"]),
                called,
            ),
        ],
    );
}

#[test]
fn a_let_with_an_attribute_cuts_the_column_and_is_not_in_it() {
    let g1 = col("  ", &[("let g", "x * 0.5"), ("let gain_total", "g")]);
    let g2 = col("  ", &[("let h", "d"), ("let hh_long", "h")]);
    let expected = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        &g1[0],
        &g1[1],
        "  @mem(bulk) let d = delay~(g, 4800)",
        &g2[0],
        &g2[1],
        "  h",
        "}",
    ]);
    let input = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  let g = x * 0.5",
        "  let gain_total = g",
        "  @mem(bulk) let d = delay~(g, 4800)",
        "  let h = d",
        "  let hh_long = h",
        "  h",
        "}",
    ]);
    // A long name after the attribute and a plain let in front of it do not share a column.
    let a = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  @mem(bulk) let line_long_name = delay~(x, 4800)",
        "  let a   = line_long_name",
        "  let abc = a + x",
        "  abc",
        "}",
    ]);
    let a_in = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  @mem(bulk) let line_long_name = delay~(x, 4800)",
        "  let a = line_long_name",
        "  let abc = a + x",
        "  abc",
        "}",
    ]);
    let b = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  let p  = x",
        "  let pq = p",
        "  @mem(bulk) let tail = delay~(pq, 64)",
        "  tail",
        "}",
    ]);
    let b_in = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  let p = x",
        "  let pq = p",
        "  @mem(bulk) let tail = delay~(pq, 64)",
        "  tail",
        "}",
    ]);
    expect_fmt(
        "attribute",
        &[
            ("plain lets on both sides", input, expected),
            ("the attributed let first", a_in, a),
            ("the attributed let last", b_in, b),
        ],
    );
}

#[test]
fn a_let_in_a_one_line_block_is_in_no_column() {
    // Plan S-509: the column of `=` is of the one-line `let` and `var` lines that hold the statement
    // alone; a `let` in a one-line block is on the line of its head, so it is in no column, even on
    // consecutive lines.
    let expected = src(&[
        "fn g() { let a = 1 }",
        "fn h() { let bbbb = 2 }",
        "",
        "fn f(x: I32) {",
        "  match x {",
        "    0 => { let a = 1 },",
        "    _ => { let bbbb = 2 },",
        "  }",
        "}",
        "",
        "fn k(c: Bool) {",
        "  let a = 1",
        "  if c { let bbbbbb = 2 }",
        "  let cc = 3",
        "}",
    ]);
    let input = src(&[
        "fn g() {  let a=1 }",
        "fn h() { let bbbb =  2 }",
        "",
        "fn f(x: I32) {",
        "  match x {",
        "    0 => { let a  = 1 },",
        "    _ => { let bbbb = 2 },",
        "  }",
        "}",
        "",
        "fn k(c: Bool) {",
        "  let a = 1",
        "  if c { let bbbbbb    = 2 }",
        "  let cc = 3",
        "}",
    ]);
    expect_fmt(
        "oneline",
        &[("lets in one-line blocks", input, expected.clone()), ("the canonical form", expected.clone(), expected)],
    );
}

#[test]
fn a_nested_block_has_a_column_of_its_own() {
    let outer = col("  ", &[("let a", "1"), ("let bcd", "2")]);
    let inner = col("    ", &[("let inner_long", "3"), ("let i", "4")]);
    let after = col("  ", &[("let ef", "5"), ("let g", "6")]);
    let expected = src(&[
        "fn f(c: Bool) {",
        &outer[0],
        &outer[1],
        "  if c {",
        &inner[0],
        &inner[1],
        "  }",
        &after[0],
        &after[1],
        "}",
    ]);
    let input = src(&[
        "fn f(c: Bool) {",
        "  let a = 1",
        "  let bcd = 2",
        "  if c {",
        "    let inner_long = 3",
        "    let i = 4",
        "  }",
        "  let ef = 5",
        "  let g = 6",
        "}",
    ]);
    // A column in the body of a test block and of an anonymous function.
    let in_test = src(&["test \"t\" {", "  let x      = 1", "  let long_n = 2", "  assert x < long_n", "}"]);
    let in_test_in = src(&["test \"t\" {", "  let x = 1", "  let long_n = 2", "  assert x < long_n", "}"]);
    let closure = src(&[
        "fn f() -> [U32; 3] {",
        "  array.from_fn(fn(i: U32) -> U32 {",
        "    let twice    = i * 2",
        "    let plus_one = twice + 1",
        "    plus_one",
        "  })",
        "}",
    ]);
    let closure_in = src(&[
        "fn f() -> [U32; 3] {",
        "  array.from_fn(fn(i: U32) -> U32 {",
        "    let twice = i * 2",
        "    let plus_one = twice + 1",
        "    plus_one",
        "  })",
        "}",
    ]);
    expect_fmt(
        "nested",
        &[
            ("a branch", input, expected),
            ("a test block", in_test_in, in_test),
            ("an anonymous function", closure_in, closure),
        ],
    );
}

#[test]
fn a_let_alone_has_one_space_and_so_does_a_column_that_is_already_right() {
    let alone = in_fn(&[s("  let only_one = 1"), s("  g(only_one)"), s("  let a = 2"), s("  g(a)")]);
    let alone_in = in_fn(&[s("  let only_one    = 1"), s("  g(only_one)"), s("  let a     = 2"), s("  g(a)")]);
    let right = in_fn(&col("  ", &[("let a", "1"), ("let bcd", "2")]));
    expect_fmt(
        "alone",
        &[("lets with a statement between", alone_in, alone), ("a column that is right", right.clone(), right)],
    );
}

#[test]
fn the_equals_of_the_let_is_the_one_in_the_column_and_not_one_in_the_right_side() {
    let expected = in_fn(&col("  ", &[("let same", "a == b"), ("let longer_name", "a >= b"), ("let c", "a <= b")]));
    let input = src(&["fn f() {", "  let same = a == b", "  let longer_name = a >= b", "  let c = a <= b", "}"]);
    expect_fmt("compare", &[("comparisons on the right", input, expected)]);
}

#[test]
fn the_items_that_are_not_lets_are_not_in_a_column() {
    // spec/tools.md §3.2 lists `let` and `var` only: the `=` of `const` items keeps one space on each side.
    let consts = src(&["const A: U32 = 1", "const LONGER_NAME: U32 = 2", "pub const B: F32 = 0.5"]);
    expect_fmt("consts", &[("const items in a row", consts.clone(), consts)]);
}

#[test]
fn the_three_rules_work_together_and_a_second_fmt_changes_nothing() {
    let input = src(&[
        "fn f(n: U32) -> U32 {",
        "  let lo = 0X10",
        "  let hi: U32 = 1E+3",
        "  var total = 0",
        "  for i in lo+1..<hi-1 {",
        "    total = total + i",
        "  }",
        "  let mask = 0xdead_BEEF",
        "  let m = 1__0",
        "  total",
        "}",
    ]);
    let a = col("  ", &[("let lo", "0x10"), ("let hi: U32", "1e3"), ("var total", "0")]);
    let b = col("  ", &[("let mask", "0xDEAD_BEEF"), ("let m", "1_0")]);
    let expected = src(&[
        "fn f(n: U32) -> U32 {",
        &a[0],
        &a[1],
        &a[2],
        "  for i in lo + 1 ..< hi - 1 {",
        "    total = total + i",
        "  }",
        &b[0],
        &b[1],
        "  total",
        "}",
    ]);
    expect_fmt("together", &[("all three", input, expected)]);
}

// ---- diff --ast compares the numbers by value (spec/tools.md §3.5) ---------------------------

fn tail(expr: &str) -> String {
    src(&["fn f() -> F32 {", &format!("  {expr}"), "}"])
}

fn diff_code(d: &Dir, one: &str, other: &str) -> i32 {
    let a = d.file("old.onsa", one);
    let b = d.file("new.onsa", other);
    code(&onsa(&["diff", "--ast", &a, &b]))
}

/// Every pair has the same value: `diff --ast` reports nothing (exit code 0), in both orders.
fn same_values(tag: &str, pairs: &[(&str, &str)]) {
    let d = Dir::new(tag);
    let mut wrong = Vec::new();
    for (x, y) in pairs {
        for (p, q) in [(x, y), (y, x)] {
            let c = diff_code(&d, &tail(p), &tail(q));
            if c != 0 {
                wrong.push(format!("`{p}` against `{q}`: exit code {c}"));
            }
        }
    }
    assert!(wrong.is_empty(), "spellings of one value reported as a difference:\n{}", wrong.join("\n"));
}

/// Every pair has two values: `diff --ast` reports the difference (exit code 1), in both orders.
fn other_values(tag: &str, pairs: &[(&str, &str)]) {
    let d = Dir::new(tag);
    let mut wrong = Vec::new();
    for (x, y) in pairs {
        for (p, q) in [(x, y), (y, x)] {
            let c = diff_code(&d, &tail(p), &tail(q));
            if c != 1 {
                wrong.push(format!("`{p}` against `{q}`: exit code {c}"));
            }
        }
    }
    assert!(wrong.is_empty(), "different values not reported as a difference:\n{}", wrong.join("\n"));
}

#[test]
fn integers_with_the_same_value_in_other_spellings_are_not_a_difference() {
    same_values(
        "intsame",
        &[
            ("0x1f", "0x1F"),
            ("0X1F", "0x1f"),
            ("1_000", "1000"),
            ("0b101", "5"),
            ("0x_1F", "31"),
            ("1_", "1"),
            ("0xFFFF_FFFF_FFFF_FFFF", "18446744073709551615"),
            ("0b1111_1111", "0xFF"),
            ("-0x80", "-0X80"),
            ("0", "0_"),
            ("0x0", "0b0"),
            ("1__000", "1_000"),
            ("0x1F", "0x1_F"),
        ],
    );
}

#[test]
fn integers_with_other_values_are_a_difference() {
    other_values(
        "intother",
        &[
            ("0x1F", "0x1E"),
            ("1_000", "1_001"),
            ("0xFF", "0xFFF"),
            ("1", "2"),
            ("0b101", "0b100"),
            ("-0x80", "0x80"),
            ("18446744073709551615", "18446744073709551614"),
        ],
    );
}

#[test]
fn floats_with_the_same_value_in_other_spellings_are_not_a_difference() {
    same_values(
        "floatsame",
        &[
            ("1e3", "1E3"),
            ("1e3", "1e+3"),
            ("1e3", "1000.0"),
            ("1.5", "01.5"),
            ("1.5", "1.50"),
            ("10.5", "1_0.5"),
            ("0.5", "5e-1"),
            ("2.5e2", "250.0"),
            ("1e3", "1.0e3"),
            ("1e03", "1e3"),
            ("-1e3", "-1E+3"),
            ("0.0", "0e0"),
            ("1.5E3", "1500.0"),
        ],
    );
}

#[test]
fn floats_with_other_values_are_a_difference() {
    other_values(
        "floatother",
        &[
            ("1e3", "1e4"),
            ("1.5", "1.25"),
            ("1e3", "1e-3"),
            ("0.5", "0.05"),
            ("1.5", "-1.5"),
            ("1e03", "1e04"),
            ("1.5", "1.5000001"),
            ("2.5e2", "2.5e3"),
        ],
    );
}

#[test]
fn an_integer_and_a_float_are_a_difference_and_a_float_is_not_rounded() {
    // Plan S-503: an integer literal and a float literal are two kinds of literal (spec §2.4), so
    // `1000` against `1000.0` is a difference; a float is compared by its exact decimal value, so two
    // values that round to one `F64` are two values.
    other_values(
        "kinds",
        &[
            ("1000", "1000.0"),
            ("1000", "1e3"),
            ("0", "0.0"),
            // A float whose value is a whole number with no power of ten is no integer either.
            ("1", "1.0"),
            ("5", "5.0"),
            ("1", "1e0"),
            ("0.1", "0.10000000000000000001"),
            ("1.0", "1.00000000000000000001"),
            ("9007199254740993.0", "9007199254740992.0"),
        ],
    );
}

/// 2^127, one more than the largest `i128`: an exponent no machine integer of the compiler holds.
const BIG: &str = "170141183460469231731687303715884105728";

#[test]
fn a_float_with_an_exponent_of_any_length_is_compared_by_its_value() {
    // spec/tools.md §3.5: the spellings of one value are no difference, whatever the length of
    // the exponent, and two values are a difference.
    let same = [
        (format!("1e{BIG}"), format!("1E+{BIG}")),
        (format!("0.5E-{BIG}"), "5e-170141183460469231731687303715884105729".to_string()),
        (format!("10e{BIG}"), "1e170141183460469231731687303715884105729".to_string()),
    ];
    let same: Vec<(&str, &str)> = same.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    same_values("bigsame", &same);
    let other = [
        (format!("1e{BIG}"), "1e170141183460469231731687303715884105729".to_string()),
        (format!("0.5E-{BIG}"), format!("5e-{BIG}")),
        (format!("1e{BIG}"), format!("1e-{BIG}")),
    ];
    let other: Vec<(&str, &str)> = other.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    other_values("bigother", &other);
}

/// A program with `lit` in the place `template` names (`{}` is the literal).
fn places() -> Vec<(&'static str, &'static str)> {
    vec![
        ("an argument", "fn f() -> F32 {\n  g(1, {}, 2)\n}\n"),
        ("an operand", "fn f(x: F32) -> F32 {\n  x * {} + 1\n}\n"),
        ("a field of a struct", "fn f() -> P {\n  P { x: {}, y: 0 }\n}\n"),
        ("an element", "fn f() -> [F32; 2] {\n  [{}, 2]\n}\n"),
        ("a branch", "fn f(c: Bool) -> F32 {\n  if c {\n    {}\n  } else {\n    0\n  }\n}\n"),
        ("a constant", "const A: F32 = {}\n"),
        ("a let", "fn f() -> F32 {\n  let a = {}\n  a\n}\n"),
    ]
}

fn at(template: &str, lit: &str) -> String {
    template.replacen("{}", lit, 1)
}

#[test]
fn a_number_is_compared_by_value_in_every_place() {
    let d = Dir::new("places");
    let mut wrong = Vec::new();
    for (what, template) in places() {
        for (x, y) in [("0X1F", "0x1f"), ("1_0", "10"), ("0B11", "3")] {
            let c = diff_code(&d, &at(template, x), &at(template, y));
            if c != 0 {
                wrong.push(format!("{what}: `{x}` against `{y}` (the same value): exit code {c}"));
            }
        }
        for (x, y) in [("0x1F", "0x1E"), ("10", "11"), ("0b11", "0b10")] {
            let c = diff_code(&d, &at(template, x), &at(template, y));
            if c != 1 {
                wrong.push(format!("{what}: `{x}` against `{y}` (two values): exit code {c}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_float_is_compared_by_value_in_every_place() {
    let d = Dir::new("floatplaces");
    let mut wrong = Vec::new();
    for (what, template) in places() {
        for (x, y) in [("1E3", "1e3"), ("1e+3", "1000.0"), ("01.5", "1.5"), ("1_0.5", "10.50")] {
            let c = diff_code(&d, &at(template, x), &at(template, y));
            if c != 0 {
                wrong.push(format!("{what}: `{x}` against `{y}` (the same value): exit code {c}"));
            }
        }
        for (x, y) in [("1e3", "1e4"), ("1.5", "1.25"), ("0.5", "0.05")] {
            let c = diff_code(&d, &at(template, x), &at(template, y));
            if c != 1 {
                wrong.push(format!("{what}: `{x}` against `{y}` (two values): exit code {c}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn the_numbers_of_a_pattern_and_of_a_length_are_compared_by_value() {
    let d = Dir::new("patterns");
    let pat = |lit: &str| {
        src(&["fn f(v: I32) -> I32 {", "  match v {", &format!("    {lit} => 1,"), "    _ => 0,", "  }", "}"])
    };
    let len = |lit: &str| src(&[&format!("fn f(xs: [F32; {lit}]) -> F32 {{"), "  xs[0]", "}"]);
    let head = |lit: &str| for_head(&format!("0..<{lit}"));
    for (what, make) in
        [("a pattern", &pat as &dyn Fn(&str) -> String), ("a length", &len), ("the end of a range", &head)]
    {
        assert_eq!(diff_code(&d, &make("0X1F"), &make("0x1f")), 0, "{what}: the same value");
        assert_eq!(diff_code(&d, &make("1_000"), &make("1000")), 0, "{what}: the same value");
        assert_eq!(diff_code(&d, &make("0x1F"), &make("0x1E")), 1, "{what}: two values");
        assert_eq!(diff_code(&d, &make("1_000"), &make("1_001")), 1, "{what}: two values");
    }
}

#[test]
fn a_difference_other_than_a_number_is_still_reported_when_the_numbers_are_spelled_apart() {
    // The comparison by value must not hide a real difference in the same program.
    let d = Dir::new("real");
    let one = src(&["fn f() -> I32 {", "  g(0X1F, 1_0)", "}"]);
    let same = src(&["fn f() -> I32 {", "  g(0x1f, 10)", "}"]);
    let other_callee = src(&["fn f() -> I32 {", "  h(0x1f, 10)", "}"]);
    let other_count = src(&["fn f() -> I32 {", "  g(0x1f)", "}"]);
    assert_eq!(diff_code(&d, &one, &same), 0);
    assert_eq!(diff_code(&d, &one, &other_callee), 1);
    assert_eq!(diff_code(&d, &one, &other_count), 1);
}

#[test]
fn a_file_and_its_formatted_form_are_not_a_difference() {
    let d = Dir::new("roundtrip");
    let input = src(&[
        "fn f(n: U32) -> F32 {",
        "  let a = 0XFF",
        "  let b = 1E+3",
        "  for i in 0..<a {",
        "    g(1__0, 01.5, 0x1e3)",
        "  }",
        "  b",
        "}",
    ]);
    let before = d.file("before.onsa", &input);
    let after = d.file("after.onsa", &input);
    let out = onsa(&["fmt", &after]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert_ne!(read(&before), read(&after), "fmt changes the file");
    let out = onsa(&["diff", "--ast", &before, &after]);
    assert_eq!(code(&out), 0, "fmt changed the spelling and the spaces only: {out:?}");
}
