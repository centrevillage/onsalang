//! What `onsa fmt` writes for the spelling of a number, the `=` of `let` and `var` and the spaces round a
//! range symbol, and how `onsa diff --ast` compares the numbers (W3-11/t, unit U1; `spec/tools.md`
//! §3.2, §3.5, spec §2.4, §18.2; plan S-334, S-62, S-126, S-07, S-970).
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
//! - the `=` of `let` and `var`: one space on each side and no column, whatever the left sides next to
//!   it (S-970); the comments at the ends of consecutive lines stay in one column.
//!
//! §3.5: `onsa diff --ast` compares the numbers by value, not by spelling.
//!
//! The readings of plan S-503 (an integer literal and a float literal are two kinds, and a float is
//! compared by its exact decimal value, not rounded) and S-504 (the canonical spelling is made from the
//! digits, and a `_` stays only between two digits that stay) are pinned too.
//!
//! What is not here: the places of the comments, the line breaks of the writer and the indentation
//! (U3, U4).
//!
//! The texts of `fmt` are made by the function `onsa fmt` calls (`test_support::fmt`, no file written), the
//! rest by the binary (`onsa fmt`, `onsa diff --ast`). Expected texts are written from the spec; none is
//! taken from the output of the compiler.

use crate::test_support;

use crate::test_support::{Dir, code, onsa};

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

/// `onsa fmt` on every input gives the expected text, which is a fixed point (`test_support::fmt`).
fn expect_fmt(tag: &str, cases: &[Case]) {
    let cases: Vec<_> =
        cases.iter().map(|(what, input, expected)| (*what, input.as_str(), expected.as_str())).collect();
    test_support::fmt::expect_fmt(tag, &cases);
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
        &format!("  par~ i in {head} {{"),
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

// ---- the `=` of `let` and `var`: one space, no column ------------------------------------------

/// A function `fn f() {` whose body is `lines`.
fn in_fn(lines: &[&str]) -> String {
    let mut all = vec!["fn f() {"];
    all.extend(lines);
    all.push("}");
    src(&all)
}

#[test]
fn the_equals_of_consecutive_lets_and_vars_has_one_space_and_no_column() {
    // spec/tools.md §3.2 (S-970): one space on each side of the `=` of a `let` and a `var`, whatever
    // the lengths of the left sides next to it and whatever the author wrote before it.
    let three = in_fn(&["  let a = 1", "  let bcd = 2", "  let ef = 3"]);
    let typed = in_fn(&["  let a: F32 = 1.0", "  let bcd = 2.0", "  var e: U8 = 3", "  let (x, y) = p"]);
    let between = in_fn(&["  let a = 1", "  // note", "  let bcd = 2", "", "  let ef = 3", "  g(a)", "  var hij = 4"]);
    expect_fmt(
        "equals",
        &[
            ("three lets", three.clone(), three.clone()),
            ("a column written by the author", in_fn(&["  let a   = 1", "  let bcd = 2", "  let ef  = 3"]), three),
            (
                "typed, var, tuple, with extra spaces and tabs",
                in_fn(&["  let a: F32    = 1.0", "  let bcd\t= 2.0", "  var e: U8      = 3", "  let (x,y)  = p"]),
                typed,
            ),
            (
                "a comment line, a blank line and another statement",
                in_fn(&[
                    "  let a      = 1",
                    "  // note",
                    "  let bcd    = 2",
                    "",
                    "  let ef  = 3",
                    "  g(a)",
                    "  var hij  = 4",
                ]),
                between,
            ),
            (
                "comparisons on the right",
                in_fn(&["  let same        = a == b", "  let longer_name = a >= b", "  let c = a <= b"]),
                in_fn(&["  let same = a == b", "  let longer_name = a >= b", "  let c = a <= b"]),
            ),
        ],
    );
}

#[test]
fn the_equals_has_one_space_next_to_an_attribute_and_in_every_block() {
    let attribute = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  let g = x * 0.5",
        "  @mem(bulk) let d = delay~(g, 4800)",
        "  let hh_long = d",
        "  hh_long",
        "}",
    ]);
    let attribute_in = src(&[
        "pub flow f(x: F32 at sample) -> F32 at sample {",
        "  let g         = x * 0.5",
        "  @mem(bulk) let d  = delay~(g, 4800)",
        "  let hh_long   = d",
        "  hh_long",
        "}",
    ]);
    let blocks = src(&[
        "fn g() { let a = 1 }",
        "fn h(c: Bool) {",
        "  let a = 1",
        "  if c { let bbbbbb = 2 }",
        "  if c {",
        "    let inner_long = 3",
        "    let i = 4",
        "  }",
        "}",
        "test \"t\" {",
        "  let x = 1",
        "  let long_n = 2",
        "  assert x < long_n",
        "}",
    ]);
    let blocks_in = src(&[
        "fn g() {  let a=1 }",
        "fn h(c: Bool) {",
        "  let a = 1",
        "  if c { let bbbbbb    = 2 }",
        "  if c {",
        "    let inner_long = 3",
        "    let i          = 4",
        "  }",
        "}",
        "test \"t\" {",
        "  let x      = 1",
        "  let long_n = 2",
        "  assert x < long_n",
        "}",
    ]);
    expect_fmt("blocks", &[("next to an attribute", attribute_in, attribute), ("blocks", blocks_in, blocks)]);
}

#[test]
fn the_comments_at_the_ends_of_the_lines_stay_in_one_column_after_the_equals() {
    // spec/tools.md §3.2: the comments of consecutive lines are in one column, one space after the
    // longest code; the `=` is not in a column, so the column is read from the lines with one space.
    let expected = in_fn(&[
        "  let a = 1       // one",
        "  let bcdefg = 2  // two",
        "  var h: U8 = 3   // three",
        "  g(a, bcdefg, h) // four",
    ]);
    let input = in_fn(&[
        "  let a      = 1 // one",
        "  let bcdefg = 2      // two",
        "  var h: U8  = 3 // three",
        "  g(a, bcdefg, h) // four",
    ]);
    expect_fmt(
        "comments",
        &[("lets with comments", input, expected.clone()), ("the canonical form", expected.clone(), expected)],
    );
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
    let expected = src(&[
        "fn f(n: U32) -> U32 {",
        "  let lo = 0x10",
        "  let hi: U32 = 1e3",
        "  var total = 0",
        "  for i in lo + 1 ..< hi - 1 {",
        "    total = total + i",
        "  }",
        "  let mask = 0xDEAD_BEEF",
        "  let m = 1_0",
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
    let d = Dir::bare(tag);
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
    let d = Dir::bare(tag);
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
    let d = Dir::bare("places");
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
    let d = Dir::bare("floatplaces");
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
    let d = Dir::bare("patterns");
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
    let d = Dir::bare("real");
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
    let d = Dir::bare("roundtrip");
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
