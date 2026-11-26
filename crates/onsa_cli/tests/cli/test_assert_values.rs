//! The values of the two sides of a failed `assert` (S-1261, W8-13; spec §18.1, §6.3, §3.1,
//! §4.5, `spec/tools.md` §4).
//!
//! What the spec fixes, and so what is checked here:
//! - an `assert` whose expression is, outside its outer parentheses, a comparison (§3.1: `==` `!=`
//!   `<` `<=` `>` `>=`) with operands of a type that satisfies `Show` (a type parameter by its
//!   bounds, §4.5) gives `failure.left` and `failure.right` in `--json` (§18.1): the `Show` strings
//!   of §6.3 of the two values compared (shortest decimal of the type, a `Char` in its literal form
//!   even at the top, tuples, arrays, `Option` and `Result` in the form of an expression). For any
//!   other `assert` the two keys are not there. `message` stays `assert <source>` (§18.1);
//! - the text puts the two values in lines after the line of the result, indented (`spec/tools.md`
//!   §4: only the lines that start with `test` are results). The implementation writes
//!   `left: <value>` and `right: <value>` in this order (S-1261 G6): that is the one form of the
//!   lines checked, the width of the indent is not;
//! - a long value is cut. The length and the mark are not promised, so only that the string is
//!   much shorter than the whole `Show` string, starts as it does, and is the same in the text and
//!   in the JSON is checked;
//! - the operands are evaluated once, in the order of §3.5; the values shown are the values
//!   compared. A panic in an operand is a failure of `kind` `"panic"` with no values.
//!
//! Not checked, on purpose: the characters of a `Char` that §2.5 cannot write and the other rare
//! ones (S-270 is open: the form is not fixed); a `Str` (this version has E0200 for the Shared type
//! `Str`, so no program can compare one yet); the length where a value is cut.
//!
//! The forms that give values are in the tests that name what they show; the forms that give
//! none (the same today and after the work) are in the tests whose names say "no values", so that
//! a list of waiting tests can name the first and not the second.

use crate::test_support;

use serde_json::Value;
use test_support::*;

/// One failing `test` of a package: its body (the lines are written indented by two), and what the
/// failure has to be.
struct Case {
    name: String,
    body: String,
    shows: Option<(String, String)>,
    /// The `kind` of the failure; empty is not checked.
    kind: &'static str,
    /// The message, when it is not the source of the last `assert` line of the body.
    msg: Option<String>,
    /// The text of the line (trimmed) that the text output names in `failed at`, when it is not
    /// the last `assert` line of the body.
    at: Option<String>,
}

impl Case {
    fn new(name: &str, body: &str) -> Case {
        Case { name: name.to_string(), body: body.to_string(), shows: None, kind: "assert", msg: None, at: None }
    }
    fn shows(mut self, left: &str, right: &str) -> Case {
        self.shows = Some((left.to_string(), right.to_string()));
        self
    }
    fn kind(mut self, kind: &'static str) -> Case {
        self.kind = kind;
        self
    }
    fn msg(mut self, msg: &str) -> Case {
        self.msg = Some(msg.to_string());
        self
    }
    fn at(mut self, line: &str) -> Case {
        self.at = Some(line.to_string());
        self
    }
}

/// A case that shows `left` and `right`.
fn show(name: &str, body: &str, left: &str, right: &str) -> Case {
    Case::new(name, body).shows(left, right)
}

/// A case that shows no values.
fn plain(name: &str, body: &str) -> Case {
    Case::new(name, body)
}

/// The index of the last `assert` line of a body (a body of one call, whose `assert` is in the
/// prelude, has none: its last line).
fn last_assert(body: &[&str]) -> usize {
    body.iter().rposition(|l| l.starts_with("assert ")).unwrap_or(body.len() - 1)
}

/// The source of the package (`prelude` and one `test` for each case) and the line (from 1) of the
/// last `assert` line of each body.
fn build(prelude: &str, cases: &[Case]) -> (String, Vec<usize>) {
    let mut src = prelude.to_string();
    let mut lines = vec![];
    for c in cases {
        src.push_str(&format!("\ntest \"{}\" {{\n", c.name));
        let first = src.matches('\n').count() + 1;
        let body: Vec<&str> = c.body.lines().collect();
        let last = last_assert(&body);
        lines.push(first + last);
        for l in &body {
            src.push_str(&format!("  {l}\n"));
        }
        src.push_str("}\n");
    }
    (src, lines)
}

/// The message the failure has: the source of the expression of the last `assert` line, to the
/// end of the body, the lines after the first kept as written (§18.1).
fn message_of(c: &Case) -> String {
    if let Some(m) = &c.msg {
        return m.clone();
    }
    let body: Vec<&str> = c.body.lines().collect();
    let last = last_assert(&body);
    let mut out = body[last].to_string();
    for l in &body[last + 1..] {
        out.push_str(&format!("\n  {l}"));
    }
    out
}

fn is_summary(l: &str) -> bool {
    l.chars().next().is_some_and(|c| c.is_ascii_digit()) && l.contains(" passed, ")
}

/// The lines of the text output after the result line of `name`, up to the next result line or
/// the summary, with the result line itself first.
fn block_of(text: &Out, name: &str) -> (String, Vec<String>) {
    let head = format!("test m \"{name}\" failed at ");
    let lines: Vec<&str> = text.stdout.lines().collect();
    let i = lines
        .iter()
        .position(|l| l.starts_with(&head))
        .unwrap_or_else(|| panic!("no failed line of {name}: {}", text.stdout));
    let rest: Vec<String> = lines[i + 1..]
        .iter()
        .take_while(|l| !l.starts_with("test ") && !is_summary(l))
        .map(|l| l.to_string())
        .collect();
    (lines[i].to_string(), rest)
}

fn check_json(c: &Case, doc: &Value, src: &str) {
    let f = failure_of(record(doc, "m", &c.name));
    if !c.kind.is_empty() {
        assert_eq!(str_of(f, "kind"), c.kind, "{}: {f}\n{src}", c.name);
    }
    if c.kind != "panic" {
        assert_eq!(str_of(f, "message"), message_of(c), "{}: {f}", c.name);
    }
    match &c.shows {
        Some((l, r)) => {
            assert_eq!(f.get("left").and_then(Value::as_str), Some(l.as_str()), "{}: left of {f}", c.name);
            assert_eq!(f.get("right").and_then(Value::as_str), Some(r.as_str()), "{}: right of {f}", c.name);
        }
        None => {
            assert!(f.get("left").is_none(), "{}: no `left` in {f}", c.name);
            assert!(f.get("right").is_none(), "{}: no `right` in {f}", c.name);
        }
    }
}

fn check_text(c: &Case, line_no: usize, text: &Out) {
    let (head, rest) = block_of(text, &c.name);
    let want_head = format!("test m \"{}\" failed at m.onsa:{line_no}: ", c.name);
    for l in &rest {
        assert!(l.starts_with(char::is_whitespace), "{}: a line after the result is indented: {l:?}", c.name);
    }
    let got: Vec<&str> = rest.iter().map(|l| l.trim_start()).collect();
    if c.kind == "panic" {
        // The wording of a panic is not fixed; what is fixed here is the position and no values.
        assert!(head.starts_with(&want_head), "{}: {head}", c.name);
        assert!(got.iter().all(|l| !l.starts_with("left:") && !l.starts_with("right:")), "{}: {got:?}", c.name);
        return;
    }
    let msg = message_of(c);
    let mut lines = msg.lines();
    assert_eq!(head, format!("{want_head}{}", lines.next().unwrap()), "{}", c.name);
    let mut want: Vec<String> = lines.map(|l| l.trim_start().to_string()).collect();
    if let Some((l, r)) = &c.shows {
        want.push(format!("left: {l}"));
        want.push(format!("right: {r}"));
    }
    assert_eq!(got, want, "{}: the lines after the result line", c.name);
}

/// Run the package of `prelude` and the cases once with `--json` and once as text, and check each
/// case against both (the exit code is 1: every test fails).
fn run_cases(tag: &str, prelude: &str, cases: &[Case]) {
    let (src, mut lines) = build(prelude, cases);
    for (c, line) in cases.iter().zip(lines.iter_mut()) {
        if let Some(at) = &c.at {
            let n = src.lines().position(|l| l.trim() == at).unwrap_or_else(|| panic!("no line {at:?} in\n{src}"));
            *line = n + 1;
        }
    }
    let d = Dir::pkg(tag);
    d.write("m.onsa", &src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}\n{src}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "the program does not check: {doc}\n{src}");
    assert_eq!(tests_of(&doc).len(), cases.len(), "{doc}");
    let text = run(d.root(), &["test", &d.arg()]);
    assert_eq!(text.code, 1, "{}{}", text.stdout, text.stderr);
    for (c, line) in cases.iter().zip(&lines) {
        check_json(c, &doc, &src);
        check_text(c, *line, &text);
    }
}

// ---------------------------------------------------------------- the forms that give values

/// §18.1 (S-1261): each of the six comparisons gives the two values it compared, including the
/// failure of `!=` (equal values) and an operand that is an expression; every integer type.
#[test]
fn the_six_comparisons_and_the_integer_types_show_both_sides() {
    let two = |op: &str, a: i32, b: i32| format!("let a: I32 = {a}\nlet b: I32 = {b}\nassert a {op} b");
    run_cases(
        "values_ops",
        "",
        &[
            show("eq", "assert 1 == 2", "1", "2"),
            show("ne", &two("!=", 3, 3), "3", "3"),
            show("lt", &two("<", 5, 3), "5", "3"),
            show("le", &two("<=", 5, 3), "5", "3"),
            show("gt", &two(">", 3, 5), "3", "5"),
            show("ge", &two(">=", 3, 5), "3", "5"),
            show("negative", &two("==", -5, 5), "-5", "5"),
            show("expression", "let x: I32 = 2\nassert x * 3 == 7", "6", "7"),
            show("i8", "let a: I8 = -128\nlet b: I8 = 127\nassert a == b", "-128", "127"),
            show(
                "i64",
                "let a: I64 = -9223372036854775807\nlet b: I64 = 9223372036854775807\nassert a == b",
                "-9223372036854775807",
                "9223372036854775807",
            ),
            show("u8", "let a: U8 = 255\nlet b: U8 = 0\nassert a == b", "255", "0"),
            show("u32", "let a: U32 = 4294967295\nlet b: U32 = 0\nassert a == b", "4294967295", "0"),
            show(
                "u64",
                "let a: U64 = 18446744073709551615\nlet b: U64 = 1\nassert a == b",
                "18446744073709551615",
                "1",
            ),
        ],
    );
}

/// §6.3: a float is its shortest decimal that reads back to its own type, always with a point
/// (`1.0`, `-0.0`), `NaN`, `inf` and `-inf`, an exponent from `1.0e21` and below `1.0e-7`. An
/// `F32` is shown as an `F32` (`0.1`, not `0.10000000149011612`); `Bool` is `true` and `false`.
/// The expected strings were checked with the shortest forms of Rust (`{}` and `{:e}`) for each type.
#[test]
fn floats_and_bools_show_their_shortest_form() {
    run_cases(
        "values_floats",
        "",
        &[
            show("f64 sum", "let a: F64 = 0.1\nlet b: F64 = 0.2\nassert a + b == 0.3", "0.30000000000000004", "0.3"),
            show("f64 whole", "let a: F64 = 1.0\nassert a == 2.0", "1.0", "2.0"),
            show("f64 negative zero", "let z: F64 = -0.0\nassert z == 1.0", "-0.0", "1.0"),
            show("f64 zeros", "let z: F64 = -0.0\nlet p: F64 = 0.0\nassert z < p", "-0.0", "0.0"),
            show("f64 nan", "let n: F64 = F64.NAN\nassert n == n", "NaN", "NaN"),
            show("f64 nan order", "let n: F64 = F64.NAN\nassert n <= 1.0", "NaN", "1.0"),
            show("f64 inf", "let i: F64 = F64.INFINITY\nassert i < 1.0", "inf", "1.0"),
            show("f64 negative inf", "let m: F64 = -F64.INFINITY\nassert m > 1.0", "-inf", "1.0"),
            show(
                "f64 e21 edge",
                "let a: F64 = 1.0e21\nlet b: F64 = 1.0e20\nassert a == b",
                "1.0e21",
                "100000000000000000000.0",
            ),
            show("f64 large", "let a: F64 = 1.2345e25\nlet b: F64 = -2.5e22\nassert a == b", "1.2345e25", "-2.5e22"),
            show("f64 small", "let a: F64 = 1.5e-8\nlet b: F64 = 1.0e-6\nassert a == b", "1.5e-8", "0.000001"),
            show("f64 e-7 edge", "let a: F64 = 1.0e-7\nlet b: F64 = 9.0e-8\nassert a == b", "0.0000001", "9.0e-8"),
            show("f32 shortest", "let a: F32 = 0.1\nlet b: F32 = 0.2\nassert a == b", "0.1", "0.2"),
            show("f32 sum", "let a: F32 = 0.1\nlet b: F32 = 0.2\nassert a + b == 0.4", "0.3", "0.4"),
            show("f32 third", "let a: F32 = 1.0\nlet b: F32 = 3.0\nassert a / b == 0.5", "0.33333334", "0.5"),
            show("f32 widened", "let a: F32 = 0.1\nassert (a as F64) == 0.1", "0.10000000149011612", "0.1"),
            show("f32 max", "let a: F32 = 3.4028235e38\nlet b: F32 = 1.0\nassert a == b", "3.4028235e38", "1.0"),
            show(
                "f32 e21 edge",
                "let a: F32 = 1.0e21\nlet b: F32 = 1.0e20\nassert a == b",
                "1.0e21",
                "100000000000000000000.0",
            ),
            show("f32 small", "let a: F32 = 1.5e-8\nlet b: F32 = 1.0e-6\nassert a == b", "1.5e-8", "0.000001"),
            show("f32 nan", "let n: F32 = F32.NAN\nassert n == n", "NaN", "NaN"),
            show("f32 inf", "let i: F32 = F32.INFINITY\nassert i < 1.0", "inf", "1.0"),
            show("bool eq", "let t = true\nlet f = false\nassert t == f", "true", "false"),
            show("bool ne", "let t = true\nassert t != t", "true", "true"),
            show("bool of comparisons", "let a: I32 = 1\nlet b: I32 = 2\nassert (a < b) == false", "true", "false"),
        ],
    );
}

/// §6.3 (G5): a `Char` is in its literal form at the top, with its escapes: `'a'`, `'\n'`, `'\''`,
/// `'\\'`. The rare characters (S-270) are not here.
#[test]
fn a_char_is_shown_in_its_literal_form_at_the_top() {
    run_cases(
        "values_chars",
        "",
        &[
            show("plain", "let a: Char = 'a'\nlet b: Char = 'b'\nassert a == b", "'a'", "'b'"),
            show("order", "let a: Char = 'b'\nlet b: Char = 'a'\nassert a < b", "'b'", "'a'"),
            show("newline", "let a: Char = '\\n'\nassert a == 'x'", r"'\n'", "'x'"),
            show("quote", "let a: Char = '\\''\nassert a == 'x'", r"'\''", "'x'"),
            show("backslash", "let a: Char = '\\\\'\nassert a == 'x'", r"'\\'", "'x'"),
        ],
    );
}

/// §6.3: tuples, arrays, `Option` and `Result` are in the form of an expression; a `Char` inside
/// is in its literal form; floats inside are in the shortest form of their type. Short values are
/// whole (no cut): `[F32; 8]` is 40 characters.
#[test]
fn tuples_arrays_options_and_results_show_their_elements() {
    run_cases(
        "values_composite",
        "",
        &[
            show(
                "tuple with a char",
                "let a: (I32, Char) = (1, 'a')\nlet b: (I32, Char) = (2, 'b')\nassert a == b",
                "(1, 'a')",
                "(2, 'b')",
            ),
            show("tuple with a float", "let a: (I32, F64) = (1, 2.0)\nassert a == (1, 3.0)", "(1, 2.0)", "(1, 3.0)"),
            show(
                "array",
                "let a: [I32; 3] = [1, 2, 3]\nlet b: [I32; 3] = [1, 2, 4]\nassert a == b",
                "[1, 2, 3]",
                "[1, 2, 4]",
            ),
            show("array of chars", "let a: [Char; 2] = ['a', 'b']\nassert a == ['a', 'c']", "['a', 'b']", "['a', 'c']"),
            show(
                "array of arrays",
                "let a: [[I32; 2]; 2] = [[1, 2], [3, 4]]\nassert a == [[1, 2], [3, 5]]",
                "[[1, 2], [3, 4]]",
                "[[1, 2], [3, 5]]",
            ),
            show("empty array", "let a: [I32; 0] = []\nassert a != a", "[]", "[]"),
            show(
                "short f32 array",
                "let a: [F32; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\nlet b: [F32; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 9.5]\nassert a == b",
                "[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]",
                "[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 9.5]",
            ),
            show(
                "some and none",
                "let a: Option[I32] = Some(1)\nlet b: Option[I32] = None\nassert a == b",
                "Some(1)",
                "None",
            ),
            show("some float", "let a: Option[F64] = Some(0.5)\nassert a == None", "Some(0.5)", "None"),
            show(
                "some char",
                "let a: Option[Char] = Some('a')\nlet b: Option[Char] = Some('b')\nassert a == b",
                "Some('a')",
                "Some('b')",
            ),
            show(
                "some tuple",
                "let a: Option[(I32, Char)] = Some((1, 'a'))\nlet b: Option[(I32, Char)] = None\nassert a == b",
                "Some((1, 'a'))",
                "None",
            ),
            show(
                "nested option",
                "let a: Option[Option[I32]] = Some(Some(1))\nlet b: Option[Option[I32]] = Some(None)\nassert a == b",
                "Some(Some(1))",
                "Some(None)",
            ),
            show(
                "ok and err",
                "let a: Result[I32, U32] = Ok(1)\nlet b: Result[I32, U32] = Err(7)\nassert a == b",
                "Ok(1)",
                "Err(7)",
            ),
            show(
                "ok char",
                "let a: Result[Char, I32] = Ok('a')\nlet b: Result[Char, I32] = Err(2)\nassert a == b",
                "Ok('a')",
                "Err(2)",
            ),
        ],
    );
}

// ---------------------------------------------------------------- the forms that give no values

const NO_SHOW_TYPES: &str = "pub struct P: PartialEq {
  x: I32,
}

pub enum M: PartialEq {
  Off,
  On(I32),
}

pub fn is_pos(x: I32) -> Bool {
  x > 0
}
";

/// §18.1 (G1): a type that does not satisfy `Show` gives no values: `()`, a struct and an enum of
/// the program (this version does not derive `Show`), and a tuple, an array, an `Option` and a
/// `Result` that hold one. The message and the result line are the same as before.
#[test]
fn types_without_show_give_no_values() {
    run_cases(
        "novalues_types",
        NO_SHOW_TYPES,
        &[
            plain("unit", "let u = ()\nassert u != u"),
            plain("struct eq", "let a = P { x: 1 }\nlet b = P { x: 2 }\nassert a == b"),
            plain("enum", "assert M.Off == M.On(1)"),
            plain("enum payload", "let a = M.On(1)\nlet b = M.On(2)\nassert a == b"),
            plain("tuple with a struct", "let a: (P, I32) = (P { x: 1 }, 1)\nassert a == (P { x: 2 }, 1)"),
            plain("option of a struct", "let a: Option[P] = Some(P { x: 1 })\nlet b: Option[P] = None\nassert a == b"),
            plain(
                "result of a struct",
                "let a: Result[P, I32] = Ok(P { x: 1 })\nlet b: Result[P, I32] = Err(1)\nassert a == b",
            ),
            plain(
                "array of structs",
                "let a: [P; 2] = [P { x: 1 }, P { x: 2 }]\nlet b: [P; 2] = [P { x: 1 }, P { x: 3 }]\nassert a == b",
            ),
        ],
    );
}

/// §18.1: an `assert` that is not a comparison at the top (outside its parentheses) gives no
/// values: `&&`, `||`, `!`, a call, a bare `false`, even when a comparison is inside.
#[test]
fn an_assert_that_is_not_a_comparison_gives_no_values() {
    run_cases(
        "novalues_forms",
        NO_SHOW_TYPES,
        &[
            plain("and", "let a: I32 = 0\nlet b: I32 = 2\nassert a == 1 && b == 2"),
            plain("or", "let a: I32 = 0\nlet b: I32 = 0\nassert a == 1 || b == 1"),
            plain("chain", "let a: I32 = 1\nlet b: I32 = 2\nlet c: I32 = 0\nassert a == 1 && b == 2 && c == 3"),
            plain("parts in parentheses", "let a: I32 = 0\nlet b: I32 = 2\nassert (a == 1) && (b == 2)"),
            plain("parentheses around and", "let a: I32 = 0\nassert (a == 1 && a == 0)"),
            plain("not", "let a: I32 = 0\nassert !(a == 0)"),
            plain("call", "assert is_pos(0)"),
            plain("false", "assert false"),
        ],
    );
}

const GENERIC_BODIES: &str = "pub fn same[T: PartialEq](a: T, b: T) {
  assert a == b
}

pub fn same_show[T: PartialEq + Show](p: T, q: T) {
  assert p == q
}

pub fn zero_num[T: Num](z: T) {
  assert z == T.ZERO
}

pub fn zero_show[T: Num + Show](w: T) {
  assert w == T.ZERO
}

pub fn less[T: PartialOrd](m: T, n: T) {
  assert m < n
}

pub fn less_show[T: PartialOrd + Show](s: T, t: T) {
  assert s < t
}

pub struct P: PartialEq {
  x: I32,
}
";

/// §4.5, §18.1 (G2): in a generic body the type of an operand is a type parameter, and what it
/// satisfies is what its bounds say: `T: PartialEq` and `T: Num` (which does not include `Show`)
/// give no values, though `I32` has `Show` in the instance. The message and the position are the
/// `assert` in the generic function.
#[test]
fn a_type_parameter_without_show_in_its_bounds_gives_no_values() {
    run_cases(
        "novalues_generic",
        GENERIC_BODIES,
        &[
            plain("partial eq", "same(1, 2)").msg("assert a == b").at("assert a == b"),
            plain("partial eq tuple", "same((1, 'a'), (2, 'b'))").msg("assert a == b").at("assert a == b"),
            plain("partial eq struct", "same(P { x: 1 }, P { x: 2 })").msg("assert a == b").at("assert a == b"),
            plain("num", "zero_num(5)").msg("assert z == T.ZERO").at("assert z == T.ZERO"),
            plain("partial ord", "less(3, 2)").msg("assert m < n").at("assert m < n"),
        ],
    );
}

/// §4.5, §18.1 (G2): with `Show` in the bounds (`T: PartialEq + Show`, `T: Num + Show`,
/// `T: PartialOrd + Show`) the values are shown, for any instance of the type parameter.
#[test]
fn a_type_parameter_with_show_in_its_bounds_gives_values() {
    run_cases(
        "values_generic",
        GENERIC_BODIES,
        &[
            show("show int", "same_show(1, 2)", "1", "2").msg("assert p == q").at("assert p == q"),
            show("show tuple", "same_show((1, 'a'), (2, 'b'))", "(1, 'a')", "(2, 'b')")
                .msg("assert p == q")
                .at("assert p == q"),
            show("show char", "same_show('a', 'b')", "'a'", "'b'").msg("assert p == q").at("assert p == q"),
            show("show float", "let a: F64 = 1.5\nlet b: F64 = 2.5\nsame_show(a, b)", "1.5", "2.5")
                .msg("assert p == q")
                .at("assert p == q"),
            show("show num int", "zero_show(5)", "5", "0").msg("assert w == T.ZERO").at("assert w == T.ZERO"),
            show("show num float", "let a: F64 = 2.5\nzero_show(a)", "2.5", "0.0")
                .msg("assert w == T.ZERO")
                .at("assert w == T.ZERO"),
            show("show order", "less_show(3, 2)", "3", "2").msg("assert s < t").at("assert s < t"),
        ],
    );
}

// ---------------------------------------------------------------- parentheses and lines

/// §18.1: the parentheses outside the whole expression are removed to see that it is a comparison
/// (any number of them); the message keeps them, as written. Parentheses round an operand, or
/// inside it, do not change what is compared.
#[test]
fn the_outer_parentheses_are_looked_through_and_the_message_keeps_them() {
    run_cases(
        "values_parentheses",
        "",
        &[
            show("one", "let a: I32 = 1\nassert (a == 2)", "1", "2"),
            show("two", "let a: I32 = 1\nassert ((a == 2))", "1", "2"),
            show("operands", "let a: I32 = 1\nassert (a) == (2)", "1", "2"),
            show("sums", "let a: I32 = 1\nassert (a + 1) == (a + 2)", "2", "3"),
        ],
    );
}

/// `spec/tools.md` §4, §18.1: an `assert` of more lines. The message is the source, its lines
/// after the first as written; the text puts the first line in the result line, the others in
/// indented lines, and the two values after them.
#[test]
fn a_multi_line_assert_has_its_message_lines_and_then_the_values() {
    run_cases(
        "values_lines",
        "pub fn add(a: I32, b: I32) -> I32 {\n  a + b\n}\n",
        &[
            show("parenthesised", "let a: I32 = 1\nassert (a ==\n    2)", "1", "2"),
            show("operator at the end", "let a: I32 = 1\nassert a ==\n    2", "1", "2"),
            show("call over lines", "let a: I32 = 1\nassert add(\n    a,\n    3\n  ) == 5", "4", "5"),
            show("both sides over lines", "assert add(\n    1,\n    1\n  ) ==\n  add(\n    2,\n    2\n  )", "2", "4"),
        ],
    );
}

// ---------------------------------------------------------------- order and once

const COUNTERS: &str = "pub fn next(inout n: I32) -> I32 {
  n = n + 1
  n
}
";

/// §3.5 and §18.1: the operands are evaluated in order, and the values shown are the ones
/// compared: the left is read before the call on the right changes `x` (`1`, not `2`). An operand
/// with an effect is evaluated once: the two calls that count give `1` and `2` (`+ 5` is `7`), not
/// the values of a second evaluation; and a passing `assert` has evaluated its operand once (`n`
/// is `1` after it).
#[test]
fn operands_are_evaluated_once_in_order_and_the_values_are_those_compared() {
    run_cases(
        "values_order",
        COUNTERS,
        &[
            show("left before the call", "var x: I32 = 1\nassert x == next(inout x)", "1", "2"),
            show("once when failing", "var n: I32 = 0\nassert next(inout n) == next(inout n) + 5", "1", "7"),
            show("once when passing", "var n: I32 = 0\nassert next(inout n) == 1\nassert n == 2", "1", "2"),
            show(
                "once for each side",
                "var n: I32 = 0\nvar m: I32 = 10\nassert next(inout n) > next(inout m)",
                "1",
                "11",
            ),
            // The call with an effect inside a literal of an aggregate is evaluated once too.
            show("once in a tuple", "var n: I32 = 0\nassert (next(inout n), 1) == (7, 1)", "(1, 1)", "(7, 1)"),
            show("once in an array", "var n: I32 = 0\nassert [next(inout n), 1] == [7, 1]", "[1, 1]", "[7, 1]"),
            show("once in some", "var n: I32 = 0\nassert Some(next(inout n)) == Some(7)", "Some(1)", "Some(7)"),
            show("once in a repeat", "var n: I32 = 0\nassert [next(inout n); 2] == [7, 7]", "[1, 1]", "[7, 7]"),
        ],
    );
}

/// §3.5, §18.1: a panic in an operand (an index out of range) is a failure of `kind` `"panic"`,
/// before there are values to show, so the failure has no `left` and no `right` and the text has
/// no value lines. The panic is in the operand, on the left, on the right, or in a call (the text
/// names the innermost position out of std, the line in the function called).
#[test]
fn a_panic_in_an_operand_gives_no_values() {
    run_cases(
        "novalues_panic",
        "pub fn element(xs: [I32; 2], i: U32) -> I32 {\n  xs[i]\n}\n",
        &[
            plain("left", "let xs: [I32; 2] = [1, 2]\nlet i: U32 = 2\nassert xs[i] == 0").kind("panic"),
            plain("right", "let xs: [I32; 2] = [1, 2]\nlet i: U32 = 2\nassert 0 == xs[i]").kind("panic"),
            plain("in a call", "let xs: [I32; 2] = [1, 2]\nlet i: U32 = 2\nassert element(xs, i) == 0")
                .kind("panic")
                .at("xs[i]"),
        ],
    );
}

// ---------------------------------------------------------------- std

/// §18.1, `spec/tools.md` §4 (S-1261): an `assert` in the body of std shows its values too: the
/// two `assert`s of `std.dsp.test.energy` (`from <= to`, `to <= xs.len()`). The JSON keeps the
/// position in std (`std/dsp/test.onsa`); the text names the line of the call in the test.
#[test]
fn an_assert_in_a_std_body_shows_its_values() {
    let cases = [
        show("range reversed", "let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]\nassert energy(xs, 5, 2) == 0.0", "5", "2")
            .msg("assert from <= to")
            .kind(""),
        show("range past the end", "let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]\nassert energy(xs, 0, 9) == 0.0", "9", "4")
            .msg("assert to <= xs.len()")
            .kind(""),
    ];
    run_cases("values_std", "use std.dsp.test.energy\n", &cases);
    let d = Dir::pkg("values_std_file");
    let (src, _) = build("use std.dsp.test.energy\n", &cases);
    d.write("m.onsa", &src);
    let (_out, doc) = test_json(d.root(), &[&d.arg()]);
    for name in ["range reversed", "range past the end"] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]).file, "std/dsp/test.onsa", "{f}");
        assert!(!array_of(f, "calls").is_empty(), "{f}");
    }
}

// ---------------------------------------------------------------- long values

/// The two values of the case `name` in the JSON and in the text, and that they are the same
/// strings.
fn values_of(doc: &Value, text: &Out, name: &str) -> (String, String) {
    let f = failure_of(record(doc, "m", name));
    let (l, r) = (str_of(f, "left").to_string(), str_of(f, "right").to_string());
    let (_, rest) = block_of(text, name);
    let got: Vec<&str> = rest.iter().map(|l| l.trim_start()).collect();
    assert_eq!(got, [format!("left: {l}"), format!("right: {r}")], "{name}: the lines of the text are the JSON");
    assert!(!l.contains('\n') && !r.contains('\n'), "{name}: a value is one line");
    (l, r)
}

/// §18.1 (G3): a long value is cut. The length and the mark are not fixed, so: a `[F32; 2000]` has
/// a `Show` string of about 10000 characters, and what is shown is much shorter, starts as the
/// whole string does (`[` and the first elements), and is the same string in the JSON and in the
/// text. The same for a long array inside a tuple. A value that is equal on both sides (`!=`) is
/// cut the same on both sides.
#[test]
fn a_long_value_is_cut_and_starts_as_the_whole_string_does() {
    let src = "test \"two arrays\" {
  let a: [F32; 2000] = [0.5; 2000]
  let b: [F32; 2000] = [0.25; 2000]
  assert a == b
}

test \"same arrays\" {
  let a: [F32; 2000] = [0.5; 2000]
  let b: [F32; 2000] = [0.5; 2000]
  assert a != b
}

test \"in a tuple\" {
  let a: (I32, [F32; 2000]) = (1, [0.5; 2000])
  let b: (I32, [F32; 2000]) = (2, [0.5; 2000])
  assert a == b
}
";
    let d = Dir::pkg("values_long");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = run(d.root(), &["test", &d.arg()]);
    let whole = |elem: &str| format!("[{}]", vec![elem; 2000].join(", "));
    let (l, r) = values_of(&doc, &text, "two arrays");
    assert!(l.starts_with("[0.5, 0.5, 0.5,") && l.len() < whole("0.5").len() / 4, "{l}");
    assert!(r.starts_with("[0.25, 0.25, 0.25,") && r.len() < whole("0.25").len() / 4, "{r}");
    let (l, r) = values_of(&doc, &text, "same arrays");
    assert!(l.starts_with("[0.5, 0.5, 0.5,") && l.len() < whole("0.5").len() / 4, "{l}");
    assert_eq!(l, r, "the same value is cut the same way");
    let (l, r) = values_of(&doc, &text, "in a tuple");
    assert!(l.starts_with("(1, [0.5, 0.5,") && l.len() < whole("0.5").len() / 4, "{l}");
    assert!(r.starts_with("(2, [0.5, 0.5,") && r.len() < whole("0.5").len() / 4, "{r}");
}

// ---------------------------------------------------------------- what stays the same

/// `spec/tools.md` §4, §18.1: what the lines of the result and the message were before stays:
/// the result lines (the lines that start with `test`) are the same, with or without values, the
/// summary is the last line, every other line is indented, and `message` is `assert <source>`.
/// The same passes today and after the work.
#[test]
fn the_result_lines_and_the_messages_are_the_same_with_values_or_without() {
    let src = "pub struct P: PartialEq {
  x: I32,
}

test \"a ok\" {
  let x: I32 = 1
  assert x == 1
}

test \"b value\" {
  let x: I32 = 1
  assert x == 2
}

test \"c plain\" {
  let a = P { x: 1 }
  assert a == P { x: 2 }
}

test \"d lines\" {
  let x: I32 = 1
  assert (x ==
    2)
}

test \"e not a comparison\" {
  let x: I32 = 1
  assert x == 1 && x == 2
}
";
    let d = Dir::pkg("same_lines");
    d.write("m.onsa", src);
    let text = run(d.root(), &["test", &d.arg()]);
    assert_eq!(text.code, 1, "{}{}", text.stdout, text.stderr);
    assert_eq!(
        result_lines(&text),
        [
            "test m \"a ok\" ok",
            "test m \"b value\" failed at m.onsa:12: assert x == 2",
            "test m \"c plain\" failed at m.onsa:17: assert a == P { x: 2 }",
            "test m \"d lines\" failed at m.onsa:22: assert (x ==",
            "test m \"e not a comparison\" failed at m.onsa:28: assert x == 1 && x == 2",
        ],
        "{}",
        text.stdout
    );
    let lines: Vec<&str> = text.stdout.lines().collect();
    assert_eq!(lines.last().copied(), Some("1 passed, 4 failed"), "{}", text.stdout);
    for l in &lines {
        assert!(
            l.starts_with("test ") || l.starts_with(char::is_whitespace) || is_summary(l),
            "not a result, not indented: {l:?}"
        );
    }
    let (_out, doc) = test_json(d.root(), &[&d.arg()]);
    for (name, msg) in [
        ("b value", "assert x == 2"),
        ("c plain", "assert a == P { x: 2 }"),
        ("d lines", "assert (x ==\n    2)"),
        ("e not a comparison", "assert x == 1 && x == 2"),
    ] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(str_of(f, "message"), msg, "{f}");
        assert_eq!(str_of(f, "kind"), "assert", "{f}");
    }
    assert!(record(&doc, "m", "a ok").get("failure").is_none());
}

/// §18.1: a passing comparison prints no values: all passing tests give only result lines and the
/// summary, and the JSON has no `failure` (so no `left` and no `right`).
#[test]
fn passing_comparisons_print_no_values() {
    let src = "test \"one\" {
  let x: I32 = 1
  assert x == 1
  assert x != 2
  assert x < 2
  assert (x <= 1)
}

test \"two\" {
  let a: [F32; 2] = [0.5, 1.5]
  assert a == [0.5, 1.5]
  assert Some(1) == Some(1)
}
";
    let d = Dir::pkg("passing");
    d.write("m.onsa", src);
    let text = run(d.root(), &["test", &d.arg()]);
    assert_eq!(text.code, 0, "{}{}", text.stdout, text.stderr);
    assert_eq!(
        text.stdout.lines().collect::<Vec<_>>(),
        ["test m \"one\" ok", "test m \"two\" ok", "2 passed, 0 failed"]
    );
    let (_out, doc) = test_json(d.root(), &[&d.arg()]);
    for rec in tests_of(&doc) {
        assert!(rec.get("failure").is_none(), "{rec}");
    }
}
