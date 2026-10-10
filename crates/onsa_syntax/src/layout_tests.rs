//! Tests of the lines and blanks of §2.5 (the line facts of
//! [`crate::layout`], the candidates of `foreign/lists.rs` and the rows of
//! `foreign/spaces.rs`): the postfix openers kept apart from the token before
//! them (S-89, S-123, S-399), the missing `,` of a list (S-384, S-387, S-388,
//! S-373) and the literals with a prefix (S-400). Every candidate is applied
//! and the result is parsed again: the syntax stage reports nothing (S-236).

use onsa_diag::{Code, Diagnostic, FileId};

use crate::token::{Gap, TokenKind};

fn parse(src: &str) -> crate::Parsed {
    crate::parse(FileId(0), src)
}

/// The one diagnostic of `src`, and the source after each of its candidates.
#[track_caller]
fn one(src: &str) -> (Diagnostic, Vec<String>) {
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1, "{src}: {:?}", p.diagnostics);
    let d = p.diagnostics[0].clone();
    let fixed =
        d.fixes.iter().map(|f| onsa_diag::apply_text(src, &f.edits().iter().collect::<Vec<_>>()).unwrap()).collect();
    (d, fixed)
}

/// `src` has one diagnostic of `code` whose found text is `found`, and its
/// candidates give `want` in order, each of which parses with no diagnostic.
#[track_caller]
fn check(src: &str, code: Code, found: &str, want: &[&str]) {
    let (d, fixed) = one(src);
    assert_eq!(d.code, code, "{src}: {d:?}");
    assert_eq!(d.found.as_deref(), Some(found), "{src}: {d:?}");
    assert_eq!(fixed, want, "{src}");
    for f in &fixed {
        let after = parse(f);
        assert!(after.diagnostics.is_empty(), "{src}\nafter a candidate:\n{f}\n{:?}", after.diagnostics);
    }
}

const DECLS: &str = "fn two(a: I32, b: I32) -> I32 { a + b }\nfn h(x: I32) -> I32 { x }\n";

fn body(stmts: &str) -> String {
    format!("{DECLS}fn f(a: I32, b: I32, xs: [I32; 4]) -> I32 {{\n{stmts}\n}}\n")
}

#[test]
fn a_blank_before_an_opener_after_a_name_is_e0020() {
    check(&body("  h (a)"), Code::E0020, "(", &[&body("  h(a)")]);
    check(&body("  xs [0]"), Code::E0020, "[", &[&body("  xs[0]"), &body("  xs([0])")]);
    // `xs[0, 1]` is no index: the call is the one candidate.
    check(&body("  xs [0, 1]"), Code::E0020, "[", &[&body("  xs([0, 1])")]);
    check(&body("  two(h (a), 1)"), Code::E0020, "(", &[&body("  two(h(a), 1)")]);
    check("fn g (x: I32) -> I32 { x }\n", Code::E0020, "(", &["fn g(x: I32) -> I32 { x }\n"]);
    check("fn g[T] (x: T) -> T { x }\n", Code::E0020, "(", &["fn g[T](x: T) -> T { x }\n"]);
    check("fn g [T](x: T) -> T { x }\n", Code::E0020, "[", &["fn g[T](x: T) -> T { x }\n"]);
    check("fn g(o: Option [I32]) {\n}\n", Code::E0020, "[", &["fn g(o: Option[I32]) {\n}\n"]);
    check(
        "fn g(o: Option[I32]) -> I32 {\n  match o {\n    Some (v) => v,\n    None => 0,\n  }\n}\n",
        Code::E0020,
        "(",
        &["fn g(o: Option[I32]) -> I32 {\n  match o {\n    Some(v) => v,\n    None => 0,\n  }\n}\n"],
    );
    check("@repr (c)\nstruct S {\n  a: I32,\n}\n", Code::E0020, "(", &["@repr(c)\nstruct S {\n  a: I32,\n}\n"]);
    check("enum E {\n  V (I32),\n}\n", Code::E0020, "(", &["enum E {\n  V(I32),\n}\n"]);
}

#[test]
fn a_blank_before_a_mark_is_e0020() {
    let s = "struct P {\n  x: I32,\n}\nimpl P {\n  fn s(inout self, k: I32) {\n    self.x = k\n  }\n}\n";
    check(
        &format!("{s}fn g(inout p: P) {{\n  p.s !(2)\n}}\n"),
        Code::E0020,
        "!",
        &[&format!("{s}fn g(inout p: P) {{\n  p.s!(2)\n}}\n")],
    );
    let lp = "flow lp(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    check(
        &format!("{lp}flow g(x: F32 at sample) -> F32 at sample {{\n  lp ~(x)\n}}\n"),
        Code::E0020,
        "~",
        &[&format!("{lp}flow g(x: F32 at sample) -> F32 at sample {{\n  lp~(x)\n}}\n")],
    );
}

#[test]
fn a_blank_before_an_opener_after_no_name_is_a_missing_comma_in_a_list() {
    // S-399: the `,` first, then the blank taken out when it reads.
    let tuples = "fn t() -> [(I32, I32); 2] {\n  [(1, 2) (3, 4)]\n}\n";
    check(tuples, Code::E0002, "(", &["fn t() -> [(I32, I32); 2] {\n  [(1, 2), (3, 4)]\n}\n"]);
    let arrays = "fn k(x: I32) -> [I32; 2] { [x, x] }\nfn t(x: I32) -> [I32; 2] {\n  [k(x) [0], 1]\n}\n";
    check(
        arrays,
        Code::E0002,
        "[",
        &[
            "fn k(x: I32) -> [I32; 2] { [x, x] }\nfn t(x: I32) -> [I32; 2] {\n  [k(x), [0], 1]\n}\n",
            "fn k(x: I32) -> [I32; 2] { [x, x] }\nfn t(x: I32) -> [I32; 2] {\n  [k(x)[0], 1]\n}\n",
        ],
    );
}

#[test]
fn a_blank_before_an_opener_after_no_name_out_of_a_list() {
    // The blank taken out when that reads; `g(x)(y)` does not (R-203).
    let arrays = "fn k(x: I32) -> [I32; 2] { [x, x] }\n";
    check(
        &format!("{arrays}fn t(x: I32) -> I32 {{\n  k(x) [0]\n}}\n"),
        Code::E0020,
        "[",
        &[&format!("{arrays}fn t(x: I32) -> I32 {{\n  k(x)[0]\n}}\n")],
    );
    let (d, fixed) =
        one("fn g(x: I32) -> fn(I32) -> I32 { fn(a: I32) -> I32 { a } }\nfn k() -> I32 {\n  g(1) (2)\n}\n");
    assert_eq!((d.code, d.found.as_deref(), fixed.len()), (Code::E0002, Some("("), 0), "{d:?}");
    let (d, fixed) = one("fn k(g: fn(I32) -> fn(I32) -> I32) -> I32 {\n  g.(1) (2)\n}\n");
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
}

#[test]
fn a_line_break_before_an_opener_in_a_list() {
    // S-89: the `,`, and the line break taken out (after a path of names).
    check(&body("  h(h\n    (a))"), Code::E0002, "(", &[&body("  h(h,\n    (a))"), &body("  h(h(a))")]);
    // The code moves up before the comment of the line (S-216).
    check(
        &body("  two(h // c\n    (a), 1)"),
        Code::E0002,
        "(",
        &[&body("  two(h, // c\n    (a), 1)"), &body("  two(h(a), 1) // c")],
    );
    // After no path of names, only the `,`.
    check(&body("  two(h(a)\n    (b))"), Code::E0002, "(", &[&body("  two(h(a),\n    (b))")]);
    check(&body("  two(a\n    [b][0])"), Code::E0002, "[", &[&body("  two(a,\n    [b][0])"), &body("  two(a[b][0])")]);
}

#[test]
fn a_line_break_before_a_mark_in_a_list() {
    // S-373: the `,` when the mark starts an element (`!`, not `~`), and the
    // line break taken out after a name.
    let s = "struct P {\n  x: I32,\n}\nimpl P {\n  fn s(inout self, k: I32) -> I32 {\n    k\n  }\n}\n";
    let g = |args: &str| format!("{s}{DECLS}fn g(inout p: P) -> I32 {{\n  two({args}, 2)\n}}\n");
    check(&g("p.s\n    !(1)"), Code::E0002, "!", &[&g("p.s,\n    !(1)"), &g("p.s!(1)")]);
    let lp = "flow lp(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    let f = |args: &str| format!("{lp}flow g(x: F32 at sample) -> F32 at sample {{\n  F32.max({args}, 1.0)\n}}\n");
    check(&f("lp\n    ~(x)"), Code::E0002, "~", &[&f("lp~(x)")]);
}

#[test]
fn a_missing_comma_between_elements() {
    // S-384 and S-387: whatever is between the elements.
    check(&body("  two(a\n    b)"), Code::E0002, "b", &[&body("  two(a,\n    b)")]);
    check(&body("  two(a b)"), Code::E0002, "b", &[&body("  two(a, b)")]);
    let (d, _) = one(&body("  two(a b)"));
    assert_eq!(d.message, "expected `,` or `)`, found identifier");
    check(
        "fn t() -> [F32; 3] {\n  [0.1 0.2, 0.3]\n}\n",
        Code::E0002,
        "0.2",
        &["fn t() -> [F32; 3] {\n  [0.1, 0.2, 0.3]\n}\n"],
    );
    check("struct S {\n  x: I32\n  y: I32\n}\n", Code::E0002, "y", &["struct S {\n  x: I32,\n  y: I32\n}\n"]);
    check(
        "fn g(x: I32) -> I32 {\n  match x {\n    0 => { 1 }\n    _ => 0,\n  }\n}\n",
        Code::E0002,
        "_",
        &["fn g(x: I32) -> I32 {\n  match x {\n    0 => { 1 },\n    _ => 0,\n  }\n}\n"],
    );
    // An index holds one expression, and `~` starts no element: no `,`.
    let (d, fixed) = one(&body("  xs[a\n    b]"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    assert_eq!(d.message, "expected `]`, found identifier");
    let (d, fixed) = one(&body("  two(a ~b, 1)"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    // `fn name` declares a function, no element (the fuzzing's 45eb3d28).
    let (d, fixed) = one(&body("  two(a\n    fn q)"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
}

#[test]
fn two_string_literals_next_to_each_other() {
    // S-388: the `,`, then the one literal: the second literal's token goes,
    // and what is around it stays on its line.
    let f = |args: &str| format!("fn s(a: Str, b: Str) -> I32 {{ 1 }}\nfn g() -> I32 {{\n  s({args})\n}}\n");
    check(&f("\"a\" \"b\""), Code::E0002, "\"b\"", &[&f("\"a\", \"b\""), &f("\"ab\" ")]);
    check(&f("\"a\"\n    \"b\""), Code::E0002, "\"b\"", &[&f("\"a\",\n    \"b\""), &f("\"ab\"\n    ")]);
    check(&f("\"é\" \"😀\""), Code::E0002, "\"😀\"", &[&f("\"é\", \"😀\""), &f("\"é😀\" ")]);
    check(&f("\"a\" // c\n    \"b\""), Code::E0002, "\"b\"", &[&f("\"a\", // c\n    \"b\""), &f("\"ab\" // c\n    ")]);
}

#[test]
fn a_name_against_a_literal_is_e0002_with_no_candidate() {
    // S-400: found before the `,` of the list; the range is the name and the literal.
    let f = |args: &str| format!("fn s(a: Str, b: Str) -> I32 {{ 1 }}\nfn g() -> I32 {{\n  s({args})\n}}\n");
    for (args, found) in [("b\"x\", \"y\"", "b\"x\""), ("\"x\"_s, \"y\"", "\"x\"_s"), ("\"y\", u8\"x\"", "u8\"x\"")] {
        let (d, fixed) = one(&f(args));
        assert_eq!((d.code, d.found.as_deref(), fixed.len()), (Code::E0002, Some(found), 0), "{args}: {d:?}");
    }
    let (d, fixed) = one("fn g(x: I32) -> Str {\n  let a = f\"{x}\"\n  a\n}\n");
    assert_eq!((d.code, d.found.as_deref(), fixed.len()), (Code::E0002, Some("f\"{x}\""), 0), "{d:?}");
}

#[test]
fn a_blank_inside_a_visibility_is_the_form_of_the_visibility() {
    // `pub(crate)` is one form with its blanks (S-248): its own row, and the
    // candidate leaves nothing.
    check("pub (crate) fn g() {\n}\n", Code::E0020, "pub (crate)", &["fn g() {\n}\n"]);
    // `pub(pkg)` waits for W3-08 (`pub_pkg`): read as it is without the blank.
    assert!(parse("pub (pkg) fn g() {\n}\n").diagnostics.is_empty());
}

#[test]
fn a_line_break_before_the_parameters_of_an_anonymous_function_in_a_list() {
    // S-412: in a list a line break is a blank, and the list is required.
    let ap = "fn ap(f: fn(I32) -> I32, x: I32) -> I32 {\n  f.(x)\n}\n";
    check(
        &format!("{ap}fn g() -> I32 {{\n  ap(fn\n    (a: I32) -> I32 {{ a }}, 1)\n}}\n"),
        Code::E0020,
        "(",
        &[&format!("{ap}fn g() -> I32 {{\n  ap(fn(a: I32) -> I32 {{ a }}, 1)\n}}\n")],
    );
}

#[test]
fn a_literal_that_does_not_close_is_the_lexer_s_error() {
    // H1 of W3-06/b (1a): no candidate cuts a literal that does not close
    // (a character of several bytes at its end), and nothing panics: the
    // lexer's E0001 is there.
    for src in [
        "fn main() -> I32 { let a = [\"あ\n\"b\"]\n 0 }\n",
        "fn main() -> I32 { let a = [\"é\n\"b\"]\n 0 }\n",
        "fn main() -> I32 { let a = [\"😀\n\"b\"]\n 0 }\n",
        "fn main() -> I32 { two(\"あ\n\"b\", 1)\n}\n",
        "fn main() -> I32 { let a = (\"あ\n\"b\")\n 0 }\n",
        "fn main() -> I32 { let a = S { a: \"あ\n\"b\" }\n 0 }\n",
        "use a.{\"あ\n\"b\"}\n",
        "@repr(\"あ\n\"b\")\nfn main() -> I32 { 0 }\n",
        "fn main() -> I32 { let a = [\"ab\n\"c\"]\n 0 }\n",
    ] {
        let p = parse(src);
        assert!(p.diagnostics.iter().any(|d| d.code == Code::E0001), "{src}: {:?}", p.diagnostics);
        let merged = p.diagnostics.iter().flat_map(|d| &d.fixes).any(|f| f.title().contains("literals one"));
        assert!(!merged, "{src}: {:?}", p.diagnostics);
    }
}

#[test]
fn a_literal_with_an_error_against_a_name_is_the_lexer_s_error() {
    // M6 of W3-06/b (1a): S-400 is a whole literal against a name; a literal
    // that does not close or holds an error is the E0001 of §2.4.
    for src in [
        "fn main() -> Str {\n  let a = f\"abc\n  a\n}\n",
        "fn main() -> I32 { let a = x'ab'\n 0 }\n",
        "fn main() -> I32 {\n  let a = b'\n  0\n}\n",
        "flow ap(x: F32 at sample) -> F32 at sample {\n  let a = x'\n  a\n}\n",
    ] {
        let p = parse(src);
        assert!(p.diagnostics.iter().any(|d| d.code == Code::E0001), "{src}: {:?}", p.diagnostics);
        let prefix = p.diagnostics.iter().any(|d| d.message.contains("no prefix or suffix"));
        assert!(!prefix, "{src}: {:?}", p.diagnostics);
    }
}

#[test]
fn a_missing_comma_in_nested_type_arguments() {
    // M1 and M2 of W3-06/b (1a): the error inside a list of type arguments
    // that a type argument opened is that list's, at any depth.
    check(
        "type A = Result[Result[I32 Bool], Bool]\n",
        Code::E0002,
        "Bool",
        &["type A = Result[Result[I32, Bool], Bool]\n"],
    );
    check(
        "type A = Result[Result[I32, Bool] Bool]\n",
        Code::E0002,
        "Bool",
        &["type A = Result[Result[I32, Bool], Bool]\n"],
    );
    check(
        "fn f(x: Option[Option[Option[I32 Bool]]]) -> I32 {\n  0\n}\n",
        Code::E0002,
        "Bool",
        &["fn f(x: Option[Option[Option[I32, Bool]]]) -> I32 {\n  0\n}\n"],
    );
    // `[` starts a type, so the `,` is offered (S-384, the lexical condition);
    // `[I32]` is then no array type, the next check's error.
    let (d, fixed) = one("type A = Option[Option[Option\n  [I32]]]\n");
    assert_eq!((d.code, d.found.as_deref()), (Code::E0002, Some("[")), "{d:?}");
    assert_eq!(fixed, ["type A = Option[Option[Option,\n  [I32]]]\n", "type A = Option[Option[Option[I32]]]\n"]);
    // A const argument is still an expression.
    assert!(parse("type A = Ring[F32, N * 2]\n").diagnostics.is_empty());
    // A range symbol goes on with the expression too: the range is the
    // table's `range_outside_header` (as before W3-06), not a missing `,`.
    for src in ["type A = Buf[F32, N..<4]\n", "type A = Option[0..<2]\n"] {
        let (d, _) = one(src);
        assert_eq!(
            (d.code, d.message.as_str()),
            (Code::E0002, "ranges are only written in `for` and `par` heads"),
            "{src}"
        );
    }
}

#[test]
fn a_line_break_before_the_parenthesis_of_a_pattern_in_an_arm() {
    // M3 of W3-06/b (1a): the line break taken out, as in a tuple pattern;
    // no `,` (`Some,` is no arm).
    let g = |arm: &str| {
        format!("fn g(o: Option[I32]) -> I32 {{\n  match o {{\n    {arm} => x,\n    None => 0,\n  }}\n}}\n")
    };
    check(&g("Some\n    (x)"), Code::E0002, "(", &[&g("Some(x)")]);
}

#[test]
fn an_array_type_after_a_blank_is_no_list_of_type_arguments() {
    // M5 of W3-06/b (1a): `I32[I32; 2]` would not read (S-236): in a list it
    // is the missing `,`, out of a list E0002 with no candidate.
    check("type A = (I32 [I32; 2])\n", Code::E0002, "[", &["type A = (I32, [I32; 2])\n"]);
    let (d, fixed) = one("struct S {\n  a: I32 [I32; 2],\n}\n");
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
}

#[test]
fn a_blank_before_the_type_parameters_of_an_impl() {
    // S-412: `impl [T] P[T]` is a blank before the list.
    let p = "struct P[T] {\n  a: T,\n}\n";
    check(&format!("{p}impl [T] P[T] {{\n}}\n"), Code::E0020, "[", &[&format!("{p}impl[T] P[T] {{\n}}\n")]);
}

// ------------------------------------------------------------ unit 1b of W3-06

#[test]
fn a_binary_minus_with_a_blank_only_before_it() {
    // S-398: `a - -b` has blanks on both sides; `a -b` is the form, with the
    // `,` in a list whose elements are expressions.
    assert!(parse(&body("  let c = a - -b\n  c")).diagnostics.is_empty());
    check(&body("  let c = a -b\n  c"), Code::E0020, "-", &[&body("  let c = a - b\n  c")]);
    check(&body("  two(a -b, 1)"), Code::E0020, "-", &[&body("  two(a - b, 1)"), &body("  two(a, -b, 1)")]);
    check(&body("  xs[a -1]"), Code::E0020, "-", &[&body("  xs[a - 1]")]);
}

#[test]
fn a_blank_or_a_line_break_after_a_prefix_symbol() {
    // S-123, S-369, S-411.
    check(&body("  let c = - a\n  c"), Code::E0020, "-", &[&body("  let c = -a\n  c")]);
    check(&body("  two(-\n    a, 1)"), Code::E0020, "-", &[&body("  two(\n    -a, 1)")]);
    let m = |arm: &str| format!("fn g(k: I32) -> I32 {{\n  match k {{\n    {arm} => 1,\n    _ => 0,\n  }}\n}}\n");
    check(&m("- 1"), Code::E0020, "-", &[&m("-1")]);
    // S-410: a stack with blanks is the E0012 of the stack, and its candidate
    // takes the blanks out.
    check(&body("  let c = - - a\n  c"), Code::E0012, "- - a", &[&body("  let c = -(-a)\n  c")]);
}

#[test]
fn a_line_break_after_a_member_dot_and_before_a_question_mark() {
    // S-353, S-369.
    check(&body("  let c = (a, b).\n    0\n  c"), Code::E0020, ".", &[&body("  let c = (a, b)\n    .0\n  c")]);
    let o = |s: &str| format!("{DECLS}fn f(o: Option[I32]) -> Option[I32] {{\n{s}\n}}\n");
    check(&o("  Some(two(o\n    ?, 1))"), Code::E0020, "?", &[&o("  Some(two(o?\n    , 1))")]);
    check(&o("  let v = o ?\n  Some(v)"), Code::E0020, "?", &[&o("  let v = o?\n  Some(v)")]);
}

#[test]
fn a_blank_or_a_line_break_between_a_mark_and_its_parenthesis() {
    // S-412: one form with the blank before the mark too.
    let lp = "flow lp(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
    let g = |call: &str| format!("{lp}flow g(x: F32 at sample) -> F32 at sample {{\n  {call}\n}}\n");
    check(&g("lp~ (x)"), Code::E0020, "~", &[&g("lp~(x)")]);
    check(&g("lp ~ (x)"), Code::E0020, "~", &[&g("lp~(x)")]);
    check(&g("lp~\n  (x)"), Code::E0020, "~", &[&g("lp~(x)")]);
}

#[test]
fn a_line_break_between_if_and_its_tilde_in_the_arms_of_a_match() {
    // S-385: the arms are a list where a line break is a blank; `~` and a
    // line break after it is no `!`.
    let g = |arm: &str| {
        format!("fn g(k: U32, c: Bool) -> F32 {{\n  match k {{\n    0 => {arm},\n    _ => 0.0,\n  }}\n}}\n")
    };
    check(
        &g("if\n      ~c { 1.0 } else { 2.0 }"),
        Code::E0020,
        "~",
        &[&g("if~\n      c { 1.0 } else { 2.0 }"), &g("if\n      !c { 1.0 } else { 2.0 }")],
    );
    let (d, fixed) = one(&g("if ~\n      c { 1.0 } else { 2.0 }"));
    assert_eq!((d.code, fixed.len()), (Code::E0020, 1), "{d:?}");
}

#[test]
fn a_statement_as_the_body_of_an_arm() {
    let g = |arm: &str| {
        format!("fn g(o: Option[I32]) -> I32 {{\n  match o {{\n    Some(v) => v,\n    None => {arm},\n  }}\n}}\n")
    };
    check(&g("return 0"), Code::E0020, "return", &[&g("{ return 0 }")]);
}

#[test]
fn a_line_that_ends_where_it_cannot_has_an_empty_range() {
    // The end of the code of the line, before its comment; no `found` (§18.1).
    let src = "fn g(c: Bool) -> I32 {\n  let a = if // c\n    ~c { 1 } else { 2 }\n  a\n}\n";
    let p = parse(src);
    let d = &p.diagnostics[0];
    assert_eq!((d.code, d.span.start, d.span.end, d.found.as_deref()), (Code::E0002, 35, 35, None), "{d:?}");
}

#[test]
fn a_clock_written_after_a_type_is_apart_from_the_name_after_it() {
    // R-205 (tests/fuzz/f60b27e5.onsa): ` at a` before `e` is not ` at ae`.
    let src = "flow m(x:(((F at a)))e";
    let p = parse(src);
    let d = p.diagnostics.iter().find(|d| d.code == Code::E0020).unwrap_or_else(|| panic!("{:?}", p.diagnostics));
    let fixed = onsa_diag::apply_text(src, &d.fixes[0].edits().iter().collect::<Vec<_>>()).unwrap();
    assert_eq!(fixed, "flow m(x:(((F))) at a e");
}

#[test]
fn the_prefix_rows_of_a_pattern_take_only_a_negative_integer() {
    // H1 and L1 of W3-06/b (1b): a range, a float or a constant after the
    // `-` is the form of its own row (no two rows on one failure, which is an
    // internal error), and another operand is no pattern (E0002, no candidate).
    let m = |pat: &str| {
        format!("const S: I32 = 1\nfn g(x: I32) -> I32 {{\n  match x {{\n    {pat} => 1,\n    _ => 0,\n  }}\n}}\n")
    };
    for (pat, message) in [
        ("- 1..<3", "ranges cannot be patterns"),
        ("-\n    1..=3", "ranges cannot be patterns"),
        ("- 0.5", "float literals cannot be patterns"),
        ("- S", "a constant with `-` cannot be a pattern"),
    ] {
        let p = parse(&m(pat));
        assert!(p.diagnostics.iter().any(|d| d.message.starts_with(message)), "{pat}: {:?}", p.diagnostics);
    }
    // The guard writes the `-` against the constant (S-123).
    let (d, fixed) = one(&m("- S"));
    assert_eq!((d.code, fixed[0].contains("v == -S")), (Code::E0020, true), "{fixed:?}");
    for pat in ["- x", "- _", "- true", "- (x)", "- (-1)"] {
        let (d, fixed) = one(&m(pat));
        assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{pat}: {d:?}");
    }
    check(&m("- (8)"), Code::E0020, "-", &[&m("-(8)")]);
    check(&m("-\n    1"), Code::E0020, "-", &[&m("-1")]);
}

#[test]
fn the_guard_of_a_range_writes_a_leading_minus_against_its_operand() {
    // W3-06/b (1b, the second check): `- 1..<3` has the guard `-1 <= v`, not
    // `- 1 <= v` (which the check after it would report, S-123, S-236).
    let m = |arm: &str| format!("fn g(x: I32) -> I32 {{\n  match x {{\n    {arm} => 1,\n    _ => 0,\n  }}\n}}\n");
    check(&m("- 1..<3"), Code::E0020, "- 1..<3", &[&m("v if -1 <= v && v < 3")]);
}

#[test]
fn a_line_break_after_a_dot_before_a_keyword() {
    // M1 of W3-06/b (1b): the keyword starts the next statement; no candidate.
    let s = "struct S {\n  f: I32,\n}\n";
    let (d, fixed) = one(&format!("{s}fn g(s: S) -> I32 {{\n  let c = s.\n  let d = 1\n  d\n}}\n"));
    assert_eq!((d.code, d.found.as_deref(), fixed.len()), (Code::E0002, Some("."), 0), "{d:?}");
}

#[test]
fn the_dot_of_a_path() {
    // M2 of W3-06/b (1b): the `.` of a path in a pattern, a type, a `use` and
    // an `impl` takes no blank and no line break after it, as in an expression.
    let e = "enum E {\n  A,\n  B,\n}\n";
    let m = |pat: &str| format!("{e}fn g(e: E) -> I32 {{\n  match e {{\n    {pat} => 1,\n    _ => 0,\n  }}\n}}\n");
    check(&m("E. A"), Code::E0020, ".", &[&m("E.A")]);
    check(&m("E .A"), Code::E0020, ".", &[&m("E.A")]);
    check(&m("E.\n      A"), Code::E0020, ".", &[&m("E\n      .A")]);
    check(
        &format!("{e}fn g(e: E) -> I32 {{\n  let x: E. A = e\n  1\n}}\n"),
        Code::E0020,
        ".",
        &[&format!("{e}fn g(e: E) -> I32 {{\n  let x: E.A = e\n  1\n}}\n")],
    );
    let (d, fixed) = one("use std. math\n");
    assert_eq!((d.code, fixed.as_slice()), (Code::E0020, ["use std.math\n".to_string()].as_slice()), "{d:?}");
    let (d, fixed) = one("use std.\n  math\n");
    assert_eq!((d.code, fixed.as_slice()), (Code::E0020, ["use std\n  .math\n".to_string()].as_slice()), "{d:?}");
    assert!(parse("use std\n  .math\n").diagnostics.is_empty());
    let (d, fixed) = one("struct S {\n  a: I32,\n}\nimpl S. T {\n}\n");
    assert_eq!((d.code, fixed[0].contains("impl S.T")), (Code::E0020, true), "{d:?}");
}

#[test]
fn a_stack_of_prefix_operators_over_lines() {
    // M3 of W3-06/b (1b): one form, the E0012 of the stack (S-410, S-248).
    check(&body("  two(-\n    -a, 1)"), Code::E0012, "-\n    -a", &[&body("  two(-(-a), 1)")]);
    let g = |s: &str| format!("fn g(c: Bool) -> Bool {{\n{s}\n}}\n");
    check(&g("  !\n    !c"), Code::E0012, "!\n    !c", &[&g("  !(!c)")]);
}

// ------------------------------------------------------------ W3-06 unit 2: lines

/// The codes of the parser's diagnostics of `src`.
fn codes(src: &str) -> Vec<Code> {
    parse(src).diagnostics.iter().map(|d| d.code).collect()
}

#[test]
fn a_line_goes_on_after_its_continuing_tokens_at_the_top_level_too() {
    // S-47, R-58, S-121, S-124, S-335, S-374: `=`, `->`, a range symbol, and a
    // next line that starts with `uses` or `.`; comment lines and blank lines between.
    for src in [
        "type Gain =\n  F32\n",
        "fn f(x: I32) ->\n  I32 {\n  x\n}\n",
        "fn f(x: I32) -> I32\n  uses {Alloc} {\n  x\n}\n",
        "type Op =\n  fn(I32) ->\n  I32\n",
        "fn f(n: U32) {\n  for i in 0..<\n    // the end\n\n    n {\n  }\n}\n",
        "fn f(a: I32, b: I32) -> I32 {\n  let c = a +\n    // b next\n\n    b\n  c\n}\n",
        "fn f(a: I32) -> I32 {\n  a\n    // the chain\n    .abs()\n}\n",
        "@repr(c)\nstruct P {\n  x: I32,\n}\n",
    ] {
        assert!(codes(src).is_empty(), "{src}: {:?}", parse(src).diagnostics);
    }
    // A prefix `-` at the end of a line does not go on (S-369).
    assert_eq!(codes("fn f(a: I32) -> I32 {\n  let y = -\n    a\n  y\n}\n"), [Code::E0020]);
}

#[test]
fn a_misplaced_else_with_brace_or_if_is_e0003_at_the_token() {
    // R-160: the main position and `found` are the misplaced token; the
    // reading goes on. S-414: the `if` after `else`. S-415: the bodies of
    // the declarations.
    check(&body("  if a > 0 { 1 }\n  else { 2 }"), Code::E0003, "else", &[&body("  if a > 0 { 1 } else { 2 }")]);
    check(
        &body("  if a > 0 { 1 } else\n  if b > 0 { 2 } else { 3 }"),
        Code::E0003,
        "if",
        &[&body("  if a > 0 { 1 } else if b > 0 { 2 } else { 3 }")],
    );
    check(
        &body("  two(if a > 0 { 1 }\n    else { 2 }, 1)"),
        Code::E0003,
        "else",
        &[&body("  two(if a > 0 { 1 } else { 2 }, 1)")],
    );
    check("struct P\n{\n  x: I32,\n}\n", Code::E0003, "{", &["struct P {\n  x: I32,\n}\n"]);
    check("enum E\n{\n  A,\n}\n", Code::E0003, "{", &["enum E {\n  A,\n}\n"]);
    check("trait T\n{\n}\n", Code::E0003, "{", &["trait T {\n}\n"]);
    check("test \"t\"\n{\n  assert true\n}\n", Code::E0003, "{", &["test \"t\" {\n  assert true\n}\n"]);
    check(&body("  while a > b\n  {\n  }\n  a"), Code::E0003, "{", &[&body("  while a > b {\n  }\n  a")]);
    // The comment of the misplaced token's line stays on its line (S-216).
    check(
        &body("  if a > 0 { 1 }\n  else { 2 } // two"),
        Code::E0003,
        "else",
        &[&body("  if a > 0 { 1 } else { 2 }\n  // two")],
    );
    // `with` of `handle` (in brackets too).
    let h = "effect Ask {\n  fn ask() -> I32\n}\nhandler one: Ask {\n  fn ask() -> I32 {\n    1\n  }\n}\n";
    let g = |e: &str| format!("{h}{DECLS}fn g() -> I32 {{\n  two({e}, 1)\n}}\n");
    check(&g("handle { 1 }\n    with one"), Code::E0003, "with", &[&g("handle { 1 } with one")]);
}

#[test]
fn the_brace_of_a_struct_literal_pattern_or_effect_row_in_brackets() {
    // S-413: in brackets, and in a `let` pattern, the `{` is on the line of
    // the name; out of brackets the line ends at the name (another reading).
    let s = "struct S {\n  a: I32,\n}\nfn two(s: S, b: I32) -> I32 {\n  s.a + b\n}\n";
    let g = |e: &str| format!("{s}fn g(s: S) -> I32 {{\n{e}\n}}\n");
    check(&g("  two(S\n    { a: 1 }, 2)"), Code::E0003, "{", &[&g("  two(S { a: 1 }, 2)")]);
    check(&g("  let S\n    { a: x } = s\n  x"), Code::E0003, "{", &[&g("  let S { a: x } = s\n  x")]);
    check(
        "fn h(k: fn(I32) -> I32 uses\n  {Alloc}, x: I32) -> I32 {\n  x\n}\n",
        Code::E0003,
        "{",
        &["fn h(k: fn(I32) -> I32 uses {Alloc}, x: I32) -> I32 {\n  x\n}\n"],
    );
    // Out of brackets `uses` ends the line (E0002), as before.
    assert_eq!(codes("fn h(x: I32) -> I32 uses\n  {Alloc} {\n  x\n}\n"), [Code::E0002]);
    // A constant before a `{` reads as a struct literal by its spelling; the
    // E0003 comes first, and the rest is the next check's (S-413).
    assert_eq!(codes(&body("  h(N\n    { 1 })"))[0], Code::E0003);
}

#[test]
fn the_brace_of_a_handler_written_in_place() {
    // S-421 (the provisional reading (1)): E0003 in brackets; out of them the
    // line ends at the handler's name.
    let h = "effect Ask {\n  fn ask() -> I32\n}\n";
    let g = |e: &str| format!("{h}{DECLS}fn g() -> I32 {{\n{e}\n}}\n");
    check(
        &g("  two(handle { 1 } with Ask\n    { fn ask() -> I32 { 1 } }, 1)"),
        Code::E0003,
        "{",
        &[&g("  two(handle { 1 } with Ask { fn ask() -> I32 { 1 } }, 1)")],
    );
    assert!(!codes(&g("  handle { 1 } with Ask\n  { fn ask() -> I32 { 1 } }")).contains(&Code::E0003));
}

#[test]
fn a_keyword_and_its_operand_in_brackets() {
    // S-416: no rule of place; in brackets the line break is a blank.
    assert!(codes(&body("  two(if\n    a > 0 { 1 } else { 2 }, match\n    a { _ => 1 })")).is_empty());
}

#[test]
fn an_operator_at_the_head_of_a_line() {
    // S-124, S-370: the operator moves to the end of the line before, before
    // its comment (S-216); in brackets too.
    check(&body("  let c = a\n  + b\n  c"), Code::E0020, "+", &[&body("  let c = a +\n  b\n  c")]);
    check(&body("  let c = a // one\n  * b\n  c"), Code::E0020, "*", &[&body("  let c = a * // one\n  b\n  c")]);
    check(&body("  two(a\n    + b, 1)"), Code::E0020, "+", &[&body("  two(a +\n    b, 1)")]);
    // In a head waiting for its `{`: the next line's operator.
    check(
        &body("  if a > 0\n  && b > 0 {\n  }\n  a"),
        Code::E0020,
        "&&",
        &[&body("  if a > 0 &&\n  b > 0 {\n  }\n  a")],
    );
    // `->` and `=` (S-374).
    check("fn f(a: I32)\n  -> I32 {\n  a\n}\n", Code::E0020, "->", &["fn f(a: I32) ->\n  I32 {\n  a\n}\n"]);
    check(
        "fn f(h: fn(I32)\n  -> I32, x: I32) -> I32 {\n  x\n}\n",
        Code::E0020,
        "->",
        &["fn f(h: fn(I32) ->\n  I32, x: I32) -> I32 {\n  x\n}\n"],
    );
    check(&body("  let c: I32\n  = 5\n  c"), Code::E0020, "=", &[&body("  let c: I32 =\n  5\n  c")]);
    check(&body("  var d = 1\n  d\n  = 5\n  d"), Code::E0020, "=", &[&body("  var d = 1\n  d =\n  5\n  d")]);
    // After a statement that has its `=` (or a `return`), a `=` goes on with nothing (S-236).
    let (d, fixed) = one(&body("  var d = 1\n  d = 2\n  = 5\n  d"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    check("type A = fn(I32)\n  -> I32\n", Code::E0020, "->", &["type A = fn(I32) ->\n  I32\n"]);
    // The `|` of a pattern choice (S-380).
    let m = |arms: &str| format!("fn g(x: U32) -> U32 {{\n  match x {{\n{arms}\n    _ => 0,\n  }}\n}}\n");
    check(&m("    0\n    | 1 => 1,"), Code::E0020, "|", &[&m("    0 |\n    1 => 1,")]);
    // `+b` touching its operand in a list of expressions: the `,` with the `+`
    // taken out is the second candidate (S-405); `+ b` has the move only.
    check(
        &body("  two(a\n    +b, 1)"),
        Code::E0020,
        "+",
        &[&body("  two(a +\n    b, 1)"), &body("  two(a,\n    b, 1)")],
    );
}

#[test]
fn no_candidate_moves_a_symbol_after_what_ends_no_operand() {
    // S-236, S-124: after the `}` of a `for`, a `while` or a declaration, the
    // moved symbol would follow no operand; the form is then no
    // `leading_operator` (the general E0002, or `prefix_plus` for a `+`).
    let d = &parse(&body("  for i in 0..<4 {\n  }\n  * 2")).diagnostics;
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].code, Code::E0002);
    check(&body("  while a > b {\n  }\n  +2"), Code::E0020, "+", &[&body("  while a > b {\n  }\n  2")]);
    assert_eq!(codes("fn f() {\n}\n+ 1\n"), [Code::E0002]);
    // After an `if` expression the line goes on (an operand).
    check(
        &body("  if a > 0 { 1 } else { 2 }\n  + 1"),
        Code::E0020,
        "+",
        &[&body("  if a > 0 { 1 } else { 2 } +\n  1")],
    );
}

#[test]
fn a_line_that_starts_with_minus_or_caret() {
    // `- b` after an operand: the blank out, or the line joined (leading_minus).
    check(
        &body("  let c = a\n  - b\n  c"),
        Code::E0020,
        "-",
        &[&body("  let c = a\n  -b\n  c"), &body("  let c = a - b\n  c")],
    );
    // In brackets: `-b` moves up or takes a `,` (S-370); `- b` joins only.
    check(
        &body("  two(a\n    -b, 1)"),
        Code::E0020,
        "-",
        &[&body("  two(a -\n    b, 1)"), &body("  two(a,\n    -b, 1)")],
    );
    check(&body("  two(a\n    - b, 1)"), Code::E0020, "-", &[&body("  two(a - b, 1)")]);
    // After a `for`, no join (S-236).
    check(&body("  for i in 0..<4 {\n  }\n  - b"), Code::E0020, "-", &[&body("  for i in 0..<4 {\n  }\n  -b")]);
}

#[test]
fn an_arm_without_its_comma_before_a_sign() {
    // S-386: a `-` / `|` / `+` at the head of a line that a `=>` follows starts
    // the next arm: E0002 at it, the `,` the one candidate (for `+`, with the
    // `+` and its blank out, S-405); `- 1` has none. The same on one line.
    let m =
        |arms: &str| format!("fn g(x: I32) -> I32 {{\n  match x {{\n    0 => {{ 1 }}{arms}\n    _ => 3,\n  }}\n}}\n");
    check(&m("\n    -1 => 2,"), Code::E0002, "-", &[&m(",\n    -1 => 2,")]);
    check(&m("\n    +1 => 2,"), Code::E0002, "+", &[&m(",\n    1 => 2,")]);
    check(&m("\n    + 1 => 2,"), Code::E0002, "+", &[&m(",\n    1 => 2,")]);
    check(&m(" -1 => 2,"), Code::E0002, "-", &[&m(", -1 => 2,")]);
    let (d, fixed) = one(&m("\n    - 1 => 2,"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    let (d, fixed) = one(&m("\n    | 1 => 2,"));
    assert_eq!((d.code, d.found.as_deref()), (Code::E0002, Some("|")));
    assert_eq!(fixed, [m(",\n    | 1 => 2,")]);
}

#[test]
fn a_prefix_plus_and_an_asymmetric_binary_plus() {
    // S-405 (a): no prefix `+`; the candidate takes it out with its blank.
    check(&body("  let c = +1\n  c"), Code::E0020, "+", &[&body("  let c = 1\n  c")]);
    check(&body("  two(+ a, 1)"), Code::E0020, "+", &[&body("  two(a, 1)")]);
    let m = |p: &str| format!("fn g(x: I32) -> I32 {{\n  match x {{\n    {p} => 1,\n    _ => 0,\n  }}\n}}\n");
    check(&m("+1"), Code::E0020, "+", &[&m("1")]);
    // (ii): the blanks on both sides, and in a list of expressions the `,`
    // with the `+` out.
    check(
        &body("  let v = [1 +1]\n  0"),
        Code::E0020,
        "+",
        &[&body("  let v = [1 + 1]\n  0"), &body("  let v = [1, 1]\n  0")],
    );
    check(&body("  let c = a +b\n  c"), Code::E0020, "+", &[&body("  let c = a + b\n  c")]);
}

#[test]
fn the_two_candidates_of_an_opener_after_a_line_break_are_those_that_read() {
    // S-419: in the arms, the `,` when a `=>` follows, else the line break out.
    let m = |arms: &str| {
        format!(
            "fn one(x: I32) -> I32 {{\n  x\n}}\nfn g(x: (I32, I32)) -> I32 {{\n  match x {{\n{arms}\n    _ => 0,\n  }}\n}}\n"
        )
    };
    check(&m("    (0, 0) => one\n    (1, 1) => 2,"), Code::E0002, "(", &[&m("    (0, 0) => one,\n    (1, 1) => 2,")]);
    check(&m("    (0, 0) => one\n    (1),"), Code::E0002, "(", &[&m("    (0, 0) => one(1),")]);
    // In a list of types only, a `[` without `;` starts no element.
    check("enum E {\n  V(Option\n    [I32]),\n}\n", Code::E0002, "[", &["enum E {\n  V(Option[I32]),\n}\n"]);
    let (_, fixed) = one("enum E {\n  V(I32\n    [I32; 2]),\n}\n");
    assert_eq!(fixed, ["enum E {\n  V(I32,\n    [I32; 2]),\n}\n"]);
    // Elsewhere both, as before (S-89).
    check(&body("  two(h\n    (a), 1)"), Code::E0002, "(", &[&body("  two(h,\n    (a), 1)"), &body("  two(h(a), 1)")]);
}

#[test]
fn the_vert_of_a_pattern_out_of_its_place() {
    let m = |arms: &str| format!("fn g(x: U32) -> U32 {{\n  match x {{\n{arms}\n    _ => 0,\n  }}\n}}\n");
    // S-383: before the first alternative, out with its blank.
    check(&m("    | 0 | 1 => 1,"), Code::E0020, "|", &[&m("    0 | 1 => 1,")]);
    check(&body("  let | (c, d) = (a, b)\n  c"), Code::E0020, "|", &[&body("  let (c, d) = (a, b)\n  c")]);
    let (d, fixed) = one(&m("    | x > 0 => 1,"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0));
    // S-389: `||` is one `|`; with no pattern after it, none.
    check(&m("    0 || 1 => 1,"), Code::E0020, "||", &[&m("    0 | 1 => 1,")]);
    let (d, fixed) = one(&m("    0 || => 1,"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0));
}

#[test]
fn a_range_symbol_at_the_head_of_a_line() {
    // S-335: in a head, moved up; `..` gives the two readings; after a
    // statement, the range outside a head (E0002).
    let f = |head: &str| format!("fn f(n: U32) {{\n  for i in 0{head} {{\n  }}\n}}\n");
    check(&f("\n    ..<n"), Code::E0020, "..<", &[&f(" ..<\n    n")]);
    check(&f("\n    ..n"), Code::E0020, "..", &[&f(" ..<\n    n"), &f(" ..=\n    n")]);
    let (d, fixed) = one("fn f(n: U32) -> U32 {\n  let r = 0\n  ..<n\n  n\n}\n");
    assert_eq!((d.code, d.found.as_deref(), fixed.len()), (Code::E0002, Some("..<"), 0));
}

// ------------------------------------------------------------ W3-06 unit 2: the break side's findings

#[test]
fn a_line_that_starts_with_an_ampersand() {
    // The break side's 1: the binary `&` at the head of a line goes on with the
    // line before (leading_operator); `&mut b`, `&*x`, `&= b` are the rows of
    // the references or the general E0002, never two rows (an internal error).
    check(&body("  let c = a\n  & b\n  c"), Code::E0020, "&", &[&body("  let c = a &\n  b\n  c")]);
    check(&body("  two(a\n    & b, 1)"), Code::E0020, "&", &[&body("  two(a &\n    b, 1)")]);
    for tail in ["&mut b", "&*b", "&= b", "& mut b"] {
        let p = parse(&body(&format!("  let c = a\n  {tail}\n  c")));
        assert!(!p.diagnostics.is_empty(), "{tail}");
        assert!(
            p.diagnostics.iter().all(|d| d.fixes.iter().all(|f| !f.title().contains("end of the line before"))),
            "{tail}: {:?}",
            p.diagnostics
        );
    }
    assert!(!codes(&body("  two(a\n    &mut b, 1)")).is_empty());
}

#[test]
fn an_arrow_or_an_equal_at_the_head_of_a_line_after_a_head_without_a_body() {
    // The break side's 3: S-374 for the members of a trait, an effect and an
    // `extern`, and a constant of a trait.
    check("trait T {\n  fn m(self)\n    -> I32\n}\n", Code::E0020, "->", &["trait T {\n  fn m(self) ->\n    I32\n}\n"]);
    check(
        "effect Ask {\n  fn ask()\n    -> I32\n}\n",
        Code::E0020,
        "->",
        &["effect Ask {\n  fn ask() ->\n    I32\n}\n"],
    );
    check("trait T {\n  const A: I32\n    = 5\n}\n", Code::E0020, "=", &["trait T {\n  const A: I32 =\n    5\n}\n"]);
    // After a body the line does not go on (S-236).
    let (d, fixed) = one("fn f() {\n}\n-> I32\n");
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    // `let _` and `= v` on the next line (the break side's 10).
    check(&body("  let _\n    = a\n  b"), Code::E0020, "=", &[&body("  let _ =\n    a\n  b")]);
}

#[test]
fn the_vert_after_a_pattern_that_is_a_name() {
    // The break side's 4: S-380 and S-389 after a name, a variant without
    // fields, a path; `||` in a `let` and a `for` too.
    let e = "enum Color {\n  Red,\n  Blue,\n}\n";
    let m = |arms: &str| format!("{e}fn g(c: Color) -> I32 {{\n  match c {{\n{arms}\n    _ => 0,\n  }}\n}}\n");
    check(
        &m("    Color.Red\n    | Color.Blue => 1,"),
        Code::E0020,
        "|",
        &[&m("    Color.Red |\n    Color.Blue => 1,")],
    );
    check(&m("    Color.Red || Color.Blue => 1,"), Code::E0020, "||", &[&m("    Color.Red | Color.Blue => 1,")]);
    let n = |arms: &str| format!("fn g(o: Option[I32]) -> I32 {{\n  match o {{\n{arms}\n    _ => 0,\n  }}\n}}\n");
    check(&n("    None\n    | Some(1) => 1,"), Code::E0020, "|", &[&n("    None |\n    Some(1) => 1,")]);
    check(&body("  let c || d = a\n  c"), Code::E0020, "||", &[&body("  let c | d = a\n  c")]);
}

#[test]
fn no_blank_or_comma_where_it_does_not_read() {
    // The break side's 7: a sign after the `}` of a `for` on its line is no
    // binary operator whatever its blanks (S-236).
    let (d, fixed) = one(&body("  for i in xs {\n  } +b\n  a"));
    assert_eq!((d.code, fixed.len()), (Code::E0002, 0), "{d:?}");
    // The break side's 8: the repetition of an array takes no `,` (S-398).
    check(&body("  let v = [a -b; 4]\n  v[0]"), Code::E0020, "-", &[&body("  let v = [a - b; 4]\n  v[0]")]);
    check(&body("  let v = [a\n    -b; 4]\n  v[0]"), Code::E0020, "-", &[&body("  let v = [a -\n    b; 4]\n  v[0]")]);
    // The break side's 9: a symbol touching another at the head of a line does not move.
    for tail in ["+= b", "=== b", "** b", "<> b", "-= b"] {
        let p = parse(&body(&format!("  let c = a\n  {tail}\n  c")));
        assert!(
            p.diagnostics.iter().all(|d| d.fixes.iter().all(|f| !f.title().contains("end of the line before"))),
            "{tail}: {:?}",
            p.diagnostics
        );
    }
}

#[test]
fn the_readings_of_a_range_symbol_at_the_head_of_a_line_are_told_apart() {
    // The break side's 13.
    let f = "fn f(n: U32) {\n  for i in 0\n    ..n {\n  }\n}\n";
    let (_, _) = one(f);
    let d = &parse(f).diagnostics[0];
    let titles: Vec<&str> = d.fixes.iter().map(|x| x.title()).collect();
    assert!(titles[0].contains("`..<`") && titles[1].contains("`..=`"), "{titles:?}");
}

#[test]
fn a_long_run_of_comment_lines_is_read_in_linear_time() {
    // The break side's 2: the line breaks are judged once per run.
    let src = format!("fn f() -> I32 {{\n  let x = 1\n{}  x\n}}\n", "  // c\n".repeat(20000));
    let start = std::time::Instant::now();
    assert!(codes(&src).is_empty());
    assert!(start.elapsed() < std::time::Duration::from_secs(5), "{:?}", start.elapsed());
}

#[test]
fn a_line_break_after_a_prefix_plus() {
    // S-425: the `+` and the blanks after it, the line break too, go; a
    // comment of the `+`'s line stays on it, after the operand's code (S-216).
    check(&body("  let y = +\n    a\n  y"), Code::E0020, "+", &[&body("  let y = a\n  y")]);
    check(&body("  two(+\n    a, 1)"), Code::E0020, "+", &[&body("  two(a, 1)")]);
    check(&body("  two(+ // c\n    a, 1)"), Code::E0020, "+", &[&body("  two(a, 1) // c")]);
    let m = |p: &str| format!("fn g(x: I32) -> I32 {{\n  match x {{\n    {p} => 1,\n    _ => 0,\n  }}\n}}\n");
    check(&m("+\n    1"), Code::E0020, "+", &[&m("1")]);
}

#[test]
fn the_line_facts_of_each_token() {
    // The gaps around each token the parser reads, the tokens at the head of
    // a line and the line breaks that go on (§2.5), found once (D-13).
    let src = "a +\n  // c\n\n  b\n.c ? d\n-e";
    let all = crate::lex(FileId(0), src).tokens;
    let (tokens, full, lines) = crate::layout::code_tokens(&all);
    // The gaps are those that `gap_before` reads in the full list.
    for (k, &i) in full.iter().enumerate() {
        assert_eq!(lines.before(k), crate::token::gap_before(&all, i as usize), "{k}");
    }
    let text = |i: usize| &src[tokens[i].span.start as usize..tokens[i].span.end as usize];
    let at = |s: &str| (0..tokens.len()).find(|&i| text(i) == s).unwrap();
    use Gap::*;
    assert_eq!((lines.before(at("+")), lines.after(at("+"))), (Space, Newline));
    assert_eq!((lines.before(at("b")), lines.after(at("b"))), (Newline, Newline));
    assert_eq!((lines.before(at("?")), lines.after(at("?"))), (Space, Space));
    assert!(lines.at_line_head(at("b")) && lines.at_line_head(at(".")) && lines.at_line_head(at("-")));
    assert!(!lines.at_line_head(at("+")) && !lines.at_line_head(at("c")));
    // The line breaks after `+` (and over the comment and the blank line) go
    // on; the one before `.` goes on; the one before `-` does not.
    let newlines: Vec<bool> =
        (0..tokens.len()).filter(|&i| tokens[i].kind == TokenKind::Newline).map(|i| lines.goes_on(i)).collect();
    assert_eq!(newlines, vec![true, true, true, true, false]);
    assert_eq!(lines.after(tokens.len() - 1), None);
}

#[test]
fn the_gaps_are_those_of_gap_before() {
    // One rule of the gaps (`Gap::then`): the line facts keep what
    // `token::gap_before` reads in the full list, with CRLF, tabs, block
    // comments, blanks before a newline and blanks at the start.
    for src in [
        "a\r\n  b",
        "\t a\t+\tb",
        "a /* c */ + /* d */b",
        "/* c */a",
        "  a  \n\n \t b\r\n",
        "a // c\r\n  b",
        "",
        "\n\n",
    ] {
        let all = crate::lex(FileId(0), src).tokens;
        let (_, full, lines) = crate::layout::code_tokens(&all);
        for (k, &i) in full.iter().enumerate() {
            assert_eq!(lines.before(k), crate::token::gap_before(&all, i as usize), "{src:?} {k}");
        }
    }
}

#[test]
fn a_line_goes_on_across_a_block_comment() {
    // A comment is passed over where the code of a line is looked for
    // (`TokenKind::is_comment`, §2.5): a line that ends in an operator and a
    // block comment goes on, as one that ends in a line comment does.
    for src in ["a |\n/* c */\n  b", "a | /* c */\n  b", "a |\n  /* c */ b"] {
        let all = crate::lex(FileId(0), src).tokens;
        let (tokens, _, lines) = crate::layout::code_tokens(&all);
        let newlines: Vec<bool> =
            (0..tokens.len()).filter(|&i| tokens[i].kind == TokenKind::Newline).map(|i| lines.goes_on(i)).collect();
        assert!(newlines.iter().all(|&g| g), "{src:?}: {newlines:?}");
    }
}
