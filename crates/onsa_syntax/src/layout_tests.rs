//! Tests of the lines and blanks of §2.5 ([`crate::layout`] and the rows of
//! `foreign/spaces.rs`): the postfix openers kept apart from the token before
//! them (S-89, S-123, S-399), the missing `,` of a list (S-384, S-387, S-388,
//! S-373) and the literals with a prefix (S-400). Every candidate is applied
//! and the result is parsed again: the syntax stage reports nothing (S-236).

use onsa_diag::{Code, Diagnostic, FileId};

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
