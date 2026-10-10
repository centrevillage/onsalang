//! Tests of the table of the forms of other languages ([`crate::foreign`]):
//! each form is found where the parser fails, with its code, and its first
//! candidate gives the Onsa form. The examples of the data file
//! `docs/foreign-forms.toml`, which run through the same entry as the cases
//! and check every candidate against the contract of §18.1, are the tests of
//! `onsa_tests` (D-15); these are the unit tests of the matchers.

use onsa_diag::{Code, FileId};

use crate::foreign::{ROWS, RowId};

fn parse(src: &str) -> crate::Parsed {
    crate::parse(FileId(0), src)
}

fn codes(src: &str) -> Vec<Code> {
    parse(src).diagnostics.iter().map(|d| d.code).collect()
}

/// `src` after candidate `k` (from 0) of its first diagnostic.
fn fixed_by(src: &str, k: usize) -> String {
    let p = parse(src);
    let d = p.diagnostics.first().unwrap_or_else(|| panic!("no diagnostic: {src}"));
    let fix = d.fixes.get(k).unwrap_or_else(|| panic!("no candidate {k}: {d:?}"));
    onsa_diag::apply_text(src, &fix.edits().iter().collect::<Vec<_>>()).unwrap()
}

fn fixed(src: &str) -> String {
    fixed_by(src, 0)
}

/// One E0020 whose first candidate gives `want`, after which the parse
/// reports nothing.
#[track_caller]
fn e0020(src: &str, want: &str) {
    assert_eq!(codes(src), [Code::E0020], "{src}: {:?}", parse(src).diagnostics);
    let got = fixed(src);
    assert_eq!(got, want, "{src}");
    let after = parse(&got);
    assert!(after.diagnostics.is_empty(), "{src}\nafter the candidate:\n{got}\n{:?}", after.diagnostics);
}

/// One E0002 with the note of the row and no candidate.
#[track_caller]
fn e0002(src: &str) {
    let p = parse(src);
    assert_eq!(codes(src), [Code::E0002], "{src}: {:?}", p.diagnostics);
    let d = &p.diagnostics[0];
    assert!(d.fixes.is_empty() && d.notes.iter().any(|n| n.span.is_none()), "{src}: {d:?}");
}

fn body(stmts: &str) -> String {
    format!("fn f() {{\n{stmts}\n}}\n")
}

#[test]
fn the_rows_have_distinct_names_and_codes_of_their_kind() {
    for (i, r) in ROWS.iter().enumerate() {
        assert!(ROWS[..i].iter().all(|o| o.id != r.id && o.name != r.name), "{} twice", r.name);
        assert!(r.name.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_'), "{}", r.name);
        assert!(matches!(r.code, Code::E0020 | Code::E0002), "{}", r.name);
        assert!(r.rule.contains('§'), "{}: the rule names its section", r.name);
    }
    assert_eq!(crate::foreign::row(RowId::Semicolon).name, "semicolon");
}

#[test]
fn semicolons() {
    e0020(&body("  let x = 1;"), &body("  let x = 1"));
    // `;;` is one form (S-248).
    e0020(&body("  let x = 1;;"), &body("  let x = 1"));
    // Code after it on its line goes to a line of its own (S-236).
    e0020(&body("  let a = 1; let b = 2"), &body("  let a = 1\n  let b = 2"));
    e0020(&body("  if a { return 1; }"), &body("  if a { return 1 }"));
    e0020(&body("  return;"), &body("  return"));
    e0020(&body("  let x = 1; // c"), &body("  let x = 1 // c"));
    e0020("const A: I32 = 1;\n", "const A: I32 = 1\n");
    e0020("fn f() { };\n", "fn f() { }\n");
    e0020(";\nfn f() { }\n", "\nfn f() { }\n");
    e0020("impl A {\n  fn f(self) { };\n}\n", "impl A {\n  fn f(self) { }\n}\n");
    // In a list separated with `,` (S-250).
    e0020("struct P { x: I32; y: I32 }\n", "struct P { x: I32, y: I32 }\n");
    e0020("struct P {\n  x: I32;\n}\n", "struct P {\n  x: I32\n}\n");
    e0020(&body("  g(a; b)"), &body("  g(a, b)"));
    // No element before it: the general E0002.
    assert_eq!(codes("pub fn t(;\n"), [Code::E0002]);
    assert_eq!(codes(&body("  g(a, ; b)")), [Code::E0002]);
    // Not the end of a statement: the general E0002.
    assert_eq!(codes(&body("  let x = ;")), [Code::E0002]);
    // Each statement's `;` is an error of its own; the unit stops at the first (R-87 (4)).
    assert_eq!(codes(&body("  let a = 1;\n  let b = 2;")), [Code::E0020]);
    // A node that has read nothing is not yet a list (`pub struct Marker;`,
    // `while c; {`): the general E0002.
    for src in ["pub struct Marker;\n", "pub enum E;\n", "pub trait T;\n", "impl S;\n"] {
        let p = parse(src);
        assert_eq!(codes(src), [Code::E0002], "{src}");
        assert!(p.diagnostics[0].notes.is_empty(), "{src}: {:?}", p.diagnostics);
    }
    assert_eq!(codes(&body("  while x < 3; { }")), [Code::E0002]);
    assert_eq!(codes("pub fn f(x: I32) -> I32; { x }\n"), [Code::E0002]);
}

#[test]
fn paths() {
    e0020(&body("  F32::PI"), &body("  F32.PI"));
    // One path is one form: every `::` (S-248).
    e0020(&body("  std::math::sqrt(2.0)"), &body("  std.math.sqrt(2.0)"));
    e0020(&body("  a.b::c::d"), &body("  a.b.c.d"));
    e0020("fn f(p: std::fs::Path) { }\n", "fn f(p: std.fs.Path) { }\n");
    e0020("use std::math::{sin, cos}\n", "use std.math.{sin, cos}\n");
    e0020(
        "fn f(s: Shape) -> I32 {\n  match s {\n    Shape::Circle(r) => 1,\n    _ => 0,\n  }\n}\n",
        "fn f(s: Shape) -> I32 {\n  match s {\n    Shape.Circle(r) => 1,\n    _ => 0,\n  }\n}\n",
    );
    // `::<` is a form of the type arguments (S-239), not a separator.
    e0020(&body("  parse::<I32>(s)"), &body("  parse::[I32](s)"));
}

#[test]
fn type_args_in_an_expression() {
    // The path goes on across `::[…]`, whose `::` is no separator (S-248, S-239).
    e0020(&body("  m::Buf::[F32]::zeroed(4)"), &body("  m.Buf::[F32].zeroed(4)"));
    e0020(&body("  Buf::[F32]::zeroed(4)"), &body("  Buf::[F32].zeroed(4)"));
    // A path with `::<…>` in it is two forms, fixed one after the other: the
    // list first (in the order of the text), then the separator after it (S-326).
    let first = fixed(&body("  Buf::<F32>::zeroed(4)"));
    assert_eq!(first, body("  Buf::[F32]::zeroed(4)"));
    assert_eq!(codes(&first), [Code::E0020]);
    assert_eq!(fixed(&first), body("  Buf::[F32].zeroed(4)"));
    // The path before a `::<` is one form, and the list another (S-326).
    assert_eq!(fixed(&body("  std::conv::parse::<I32>(s)")), body("  std.conv.parse::<I32>(s)"));
    // Turbofish: the nested brackets, the `>>` one edit (S-248).
    e0020(&body("  id::<Option<U8>>(None)"), &body("  id::[Option[U8]](None)"));
    e0020(&body("  t.0::<U8>(1)"), &body("  t.0::[U8](1)"));
    // After an expression that is no path: the call of the value (`.(` is W3-20's).
    assert_eq!(fixed(&body("  (s.f)::<U8>(1)")), body("  s.f.(1)"));
    assert_eq!(fixed(&body("  g(x)::<U8>(1)")), body("  g(x).(1)"));
    assert_eq!(fixed(&body("  (a + b)<U8>(1)")), body("  (a + b).(1)"));
    // Angle brackets: read as a chain without a `,`, a failure at the `,` with one.
    assert_eq!(fixed_by(&body("  id<U8>(250)"), 1), body("  id < U8 && U8 > (250)"));
    e0020(&body("  id<Option<U8>>(None)"), &body("  id::[Option[U8]](None)"));
    assert_eq!(parse(&body("  id<Option<U8>>(None)")).diagnostics[0].fixes.len(), 1);
    e0020(&body("  pair<Option<U8>, F32>(x, y)"), &body("  pair::[Option[U8], F32](x, y)"));
    // A chain written with spaces, or not before a call, stays a chain (§3.1).
    assert_eq!(codes(&body("  a < b > (c)")), [Code::E0010]);
    assert_eq!(codes(&body("  a<b>c")), [Code::E0010]);
    // A `[…]` with a `,` is no index.
    e0020(&body("  s.pair[U8, F32](1, 2.0)"), &body("  s.pair::[U8, F32](1, 2.0)"));
    assert_eq!(codes(&body("  g(x)[U8, F32]")), [Code::E0002]);
    // Not for a list that no `]` closes, or with nothing before the `,`
    // (tests/fuzz/fbdbd5d8.onsa); a bracket that closes no bracket of the
    // element ends it (tests/fuzz/b2ecacdc.onsa).
    assert_eq!(codes("fn o(v: V) {\n  v[,\n}\n"), [Code::E0002]);
    assert_eq!(codes(&body("  pair[U8, F32\n")), [Code::E0002]);
    assert_eq!(codes("struct H { f: f[(] }\n"), [Code::E0002]);
    // The type position, also inside a list of an expression.
    e0020("fn f(b: Buf::[F32]) { }\n", "fn f(b: Buf[F32]) { }\n");
    e0020("fn f(b: Buf:: [F32]) { }\n", "fn f(b: Buf[F32]) { }\n");
    e0020(&body("  id::[Option::[U8]](None)"), &body("  id::[Option[U8]](None)"));
    // Spaces around the `::` of an expression; a newline is no space here.
    e0020(&body("  id :: [U8](1)"), &body("  id::[U8](1)"));
    assert_eq!(codes(&body("  let a = id\n  ::[U8](1)")), [Code::E0002]);
    // Where `::[` cannot be read: E0002 with no candidate.
    for src in ["  (id)::[U8](1)", "  id::[U8]::[U8](1)", "  id::[](1)", "  1::[U8]"] {
        let p = parse(&body(src));
        assert_eq!(codes(&body(src)), [Code::E0002], "{src}");
        assert!(p.diagnostics[0].fixes.is_empty(), "{src}");
    }
    // The elements of a list are types and constant expressions (§4.5, R-192).
    for src in ["fn f(r: Rg[F32, 2 * N * 3, N - 1]) { }\n", "fn f(r: Rg[F32, (1 + 2) * 3, -(1), size(3)]) { }\n"] {
        assert!(codes(src).is_empty(), "{src}");
    }
    assert_eq!(codes("fn f(r: Rg[]) { }\n"), [Code::E0002]);
}

/// W3-19/b: the forms of a call's type arguments are found from the tokens
/// before the `<` or `[` is read, whatever follows the call.
#[test]
fn type_args_before_a_call_whatever_follows() {
    for (src, want) in [
        ("  f<I32>(s).unwrap()", "  f::[I32](s).unwrap()"),
        ("  f<I32>(s)?", "  f::[I32](s)?"),
        ("  f<I32>(s) as F32", "  f::[I32](s) as F32"),
        ("  f<I32>(s)[0]", "  f::[I32](s)[0]"),
        ("  f<I32>(s) + 1", "  f::[I32](s) + 1"),
        ("  2 * f<I32>(s)", "  2 * f::[I32](s)"),
        ("  f<A<B<C>>>(x)", "  f::[A[B[C]]](x)"),
        ("  show(pair<U8, F32>(1, 2.0))", "  show(pair::[U8, F32](1, 2.0))"),
        ("  t.0<U8>(1)", "  t.0::[U8](1)"),
    ] {
        e0020(&body(src), &body(want));
    }
    // A value before the list: the call with `.(`, the blanks before the list
    // too (`.(` is read from W3-20).
    for (src, want) in [
        ("  (s.f)<T, U>(x)", "  s.f.(x)"),
        ("  g(x)<T, U>(y)", "  g(x).(y)"),
        ("  (e)[T, U](x)", "  e.(x)"),
        ("  (e) ::<T>(x)", "  e.(x)"),
    ] {
        assert_eq!(codes(&body(src)), [Code::E0020], "{src}");
        assert_eq!(fixed(&body(src)), body(want), "{src}");
    }
    // No candidate: a literal before the list, an empty list, a list after an
    // index of a value with no call, `_` in a list, a type position list that
    // is empty or followed by what no type is.
    // `d<->>(x)` and `d<U->8>(x)`: tests/fuzz/1a0a32db.onsa, 807eade3.onsa.
    for src in [
        "  1::<T>(x)",
        "  f::<>(x)",
        "  a[i][j, k]",
        "  a[i, _]",
        "  pair::[U8, _](1, 2)",
        "  d<->>(x)",
        "  f<A,>(x)",
        "  d<U->8>(x)",
    ] {
        let p = parse(&body(src));
        assert!(p.diagnostics.iter().all(|d| d.fixes.is_empty()), "{src}: {:?}", p.diagnostics);
    }
    for src in ["fn g(x: Buf::[]) { }\n", "fn g(x: Buf::[F32].Inner) { }\n"] {
        assert!(parse(src).diagnostics.iter().all(|d| d.fixes.is_empty()), "{src}");
    }
    // The elements of a list that are no type read as expressions (the later
    // stages check the constant): `(N)`, `1.5`, `"s"`, `if`.
    for src in [
        "  Rg::[F32, (N)].CAP",
        "  f::[(K)](x)",
        "  Rg::[F32, 1.5].CAP",
        "  Rg::[F32, \"s\"].CAP",
        "  Rg::[F32, if c { 1 } else { 2 }].CAP",
    ] {
        assert!(codes(&body(src)).is_empty(), "{src}");
    }
    // A chain written with spaces stays a chain (§3.1).
    assert_eq!(codes(&body("  a < b > (c)")), [Code::E0010]);
}

#[test]
fn angle_brackets() {
    e0020("fn f(x: Vec<T>) { }\n", "fn f(x: Vec[T]) { }\n");
    e0020("fn f<T>(x: T) { }\n", "fn f[T](x: T) { }\n");
    e0020("fn f<T: Eq, U>(x: T) { }\n", "fn f[T: Eq, U](x: T) { }\n");
    e0020("struct S<T> { x: T }\n", "struct S[T] { x: T }\n");
    e0020("impl<T> S[T] { }\n", "impl[T] S[T] { }\n");
    // Nested: one form, `>>` is `]]` (S-248).
    e0020("fn f(x: Option<Option<I32>>) { }\n", "fn f(x: Option[Option[I32]]) { }\n");
    e0020("fn f(x: Result<Option<I32>, Str>) { }\n", "fn f(x: Result[Option[I32], Str]) { }\n");
    e0020(&body("  let x: Vec<I32> = v"), &body("  let x: Vec[I32] = v"));
    // The candidate edits the brackets only (S-251).
    let p = parse("fn f(x: Vec< // c\n  T>) { }\n");
    assert_eq!(p.diagnostics[0].code, Code::E0020);
    let edits: Vec<&str> = p.diagnostics[0].fixes[0].edits().iter().map(|e| e.replace.as_str()).collect();
    assert_eq!(edits, ["[", "]"]);
    // Not closed: no list of type arguments, the general E0002 (no note).
    let p = parse("fn f(x: Vec<T) { }\n");
    assert_eq!(codes("fn f(x: Vec<T) { }\n"), [Code::E0002]);
    assert!(p.diagnostics[0].notes.is_empty(), "{:?}", p.diagnostics);
    assert_eq!(codes("fn f() -> I32 < 3 { 1 }\n"), [Code::E0002]);
}

#[test]
fn references_and_mut() {
    e0020("fn f(v: &mut I32) { }\n", "fn f(inout v: I32) { }\n");
    e0020("fn f(a: I32, v: &mut [I32; 4]) { }\n", "fn f(a: I32, inout v: [I32; 4]) { }\n");
    e0020("fn f(v: &I32) { }\n", "fn f(v: I32) { }\n");
    e0020("impl A {\n  fn f(&mut self) { }\n}\n", "impl A {\n  fn f(inout self) { }\n}\n");
    e0020("impl A {\n  fn f(&self) { }\n}\n", "impl A {\n  fn f(self) { }\n}\n");
    // Modes are not written twice (`inout &mut self`, `move mut self`).
    e0020("impl A {\n  fn f(inout &mut self) { }\n}\n", "impl A {\n  fn f(inout self) { }\n}\n");
    e0020("impl A {\n  fn f(inout mut self) { }\n}\n", "impl A {\n  fn f(inout self) { }\n}\n");
    e0020("impl A {\n  fn f(move mut self) { }\n}\n", "impl A {\n  fn f(move self) { }\n}\n");
    e0020("impl A {\n  fn f(move &mut self) { }\n}\n", "impl A {\n  fn f(inout self) { }\n}\n");
    assert_eq!(fixed_by("impl A {\n  fn f(move &mut self) { }\n}\n", 1), "impl A {\n  fn f(move self) { }\n}\n");
    e0020(&body("  g(inout &mut x)"), &body("  g(inout x)"));
    e0020("fn f(g: fn(move &mut I32)) { }\n", "fn f(g: fn(inout I32)) { }\n");
    // A `&` after a name is no receiver (`x&self`): the general E0002.
    assert_eq!(codes("fn f(x&self: I32) { }\n"), [Code::E0002]);
    e0020("impl A {\n  fn f(mut self) { }\n}\n", "impl A {\n  fn f(move self) { }\n}\n");
    e0020(&body("  g(&mut x)"), &body("  g(inout x)"));
    e0020(&body("  g(a, &mut s.x)"), &body("  g(a, inout s.x)"));
    e0020(&body("  g(&x)"), &body("  g(x)"));
    assert_eq!(fixed_by(&body("  g(&x)"), 1), body("  g(inout x)"));
    e0020(&body("  let y = &x"), &body("  let y = x"));
    e0020(&body("  let mut x = 1"), &body("  var x = 1"));
    e0020(&body("  let mut x: I32 = 1"), &body("  var x: I32 = 1"));
    // `&mut` outside a parameter has no Onsa form (R-173).
    e0002(&body("  let x: &mut I32 = y"));
    e0002("struct S { x: &mut I32 }\n");
    e0002("fn f() -> &mut I32 { x }\n");
    e0002(&body("  let y = &mut x"));
}

#[test]
fn keywords_and_marks() {
    e0020(&body("  loop {\n    break\n  }"), &body("  while true {\n    break\n  }"));
    e0020("proc f(x: Sig[F32]) -> Sig[F32] { x }\n", "flow f(x: Sig[F32]) -> Sig[F32] { x }\n");
    e0020("#[inline]\nfn f() { }\n", "@inline\nfn f() { }\n");
    // `#[derive(..)]`: the traits at the head (the syntax of `: Eq` is W3-08's).
    assert_eq!(codes("#[derive(Eq, Ord)]\npub struct S { }\n"), [Code::E0020]);
    assert_eq!(fixed("#[derive(Eq, Ord)]\npub struct S { }\n"), "pub struct S: Eq + Ord { }\n");
    // A generic declaration: after its `]` (§6.4).
    assert_eq!(fixed("#[derive(Show)]\npub struct S[T] { a: T }\n"), "pub struct S[T]: Show { a: T }\n");
    // Where no attribute goes (a field, a variant, a statement): no candidate.
    for src in [
        "struct S {\n  #[allow(x)]\n  a: I32,\n}\n",
        "enum E {\n  #[default]\n  A,\n}\n",
        "fn f() {\n  #[allow(x)]\n  let a = 1\n}\n",
    ] {
        let p = parse(src);
        assert_eq!(codes(src), [Code::E0002], "{src}");
        assert!(p.diagnostics[0].fixes.is_empty() && !p.diagnostics[0].notes.is_empty(), "{src}");
    }
    // An input of a flow takes one.
    let src = "flow g(#[param(min: 0.0)] x: Sig[F32]) -> Sig[F32] { x }\n";
    assert_eq!(codes(src), [Code::E0020]);
    e0020("pub(crate) fn f() { }\n", "fn f() { }\n");
    e0020("fn f(x: i32) -> I32 { x }\n", "fn f(x: I32) -> I32 { x }\n");
    e0020("fn f(x: usize) { }\n", "fn f(x: U32) { }\n");
    e0020("fn f(c: char, s: Str) { }\n", "fn f(c: Char, s: Str) { }\n");
    // `String` and `i128` are names that are not declared (E0302), not forms of the table.
    assert!(codes("fn f(x: String, y: i128) { }\n").is_empty());
    e0020(&body("  let n = ~m"), &body("  let n = !m"));
    // Before another prefix operator, the operand in parentheses (no stack, §3.1).
    e0020(&body("  let n = ~-m"), &body("  let n = !(-m)"));
    e0020(&body("  let n = ~!m.f(1)"), &body("  let n = !(!m.f(1))"));
    // After one, or before `~` or `--`: no candidate.
    assert_eq!(codes(&body("  let n = -~m")), [Code::E0002]);
    assert_eq!(codes(&body("  let n = ~~m")), [Code::E0002]);
    // A flow is not a member: the general E0002.
    assert_eq!(codes("impl A {\n  proc g(x: Sig[F32]) -> Sig[F32] { x }\n}\n"), [Code::E0002]);
}

#[test]
fn literals() {
    e0020(&body("  let a = 1."), &body("  let a = 1.0"));
    e0020(&body("  let a = .5"), &body("  let a = 0.5"));
    e0020(&body("  let a = 1u8"), &body("  let a = 1"));
    e0020(&body("  let a = 1.5f32"), &body("  let a = 1.5"));
    // The suffix goes where the number reads the same (`0u32..n`, `1u8.abs()`).
    e0020(&body("  for i in 0u32..<n { }"), &body("  for i in 0..<n { }"));
    e0020(&body("  let a = 1u8.abs()"), &body("  let a = 1.abs()"));
    e0020(&body("  let a = 1.0f32.abs()"), &body("  let a = 1.0.abs()"));
    // Not where it would read with the `.` (`1d.5`, `1d.`).
    assert!(parse(&body("  let a = 1d.5")).diagnostics[0].fixes.is_empty());
    assert!(parse(&body("  let a = 1d.")).diagnostics[0].fixes.is_empty());
    // A number too large with a suffix: its E0408 too (one token, two errors).
    let big = parse(&body("  let a = 66920938463463374607u8"));
    assert_eq!(big.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), [Code::E0408, Code::E0020]);
    // Where no literal goes, the place is an error too (S-281): both are reported.
    assert_eq!(codes("1.\n"), [Code::E0020, Code::E0002]);
}

#[test]
fn block_comments() {
    // Ending its line: in place.
    e0020(&body("  let a = 1 /* one */"), &body("  let a = 1 // one"));
    e0020(&body("  /* one */"), &body("  // one"));
    // Code after it: the words go above the line, the code stays (S-247).
    e0020(&body("  1 /* one */ + 2"), &body("  // one\n  1 + 2"));
    e0020(&body("  1 /* one */+ 2"), &body("  // one\n  1 + 2"));
    e0020(&body("  1/* one */+2"), &body("  // one\n  1 +2"));
    e0020("/* c */ pub fn f() { }\n", "// c\npub fn f() { }\n");
    // Over lines.
    e0020(&body("  /* a\n     b */"), &body("  // a\n  // b"));
    e0020(&body("  let a = 1 /* x\n  y */"), &body("  let a = 1 // x\n  // y"));
    // Over lines with code after it: no candidate keeps the line breaks (S-302).
    e0002(&body("  let a = 1 /* x\n  y */ + 2"));
    // In the middle of a line, `/** */` is `//` (a `///` above would document another declaration).
    e0020("fn f(/** d */ x: I32) { }\n", "// d\nfn f( x: I32) { }\n");
    // Doc comments: `///` before a declaration, `//!` at the head of the file.
    e0020("/** Doc. */\nfn f() { }\n", "/// Doc.\nfn f() { }\n");
    e0020("/**\n * Doc.\n */\nfn f() { }\n", "/// * Doc.\nfn f() { }\n");
    e0020(&body("  /** not a doc */"), &body("  // not a doc"));
    // `///` before a field, a variant, an input of a flow (§2.1).
    e0020("struct S {\n  /** d */\n  a: I32,\n}\n", "struct S {\n  /// d\n  a: I32,\n}\n");
    e0020("enum E {\n  /** d */\n  A,\n}\n", "enum E {\n  /// d\n  A,\n}\n");
    // `//` before `use` and `test`, past `pub` and attributes (their `///` is E0004).
    e0020("/** d */\npub use std.math\n", "// d\npub use std.math\n");
    e0020("/** d */\n@x\nuse std.math\n", "// d\n@x\nuse std.math\n");
    e0020("/** d */\n@fp(relaxed)\npub fn f() { }\n", "/// d\n@fp(relaxed)\npub fn f() { }\n");
    e0020("/*! Module. */\nfn f() { }\n", "//! Module.\nfn f() { }\n");
    assert_eq!(fixed_by("/*! Module. */\nfn f() { }\n", 1), "/// Module.\nfn f() { }\n");
    // Never closed, and nested: E0002 with the note.
    e0002(&body("  /* open"));
    e0002(&body("  /* a /* b */ c */"));
    // Several on one line: one by one, each adds its line above, and the code is fixed.
    let mut src = body("  let a = /* one */ 1 /* two */ + /* three */ 2");
    for _ in 0..3 {
        assert_eq!(codes(&src), [Code::E0020], "{src}");
        src = fixed(&src);
    }
    assert_eq!(src, body("  // one\n  // two\n  // three\n  let a = 1 + 2"));
    assert!(codes(&src).is_empty());
    // The unit with the comment fails (R-87 (4)).
    assert_eq!(codes("fn f() -> I32 {\n  1 /* c */\n}\nfn g() -> I32 { 2 }\n"), [Code::E0020]);
}

#[test]
fn float_patterns() {
    let m = |arms: &str| format!("fn f(x: F32) -> I32 {{\n  match x {{\n{arms}\n  }}\n}}\n");
    e0020(&m("    1.0 => 1,\n    _ => 0,"), &m("    v if v == 1.0 => 1,\n    _ => 0,"));
    e0020(&m("    -1.5 => 1,\n    _ => 0,"), &m("    v if v == -1.5 => 1,\n    _ => 0,"));
    // A float written as in other languages in a pattern: one form, in its Onsa spelling.
    e0020(&m("    1. => 1,\n    _ => 0,"), &m("    v if v == 1.0 => 1,\n    _ => 0,"));
    e0020(&m("    0.5f32 => 1,\n    _ => 0,"), &m("    v if v == 0.5 => 1,\n    _ => 0,"));
    e0020(&m("    .5 => 1,\n    _ => 0,"), &m("    v if v == 0.5 => 1,\n    _ => 0,"));
    // All the float literals of one pattern are one form (S-248, S-317): the
    // alternatives of one skeleton merge, their conditions joined with `||`.
    e0020(&m("    1.0 | 2.0 => 1,\n    _ => 0,"), &m("    v if v == 1.0 || v == 2.0 => 1,\n    _ => 0,"));
    // Removing the other alternatives would remove a comment (S-251): none.
    e0002(&m("    1.0 // one\n    | 2.0 => 1,\n    _ => 0,"));
    e0020(&m("    1.0 if g => 1,\n    _ => 0,"), &m("    v if v == 1.0 && g => 1,\n    _ => 0,"));
    let t = |arms: &str| format!("fn f(x: (F32, F32)) -> I32 {{\n  match x {{\n{arms}\n  }}\n}}\n");
    e0020(&t("    (1.0, 2.0) => 1,\n    _ => 0,"), &t("    (v, v2) if v == 1.0 && v2 == 2.0 => 1,\n    _ => 0,"));
    e0020(
        &t("    (0.5, 1.5) | (1.5, 0.5) => 1,\n    _ => 0,"),
        &t("    (v, v2) if (v == 0.5 && v2 == 1.5) || (v == 1.5 && v2 == 0.5) => 1,\n    _ => 0,"),
    );
    // The alternatives differ outside the holes: no candidate (S-317).
    e0002(&t("    (0.5, 1) | (1.5, 2) => 1,\n    _ => 0,"));
    // An `||` inside an `&&` in parentheses.
    e0020(
        &t("    (0.5 | 1.5, 0.7) => 1,\n    _ => 0,"),
        &t("    (v, v2) if (v == 0.5 || v == 1.5) && v2 == 0.7 => 1,\n    _ => 0,"),
    );
    e0020(
        &t("    (0.5 | 1.5, 0.7 | 1.7) => 1,\n    _ => 0,"),
        &t("    (v, v2) if (v == 0.5 || v == 1.5) && (v2 == 0.7 || v2 == 1.7) => 1,\n    _ => 0,"),
    );
    e0020(&t("    (1.0, n) => n,\n    _ => 0,"), &t("    (v, n) if v == 1.0 => n,\n    _ => 0,"));
    // A new name no other name of the file has (S-253).
    let s = |arms: &str| format!("fn f(v: Option[F32]) -> I32 {{\n  match v {{\n{arms}\n  }}\n}}\n");
    e0020(&s("    Some(1.0) => 1,\n    _ => 0,"), &s("    Some(v2) if v2 == 1.0 => 1,\n    _ => 0,"));
    // A name in the hole of a string literal is a name of the file too (S-319):
    // a misspelt `{v}` stays unresolved, not caught by the new binding.
    let h = |arms: &str| format!("fn f(x: F32) -> Str {{\n  match x {{\n{arms}\n  }}\n}}\n");
    e0020(&h("    1.0 => \"a{v}\",\n    _ => \"b\","), &h("    v2 if v2 == 1.0 => \"a{v}\",\n    _ => \"b\","));
    e0020(
        &s("    Some(0.5) | Some(1.5) => 1,\n    _ => 0,"),
        &s("    Some(v2) if v2 == 0.5 || v2 == 1.5 => 1,\n    _ => 0,"),
    );
    e0020(
        &s("    Some(0.5 | 1.5) => 1,\n    _ => 0,"),
        &s("    Some(v2) if v2 == 0.5 || v2 == 1.5 => 1,\n    _ => 0,"),
    );
    // Nested alternatives, merged where they are, then the outer ones.
    let u = |arms: &str| format!("fn f(x: (F32, I32)) -> I32 {{\n  match x {{\n{arms}\n  }}\n}}\n");
    e0020(
        &u("    (0.5 | 1.5, 1) | (2.5, 1) => 1,\n    _ => 0,"),
        &u("    (v, 1) if v == 0.5 || v == 1.5 || v == 2.5 => 1,\n    _ => 0,"),
    );
    // The name cannot be bound in every alternative, and `let`: E0002 (§7).
    e0002(&s("    Some(1.0) | None => 1,\n    _ => 0,"));
    e0002(&s("    Some(0.5) | Some(x) => 1,\n    _ => 0,"));
    e0002(&body("  let 1.0 = x"));
}

#[test]
fn compound_assignments_and_increments() {
    e0020(&body("  x += 1"), &body("  x = x + 1"));
    e0020(&body("  self.n -= 2"), &body("  self.n = self.n - 2"));
    e0020(&body("  x *= a + b"), &body("  x = x * (a + b)"));
    e0020(&body("  x <<= 1"), &body("  x = x << 1"));
    e0020(&body("  x++"), &body("  x = x + 1"));
    e0020(&body("  x--"), &body("  x = x - 1"));
    // A `;` after it is an error of its own, reported next; a comment stays.
    assert_eq!(fixed(&body("  x++;")), body("  x = x + 1;"));
    e0020(&body("  x-- // c"), &body("  x = x - 1 // c"));
    assert_eq!(fixed(&body("  x-- /* c */")), body("  x = x - 1 /* c */"));
    e0020(&body("  ++x"), &body("  x = x + 1"));
    e0020(&body("  --s.x"), &body("  s.x = s.x - 1"));
    // Read twice, or an expression: E0002 (S-250).
    e0002(&body("  a[i] += 1"));
    e0002(&body("  let y = x += 1"));
    e0002(&body("  let y = x++"));
    e0002(&body("  g(--x)"));
    // `---x` is `--` and `-x` (S-297); `- - x` stays E0012.
    e0002(&body("  ---x"));
    assert_eq!(codes(&body("  let y = - - x")), [Code::E0012]);
}

/// The code of a Rust source without its comments and its test modules: a
/// `#[cfg(test)]` drops the item after it, to the `;` or the `}` that closes
/// its first `{` (the braces in strings, chars and comments not counted).
fn code_without_tests(text: &str) -> String {
    let b = text.as_bytes();
    let (mut out, mut i, mut skip, mut depth) = (String::new(), 0, false, 0i32);
    while i < b.len() {
        let rest = &text[i..];
        // Comments: dropped.
        if rest.starts_with("//") {
            i += rest.find('\n').unwrap_or(rest.len());
            continue;
        }
        if rest.starts_with("/*") {
            i += rest.find("*/").map_or(rest.len(), |k| k + 2);
            continue;
        }
        if !skip && rest.starts_with("#[cfg(test)]") {
            (skip, depth) = (true, 0);
            i += "#[cfg(test)]".len();
            continue;
        }
        // Strings (raw ones too) and chars: one piece.
        let len = if rest.starts_with("r#") || rest.starts_with("r\"") {
            let hashes = rest[1..].bytes().take_while(|&c| c == b'#').count();
            let close = format!("\"{}", "#".repeat(hashes));
            2 + hashes + rest[2 + hashes..].find(&close).map_or(rest.len(), |k| k + close.len())
        } else if rest.starts_with('"') {
            let mut k = 1;
            while k < rest.len() && rest.as_bytes()[k] != b'"' {
                k += if rest.as_bytes()[k] == b'\\' { 2 } else { 1 };
            }
            k + 1
        } else if rest.starts_with('\'')
            && rest.len() > 2
            && (rest.as_bytes()[2] == b'\'' || rest.as_bytes()[1] == b'\\')
        {
            rest[1..].find('\'').map_or(1, |k| k + 2)
        } else {
            rest.chars().next().map_or(1, char::len_utf8)
        };
        let piece = &rest[..len.min(rest.len())];
        if skip {
            match piece {
                "{" => depth += 1,
                "}" => {
                    depth -= 1;
                    skip = depth != 0;
                }
                ";" if depth == 0 => skip = false,
                _ => {}
            }
        } else {
            out.push_str(piece);
        }
        i += piece.len().max(1);
    }
    out
}

#[test]
fn code_without_tests_drops_only_the_test_items_and_the_comments() {
    let src = "a // E\n#[cfg(test)]\nuse x;\nb\n#[cfg(test)]\nmod t {\n    c \"}\" '}' r#\"}\"#\n}\nd /* e */\n";
    assert_eq!(code_without_tests(src), "a \n\nb\n\nd \n");
}

/// The table is the one place that makes an E0020 (W3-15, R-87 (4)): no
/// source of the compiler outside it spells the code (`Code::E0020`, a glob
/// import's `E0020`), but its registry (`onsa_diag::codes`), the comments
/// and the tests (the test modules, and the `*_tests.rs` files).
#[test]
fn only_the_table_makes_an_e0020() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut found = Vec::new();
    let mut dirs = vec![root.join("crates")];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            if path.is_dir() {
                // The sources of the crates (not their integration tests or build output).
                if name != "target" && name != "tests" {
                    dirs.push(path);
                }
                continue;
            }
            if !name.ends_with(".rs")
                || name.ends_with("_tests.rs")
                || path.ends_with("onsa_syntax/src/foreign.rs")
                || path.ends_with("onsa_syntax/src/foreign/rows.rs")
                || path.ends_with("onsa_diag/src/codes.rs")
            {
                continue;
            }
            let code = code_without_tests(&std::fs::read_to_string(&path).unwrap());
            let spelled = code.match_indices("E0020").any(|(i, _)| {
                let next = code[i + 5..].chars().next();
                !next.is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_')
            });
            if spelled {
                found.push(path.strip_prefix(&root).unwrap_or(&path).display().to_string());
            }
        }
    }
    assert!(found.is_empty(), "E0020 made outside `onsa_syntax::foreign`: {found:?}");
}
