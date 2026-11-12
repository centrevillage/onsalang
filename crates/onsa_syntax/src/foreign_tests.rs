//! Tests of the table of the forms of other languages ([`crate::foreign`]):
//! each form is found where the parser fails, with its code, and its first
//! candidate gives the Onsa form. The examples of the data file
//! `spec/foreign-forms.toml`, which run through the same entry as the cases
//! and check every candidate against the contract of §18.1, are the tests of
//! `onsa_tests` (D-15); these are the unit tests of the matchers.

use onsa_diag::{Code, FileId, Span};

use crate::foreign::{ROWS, RowId, WAITING};
use crate::parser_tests::codes;

fn parse(src: &str) -> crate::Parsed {
    crate::parse(FileId(0), src)
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

/// A row is made (`ROWS`) or waits for a later work (`WAITING`), not both:
/// a row moved into `ROWS` leaves `WAITING` (the module's documentation).
#[test]
fn no_row_is_both_made_and_waiting() {
    assert!(!WAITING.is_empty() && !ROWS.is_empty());
    for w in WAITING {
        assert!(ROWS.iter().all(|r| r.name != w.name), "{} is in ROWS and WAITING", w.name);
    }
}

/// Every `RowId` has its row in `ROWS` (one, by the test above), so that
/// [`crate::foreign::row`] finds it: a row a later stage reports
/// (`Detect::Reported`) has no matcher to tell that it is missing.
#[test]
fn every_row_id_has_its_row() {
    for &id in RowId::ALL {
        assert!(ROWS.iter().any(|r| r.id == id), "{id:?} has no row in ROWS");
    }
    assert_eq!(RowId::ALL.len(), ROWS.len());
}

/// A row of a later stage found with no candidate keeps its E0020 (§18.1,
/// R-301): the syntax stage alone makes it the general E0002.
#[test]
fn a_row_of_a_later_stage_keeps_e0020_with_no_candidate() {
    let span = onsa_diag::Span::new(FileId(0), 0, 1);
    for id in [RowId::ValueCall, RowId::ItemDotCall, RowId::IndexedValueCall] {
        assert_eq!(crate::foreign::report(id, "f(x)", span, Vec::new()).code, Code::E0020, "{id:?}");
    }
}

#[test]
fn every_row_of_the_syntax_stage_has_a_matcher() {
    // The registry of the matchers (R-206): each row found where the parser
    // fails is named by a matcher, each matcher names rows of that kind only,
    // and a matcher lists a row once. The same for the forms the parser
    // reads whole (`READS`, `Detect::Read`).
    use crate::foreign::{Detect, MATCHERS, READS};
    for (registry, detect) in [(MATCHERS, Detect::Syntax), (READS, Detect::Read)] {
        for r in ROWS {
            let named = registry.iter().any(|m| m.rows.contains(&r.id));
            assert_eq!(named, r.detect == detect, "{}", r.name);
        }
        for m in registry {
            for (i, id) in m.rows.iter().enumerate() {
                assert!(!m.rows[..i].contains(id), "{id:?} twice");
                assert_eq!(crate::foreign::row(*id).detect, detect, "{id:?}");
            }
        }
    }
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
    // No element before it: the general E0002, and the `(` is not closed (R-371).
    assert_eq!(codes("pub fn t(;\n"), [Code::E0002, Code::E0002]);
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
    // A tuple index is no name: the call of the value (§4.5, S-606).
    e0020(&body("  t.0::<U8>(1)"), &body("  t.0.(1)"));
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
    for src in ["  (id)::[U8](1)", "  id::[U8]::[U8](1)", "  1::[U8]"] {
        let p = parse(&body(src));
        assert_eq!(codes(&body(src)), [Code::E0002], "{src}");
        assert!(p.diagnostics[0].fixes.is_empty(), "{src}");
    }
    // The elements of a list are types and constant expressions (§4.5, R-192).
    for src in ["fn f(r: Rg[F32, 2 * N * 3, N - 1]) { }\n", "fn f(r: Rg[F32, (1 + 2) * 3, -(1), size(3)]) { }\n"] {
        assert!(codes(src).is_empty(), "{src}");
    }
    // An empty list: E0002, whose candidate takes it out, with its `::` in
    // an expression (§2.5, S-548).
    assert_eq!(codes("fn f(r: Rg[]) { }\n"), [Code::E0002]);
    assert_eq!(fixed("fn f(r: Rg[]) { }\n"), "fn f(r: Rg) { }\n");
    assert_eq!(codes(&body("  id::[](1)")), [Code::E0002]);
    assert_eq!(fixed(&body("  id::[](1)")), body("  id(1)"));
}

/// W5-24 U6b: the content of an index that holds lists `name[A, B]` is read
/// as a type once, whatever the number of lists in it (S-975), in the file
/// and in the readings of its candidates: the tokens read for 300 lists in a
/// tuple are at most 3.5 times those for 100, whether the content is a type
/// or not (a string after the lists).
#[test]
fn the_content_of_an_outer_index_is_read_once() {
    let src = |n: usize, last: &str| body(&format!("  id[({}{last})](x)", vec!["f[1, 2]"; n].join(", ")));
    onsa_diag::stack::run(|| {
        for last in ["", ", \"s\""] {
            let bumped = |n| {
                let before = crate::parser::BUMPED.get();
                parse(&src(n, last));
                crate::parser::BUMPED.get() - before
            };
            let (few, many) = (bumped(100), bumped(300));
            // Each list has 6 tokens: all are read.
            assert!(few > 100 * 6 && many * 2 <= few * 7, "`{last}`: {few} tokens for 100 lists, {many} for 300");
        }
    });
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
        ("  t.0<U8>(1)", "  t.0.(1)"),
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
        "  xs[,]",
        "  xs[1, 2 +]",
        "  pair::[U8, _](1, 2)",
        "  d<->>(x)",
        "  f<A,>(x)",
        "  d<U->8>(x)",
    ] {
        let p = parse(&body(src));
        assert!(p.diagnostics.iter().all(|d| d.fixes.is_empty()), "{src}: {:?}", p.diagnostics);
    }
    // A list after a name that does not read as type arguments has the
    // index form alone (§4.5, S-333): `_` is an expression (a hole). The
    // E0020 of its `[` is the first error of the unit (§18.1).
    let src = body("  a[i, _]");
    let p = parse(&src);
    let first = p.diagnostics.iter().min_by_key(|d| d.span.start).unwrap();
    assert_eq!((first.code, first.fixes.len()), (Code::E0020, 1));
    let edits: Vec<_> = first.fixes[0].edits().iter().collect();
    assert_eq!(onsa_diag::apply_text(&src, &edits).unwrap(), body("  a[i][_]"));
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

/// A derive whose candidate leaves the kinds `Copy` and `Dup` out says why in
/// a note after the row's rule (the rule of `copy_bound`, S-463); one that
/// leaves nothing out has the row's rule alone.
#[test]
fn a_derive_notes_the_kinds_it_leaves_out() {
    let kinds = crate::foreign::row(RowId::CopyBound).rule;
    for (src, left_out) in [
        ("#[derive(Copy, Eq)]\npub struct P { a: I32 }\n", true),
        ("#[derive(Dup)]\npub enum E { A }\n", true),
        ("#[derive(Eq)]\npub struct P { a: I32 }\n", false),
    ] {
        let p = parse(src);
        let [d] = p.diagnostics.as_slice() else { panic!("{src}: {:?}", p.diagnostics) };
        assert_eq!((d.code, d.fixes.len()), (Code::E0020, 1), "{src}");
        let rules: Vec<&str> = d.notes.iter().map(|n| n.message.as_str()).collect();
        let mut want = vec![crate::foreign::row(RowId::HashAttribute).rule];
        want.extend(left_out.then_some(kinds));
        assert_eq!(rules, want, "{src}");
    }
}

/// The rule of the attributes names those of the table and no others (§6.5),
/// and the note of a `#[…]` ends with it.
#[test]
fn the_rule_of_the_attributes_names_the_table() {
    use crate::attrs::{ATTRIBUTES, RULE};
    let named: Vec<&str> = RULE
        .split("`@")
        .skip(1)
        .map(|s| s.split(|c: char| !c.is_ascii_alphanumeric() && c != '_').next().unwrap_or(""))
        .collect();
    let table: Vec<&str> = ATTRIBUTES.iter().map(|a| a.name).collect();
    assert_eq!(named, table);
    for id in [RowId::HashAttribute, RowId::HashAttributeNoCandidate, RowId::HashAttributeUnfixable] {
        assert!(crate::foreign::row(id).rule.ends_with(RULE), "{id:?}");
    }
}

/// The place of a `#[…]` in the head of a declaration is the declaration
/// the parser read (§6.5, S-435): past the other attributes, both forms, and
/// a visibility of another language read on, the derive goes to the head of
/// the struct, and the attribute of Onsa is written with `@`.
#[test]
fn a_hash_attribute_goes_to_the_declaration_the_parser_read() {
    for (src, want) in [
        ("#[repr(C)]\npub(crate) struct P { x: I32 }\n", "@repr(c)\npub(crate) struct P { x: I32 }\n"),
        ("#[derive(Eq)] pub(crate) struct P { x: I32 }\n", "pub(crate) struct P: Eq { x: I32 }\n"),
        (
            "#[derive(Eq)]\n#[derive(PartialEq)]\npub struct P { x: I32 }\n",
            "#[derive(PartialEq)]\npub struct P: Eq { x: I32 }\n",
        ),
        ("#[derive(Eq)]\n#[repr(C)]\npub struct P { x: I32 }\n", "#[repr(C)]\npub struct P: Eq { x: I32 }\n"),
        ("#[derive(Eq)] @repr(c) pub struct P { x: I32 }\n", "@repr(c) pub struct P: Eq { x: I32 }\n"),
        ("@derive(Eq) pub(pkg) struct P { x: I32 }\n", "pub(pkg) struct P: Eq { x: I32 }\n"),
        ("@derive(Eq)\n@repr(c)\nstruct P { x: I32 }\n", "@repr(c)\nstruct P: Eq { x: I32 }\n"),
    ] {
        let p = parse(src);
        let d = p.diagnostics.iter().min_by_key(|d| d.span.start).unwrap_or_else(|| panic!("{src}"));
        assert_eq!((d.code, d.span.start), (Code::E0020, 0), "{src}: {:?}", p.diagnostics);
        let fix = d.fixes.first().unwrap_or_else(|| panic!("{src}: {d:?}"));
        assert_eq!(onsa_diag::apply_text(src, &fix.edits().iter().collect::<Vec<_>>()).unwrap(), want, "{src}");
    }
}

/// A `#[…]` with no candidate says why: the place takes no Onsa form of it
/// (S-483), or the form as written cannot be rewritten (its names or its
/// brackets do not read, one not closed on its line, §18.1).
#[test]
fn a_hash_attribute_with_no_candidate_says_why() {
    let no_form = crate::foreign::row(RowId::HashAttributeNoCandidate).message;
    let unfixable = crate::foreign::row(RowId::HashAttributeUnfixable).message;
    for (src, message) in [
        ("#[derive(Eq)]\npub fn h() -> I32 { 1 }\n", no_form),
        ("#[inline]\npub fn h() -> I32 { 1 }\n", no_form),
        ("#[repr(C)]\npub fn h() -> I32 { 1 }\n", no_form),
        ("#[inline]\nfoo bar\n", no_form),
        ("#[inline]\nlet x = 1\n", no_form),
        // Another `#[…]` that fails after it begins no declaration.
        ("#[inline]\n#[b]\n", no_form),
        ("#[inline]\n#\n", no_form),
        ("#[inline]\n#[b\n", no_form),
        // Before a head that began and failed, the place is not known (W3-08).
        ("#[repr(C)]\npub(crate struct P { x: I32 }\n", unfixable),
        ("#[derive(Eq Ord)]\npub struct P { x: I32 }\n", unfixable),
        ("#[derive(Eq)]\npub struct P: { x: I32 }\n", unfixable),
        ("#[repr(\nC)]\npub struct P { x: I32 }\n", unfixable),
        ("#[inline) fn h() -> I32 { 1 }\n", unfixable),
    ] {
        let p = parse(src);
        let d = p.diagnostics.iter().min_by_key(|d| d.span.start).unwrap_or_else(|| panic!("{src}"));
        assert_eq!((d.code, d.span.start, d.message.as_str()), (Code::E0002, 0, message), "{src}");
        assert!(d.fixes.is_empty(), "{src}: {d:?}");
    }
    // Before the `}` of a list or the end of the file, no declaration comes:
    // the one error is the attribute's (the head is not read on to the `}`).
    for src in ["pub struct P { x: I32 }\nimpl P {\n  fn a(self) -> I32 { 1 }\n  #[inline]\n}\n", "#[inline]\n"] {
        assert_eq!(messages(src), [no_form], "{src}");
    }
}

/// A bracket closes on its line only with a closer of its kind (§18.1): a
/// form closed by another kind is not read on after, at a `pub(…)`, a `#[…]`
/// and an attribute of Onsa alike.
#[test]
fn a_bracket_closed_by_another_kind_does_not_close() {
    for src in
        ["pub(crate] fn h() -> I32 { 1 }\n", "pub(crate} fn h() -> I32 { 1 }\n", "#[inline) fn h() -> I32 { 1 }\n"]
    {
        let p = parse(src);
        assert!(p.diagnostics.iter().all(|d| d.fixes.is_empty()), "{src}: {:?}", p.diagnostics);
        assert!(p.ast.root.is_empty(), "{src}: read on");
    }
    let src = "@fp(relaxed, 1 +] fn h() -> I32 { 1 }\n";
    assert!(parse(src).ast.root.is_empty(), "{src}: read on");
    let tokens = crate::layout::code_tokens(&crate::lex(FileId(0), "(a] b").tokens).0;
    assert_eq!(crate::scan::Brackets::new(&tokens).closing(0), None);
    // At a token that opens nothing, none (no overflow, no failure).
    assert_eq!(crate::scan::Brackets::new(&tokens).closing(1), None);
    assert_eq!(crate::scan::Brackets::new(&tokens).closing(2), None);
}

/// Which bracket a closer closes (`crate::scan::pair`): the innermost one of
/// its kind above the base, with the ones opened inside it; with none of its
/// kind, nothing. [`crate::scan::Brackets::closing`] reads it strictly: a closer of
/// another kind first closes nothing.
#[test]
fn a_closer_closes_the_innermost_bracket_of_its_kind() {
    use crate::token::TokenKind::{LBrace, LParen, RBrace, RBracket, RParen};
    let tokens = crate::layout::code_tokens(&crate::lex(FileId(0), "{ f ( a ] } )").tokens).0;
    let at = |kind| tokens.iter().position(|t| t.kind == kind).unwrap();
    let mut open = crate::scan::OpenBrackets::default();
    let closed: Vec<Option<usize>> = (0..tokens.len()).map(|i| crate::scan::pair(&mut open, &tokens, i, 0)).collect();
    assert_eq!(closed[at(RBracket)], None);
    assert_eq!(closed[at(RBrace)], Some(at(LBrace)), "the `}}` closes the `{{` with the `(` in it");
    assert_eq!(closed[at(RParen)], None);
    assert!(open.is_empty());
    // A `}` whose `{` is below the base closes nothing, and leaves it open.
    let mut open = crate::scan::OpenBrackets::default();
    for opener in [at(LBrace), at(LParen)] {
        crate::scan::pair(&mut open, &tokens, opener, 0);
    }
    assert_eq!(crate::scan::pair(&mut open, &tokens, at(RBrace), 1), None);
    assert_eq!(*open, [at(LBrace), at(LParen)]);
    let tokens = crate::layout::code_tokens(&crate::lex(FileId(0), "( [ { ] ) ( [ ] )").tokens).0;
    assert_eq!(crate::scan::Brackets::new(&tokens).closing(0), None);
    let second = tokens.iter().rposition(|t| t.kind == LParen).unwrap();
    let last = tokens.iter().rposition(|t| t.kind == RParen).unwrap();
    assert_eq!(crate::scan::Brackets::new(&tokens).closing(second), Some(last));
}

/// The traits a head has end with its list (§6.4): a line break after a
/// name, or any token that is no part of the list; the candidate of a derive
/// edits that head only.
#[test]
fn the_derive_adds_after_the_list_of_its_head_only() {
    for (src, want) in [
        ("#[derive(Eq)]\nstruct P: PartialEq\nfn f() {}\n", "struct P: PartialEq + Eq\nfn f() {}\n"),
        ("#[derive(Eq)]\nstruct P: PartialEq;\nfn f() {}\n", "struct P: PartialEq + Eq;\nfn f() {}\n"),
        (
            "#[derive(Eq)]\npub struct P: PartialEq +\n  Ord { x: I32 }\n",
            "pub struct P: PartialEq +\n  Ord + Eq { x: I32 }\n",
        ),
        // A `,` after the last name (W3-08), of both attributes.
        ("#[derive(PartialEq, Eq,)]\npub struct P { x: I32 }\n", "pub struct P: PartialEq + Eq { x: I32 }\n"),
        ("@derive(Eq,)\npub struct P { x: I32 }\n", "pub struct P: Eq { x: I32 }\n"),
        // A trait the head has is a name alone, not the last word of a path
        // (S-488): `std.Eq` is no `Eq`.
        ("#[derive(Eq)]\npub struct P: std.Eq { x: I32 }\n", "pub struct P: std.Eq + Eq { x: I32 }\n"),
        ("#[derive(Eq)]\npub struct P: std.Eq + Eq { x: I32 }\n", "pub struct P: std.Eq + Eq { x: I32 }\n"),
    ] {
        assert_eq!(fixed(src), want, "{src}");
    }
}

/// The candidate of a tuple struct of one element (S-39): one `,` after the
/// field, one blank before the `{`, the line break of the file, and the
/// field `priv` but in a `priv struct` (§15.1, S-494).
#[test]
fn the_candidate_of_a_tuple_struct_writes_one_priv_field() {
    e0020("pub struct Hz(F32,)\n", "pub struct Hz {\n  priv value: F32,\n}\n");
    e0020("pub struct Hz (F32)\n", "pub struct Hz {\n  priv value: F32,\n}\n");
    e0020("pub struct Hz: Eq ( F32 , )\n", "pub struct Hz: Eq {\n  priv value: F32,\n}\n");
    e0020("struct Gain(F32)\n", "struct Gain {\n  priv value: F32,\n}\n");
    e0020("priv struct Level(I32)\n", "priv struct Level {\n  value: I32,\n}\n");
    e0020("pub struct Hz(F32)\r\nfn f() {}\r\n", "pub struct Hz {\r\n  priv value: F32,\r\n}\r\nfn f() {}\r\n");
}

#[test]
fn keywords_and_marks() {
    e0020(&body("  loop {\n    break\n  }"), &body("  while true {\n    break\n  }"));
    e0020("proc f(x: Sig[F32]) -> Sig[F32] { x }\n", "flow f(x: Sig[F32]) -> Sig[F32] { x }\n");
    // An attribute that the table of the attributes does not take (§6.5): no
    // candidate, which would leave the E0005 (S-483).
    e0002("#[inline]\nfn f() { }\n");
    e0020("#[repr(C)]\nstruct S { }\n", "@repr(c)\nstruct S { }\n");
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
    // After one, or before `~`, `--` or `!` (S-962): no candidate.
    assert_eq!(codes(&body("  let n = ~!m.f(1)")), [Code::E0002]);
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
    // In the parentheses of a negative literal pattern, the number's row (§4.7, S-227).
    let m = |pat: &str| format!("fn f(x: I32) -> I32 {{\n  match x {{\n    {pat} => 1,\n    _ => 0,\n  }}\n}}\n");
    e0020(&m("-(017)"), &m("-(17)"));
    assert_eq!(fixed_by(&m("-(017)"), 1), m("-(15)"));
    e0020(&m("-((0o17))"), &m("-((15))"));
    e0020(&m("-( 1u8 )"), &m("-( 1 )"));
}

#[test]
fn block_comments() {
    // Ending its line: in place.
    e0020(&body("  let a = 1 /* one */"), &body("  let a = 1 // one"));
    e0020(&body("  /* one */"), &body("  // one"));
    // Code after it: the words go above the line, the code stays (S-247).
    e0020(&body("  1 /* one */ + 2"), &body("  // one\n  1 + 2"));
    e0020(&body("  1 /* one */+ 2"), &body("  // one\n  1 + 2"));
    // Between tokens it touches, no blank goes in where they stay apart
    // without one: `1 +2` would be the asymmetric `+` (S-405).
    e0020(&body("  1/* one */+2"), &body("  // one\n  1+2"));
    e0020(&body("  1 /* one */-2"), &body("  // one\n  1-2"));
    e0020(&body("  1 +/* one */2"), &body("  // one\n  1 + 2"));
    e0020(&body("  let x = 1/* one */as I64"), &body("  // one\n  let x = 1 as I64"));
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
    // A line break or a comment between the `=` and the right side stays
    // (S-251, R-210); blanks alone are replaced.
    e0020(&body("  x +=\n    1"), &body("  x = x +\n    1"));
    e0020(&body("  x += // c\n    1"), &body("  x = x + // c\n    1"));
    e0020(&body("  x -= // c\n    -y"), &body("  x = x - ( // c\n    -y)"));
    assert_eq!(fixed(&body("  x -= /* c */ -y")), body("  x = x - ( /* c */ -y)"));
    e0020(&body("  x +=1"), &body("  x = x + 1"));
    e0020(&body("  x -=  -y"), &body("  x = x - (-y)"));
}

/// The pattern of other languages with no candidate says why after the
/// row's rule (A26): a comment the candidate would lose, an end of a range
/// that does not read, alternatives of other shapes; a form the message
/// explains (`@` that is no comparison) has the rule alone.
#[test]
fn a_guard_form_with_no_candidate_says_why() {
    let comment = "no candidate: a comment in the part the guard form would rewrite would be lost (§18.1); \
                   move it out of the pattern, or write the guard by hand";
    let end = "no candidate: an end of the range does not read as an expression a guard could copy; \
               write the end as an expression, or write the guard by hand";
    let shapes = "no candidate: once the forms are replaced the alternatives are not of one shape, and one \
                  guard cannot tell which matched; split them into arms, or write the guard by hand";
    let m = |ty: &str, arms: &str| format!("fn f(x: {ty}) -> I32 {{\n  match x {{\n{arms}\n    _ => 0,\n  }}\n}}\n");
    for (src, why) in [
        (m("F32", "    1.0 // one\n    | 2.0 => 1,"), Some(comment)),
        (m("F32", "    1.0 /* one */ | 2.0 => 1,"), Some(comment)),
        (m("I32", "    k @ // c\n    1 => k,"), Some(comment)),
        (m("I32", "    k @ /* c */ 1 => k,"), Some(comment)),
        (m("I32", "    1..<(3 + // c\n      1) => 1,"), Some(comment)),
        (m("I32", "    1..< => 1,"), Some(end)),
        (m("I32", "    1..<{ 8 } => 1,"), Some(end)),
        (m("(F32, I32)", "    (0.5, 1) | (1.5, 2) => 1,"), Some(shapes)),
        (m("Str", "    \"a{x}\" | \"b\" => 1,"), Some(shapes)),
        (m("Option[I32]", "    s @ Some(_) => 1,"), None),
        // A block comment the candidate would keep, or not the reason: no note.
        (m("(F32, Option[I32])", "    (1.0, Some(/* c */ a)) => 1,"), None),
        (m("Option[I32]", "    k @ Some(_) /* c */ => 1,"), None),
    ] {
        let p = parse(&src);
        let d = &p.diagnostics[0];
        assert_eq!((d.code, d.fixes.len()), (Code::E0002, 0), "{src}: {:?}", p.diagnostics);
        let notes: Vec<&str> = d.notes.iter().map(|n| n.message.as_str()).collect();
        assert_eq!(notes.len(), 1 + usize::from(why.is_some()), "{src}: {notes:?}");
        assert_eq!(notes.get(1).copied(), why, "{src}");
    }
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
                || name == "tests.rs"
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

/// The messages of the diagnostics of `src`.
fn messages(src: &str) -> Vec<String> {
    parse(src).diagnostics.iter().map(|d| d.message.clone()).collect()
}

fn flow(stmts: &str) -> String {
    format!("pub flow f(x: I32 at sample, c: Bool at sample) -> I32 at sample {{\n{stmts}")
}

#[test]
fn a_delay_cut_at_the_end_of_the_file() {
    // A file that ends right after the `@` (no line break): a diagnostic,
    // no internal error (the reads of the cursor past the `Eof`).
    for cut in ["  x@", "  twice~(x@", "  (x@", "  if~ c { x@", "  let y = x@"] {
        assert!(codes(&flow(cut)).contains(&Code::E0002), "{cut}");
    }
}

#[test]
fn the_compositions_of_faust_stand_as_statements() {
    // S-485: the value of a `let` and a statement of a flow's body or a
    // branch; not in brackets, heads or a block of its own.
    let compose = "there are no operators that compose signals";
    for yes in ["  let a = x : x\n  a\n}\n", "  x <: x\n}\n", "  let a = if~ c { x :> x } else { x }\n  a\n}\n"] {
        assert!(messages(&flow(yes)).iter().any(|m| m == compose), "{yes}");
    }
    for no in [
        "  if c : x\n}\n",
        "  while x > 0 : x\n}\n",
        "  let a = xs[1 : 2]\n  a\n}\n",
        "  { a : 1 }\n}\n",
        "  lp~(x, cutoff : 1.0)\n}\n",
        "  if x > 0, x < 2 { x } else { x }\n}\n",
        "  let a = [0; 3, 4]\n  a\n}\n",
    ] {
        assert!(!messages(&flow(no)).iter().any(|m| m == compose), "{no}");
    }
}

#[test]
fn a_hole_in_the_parentheses_of_a_prefix_tilde() {
    // S-486: `~(_ * 0.5)` is the feedback of FAUST, no `!(…)`; `~(m)` and
    // `~-(m)` are the bitwise negation.
    let not = "bits are negated with the prefix `!`";
    assert!(!messages(&flow("  let y = x + ~(_ * 0.5)\n  y\n}\n")).iter().any(|m| m == not));
    e0020(&body("  let n = ~(m)\n  n"), &body("  let n = !(m)\n  n"));
    e0020(&body("  let n = ~-(m)\n  n"), &body("  let n = !(-(m))\n  n"));
}

#[test]
fn a_delay_is_no_length_of_an_array_type() {
    let delay = "a delay is written `prev~(x)` or `delay~(x, N)`";
    assert!(!messages(&flow("  let y: [I32; N@2] = z\n  y\n}\n")).iter().any(|m| m == delay));
}

/// A tuple index is no name (§2.3), so a callee that ends with one is a value
/// whatever is before it (§6.1, S-606): its `(` is the E0020 of `.(`, and a
/// mark `!` / `~` or a `::[` after it is the E0002 of its place with a note and
/// no candidate (§2.6, §4.5), as is a `(` or a mark after a blank (§2.5, as
/// `mk2().0 (1)`). In a list, a line break before the mark is the missing
/// `,` only where the mark starts an element (`!(`), never taken out.
#[test]
fn a_tuple_index_ends_a_callee_as_a_value() {
    for (callee, value) in [("t.0(x)", "t.0.(x)"), ("s.t.0(x)", "s.t.0.(x)"), ("mk2().0(x)", "mk2().0.(x)")] {
        e0020(&body(&format!("  let v = {callee}")), &body(&format!("  let v = {value}")));
    }
    e0020(&body("  let v = t.0<I32>(x)"), &body("  let v = t.0.(x)"));
    for e in [
        "t.0!(x)",
        "t.0~(x)",
        "s.t.0!(x)",
        "mk2().0~(x)",
        "t.0.1!(x)",
        "t.0! (x)",
        "t.0~ (x)",
        "t.0::[I32](x)",
        "mk2().0::[I32](x)",
        "t.0 (x)",
        "t.0 ~(x)",
        "t.0 !(x)",
        "t.0 ~ (x)",
        "mk2().0 !(x)",
    ] {
        e0002(&body(&format!("  let v = {e}")));
    }
    for (src, commas) in [("two(t.0\n  ~(1), 2)", 0), ("two(t.0\n  !(1), 2)", 1), ("[t.0 ~(1), 2]", 0)] {
        let src = body(&format!("  let v = {src}"));
        let p = parse(&src);
        assert_eq!(codes(&src), [Code::E0002], "{src}: {:?}", p.diagnostics);
        let fixes = &p.diagnostics[0].fixes;
        assert_eq!(fixes.len(), commas, "{src}: {fixes:?}");
        assert!(fixes.iter().all(|f| f.title().contains("`,`")), "{src}: {fixes:?}");
    }
    // After a name or a method, the marks and `::[` stay (`u.0.scale!(2.0)`).
    for e in ["u.0.scale!(2.0)", "t.0.m::[I32](x)", "t.0.(x)", "t.0.m(x)"] {
        assert!(parse(&body(&format!("  let v = {e}"))).diagnostics.is_empty(), "{e}");
    }
}

/// After a value that ends with no tuple index, a `!(` that touches it is
/// read as before (S-631): in a list, the missing `,` before `!(x)`. In the
/// arms of a `match`, an opener after a gap that no `=>` follows has the gap
/// taken out as its one candidate, and none when that does not read (§2.5).
/// A `!(` that touches a value that is no name, where no `,` of a list goes
/// before it, notes the rule of the marks as a `~(` there does (R-339).
#[test]
fn a_bang_after_another_value_notes_the_marks_where_no_comma_goes() {
    for src in ["let v = inc(1)!(x)", "let v = W { a: inc(1)!(x) }", "let v = match x { 1 => inc(1)!(x), _ => 0 }"] {
        let p = parse(&body(&format!("  {src}")));
        let d = &p.diagnostics[0];
        assert!(d.code == Code::E0002 && d.fixes.is_empty(), "{src}: {:?}", p.diagnostics);
        assert!(d.notes.iter().any(|n| n.message.contains("the marks")), "{src}: {:?}", d.notes);
    }
}

#[test]
fn a_bang_after_another_value_and_an_opener_in_the_arms() {
    for src in ["two(inc(1)!(2), 1)", "[(t)!(x)]", "(x?!(y), 1)"] {
        let src = body(&format!("  let v = {src}"));
        let p = parse(&src);
        assert_eq!(codes(&src), [Code::E0002], "{src}: {:?}", p.diagnostics);
        let fixes = &p.diagnostics[0].fixes;
        assert!(fixes.len() == 1 && fixes[0].title().contains("`,`"), "{src}: {fixes:?}");
    }
    for arm in ["t.0 (x)", "t.0\n  (x)", "mk2() (x)"] {
        let src = body(&format!("  let v = match x {{ 0 => {arm}, _ => 1 }}"));
        let p = parse(&src);
        assert_eq!(codes(&src), [Code::E0002], "{src}: {:?}", p.diagnostics);
        assert!(p.diagnostics[0].fixes.is_empty(), "{src}: {:?}", p.diagnostics);
    }
    let src = body("  let v = match x { 0 => xs\n  [0], _ => 1 }");
    assert_eq!(fixed(&src), body("  let v = match x { 0 => xs[0], _ => 1 }"));
}

/// The call of a value with `.(` in place of type arguments of another
/// language takes the callee one level down: no candidate that takes the
/// unit over the nesting limit (§2.5, §18.1), as for `t.0(x)`.
#[test]
fn the_call_of_a_value_for_type_arguments_keeps_within_the_limit() {
    let limit = crate::parser::NESTING_LIMIT as usize;
    onsa_diag::stack::run(|| {
        for (n, fixes) in [(limit - 3, 1), (limit - 2, 0)] {
            let src = body(&format!("  let v = {}t.0<I32>(x){}", "(".repeat(n), ")".repeat(n)));
            let p = parse(&src);
            assert_eq!(p.diagnostics.len(), 1, "{n}: {:?}", p.diagnostics);
            assert_eq!(p.diagnostics[0].fixes.len(), fixes, "{n}: {:?}", p.diagnostics);
            if fixes == 1 {
                assert!(parse(&fixed(&src)).diagnostics.is_empty(), "{n}");
            }
        }
    });
}

/// The candidate of the types stage counts the levels of what it writes
/// (§2.5, §18.1): none past the limit, by the `&&` before a guard at it.
#[test]
fn constants_in_guard_stops_at_the_nesting_limit() {
    let candidate = |n: usize| {
        let (open, close) = ("(".repeat(n), ")".repeat(n));
        let text =
            format!("pub fn d(k: Bool, x: F32) -> I32 {{\n  match x {{\n    L if {open}k{close} => 1,\n  }}\n}}\n");
        let at = text.find('L').unwrap() as u32;
        let (parsed, tree) = parse(&text).split();
        let arm = Span::new(FileId(0), at, text.find("1,").unwrap() as u32 + 1);
        crate::foreign::guard::constants_in_guard(&tree, &parsed.units, &text, arm, &[at]).is_ok()
    };
    onsa_diag::stack::run(move || {
        assert!(candidate(1) && candidate(250));
        assert!(!candidate(254));
    });
}

/// What the guard candidates read again is at most this many times the
/// file: the names of the file once, and the unit of each arm a few times.
const AT_MOST: usize = 4;

/// The names that the guard candidates take no new name from are made once
/// for a file (R-209): a file of many arms with a guard form, an E0020 with
/// a candidate each, goes through its tokens once for them.
#[test]
fn the_names_of_a_file_are_made_once_for_its_guard_forms() {
    let n = 200;
    let arms = ["1..<3 => 1,", "0.5 => 1,", "\"a{s}\" => 1,"];
    let src: String = (0..n)
        .map(|k| {
            let subject = ["x", "y", "s"][k % 3];
            let arm = arms[k % 3];
            format!(
                "fn f{k}(x: I32, y: F32, s: Str) -> I32 {{\n  match {subject} {{\n    {arm}\n    _ => 0,\n  }}\n}}\n"
            )
        })
        .collect();
    let tokens = crate::lex(FileId(0), &src).tokens.len();
    let before = crate::foreign::guard::NAMED.get();
    let p = parse(&src);
    let named = crate::foreign::guard::NAMED.get() - before;
    assert_eq!(p.diagnostics.len(), n, "{:?}", p.diagnostics.first());
    assert!(p.diagnostics.iter().all(|d| d.code == Code::E0020 && d.fixes.len() == 1), "{:?}", p.diagnostics.first());
    assert!(0 < named && named <= tokens, "went through {named} tokens for the names of a file of {tokens}");
}

/// The candidate of the types stage reads the unit of its arm again, not
/// the file (R-385): for a file of many arms with a constant of a type no
/// pattern compares, the texts the parsers read for all of them, and the
/// tokens gone through for the names, are bounded by the file. Every other
/// arm has a block-like guard of its own, which the completion
/// parenthesizes (a second reading of its unit).
#[test]
fn the_candidates_of_the_types_stage_read_the_units_of_their_arms() {
    let n = 200;
    let src: String = "const L: F32 = 1.0\n".to_string()
        + &(0..n)
            .map(|k| {
                let guard = if k % 2 == 0 { "" } else { " if if b { true } else { false }" };
                format!("fn f{k}(x: F32, b: Bool) -> I32 {{\n  match x {{\n    L{guard} => 1,\n    _ => 0,\n  }}\n}}\n")
            })
            .collect::<String>();
    let (parsed, tree) = parse(&src).split();
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics.first());
    let tokens = tree.cst.tokens().len();
    let (read, named) = (crate::parser::PARSED.get(), crate::foreign::guard::NAMED.get());
    let mut wrapped = 0;
    for (at, _) in src.match_indices("    L") {
        let at = at as u32 + 4;
        let end = at + src[at as usize..].find("=> 1").unwrap() as u32 + 4;
        let fix =
            crate::foreign::guard::constants_in_guard(&tree, &parsed.units, &src, Span::new(FileId(0), at, end), &[at]);
        let fix = fix.unwrap_or_else(|note| panic!("no candidate at {at}: {note:?}"));
        wrapped += usize::from(fix.edits().iter().any(|e| e.replace.ends_with("&& (")));
    }
    let (read, named) = (crate::parser::PARSED.get() - read, crate::foreign::guard::NAMED.get() - named);
    assert_eq!(wrapped, n / 2);
    assert!(0 < read && read <= AT_MOST * src.len(), "read {read} bytes of a file of {}", src.len());
    assert!(0 < named && named <= tokens, "went through {named} tokens for the names of a file of {tokens}");
}

/// The bytes the parsers read, the tokens the scans went through and the
/// tables made for `n` copies of `form` (`{i}` the copy's number), with the
/// diagnostics.
fn read_for(form: &str, n: usize) -> (usize, usize, usize, usize) {
    let src: String = (0..n).map(|i| form.replace("{i}", &i.to_string())).collect();
    let (read, walked, made) = (crate::parser::PARSED.get(), crate::scan::WALKED.get(), crate::scan::MADE.get());
    let p = parse(&src);
    let read = crate::parser::PARSED.get() - read;
    (read, crate::scan::WALKED.get() - walked, crate::scan::MADE.get() - made, p.diagnostics.len())
}

/// A pattern of an arm (also after a `|` before it), a `let` or a `for` that leaves a bracket open fails
/// in each function of a file, and the guard forms' reading of each reads
/// its tokens up to that bracket (R-410): what the parsers read and the
/// scans go through grows as the file, not as its square.
#[test]
fn the_patterns_that_leave_a_bracket_open_read_on_to_it() {
    let forms = [
        "fn f{i}() -> I32 {\n  match x {\n    A(1, [2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    n @ [1, 2 => xs[0],\n",
        "fn f{i}() -> I32 {\n  match x {\n    A(1.5 [2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    1..<f(2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    n @ A(1.5, (2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    A(1.5, (2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    A(g[1, [2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    | A(1, [2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    A => 1\n    B(1, [2 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    A if c => 1\n    -(-1 => 3,\n",
        "fn f{i}() -> I32 {\n  match x {\n    A => 1\n    | B(1, [2 => 3,\n",
        "fn f{i}() -> I32 {\n  let A(1, [2 = 3\n",
        "fn f{i}() -> I32 {\n  for A(1, [2 in xs {\n",
    ];
    for form in forms {
        let (read, walked, made, diagnostics) = read_for(form, 100);
        let (read2, walked2, made2, diagnostics2) = read_for(form, 200);
        assert!(diagnostics >= 100 && diagnostics2 >= 2 * diagnostics - 1, "{form:?}: {diagnostics}, {diagnostics2}");
        // One table for the file, and one for each reading of a unit a
        // candidate makes again (the `|` taken out).
        assert!(made >= 1 && made <= diagnostics + 1 && made2 <= 2 * made, "{form:?}: {made}, {made2} tables");
        assert!(read2 <= 2 * read + read / 10, "{form:?}: read {read} bytes for 100 and {read2} for 200");
        assert!(
            walked2 <= 2 * walked + walked / 10,
            "{form:?}: went through {walked} tokens for 100 and {walked2} for 200"
        );
    }
}

/// The range of a form that holds an opener no closer closes ends at that
/// opener (S-955, R-412): it holds no item after it, so the range of the
/// first of two functions is the same as that of the second.
#[test]
fn the_range_of_a_form_with_an_open_bracket_ends_at_it() {
    let arm = |pat: &str| format!("fn f() -> I32 {{\n  match x {{\n    {pat}(2 => 3,\n");
    for (pat, want) in [("1..<f", "1..<f("), ("n @ 1..<f", "@ 1..<f(")] {
        let one = arm(pat);
        for src in [one.clone(), one.repeat(2)] {
            let p = parse(&src);
            // The form's diagnostics (the unit's end at the `Eof` has none found).
            let found: Vec<_> = p.diagnostics.iter().filter_map(|d| Some((d.code, d.found.as_deref()?))).collect();
            assert_eq!(found, vec![(Code::E0002, want); src.matches("fn f").count()], "{src}");
            assert_eq!(p.diagnostics[0].span.end as usize, one.find(want).unwrap() + want.len(), "{src}");
        }
    }
}

/// A file of patterns with no failure makes no table of the brackets, and
/// its scans are those of before (R-410: the table is made at a failure).
#[test]
fn the_patterns_of_a_file_without_failures_make_no_table() {
    let form = "fn f{i}(x: I32, p: (I32, I32)) -> I32 {\n  let (a, b) = p\n  for k in 0..<x {\n  }\n  match x {\n    1 | 2 => a,\n    _ => b,\n  }\n}\n";
    let (_, _, made, diagnostics) = read_for(form, 50);
    assert_eq!((made, diagnostics), (0, 0));
}

/// The rows of `===` and `**` are in the place of a binary operator of an
/// expression only (S-450): after a type, a pattern or the path of a `use`
/// the failure is the general E0002 of the parser.
#[test]
fn the_operators_of_other_languages_are_rows_in_expressions_only() {
    let message = |src: &str| parse(src).diagnostics.first().map(|d| d.message.clone()).unwrap_or_default();
    for src in [
        "fn g(x: I32 ** y) {}\n",
        "fn f() {\n  let x: I32 ** = 1\n}\n",
        "struct S {\n  a: I32 **\n}\n",
        "fn f() -> I32 ** {\n  1\n}\n",
        "use std.math **\n",
        "fn f(x: I32) -> I32 {\n  match x {\n    1 ** 2 => 1,\n    _ => 0,\n  }\n}\n",
        "fn g(x: I32 === y) {}\n",
    ] {
        assert!(message(src).starts_with("expected "), "{src}: {:?}", parse(src).diagnostics);
    }
    assert_eq!(message(&body("  a ** b")), "there is no power operator `**`");
}

/// The candidate `==` of `===` is made only where the operand after it ends
/// at a token the table knows (S-450): a struct literal after it is not read.
#[test]
fn a_strict_equality_before_a_struct_literal_has_no_candidate() {
    e0002(&body("  a === P { x: 1 }.x < c"));
    e0020(&body("  a === b"), &body("  a == b"));
    e0020("fn f() {\n  while a !== b {\n  }\n}\n", "fn f() {\n  while a != b {\n  }\n}\n");
}

/// A bracket of the message of `assert c, m` that does not close ends the
/// form, with no candidate (§18.1): the statements after it stay out.
#[test]
fn an_unclosed_bracket_in_a_message_ends_the_form() {
    let src = body("  assert c, g(1\n  assert c");
    e0002(&src);
    let d = &parse(&src).diagnostics[0];
    assert_eq!(&src[d.span.start as usize..d.span.end as usize], "assert c, g(", "{d:?}");
}
