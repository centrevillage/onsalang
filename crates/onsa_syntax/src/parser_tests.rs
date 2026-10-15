//! Tests of the parser ([`crate::parser`]): the trees it builds, its
//! diagnostics and recovery, and the heights of the chains.

use onsa_diag::{Code, FileId};

#[test]
fn const_type_arguments() {
    // S-24: integer literals (optionally negated) are const arguments; names stay types.
    let p = crate::parse(FileId(0), "fn f(r: Ring[F32, 4], s: Ring[F32, N], t: Ring[F32, -1]) {}\n");
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let d = crate::dump(&p.ast);
    assert!(d.contains("Ring[F32, 4]"), "{d}");
    assert!(d.contains("Ring[F32, N]"), "{d}");
    assert!(d.contains("Ring[F32, (neg 1)]"), "{d}");
}

use crate::dump;

fn parse(src: &str) -> crate::Parsed {
    crate::parse(FileId(0), src)
}

fn codes(src: &str) -> Vec<Code> {
    parse(src).diagnostics.iter().map(|d| d.code).collect()
}

/// `src` after the first candidate of its first diagnostic.
fn fixed(src: &str) -> String {
    let p = parse(src);
    let fix = &p.diagnostics[0].fixes[0];
    onsa_diag::apply_text(src, &fix.edits().iter().collect::<Vec<_>>()).unwrap()
}

#[test]
fn the_e0003_candidate_keeps_the_comments_in_their_order() {
    let plain = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  }\n  else {\n    2\n  }\n}\n";
    assert_eq!(fixed(plain), "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}\n");
    let own_line = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  }\n  // other\n  else {\n    2\n  }\n}\n";
    assert_eq!(fixed(own_line), "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n  // other\n    2\n  }\n}\n");
    let after_brace = "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } // a\n  else { // b\n    2\n  }\n}\n";
    assert_eq!(fixed(after_brace), "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else { // a\n  // b\n    2\n  }\n}\n");
    let after = fixed(after_brace);
    assert!(parse(&after).diagnostics.is_empty(), "{:?}", parse(&after).diagnostics);
    assert!(parse(&fixed(own_line)).diagnostics.is_empty());
}

/// Dump of the body of `fn f() { <src> }`.
fn body(src: &str) -> String {
    let p = parse(&format!("fn f() {{\n{src}\n}}"));
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let d = dump(&p.ast);
    let d = d.trim_start_matches("(fn f()\n  ").trim_end_matches(")\n");
    let mut out = String::new();
    for (i, line) in d.lines().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        out.push_str(line.trim_start());
    }
    out
}

#[test]
fn newline_continuation() {
    assert_eq!(body("let a = x +\n  y"), "(block (let a = (+ x y)))");
    assert_eq!(body("let a = xs\n  .len()"), "(block (let a = (call (. xs len) ())))");
    assert_eq!(body("let a =\n  1"), "(block (let a = 1))");
    // Newlines are whitespace inside parentheses and brackets.
    assert_eq!(body("let a = f(1,\n  2)\nlet b = [1,\n 2]"), "(block (let a = (call f (1, 2))) (let b = [1, 2]))");
    // A newline without a continuation ends the statement.
    assert_eq!(body("let a = x\n-y"), "(block (let a = x) tail (neg y))");
}

#[test]
fn tail_vs_statement() {
    assert_eq!(body("let a = 1\na"), "(block (let a = 1) tail a)");
    assert_eq!(body("f(1)\n"), "(block tail (call f (1)))");
    assert_eq!(body("return"), "(block (return))");
    assert_eq!(body("x = 2"), "(block (assign x 2))");
}

#[test]
fn else_position() {
    assert!(codes("fn f() {\n  if c { a } else { b }\n}").is_empty());
    assert_eq!(codes("fn f() {\n  if c { a }\n  else { b }\n}"), vec![Code::E0003]);
    assert_eq!(
        body("if a { 1 } else if b { 2 } else { 3 }"),
        "(block tail (if a (block tail 1) else (if b (block tail 2) else (block tail 3))))"
    );
}

#[test]
fn call_marks() {
    assert_eq!(body("saw~(f0)"), "(block tail (call~ saw (f0)))");
    assert_eq!(body("out.fill!(0.0)"), "(block tail (call! (. out fill) (0.0)))");
    assert_eq!(body("a.f!=b"), "(block tail (!= (. a f) b))");
    assert_eq!(body("!(a && b)"), "(block tail (not ((&& a b))))");
    // A blank between the name and its mark (S-123, `space_before_tilde`).
    assert_eq!(codes("fn f() {\n  saw ~(f0)\n}"), vec![Code::E0020]);
    // A blank between the mark and its `(` (S-412).
    assert_eq!(codes("fn f() {\n  saw~ (f0)\n}"), vec![Code::E0020]);
}

#[test]
fn tuple_index_and_fields() {
    assert_eq!(body("t.0.1"), "(block tail (. (. t 0) 1))");
    assert_eq!(body("self.params[i].f0 = v"), "(block (assign (. (index (. self params) i) f0) v))");
}

#[test]
fn struct_literals_and_heads() {
    assert_eq!(body("let p = Point { x: 1.0, y: 2.0 }"), "(block (let p = (struct Point x: 1.0 y: 2.0)))");
    assert_eq!(body("voice.Config {}"), "(block tail (struct voice.Config))");
    // S-08: no struct literal in a head expression.
    assert_eq!(
        body("if s == Shape.Circle { 1 } else { 2 }"),
        "(block tail (if (== s (. Shape Circle)) (block tail 1) else (block tail 2)))"
    );
    assert_eq!(
        body("if f(Point { x: 1.0 }) { 1 } else { 2 }"),
        "(block tail (if (call f ((struct Point x: 1.0))) (block tail 1) else (block tail 2)))"
    );
    assert_eq!(body("while x { }"), "(block (while x (block)))");
}

#[test]
fn ranges_only_in_heads() {
    assert_eq!(body("for i in 0..<n { }"), "(block (for i in (range 0 ..< n) (block)))");
    assert_eq!(body("for i in 0..=n { }"), "(block (for i in (range 0 ..= n) (block)))");
    // Weaker than the binary operators (§3.1).
    assert_eq!(body("for i in a + 1..<n * 2 { }"), "(block (for i in (range (+ a 1) ..< (* n 2)) (block)))");
    assert_eq!(
        body("let s = par i in 0..<N { f~(i) }"),
        "(block (let s = (par i in 0..<N (block tail (call~ f (i))))))"
    );
    assert_eq!(
        body("let s = par i in 0..=N { f~(i) }"),
        "(block (let s = (par i in 0..=N (block tail (call~ f (i))))))"
    );
    // A range is the whole head (§3.1): in parentheses or an argument it
    // is outside the head (`range_outside_header`, E0002 with the note).
    let outside = |src: &str| {
        let p = parse(&format!("fn f() {{\n  {src}\n}}"));
        assert_eq!(codes_of(&p), [Code::E0002], "{src}");
        let d = &p.diagnostics[0];
        assert!(d.fixes.is_empty() && d.message.contains("`for` and `par` heads"), "{src}: {d:?}");
        assert!(d.notes.iter().any(|n| n.message.contains("xs.slice(from, to)")), "{src}: {d:?}");
        d.found.clone().unwrap_or_default()
    };
    assert_eq!(outside("let r = 0..<n"), "..<");
    assert_eq!(outside("let r = 0..=n"), "..=");
    assert_eq!(outside("let r = 0..n"), "..");
    assert_eq!(outside("let r = xs[1...3]"), "...");
    assert_eq!(outside("for i in (0..<4) { }"), "..<");
    assert_eq!(outside("for i in f(0..<3) { }"), "..<");
    assert_eq!(outside("while 0..<4 { }"), "..<");
    // A symbol after a range in a head: the general E0002, no candidate.
    let p = parse("fn f() {\n  for i in 0..<4..5 { }\n}");
    assert_eq!(codes_of(&p), [Code::E0002]);
    assert!(p.diagnostics[0].fixes.is_empty() && !p.diagnostics[0].message.contains("heads"), "{:?}", p.diagnostics);
    // The candidates of `..` for every end that starts an operand; none
    // for a range of one side (S-278).
    for end in ["n", "-n", "!n", "(n)", "[n][0]", "if c { 1 } else { 2 }", "match c { _ => 1 }", "'a'", "\"a\"", "_"] {
        let p = parse(&format!("fn f() {{\n  for i in 0..{end} {{ }}\n}}"));
        assert_eq!(p.diagnostics[0].code, Code::E0020, "{end}");
        assert_eq!(p.diagnostics[0].fixes.len(), 2, "{end}");
    }
    let p = parse("fn f() {\n  for i in 0.. { }\n}");
    assert!(p.diagnostics[0].fixes.is_empty(), "{:?}", p.diagnostics);
}

/// `starts_operand` is the set of tokens `parse_primary` and
/// `parse_prefix` read as the start of an operand.
#[test]
fn operand_starts() {
    let operands = [
        "-x",
        "!x",
        "1",
        "1.0",
        "'a'",
        "\"s\"",
        "true",
        "false",
        "_",
        "x",
        "self",
        "Self",
        "(x)",
        "[x]",
        "{ x }",
        "if c { 1 } else { 2 }",
        "match x { _ => 1 }",
        "fn(x: U32) -> U32 { x }",
        "unsafe { x }",
        "handle { x } with h",
        "par i in 0..<2 { x }",
    ];
    for src in operands {
        let p = parse(&format!("fn f() {{\n  let a = {src}\n}}"));
        let first = crate::lex(FileId(0), src).tokens.into_iter().find(|t| !t.kind.is_trivia()).unwrap();
        assert!(crate::starts::starts_operand(first.kind), "{src}");
        assert!(
            p.diagnostics.iter().all(|d| d.span.start as usize > "fn f() {\n  let a = ".len()),
            "{src}: {:?}",
            p.diagnostics
        );
    }
    for src in ["..<", "..", ".", ",", ")", "}", "=>", "+", "*", "move", "rt", "@", "<"] {
        let first = crate::lex(FileId(0), src).tokens.into_iter().find(|t| !t.kind.is_trivia()).unwrap();
        assert!(!crate::starts::starts_operand(first.kind), "{src}");
    }
}

#[test]
fn struct_pattern_rest_dots() {
    // `..` last is read (S-366: the stage that counts the fields reports it);
    // `...`, and `..` before another field, are no struct pattern.
    let p = parse("struct P { x: U32, y: U32 }\nfn f(p: P) -> U32 {\n  match p {\n    P { x: a, .. } => a\n  }\n}");
    assert_eq!(codes_of(&p), [], "{:?}", p.diagnostics);
    for rest in ["x: a, ...", ".., x: a", "x: a, ..,"] {
        let p = parse(&format!(
            "struct P {{ x: U32, y: U32 }}\nfn f(p: P) -> U32 {{\n  match p {{\n    P {{ {rest} }} => a\n  }}\n}}"
        ));
        assert_eq!(codes_of(&p), [Code::E0002], "{rest}");
    }
}

#[test]
fn precedence() {
    assert_eq!(body("-x.abs()"), "(block tail (neg (call (. x abs) ())))");
    assert_eq!(body("-x as F64"), "(block tail (as (neg x) F64))");
    assert_eq!(body("a + (x as F64)"), "(block tail (+ a ((as x F64))))");
    assert_eq!(body("x?.y"), "(block tail (. (try x) y))");
}

#[test]
fn patterns() {
    assert_eq!(body("let (a, b) = p"), "(block (let (tuple a b) = p))");
    assert_eq!(
        body("match v { Some(x) if x > 0 => x, None => 0, }"),
        "(block tail (match v Some(x) if (> x 0) => x None => 0))"
    );
    assert_eq!(
        body("match v { Point { x: px, y: _ } => px, _ => 0 }"),
        "(block tail (match v Point { x: px, y: _ } => px _ => 0))"
    );
    assert_eq!(
        body("match n { 1 | 2 => a, -1 => b, 'c' => d, _ => e }"),
        "(block tail (match n (1 | 2) => a -1 => b 'c' => d _ => e))"
    );
    assert_eq!(
        body("match s { Shape.Circle(r) => r, Shape.Rect(w, h) => w }"),
        "(block tail (match s Shape.Circle(r) => r Shape.Rect(w, h) => w))"
    );
}

#[test]
fn items() {
    // The derived traits at the head (§6.4, S-34).
    let src = "/// doc\n@repr(c)\npub struct Key[T: PartialOrd + Eq, const N: U32, e]: PartialEq + Eq {\n  id: U32,\n  xs: [T; N],\n}\n";
    assert_eq!(
        dump(&parse(src).ast),
        "(@repr(c) pub struct Key[T: PartialOrd + Eq, const N: U32, effect e]: PartialEq + Eq repr(c)\n  id: U32\n  xs: [T; N])\n"
    );
    let src = "pub fn map[T, U, e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e} { xs }";
    assert_eq!(
        dump(&parse(src).ast),
        "(pub fn map[T, U, effect e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e}\n  (block\n    tail xs))\n"
    );
    let src = "priv type S = Buf[F32]\nconst X: (U32, F32) = (1, 2.0)\nuse a.b.{c, d}\ntest \"t\" { assert true }";
    let d = dump(&parse(src).ast);
    assert!(
        d.starts_with("(priv type S = Buf[F32])\n(const X: (U32, F32) = (tuple 1 2.0))\n(use a.b.{c, d})\n(test \"t\""),
        "{d}"
    );
    let src = "pub trait Show {\n  fn show(self) -> Str uses {Alloc}\n  const ZERO: Self\n}\nimpl Show for Point {\n  fn show(self) -> Str uses {Alloc} { \"({self.x}, {self.y})\" }\n}";
    let p = parse(src);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    assert!(dump(&p.ast).contains("(block\n      tail \"({self.x}, {self.y})\"))"));
    let src = "handler arena(inout mem: Span[U8]): Alloc {\n  fn alloc(n: U32) -> U32 { n }\n}\nfn g() { handle { f() } with arena(inout scratch) }\nfn h() { handle { f() } with Fs { fn read(_: Path) -> Str { \"\" } } }";
    let p = parse(src);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
}

/// The members of a list of declarations are a closed list (§18.1,
/// S-263): any other declaration there is E0002, so declarations do not
/// nest without bound (they count no level, spec §2.5): the 10 000
/// nested `impl`s stop at the second one.
#[test]
fn members_are_a_closed_list() {
    for kw in [
        "impl B",
        "trait T",
        "effect E",
        "blocking effect E",
        "handler h: E",
        "extern \"C\" lib \"x\"",
        "struct S",
        "enum E",
        "flow g(x: Sig[F32]) -> Sig[F32]",
        "proc g(x: Sig[F32]) -> Sig[F32]",
        "test \"t\"",
    ] {
        assert_eq!(codes(&format!("impl A {{\n  {kw} {{\n  }}\n}}\n")), vec![Code::E0002], "{kw}");
    }
    for member in ["use a.{b}", "type T = I32", "target fn f()"] {
        assert_eq!(codes(&format!("impl A {{\n  {member}\n}}\n")), vec![Code::E0002], "{member}");
    }
    assert_eq!(codes("effect E {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
    assert_eq!(codes("handler h: E {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
    assert_eq!(codes("extern \"C\" lib \"x\" {\n  const C: I32 = 1\n}\n"), vec![Code::E0002]);
    assert!(codes("impl A {\n  const C: I32 = 1\n  fn f() { }\n  rt fn g() { }\n}\n").is_empty());
    assert!(codes("trait T {\n  const C: Self\n  fn f(self)\n}\n").is_empty());
    assert!(codes("extern \"C\" lib \"x\" {\n  type Raw\n  rt fn f(h: Ptr[Raw])\n}\n").is_empty());
    let p = parse("impl A {\n  struct S { x: I32 }\n}\n");
    assert_eq!(p.diagnostics[0].notes.len(), 1, "the note with the members");
    let deep = format!("{}{}", "impl A { ".repeat(10_000), "}".repeat(10_000));
    assert_eq!(codes(&deep), vec![Code::E0002]);
}

/// The height of a binary chain is the one of the tree of §3.1 (spec §2.5).
#[test]
fn chain_heights_follow_the_strengths() {
    use crate::ast::OpGroup::*;
    let height = |first: u32, rest: &[(crate::ast::OpGroup, u32)]| {
        let mut c = crate::parser::Chain::new(first);
        for &(g, h) in rest {
            c.operator(g);
            c.operand(h);
        }
        c.height()
    };
    // a + b + c: ((a + b) + c)
    assert_eq!(height(0, &[(Additive, 0), (Additive, 0)]), 2);
    // a + b * c * d: a + ((b * c) * d)
    assert_eq!(height(0, &[(Additive, 0), (Multiplicative, 0), (Multiplicative, 0)]), 3);
    // a * b + c * d: (a * b) + (c * d)
    assert_eq!(height(0, &[(Multiplicative, 0), (Additive, 0), (Multiplicative, 0)]), 2);
    // lo <= x && x < hi: (lo <= x) && (x < hi)
    assert_eq!(height(0, &[(Comparison, 0), (And, 0), (Comparison, 0)]), 2);
    // a deep operand on the right of the last operator
    assert_eq!(height(0, &[(Additive, 0), (Additive, 5)]), 6);
    // the strengths of §3.1
    assert!(Multiplicative.stronger(Additive) && Additive.stronger(Comparison) && Comparison.stronger(Or));
    assert!(!And.stronger(Or) && !Or.stronger(And) && !Bitwise.stronger(Or) && !Additive.stronger(Bitwise));
    assert!(!Additive.stronger(Multiplicative) && !Additive.stronger(Additive));
}

#[test]
fn signatures_without_bodies() {
    assert!(codes("extern \"C\" lib \"x\" {\n  type Raw\n  rt fn f(h: Ptr[Raw]) uses {Alloc}\n}").is_empty());
    assert_eq!(codes("extern \"C\" lib \"x\" {\n  fn f() { }\n}"), vec![Code::E0002]);
    assert!(codes("target type Device\ntarget rt fn read(inout d: Device)").is_empty());
    assert_eq!(codes("fn f()\nfn g() { }"), vec![Code::E0002]);
    assert_eq!(codes("effect Log {\n  rt fn info(msg: Str)\n}"), vec![]);
}

#[test]
fn a_form_of_another_language_fails_its_unit() {
    // R-87 (4): the first form stops the unit (the table of the forms,
    // `crate::foreign`, makes the diagnostic); the next unit is read.
    let p = parse("fn f() {\n  let x = 1;\n  let y = 2;\n}\nfn g(x: i32, y: i32) { }\nfn h() { }\n");
    assert_eq!(codes_of(&p), [Code::E0020, Code::E0020]);
    let d = dump(&p.ast);
    assert!(d.contains("(failed:body fn f()") && d.contains("(fn h()"), "{d}");
    assert_eq!(codes("fn f() {\n  for i in 0..n { }\n}"), vec![Code::E0020]);
}

#[test]
fn first_error_per_item_and_recovery() {
    let src = "fn a() {\n  let = 1\n  let = 2\n}\nfn b() { 1 }\nfn c() {\n  )\n}\n";
    let p = parse(src);
    let lines: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
    // One parse error per unit: the parser stops at the first one of `a` (S-59).
    assert_eq!(p.diagnostics.len(), 2, "{lines:?}");
    // The failed items stay, by their name, with their body unread (R-71).
    assert_eq!(
        dump(&p.ast),
        "(failed:body fn a()\n  <error>)\n(fn b()\n  (block\n    tail 1))\n(failed:body fn c()\n  <error>)\n"
    );
    // The diagnostics are not reduced here (the driver chooses one per unit).
    let p = parse("fn a() {\n  let s = \"abc\n  let = 1\n}");
    assert_eq!(p.diagnostics[0].code, Code::E0001);
}

#[test]
fn an_unclosed_brace_ends_at_an_item_keyword_indented_as_its_line() {
    // §18.1: the E0002 is at the `{` that is never closed, with a note on the declaration;
    // the error at the next item is that brace, and `g` is read.
    let src = "fn f() -> I32 {\n  if c {\n    1\n  }\nfn g() {}\n";
    let p = parse(src);
    let ds: Vec<(Code, &str)> =
        p.diagnostics.iter().map(|d| (d.code, &src[d.span.start as usize..d.span.end as usize])).collect();
    assert_eq!(ds, [(Code::E0002, "{")]);
    assert_eq!(p.diagnostics[0].span.start, 14);
    let note = p.diagnostics[0].notes.iter().find(|n| n.span.is_some()).unwrap();
    assert_eq!(note.message, "it is in the body of `f`");
    assert!(dump(&p.ast).contains("(fn g()"));
    // A line indented deeper than the `{` is not a place to end it.
    let p = parse("fn f() -> I32 {\n  1 +\n    fn g() {}\n");
    assert!(p.diagnostics.iter().all(|d| d.message != "this `{` is never closed"));
    // In an `impl`, by the member.
    let src = "impl P {\n  fn a(self) {\n    1\n\n  fn b(self) {}\n}\nfn c() {}\n";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1);
    assert_eq!(&src[p.diagnostics[0].span.start as usize..][..1], "{");
    assert_eq!(p.diagnostics[0].span.start, 22);
    let d = dump(&p.ast);
    assert!(d.contains("fn b(self)") && d.contains("(fn c()"), "{d}");
}

#[test]
fn the_recovery_does_not_start_a_unit_on_a_continued_line() {
    // S-47: after a line that ends with `=`, a line that starts with `fn`
    // goes on with it (a function type), so the skip of the unit with the
    // error does not end there; it ends at `fn g`.
    let p = parse("type Op = ? =\nfn(I32) -> I32\nfn g() {}\n");
    assert_eq!(codes_of(&p), [Code::E0002], "{:?}", p.diagnostics);
    assert!(dump(&p.ast).contains("(fn g()"));
    // A line that does not go on is the next unit, as before.
    let p = parse("type Op = ?\nfn g() {}\n");
    assert_eq!(codes_of(&p), [Code::E0002]);
    assert!(dump(&p.ast).contains("(fn g()"));
}

#[test]
fn an_unclosed_list_of_members_ends_at_an_item_keyword_indented_as_its_line() {
    // The `{` of the `impl` is never closed: `after` is an item of the file (§18.1).
    let src = "impl S {\n  fn m(self) -> I32 {\n    1\n  }\n\nfn after() -> I32 { 5 }\n";
    let p = parse(src);
    let ds: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
    assert_eq!(ds, [(Code::E0002, 7)]);
    assert!(dump(&p.ast).contains("\n(fn after()"), "{}", dump(&p.ast));
    // The member's `{` is not closed either: the innermost is reported, once.
    let src = "impl S {\n  fn m(self) -> I32 {\n    1\n\nfn after() -> I32 { 5 }\n";
    let p = parse(src);
    let ds: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
    assert_eq!(ds, [(Code::E0002, 29)]);
    assert!(dump(&p.ast).contains("\n(fn after()"), "{}", dump(&p.ast));
    // A correct program whose members are not indented reads as before.
    assert!(codes("impl S {\nfn m(self) -> I32 { 1 }\n}\n").is_empty());
}

#[test]
fn an_unclosed_parenthesis_ends_at_an_item_keyword_indented_as_its_line() {
    // S-280: an item keyword indented deeper than the line of an open `(` is not the end.
    let src = "pub flow v(\n  g: Sig[F32] oops,\n  @param(min: 1.0)\n  f0: Ctl[F32],\n) -> Sig[F32] {\n  g\n}\nfn after() -> I32 { 1 }\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0002]);
    assert!(dump(&p.ast).contains("(fn after()"));
    // One at the indentation of its line ends it, and the `(` is reported.
    let src = "fn f(a: I32,\nfn g() {}\n";
    let p = parse(src);
    assert_eq!(p.diagnostics.iter().map(|d| d.message.as_str()).collect::<Vec<_>>(), ["this `(` is never closed"]);
    assert!(dump(&p.ast).contains("(fn g()"));
}

#[test]
fn an_unclosed_brace_at_the_end_of_the_file() {
    // The reading stopped at the end of the file: the `{` of `f` is the error.
    let src = "fn f() -> I32 {\n  if c {\n    1\n  }\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0002]);
    assert_eq!(p.diagnostics[0].span.start, 14);
    // Another error stopped it earlier: the open `{` follow from it, no diagnostic.
    let p = parse("fn f() -> I32 {\n  let = 1\n");
    assert_eq!(p.diagnostics.iter().map(|d| d.message.as_str()).collect::<Vec<_>>(), ["expected a pattern, found `=`"]);
}

#[test]
fn a_member_is_a_unit_of_the_recovery() {
    // S-59: an error in a member does not stop the list.
    let p = parse("impl P {\n  fn a(self) {\n    let = 1\n  }\n  fn b(self) {\n    let = 2\n  }\n}\n");
    assert_eq!(codes_of(&p), [Code::E0002, Code::E0002]);
    // `fn name` is not a closure: the error is at the `fn`, where the next unit starts.
    let p = parse("fn f() {\n  let x = 1\nfn g() {}\n");
    assert!(dump(&p.ast).contains("(fn g()"), "{}", dump(&p.ast));
    // The tokens after an item on its line are its unit's (S-274); the next line is not.
    let p = parse("fn a() {} ) ]\nfn b() {}\n");
    assert!(dump(&p.ast).contains("(fn b()"));
    assert_eq!(codes_of(&p), [Code::E0002]);
}

fn codes_of(p: &crate::Parsed) -> Vec<Code> {
    p.diagnostics.iter().map(|d| d.code).collect()
}

#[test]
fn literals() {
    assert_eq!(body("let s = \"a\\nb {{x}} {p.q}\""), "(block (let s = \"a\\nb {{x}} {p.q}\"))");
    assert_eq!(body("let c = '\\u{1F600}'"), "(block (let c = '\\u{1f600}'))");
    assert_eq!(body("let n = 0xFF + 1_000"), "(block (let n = (+ 255 1000)))");
    assert_eq!(codes("fn f() {\n  let n = 99999999999999999999\n}"), vec![Code::E0408]);
    assert_eq!(body("Ok(())"), "(block tail (call Ok ((tuple))))");
}

#[test]
fn closures_and_args() {
    assert_eq!(body("xs.map(fn(x) { x * 2.0 })"), "(block tail (call (. xs map) ((fn(x) (block tail (* x 2.0))))))");
    assert_eq!(body("f(inout a, move b, inout [c, d])"), "(block tail (call f (inout a, move b, inout [c, d])))");
    assert_eq!(
        body("fn(move v: S) -> U64 uses {Sync} { v }"),
        "(block tail (fn(move v: S) -> U64 uses {Sync} (block tail v)))"
    );
}

#[test]
fn move_in_consuming_positions() {
    // S-21 (§5.2): `move x` as an expression form.
    let src = "fn f(move b: Buf[F32]) {\n  let y = move b\n  var v = move y\n  v = move b\n  let t = (move v, 1)\n  let a = [move b, move v]\n  let s = Box { b: move b }\n  match move b {\n    _ => 1,\n  }\n  take(move b)\n}\n";
    assert!(codes(src).is_empty(), "{:?}", crate::parse(FileId(0), src).diagnostics);
    let d = crate::dump(&crate::parse(FileId(0), src).ast);
    assert!(d.contains("(let y = (move b))"), "{d}");
    assert!(d.contains("(match (move b)"), "{d}");
    // Where the function returns and on the last expression of a block (S-100).
    assert!(codes("fn f(move b: U32) -> U32 {\n  return move b\n}\n").is_empty());
    assert!(codes("fn f(move b: U32) -> U32 {\n  move b\n}\n").is_empty());
    assert!(codes("fn f(c: Bool, move b: U32) -> U32 {\n  let y = if c { move b } else { 1 }\n  y\n}\n").is_empty());
    // Elsewhere it is E0002: an operand, a head, a group, a statement that is no block's last.
    assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = 1 + move b\n  y\n}\n"), vec![Code::E0002]);
    assert_eq!(codes("fn f(move b: Bool) -> U32 {\n  if move b { 1 } else { 2 }\n}\n"), vec![Code::E0002]);
    assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = (move b)\n  y\n}\n"), vec![Code::E0002]);
    assert_eq!(codes("fn f(move b: U32) -> U32 {\n  move b\n  1\n}\n"), vec![Code::E0002]);
}

#[test]
fn a_reserved_word_is_e0200_where_it_is_read() {
    // §2.2, S-169, S-279, S-371: the E0200 at the word, wherever it is
    // read, and no E0002 there.
    for (src, word) in [
        ("fn f() {\n  let when = 1\n}\n", "when"),
        ("fn ser() {\n}\n", "ser"),
        ("fn f(reset_if: I32) {\n}\n", "reset_if"),
        ("struct S {\n  clock: I32,\n}\n", "clock"),
        ("use std.math.{clock}\n", "clock"),
        ("flow f(x: F32 at clock) -> F32 at sample {\n  x\n}\n", "clock"),
        ("flow f(x: F32) -> F32 {\n  let y = x + prev~(^clock)\n  y\n}\n", "clock"),
        ("fn f() {\n  when\n}\n", "when"),
        ("clock fast = sample / 32\n", "clock"),
        ("fn f(x: I32) {\n  x when 1\n}\n", "when"),
    ] {
        let p = parse(src);
        let d: Vec<(Code, &str)> =
            p.diagnostics.iter().map(|d| (d.code, &src[d.span.start as usize..d.span.end as usize])).collect();
        assert_eq!(d, vec![(Code::E0200, word)], "{src}");
    }
    // After a `.` and at the head of the path of a `use`, a name (S-357, S-20, S-37).
    for src in ["fn f(s: S) -> I32 {\n  s.clock\n}\n", "use clock.{x}\n", "use test.{Gen}\n", "use a.ser.{x}\n"] {
        assert_eq!(codes(src), vec![], "{src}");
    }
}

/// The words before a head are one E0002 with its note, and the member is
/// read on, in every list whose members are units (§18.1, S-459, S-493):
/// the operations of an `effect` and the functions of a handler written in
/// place too.
#[test]
fn a_member_of_an_effect_and_of_a_handler_in_place_is_read_on_after_words() {
    use crate::ast::ItemKind;
    for src in [
        "effect Ask {\n  public fn ask() -> I32\n}\n",
        "fn f() -> I32 {\n  handle { ask() } with Ask {\n    public fn ask() -> I32 { 1 }\n  }\n}\n",
    ] {
        let p = parse(src);
        let [d] = p.diagnostics.as_slice() else { panic!("{src}: {:?}", p.diagnostics) };
        assert_eq!((d.code, &src[d.span.start as usize..d.span.end as usize]), (Code::E0002, "public"), "{src}");
        assert!(d.notes.iter().any(|n| n.span.is_none() && n.message.contains("§18.1")), "{src}: {d:?}");
        let read = p.ast.items.iter().any(|i| matches!(&i.kind, ItemKind::Fn(f) if f.name.name == "ask"));
        assert!(read, "{src}: the member is not read on");
    }
}

#[test]
fn a_head_read_on_keeps_what_was_written_right() {
    // §18.1, S-435, S-464, S-482: the head is read on after a form that ends on
    // its line; the declaration is read whole, the modifiers written are
    // recorded, and a visibility of another language or two that disagree are
    // the default.
    use crate::ast::{ItemKind, Vis};
    let src = "rt pub fn a() {}\npub(crate) fn b() {}\npriv pub fn c() {}\nexport pub fn d() {}\nconst fn e() {}\n\
               #[inline] priv fn f() {}\n@fp(relaxed, 1 +) fn g() {}\n";
    let p = parse(src);
    assert_eq!(p.ast.root.len(), 7, "{:?}", p.diagnostics);
    let heads: Vec<(String, Vis, bool)> = p
        .ast
        .root
        .iter()
        .map(|&i| {
            let item = p.ast.item(i);
            let ItemKind::Fn(f) = &item.kind else { unreachable!() };
            (f.name.name.clone(), item.vis, f.rt)
        })
        .collect();
    let want = [
        ("a", Vis::Pub, true),
        ("b", Vis::Default, false),
        ("c", Vis::Default, false),
        ("d", Vis::Pub, false),
        ("e", Vis::Default, false),
        ("f", Vis::Priv, false),
        ("g", Vis::Default, false),
    ];
    let want: Vec<(String, Vis, bool)> = want.iter().map(|&(n, v, rt)| (n.to_string(), v, rt)).collect();
    assert_eq!(heads, want);
    // One diagnostic of the syntax stage for each, and every unit is an item's.
    assert_eq!(p.diagnostics.len(), 7, "{:?}", p.diagnostics);
    assert!(p.units.list.iter().all(|u| u.item.is_some()), "{:?}", p.units.list);
    // A form that does not end on its line is not read on; after a line break
    // after it, the declaration is a unit of its own.
    for src in ["pub(crate fn a() {}\n", "const unsafe fn a() {}\n"] {
        assert!(parse(src).ast.root.is_empty(), "{src:?}");
    }
    for src in ["pub(crate)\nfn a() {}\n", "export\nfn a() {}\n"] {
        let p = parse(src);
        let items: Vec<bool> = p.units.list.iter().map(|u| u.item.is_some()).collect();
        assert_eq!(items, [false, true], "{src:?}");
    }
}
