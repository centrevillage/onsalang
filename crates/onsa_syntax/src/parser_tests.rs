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
        body("let s = par~ i in 0..<N { f~(i) }"),
        "(block (let s = (par~ i in 0..<N (block tail (call~ f (i))))))"
    );
    assert_eq!(
        body("let s = par~ i in 0..=N { f~(i) }"),
        "(block (let s = (par~ i in 0..=N (block tail (call~ f (i))))))"
    );
    // A range is the whole head (§3.1): in parentheses or an argument it
    // is outside the head (`range_outside_header`, E0002 with the note).
    let outside = |src: &str| {
        let p = parse(&format!("fn f() {{\n  {src}\n}}"));
        assert_eq!(codes_of(&p), [Code::E0002], "{src}");
        let d = &p.diagnostics[0];
        assert!(d.fixes.is_empty() && d.message.contains("`for` and `par~` heads"), "{src}: {d:?}");
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
        "par~ i in 0..<2 { x }",
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
fn struct_pattern_rest_marks() {
    // `_` and `..` last are read (S-903; S-366: the stage that counts the
    // fields reports the `..`); `...`, a mark before another field and a `,`
    // after one are no struct pattern.
    for rest in ["x: a, ..", "..", "x: a, _", "_"] {
        let p = parse(&format!(
            "struct P {{ x: U32, y: U32 }}\nfn f(p: P) -> U32 {{\n  match p {{\n    P {{ {rest} }} => a\n  }}\n}}"
        ));
        assert_eq!(codes_of(&p), [], "{rest}: {:?}", p.diagnostics);
    }
    let bad = ["x: a, ...", ".., x: a", "x: a, ..,", "_, x: a", "x: a, _,", "_: a", "_ x: a", "_, _", "_, ..", ".., _"];
    for rest in bad {
        let p = parse(&format!(
            "struct P {{ x: U32, y: U32 }}\nfn f(p: P) -> U32 {{\n  match p {{\n    P {{ {rest} }} => a\n  }}\n}}"
        ));
        assert_eq!(codes_of(&p), [Code::E0002], "{rest}");
    }
}

#[test]
fn no_comma_goes_after_a_struct_pattern_rest() {
    // The `,` would leave an E0002 (§7, S-903): the mark is last.
    let fixes = |rest: &str| {
        let p =
            parse(&format!("struct P {{ x: U32, y: U32 }}\nfn f(p: P) -> U32 {{\n  let P {{ {rest} }} = p\n  1\n}}"));
        assert_eq!(codes_of(&p), [Code::E0002], "{rest}");
        p.diagnostics[0].fixes.len()
    };
    for rest in ["_ x: a", ".. x: a", "_ _", "_ ..", ".. _"] {
        assert_eq!(fixes(rest), 0, "{rest}");
    }
    // Before the mark it goes.
    assert_eq!(fixes("x: a _"), 1);
}

#[test]
fn struct_pattern_rest_keeps_its_mark() {
    // The dump prints the mark as written (S-903).
    assert_eq!(body("let P { x: a, _ } = p"), "(block (let P { x: a, _ } = p))");
    assert_eq!(body("let P { _ } = p"), "(block (let P { _ } = p))");
    assert_eq!(body("let P { x: a, .. } = p"), "(block (let P { x: a, .. } = p))");
}

#[test]
fn a_literal_and_a_field_keep_their_rest_and_default() {
    // The dump prints them (§4.4, S-697): the comparison of `diff` reads it.
    assert_eq!(body("P { x: 1, ... }"), "(block tail (struct P x: 1 ...))");
    assert_eq!(body("P { ... }"), "(block tail (struct P ...))");
    let p = parse("struct P {\n  x: U32 = 1 + 2,\n  y: F32,\n}\n");
    assert_eq!(codes_of(&p), []);
    assert!(crate::dump::dump(&p.ast).contains("x: U32 = (+ 1 2)\n"), "{}", crate::dump::dump(&p.ast));
}

#[test]
fn no_comma_goes_after_a_struct_literal_rest() {
    // The `,` would leave an E0002 (§4.4): the mark is last. `x: 1 ...` reads
    // the `...` of an expression, which has no candidate.
    let fixes = |list: &str| {
        let p = parse(&format!("fn f() -> P {{\n  P {{\n    {list}\n  }}\n}}"));
        assert_eq!(codes_of(&p), [Code::E0002], "{list}");
        p.diagnostics[0].fixes.len()
    };
    assert_eq!(fixes("x: 1, ... y: 2"), 0);
    assert_eq!(fixes("... ..."), 0);
    assert_eq!(fixes("x: 1 ..."), 0);
}

#[test]
fn the_base_of_a_literal_is_read_where_a_field_starts() {
    // `..` as an element is the row; as a value of a field it is no base.
    let note = |list: &str| {
        let p = parse(&format!("fn f() -> P {{\n  P {{ {list} }}\n}}"));
        assert_eq!(codes_of(&p), [Code::E0002], "{list}");
        p.diagnostics[0].notes.iter().any(|n| n.message.contains("`...`"))
    };
    for list in ["..", "x: 1, ..", "..v", "x: 1, ..v", "..Default::default()"] {
        assert!(note(list), "{list}");
    }
    assert!(!note("x: ..v"));
    assert!(!note("x: 1 .. v"));
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
    for member in ["use a.{b}", "type T = I32", "target type T", "target const C: I32 = 1"] {
        assert_eq!(codes(&format!("impl A {{\n  {member}\n}}\n")), vec![Code::E0002], "{member}");
    }
    // A `target fn` is a member of an `impl` (§15.2, S-661), and of no other list.
    for owner in ["trait T", "effect E", "handler h: E", "extern \"C\" lib \"x\""] {
        assert_eq!(codes(&format!("{owner} {{\n  target fn f()\n}}\n")), vec![Code::E0002], "{owner}");
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
        let mut c = crate::parser::ChainHeight::new(first);
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

/// A `target fn` (§15.2, S-661, S-669): no body in braces, and a body after an `else` on the
/// line of the last token of its heading, at the top level and in an `impl` (a trait
/// implementation too), in the files of every package.
#[test]
fn a_target_fn_takes_a_body_after_else_on_the_line_of_its_heading() {
    for src in [
        "target fn f() -> I32 else { 1 }\n",
        "pub target rt fn f[T: Num](x: T) -> T uses {Log} else {\n  x\n}\n",
        "impl A {\n  target fn f(self) -> I32\n  target rt fn g(self) -> I32 else { 1 }\n}\n",
        "impl Tr for A {\n  target fn f(self) -> I32 else { 1 }\n}\n",
    ] {
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{src}: {:?}", p.diagnostics);
    }
    // The body is the declaration's (the AST and the CST).
    let p = parse("target fn f() -> I32 else { 1 }\n");
    let crate::ast::ItemKind::Target(inner) = &p.ast.item(p.ast.root[0]).kind else { panic!("no target") };
    assert!(matches!(&**inner, crate::ast::ItemKind::Fn(f) if f.body.is_some()));
    let tree = p.cst.tree("target fn f() -> I32 else { 1 }\n");
    assert!(tree.contains("KwElse") && tree.contains("Block"), "{tree}");
    // An `else` on the next line: E0003 at it, whose candidate moves it up.
    let src = "target fn f() -> I32\nelse { 1 }\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0003]);
    assert_eq!(p.diagnostics[0].message, "`else` must be on the line of the declaration's heading");
    assert_eq!(p.diagnostics[0].span.start as usize, src.find("else").unwrap());
    assert_eq!(fixed(src), "target fn f() -> I32 else { 1 }\n");
    assert_eq!(
        fixed("impl A {\n  target fn f() // c\n  else { 1 }\n}\n"),
        "impl A {\n  target fn f() else { 1 } // c\n}\n"
    );
    // The kinds of `target` out of their places (the table of the declarations): the E0002 at
    // `target`, named by its kind.
    let top = "; declare it at the top level of the module";
    let value = "there is no `target const`; write the associated constant with its value (`const C: F32 = 0.0 / 0.0`)";
    for (src, message) in [
        ("impl A {\n  target type T\n}\n", format!("`target type` cannot be declared in an `impl`{top}")),
        ("trait T {\n  target fn f()\n}\n", format!("`target fn` cannot be declared in a `trait`{top}")),
        ("impl A {\n  target const C: I32 = 1\n}\n", value.to_string()),
        ("trait T {\n  target const C: I32\n}\n", value.to_string()),
    ] {
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002], "{src}");
        assert_eq!(p.diagnostics[0].message, message, "{src}");
        assert_eq!(p.diagnostics[0].span.start as usize, src.find("target").unwrap(), "{src}");
    }
    // A body in braces is E0002 in every package and place.
    for src in ["target fn f() -> I32 { 1 }\n", "impl A {\n  target fn f() { }\n}\n"] {
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002], "{src}");
        assert_eq!(p.diagnostics[0].message, "this declaration is a signature and takes no body", "{src}");
    }
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
    // A line indented deeper than the `{` is not a place to end it, and the
    // `{` is reported at the end of the file all the same (S-943, R-371).
    let p = parse("fn f() -> I32 {\n  1 +\n    fn g() {}\n");
    assert_eq!(p.diagnostics.last().unwrap().message, "this `{` is never closed");
    assert_eq!(p.diagnostics.last().unwrap().span.start, 14);
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
fn the_recovery_does_not_start_a_unit_at_fn_and_a_parenthesis() {
    // S-947: `fn(` and `rt fn(` (a function type, an anonymous function) have
    // no name and start no item, on a line that goes on with the one before
    // or not, `fn (` too: the skip of the unit with the error ends at `fn g`.
    for src in [
        "type Op = ? =\nfn(I32) -> I32\nfn g() {}\n",
        "type Op = ?\nfn(I32) -> I32\nfn g() {}\n",
        "type Op = ? =\nfn (I32) -> I32\nfn g() {}\n",
        "type Op = ?\nrt fn /* c */ (I32) -> I32\nfn g() {}\n",
    ] {
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002], "{src:?}: {:?}", p.diagnostics);
        assert!(dump(&p.ast).contains("(fn g()"), "{src:?}");
    }
    // A line that does not go on is the next unit, as before, and so is one
    // that goes on, at an item (`fn z`, S-947).
    for src in ["type Op = ?\nfn g() {}\n", "type Op = ? =\nfn g() {}\n"] {
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002], "{src:?}");
        assert!(dump(&p.ast).contains("(fn g()"), "{src:?}");
    }
}

#[test]
fn the_recovery_ends_at_an_item_on_a_continued_line_and_after_a_type_cut() {
    // S-947, R-396, S-950: an item at the head of a line that goes on with
    // the line before ends the unit with the error; the reading of a type
    // fails at the `fn` (`rt`) of `fn z`; the tokens after an item end at
    // the end of a line that goes on there too. One E0002, and `z` is read.
    for src in [
        "fn f() -> I32 {\n  let y = x *\nfn z() -> I32 { 1 }\n",
        "fn f() -> I32 {\n  let g = fn(x: I32) ->\nfn z() -> I32 { 1 }\n",
        "struct P {\n  v:\nrt fn z() -> I32 { 1 }\n",
        "type Op =\nfn z() -> I32 { 1 }\n",
        "pub type Op = I32 =\nfn(I32) -> I32\nfn z() -> I32 { 1 }\n",
        "pub type Op = I32 =\nfn z() -> I32 { 1 }\n",
    ] {
        let p = parse(src);
        assert_eq!(codes_of(&p), [Code::E0002], "{src:?}: {:?}", p.diagnostics);
        assert!(dump(&p.ast).contains("fn z()"), "{src:?}: {}", dump(&p.ast));
    }
}

/// A sample of the grid of the breaking side of W5-11 U9 (S-947, R-396,
/// S-950): a unit cut at the end of a line, after a token that goes on (§2.5)
/// or a `,` in a bracket, in one of the contexts, and at the head of the next
/// line the head of an item `z`, then an item `w` that uses it. The unit ends
/// at the head of `z` (a run of words before a head, an attribute or a doc
/// comment included, the first of their lines, §18.1), so `z` and `w` are
/// items of the file, and the tree holds the text as it is. The pairs
/// of a context and a head are fixed; the whole grid is the breaking side's.
#[test]
fn an_item_after_a_cut_line_is_read_on_a_sample_of_contexts_and_heads() {
    let contexts = [
        "fn f() -> I32 {\n  let y = x {T}\n",
        "fn f() -> I32 {\n  x {T}\n",
        "fn f(a: I32) -> I32 {\n  match a {\n    A |\n",
        "fn f() -> I32 {\n  let (x |\n",
        "fn f(a: I32) -> I32 {\n  match a {\n    A => x {T}\n",
        "fn f(a: I32) -> I32 {\n  match a {\n    A if b {T}\n",
        "pub type Op = I32 {T}\n",
        "fn f(a: I32 {T}\n",
        "fn f() -> I32 {T}\n",
        "struct S {\n  a: I32 {T}\n",
        "const K: I32 = 1 {T}\n",
        "fn f() -> I32 {\n  if a {T}\n",
        "fn f() -> I32 {\n  for i in 0 {T}\n",
        "impl P {\n  fn m(self) -> I32 {\n    x {T}\n",
        "fn f() -> I32 {\n  let y = [1,\n",
        "fn f() -> I32 {\n  let y = g(1,\n",
    ];
    let tokens = ["*", "|", "=", "->", "..<", "&&", "+%", ">>", "==", "&"];
    let heads = [
        "export fn z() {}",
        "unsafe fn z() {}",
        "export \"C\" fn z() {}",
        "foo fn z() {}",
        "foo bar fn z() {}",
        "static fn z() {}",
        "pub fn z() {}",
        "fn z() {}",
        "rt fn z() {}",
        "/// d\nfn z() {}",
        "@fp(relaxed)\nfn z() {}",
        "/// d\n@fp(relaxed)\nfn z() {}",
        "@export\n@fp(relaxed)\npub fn z() {}",
    ];
    let mut cases = 0;
    for (c, context) in contexts.iter().enumerate() {
        for (h, head) in heads.iter().enumerate().filter(|(h, _)| (c + h) % 2 == 0) {
            let src =
                format!("{}{head}\nfn w() {{ z() }}\n", context.replace("{T}", tokens[(3 * c + h) % tokens.len()]));
            let p = parse(&src);
            let items: Vec<(&str, usize)> = (p.ast.root.iter())
                .filter_map(|&id| match &p.ast.item(id).kind {
                    crate::ast::ItemKind::Fn(f) => Some((f.name.name.as_str(), p.ast.item(id).attrs.len())),
                    _ => None,
                })
                .collect();
            // `z` with its attributes, and its doc comment documents it (no E0004).
            let z = (items.iter()).any(|&(name, attrs)| name == "z" && attrs == head.matches('@').count());
            let documented = !p.diagnostics.iter().any(|d| d.code == Code::E0004);
            assert!(z && documented && items.iter().any(|i| i.0 == "w"), "{src:?}: {items:?} {:?}", p.diagnostics);
            // The tree holds the text as it is (what the reading undone left).
            assert_eq!(p.cst.text(&src), src);
            p.cst.validate(&src).unwrap_or_else(|e| panic!("{src:?}: {e:?}"));
            cases += 1;
        }
    }
    assert_eq!(cases, 104);
}

#[test]
fn the_recovery_does_not_end_a_unit_at_the_line_of_the_head_it_read() {
    // S-947: the line of the head after its attributes does not go on with
    // the line before (§2.5): it is of the unit read, which ends at the next
    // item, two units in all.
    for src in ["@fp(relaxed)\npub fn z( {\nfn w() {}\n", "#[derive(Eq)]\npub struct {\n  id: U32,\n}\nfn w() {}\n"] {
        let p = parse(src);
        assert_eq!(p.units.list.len(), 2, "{src:?}: {:?} {:?}", p.units.list, p.diagnostics);
    }
}

#[test]
fn an_item_after_the_attributes_of_a_member_ends_a_list_never_closed() {
    // §18.1, §2.5: the line after a member line that ends with attributes
    // goes on, and an item at its head as deep as the `{` ends the list of
    // the `{` never closed (an attribute over two lines too, whose unit has
    // an error of its own); a deeper one is a member.
    let canary = |p: &crate::Parsed| {
        (p.ast.root.iter())
            .any(|&id| matches!(&p.ast.item(id).kind, crate::ast::ItemKind::Fn(f) if f.name.name == "canary"))
    };
    for list in
        ["impl S {\n  fn n(self) -> I32 { 1 }\n", "trait T {\n  fn n(self) -> I32\n", "effect E {\n  fn n() -> I32\n"]
    {
        for line in ["  x @a\n", "  x @fp(relaxed)\n", "  @fp(\n    relaxed)\n"] {
            let src = format!("{list}{line}fn canary() -> I32 {{ 1 }}\n");
            let p = parse(&src);
            assert!(canary(&p), "{src:?}: {:?}", p.diagnostics);
            let deeper = format!("{list}{line}  fn canary() -> I32 {{ 1 }}\n");
            assert!(!canary(&parse(&deeper)), "{deeper:?}");
        }
    }
}

#[test]
fn a_line_of_attributes_alone_is_measured_at_the_line_of_its_item() {
    // §18.1, S-947 (947-2): the lines `@export` and `@fp(relaxed)` start
    // the item `canary` of the file, at the indentation of its head: the
    // members' `{` and the `impl`'s end there, the innermost reported.
    let src = "impl S {\n  fn a(self) -> I32 {\n    1\n  @export\n  @fp(relaxed)\npub fn canary() {}\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0002], "{:?}", p.diagnostics);
    assert_eq!(p.diagnostics[0].span.start, src.find("{\n    1").unwrap() as u32);
    assert!(dump(&p.ast).contains("\n(@export @fp(relaxed) pub fn canary()"), "{}", dump(&p.ast));
    // Measured at the line of `fn b`, as deep as the member: it is one.
    let src = "impl S {\n  fn a(self) -> I32 {\n    1\n@fp(relaxed)\n  fn b(self) {}\n}\n";
    let d = dump(&parse(src).ast);
    assert!(d.contains("fn b(self)") && !d.contains("\n(@fp"), "{d}");
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
    // Another error stopped it earlier: the `{` is reported too (R-371).
    let p = parse("fn f() -> I32 {\n  let = 1\n");
    let messages = p.diagnostics.iter().map(|d| d.message.as_str()).collect::<Vec<_>>();
    assert_eq!(messages, ["expected a pattern, found `=`", "this `{` is never closed"]);
    // Not an E0006 unit (§2.5), nor one with a literal or a `/*` that does not close (S-859).
    for src in ["fn f() {\n  let s = \"x }\n", "fn f() {\n  let s = $\"x }\n", "fn f() {\n  /* x }\n"] {
        assert!(parse(src).diagnostics.iter().all(|d| d.message != "this `{` is never closed"), "{src}");
    }
    // By its place: the literal is in a member, and the `impl` around does not report.
    let p = parse("impl S {\n  fn a() { \"x }\n  fn b() { }\n");
    assert!(p.diagnostics.iter().all(|d| d.message != "this `{` is never closed"), "{:?}", p.diagnostics);
}

#[test]
fn the_other_brackets_never_closed_are_notes_in_order_after_the_declaration() {
    // S-943: the innermost has the E0002, the others have notes, of the
    // member's unit and of the list around it.
    let src = "impl S {\n  fn a(self) -> I32 {\n    if c {\n      1\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0002]);
    let at = |s: &str| src.find(s).unwrap() as u32 + s.len() as u32 - 1;
    assert_eq!(p.diagnostics[0].span.start, at("if c {"));
    let notes: Vec<(&str, u32)> =
        p.diagnostics[0].notes.iter().filter_map(|n| n.span.map(|s| (n.message.as_str(), s.start))).collect();
    assert_eq!(
        notes,
        [
            ("it is in the body of `a`", src.find("a(self)").unwrap() as u32),
            ("this `{` is open here too", at("impl S {")),
            ("this `{` is open here too", at("I32 {")),
        ]
    );
}

#[test]
fn the_note_on_an_outer_bracket_says_it_is_open_where_the_unit_stops() {
    // R-395: the `{` of the `impl` is closed later, by the last `}`; where the
    // member stops, it is open, and the note says no more than that.
    let src = "impl P {\n  fn a(self) -> I32 {\n    self.v\n\n  fn b(self) -> I32 { 2 }\n}\n";
    let p = parse(src);
    assert_eq!(codes_of(&p), [Code::E0002]);
    let notes: Vec<&str> = p.diagnostics[0].notes.iter().map(|n| n.message.as_str()).collect();
    assert_eq!(notes[notes.len() - 1], "this `{` is open here too");
}

#[test]
fn an_error_found_at_the_next_item_says_what_its_unit_wants_after_its_last_token() {
    // R-400 (§18.1, S-276): the error is of the unit that stops, at its end;
    // the forms the next item starts are of the next unit (the attribute of
    // other languages is reported once, at itself).
    let cases = [
        ("const K: I32 = 1 +\nfn z() -> I32 { 1 }\n", "expected an expression after `+`", 1),
        ("type Op =\nfn z() -> I32 { 1 }\n", "expected a type after `=`", 1),
        ("pub type Op =\n  #[x]\n  fn(I32) -> I32\n", "expected a type after `=`", 3),
        // A reserved word found there too (S-952): its unit has its own E0002.
        ("const K: I32 = 1 +\nstatic fn z() -> I32 { 1 }\n", "expected an expression after `+`", 2),
        // Failed after the doc comment where the unit stops, the same.
        ("const K: I32 = 1 +\n/// d\nstatic fn z() -> I32 { 1 }\n", "expected an expression after `+`", 2),
    ];
    for (src, message, count) in cases {
        let p = parse(src);
        let end = src.find('\n').unwrap() as u32;
        let first = &p.diagnostics[0];
        assert!(first.message.starts_with(message) && first.span.start == end, "{src:?}: {:?}", p.diagnostics);
        assert_eq!(p.diagnostics.len(), count, "{src:?}: {:?}", p.diagnostics);
    }
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

/// §6.5, S-639: `@export` goes on a function of the top level, not on one in
/// the list of a declaration (an `extern` block here; `impl` and `trait` are
/// in the cases) nor on a `target` declaration; `@fp` goes on both kinds of
/// function, and the old `@relaxed` of a member keeps its candidate.
#[test]
fn the_places_of_a_member_function() {
    let ext = "extern \"C\" lib \"m\" {\n  @export\n  fn g() -> I32\n}\n";
    assert_eq!(codes(ext), [Code::E0005], "{ext}");
    let target = "@export\ntarget fn now() -> U32\n";
    assert_eq!(codes(target), [Code::E0005], "{target}");
    let fp = "struct S {}\n\nimpl S {\n  @fp(relaxed)\n  fn m(self) -> F32 {\n    1.0\n  }\n}\n";
    assert_eq!(codes(fp), [], "{fp}");
    let old = fp.replace("@fp(relaxed)", "@relaxed");
    assert_eq!(codes(&old), [Code::E0020], "{old}");
    assert_eq!(fixed(&old), fp);
    assert_eq!(fixed("#[export]\npub fn f() -> I32 {\n  1\n}\n"), "@export\npub fn f() -> I32 {\n  1\n}\n");
}

/// `par~` (§2.6, §11.5, S-745): the `~` touches `par`, and the syntax stage
/// reads `par` without it the same (the names stage's E0811). A blank or, in
/// parentheses, a line break between them is the E0020 of
/// `space_after_branch_keyword` with one candidate (a name follows: no `!`
/// form); outside parentheses `par` ends its line (E0002).
#[test]
fn the_tilde_of_par_touches_the_keyword() {
    assert_eq!(body("par~ i in 0..<2 { x }"), "(block tail (par~ i in 0..<2 (block tail x)))");
    assert_eq!(body("par i in 0..<2 { x }"), "(block tail (par i in 0..<2 (block tail x)))");
    let flow = |s: &str| format!("flow g(x: F32 at sample) -> [F32; 2] at sample {{\n  {s}\n}}\n");
    let two = |s: &str| {
        format!(
            "rt fn two(a: [F32; 2], b: F32) -> F32 {{ b }}\nflow g(x: F32 at sample) -> F32 at sample {{\n  {s}\n}}\n"
        )
    };
    for (src, after) in [
        (flow("par ~ i in 0..<2 { x }"), flow("par~ i in 0..<2 { x }")),
        (flow("par\t~i in 0..<2 { x }"), flow("par~ i in 0..<2 { x }")),
        (two("two(par\n    ~ i in 0..<2 { x }, 1.0)"), two("two(par~\n    i in 0..<2 { x }, 1.0)")),
    ] {
        let p = parse(&src);
        assert_eq!(codes_of(&p), [Code::E0020], "{src}");
        assert_eq!(p.diagnostics[0].fixes.len(), 1, "{src}: {:?}", p.diagnostics[0]);
        assert_eq!(fixed(&src), after);
    }
    assert_eq!(codes(&flow("let a = par\n    ~i in 0..<2 { x }\n  a")), [Code::E0002]);
}

/// The guard reading of the pattern `src` alone ([`crate::parser::reads_as_pattern`]):
/// its tree, a node as its kind and its child nodes, an `Error` node as its
/// guard form; `None` when it does not read.
fn guard_reading(src: &str, whole: bool) -> Option<String> {
    use crate::cst::{Cst, NodeId, NodeKind};
    use crate::parser::Guarded;
    fn show(cst: &Cst, forms: &[(u32, Guarded)], n: NodeId) -> String {
        let head = match cst.kind(n) {
            NodeKind::Error => {
                let start = cst.span(n).start;
                let form = forms.iter().find(|f| f.0 == start).map(|f| f.1);
                form.map_or_else(|| "Error".to_string(), |f| format!("{f:?}"))
            }
            k => format!("{k:?}"),
        };
        let kids: Vec<String> = cst.child_nodes(n).map(|k| show(cst, forms, k)).collect();
        if kids.is_empty() { head } else { format!("({head} {})", kids.join(" ")) }
    }
    let lexed = crate::lex(FileId(0), src);
    let tokens = lexed.tokens.iter().copied().filter(|t| t.kind != crate::TokenKind::Eof).collect();
    let (cst, forms) = crate::parser::reads_as_pattern(FileId(0), src, tokens, &lexed.literals, whole)?;
    let pat = cst.child_nodes(cst.root()).next()?;
    Some(show(&cst, &forms, pat))
}

/// The guard reading (§7, §18.1): the parser's grammar of the patterns,
/// where each guard form it fails at in a file is an `Error` node, and a
/// `|` at the head of a line is one between alternatives.
#[test]
fn the_guard_reading_reads_the_guard_forms_as_error_nodes() {
    let read = |src: &str| guard_reading(src, true);
    assert_eq!(read("1.5").as_deref(), Some("Number"));
    assert_eq!(read("-(1.5)").as_deref(), Some("Number"));
    assert_eq!(read("-LIMIT").as_deref(), Some("(Number Path)"));
    assert_eq!(read("(1..<5, x)").as_deref(), Some("(TuplePat Range { sym: 2 } (BindPat Path))"));
    assert_eq!(read("Some(\"a{x}\")").as_deref(), Some("(TupleStructPat Path Str)"));
    assert_eq!(read("n @ 1").as_deref(), Some("(At BindPat LitPat)"));
    // The right of `@` that is no pattern is left out: the form is `@`
    // alone, and the alternative ends there.
    assert_eq!(guard_reading("n @ ..", false).as_deref(), Some("(At BindPat)"));
    assert_eq!(read("n @ .."), None);
    assert_eq!(read("1.5\n| 2.5").as_deref(), Some("(OrPat Number Number)"));
    assert_eq!(read("1 | 2").as_deref(), Some("(OrPat LitPat LitPat)"));
    // One alternative when not whole; the whole must read to its end.
    assert_eq!(guard_reading("1.5 | 2", false).as_deref(), Some("Number"));
    assert_eq!(read("1.5 x"), None);
    assert_eq!(read("-(-1)"), None);
}

/// A trial of the guard reading that is undone drops the guard forms it
/// read: the right of `@` that reads `1.5` and then fails leaves only the
/// form of `@` ([`crate::parser::reads_as_pattern`]).
#[test]
fn an_undone_trial_of_the_guard_reading_leaves_no_form() {
    let src = "n @ (1.5, &)";
    let lexed = crate::lex(FileId(0), src);
    let tokens = lexed.tokens.iter().copied().filter(|t| t.kind != crate::TokenKind::Eof).collect();
    let read = crate::parser::reads_as_pattern(FileId(0), src, tokens, &lexed.literals, false);
    let forms: Vec<_> = read.map(|(_, forms)| forms.into_iter().map(|f| f.1).collect()).unwrap_or_default();
    assert_eq!(forms, [crate::parser::Guarded::At]);
}

/// The guard reading nests as deep as the parser (§2.5): 256 levels read,
/// 257 do not; an `@` counts one level, so the right of the 257th `@` of
/// a chain is left out (the alternative ends at that `@`).
#[test]
fn the_guard_reading_stops_at_the_limit_of_nesting() {
    onsa_diag::stack::run(|| {
        let limit = crate::parser::NESTING_LIMIT as usize;
        let groups = |n: usize| format!("{}1.5{}", "(".repeat(n), ")".repeat(n));
        assert!(guard_reading(&groups(limit), true).is_some());
        assert_eq!(guard_reading(&groups(limit + 1), true), None);
        let chain = |n: usize| format!("{}1.5", "n @ ".repeat(n));
        let count = |t: String| (t.matches("At").count(), t.matches("Number").count());
        assert_eq!(guard_reading(&chain(limit), true).map(count), Some((limit, 1)));
        assert_eq!(guard_reading(&chain(limit + 1), true), None);
        assert_eq!(guard_reading(&chain(limit + 1), false).map(count), Some((limit, 0)));
        assert_eq!(guard_reading(&chain(300), false).map(count), Some((limit, 0)));
    });
}

/// R-417: an element of a list of type arguments that the tokens show to be
/// an expression is not tried as a type, so a chain of `Rg::[F32, [F32;
/// …].len]` is read once, as many tokens as it has (§2.5, under the limit):
/// the tokens read for 60 levels are at most 3.5 times those for 20, in a
/// type, a value and the length of an array, with `::[` and with `[`.
#[test]
fn the_type_arguments_of_a_chain_are_read_once() {
    let head =
        "pub struct Rg[T, const N: U32] { d: [T; N] }\nimpl[T, const N: U32] Rg[T, N] { pub const CAP: U32 = 4 }\n";
    let chain =
        |n: usize, colons: &str| (0..n).fold("I32".to_string(), |t, _| format!("Rg{colons}[F32, [F32; {t}].len]"));
    let forms: [fn(&str) -> String; 3] = [
        |t| format!("pub fn f(r: {t}) -> U32 {{ 0 }}\n"),
        |t| format!("pub fn f() -> U32 {{\n  let a = {t}.CAP\n  0\n}}\n"),
        |t| format!("pub fn f(r: [F32; {t}.CAP]) -> U32 {{ 0 }}\n"),
    ];
    onsa_diag::stack::run(|| {
        for (k, form) in forms.iter().enumerate() {
            for colons in ["::", ""] {
                let bumped = |n: usize| {
                    let before = crate::parser::BUMPED.get();
                    parse(&format!("{head}{}", form(&chain(n, colons))));
                    crate::parser::BUMPED.get() - before
                };
                let (few, many) = (bumped(20), bumped(60));
                // Each level has 12 tokens: the chain is read to its end.
                assert!(
                    few > 20 * 12 && many * 2 <= few * 7,
                    "form {k}, `{colons}`: {few} tokens for 20 levels, {many} for 60"
                );
            }
        }
    });
}
