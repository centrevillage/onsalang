//! Tests of the tails of a value and of what diverges
//! (`onsa_syntax::tails`, §5.2, §5.4, §7), on the table of the names stage.

use onsa_diag::FileId;
use onsa_syntax::ast::ItemKind;
use onsa_syntax::tails::Tail;

use crate::tests::{check, def};

/// The tails of the body of the first item of `src`, a function `f`, by
/// their text. The table is the names stage's, so an error of the types stage
/// in the body does not change it.
fn tails_of(src: &str) -> Vec<String> {
    let p = onsa_syntax::parse(FileId(0), src);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let ItemKind::Fn(f) = &p.ast.item(p.ast.root[0]).kind else { panic!("not a function") };
    let a = check(src);
    let mut out = Vec::new();
    p.ast.tails(f.body.expect("a body"), &a.bodies[&def(&a, "f")].diverging, &mut out);
    let text = |e| {
        let s = p.ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    out.into_iter()
        .map(|t| match t {
            Tail::Value(e) => text(e),
            Tail::Exits => "exits".into(),
            Tail::Unit(e) => format!("() of {}", text(e)),
        })
        .collect()
}

#[test]
fn the_tails_through_branches_blocks_and_parentheses() {
    let src = "fn f(c: Bool, x: I32, y: I32) -> I32 {\n  (if c { (x) } else { match c { true => { y.a }, false => { return 0 } } })\n}\n";
    assert_eq!(tails_of(src), ["x", "y.a", "exits"]);
    let src = "fn f(c: Bool, x: I32) -> I32 {\n  { if c { x } }\n}\n";
    assert_eq!(tails_of(src), ["() of if c { x }"]);
    let src = "fn f(x: I32) -> I32 {\n  { let y = x }\n}\n";
    assert_eq!(tails_of(src), ["() of { let y = x }"]);
    let src = "fn f(x: I32) -> I32 {\n  if true { move x } else { x.slice(0, 1) }\n}\n";
    assert_eq!(tails_of(src), ["move x", "x.slice(0, 1)"]);
}

/// S-891: the forms count by recursion, `panic` by its name.
#[test]
fn a_diverging_form_is_one_tail_that_exits() {
    for body in [
        "{ return 1 }",
        "{ { return 1 } }",
        "{ if c { return 1 } else { return 2 } }",
        "({ panic(\"x\") })",
        "panic(\"x\")",
        "if c { panic(\"x\") } else { return 1 }",
        "match c { true => panic(\"x\"), false => { return 1 } }",
        "{ while true {} }",
        "{ let x: I32 = { return 1 } }",
    ] {
        let src = format!("fn f(c: Bool) -> I32 {{\n  {body}\n}}\n");
        assert_eq!(tails_of(&src), ["exits"], "{body}");
    }
    let src = "fn f(c: Bool, x: I32) -> I32 {\n  if c { x } else { panic(\"no\") }\n}\n";
    assert_eq!(tails_of(src), ["x", "exits"]);
    // No `else`: the branch alone diverges.
    let src = "fn f(c: Bool) {\n  { if c { panic(\"x\") } }\n}\n";
    assert_eq!(tails_of(src), ["() of if c { panic(\"x\") }"]);
}

/// An arm-less `match` is no diverging form (S-891).
#[test]
fn a_match_with_no_arm_does_not_diverge() {
    let src = "fn f(x: I32) -> I32 {\n  { match x {} \n  }\n}\n";
    assert!(tails_of(src).is_empty());
    let src = "fn f(x: I32) -> I32 {\n  let y = match x {}\n  return y\n}\n";
    assert_eq!(tails_of(src), ["exits"], "the `return` diverges, not the `match`");
    let src = "fn f(x: I32) {\n  { let y = match x {} }\n}\n";
    assert_eq!(tails_of(src), ["() of { let y = match x {} }"]);
}

/// §7: a `while` of the literal `true` with no `break` of its own; the table
/// of what is searched is in `Ast::leaves_loop`.
#[test]
fn a_while_diverges_by_its_condition_and_its_breaks() {
    let whole = |body: &str| format!("fn f(c: Bool, xs: [I32; 2]) {{\n  {{ {body}\n  }}\n}}\n");
    for body in [
        "while true {}",
        "while (true) {}",
        "while ((true)) { continue }",
        "while true { return }",
        "while true { while c { break } }",
        "while true { for x in xs { break } }",
        "while true { let g = fn() { while c { break } } }",
    ] {
        assert_eq!(tails_of(&whole(body)), ["exits"], "{body}");
    }
    for body in [
        "while c {}",
        "while !true {}",
        "while true { break }",
        "while true { if c { break } }",
        "while true { match c { true => { break }, false => {} } }",
        "while true { let x = { break } }",
        "while true { return\n break }",
        // The head of a loop inside is evaluated in this one.
        "while true { while ({ break }) {} }",
        "while true { for x in ({ break }) {} }",
    ] {
        let src = whole(body);
        assert!(matches!(&tails_of(&src)[..], [t] if t.starts_with("() of ")), "{body}");
    }
}
