//! Tests of the tails of a value and of what diverges
//! (`onsa_syntax::tails`, §5.2, §5.4, §7), on the table of the names stage.

use onsa_diag::FileId;
use onsa_syntax::ast::{Block, ExprId, ExprKind, ItemKind, StmtId, StmtKind};
use onsa_syntax::tails::{Patch, Tail};

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

/// R-389: the form of the join of an E0418 takes `a` out of the block and
/// gives it to `-b` as its left operand (`a - b`), so a `break` in `a` still
/// leaves the loop (§7); the form that only takes `a` out has none.
#[test]
fn the_left_operand_of_a_joined_line_is_searched_for_a_break() {
    let src = "fn f(c: Bool, b: I32) -> I32 {\n  while true {\n    let v = {\n      h(if c { break } else { true })\n      -b\n    }\n  }\n  1\n}\nfn h(x: Bool) -> I32 {\n  1\n}\n";
    let p = onsa_syntax::parse(FileId(0), src);
    let ItemKind::Fn(f) = &p.ast.item(p.ast.root[0]).kind else { panic!("not a function") };
    let root = f.body.expect("a body");
    let block = |e: ExprId| match &p.ast.expr(e).kind {
        ExprKind::Block(b) => b.clone(),
        _ => panic!("no block"),
    };
    let s = block(root).stmts[0];
    let StmtKind::While { body, .. } = p.ast.stmt(s).kind else { panic!("no while") };
    let StmtKind::Let { init, .. } = p.ast.stmt(block(body).stmts[0]).kind else { panic!("no let") };
    let b = block(init);
    let StmtKind::Expr(left) = p.ast.stmt(b.stmts[0]).kind else { panic!("no statement") };
    let last = b.tail.expect("a last expression");
    let rest = Block { stmts: Vec::new(), tail: Some(last) };
    let a = check(src);
    let table = &a.bodies[&def(&a, "f")].diverging;
    assert!(!table.forever(s), "the names stage reads the `break`");
    let joined = Patch::Operand(init, rest.clone(), last, left);
    assert!(!table.patched(&p.ast, root, &joined).forever(s));
    assert!(table.patched(&p.ast, root, &Patch::Block(init, rest)).forever(s));
}

/// Whether `Diverging::patched` of a form that changes no node gives the
/// table of every body of `src` back: it is the table of the names stage,
/// read again in the same order with the same readings. What a form changes
/// is in the cases `tests/spec/fixes/match_unreachable_dead_break_*`.
fn same_table_again(src: &str) -> usize {
    let p = onsa_syntax::parse(FileId(0), src);
    let a = check(src);
    let no_node = Patch::Arms(ExprId(u32::MAX), Vec::new());
    let (main, mut read) = (a.defs.last().expect("a def").module, 0);
    let walked = |id: &crate::DefId| a.def(*id).module == main && a.names.get(id).is_some_and(|n| n.complete);
    for (&id, info) in a.bodies.iter().filter(|(id, _)| walked(id)) {
        let Some(root) = crate::body::root_of(&a, id) else { continue };
        let table = info.diverging.patched(&p.ast, root, &no_node);
        for e in (0..p.ast.exprs.len() as u32).map(ExprId) {
            assert_eq!(info.diverging.expr(e), table.expr(e), "{}", p.ast.expr(e).span.start);
        }
        for s in (0..p.ast.stmts.len() as u32).map(StmtId) {
            assert_eq!(info.diverging.forever(s), table.forever(s), "{}", p.ast.stmt(s).span.start);
        }
        read += 1;
    }
    read
}

#[test]
fn a_form_that_changes_no_node_gives_the_table_of_the_names_stage() {
    let src = r#"
fn a(c: Bool) -> I32 {
  while true {
    while c { break }
    if c { return 1 } else { panic("x") }
  }
}
fn b(c: Bool, n: I32) -> I32 {
  while (true) {
    match n {
      0 => { break },
      _ => { return 1 },
    }
  }
  let g = fn() -> I32 { while true { return 2 } }
  (panic("y"))
}
fn d(n: I32) -> I32 {
  let k = if n > 0 { { return 1 } } else { (panic("z")) }
  k
}
"#;
    assert_eq!(same_table_again(src), 3);
}

/// The always evaluated part of `whole`, the last expression of a function
/// (§7, S-291, S-889), or its statement `head` before it; by its text.
fn parts(whole: &str, head: Option<&str>) -> (Option<String>, Option<String>) {
    let first = head.map_or(String::new(), |h| format!("  {h}\n"));
    let src = format!(
        "fn g(n: I32) -> I32 {{ n }}\nfn f(c: Bool, x: I32, s: S) -> I32 {{\n{first}  {whole}\n}}\nstruct S {{ n: I32 }}\n"
    );
    let p = onsa_syntax::parse(FileId(0), &src);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let ItemKind::Fn(f) = &p.ast.item(p.ast.root[1]).kind else { panic!("not a function") };
    let ExprKind::Block(b) = &p.ast.expr(f.body.expect("a body")).kind else { panic!("no block") };
    let a = check(&src);
    let table = &a.bodies[&def(&a, "f")].diverging;
    let text = |e: ExprId| {
        let s = p.ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    let of_stmt = b.stmts.first().and_then(|&s| table.stmt_part(&p.ast, s));
    (b.tail.and_then(|t| table.evaluated_part(&p.ast, t)).map(text), of_stmt.map(text))
}

#[test]
fn the_parts_that_are_always_evaluated() {
    const R: &str = "{ return 1 }";
    for whole in [
        "x + ({ return 1 })",
        "({ return 1 }) + x",
        "({ return 1 }) && c",
        "-({ return 1 })",
        "({ return 1 }) as I64",
        "({ return 1 })?",
        "move ({ return 1 })",
        "({ return 1 }).n",
        "({ return 1 }).0",
        "(x, ({ return 1 }))",
        "[x, ({ return 1 })]",
        "[({ return 1 }); 2]",
        "S { n: ({ return 1 }) }",
        "g(({ return 1 }))",
        "g(move ({ return 1 }))",
        "({ return 1 }).(x)",
        "({ return 1 }).m()",
        "s.m(({ return 1 }))",
        "s[({ return 1 })]",
        "({ return 1 })[x]",
        "if ({ return 1 }) { 1 } else { 2 }",
        "match ({ return 1 }) { _ => 1 }",
    ] {
        assert_eq!(parts(whole, None).0.as_deref(), Some(R), "{whole}");
    }
    assert_eq!(parts("g(panic(\"x\"))", None).0.as_deref(), Some("panic(\"x\")"));
    for (head, whole) in [
        ("x = ({ return 1 })", "x"),
        ("return ({ return 1 })", "x"),
        ("assert ({ return 1 })", "x"),
        ("while ({ return 1 }) {}", "x"),
        ("for v in ({ return 1 }) {}", "x"),
        ("for v in ({ return 1 })..<3 {}", "x"),
        ("for v in 0..<({ return 1 }) {}", "x"),
    ] {
        assert_eq!(parts(whole, Some(head)).1.as_deref(), Some(R), "{head}");
    }
}

/// What §7 keeps out of the parts, and an outer expression over a part that
/// is no diverging form itself.
#[test]
fn the_parts_end_at_what_is_not_always_evaluated() {
    for whole in [
        "c && ({ return true })",
        "c || panic(\"x\")",
        "if c { return 1 } else { return 2 }",
        "g(if c { return 1 } else { 2 })",
        "match c { _ if { return true } => 1, _ => 2 }",
        "g.(fn() { return })",
        "({ return 1 })",
        "{ return 1 }",
        "g(g({ return 1 }))",
    ] {
        assert_eq!(parts(whole, None).0, None, "{whole}");
    }
    assert_eq!(parts("x", Some("let y = ({ return 1 })")).1, None, "S-268");
    // The part of `if` and `while` is the condition.
    assert_eq!(parts("x", Some("while c { return 1 }")).1, None);
}
