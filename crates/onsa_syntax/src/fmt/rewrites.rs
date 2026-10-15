//! The rewrites of `onsa fmt` that change the tree (`docs/onsa-tools.md`
//! §3.3): the one closed list, in [`REWRITES`].
//!
//! A rewrite decides on the CST which nodes it rewrites: the nodes it drops
//! code tokens from. [`choose`] runs them once, in the order of the list and
//! from the root down; the plan (`fmt/plan.rs`) reads the dropped tokens and
//! the comparison of the check before writing and of `diff --ast` (§3.5,
//! [`crate::diff::same_program`]) reads the chosen nodes ([`normalize`]): the
//! AST side does not decide again, it rewrites the AST nodes made from the
//! chosen CST nodes (`Parsed::map`), and a chosen node whose AST is not of
//! the form the CST side saw is an internal error.
//!
//! Here is the `return e` in the tail position (§6.1), whose places
//! `fmt/tail.rs` decides; a `return` without a value stays (S-547). The
//! keyword is the only token it drops, and a comment at the end of its line
//! belongs to the value after it (§3.4, S-538: `return e // c` is `e //
//! c`), so no comment is ever in its range (S-536 (1)). The redundant
//! parentheses (W3-12 U2) come in the same form and go last (their AST side
//! copies the node inside, which the others must have rewritten before).

use std::collections::{HashMap, HashSet};

use super::tail;
use crate::ast::{Ast, ExprKind, StmtKind};
use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::parser::Parsed;
use crate::token::TokenKind;

/// A rewrite of §3.3.
struct Rewrite {
    /// The kinds of the nodes it chooses (an AST side is given no other).
    kinds: &'static [NodeKind],
    /// The code tokens it drops from the node (it is called on every node of
    /// the tree): the node it drops tokens from is a node it rewrites.
    cst: fn(&Cst, NodeId, &mut Vec<TokenIdx>),
    /// The same rewrite on the AST, of the nodes the CST side chose.
    ast: fn(&mut Ast, &Parsed, &[NodeId]),
}

/// The closed list of §3.3, in the order they are chosen and done.
const REWRITES: &[Rewrite] = &[Rewrite { kinds: &[NodeKind::ReturnStmt], cst: tail_return, ast: tail_return_ast }];

/// The choice of every rewrite of a tree ([`choose`]).
pub(super) struct Choices {
    /// Whether each token (by its index) is dropped.
    pub(super) dropped: Vec<bool>,
    /// The nodes each rewrite of [`REWRITES`] chose, in its order.
    chosen: Vec<Vec<NodeId>>,
}

/// Every node of the tree, the root first (without recursion).
pub(crate) fn all_nodes(cst: &Cst) -> Vec<NodeId> {
    let mut nodes = vec![cst.root()];
    let mut i = 0;
    while let Some(&n) = nodes.get(i) {
        nodes.extend(cst.child_nodes(n));
        i += 1;
    }
    nodes
}

/// The rewrites of `cst` (`nodes` is [`all_nodes`]), the one walk that the
/// plan and [`normalize`] read.
pub(super) fn choose(cst: &Cst, nodes: &[NodeId]) -> Choices {
    let mut dropped = vec![false; cst.tokens().len()];
    let mut chosen = Vec::with_capacity(REWRITES.len());
    let mut out = Vec::new();
    for rewrite in REWRITES {
        let mut these = Vec::new();
        for &n in nodes {
            (rewrite.cst)(cst, n, &mut out);
            if out.is_empty() {
                continue;
            }
            if !rewrite.kinds.contains(&cst.kind(n)) {
                onsa_diag::internal::bug(Some(cst.span(n)), "fmt's rewrite chose a node of a kind it does not do");
            }
            these.push(n);
            out.drain(..).for_each(|t| dropped[t.index()] = true);
        }
        chosen.push(these);
    }
    Choices { dropped, chosen }
}

/// The AST of `parsed` with every rewrite of the list (§3.5). `parsed` has
/// no diagnostic of the syntax stage (the callers refuse such a file first):
/// one is an internal error here, before a rewrite meets a broken tree.
pub(crate) fn normalize(parsed: &Parsed) -> Ast {
    if let Some(d) = parsed.first_syntax_error() {
        onsa_diag::internal::bug(Some(d.span), "the comparison of fmt and `diff --ast` got a tree with a syntax error");
    }
    let mut ast = parsed.ast.clone();
    let choices = choose(&parsed.cst, &all_nodes(&parsed.cst));
    for (rewrite, chosen) in REWRITES.iter().zip(&choices.chosen) {
        (rewrite.ast)(&mut ast, parsed, chosen);
    }
    ast
}

/// The index in `map` (an array of `Parsed::map`) of each node of `wanted`.
fn index_of(map: &[NodeId], wanted: &HashSet<NodeId>) -> HashMap<NodeId, usize> {
    map.iter().enumerate().filter(|(_, n)| wanted.contains(n)).map(|(i, &n)| (n, i)).collect()
}

/// The `return` of a `return e` in the tail position (spec §6.1,
/// `fmt/tail.rs`): the last statement of a block there. A `return` in the
/// value of one that goes is in the tail position too, so one pass reaches
/// the fixed point. A `return` without a value stays (S-547).
fn tail_return(cst: &Cst, n: NodeId, out: &mut Vec<TokenIdx>) {
    if cst.kind(n) != NodeKind::ReturnStmt || cst.child_nodes(n).next().is_none() || !tail::last_of_tail_block(cst, n) {
        return;
    }
    let keyword = cst.children(n).iter().find_map(|e| match *e {
        Elem::Token(t) if cst.token(t).kind == TokenKind::KwReturn => Some(t),
        _ => None,
    });
    out.extend(keyword);
}

/// [`tail_return`] on the AST: the chosen statement `return e`, the last of
/// its block, becomes the value `e` of the block.
fn tail_return_ast(ast: &mut Ast, parsed: &Parsed, chosen: &[NodeId]) {
    let bug = |n: NodeId, what: &str| -> ! {
        onsa_diag::internal::bug(Some(parsed.cst.span(n)), format!("fmt's rewrite of the `return` at the end: {what}"))
    };
    let wanted: HashSet<NodeId> = chosen.iter().flat_map(|&n| [Some(n), parsed.cst.parent(n)]).flatten().collect();
    let (stmt_of, expr_of) = (index_of(&parsed.map.stmts, &wanted), index_of(&parsed.map.exprs, &wanted));
    for &n in chosen {
        let block = parsed.cst.parent(n).and_then(|b| expr_of.get(&b));
        let (Some(&s), Some(&e)) = (stmt_of.get(&n), block) else { bug(n, "no statement in a block") };
        let ExprKind::Block(block) = &mut ast.exprs[e].kind else { bug(n, "no statement in a block") };
        let StmtKind::Return(Some(value)) = ast.stmts[s].kind else { bug(n, "not a `return` with a value") };
        if block.stmts.last().map(|l| l.index()) != Some(s) || block.tail.is_some() {
            bug(n, "not the last statement of its block");
        }
        block.stmts.pop();
        block.tail = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::FileId;

    use crate::ast::Ast;
    use crate::cst::{NodeId, NodeKind};
    use crate::parser::Parsed;

    /// W3-11/b 1: a body that ends in more than one `return` (the ones before
    /// the last are dead code, which `check` takes) loses the `return` of the
    /// last statement only, on the CST and on the AST alike, so the check
    /// passes and the output is the one fmt wrote before the check.
    #[test]
    fn only_the_last_of_several_returns_is_rewritten() {
        let f = |body: &str| format!("fn f(c: Bool) -> I32 {{\n{body}}}\n");
        let cases = [
            ("  return 1\n  return 2\n", "  return 1\n  2\n"),
            ("  return 1\n  return 2\n  return 3\n", "  return 1\n  return 2\n  3\n"),
            ("  return 1\n  return 2 // c\n", "  return 1\n  2 // c\n"),
            ("  return 1\n  return 2\n  // trailing\n", "  return 1\n  2\n  // trailing\n"),
            ("  if c {\n    return 1\n  }\n  return 2\n  return 3\n", "  if c {\n    return 1\n  }\n  return 2\n  3\n"),
        ];
        let mut all = cases.map(|(a, b)| (f(a), f(b))).to_vec();
        all.push((
            "impl S {\n  fn g(self) -> I32 {\n    return 1\n    return self.v\n  }\n}\n".into(),
            "impl S {\n  fn g(self) -> I32 {\n    return 1\n    self.v\n  }\n}\n".into(),
        ));
        for (src, want) in &all {
            let parsed = crate::parse(FileId(0), src);
            assert!(parsed.diagnostics.is_empty(), "{src}: {:?}", parsed.diagnostics);
            assert_eq!(crate::format(&parsed, src).as_deref(), Ok(want.as_str()), "{src}");
        }
    }

    /// The output of `format` for `src`, which must have no diagnostic, and
    /// a fixed point.
    fn formatted(src: &str) -> String {
        let parsed = crate::parse(FileId(0), src);
        assert!(parsed.diagnostics.is_empty(), "{src}: {:?}", parsed.diagnostics);
        let out = crate::format(&parsed, src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let again = crate::parse(FileId(0), &out);
        assert_eq!(crate::format(&again, &out).as_deref(), Ok(out.as_str()), "not a fixed point: {src}");
        out
    }

    /// Whether `diff --ast` sees `a` and `b` as the same program.
    fn same(a: &str, b: &str) -> bool {
        let (pa, pb) = (crate::parse(FileId(0), a), crate::parse(FileId(1), b));
        crate::diff::diff(&pa, &pb).is_empty()
    }

    /// W3-12: the forms that a choice of the last statement alone would
    /// change again at the next `fmt` reach the fixed point in one pass: a
    /// `return` in the value of the last `return`.
    #[test]
    fn the_tail_position_is_reached_in_one_pass() {
        let cases = [
            (
                "fn f(c: Bool) -> I32 {\n  return if c { return 1 } else { 2 }\n}\n",
                "fn f(c: Bool) -> I32 {\n  if c { 1 } else { 2 }\n}\n",
            ),
            (
                "fn f(c: Bool, move a: B) -> B {\n  return match c {\n    true => { return move a },\n    _ => move a,\n  }\n}\n",
                "fn f(c: Bool, move a: B) -> B {\n  match c {\n    true => { move a },\n    _ => move a,\n  }\n}\n",
            ),
            // Through parentheses (U2 takes these off too).
            (
                "fn f(c: Bool) -> I32 {\n  return (if c { return 1 } else { 2 })\n}\n",
                "fn f(c: Bool) -> I32 {\n  (if c { 1 } else { 2 })\n}\n",
            ),
        ];
        for (src, want) in cases {
            assert_eq!(formatted(src), want, "{src}");
        }
    }

    /// S-547: a `return` without a value stays wherever it is: at the end of
    /// a body, after an expression, a `let`, a loop, an assignment or a
    /// `return` (dead code, which `check` may reject: `return a` then
    /// `return` in a function of `I32` is E0401, and taking the `return` off
    /// would make `return a` the last statement and the program pass), in a
    /// run of them, in a branch, with a comment at the end of its line (the
    /// forms of W3-12/b2 1 and 2, which fmt rewrote to another program or
    /// stopped on with an internal error). The `return e` before it is not
    /// the last statement, so it stays too.
    #[test]
    fn a_return_without_a_value_stays() {
        let f = |body: &str| format!("fn f(c: Bool, a: I32, move m: B) -> I32 {{\n{body}}}\n");
        let bodies = [
            "  g()\n  return\n",
            "  g()\n  return\n  return\n",
            "  if c { 1 } else { 2 }\n  return\n",
            "  if c { move m }\n  return\n",
            "  if c { return }\n  return\n",
            "  if c {\n    return\n  }\n  return\n  return\n",
            "  match c {\n    _ => { return },\n  }\n  return\n",
            "  var x = 1\n  x = 2\n  return\n",
            "  for i in 0 ..< 3 {}\n  return\n",
            "  while true {}\n  return\n",
            "  let y = 1\n  return\n",
            "  return\n",
            "  return\n  return\n",
            "  return a\n  return\n",
            "  return 1\n  return\n  return\n",
            "  return a\n  // c\n  return\n",
            "  return a\n  return // c\n",
            "  return g()\n  return // c\n",
            "  return if c { 1 } else { 2 }\n  return // c\n",
            "  return (a)\n  return // c\n  return // d\n",
            "  if c {\n    return a\n    return // c\n  }\n  return\n",
            "  if c {}\n  return // done\n",
            "  g()    // c\n  return // d\n  return // e\n  return\n",
        ];
        for body in bodies {
            assert_eq!(formatted(&f(body)), f(body), "{body}");
        }
        // Not a rewrite of §3.3: `diff --ast` tells a file with it from one without it.
        assert!(!same(&f("  if c {}\n  return // done\n"), &f("  if c {}\n")));
        assert!(!same(&f("  return a\n  return\n"), &f("  a\n")));
    }

    /// S-538: a comment at the end of a line belongs to the last code of the
    /// line, so `return e // c` is `e // c` (the keyword is not the last code).
    #[test]
    fn a_return_with_a_value_whose_line_ends_in_a_comment_goes() {
        let value = "fn h() -> I32 {\n  return 1 // one\n}\n";
        assert_eq!(formatted(value), "fn h() -> I32 {\n  1 // one\n}\n");
        let branch = "fn h(c: Bool) -> I32 {\n  if c {\n    return 1 // one\n  } else {\n    return 2 // two\n  }\n}\n";
        assert_eq!(
            formatted(branch),
            "fn h(c: Bool) -> I32 {\n  if c {\n    1 // one\n  } else {\n    2 // two\n  }\n}\n"
        );
    }

    /// W3-12 (the user's decision of 2026-10-15): the `move` in the returned
    /// position stays (S-100 is taken back: `move K` of a constant is E0711,
    /// and the syntax does not show that a name is a local), and so do `->
    /// ()` and an empty `uses {}` (left to the second phase). `fmt` rewrites
    /// only the `return` around them.
    #[test]
    fn the_returned_move_and_the_heads_stay() {
        for kept in [
            "fn f(move a: B) -> B {\n  move a\n}\n",
            "fn f(c: Bool, move a: B) -> B {\n  if c { move a } else { move a }\n}\n",
            "fn f() {\n  let g = fn(move a: B) -> B { move a }\n}\n",
            "fn f() -> () uses {} {}\n",
            "type T = fn(F32) -> () uses {}\n",
            "struct S {\n  a: fn(F32) -> (),\n}\n",
            "fn f() {\n  take(fn(x: I32) -> () uses {} { x })\n}\n",
            "fn f() -> () {\n  g()\n  return\n}\n",
            "fn f(inout x: I32) -> () uses {} {\n  x = 1\n  return\n}\n",
        ] {
            assert_eq!(formatted(kept), kept);
        }
        assert_eq!(formatted("fn f(move a: B) -> B {\n  return move a\n}\n"), "fn f(move a: B) -> B {\n  move a\n}\n");
        // Not rewrites of §3.3 any more: `diff --ast` tells them apart.
        assert!(!same("fn f(move a: B) -> B {\n  move a\n}\n", "fn f(move a: B) -> B {\n  a\n}\n"));
        assert!(!same("fn f() -> () uses {} {}\n", "fn f() {}\n"));
    }

    /// W3-12: a `return` that is not in the tail position (§6.1) stays: in
    /// a loop, an `unsafe` or block expression, a `flow`.
    #[test]
    fn a_return_out_of_the_tail_position_stays() {
        for kept in [
            "fn f(move a: B) -> B {\n  unsafe { move a }\n}\n",
            "fn f(move a: B) -> B {\n  let b = { move a }\n  b\n}\n",
            "fn f(c: Bool) {\n  while c {\n    return\n  }\n}\n",
            "fn f(c: Bool) -> I32 {\n  while c {\n    return 1\n  }\n  2\n}\n",
            "flow f(x: Sig[F32]) -> Sig[F32] { x }\n",
        ] {
            assert_eq!(formatted(kept), kept);
        }
    }

    /// S-539: the `init` that equals the default value stays, in any spelling,
    /// with a comment, in the block and the continuation forms (the syntax
    /// alone does not show that it can go: `let y = prev~(^y, 0)` takes its
    /// type from it). Only the layout of §3.2 changes.
    #[test]
    fn the_init_of_the_value_zero_stays() {
        let f = |body: &str| {
            format!("pub flow f(x: F32 at sample, n: I32 at sample, b: Bool at sample) -> F32 at sample {{\n{body}}}\n")
        };
        let cases = [
            ("  prev~(x, 00.00,)\n", "  prev~(x, 0.00)\n"),
            ("  delay~(\n    x,\n    4,\n    0.0\n  )\n", "  delay~(\n    x,\n    4,\n    0.0,\n  )\n"),
            (
                "  let y = prev~(x, // c\n    0.0) // d\n  y\n",
                "  let y = prev~(x,   // c\n                0.0) // d\n  y\n",
            ),
        ];
        for (body, want) in cases {
            assert_eq!(formatted(&f(body)), f(want), "{body}");
        }
        for body in ["  vdelay~(x, x, 8, 0x0_0) + prev~(x, (0.0e5))\n", "  prev~(n, 0)\n", "  prev~(b, false)\n"] {
            assert_eq!(formatted(&f(body)), f(body));
        }
    }

    /// The AST side does not decide again: a chosen node whose AST is not of
    /// the form the CST side saw is an internal error.
    #[test]
    fn a_chosen_node_of_another_form_is_an_internal_error() {
        let src = "fn f(move a: B) -> I32 {\n  return 1\n  2\n}\n";
        let parsed = crate::parse(FileId(0), src);
        let of =
            |kind: NodeKind| super::all_nodes(&parsed.cst).into_iter().find(|&n| parsed.cst.kind(n) == kind).unwrap();
        let (ret, head) = (of(NodeKind::ReturnStmt), of(NodeKind::Fn));
        for (rewrite, chosen, what) in [
            (super::tail_return_ast as fn(&mut Ast, &Parsed, &[NodeId]), ret, "not the last statement of its block"),
            (super::tail_return_ast, head, "no statement in a block"),
        ] {
            let mut ast = parsed.ast.clone();
            let caught =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| rewrite(&mut ast, &parsed, &[chosen])));
            let payload = caught.expect_err("an internal error");
            let bug = payload.downcast_ref::<onsa_diag::internal::InternalBug>().expect("a bug of the compiler");
            assert!(bug.message.contains(what), "{}", bug.message);
        }
    }

    /// Every node of `tests/spec` (the files without a syntax error) that a
    /// rewrite here can choose, and the block of a `return`, is made into one
    /// AST node of the kind the AST side reads (W3-11/b2 `mapcheck`:
    /// `Parsed::map` is not injective for every kind), and [`super::normalize`]
    /// takes the chosen ones.
    #[test]
    fn the_nodes_a_rewrite_can_choose_have_their_ast_node_in_every_case_file() {
        onsa_diag::stack::run(|| {
            let (mut nodes, mut chosen) = (0, 0);
            let files = crate::cst_tests::repo_files();
            let files: Vec<_> = files.iter().filter(|(name, _)| name.starts_with("tests/spec/")).collect();
            assert!(files.len() > 400, "only {} files", files.len());
            for (name, text) in files {
                let parsed = crate::parse(FileId(0), text);
                if parsed.syntax_errors() {
                    continue;
                }
                let counts = |map: &[NodeId]| {
                    let mut c = std::collections::HashMap::new();
                    map.iter().for_each(|&n| *c.entry(n).or_insert(0) += 1);
                    c
                };
                let (stmts, exprs) = (counts(&parsed.map.stmts), counts(&parsed.map.exprs));
                for n in super::all_nodes(&parsed.cst) {
                    let map = match parsed.cst.kind(n) {
                        NodeKind::ReturnStmt => &stmts,
                        NodeKind::Block => &exprs,
                        _ => continue,
                    };
                    assert_eq!(
                        map.get(&n),
                        Some(&1),
                        "{name}: {} at {:?}",
                        parsed.cst.kind(n).name(),
                        parsed.cst.span(n)
                    );
                    nodes += 1;
                }
                let choices = super::choose(&parsed.cst, &super::all_nodes(&parsed.cst));
                chosen += choices.chosen.iter().flatten().count();
                super::normalize(&parsed);
            }
            assert!(nodes > 1000 && chosen > 0, "{nodes} nodes, {chosen} chosen");
        });
    }
}
