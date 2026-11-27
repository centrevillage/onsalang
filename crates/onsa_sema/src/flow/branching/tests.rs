//! The reading of an `if` chain (§11.5): the conditions of its links and its
//! last `else`, the later `if`s with no `~` only.

use onsa_diag::FileId;
use onsa_syntax::ast::ExprKind;

use super::chain;

/// The texts of the conditions and of the last `else` of the chain of the
/// first `if` of the body `body`.
fn read(body: &str) -> (Vec<String>, Option<String>) {
    let src = format!("fn f(a: Bool, b: Bool, c: Bool) -> I32 {{\n  {body}\n}}\n");
    let ast = onsa_syntax::parse(FileId(0), &src).ast;
    let text = |e: onsa_syntax::ast::ExprId| {
        let s = ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    let ifs = (0..ast.exprs.len() as u32).map(onsa_syntax::ast::ExprId);
    let head = ifs.filter(|&e| matches!(ast.expr(e).kind, ExprKind::If { .. })).min_by_key(|&e| ast.expr(e).span.start);
    let c = chain(&ast, head.expect("an `if`"));
    (c.links.iter().map(|l| text(l.cond)).collect(), c.last.map(text))
}

fn texts(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|x| x.to_string()).collect()
}

#[test]
fn a_chain_is_read_to_its_last_else() {
    let (conds, last) = read("if~ a { 1 } else if b { 2 } else if c { 3 } else { 4 }");
    assert_eq!((conds, last.as_deref()), (texts(&["a", "b", "c"]), Some("{ 4 }")));
    let (conds, last) = read("if a { 1 } else if b { 2 } else { 3 }");
    assert_eq!((conds, last.as_deref()), (texts(&["a", "b"]), Some("{ 3 }")));
}

/// An `if` in the block of an `else` is the branch, not a link (§11.5: its
/// condition is evaluated as a part of the branch).
#[test]
fn an_if_in_an_else_block_is_the_branch() {
    let (conds, last) = read("if~ a { 1 } else { if b { 2 } else { 3 } }");
    assert_eq!((conds, last.as_deref()), (texts(&["a"]), Some("{ if b { 2 } else { 3 } }")));
    let (conds, last) = read("if a { 1 }");
    assert_eq!((conds, last), (texts(&["a"]), None));
}

/// The positions of the first expression of the kind `kind` (in the order
/// of the text) of the body `body`: of each part, its text and its position,
/// `Branch` with the first word of its head; `node`: of a walk of the nodes.
fn positions_of(body: &str, kind: fn(&ExprKind) -> bool, node: bool) -> Vec<(String, String)> {
    let src = format!("fn f(a: Bool, b: Bool, c: Bool, k: I32) -> I32 {{\n  {body}\n}}\n");
    let ast = onsa_syntax::parse(FileId(0), &src).ast;
    let text = |e: onsa_syntax::ast::ExprId| {
        let s = ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    let all = (0..ast.exprs.len() as u32).map(onsa_syntax::ast::ExprId);
    let e = all.filter(|&e| kind(&ast.expr(e).kind)).min_by_key(|&e| ast.expr(e).span.start).expect("the expression");
    let shown = |p: super::Pos| match p {
        super::Pos::Branch { head } => format!("Branch {}", text(head).split(' ').next().unwrap_or("")),
        p => format!("{p:?}"),
    };
    let ps = super::positions(&ast, e);
    let ps: Vec<_> = if node { ps.of_node().collect() } else { ps.collect() };
    ps.into_iter().map(|(x, p)| (text(x), shown(p))).collect()
}

fn pairs(xs: &[(&str, &str)]) -> Vec<(String, String)> {
    xs.iter().map(|(x, p)| (x.to_string(), p.to_string())).collect()
}

fn is_if(k: &ExprKind) -> bool {
    matches!(k, ExprKind::If { .. })
}

fn is_match(k: &ExprKind) -> bool {
    matches!(k, ExprKind::Match { .. })
}

/// A chain with no `~` (§11.5, S-1094): its first condition chooses, a
/// later one chooses where the ones before do not, its branches are of its
/// head; each later `if` is a node in the `else` before it, where a walk of
/// the nodes stops.
#[test]
fn the_positions_of_a_chain_with_no_tilde() {
    let body = "if a { 1 } else if b { 2 } else if c { 3 } else { 4 }";
    let link = |x: &str| (x.to_string(), "Link".to_string());
    let all = positions_of(body, is_if, false);
    let mut want = pairs(&[("a", "Cond"), ("{ 1 }", "Branch if")]);
    want.push(link("if b { 2 } else if c { 3 } else { 4 }"));
    want.extend(pairs(&[("b", "Choose"), ("{ 2 }", "Branch if")]));
    want.push(link("if c { 3 } else { 4 }"));
    want.extend(pairs(&[("c", "Choose"), ("{ 3 }", "Branch if"), ("{ 4 }", "Branch if")]));
    assert_eq!(all, want);
    assert_eq!(positions_of(body, is_if, true), want[..3]);
    let one = positions_of("if a { 1 } else { if b { 2 } else { 3 } }", is_if, false);
    assert_eq!(one, pairs(&[("a", "Cond"), ("{ 1 }", "Branch if"), ("{ if b { 2 } else { 3 } }", "Branch if")]));
    assert_eq!(positions_of("if a { 1 }", is_if, true), pairs(&[("a", "Cond"), ("{ 1 }", "Branch if")]));
}

/// An `if~` evaluates every branch (S-1094): its later conditions choose,
/// and its later `if`s are no nodes (no `Link`).
#[test]
fn the_positions_of_an_if_tilde_chain() {
    let body = "if~ a { 1 } else if b { 2 } else { 3 }";
    let want = pairs(&[("a", "Cond"), ("{ 1 }", "Always"), ("b", "Choose"), ("{ 2 }", "Always"), ("{ 3 }", "Always")]);
    assert_eq!(positions_of(body, is_if, false), want);
    assert_eq!(positions_of(body, is_if, true), want);
}

/// A `match`: the scrutinee chooses, a guard chooses where the arms before
/// are not taken, an arm body is a branch of it; of a `match~` the bodies
/// are evaluated every time (S-1094, S-1131).
#[test]
fn the_positions_of_a_match_and_a_match_tilde() {
    let body = "match k { 0 if a => 1, 1 => 2, _ if b => 3, _ => 4 }";
    let want = pairs(&[
        ("k", "Cond"),
        ("a", "Choose"),
        ("1", "Branch match"),
        ("2", "Branch match"),
        ("b", "Choose"),
        ("3", "Branch match"),
        ("4", "Branch match"),
    ]);
    assert_eq!(positions_of(body, is_match, false), want);
    let body = "match~ k { 0 if a => 1, _ => 2 }";
    let want = pairs(&[("k", "Cond"), ("a", "Choose"), ("1", "Always"), ("2", "Always")]);
    assert_eq!(positions_of(body, is_match, false), want);
}

/// The left of `&&` / `||` chooses its right; the operands of another
/// operator, and the parts of the other kinds, are evaluated every time.
#[test]
fn the_positions_of_a_short_circuit_and_of_other_kinds() {
    let and = |k: &ExprKind| matches!(k, ExprKind::Binary { op: onsa_syntax::ast::BinOp::And, .. });
    assert_eq!(positions_of("if a && b { 1 } else { 2 }", and, false), pairs(&[("a", "Cond"), ("b", "Right")]));
    let or = |k: &ExprKind| matches!(k, ExprKind::Binary { op: onsa_syntax::ast::BinOp::Or, .. });
    assert_eq!(positions_of("if a || b { 1 } else { 2 }", or, false), pairs(&[("a", "Cond"), ("b", "Right")]));
    let add = |k: &ExprKind| matches!(k, ExprKind::Binary { op: onsa_syntax::ast::BinOp::Add, .. });
    assert_eq!(positions_of("k + 1", add, false), pairs(&[("k", "Always"), ("1", "Always")]));
    let tuple = |k: &ExprKind| matches!(k, ExprKind::Tuple(_));
    assert_eq!(positions_of("(k, 2).0", tuple, false), pairs(&[("k", "Always"), ("2", "Always")]));
}

/// The `.onsa` files under `dir`, in its directories too.
fn files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    for p in std::fs::read_dir(dir).expect("the cases").flatten().map(|d| d.path()) {
        if p.is_dir() {
            files(&p, out);
        } else if p.extension().is_some_and(|x| x == "onsa") {
            out.push(p);
        }
    }
}

/// The chain of `e` ([`chain`]): of each link its condition and its branch,
/// then its last `else`.
fn chain_parts(ast: &onsa_syntax::ast::Ast, e: onsa_syntax::ast::ExprId) -> Vec<u32> {
    let c = chain(ast, e);
    c.links.iter().flat_map(|l| [l.cond.0, l.then.0]).chain(c.last.map(|x| x.0)).collect()
}

/// Of every expression of the flow cases, the positions are of the parts
/// the walks read, and of a chain as [`chain`] reads it (D-15: the two
/// readings of a chain agree): in a walk of the nodes, the parts of
/// `sub_exprs`, of an `if~` those of its chain; the whole positions of an
/// `if` with no `~`, the parts of its chain and each later `if` once.
#[test]
fn the_positions_are_the_parts_and_the_chain_of_every_expression() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec");
    let mut all = Vec::new();
    for sub in ["flow", "flow_clock", "flow_semantics", "flow_syntax"] {
        files(&root.join(sub), &mut all);
    }
    let (mut ifs, mut exprs) = (0, 0);
    for p in &all {
        let text = std::fs::read_to_string(p).expect("a case");
        let ast = onsa_syntax::parse(FileId(0), &text).ast;
        for e in (0..ast.exprs.len() as u32).map(onsa_syntax::ast::ExprId) {
            let sorted = |mut v: Vec<u32>| {
                v.sort_unstable();
                v
            };
            let node = sorted(super::positions(&ast, e).of_node().map(|(x, _)| x.0).collect());
            let parts = match ast.expr(e).kind {
                ExprKind::If { tilde: Some(_), .. } => chain_parts(&ast, e),
                _ => ast.sub_exprs(e).into_iter().map(|x| x.0).collect(),
            };
            assert_eq!(node, sorted(parts), "{} at {:?}", p.display(), ast.expr(e).span);
            if let ExprKind::If { tilde: None, .. } = ast.expr(e).kind {
                let whole = sorted(super::positions(&ast, e).map(|(x, _)| x.0).collect());
                let mut want = chain_parts(&ast, e);
                want.extend(chain(&ast, e).links.iter().skip(1).map(|l| l.at.0));
                assert_eq!(whole, sorted(want), "{} at {:?}", p.display(), ast.expr(e).span);
                ifs += 1;
            }
            exprs += 1;
        }
    }
    assert!(all.len() > 100 && ifs > 100 && exprs > 10_000, "{} files, {ifs} `if`s, {exprs} expressions", all.len());
}
