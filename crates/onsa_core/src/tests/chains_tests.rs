//! The chains the lowering makes of a list (W8-02 U5a, V-22): the fields of
//! a derived `==`, the alternatives of a `|` that binds nothing and the arms
//! of a `match~` are trees ⌈log2 n⌉ deep, not chains n deep. Each source is
//! lowered on a thread of a large stack (`onsa_diag::stack`): the Core of
//! the chains before was 1000 deep.

use super::core;
use crate::ir::*;
use crate::walk::{Child, Part, Role, block_children, expr_children, place_children, stmt_children};

/// The number of nodes on the longest path from `c` down (a block, a
/// statement, an expression and a place are each one).
fn child_depth(c: Child) -> usize {
    match c {
        Child::Expr(e, ..) => 1 + max_of(|f| expr_children(e, f)),
        Child::Block(b, ..) => block_depth(b),
        Child::Place(p, role) => 1 + max_of(|f| place_children(p, role, f)),
    }
}

fn block_depth(b: &Block) -> usize {
    let mut d = 0;
    block_children(b, Role::Read, &mut |p| {
        d = d.max(match p {
            Part::Stmt(s) => 1 + max_of(|f| stmt_children(s, f)),
            Part::Value(v, _) => child_depth(Child::Expr(v, crate::walk::Eval::Always, Role::Read)),
        })
    });
    1 + d
}

fn max_of<'a>(list: impl FnOnce(&mut dyn FnMut(Child<'a>))) -> usize {
    let mut d = 0;
    list(&mut |c| d = d.max(child_depth(c)));
    d
}

/// The depth of the deepest body of `m`.
fn deepest(m: &Module) -> usize {
    m.fns.iter().filter_map(|f| f.body.as_ref()).map(block_depth).max().unwrap_or(0)
}

/// The depth of the deepest body of `src` lowered, on a large stack.
fn depth_of(src: String) -> usize {
    onsa_diag::stack::spawn("chains", move || deepest(&core(&src))).unwrap().join().unwrap()
}

/// The deepest body of the chain of `n` is deeper than that of a chain of 2
/// by the levels of a tree, ⌈log2 n⌉ = `levels`, not by `n`: at most two
/// nodes for each level (an `IfExpr` and its block).
fn assert_log_deep(of: impl Fn(usize) -> String, n: usize, levels: usize) {
    let (short, long) = (depth_of(of(2)), depth_of(of(n)));
    assert!(long <= short + 2 * levels, "{n}: {long}, 2: {short}");
}

#[test]
fn the_derived_eq_of_1000_fields_is_a_balanced_tree() {
    let of = |n: usize| {
        let fields: String = (0..n).map(|i| format!("  a{i}: I32,\n")).collect();
        format!("pub struct P: PartialEq {{\n{fields}}}\npub fn same(x: P, y: P) -> Bool {{\n  x == y\n}}\n")
    };
    assert_log_deep(of, 1000, 10);
}

#[test]
fn an_alternative_of_1000_is_a_balanced_tree() {
    let of = |n: usize| {
        let alts: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        let alts = alts.join(" | ");
        format!(
            "pub fn f(x: I32) -> I32 {{\n  var r = 0\n  match x {{\n    {alts} => {{ r = 1 }},\n    _ => {{ r = 2 }},\n  }}\n  r\n}}\n"
        )
    };
    assert_log_deep(of, 1000, 10);
}

#[test]
fn a_match_tilde_of_200_arms_is_a_binary_tree() {
    let acc = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n";
    let of = |n: usize| {
        let arms: String = (0..n - 1).map(|k| format!("    {k} => acc~({k}.0),\n")).collect();
        format!(
            "{acc}pub flow f(k: U32 at sample) -> F32 at sample {{\n  match~ k {{\n{arms}    _ => acc~(0.5),\n  }}\n}}\n"
        )
    };
    assert_log_deep(of, 200, 8);
}

/// The line of `text` with `op` in it, trimmed.
fn line_with<'a>(text: &'a str, op: &str) -> &'a str {
    text.lines().find(|l| l.contains(op)).unwrap_or_else(|| panic!("no `{op}`:\n{text}")).trim()
}

/// The larger half is on the left, so a chain of up to three is as it was
/// before the trees (`(a && b) && c`) and five is `((a && b) && c) && (d && e)`.
#[test]
fn the_larger_half_of_a_chain_is_on_the_left() {
    let eq = |n: usize| {
        let fields: String = (0..n).map(|i| format!("  a{i}: I32,\n")).collect();
        let src = format!("pub struct P: PartialEq {{\n{fields}}}\npub fn same(x: P, y: P) -> Bool {{\n  x == y\n}}\n");
        line_with(&crate::dump(&core(&src)), "&&").to_string()
    };
    assert_eq!(eq(3), "(((a.0 == b.0) && (a.1 == b.1)) && (a.2 == b.2))");
    assert_eq!(eq(5), "((((a.0 == b.0) && (a.1 == b.1)) && (a.2 == b.2)) && ((a.3 == b.3) && (a.4 == b.4)))");
    let alts = |n: usize| {
        let alts: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        let src = format!(
            "pub fn f(x: I32) -> I32 {{\n  var r = 0\n  match x {{\n    {} => {{ r = 1 }},\n    _ => {{ r = 2 }},\n  }}\n  r\n}}\n",
            alts.join(" | ")
        );
        let line = line_with(&crate::dump(&core(&src)), "||").to_string();
        line.trim_start_matches("if ((!__done) && ").trim_end_matches(") {").to_string()
    };
    assert_eq!(alts(3), "(((x == 0:I32) || (x == 1:I32)) || (x == 2:I32))");
    assert_eq!(alts(5), "((((x == 0:I32) || (x == 1:I32)) || (x == 2:I32)) || ((x == 3:I32) || (x == 4:I32)))");
}

/// The compares of the tree of a `match~` of `n` arms, from the top: a left
/// of one by `==` and else `<` the middle, so 2 and 3 arms are the chain of
/// `==` they were. (They are the `if`s after the last write of `__arm`.)
#[test]
fn the_tree_of_the_arms_splits_at_the_middle() {
    let acc = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n";
    let tree = |n: usize| {
        let arms: String = (0..n - 1).map(|k| format!("    {k} => acc~({k}.0),\n")).collect();
        let src = format!(
            "{acc}pub flow f(k: U32 at sample) -> F32 at sample {{\n  match~ k {{\n{arms}    _ => acc~(0.5),\n  }}\n}}\n"
        );
        let text = crate::dump(&core(&src));
        let after = &text[text.rfind("__arm = ").unwrap()..];
        let ifs = after.lines().filter_map(|l| l.trim().strip_prefix("if (__arm")?.strip_suffix(") {"));
        ifs.map(|c| c.trim_start_matches(|ch: char| ch == '@' || ch.is_ascii_digit()).trim().to_string())
            .collect::<Vec<_>>()
    };
    assert_eq!(tree(2), ["== 0:U32"]);
    assert_eq!(tree(3), ["== 0:U32", "== 1:U32"]);
    assert_eq!(tree(4), ["< 2:U32", "== 0:U32", "== 2:U32"]);
    assert_eq!(tree(5), ["< 2:U32", "== 0:U32", "== 2:U32", "== 3:U32"]);
    assert_eq!(tree(8), ["< 4:U32", "< 2:U32", "== 0:U32", "== 2:U32", "< 6:U32", "== 4:U32", "== 6:U32"]);
}

#[test]
fn the_parts_of_a_struct_pattern_of_300_are_a_balanced_tree() {
    let of = |n: usize| {
        let fields: String = (0..n).map(|i| format!("  a{i}: I32,\n")).collect();
        let pat: Vec<String> = (0..n).map(|i| format!("a{i}: {i}")).collect();
        format!(
            "pub struct S {{\n{fields}}}\npub fn f(s: S) -> I32 {{\n  var r = 0\n  match s {{\n    S {{ {} }} => {{ r = 1 }},\n    _ => {{ r = 2 }},\n  }}\n  r\n}}\n",
            pat.join(", ")
        )
    };
    assert_log_deep(of, 300, 9);
}

#[test]
fn the_parts_of_a_tuple_pattern_of_300_are_a_balanced_tree() {
    let of = |n: usize| {
        let ty: Vec<&str> = (0..n).map(|_| "I32").collect();
        let pat: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        format!(
            "pub fn f(s: ({})) -> I32 {{\n  var r = 0\n  match s {{\n    ({}) => {{ r = 1 }},\n    _ => {{ r = 2 }},\n  }}\n  r\n}}\n",
            ty.join(", "),
            pat.join(", ")
        )
    };
    assert_log_deep(of, 300, 9);
}

#[test]
fn the_parts_of_a_variant_pattern_of_300_are_a_balanced_tree() {
    let of = |n: usize| {
        let ty: Vec<&str> = (0..n).map(|_| "I32").collect();
        let pat: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        format!(
            "pub enum E {{\n  V({}),\n  W,\n}}\npub fn f(s: E) -> I32 {{\n  var r = 0\n  match s {{\n    E.V({}) => {{ r = 1 }},\n    _ => {{ r = 2 }},\n  }}\n  r\n}}\n",
            ty.join(", "),
            pat.join(", ")
        )
    };
    assert_log_deep(of, 300, 9);
}
