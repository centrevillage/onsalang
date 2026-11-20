//! The order in which an `if~` evaluates its parts, seen by the position of the panic that `onsa test` reports (W7-06 U2/t; spec §11.5, §18.1:
//! `span` is the position of the expression that panicked; S-1094 (1), S-110, R-14).
//!
//! §11.5: "選ぶ側（`if~` の連鎖の条件 …）は普通の `if` / `match` と同じく上から評価し、最初に真になった条件か合った腕で止める（後ろの条件とガードは
//! 評価しない）。`~` が全て評価するのは枝と腕の本体である。評価の順は、選ぶ側を先に、次に全ての枝と腕の本体を書いた順である". With the input 0 every
//! division by `x` panics, so the first part that is evaluated is the one that the failure reports; the cases in tests/spec/flow_semantics/
//! if_tilde_select_order.onsa see only whether a panic happens, and this file sees which one. The line of each part is marked in the source by a
//! comment (`// C`, `// T`, ...), and no test fixes a column.
//!
//! Each test writes one package of one file and runs `onsa test --json` on it.

use crate::test_support::*;

const ACC: &str = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n\n";

/// The package source: `ACC`, the flow `f` (written in `flow`, with `x` as its `sample` input of `I32`) and a test that renders it over `xs`.
fn source(flow: &str, xs: &[i32]) -> String {
    let list = xs.iter().map(i32::to_string).collect::<Vec<_>>().join(", ");
    format!(
        "{ACC}{flow}\ntest \"t\" {{\n  let xs: [I32; {n}] = [{list}]\n  let o = f.render(xs, 8.0)\n  assert o.out[0] == 0.0\n}}\n",
        n = xs.len()
    )
}

/// The 1-based line of the first line of `src` that ends with the comment `// <mark>`.
fn line_of(src: &str, mark: &str) -> u64 {
    let tag = format!("// {mark}");
    let at = src
        .lines()
        .position(|l| l.trim_end().ends_with(&tag))
        .unwrap_or_else(|| panic!("no line marked {tag} in:\n{src}"));
    at as u64 + 1
}

/// The line of the panic of the test `t` of the source, or `None` when the test passes.
fn panic_line(tag: &str, src: &str) -> Option<u64> {
    let d = Dir::pkg(tag);
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    let rec = record(&doc, "m", "t");
    if str_of(rec, "status") == "ok" {
        assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
        return None;
    }
    let f = failure_of(rec);
    assert_eq!(str_of(f, "kind"), "panic", "{f}");
    Some(span_of(&f["span"]).line)
}

/// §11.5: the condition of the chain is of the side that selects, which goes first: the panic of the condition, not that of the branches
/// above and below it in the text.
#[test]
fn the_condition_is_evaluated_before_the_branches() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ 100 / x > 5 { // C
    acc~(F32.round_from(100 / x)) // T
  } else {
    F32.round_from(100 / x) // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("cond_first", &src), Some(line_of(&src, "C")));
}

/// §11.5: "次に全ての枝と腕の本体を書いた順": the branch that is not chosen comes first when it is written first (`x > 0` is false for 0),
/// and the `else` is reached only if the branches above it are fine.
#[test]
fn the_branches_are_evaluated_in_the_order_written() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x > 0 { // C
    acc~(F32.round_from(100 / x)) // T
  } else {
    F32.round_from(200 / x) // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("branch_order", &src), Some(line_of(&src, "T")));
    // The first branch does not panic where the second does: the `else` is the panic.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x >= 0 { // C
    acc~(1.0) // T
  } else {
    F32.round_from(200 / x) // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("else_reached", &src), Some(line_of(&src, "E")));
}

/// A branch in the middle of a chain is evaluated in its place: after the branches written before it and before the later ones.
#[test]
fn the_branches_of_a_chain_are_evaluated_in_the_order_written() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x > 5 { // C1
    acc~(1.0) // T1
  } else if x > 0 { // C2
    F32.round_from(100 / x) // T2
  } else {
    F32.round_from(200 / x) // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("chain_branch_order", &src), Some(line_of(&src, "T2")));
}

/// §11.5: the second condition (evaluated, the first is false for 0) is of the side that selects, so it goes before the first branch,
/// which is written above it (`c1, a, c2, b, e` in the order of the text is not the order of the evaluation).
#[test]
fn the_second_condition_is_evaluated_before_the_first_branch() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x > 0 { // C1
    acc~(F32.round_from(200 / x)) // T1
  } else if 100 / x > 5 { // C2
    F32.round_from(300 / x) // T2
  } else {
    0.0
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("second_condition", &src), Some(line_of(&src, "C2")));
}

/// §11.5: "`c1` が真なら `c2` を評価しない": the first condition is true for 0, so the second is not evaluated, and the panic is that of the
/// first branch (every branch is evaluated, the first is written first).
#[test]
fn a_condition_after_a_true_one_is_not_evaluated_but_the_branches_are() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x == 0 { // C1
    F32.round_from(200 / x) // T1
  } else if 100 / x > 5 { // C2
    acc~(1.0) // T2
  } else {
    0.0
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("true_then_branches", &src), Some(line_of(&src, "T1")));
    // With a branch that does not panic, no part of the chain panics: the second condition is not evaluated.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x == 0 { // C1
    acc~(0.0) // T1
  } else if 100 / x > 5 { // C2
    2.0 // T2
  } else {
    0.0
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("true_then_no_panic", &src), None);
}

/// §11.5: "`else { if~ c2 { b } else { e } }` と入れ子に書いた `if~` は else の枝の本体なので、その条件は常に評価する": the condition of the `if~`
/// in the `else` is evaluated although the outer condition is true, and it is evaluated after the first branch.
#[test]
fn an_if_tilde_in_the_else_has_its_condition_evaluated() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x == 0 { // C1
    acc~(1.0) // T1
  } else {
    if~ 100 / x > 5 { // C2
      acc~(10.0) // T2
    } else {
      0.0
    }
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("nested_in_else", &src), Some(line_of(&src, "C2")));
    // The first branch comes before it: where it panics too, it is the first.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x == 0 { // C1
    acc~(F32.round_from(100 / x)) // T1
  } else {
    if~ 100 / x > 5 { // C2
      acc~(10.0) // T2
    } else {
      0.0
    }
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("nested_in_else_after_a_branch", &src), Some(line_of(&src, "T1")));
}

/// R-14, §11.5: the branch that is not chosen is evaluated, and its panic is the panic of the call (in a sample after other samples that
/// give no panic: the failure is the one of the first sample that panics, and the branch of that sample).
#[test]
fn a_branch_that_is_not_chosen_panics() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  if~ x > 0 { // C
    acc~(F32.round_from(100 / x)) // T
  } else {
    0.0 // E
  }
}
",
        &[5, 20, 0],
    );
    assert_eq!(panic_line("untaken_branch", &src), Some(line_of(&src, "T")));
}
