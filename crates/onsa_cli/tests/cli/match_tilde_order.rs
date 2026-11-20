//! The order in which a `match~` evaluates its parts, seen by the position of the panic that `onsa test` reports (W7-06 U3b/t; spec §11.5, §18.1:
//! `span` is the position of the expression that panicked; S-1094 (1), S-110, R-14).
//!
//! §11.5: "選ぶ側（`match~` の対象とパターンとガード）は普通の `if` / `match` と同じく上から評価し、最初に合った腕で止める（後ろの条件とガードは評価しない）。
//! `~` が全て評価するのは枝と腕の本体である。評価の順は、選ぶ側を先に、次に全ての枝と腕の本体を書いた順である". With the input 0 every division by `x`
//! panics, so the first part that is evaluated is the one that the failure reports; the cases in tests/spec/flow_semantics/match_tilde_select_order.onsa see
//! only whether a panic happens, and this file sees which one. The line of each part is marked in the source by a comment (`// C`, `// G`, `// T`, ...), and no
//! test fixes a column.
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

/// §11.5: the target is of the side that selects, which goes first: the panic of the target, not that of a guard or a body below it in the text.
#[test]
fn the_target_is_evaluated_before_the_guards_and_the_bodies() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ 100 / x { // C
    n if 200 / n > 5 => { // G
      acc~(F32.round_from(300 / x)) // T
    },
    _ => F32.round_from(400 / x), // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("target_first", &src), Some(line_of(&src, "C")));
}

/// §11.5: the guard of the arm that matches (evaluated, the pattern `n` matches) is of the side that selects, so it goes before the body written
/// on the lines under it.
#[test]
fn a_guard_is_evaluated_before_the_bodies() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    n if 100 / n > 5 => { // G
      acc~(F32.round_from(200 / x)) // T
    },
    _ => F32.round_from(300 / x), // E
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("guard_first", &src), Some(line_of(&src, "G")));
}

/// §11.5: the second guard (evaluated, the first is false for 0) goes before the body of the first arm, which is written above it
/// (`g1, t1, g2, t2` in the order of the text is not the order of the evaluation).
#[test]
fn the_second_guard_is_evaluated_before_the_first_body() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    n if n < 0 => { // G1
      F32.round_from(200 / x) // T1
    },
    n if 100 / n > 5 => { // G2
      acc~(F32.round_from(300 / x)) // T2
    },
    _ => 0.0,
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("second_guard", &src), Some(line_of(&src, "G2")));
}

/// §11.5: "次に全ての枝と腕の本体を書いた順": the body of the arm that is taken (here the first) comes first when it is written first, and the
/// one of an arm that is not taken is reached only if the bodies above it are fine.
#[test]
fn the_bodies_are_evaluated_in_the_order_written() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    0 => { // C1
      acc~(F32.round_from(100 / x)) // T1
    },
    _ => F32.round_from(200 / x), // T2
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("body_order", &src), Some(line_of(&src, "T1")));
    // The first body does not panic where the second does: the second is the panic.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    0 => { // C1
      acc~(0.0) // T1
    },
    _ => F32.round_from(200 / x), // T2
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("second_body", &src), Some(line_of(&src, "T2")));
}

/// A body in the middle of the arms that is not taken is evaluated in its place: after the bodies written before it and before the later ones.
#[test]
fn the_bodies_of_three_arms_are_evaluated_in_the_order_written() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    5 => { // C1
      acc~(1.0) // T1
    },
    n if n > -1 => { // C2
      F32.round_from(100 / x) // T2
    },
    _ => F32.round_from(200 / x), // T3
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("three_bodies", &src), Some(line_of(&src, "T2")));
}

/// §11.5: the guard of an arm after the one that is taken is not evaluated, and the bodies are: the panic is that of the last body, not of the
/// second guard, which is written above it.
#[test]
fn a_guard_after_the_taken_arm_is_not_evaluated_but_the_bodies_are() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    n if n <= 0 => { // G1
      acc~(1.0) // T1
    },
    n if 100 / n > 5 => { // G2
      2.0 // T2
    },
    _ => F32.round_from(300 / x), // T3
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("guard_not_evaluated", &src), Some(line_of(&src, "T3")));
    // Where the last body does not panic either, nothing does: the second guard is not evaluated.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    n if n <= 0 => { // G1
      acc~(0.0) // T1
    },
    n if 100 / n > 5 => { // G2
      2.0 // T2
    },
    _ => 3.0,
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("guard_not_evaluated_no_panic", &src), None);
}

/// §11.5: the target of a `match~` in the body of an arm is evaluated whatever the outer arm is, after the bodies written before it.
#[test]
fn the_target_of_a_match_tilde_in_an_arm_is_evaluated_in_its_place() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    0 => { // C1
      acc~(1.0) // T1
    },
    _ => { // C2
      match~ 100 / x { // C3
        0 => 2.0,
        _ => acc~(3.0),
      }
    },
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("inner_target", &src), Some(line_of(&src, "C3")));
    // The body of the first arm is written before it: where that panics too, it is the first.
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    0 => { // C1
      acc~(F32.round_from(100 / x)) // T1
    },
    _ => { // C2
      match~ 100 / x { // C3
        0 => 2.0,
        _ => acc~(3.0),
      }
    },
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("inner_target_after_a_body", &src), Some(line_of(&src, "T1")));
}

/// §11.5: the condition of an `if~` in the body of an arm is of the side that selects of that `if~`, and the body of the arm that comes after
/// it in the text is evaluated after the whole first body.
#[test]
fn an_if_tilde_in_an_arm_is_evaluated_in_its_place() {
    let src = source(
        "pub flow f(x: I32 at sample) -> F32 at sample {
  match~ x {
    0 => { // C1
      if~ 100 / x > 5 { // C2
        acc~(1.0) // T2
      } else {
        0.0
      }
    },
    _ => F32.round_from(200 / x), // T3
  }
}
",
        &[0],
    );
    assert_eq!(panic_line("if_tilde_in_an_arm", &src), Some(line_of(&src, "C2")));
}

/// §11.5: the guard `100 / v` is tried only where the pattern `Some(v)` matches: not for `None`, where no part of the `match~` panics; for `Some(0)`
/// the pattern matches and the guard divides by zero.
#[test]
fn the_guard_of_an_arm_whose_pattern_does_not_match_is_not_evaluated() {
    let flow = "pub flow f(x: I32 at sample) -> F32 at sample {
  let o: Option[I32] = if x >= 0 { Some(x) } else { None }
  match~ o {
    Some(v) if 100 / v > 5 => { // G
      acc~(1.0) // T
    },
    Some(_) => 2.0,
    None => 0.0,
  }
}
";
    assert_eq!(panic_line("guard_of_none", &source(flow, &[-1])), None);
    let src = source(flow, &[0]);
    assert_eq!(panic_line("guard_of_some", &src), Some(line_of(&src, "G")));
}
