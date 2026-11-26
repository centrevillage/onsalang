//! Where `onsa test` reports a panic of an expression that reads an event (W7-11 U3/t; spec §11.3, §11.10, §11.11; S-563, S-1158, S-1197, S-1239): an expression that has no operand of a periodic clock is computed at the events,
//! and in a position that a condition selects (a branch of an `if`, the right side of `&&`) it is computed only at the events where the condition holds ("条件が成り立つときだけ評価する"; "その位置を選ぶ条件…が全て `init`・`block` の段で決まるなら、式の段と条件の段のうち最も速い段で、
//! 条件が成り立つときだけ評価する"; the same for a condition decided by the same event); a `let` computes it whether or not a branch is taken. A call with a modifier evaluates its arguments and its condition in the order of the
//! text, then the part (§11.3: "引数と修飾子の条件を字面の順に評価してから、初期化と部品の段を外の修飾子から行い").
//!
//! The events of `msgs` are one at each frame, with the kind x and the vel 0: the kind 1 is an on event whose vel is 0, so `100 / vel(m)` stops at an on event. A module is one flow `f` and one test `t` that renders it;
//! one launch of `onsa test` reads all the modules. The places of a division are named by a letter: `@A` is the divisor of the argument of the head, `@C` the one of the condition of `when~` (a value of `sample` over the last event), `@P` the one
//! in the part; each is `(.. - ..)` (0: the run stops there) or `(.. + 1)` (made safe, so the next place stops), with the letter in a comment at the end of the line, which is what the test looks for. The texts are written from the spec;
//! none is taken from the output of the compiler.

use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, str_of, test_json};

const PRELUDE: &str = "\
pub struct Msg: Default {
  kind: U32,
  vel: U32,
}

rt fn vel(m: Msg) -> U32 {
  m.vel
}

rt fn is_on(m: Msg) -> Bool {
  m.kind == 1
}

flow msgs(x: U32 at sample) -> Msg at event {
  Some(Msg { kind: x, vel: 0 })
}

flow gen(v: U32 at sample) -> U32 at event {
  Some(v)
}

flow part(v: U32 at sample) -> U32 at sample {
  let q = 100 / @P
  q
}

";

/// Replace each `@X` by the divisor of the place X with a comment `// X`: the zero when X is not in `safe`, a divisor over 0 otherwise.
fn fill(text: &str, safe: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match chars.peek().copied() {
            Some(l) if c == '@' && l.is_ascii_uppercase() => {
                chars.next();
                let (zero, one) = match l {
                    'A' => ("(sample_tick() - sample_tick())", "(sample_tick() + 1)"),
                    'C' => ("((e at sample) - (e at sample))", "((e at sample) + 1)"),
                    _ => ("(v - v)", "(v + 1)"),
                };
                out.push_str(&format!("{} // {l}", if safe.contains(l) { one } else { zero }));
            }
            _ => out.push(c),
        }
    }
    out
}

/// The test `t` of a module: the flow `f` is rendered over the given values of `x` (none: over one frame), and the assertion is never reached when it stops.
fn test_of(xs: Option<&str>, first: &str) -> String {
    match xs {
        Some(list) => format!(
            "\ntest \"t\" {{\n  let xs: [U32; 3] = {list}\n  let o = f.render(xs, 8.0)\n  assert o.out[0] == {first}\n}}\n"
        ),
        None => format!("\ntest \"t\" {{\n  let o = f.render(1, 8.0)\n  assert o.out[0] == {first}\n}}\n"),
    }
}

/// (module name, text, the text of the line that stops the run, or None when the test passes)
fn cases() -> Vec<(String, String, Option<String>)> {
    let guard = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let m = msgs~(x)\n  if is_on(m) { 100 / vel(m) } else { x } // D\n}\n";
    let and_right = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let m = msgs~(x)\n  if is_on(m) && 100 / vel(m) > 3 { x } else { 0 } // D\n}\n";
    let moved = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let m = msgs~(x)\n  let y = 100 / vel(m) // D\n  if is_on(m) { y } else { x }\n}\n";
    let none = "[2, 2, 2]";
    let on = "[2, 2, 1]";
    let mut all = Vec::new();
    for (name, body, first) in [("guard", guard, "2"), ("and_right", and_right, "0")] {
        all.push((format!("{name}_false"), fill(&[PRELUDE, body, &test_of(Some(none), first)].concat(), "ACP"), None));
        all.push((
            format!("{name}_true"),
            fill(&[PRELUDE, body, &test_of(Some(on), first)].concat(), "ACP"),
            Some("// D".to_string()),
        ));
    }
    let text = fill(&[PRELUDE, moved, &test_of(Some(none), "2")].concat(), "ACP");
    all.push(("moved_to_a_let".to_string(), text, Some("// D".to_string())));
    // The head, the condition and the part: the argument first, then the condition, then the part; the order of the text is the order of the places.
    let order = "ACP";
    let call = "pub flow f() -> U32 at sample {\n  let e = gen~(sample_tick())\n  part~(\n    100 / @A\n  ).when~(\n    3 < 100 / @C\n  )\n}\n";
    for k in 0..order.len() {
        let text = [PRELUDE, call, &test_of(None, "0")].concat();
        let text = fill(&text, &order[..k]);
        all.push((format!("when_order_{k}"), text, Some(format!("// {}", &order[k..=k]))));
    }
    all
}

/// §11.3 "条件の位置の中の…式は…その位置を選ぶ条件が…その式と同じ刻みで決まるときだけ…その刻みで条件が成り立つときだけ評価する"; §11.3 "本体の `let` の値と出力の式も、読まれるか、どこで読まれるかによらず、その段で評価する"; §11.3 "値は `let` に分けても分けなくても同じである"; §11.10 "引数と修飾子の条件を字面の順に評価してから、…部品". One launch reads the 8 modules: a division in a branch chosen by an event stops the run at the event where the condition holds and not at the
/// others (the same for the right side of `&&`); moved to a `let` it stops at the first event; the argument, the condition and the part of a `when~` stop in this order.
#[test]
fn the_panic_of_an_expression_that_reads_an_event_is_at_the_events_the_condition_holds_u3() {
    let d = Dir::pkg("event_read_panics");
    let all = cases();
    for (name, text, first) in &all {
        if let Some(first) = first {
            assert_eq!(
                text.lines().filter(|l| l.contains(first.as_str())).count(),
                1,
                "`{first}` is on one line: {text}"
            );
        }
        d.write(&format!("{name}.onsa"), text);
    }
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{}", out.stdout);
    let mut wrong = Vec::new();
    for (name, text, first) in &all {
        let rec = record(&doc, name, "t");
        match first {
            None => {
                if str_of(rec, "status") != "ok" {
                    wrong.push(format!("{name}: the test should pass: {rec}"));
                }
            }
            Some(first) => {
                let at = span_of(&failure_of(rec)["span"]);
                let want = line_of(text, first);
                if at.file != format!("{name}.onsa") || at.line != want {
                    wrong.push(format!("{name}: want the line {want} (`{first}`), stopped at {}:{}", at.file, at.line));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
