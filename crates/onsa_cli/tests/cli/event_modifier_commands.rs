//! Which of several panics `onsa test` reports when a part that has an event, or that gives one, is under a `.when~` (W7-17 U4/t; spec §11.10, §11.11, §11.3; S-562, S-1233, S-1234): a stopped part still gets its events, its
//! arguments and conditions are evaluated whether it runs or not, and a stopped maker of a `sample` expression gives no event (the values are in `event_when_receiver_values.onsa` and `event_modifier_mix_values.onsa`).
//! A case is a module with a flow `f` that has a division by 0 in each of two to three places that run at the frame 0, and the line of the one that stops the run (`failure.span`, the line only).
//!
//! The places are named by a letter: `@A` is the divisor of `100 / @A`, `(v - v)` (0: the run stops there) or `(v + 1)` (made safe, so the next place stops); the variable is `v` for A and C, `e` for G, and the letters T U V D are
//! places of `sample` (`sample_tick() * 0` or `sample_tick() + 1`). V is the condition `100 / @V > 1000`, false when it is safe, so the call is stopped. Each group is run with its places made safe from the first one on, so a line says
//! which came first; a place that is not in the order (T, C of a stopped part) is not made safe, so it stops the run if it is reached. One launch of `onsa test` reads all the modules.

use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, test_json};

const PRELUDE: &str = "\
flow gen(v: U32 at sample) -> U32 at event {
  Some(v)
}

";

/// A part with a division in the event stage (G) and a receiver of the event of a maker (C).
const DACC: &str = "\
flow dacc(e: U32 at event) -> U32 at sample {
  let q = 100 / @G
  q
}

";
const RCV: &str = "\
flow rcv(v: U32 at event) -> U32 at sample {
  let q = 100 / @C
  q
}

";
/// A part with a division in the stage of sample (T), and a maker that gives from a `sample` expression (T).
const RSD: &str = "\
flow rsd(x: U32 at sample) -> U32 at sample {
  let q = 100 / @T
  x + q
}

";
const MK: &str = "\
flow mk(v: U32 at sample) -> U32 at event {
  let z = 100 / @T
  Some(v + z)
}

";

/// Replace each `@X` by the divisor of the place X (0 when X is not in `safe`, 1 + the value otherwise) and put `// X` at the end of its line.
fn fill(text: &str, safe: &str) -> String {
    let mut out = String::new();
    for line in text.lines() {
        let mut placed = None;
        let mut row = String::new();
        let mut chars = line.chars().peekable();
        while let Some(c) = chars.next() {
            match chars.peek().copied() {
                Some(l) if c == '@' && l.is_ascii_uppercase() => {
                    chars.next();
                    let var = match l {
                        'A' | 'C' => Some("v"),
                        'G' => Some("e"),
                        _ => None,
                    };
                    let (zero, one) = match var {
                        Some(v) => (format!("{v} - {v}"), format!("{v} + 1")),
                        None => ("sample_tick() * 0".to_string(), "sample_tick() + 1".to_string()),
                    };
                    row.push_str(&format!("({})", if safe.contains(l) { one } else { zero }));
                    assert!(placed.is_none(), "one place in a line: {line}");
                    placed = Some(l);
                }
                _ => row.push(c),
            }
        }
        out.push_str(&row);
        if let Some(l) = placed {
            out.push_str(&format!(" // {l}"));
        }
        out.push('\n');
    }
    out
}

/// A group: the name, the places in the order they must stop the run, and the text of the module.
struct Group {
    name: &'static str,
    order: &'static str,
    parts: Vec<&'static str>,
    body: &'static str,
}

fn groups() -> Vec<Group> {
    vec![
        // The condition of the event of a reset outside the stopped part is read at its tick: before the argument (U) and the condition that stops the part (V).
        Group {
            name: "stopped_event_condition",
            order: "AUV",
            parts: vec![RSD],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  rsd~(100 / @U)\n    .when~(100 / @V > 1000)\n    .reset_if~(100 / @A > 1)\n}\n",
        },
        // The same condition and a part with an event stage: the condition (A) is before the event stage of the part (G), and the sample stage (V) after both.
        Group {
            name: "stopped_condition_then_stage",
            order: "AGV",
            parts: vec![DACC],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  dacc~(v)\n    .when~(100 / @V > 1000)\n    .reset_if~(100 / @A > 1)\n}\n",
        },
        // A stopped maker of a `sample` expression gives no event: the receiver (C) and the stage of the maker (T) are not reached, the next line of sample (D) is.
        Group {
            name: "stopped_maker_of_sample",
            order: "VD",
            parts: vec![MK, RCV],
            body: "pub flow f() -> U32 at sample {\n  let v = mk~(sample_tick())\n    .when~(100 / @V > 1000)\n  let r = rcv~(v)\n  let t = 100 / @D\n  r + t\n}\n",
        },
    ]
}

/// (module name, text, the line text of the place that must stop the run)
fn cases() -> Vec<(String, String, String)> {
    let mut all = Vec::new();
    for g in groups() {
        for k in 0..g.order.len() {
            let safe = &g.order[..k];
            let text = [PRELUDE, &g.parts.concat(), g.body].concat();
            let text = format!(
                "{}\ntest \"stops\" {{\n  let o = f.render(1, 8.0)\n  assert o.out[0] == 0\n}}\n",
                fill(&text, safe)
            );
            all.push((format!("{}_{k}", g.name), text, format!("// {}", &g.order[k..=k])));
        }
    }
    all
}

/// §11.10 "x の中の `at event` の入力に来たイベントは止まっている間も処理し、入力のイベントごとの出力も出る"; "頭の引数と `block` の段は呼び出し側のもので、止まっている間も評価する"; §11.3 "引数と修飾子の条件を字面の順に評価してから";
/// §11.11 "`when~` で止まっている間は、周期のクロックの式の出力は出さず" (S-562, S-1233, S-1234). One launch reads the 8 modules of the three groups: each stops at the line of the first place that is not made safe.
#[test]
fn the_panic_of_a_part_under_a_when_is_the_first_in_the_order_of_the_ticks_u4() {
    let d = Dir::pkg("event_modifier_panics");
    let all = cases();
    for (name, text, first) in &all {
        assert_eq!(text.lines().filter(|l| l.contains(first)).count(), 1, "`{first}` is on one line: {text}");
        d.write(&format!("{name}.onsa"), text);
    }
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{}", out.stdout);
    let mut wrong = Vec::new();
    for (name, text, first) in &all {
        let at = span_of(&failure_of(record(&doc, name, "stops"))["span"]);
        let want = line_of(text, first);
        if at.file != format!("{name}.onsa") || at.line != want {
            wrong.push(format!("{name}: want the line {want} (`{first}`), stopped at {}:{}", at.file, at.line));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
