//! Which of several panics `onsa test` reports when events tick inside one position, and events in the C that `onsa build` writes (W7-11 U2/t; spec §11.11, §11.3, §3.5, §11.6; S-561, S-564, S-1233, S-1234,
//! S-1235, S-1236): the order of the ticks of events is seen by the values only through a condition of a modifier, but the report of a panic says which came first. A case is a module with a flow `f` that has a
//! division by 0 in each of two to four places that run at one position (the frame 0), and the line of the one that stops the run (`failure.span`, the line only).
//!
//! The order (§11.11): a call does its work of the stage where it is written (its arguments first); the event it gives ticks right after that work, and the work of the stage of the caller goes on after the ticks: the
//! receiver of the event gets its tick (its own work, and the events it gives, depth first) before the lower expressions of the clock the call was ticked by (S-1234). A receiver written above the producer and fed through
//! `prev~(^d)` ticks at the same time, after the producer (S-1235). One event given to two inputs ticks the first input and what it gives, then the second input (S-1236, the declaration order, not the text order).
//!
//! The places are named by a letter in the text of a module: `@A` is the divisor of a division (`100 / @A`, written at the end of its line). It is `(v - v)` (0: the run stops there) or `(v + 1)` (the case is run with it
//! made safe, so the next place stops), with the letter in a comment on the line, which is what the test looks for. `@D` is a division in the `sample` stage (the divisor is `sample_tick() * 0` or `sample_tick() + 1`), and
//! `@U` is a division by `u` (a second input). Each group is run with its places made safe from the first one on, so a line says which came first. One launch of `onsa test` reads all the modules (a module for each
//! case). The texts are written from the spec; none is taken from the output of the compiler.

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};
use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, test_json};

const PRELUDE: &str = "\
flow gen(v: U32 at sample) -> U32 at event {
  Some(v)
}

flow fwd(v: U32 at event) -> U32 at event {
  Some(v)
}

";

/// The receiver whose division is at the tick of its event input.
const RCV: &str = "\
flow rcv(v: U32 at event) -> U32 at sample {
  let q = 100 / @C
  q at sample
}

";

/// The producer whose division is in its `sample` stage, and the producer that is ticked by an event.
const MK: &str = "\
flow mk(v: U32 at sample) -> U32 at event {
  let z = 100 / @A
  Some(v + z)
}

";
const FW: &str = "\
flow fw(v: U32 at event) -> U32 at event {
  let z = 100 / @A
  Some(v + z)
}

";

/// Replace each `@X` by the divisor of the place X with a comment `// X`: 0 when X is not in `safe`, 1 + the value otherwise.
fn fill(text: &str, safe: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match chars.peek().copied() {
            Some(l) if c == '@' && l.is_ascii_uppercase() => {
                chars.next();
                let (zero, one) = match l {
                    'D' => ("sample_tick() * 0", "sample_tick() + 1"),
                    'U' => ("u - u", "u + 1"),
                    _ => ("v - v", "v + 1"),
                };
                out.push_str(&format!("({}) // {l}", if safe.contains(l) { one } else { zero }));
            }
            _ => out.push(c),
        }
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
        // The producer is ticked by an event: its work (A), the receiver of what it gives (C), the lower expression of the clock that ticked it (B).
        Group {
            name: "event_maker",
            order: "ACB",
            parts: vec![FW, RCV],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let e = fw~(v)\n  let r = rcv~(e)\n  let w = 100 / @B\n  r + (w at sample)\n}\n",
        },
        // The producer is a `sample` expression: its work (A), the receiver (C), the lower expression of the event (B), then the rest of the `sample` stage (D).
        Group {
            name: "sample_maker",
            order: "ACBD",
            parts: vec![MK, RCV],
            body: "pub flow f() -> U32 at sample {\n  let v = mk~(sample_tick())\n  let r = rcv~(v)\n  let w = 100 / @B\n  let t = 100 / @D\n  r + (w at sample) + t\n}\n",
        },
        // One event given to two inputs: the first input ticks and the receiver of what it gives (C) comes before the second input (U), though U is written above.
        Group {
            name: "two_inputs",
            order: "CU",
            parts: vec![RCV],
            body: "flow both(v: U32 at event, u: U32 at event) -> U32 at sample {\n  let w = 100 / @U\n  let e = fwd~(v)\n  let r = rcv~(e)\n  r + (w at sample)\n}\n\npub flow f() -> U32 at sample {\n  let d = gen~(sample_tick())\n  both~(d, d)\n}\n",
        },
        // A receiver in the argument of the producer, fed by the producer through a delay: the argument is evaluated first, then the work of the producer (A), the tick of the receiver (C), the rest of the stage (D).
        Group {
            name: "receiver_in_argument",
            order: "ACD",
            parts: vec![MK, RCV],
            body: "pub flow f() -> U32 at sample {\n  let v = mk~(rcv~(prev~(^v)) + sample_tick())\n  let t = 100 / @D\n  (v at sample) + t\n}\n",
        },
        // A receiver written above the producer and fed through `^`: the producer (A, written below) comes first, then the receiver (C).
        Group {
            name: "receiver_above",
            order: "AC",
            parts: vec![MK, RCV],
            body: "pub flow f() -> U32 at sample {\n  let h = rcv~(prev~(^v))\n  let v = mk~(sample_tick())\n  h\n}\n",
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

/// §11.11 "出したイベントの刻みは、作り手の呼び出しのその刻みの仕事（保存まで）が済んだ直後に、呼び出し側の段の途中で行い、呼び出し側の段の残りはその後に続く"; "同じクロックを二つ以上の入力に渡すと、部品はイベントごとに、その入力を
/// 宣言の順に一つずつ刻む（一つの刻みで出たイベントは、次の入力の刻みの前に済ませる）"; "`^名前` を通して作り手より上に書いた受け手もその時に刻む" (S-1234, S-1235, S-1236). One launch reads the 14 modules of the five groups: each stops at the
/// line of the first place that is not made safe.
#[test]
#[ignore = "W7-11 U2: S-1234, S-1235, S-1236"]
fn the_panic_of_a_position_that_ticks_events_is_the_first_in_the_order_of_the_ticks_u2() {
    let d = Dir::pkg("event_stage_panics");
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

const C_FLOWS: &str = "\
flow gate(x: F32 at sample) -> F32 at event {
  if x > 2.5 {
    Some(x)
  } else {
    None
  }
}

flow every_quarter(p: F32 at block) -> F32 at event {
  Some(p) at (sample / 4)
}

flow sum(e: F32 at event) -> F32 at sample {
  let n = prev~(^n) + e
  n
}

@export
pub flow held(x: F32 at sample) -> F32 at sample {
  gate~(x) at sample
}

@export
pub flow quarters(
  @param(min: 0.0, max: 100.0, default: 10.0)
  p: F32 at block,
) -> F32 at sample {
  sum~(every_quarter~(p))
}
";

/// §11.11, §11.6, §13.4: a flow with events inside (a producer that gives events from a `sample` expression, from `sample / 4`, and a receiver that sums them) builds, and the C gives the values worked out by hand, in one call
/// and cut in pieces (a piece of 0 frames too), and after a `reset` that follows frames of other values. `held` (x = 1 2 3 ...): the events are the values over 2.5, the last one is held, 0 before the first and after the `reset`
/// (also after a run with the events of x = 101): 0 0 3 4 5 6 7 8 9 10. `quarters` (p = 10): an event at the frames 0 4 8 with p, summed: 10 10 10 10 20 20 20 20 30 30 (the counter of the ticks restarts with `reset`).
#[test]
#[ignore = "W7-11 U2: S-564"]
fn a_flow_with_events_inside_gives_the_values_by_hand_in_c_u2() {
    let dir = build_flows("event_stage_c", C_FLOWS);
    let held = driver(&dir, "held", true);
    let quarters = driver(&dir, "quarters", false);
    for junk in [0, 3, 7] {
        for cuts in [&[][..], &[1, 1, 5, 7][..]] {
            assert_eq!(
                frames_of(&held, junk, 10, cuts),
                vec![0, 0, 3, 4, 5, 6, 7, 8, 9, 10],
                "held after {junk} frames of another run, cut at {cuts:?}"
            );
            assert_eq!(
                frames_of(&quarters, junk, 10, cuts),
                vec![10, 10, 10, 10, 20, 20, 20, 20, 30, 30],
                "quarters after {junk} frames of another run, cut at {cuts:?}"
            );
        }
    }
}
