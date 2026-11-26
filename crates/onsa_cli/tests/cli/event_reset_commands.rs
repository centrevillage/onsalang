//! Which of several panics `onsa test` reports when a `reset_if~` has an event, and the C that `onsa build` writes for it (W7-11 U2r/t; spec §11.3, §11.10, §11.11, §3.5; S-559, S-562, S-1234, S-1236):
//! the order of the work of a call that has an event in its chain is seen by the values only through a reset, but the report of a panic says which came first. A case is a module with a flow `f` that has a
//! division by 0 in each of two to five places that run at one position (the frame 0), and the line of the one that stops the run (`failure.span`, the line only).
//!
//! The order (§11.3: "引数と修飾子の条件を字面の順に評価してから、初期化と部品の段を外の修飾子から行い"; §11.10: "イベントの条件は、外の `when~` が止めている間もその刻みで初期化する"; §11.11: "出したイベントの刻みは、呼び出し側が作り手に行わせた刻み一つ（`.up~` を付けた作り手では走り一回）の仕事の全体（保存まで）が済んだ直後に、出た順に、
//! 呼び出し側の段の途中で行い"; "同じクロックを二つ以上の入力に渡すと、部品はイベントごとに、その入力を宣言の順に一つずつ刻む"):
//! - A condition of an event is read at the tick of that event, that is where its producer is written, so it comes before the arguments and the stage of the call, which are of the `sample` stage and written below it; the
//!   conditions of two events come in the order of their producers, not in the order they are written in the chain; the conditions of the kind `sample` come in the order written, after the arguments (and before the stage of the part).
//! - A part that adds an event and is reset by an event: the reset comes before the add where the producer of the condition is above that of the input or the condition is the input itself, and the add comes first where the input
//!   is made in the argument (`acc~(fwd~(m)).reset_if~(m ..)`) or above the condition. One event given to two inputs: the input declared first, with all that its tick gives, then the next one.
//!
//! The places are named by a letter in the text of a module: `@A` is the divisor of a division (`100 / @A`). It is `(v - v)` (0: the run stops there) or `(v + 1)` (the case is run with it made safe, so the next place
//! stops). The variable depends on the letter: A and C `v`, B `e1`, D `u`, G `e`, H `b` (the event of a flow, in the line of that flow), and the letters S T U V W are `sample` places (`sample_tick() * 0` or `sample_tick() + 1`). The
//! comment `// X` is put at the end of the line of the place. Each group is run with its places made safe from the first one on, so a line says which came first. One launch of `onsa test` reads all the modules (a module
//! for each case). The texts are written from the spec; none is taken from the output of the compiler.

use std::process::Command;

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

/// A part with a division in its stage (S: the stage of the sample, G: of the event `e`): it adds nothing, it gives the quotient.
const RSD: &str = "\
flow rsd(x: U32 at sample) -> U32 at sample {
  let q = 100 / @T
  x + q
}

";
const DACC: &str = "\
flow dacc(e: U32 at event) -> U32 at sample {
  let q = 100 / @G
  q
}

";
/// A producer that is ticked by an event and has a division in its work.
const FW: &str = "\
flow fw(v: U32 at event) -> U32 at event {
  let z = 100 / @C
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
                        'B' => Some("e1"),
                        'D' => Some("u"),
                        'G' => Some("e"),
                        'H' => Some("b"),
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
        // The condition of an event comes at the tick of the event: after the line above the producer (S), before the argument (U) and the stage of the part (T).
        Group {
            name: "event_condition_first",
            order: "SAUT",
            parts: vec![RSD],
            body: "pub flow f() -> U32 at sample {\n  let w = 100 / @S\n  let v = gen~(sample_tick())\n  let s = rsd~(100 / @U)\n    .reset_if~(100 / @A > 1)\n  w + s\n}\n",
        },
        // The conditions of the kind `sample` come in the order written, after the argument and before the stage.
        Group {
            name: "sample_conditions_in_order",
            order: "UVWT",
            parts: vec![RSD],
            body: "pub flow f() -> U32 at sample {\n  rsd~(100 / @U)\n    .reset_if~(100 / @V > 1)\n    .reset_if~(100 / @W > 1)\n}\n",
        },
        // Two events and a condition of `sample` between them: the producers' order (v, then u: A, then D), then the argument (U), the condition of the sample (V), the stage (T).
        Group {
            name: "two_events_and_a_sample",
            order: "ADUVT",
            parts: vec![RSD],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let u = gen~(sample_tick())\n  rsd~(100 / @U)\n    .reset_if~(100 / @D > 1)\n    .reset_if~(100 / @V > 1)\n    .reset_if~(100 / @A > 1)\n}\n",
        },
        // The condition is the event `e1` that a line above gave (its producer works first, C): the reset comes before the add (G).
        Group {
            name: "reset_then_add",
            order: "CBG",
            parts: vec![FW, DACC],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let e1 = fw~(v)\n  dacc~(v).reset_if~(100 / @B > 1)\n}\n",
        },
        // The input is made in the argument: its producer (C) and the add (G) come before the condition (A).
        Group {
            name: "add_then_reset",
            order: "CGA",
            parts: vec![FW, DACC],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  dacc~(fw~(v)).reset_if~(100 / @A > 1)\n}\n",
        },
        // One event given to two inputs: the input declared first ticks first (the add G, then the condition H); and the declaration is the other way.
        Group {
            name: "two_inputs",
            order: "GH",
            parts: vec![DACC],
            body: "flow hit(e: U32 at event, b: U32 at event) -> U32 at sample {\n  dacc~(e).reset_if~(100 / @H > 1)\n}\n\npub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  hit~(v, v)\n}\n",
        },
        Group {
            name: "two_inputs_reversed",
            order: "HG",
            parts: vec![DACC],
            body: "flow hit(b: U32 at event, e: U32 at event) -> U32 at sample {\n  dacc~(e).reset_if~(100 / @H > 1)\n}\n\npub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  hit~(v, v)\n}\n",
        },
        // What the tick of the first input gives is done before the second input ticks: the add of the event that `fwd` gives (G) before the condition of the second (H).
        Group {
            name: "event_of_the_first_input_is_done_first",
            order: "GH",
            parts: vec![DACC],
            body: "flow pair(e0: U32 at event, b: U32 at event) -> U32 at sample {\n  let t = fwd~(e0)\n  dacc~(t).reset_if~(100 / @H > 1)\n}\n\npub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  pair~(v, v)\n}\n",
        },
        // Two producers: the one written first ticks first, so the add of the input (G) and the condition of the other (D) come in the order the producers are written, in each of the two orders.
        Group {
            name: "producers_input_first",
            order: "GD",
            parts: vec![DACC],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  let u = gen~(sample_tick())\n  dacc~(v).reset_if~(100 / @D > 1)\n}\n",
        },
        Group {
            name: "producers_condition_first",
            order: "DG",
            parts: vec![DACC],
            body: "pub flow f() -> U32 at sample {\n  let u = gen~(sample_tick())\n  let v = gen~(sample_tick())\n  dacc~(v).reset_if~(100 / @D > 1)\n}\n",
        },
        // A receiver written above its producer, which gets its event through `^` after the producer: an event above it (D) comes first, then the add (G).
        Group {
            name: "receiver_above_through_a_caret",
            order: "DG",
            parts: vec![DACC],
            body: "pub flow f() -> U32 at sample {\n  let u = gen~(sample_tick())\n  let h = dacc~(prev~(^v)).reset_if~(100 / @D > 1)\n  let v = gen~(sample_tick())\n  h\n}\n",
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

/// §11.3 "引数と修飾子の条件を字面の順に評価してから"; §11.10 "イベントの条件は、外の `when~` が止めている間もその刻みで初期化する"; §11.11 "出したイベントの刻みは、呼び出し側が作り手に行わせた刻み一つ（`.up~` を付けた作り手では走り一回）の仕事の全体（保存まで）が済んだ直後に、出た順に"; "同じクロックを二つ以上の入力に渡すと…
/// 宣言の順に一つずつ刻む（同じ位置のイベントが宣言の順に来たのと同じで、一度には刻まない。一つの刻みで出たイベントは、次の入力の刻みの前に済ませる）" (S-559, S-562, S-1234, S-1236). One launch reads the modules of the eleven groups: each stops at the line of the first place that is not made safe.
#[test]
fn the_panic_of_a_chain_with_an_event_is_the_first_in_the_order_of_the_ticks_u2r() {
    let d = Dir::pkg("event_reset_panics");
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
flow hit(x: F32 at sample) -> F32 at event {
  if x == 4.0 {
    Some(x)
  } else {
    None
  }
}

flow gen(x: F32 at sample) -> F32 at event {
  Some(x)
}

flow fwd(m: F32 at event) -> F32 at event {
  Some(m)
}

flow rs(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}

flow acc(e: F32 at event) -> F32 at sample {
  let n = prev~(^n) + e
  n
}

@export
pub flow reset_sum(x: F32 at sample) -> F32 at sample {
  let m = hit~(x)
  rs~(x).reset_if~(m > 0.0)
}

@export
pub flow add_then_reset(x: F32 at sample) -> F32 at sample {
  let m = gen~(x)
  acc~(fwd~(m)).reset_if~(m == 6.0)
}

@export
pub flow reset_then_add(x: F32 at sample) -> F32 at sample {
  let m = gen~(x)
  let e1 = fwd~(m)
  acc~(m).reset_if~(e1 == 6.0)
}

@export
pub flow prev_reset(x: F32 at sample) -> F32 at sample {
  let m = gen~(x)
  prev~(m, 9.0).reset_if~(m == 5.0)
}
";

/// §11.10, §11.11, §13.4: a chain of `reset_if~` with an event builds, and the C gives the values worked out by hand, in one call and cut in pieces (a piece of 0 frames too), and after a `reset` that follows frames of other
/// values (x = 101, which has no event of the conditions). x = 1 .. 10. `reset_sum`: the event x = 4 (the frame 3) puts the running sum back before its stage: 1 3 6 4 9 15 22 30 39 49. `add_then_reset` (the event 6 at the frame 5,
/// added and then put back to 0): 1 3 6 10 15 0 7 15 24 34. `reset_then_add` (put back, then 6 added): 1 3 6 10 15 6 13 21 30 40. `prev_reset` (the delay of the event, at its init 9 where x = 5, the frame 4): 9 1 2 3 9 5 6 7 8 9.
#[test]
fn a_chain_with_an_event_gives_the_values_by_hand_in_c_u2r() {
    let dir = build_flows("event_reset_c", C_FLOWS);
    let wants: [(&str, [i64; 10]); 4] = [
        ("reset_sum", [1, 3, 6, 4, 9, 15, 22, 30, 39, 49]),
        ("add_then_reset", [1, 3, 6, 10, 15, 0, 7, 15, 24, 34]),
        ("reset_then_add", [1, 3, 6, 10, 15, 6, 13, 21, 30, 40]),
        ("prev_reset", [9, 1, 2, 3, 9, 5, 6, 7, 8, 9]),
    ];
    for (flow, want) in wants {
        let exe = driver(&dir, flow, true);
        for junk in [0, 3, 7] {
            for cuts in [&[][..], &[1, 1, 5, 7][..]] {
                assert_eq!(
                    frames_of(&exe, junk, 10, cuts),
                    want.to_vec(),
                    "{flow} after {junk} frames of another run, cut at {cuts:?}"
                );
            }
        }
    }
}

const PANIC_FLOWS: &str = "\
flow gen(x: U32 at sample) -> U32 at event {
  Some(x)
}

flow t(x: U32 at sample) -> U32 at sample {
  let e = prev~(^d)
  let q = prev~(100 / x, 9).reset_if~(e >= 5)
  let d = gen~(x)
  q
}

@export
pub flow w(x: U32 at sample) -> U32 at sample {
  t~(x)
}
";

/// A C program that runs `process` on x = 1 6 0 (the stored `100 / 0` of the third frame panics: the instance is poisoned), once more on the poisoned one, calls `reset`, and runs x = 3 4 2 5. It prints the three return codes,
/// the outputs of the first run and the outputs of the last.
const PANIC_DRIVER: &str = r#"#include <stdio.h>
#include <stdint.h>
#include "dm_w.h"
int main(void) {
  static _Alignas(16) unsigned char mem[DM_W_SIZE];
  dm_w* s = (dm_w*)mem;
  if (dm_w_init(s, NULL, 8.0f) != 0) return 2;
  dm_w_params prm;
  dm_w_params_default(&prm);
  uint32_t a[3] = {1, 6, 0}, oa[3] = {7, 7, 7}, b[4] = {3, 4, 2, 5}, ob[4] = {7, 7, 7, 7};
  int r1 = dm_w_process(s, &prm, a, oa, 3);
  int r2 = dm_w_process(s, &prm, a, oa, 3);
  dm_w_reset(s);
  int r3 = dm_w_process(s, &prm, b, ob, 4);
  printf("%d %d %d | %u %u %u | %u %u %u %u\n", r1, r2, r3, oa[0], oa[1], oa[2], ob[0], ob[1], ob[2], ob[3]);
  return 0;
}
"#;

/// §9.2 "export された flow の `process`: その呼び出しを中断し、出力を全てゼロで埋め、インスタンスを poisoned にする。以後の `process` は無音を出力し、`reset` まで復帰しない", §11.6 "`reset` は状態を `init` 値に戻し、
/// poisoned を解く", §14.2 (the return code 1), §11.3 (a delay stores at the end of its stage; it gives 9 first, then what it stored), §11.10 and S-1250 (the reset of a delay by an event that a producer below it ticks waits for the
/// store of the delay). The frame 2 of the first run (x = 0) has `e` = 6 (the x before) >= 5, so a reset of the delay is waiting for its store, and the store of `100 / 0` panics first: the instance is poisoned in the middle of the
/// frame, with that reset not done. The second call on the poisoned instance returns 1, and the outputs of both calls are all 0 (the frames of the call that panicked too). After `reset` the instance is a new one (§11.6): x = 3 4 2 5 gives 9 (the
/// init), 33 (100 / 3), 25 (100 / 4), 50 (100 / 2), and no reset comes in the run (`e`, the x before, is 0 3 4 2, never 5 or more). A reset that was left waiting would put the init back after the first store: 9 9 25 50.
#[test]
fn a_reset_after_a_panic_gives_a_new_instance_with_the_state_of_an_event_delay_in_c_u3() {
    let dir = build_flows("event_reset_panic_c", PANIC_FLOWS);
    let src = dir.file("drv_panic.c", PANIC_DRIVER);
    let exe = dir.path("drv_panic");
    let host = dir.path("target/host");
    let unit = dir.path("target/host/onsa_demo.c");
    let cc = Command::new("clang")
        .args(["-std=c11", "-O1", "-I", &host, &src, &unit, "-o", &exe])
        .output()
        .unwrap_or_else(|e| panic!("the C compiler `clang` is needed: {e}"));
    assert!(
        cc.status.success(),
        "clang: {}{}",
        String::from_utf8_lossy(&cc.stdout),
        String::from_utf8_lossy(&cc.stderr)
    );
    let ran = Command::new(&exe).output().expect("run the driver");
    assert_eq!(ran.status.code(), Some(0), "the driver: {ran:?}");
    assert_eq!(String::from_utf8_lossy(&ran.stdout).trim(), "1 1 0 | 0 0 0 | 9 33 25 50");
}
