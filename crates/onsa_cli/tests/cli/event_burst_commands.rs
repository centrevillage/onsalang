//! Which of several panics `onsa test` reports when a stage gives several events (W7-17 U4/t2 R3; spec §11.11, §11.3, §11.10, §11.9; S-1207, S-1229, S-1234, S-1235): the order of the work of the runs of a part under `.up~(M)` and of the receivers of
//! the events they give is seen by the values only through a reset, but the report of a panic says which came first. A case is a module with a flow `f` that has a division by 0 in each of two or three places that run at the frame 0, and the line
//! of the one that stops the run (`failure.span`, the line only).
//!
//! The order (§11.11: "`.up~`・`.down~` の部品の中から出るイベントの位置は…同じ位置には内側の刻みの順に並ぶ。走りごとに、その走りの直後に受け手の刻みを行う"; "出したイベントの刻みは、作り手の呼び出しのその刻みの仕事（保存まで）が済んだ直後に、呼び出し側の段の途中で行い";
//! §11.9: "同じ位置では、入力のイベントの刻み、遅い刻み、`sample` の刻みの順に並ぶ"; §11.10: "イベントの条件は、そのイベントの刻みで初期化する"):
//! - The receiver of the event of the run 0 of a maker under `.up~(2)` ticks right after that run, before the run 1: a division by 0 in the receiver for the event 0 (R) stops the run before the division in the maker at its run 1 (M). The same where the
//!   receiver is in the body of a flow that is run twice (the receiver of the same body ticks after its maker's run 0), and where the maker is in a block `.up~(2).down~(2)` (its events are at the position of the tick, one after the other).
//! - A block that is stopped by nothing runs its tick at the frame 0 in the stage of `sample / 2`, before the stage of `sample` of the frame 0 where the producer of the event gives its event, so the division in the part at the tick (T) comes before the
//!   condition of the `reset_if~` outside the boundary, which is read at the tick of that event (A).
//!
//! The places are named by a letter in the text of a module: `@X` is the divisor of a division (`100 / @R`). It is a value that is 0 (the run stops there) or one that is not (the case is run with it made safe, so the next place stops), and the
//! comment `// X` is put at the end of the line of the place. Each group is run with its first places made safe, so a line says which came first. One launch of `onsa test` reads all the modules. The texts are written from the spec; none is taken from
//! the output of the compiler.

use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, test_json};

const PRELUDE: &str = "\
flow gen(v: U32 at sample) -> U32 at event {
  Some(v)
}

flow lo2(v: U32 at (sample * 2)) -> U32 at sample {
  v[0]
}

";

/// A maker whose run 1 (sample_tick() 1) divides by 0 where M is unsafe; its event is the number of the run.
const JV: &str = "\
flow jv() -> U32 at event {
  let z = 100 / @M
  Some(sample_tick() + z * 0)
}

";

/// A receiver that divides by the event where R is unsafe (the event of the run 0 is 0).
const RCV: &str = "\
flow rcv(e: U32 at event) -> U32 at sample {
  let q = 100 / @R
  q
}

";

/// A part with a division in its stage (T: the first run of the first tick has `sample_tick()` 0).
const TK: &str = "\
flow tk() -> U32 at sample {
  let q = 100 / @T
  q
}

";

/// Replace each `@X` by the divisor of the place X (0 when X is not in `safe`, a value that is not 0 otherwise) and put `// X` at the end of its line.
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
                    let (zero, one) = match l {
                        'R' => ("e", "(e + 1)"),
                        'M' => ("(1 - sample_tick())", "(sample_tick() + 1)"),
                        'T' => ("(sample_tick() * 0)", "(sample_tick() + 1)"),
                        'A' => ("(v - v)", "(v + 1)"),
                        _ => panic!("no place {l}"),
                    };
                    row.push_str(if safe.contains(l) { one } else { zero });
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
        // The receiver of the event of the run 0 ticks before the run 1 of its maker: R, then M.
        Group {
            name: "receiver_before_the_next_run",
            order: "RM",
            parts: vec![JV, RCV],
            body: "pub flow f() -> U32 at sample {\n  rcv~(jv~().up~(2))\n}\n",
        },
        // The receiver is in the body that is run twice: it ticks right after its own maker's run 0 (R), the run 1 of the body follows (M).
        Group {
            name: "wrapped_receiver_before_the_next_run",
            order: "RM",
            parts: vec![JV, RCV],
            body: "flow hold() -> U32 at sample {\n  let d = jv~()\n  rcv~(d)\n}\n\npub flow f() -> U32 at sample {\n  let u = hold~().up~(2)\n  lo2~(u)\n}\n",
        },
        // The maker is in a block: its events are at the position of the tick, in the order of the runs, and the receiver ticks after each.
        Group {
            name: "block_receiver_before_the_next_run",
            order: "RM",
            parts: vec![JV, RCV],
            body: "pub flow f() -> U32 at sample {\n  rcv~(jv~().up~(2).down~(2))\n}\n",
        },
        // The tick of the block is in the stage of `sample / 2`, so before the producer of the frame gives its event (A, the condition outside the boundary): T, then A.
        Group {
            name: "tick_before_the_reset_outside",
            order: "TA",
            parts: vec![TK],
            body: "pub flow f() -> U32 at sample {\n  let v = gen~(sample_tick())\n  tk~().up~(2).down~(2)\n    .reset_if~(100 / @A > 1)\n}\n",
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
                "{}\ntest \"stops\" {{\n  let o = f.render(2, 8.0)\n  assert o.out[0] == 0\n}}\n",
                fill(&text, safe)
            );
            all.push((format!("{}_{k}", g.name), text, format!("// {}", &g.order[k..=k])));
        }
    }
    all
}

/// §11.11 "走りごとに、その走りの直後に受け手の刻みを行う", "出したイベントの刻みは、作り手の呼び出しのその刻みの仕事が済んだ直後に"; §11.9 "同じ位置では、入力のイベントの刻み、遅い刻み、`sample` の刻みの順に並ぶ"; §11.10 "イベントの条件は、そのイベントの刻みで初期化する"
/// (S-1207, S-1229, S-1234, S-1235). One launch reads the modules of the four groups: each stops at the line of the first place that is not made safe.
#[test]
fn the_panic_of_several_events_is_the_first_in_the_order_of_the_runs_u4() {
    let d = Dir::pkg("event_burst_panics");
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
