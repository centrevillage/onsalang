//! Which of several panics `onsa test` reports when events tick inside the replicas of a `par~`, the arms of an `if~`, and the part of a `par` (W7-17 U6a/t; spec §11.5 "`par~` は複製ごとに本体をこの順でたどる" (§11.3),
//! "出したイベントの刻みは、呼び出し側が作り手に行わせた刻み一つ（`.up~` を付けた作り手では走り一回）の仕事の全体（保存まで）が済んだ直後に、出た順に、呼び出し側の段の途中で行い"; "その刻みでは、呼び出し側の本体の、そのイベントのクロックの仕事を、上から式の順にたどり（§11.3。`par~` の中では、その複製の本体）"; §11.5 "`if~`・`match~` は全ての枝を評価する。…腕の中の状態を持つもの
//! （イベントの段を含む）は、選びによらず動く"; §11.3 "段が刻みの計算した部分式は、より速い式の中でもその刻みで評価し"; S-1096, S-1233, S-1234): the order of the ticks is seen by the values only through a condition, but
//! the report of a panic says which came first. A case is a module with a flow `f` that has a division by 0 in each of two to three places that run at one position (the frame 0), and the line of the one that stops the run.
//!
//! - `replica_order`: the replicas are walked one by one, each with its maker and then the receiver of its event (depth first): the receiver of the replica 0 (C) comes before the maker of the replica 1 (M), and the whole
//!   `par~` before the `sample` expression below it (D).
//! - `untaken_arm`: both arms run in the order they are written, so the receiver of the arm that is not chosen (C, the arm of `sample_tick() > 100`) stops the run before the maker of the arm that is chosen (N).
//! - `par_part`: a computed part of an event in a `par` (E) is evaluated at the tick of the event, right after its maker, before the `sample` expression that is written between them (D).
//!
//! The places are named by a letter in the text of a module: `@C` is the divisor of a division (`100 / @C`, at the end of its line), written `(v - v)` (0: the run stops there) or `(v + 1)` (the case is run with it made safe,
//! so the next place stops), with the letter in a comment on the line, which is what the test looks for. Each group is run with its places made safe from the first one on, so a line says which came first, and once with
//! all of them safe (the run does not stop). One launch of `onsa test` reads all the modules. The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, str_of, test_json};

const GEN: &str = "flow gen(v: U32 at sample) -> U32 at event {\n  Some(v)\n}\n\n";

/// The receiver whose division is at the tick of its event input.
const RCV: &str = "flow rcv(v: U32 at event) -> U32 at sample {\n  let q = 100 / @C\n  q at sample\n}\n\n";

/// The makers: `mk` has the divisor of its `sample` expression with the number of the replica `k` in it (the replica 0 is safe, the replica 1 stops), `mk2` a plain one.
const MK: &str =
    "flow mk(v: U32 at sample, k: U32 at block) -> U32 at event {\n  let z = 100 / @M\n  Some(v + z)\n}\n\n";
const MK2: &str = "flow mk2(v: U32 at sample) -> U32 at event {\n  let z = 100 / @N\n  Some(v + z)\n}\n\n";

/// Replace each `@X` by the divisor of the place X with a comment `// X`: 0 when X is not in `safe`, a positive number otherwise.
fn fill(text: &str, safe: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match chars.peek().copied() {
            Some(l) if c == '@' && l.is_ascii_uppercase() => {
                chars.next();
                let (zero, one) = match l {
                    'D' => ("sample_tick() * 0", "sample_tick() + 1"),
                    'E' => ("m - m + i", "m + i + 1"),
                    'M' => ("1 - k + v * 0", "1 + k + v * 0"),
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
        // The replica 0 (maker safe, receiver C), the replica 1 (maker M, its receiver is C again, made safe with the first), then the `sample` expression D.
        Group {
            name: "replica_order",
            order: "CMD",
            parts: vec![MK, RCV],
            body: "pub flow f() -> U32 at sample {\n  let r = par~ i in 0 ..< 2 { rcv~(mk~(sample_tick(), i)) }\n  let t = 100 / @D\n  r[0] + r[1] + t\n}\n",
        },
        // The arm that is not chosen runs: its receiver (C) before the maker of the arm that is chosen (N).
        Group {
            name: "untaken_arm",
            order: "CN",
            parts: vec![MK, MK2, RCV],
            body: "pub flow f() -> U32 at sample {\n  if~ sample_tick() > 100 {\n    rcv~(mk~(sample_tick(), 0))\n  } else {\n    rcv~(mk2~(sample_tick()))\n  }\n}\n",
        },
        // The part of the `par` is computed at the tick of `m` (E), before the `sample` division written above it (D) that runs after the tick.
        Group {
            name: "par_part",
            order: "ED",
            parts: vec![GEN],
            body: "pub flow f() -> U32 at sample {\n  let m = gen~(sample_tick())\n  let t = 100 / @D\n  let ys = par i in 0 ..< 2 {\n    100 / @E\n  }\n  ys[0] + ys[1] + t\n}\n",
        },
    ]
}

/// (module name, text, the line text of the place that must stop the run, none for the case with every place safe)
fn cases() -> Vec<(String, String, Option<String>)> {
    let mut all = Vec::new();
    for g in groups() {
        for k in 0..=g.order.len() {
            let safe = &g.order[..k];
            let parts = g.parts.concat();
            let text = [parts.as_str(), g.body].concat();
            let text = format!(
                "{}\ntest \"stops\" {{\n  let o = f.render(1, 8.0)\n  assert o.out[0] == o.out[0]\n}}\n",
                fill(&text, safe)
            );
            let first = (k < g.order.len()).then(|| format!("// {}", &g.order[k..=k]));
            all.push((format!("{}_{k}", g.name), text, first));
        }
    }
    all
}

/// §11.3 "`par~` は複製ごとに本体をこの順でたどる"; §11.11 "出したイベントの刻みは、呼び出し側が作り手に行わせた刻み一つ（`.up~` を付けた作り手では走り一回）の仕事の全体（保存まで）が済んだ直後に、出た順に、呼び出し側の段の途中で行い"; "その刻みでは、呼び出し側の本体の、そのイベントのクロックの仕事を、上から式の順にたどり（§11.3。`par~` の中では、その複製の本体）"; §11.5 "全ての枝を評価する";
/// §11.3 "刻みの計算した部分式は…その刻みで評価する". One launch reads the 10 modules of the three groups: each stops at the line of the first place that is not made safe, and the last of each group does not stop.
#[test]
fn the_panic_of_a_replica_an_arm_and_a_part_is_the_first_in_the_order_of_the_ticks_u6a() {
    let d = Dir::pkg("event_replica_panics");
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
        let rec = record(&doc, name, "stops");
        match first {
            None => {
                if str_of(rec, "status") != "ok" {
                    wrong.push(format!("{name}: it must not stop: {rec}"));
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
