//! Where `onsa test` stops, and where it does not, when an argument of a call or an expression that a delay stores reads an event that a call in a later argument or below gives (W7-11 U2/t2; spec §11.3 "保存する値の残りが
//! 読むイベントの値 … その読みを書いた位置 … までの最後の値", "一つの段の中では、本体の `let` を上から、最後に出力の式を行う", "順が見えるのは、二つの式が panic するときの報告（この順で先のもの）", §11.4, §11.11
//! "出した刻みの直後"; S-1240, S-1235, S-1234, S-1206): the values of `tests/spec/flow_semantics/event_saved_values.onsa` are seen here by a division by 0 that the value of an event decides. One launch of `onsa test`
//! reads a package with a module for each case (`<name>.onsa`, a test `run` that renders `f`), so the group costs one run. Every case is worked out by hand from the spec, none from the output of the compiler.
//!
//! `p = prev~(^e, 7)` is the event `e` of a call delayed by one event. An event that is not given yet reads `T.default()` = 0 (§11.11), so the first event turns p from 0 to the 7 of `init`.
//! - `arg_before_producer`: `kk~(p at sample, det~(x))` divides by its first argument. It is read before the producer in the second argument gives the first event (at the sample 0), so it is 0, not the 7 that p has after
//!   the event: the run stops in `kk`. (A run that reads p after the event does not stop at all.)
//! - `later_value_only`: `kk` divides by `(a + 5) % 10`, 0 of the a 5. With `x = 3 5 9` there is an event at each sample, so p before the event of the sample (the one before it, the first 7 of `init`) is 0 7 3, which divides by 5 2 8:
//!   no stop. (p after it is 7 3 5: a run that reads that one stops at the sample 2.)
//! - `body_before_stored`: `let r = 100 / x` is in the body and `prev~(100 / (p at sample))` is stored at the end of the stage (§11.4), so with 0 in both at the sample 0 the body stops first.
//! - `stored_only`: with `x = 1` the body is fine and the stored one is 0: p before the event of the sample is 0 (the 7 after it is not what is read, the place where it is written, §11.3).

use crate::down_two_boundaries_c_commands::{build_flows, driver, frames_of};
use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, str_of, test_json};

const DET: &str = "flow det(x: U32 at sample) -> U32 at event {\n  if x != 0 { Some(x) } else { None }\n}\n\n";

/// A module: `det`, the parts, and the test `run` that renders `f` over `xs`; the only failure it can have is a stop of the run.
fn module(parts: &[&str], xs: &[u32]) -> String {
    let list: Vec<String> = xs.iter().map(u32::to_string).collect();
    format!(
        "{DET}{}\ntest \"run\" {{\n  let xs: [U32; {}] = [{}]\n  let o = f.render(xs, 8.0)\n  assert o.out[0] == o.out[0]\n}}\n",
        parts.concat(),
        xs.len(),
        list.join(", ")
    )
}

/// The flow `kk` that divides by `div` (on its own line, marked `//K`), and `f` that calls it with `p` (the delay of its events, `init` 7) and `det~(x)`.
fn kk_case(div: &str, xs: &[u32]) -> String {
    let kk = format!(
        "flow kk(a: U32 at sample, m: U32 at event) -> U32 at event {{\n  let _ = {div} //K\n  Some(m)\n}}\n\n"
    );
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let p = prev~(^e, 7)\n  let e = kk~(p at sample, det~(x))\n  e at sample\n}\n";
    module(&[&kk, f], xs)
}

/// `f` with a division that is stored (`//S`) and one in the body (`//B`).
fn stored_case(xs: &[u32]) -> String {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {\n  let p = prev~(^d, 7)\n  let q = prev~(100 / (p at sample)) //S\n  let r = 100 / x //B\n  let d = det~(x)\n  q + r\n}\n";
    module(&[f], xs)
}

#[test]
fn a_division_that_an_event_decides_stops_at_the_place_where_the_event_is_read() {
    // (name, source, the mark of the line where the run stops: none when it does not stop)
    let cases: Vec<(&str, String, Option<&str>)> = vec![
        ("arg_before_producer", kk_case("100 / a", &[3, 5]), Some("//K")),
        ("later_value_only", kk_case("100 / ((a + 5) % 10)", &[3, 5, 9]), None),
        ("body_before_stored", stored_case(&[0, 1]), Some("//B")),
        ("stored_only", stored_case(&[1, 1]), Some("//S")),
    ];
    let d = Dir::pkg("event_saved_panics");
    for (name, src, _) in &cases {
        d.write(&format!("{name}.onsa"), src);
    }
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{}", out.stdout);
    let mut wrong = Vec::new();
    for (name, src, stops) in &cases {
        let rec = record(&doc, name, "run");
        match stops {
            None => {
                if str_of(rec, "status") != "ok" {
                    wrong.push(format!("{name}: it must not stop: {rec}"));
                }
            }
            Some(mark) => {
                let at = span_of(&failure_of(rec)["span"]);
                let want = line_of(src, mark);
                if at.file != format!("{name}.onsa") || at.line != want {
                    wrong.push(format!("{name}: want the line {want} (`{mark}`), stopped at {}:{}", at.file, at.line));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The values of `tests/spec/flow_semantics/event_saved_values.onsa` for `saved_name`, in C: `x` is the frame + 1, the event is the `x` that is a multiple of 3 (the frames 2 5 8 11 14), p before the event of the
/// frame is 0 0 0 0 0 0 3 3 3 6 6 6 9 9 9 12, the delay stores it + 1 (1 1 1 1 1 1 4 4 4 7 7 7 10 10 10 13) and gives it one frame later; a run that reads p after the event gives 4 at the frame 6.
#[test]
fn an_event_read_in_a_stored_expression_is_the_value_before_the_event_in_c() {
    let src = "flow gen(x: F32 at sample) -> F32 at event {\n  if x % 3.0 == 0.0 { Some(x) } else { None }\n}\n\n@export\npub flow saved_c(x: F32 at sample) -> F32 at sample {\n  let p = prev~(^d)\n  let q = prev~((p at sample) + 1.0)\n  let d = gen~(x)\n  q\n}\n";
    let dir = build_flows("event_saved_c", src);
    let exe = driver(&dir, "saved_c", true);
    let want = vec![0, 1, 1, 1, 1, 1, 1, 4, 4, 4, 7, 7, 7, 10, 10, 10];
    for junk in [0, 1, 5] {
        for cuts in [&[][..], &[1, 1, 5, 7][..]] {
            assert_eq!(frames_of(&exe, junk, 16, cuts), want, "after {junk} frames of another run, cut at {cuts:?}");
        }
    }
}
