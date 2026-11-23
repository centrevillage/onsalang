//! A flow with a stage of `sample / N`, a child that has one, a flow with a slow port and a flow that reads `sample_tick()` in the commands of `onsa` (W7-16 U5a/t, U5b2/t; spec §11.3, §11.4, §11.6, §11.9,
//! §12.4, §18.1, `spec/tools.md` §1.1; S-565, S-578, S-1079, S-1088, S-1129, S-1179, Q-09): what the case files in `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow with no modifier whose body has a stage of `sample / N` (a delay or a `let` of a tick, a part computed at a tick, `sample_tick()`) is lowered:
//!   `build`, `dump --core` and `test` end with 0 and with no internal error, and the tests of the package are run (U5a).
//! - A child instance with no modifier that has a stage of its own or reads `sample_tick()` (S-1088, S-1129 (1)), a grandchild, and a flow with an input or an output at `sample / N` called with no
//!   modifier (§11.9), are lowered the same way (U5b2).
//! - A chain with an `.up~(N)` in it is lowered beside the flows with ticks (U6b3); what stays E0200 is `reset_if~`, a `when~` on a built-in delay and a modifier inside a chain with an `.up~` inside a `.down~` (W7-10 U2 and U3, `check` stops at it) and the border of the outermost flow (W10-01).
//! - Of two ticks at one position that both panic, the slower one is the one that is reported (§11.9: "遅い方から並ぶ", S-1079), whether the two are of one flow or of the parent and a child (S-1088).
//!   The order of a `let` of the parent and of a child at one stage, and of two children, is the one of S-1206 and S-1159 (open: the provisional order of the reference evaluator).
//! - `onsa interface` shows the phase counter of a flow that has a stage of `sample / N`, whose child has one or reads `sample_tick()`, after `_sample_rate` and before the fields of
//!   the `let`s (§12.4, S-1179 (2)), as a field that the compiler puts (its name starts with `_`, §11.6, S-1137); a flow with neither has none; the field of a child has the `State` of the child.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::test_support::{Dir, diagnostics, doc_of, failure_of, record, run, span_of, str_of, test_json};

pub const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

pub fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

/// A package of `main.onsa` (the text of the flows and a test `reads` that holds no flow) and the other files `(name, text)`.
pub fn package(tag: &str, flows: &str, others: &[(&str, &str)]) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", &format!("{flows}\ntest \"reads\" {{\n  assert 1 + 1 == 2\n}}\n"));
    for (name, text) in others {
        d.write(name, text);
    }
    d
}

/// `check` reads the package with no diagnostic, and `build`, `dump --core` and `test` end with 0 and no internal error; the test `reads` is run and passes.
pub fn assert_lowers(tag: &str, flows: &str, others: &[(&str, &str)]) {
    let d = package(tag, flows, others);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 0, "{flows}: check: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{flows}: {}", out.stdout);

    let dir = d.arg();
    let build = run(d.root(), &["build", "--target", "host"]);
    let both = format!("{}{}", build.stdout, build.stderr);
    assert_eq!(build.code, 0, "{flows}: build: {both}");
    assert!(!both.contains("internal error") && !both.contains("E0200"), "{flows}: build: {both}");
    let dump = run(d.root(), &["dump", "--core", dir.as_str()]);
    let both = format!("{}{}", dump.stdout, dump.stderr);
    assert_eq!(dump.code, 0, "{flows}: dump --core: {both}");
    assert!(
        !dump.stdout.trim().is_empty() && !both.contains("internal error") && !both.contains("E0200"),
        "{flows}: dump --core: {both}"
    );

    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{flows}: test: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{flows}: {doc}");
    assert_eq!(str_of(record(&doc, "main", "reads"), "status"), "ok", "{flows}: {doc}");
}

// ----------------------------------------------------------------------------- what U5a lowers

/// Flows with no modifier and no child, each with a stage of `sample / N` or a `sample_tick()`: a delay read at `sample`, a part computed at a tick and read
/// at `sample`, two ticks of different ratios where one reads the other, the arms of an `if~` and the replicas of a `par~`, `sample_tick()` in a stage of `sample / 4`.
const LOWERING: [&str; 5] = [
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let lf = prev~(p at (sample / 4))\n  x * (lf at sample)\n}\n",
    "pub flow f(p: F32 at block, q: F32 at block, x: F32 at sample) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  let c = prev~(q at (sample / 4))\n  let b = (a * 2.0) at sample\n  x * b + (c at sample)\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  let b = (a at (sample / 2)) + 1.0\n  b at sample\n}\n",
    "pub flow f(c: Bool at block, p: F32 at block) -> F32 at sample {\n  let y = if~ c { prev~(p at (sample / 4)) } else { prev~((p * 2.0) at (sample / 4)) }\n  let zs = par~ i in 0 ..< 2 { prev~((p * F32.round_from(i + 1)) at (sample / 8)) }\n  (y at sample) + (zs[1] at sample)\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  let t4 = sample_tick() at (sample / 4)\n  x + F32.round_from(t4 at sample) + F32.round_from(sample_tick())\n}\n",
];

/// The flows above are read by `check`, lowered by the commands, and the package runs its tests (U5a: the Core of the stages of one flow).
#[test]
fn a_flow_with_a_stage_of_sample_over_n_is_lowered_by_build_dump_core_and_test() {
    for (k, flows) in LOWERING.iter().enumerate() {
        assert_lowers(&format!("slow_stage_lowers_{k}"), flows, &[]);
    }
}

// ----------------------------------------------------------------------------- what U5b2 lowers

const SLOW_CHILD: &str = "flow ch(p: F32 at block) -> F32 at sample {\n  prev~(p at (sample / 4)) at sample\n}\n\n";

/// A child that has a stage of its own, or reads `sample_tick()`, run by a parent with no modifier (S-1088: the stages of the child are the stages of the parent at the place of the call; S-1129 (1):
/// `sample_tick()` of the child is the time of the parent): the package is read by `check` with no diagnostic and lowered, a grandchild, the arms of an `if~`, the replicas of a `par~` and a child of a
/// module too (U5b2).
#[test]
fn a_child_with_a_stage_of_its_own_is_lowered_by_build_dump_core_and_test() {
    let bodies: [(String, Vec<(&str, &str)>); 6] = [
        (format!("{SLOW_CHILD}pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {{\n  x * ch~(p)\n}}\n"), vec![]),
        (
            "flow tk(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  tk~(x)\n}\n".to_string(),
            vec![],
        ),
        (
            format!("{SLOW_CHILD}flow mid(p: F32 at block) -> F32 at sample {{\n  ch~(p) * 2.0\n}}\n\npub flow f(p: F32 at block) -> F32 at sample {{\n  mid~(p)\n}}\n"),
            vec![],
        ),
        (
            format!("{SLOW_CHILD}pub flow f(c: Bool at block, p: F32 at block) -> F32 at sample {{\n  let ys = par~ i in 0 ..< 2 {{ ch~(p) * F32.round_from(i + 1) }}\n  let y = if~ c {{ ch~(p) }} else {{ ys[1] }}\n  y + ys[0]\n}}\n"),
            vec![],
        ),
        (
            "use slow\n\npub flow f(p: F32 at block) -> F32 at sample {\n  slow.ch~(p)\n}\n".to_string(),
            vec![("slow.onsa", "pub flow ch(p: F32 at block) -> F32 at sample {\n  prev~(p at (sample / 4)) at sample\n}\n")],
        ),
        (
            "use slow\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  slow.elapsed~(x)\n}\n".to_string(),
            vec![("slow.onsa", "pub flow elapsed(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n")],
        ),
    ];
    for (k, (flows, others)) in bodies.iter().enumerate() {
        assert_lowers(&format!("slow_stage_child_{k}"), flows, others);
    }
}

/// A flow with an input at `sample / N`, an output at `sample / N`, or both, called with no modifier (§11.9: its `sample` is the one of the caller, so the port is at a stage of the caller): a value of
/// `block`, `init` or a constant, a value of the caller's own ticks, in the arms of an `if~` and the replicas of a `par~`, read at `sample` by `at`. The package is lowered (U5b2). The flows are the
/// callees of the case `slow_port_values.onsa`.
#[test]
fn a_flow_with_a_slow_port_called_with_no_modifier_is_lowered_by_build_dump_core_and_test() {
    let callees = "flow keep4(x: F32 at (sample / 4)) -> F32 at sample {\n  x at sample\n}\n\nflow lag4(x: F32 at (sample / 4)) -> F32 at (sample / 4) {\n  prev~(x, 100.0)\n}\n\nflow ticks4() -> U32 at (sample / 4) {\n  sample_tick()\n}\n\n";
    let bodies = [
        "pub flow f(p: F32 at block) -> F32 at sample {\n  keep4~(p)\n}\n",
        "pub flow f(p: F32 at block) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  lag4~(a) at sample\n}\n",
        "pub flow f(i: F32 at init) -> F32 at sample {\n  (lag4~(lag4~(i)) at sample) + keep4~(1.0)\n}\n",
        "pub flow f() -> U32 at sample {\n  let t = ticks4~()\n  ((t at (sample / 2)) + 1) at sample\n}\n",
        "pub flow f(c: Bool at block, p: F32 at block) -> F32 at sample {\n  let ys = par~ i in 0 ..< 2 { lag4~(p * F32.round_from(i + 1)) at sample }\n  if~ c { keep4~(p) } else { ys[1] }\n}\n",
    ];
    for (k, body) in bodies.iter().enumerate() {
        assert_lowers(&format!("slow_stage_ports_{k}"), &format!("{callees}{body}"), &[]);
    }
}

// ----------------------------------------------------------------------------- what stays E0200 after U5b2

/// A chain with an `.up~(N)` beside a child with ticks and a flow that has none of the chain (W7-16 U6b3; it was E0200 in the flow with the chain until then): the package is read by `check` with no diagnostic and lowered,
/// the flows `ok` and `chained` (the child `ch` called with no chain, and a chain of `.down~(4).up~(2)` over a part with a memory) beside each other, and its test runs.
#[test]
fn a_chain_with_an_up_beside_the_flows_with_ticks_is_lowered() {
    let chain = format!(
        "{SLOW_CHILD}flow lp(x: F32 at sample) -> F32 at sample {{\n  x * 0.5 + prev~(x) * 0.5\n}}\n\npub flow ok(p: F32 at block, x: F32 at sample) -> F32 at sample {{\n  x * ch~(p)\n}}\n\npub flow chained(p: F32 at block, x: F32 at sample) -> F32 at sample {{\n  x * ch~(p) + (lp~(p).down~(4).up~(2) at sample)\n}}\n"
    );
    assert_lowers("slow_stage_left_chain", &chain, &[]);
}

/// A call of a conversion flow with a port at `sample * N` with no chain takes or gives a bundle at the caller (§11.9; W7-16 U6b2, it was E0200 until then): the package with `ok` and the child `ch`, the flows `dup2`
/// and `fold2` and the flow `burst` that passes the output of the first to the second is read by `check` with no diagnostic and lowered, and its test runs. The values are in `bursts_values.onsa`.
#[test]
fn a_burst_at_the_caller_is_lowered_with_the_conversion_flows_and_the_flows_beside_it() {
    let burst = format!(
        "{SLOW_CHILD}flow dup2(x: F32 at sample) -> F32 at (sample * 2) {{\n  [x, x]\n}}\n\nflow fold2(x: F32 at (sample * 2)) -> F32 at sample {{\n  (x[0] + x[1]) * 0.5\n}}\n\npub flow ok(p: F32 at block, x: F32 at sample) -> F32 at sample {{\n  x * ch~(p)\n}}\n\npub flow burst(x: F32 at sample) -> F32 at sample {{\n  fold2~(dup2~(x))\n}}\n"
    );
    assert_lowers("slow_stage_burst", &burst, &[]);
}

// ----------------------------------------------------------------------------- the slower tick first

/// Two ticks at the frame 4 both read a 0 and divide by it. The stage of `sample / 2` is written first and the one of `sample / 4` second, so that the order of the
/// text and the order of the stages differ: the slower tick (`sample / 4`, the expression `100 / a`, line 5) is the one that stops the run (§11.9: "比の違う遅い刻みどうしは
/// 遅い方（N の大きい方）から並び"; S-1079), not the first written (`200 / b`, line 3).
#[test]
fn of_two_ticks_that_panic_at_one_position_the_slower_is_reported() {
    let src = "pub flow both(p: I32 at block) -> I32 at sample {
  let b = delay~(p at (sample / 2), 2, 1)
  let qb = 200 / b
  let a = prev~(p at (sample / 4), 1)
  let qa = 100 / a
  (qa at sample) + (qb at sample)
}

test \"stops\" {
  let o = both.render(both.Params { p: 0 }, 5, 8.0)
  assert o.out[0] == 300
}
";
    let d = Dir::pkg("slow_stage_slower_first");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "stops"));
    let at = span_of(&f["span"]);
    assert_eq!((at.file.as_str(), at.line), ("m.onsa", 5), "the division of the tick of sample / 4: {f}");
}

// ----------------------------------------------------------------------------- the order of the panics of a parent and its children

/// The line (from 1) of the first line of `src` that has `needle`.
pub fn line_of(src: &str, needle: &str) -> u64 {
    1 + src.lines().position(|l| l.contains(needle)).unwrap_or_else(|| panic!("no `{needle}` in:\n{src}")) as u64
}

/// The source `flows` and the test `stops` that renders the flow `flow` (a `block` input `p` of 0) over 5 frames: it stops at the frame 4, the tick of `sample / 4` that reads the 0 stored at the tick 0.
fn stops_src(flows: &str, flow: &str) -> String {
    format!(
        "{flows}\ntest \"stops\" {{\n  let o = {flow}.render({flow}.Params {{ p: 0 }}, 5, 8.0)\n  assert o.out[0] == 0\n}}\n"
    )
}

/// The line of `m.onsa` of the expression where the test `stops` of `src` stops (the `failure` of `onsa test`).
pub fn stop_line(tag: &str, src: &str) -> u64 {
    let d = Dir::pkg(tag);
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{src}: {}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "stops"));
    let at = span_of(&f["span"]);
    assert_eq!(at.file, "m.onsa", "{src}: {f}");
    at.line
}

const KID: &str = "flow kid(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at (sample / 4), 1)\n  let q = 100 / d\n  q at sample\n}\n\n";

/// A child that stops alone stops at its own division; the rest of the cases of the group have the parent's own division and that of the child at the same frame. A stage of the child is a
/// stage of the parent (S-1088), so what decides which of the two is reported is the order of §11.9: the slower tick first (S-1079, "比の違う遅い刻みどうしは遅い方から"), and for the same ratio the order
/// of S-1206 and S-1159 (open; the provisional order of the reference evaluator: the `let`s of the stage of the parent in the order of the text, then the stages of the children in the order of the
/// calls; the cases say so).
#[test]
fn the_panic_of_a_stage_of_a_child_is_reported_at_the_division_of_the_child_when_it_is_alone() {
    let src = stops_src(&format!("{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  kid~(p)\n}}\n"), "f");
    assert_eq!(stop_line("slow_child_panic_alone", &src), line_of(&src, "100 / d"), "{src}");
}

/// S-1206 and S-1159 (provisional): at one stage a `let` of the parent is evaluated before the stage of a child of the same ratio, whichever is written first in the text. Both divide by the 0 at the frame 4;
/// the one that stops the run is the division of the parent (`200 / e`).
#[test]
fn at_one_stage_the_let_of_the_parent_is_before_the_stage_of_a_child_s1206_s1159_provisional() {
    let let_first = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let e = prev~(p at (sample / 4), 1)\n  let r = 200 / e\n  (r at sample) + kid~(p)\n}}\n"
    );
    let child_first = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let k = kid~(p)\n  let e = prev~(p at (sample / 4), 1)\n  let r = 200 / e\n  (r at sample) + k\n}}\n"
    );
    for (tag, flows) in [("slow_child_panic_let_first", &let_first), ("slow_child_panic_child_first", &child_first)] {
        let src = stops_src(flows, "f");
        assert_eq!(stop_line(tag, &src), line_of(&src, "200 / e"), "the let of the parent: {src}");
    }
}

/// S-1206 (provisional): the stages of two children at one stage are in the order of their calls in the parent, not in the order of their declarations (the first declared is called second).
#[test]
fn two_children_that_panic_at_one_stage_are_reported_in_the_order_of_the_calls_s1206_provisional() {
    let flows = "flow kid_a(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at (sample / 4), 1)\n  let q = 100 / d\n  q at sample\n}\n\nflow kid_b(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at (sample / 4), 1)\n  let q = 300 / d\n  q at sample\n}\n\npub flow f(p: I32 at block) -> I32 at sample {\n  let b = kid_b~(p)\n  let a = kid_a~(p)\n  a + b\n}\n";
    let src = stops_src(flows, "f");
    assert_eq!(
        stop_line("slow_child_panic_two_children", &src),
        line_of(&src, "300 / d"),
        "the child called first: {src}"
    );
}

/// §11.9 (S-1079, S-1088): the slower of two ticks at one position is first, also between a stage of the parent and a stage of a child. The child's stage of `sample / 4` is before the parent's own
/// `sample / 2` (the child's division, `100 / d`, is reported), and the parent's own `sample / 4` is before the stage of `sample / 2` of a child (the parent's `200 / e`).
#[test]
fn of_a_stage_of_the_parent_and_a_stage_of_a_child_at_one_position_the_slower_is_reported() {
    let child_slower = format!(
        "{KID}pub flow f(p: I32 at block) -> I32 at sample {{\n  let b = delay~(p at (sample / 2), 2, 1)\n  let qb = 200 / b\n  (qb at sample) + kid~(p)\n}}\n"
    );
    let src = stops_src(&child_slower, "f");
    assert_eq!(
        stop_line("slow_child_panic_child_slower", &src),
        line_of(&src, "100 / d"),
        "the child's tick of sample / 4: {src}"
    );

    let parent_slower = "flow kid_h(p: I32 at block) -> I32 at sample {\n  let d = delay~(p at (sample / 2), 2, 1)\n  let q = 400 / d\n  q at sample\n}\n\npub flow f(p: I32 at block) -> I32 at sample {\n  let e = prev~(p at (sample / 4), 1)\n  let r = 200 / e\n  (r at sample) + kid_h~(p)\n}\n";
    let src = stops_src(parent_slower, "f");
    assert_eq!(
        stop_line("slow_child_panic_parent_slower", &src),
        line_of(&src, "200 / e"),
        "the parent's tick of sample / 4: {src}"
    );
}

// ----------------------------------------------------------------------------- the interface

/// The lines of the fields of `<flow>.State` in the text of `onsa interface`: (name, offset, the line).
pub fn state_fields(text: &str, flow: &str) -> Vec<(String, u64, String)> {
    let head = format!("pub struct {flow}.State");
    let mut lines = text.lines().skip_while(|l| !l.trim_start().starts_with(&head));
    assert!(lines.next().is_some(), "no `{head}` in:\n{text}");
    lines
        .take_while(|l| l.contains(" bytes, align "))
        .map(|l| {
            let name = l.trim().split(':').next().unwrap_or("").to_string();
            let offset = l
                .rsplit("offset ")
                .next()
                .and_then(|n| n.trim().parse::<u64>().ok())
                .unwrap_or_else(|| panic!("an offset in `{l}`"));
            (name, offset, l.to_string())
        })
        .collect()
}

/// §12.4 (S-1179 (2)): after `_sample_rate` (when it is there) come the phase counter, then the fields of the `let`s, and `_poisoned` and `_initialized` are last. The counter
/// is a `U32` (4 bytes, align 4) that the compiler puts (§11.6: "処理系が置くものだと印を付ける": a name that starts with `_`, §2.3, S-1137); it is next to `_sample_rate` with no padding.
/// A flow with no stage of `sample / N` and no `sample_tick()` has no counter (the state of the flows in the cases `state_names_*` stays).
#[test]
fn the_interface_puts_the_phase_counter_after_sample_rate_and_before_the_lets() {
    let src = "pub flow slow(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let a = prev~(p at (sample / 4))
  x * (a at sample) * sample_rate()
}

pub flow counted(x: F32 at sample) -> U32 at sample {
  sample_tick()
}

pub flow plain(x: F32 at sample) -> F32 at sample {
  x * 0.5
}
";
    let d = Dir::pkg("slow_stage_interface");
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);

    let slow = state_fields(&out.stdout, "slow");
    let names: Vec<&str> = slow.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(&names[..2], ["_sample_rate", "_tick"], "{names:?}");
    assert_eq!((slow[0].1, slow[1].1), (0, 4), "the counter is next to `_sample_rate`: {slow:?}");
    assert!(slow[1].2.contains("4 bytes, align 4"), "{}", slow[1].2);
    assert_eq!(&names[names.len() - 2..], ["_poisoned", "_initialized"], "{names:?}");
    assert!(names[2..names.len() - 2].iter().all(|n| !n.starts_with("_tick")), "one counter: {names:?}");

    let counted = state_fields(&out.stdout, "counted");
    let names: Vec<&str> = counted.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(names, ["_tick", "_poisoned", "_initialized"], "a flow that reads only `sample_tick()`: {names:?}");
    assert_eq!(counted.iter().map(|f| f.1).collect::<Vec<_>>(), [0, 4, 5], "{counted:?}");
    assert!(out.stdout.contains("pub struct counted.State  // Affine; size 8, bulk 0, align 4"), "{}", out.stdout);

    let plain = state_fields(&out.stdout, "plain");
    let names: Vec<&str> = plain.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(names, ["_poisoned", "_initialized"], "a flow with no time has no counter: {names:?}");
}

// ----------------------------------------------------------------------------- the interface of a parent

/// The size in bytes of a field line (`name: N bytes, align A, …`).
pub fn bytes_of(line: &str) -> u64 {
    let n = line.split(": ").nth(1).and_then(|r| r.split(" bytes").next()).and_then(|n| n.trim().parse().ok());
    n.unwrap_or_else(|| panic!("a size in `{line}`"))
}

/// The size of `<flow>.State` in the header line of the struct.
pub fn state_size(text: &str, flow: &str) -> u64 {
    let head = format!("pub struct {flow}.State  // Affine; size ");
    let line =
        text.lines().map(str::trim).find(|l| l.starts_with(&head)).unwrap_or_else(|| panic!("no `{head}` in:\n{text}"));
    line[head.len()..].split(',').next().and_then(|n| n.parse().ok()).unwrap_or_else(|| panic!("a size in `{line}`"))
}

/// §12.4 (S-1179 (2)) and §11.9 ("誰が欄を持つかは実装の選択", S-1129 (1)): a flow whose child has a stage of `sample / N`, or whose child reads `sample_tick()`, has the phase counter (it makes the time
/// that the stages of the child are run at) at the place of §12.4, after `_sample_rate` when it has that and before the fields of the `let`s; the field of the child is the state of the child, which has
/// the size of the state of the flow alone (§12.4: "単独でも埋め込んでも同じ配置"), and the child, alone, has its counter first. A parent whose children have no stage and read no time has none, as before. The
/// flow with a slow port has a state of a known size. The names of the fields are those of §11.6 (the `let` of the instance is the name of the node).
#[test]
fn the_interface_of_a_parent_of_a_child_that_has_a_stage_has_the_counter_and_the_field_of_the_child() {
    let src = "pub flow ch(p: F32 at block) -> F32 at sample {
  prev~(p at (sample / 4)) at sample
}

pub flow tk() -> U32 at sample {
  sample_tick()
}

pub flow avg(x: F32 at sample) -> F32 at sample {
  0.5 * (x + prev~(x))
}

pub flow lag4(x: F32 at (sample / 4)) -> F32 at (sample / 4) {
  prev~(x, 100.0)
}

pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let c = ch~(p)
  x * c * sample_rate()
}

pub flow g(x: F32 at sample) -> U32 at sample {
  let k = tk~()
  k
}

pub flow h(x: F32 at sample) -> F32 at sample {
  let a = avg~(x)
  a
}

pub flow top(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let m = f~(p, x)
  m
}
";
    let d = Dir::pkg("slow_stage_interface_parent");
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the sizes of the states are known: {}", out.stdout);
    let fields = |flow: &str| -> Vec<(String, u64, String)> { state_fields(&out.stdout, flow) };
    let names = |fs: &[(String, u64, String)]| -> Vec<String> { fs.iter().map(|f| f.0.clone()).collect() };
    let child_field = |fs: &[(String, u64, String)], name: &str, child: &str| {
        let f = fs.iter().find(|f| f.0 == name).unwrap_or_else(|| panic!("a field `{name}` in {fs:?}"));
        assert_eq!(
            bytes_of(&f.2),
            state_size(&out.stdout, child),
            "the field `{name}` is the state of `{child}`: {}",
            f.2
        );
    };

    let f = fields("f");
    assert_eq!(names(&f)[..2], ["_sample_rate", "_tick"], "{f:?}");
    assert_eq!((f[0].1, f[1].1), (0, 4), "the counter is next to `_sample_rate`: {f:?}");
    assert!(f[1].2.contains("4 bytes, align 4"), "{}", f[1].2);
    assert_eq!(names(&f).iter().filter(|n| n.starts_with("_tick")).count(), 1, "one counter: {f:?}");
    child_field(&f, "c", "ch");

    let ch = fields("ch");
    assert_eq!((ch[0].0.as_str(), ch[0].1), ("_tick", 0), "the child alone has its counter first: {ch:?}");

    let g = fields("g");
    assert_eq!((g[0].0.as_str(), g[0].1), ("_tick", 0), "a parent whose child reads the time has the counter: {g:?}");
    child_field(&g, "k", "tk");

    let top = fields("top");
    assert_eq!(
        (top[0].0.as_str(), top[0].1),
        ("_tick", 0),
        "a grandchild's stage and the time run in the parent of its parent: {top:?}"
    );
    child_field(&top, "m", "f");

    let h = fields("h");
    assert!(
        names(&h).iter().all(|n| !n.starts_with("_tick")),
        "a parent of a child with no stage and no time has no counter: {h:?}"
    );
    child_field(&h, "a", "avg");

    let lag4 = fields("lag4");
    let n = names(&lag4);
    assert!(
        n.iter().any(|n| n == "_tick") && n[n.len() - 2..] == ["_poisoned", "_initialized"],
        "a flow with a slow port has a state: {lag4:?}"
    );
}
