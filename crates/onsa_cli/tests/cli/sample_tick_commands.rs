//! `sample_tick()` in the commands of `onsa` (W7-09 U4b/t, W7-16 U5a/t, U5b2/t, U6a3/t; spec §11.4, §11.3, §11.9, §18.1, `spec/tools.md` §1.1; S-565, S-567 (K6), S-1129 (1), S-1217, Q-09):
//! what the case files in `tests/spec/flow_clock/` and `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow that reads `sample_tick()` with no modifier (in a `let`, the output, a `par`, the first argument of a delay), and a child instance with no modifier that reads it (in the flow of the
//!   package or of a module, in its output or in a stage of `sample / N`, in a grandchild), is lowered by `build`, `dump --core` and `test` (W7-16 U5a, U5b2: the counter of the phase is a field of
//!   the state and the time is the time of the parent); `check` reads it with no diagnostic and `onsa interface` ends with 0.
//! - A chain of `.down~(N)` over a part that does not read `sample_tick()` is lowered even when its argument does (the argument is read in the caller, at the tick of the input; W7-16 U6a1/t).
//! - A chain of `.down~(N)` over a part that reads `sample_tick()` (the part, a child of it, also a conversion flow) is lowered and gives the number of the outermost flow divided by N, cut to `U32` last (§11.4; W7-16 U6a3/t,
//!   S-1217). The values of the chains are in `tests/spec/flow_semantics/down_chain_time_values.onsa`; the cases here are the commands: the package is lowered and its test passes.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::{assert_e0200, assert_lowers, package};
use crate::test_support::{Dir, record, run, str_of, test_json};

/// The bodies of `main.onsa` that read `sample_tick()` in the places of §11.4 (a `let`, the output, a `par`, the first argument of a delay), with no modifier and no child.
const LOWERING: [&str; 4] = [
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  let t = sample_tick()\n  x * F32.round_from(t)\n}\n",
    "pub flow f(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  let ys = par i in 0 ..< 2 { x * F32.round_from(sample_tick() + i) }\n  ys[0] + ys[1]\n}\n",
    "pub flow f(x: F32 at sample) -> U32 at sample {\n  sample_tick() -% prev~(sample_tick())\n}\n",
];

/// A package whose flows read `sample_tick()` where it is a value of the body is read by `check` with no diagnostic, and `build`, `dump --core` and `test` end with 0 and no
/// internal error: the counter of the phase is in the state (§11.9), and the package runs its tests.
#[test]
fn a_package_that_reads_sample_tick_is_lowered_by_build_dump_core_and_test() {
    for (k, flows) in LOWERING.iter().enumerate() {
        assert_lowers(&format!("sample_tick_lowers_{k}"), flows, &[]);
    }
}

/// A child instance that reads `sample_tick()` (S-1129 (1): the time of the child is the time of the parent): in its output, in a stage of `sample / 4`, in its grandchild, and in a flow of a module.
const CHILDREN: [(&str, &[(&str, &str)]); 4] = [
    (
        "flow tk(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  tk~(x)\n}\n",
        &[],
    ),
    (
        "flow tk(x: F32 at sample) -> U32 at sample {\n  let t4 = sample_tick() at (sample / 4)\n  t4 at sample\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  tk~(x) + sample_tick()\n}\n",
        &[],
    ),
    (
        "flow tk(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n\nflow mid(x: F32 at sample) -> U32 at sample {\n  tk~(x) * 2\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  mid~(x)\n}\n",
        &[],
    ),
    (
        "use ticks\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  ticks.elapsed~(x)\n}\n",
        &[("ticks.onsa", "pub flow elapsed(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n")],
    ),
];

#[test]
fn a_child_that_reads_sample_tick_is_lowered_by_build_dump_core_and_test() {
    for (k, (flows, others)) in CHILDREN.iter().enumerate() {
        assert_lowers(&format!("sample_tick_child_{k}"), flows, others);
    }
}

/// A chain of `.down~(N)` over a part that does not read `sample_tick()`, with `sample_tick()` in the argument: the argument is an expression of the caller read at the tick of the input (§11.9), so the time
/// is the time of the caller and nothing of the part (W7-16 U6a1: the time of the part is not read). The package is lowered, and the part reads the argument at the ticks of the chain: the time T of the
/// caller at T = 0, 4, 8, each held for the 4 frames of the chain (§11.4: "書いた場所の `sample_rate()` の刻みの数", the argument is written in the caller).
#[test]
fn a_chain_whose_argument_reads_sample_tick_gives_the_time_of_the_caller_at_the_ticks_of_the_chain() {
    let flows = "flow pass_u32(g: U32 at sample) -> U32 at sample {\n  g\n}\n\npub flow f() -> U32 at sample {\n  pass_u32~(sample_tick()).down~(4) at sample\n}\n\ntest \"argument time\" {\n  var out: [U32; 12] = [9; 12]\n  var st = f.init(8.0)\n  f.process(inout st, inout out)\n  assert out == [0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8]\n}\n";
    assert_lowers_and_passes("sample_tick_arg_chain_values", flows, "argument time");
}

/// A chain over a part that reads `sample_tick()` is lowered (W7-16 U6a3, S-1217; it was E0200 until then) and the part reads the number of the outermost flow divided by N, rounded down (§11.4:
/// "`.down~(N)` の本体では N で割って切り捨て"): the part runs at the frames 0, 4, 8, reads 0, 1, 2 and the output is held for 4 frames.
#[test]
fn a_chain_over_a_part_that_reads_sample_tick_gives_the_time_divided_by_n() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow f() -> U32 at sample {\n  tk~().down~(4) at sample\n}\n\ntest \"time over 4\" {\n  var out: [U32; 12] = [9; 12]\n  var st = f.init(8.0)\n  f.process(inout st, inout out)\n  assert out == [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]\n}\n";
    assert_lowers_and_passes("sample_tick_chain_values", flows, "time over 4");
}

/// A conversion flow that reads `sample_tick()` in its body, under `.down~(2)` (W7-16 U6a2 lowers its body, U6a3 the chain over it): the body has the time of the part, the number of the caller divided by 2, and
/// gathers the 2 frames before the tick (`x[1]` is the latest, the first tick has the default 0). x = 1 2 3 ... 8: the tick at T = 0 gives 0 * 0, T = 2 gives x(1) * 1 = 2, T = 4 gives x(3) * 2 = 8, T = 6 gives x(5) * 3 = 18.
#[test]
fn a_chain_over_a_conversion_flow_that_reads_sample_tick_gives_its_time_and_gathers_before_the_tick() {
    let flows = "flow g(x: F32 at (sample * 2)) -> F32 at sample {\n  x[1] * F32.round_from(sample_tick())\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x).down~(2) at sample\n}\n\ntest \"conversion time\" {\n  let xs: [F32; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n  var out: [F32; 8] = [-1.0; 8]\n  var st = f.init(8.0)\n  f.process(inout st, xs.slice(0, 8), inout out)\n  assert out == [0.0, 0.0, 2.0, 2.0, 8.0, 8.0, 18.0, 18.0]\n}\n";
    assert_lowers_and_passes("sample_tick_conversion_values", flows, "conversion time");
}

/// A child with no modifier that reads `sample_tick()` inside a part under the chain, a chain over a chain, and a time-only flow beside a flow with a stage of its own: the package is lowered and its test passes.
#[test]
fn a_chain_over_a_child_and_a_chain_inside_a_part_are_lowered_and_give_the_times_of_their_parts() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\nflow mid() -> U32 at sample {\n  tk~()\n}\n\nflow mid2() -> U32 at sample {\n  tk~().down~(2) at sample\n}\n\npub flow a() -> U32 at sample {\n  mid~().down~(2) at sample\n}\n\npub flow b() -> U32 at sample {\n  mid2~().down~(2) at sample\n}\n\ntest \"times of the parts\" {\n  var x: [U32; 8] = [9; 8]\n  var y: [U32; 8] = [9; 8]\n  var sa = a.init(8.0)\n  var sb = b.init(8.0)\n  a.process(inout sa, inout x)\n  b.process(inout sb, inout y)\n  assert x == [0, 0, 1, 1, 2, 2, 3, 3]\n  assert y == [0, 0, 0, 0, 1, 1, 1, 1]\n}\n";
    assert_lowers_and_passes("sample_tick_chain_children_values", flows, "times of the parts");
}

/// What stays E0200 over a part that reads `sample_tick()`: a chain with an `.up~(N)` in it (U6b3: the time of a part inside an up is the number times N plus the step). `build`, `dump --core` and `test` stop with E0200
/// and nothing else (no internal error) at the line of the chain (§18.1: the first of the file); `check` reads the package with no diagnostic. The chain that gathers past its first boundary is lowered from U6b1 (the next test).
#[test]
fn a_chain_with_an_up_over_a_part_that_reads_sample_tick_stays_e0200_until_u6b3() {
    let up = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow f() -> U32 at sample {\n  tk~().down~(2).up~(2) at sample\n}\n";
    assert_e0200("sample_tick_e0200_up", up, &[], Some(6));
}

/// A chain that gathers past its first boundary over a head that reads `sample_tick()` is lowered (W7-16 U6b1; it was E0200 until then, S-1214 (1), S-1217): the head runs at the frames c = 0, 4, 8, 12, reads the number of
/// the outermost flow divided by the product of the N, c / 4 (§11.4: "`.down~(N)` の本体では N で割って切り捨て"), and its port at `sample * 4` has the caller's frames c - 6 .. c - 3 (the first boundary takes the 2 frames
/// of the part that the second gave 2 frames each, §11.9). x = 1 2 3 ... (`x = c + 1`, 0 before the first frame): `x[0] + x[3] * time`: c = 0: 0; c = 4: frames -2 .. 1 = 0 0 1 2: 0 + 2 * 1 = 2; c = 8: 3 4 5 6: 3 + 6 * 2 = 15;
/// c = 12: 7 8 9 10: 7 + 10 * 3 = 37; each held 4 frames. A head that reads the time and takes nothing of its port gives c / 4 as it is: 0 1 2.
#[test]
fn a_chain_with_a_second_gathering_boundary_over_a_part_that_reads_sample_tick_gives_the_time_divided_by_the_product() {
    let flows = "flow g4(x: F32 at (sample * 4)) -> F32 at sample {\n  x[0] + x[3] * F32.round_from(sample_tick())\n}\n\nflow t4(x: F32 at (sample * 4)) -> U32 at sample {\n  sample_tick()\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  g4~(x).down~(2).down~(2) at sample\n}\n\npub flow t(x: F32 at sample) -> U32 at sample {\n  t4~(x).down~(2).down~(2) at sample\n}\n\ntest \"time over 4 with two boundaries\" {\n  let xs: [F32; 16] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0]\n  var a: [F32; 16] = [-1.0; 16]\n  var b: [U32; 16] = [9; 16]\n  var sa = f.init(8.0)\n  var sb = t.init(8.0)\n  f.process(inout sa, xs.slice(0, 16), inout a)\n  t.process(inout sb, xs.slice(0, 16), inout b)\n  assert a == [0.0, 0.0, 0.0, 0.0, 2.0, 2.0, 2.0, 2.0, 15.0, 15.0, 15.0, 15.0, 37.0, 37.0, 37.0, 37.0]\n  assert b == [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3]\n}\n";
    assert_lowers_and_passes("sample_tick_gather2_values", flows, "time over 4 with two boundaries");
}

/// The package is lowered by `check`, `build`, `dump --core` and `test` (`assert_lowers`), and the test `name` of `main.onsa` is run and passes (the values of the chain, from §11.4).
pub fn assert_lowers_and_passes(tag: &str, flows: &str, name: &str) {
    assert_lowers(tag, flows, &[]);
    let d = package(&format!("{tag}_values"), flows, &[]);
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{flows}: test: {}{}", out.stdout, out.stderr);
    assert_eq!(str_of(record(&doc, "main", name), "status"), "ok", "{flows}: {doc}");
}

/// `onsa interface` reads the signatures only (§18), so a flow that reads `sample_tick()` in its body is listed with its ports and the
/// command ends with 0 and with no internal error.
#[test]
fn interface_of_a_flow_that_reads_sample_tick_ends_with_0() {
    let d = Dir::pkg("sample_tick_interface");
    let file = d.file(
        "m.onsa",
        "pub flow g(x: F32 at sample, p: F32 at block) -> U32 at sample {\n  let t = sample_tick()\n  t + 1\n}\n",
    );
    let out = run(d.root(), &["interface", &file]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    let lines: Vec<&str> = out.stdout.lines().map(str::trim).collect();
    assert!(lines.iter().any(|l| l.starts_with("x: F32 at sample")), "the input is listed:\n{}", out.stdout);
    assert!(lines.iter().any(|l| l.starts_with(") -> U32 at sample")), "the output is listed:\n{}", out.stdout);
}

/// W7-09 U4b/i2: what `check` reads with no diagnostic, `onsa graph` and `onsa interface` end with 0 and with no internal error (§18.2,
/// `spec/tools.md` §1.1): a `par` that is no root whose body reads `sample_tick()` (its node is labelled with the clock of the place that uses
/// it, §11.4), in a `let` and in the output, of the `sample` of the body and of `sample / 4`.
#[test]
fn graph_and_interface_of_a_par_that_reads_sample_tick_end_with_0() {
    let sources = [
        "pub flow f(x: U32 at sample) -> U32 at sample {\n  let v = (par i in 0 ..< 2 { sample_tick() + i })[0]\n  v\n}\n",
        "pub flow f(x: U32 at sample) -> U32 at sample {\n  (par i in 0 ..< 2 { sample_tick() + i })[0]\n}\n",
        "pub flow f(x: U32 at sample) -> U32 at (sample / 4) {\n  (par i in 0 ..< 2 { sample_tick() * i })[1]\n}\n",
    ];
    for (k, src) in sources.iter().enumerate() {
        let d = Dir::pkg(&format!("sample_tick_par_graph_{k}"));
        let file = d.file("m.onsa", src);
        let out = run(d.root(), &["check", "--json", &file]);
        assert_eq!(out.code, 0, "{src}: check: {}{}", out.stdout, out.stderr);
        for args in [vec!["graph", "f", file.as_str()], vec!["interface", file.as_str()]] {
            let out = run(d.root(), &args);
            assert_eq!(out.code, 0, "{src}: {args:?}: {}{}", out.stdout, out.stderr);
            assert!(!out.stderr.contains("internal error"), "{src}: {args:?}: {}", out.stderr);
        }
    }
}
