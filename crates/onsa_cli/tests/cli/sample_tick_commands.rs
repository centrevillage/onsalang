//! `sample_tick()` in the commands of `onsa` (W7-09 U4b/t, W7-16 U5a/t, U5b2/t; spec §11.4, §11.3, §11.9, §18.1, `spec/tools.md` §1.1; S-565, S-567 (K6), S-1129 (1), Q-09):
//! what the case files in `tests/spec/flow_clock/` and `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow that reads `sample_tick()` with no modifier (in a `let`, the output, a `par`, the first argument of a delay), and a child instance with no modifier that reads it (in the flow of the
//!   package or of a module, in its output or in a stage of `sample / N`, in a grandchild), is lowered by `build`, `dump --core` and `test` (W7-16 U5a, U5b2: the counter of the phase is a field of
//!   the state and the time is the time of the parent); `check` reads it with no diagnostic and `onsa interface` ends with 0.
//! - A chain of `.down~(N)` over a part that does not read `sample_tick()` is lowered even when its argument does (the argument is read in the caller, at the tick of the input; W7-16 U6a1/t).
//! - What stays E0200 after U6a2 is the work of the later unit: a chain over a part that reads `sample_tick()` (the part, or a child of it, also a conversion flow; U6a3, S-1217). `build`, `dump --core` and `test` stop
//!   at it with E0200 and with nothing else (no internal error); the first diagnostic is at the first place of the file that has such a form, the chain (§18.1: the order of the diagnostics).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::{assert_e0200, assert_lowers};
use crate::test_support::{Dir, run};

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
/// is the time of the caller and nothing of the part (W7-16 U6a1: the time of the part is not read). The package is lowered. The value of the time under a chain is not pinned (S-1217).
#[test]
fn a_chain_whose_argument_reads_sample_tick_is_lowered_when_the_part_reads_no_time() {
    let flows = "flow pass_u32(g: U32 at sample) -> U32 at sample {\n  g\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  pass_u32~(sample_tick()).down~(4) at sample\n}\n";
    assert_lowers("sample_tick_arg_chain_lowers", flows, &[]);
}

/// A chain over a part that reads `sample_tick()` stays E0200 after U6a1 (line 6, the line of the chain; the part is lowered): the time of the part under `.down~(N)` is U6a3 (S-1217).
#[test]
fn a_chain_over_a_part_that_reads_sample_tick_is_e0200_until_u6a3() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow f() -> U32 at sample {\n  tk~().down~(4) at sample\n}\n";
    assert_e0200("sample_tick_e0200_0", flows, &[], Some(6));
}

/// A conversion flow that reads `sample_tick()` in its body is lowered (W7-16 U6a2: the flow `g`, line 1, has no E0200), and the chain over it stays E0200 for the time of the part (U6a3, S-1217): the first
/// diagnostic is at the chain, line 6.
#[test]
fn a_chain_over_a_conversion_flow_that_reads_sample_tick_is_e0200_at_the_chain_until_u6a3() {
    let flows = "flow g(x: F32 at (sample * 2)) -> F32 at sample {\n  x[1] * F32.round_from(sample_tick())\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x).down~(2) at sample\n}\n";
    assert_e0200("sample_tick_e0200_1", flows, &[], Some(6));
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
