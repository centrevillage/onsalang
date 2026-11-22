//! `sample_tick()` in the commands of `onsa` (W7-09 U4b/t, W7-16 U5a/t; spec §11.4, §11.3, §11.9, §18.1, `spec/tools.md` §1.1; S-565, S-567 (K6), Q-09):
//! what the case files in `tests/spec/flow_clock/` and `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow that reads `sample_tick()` with no modifier and no child (in a `let`, the output, a `par`, the first argument of a delay) is lowered by `build`, `dump --core` and
//!   `test` (W7-16 U5a: the counter of the phase is a field of the state); `check` reads it with no diagnostic and `onsa interface` ends with 0.
//! - What stays E0200 after U5a is the work of the later units: the head of a chain (U6a, U6b), a body of a conversion flow (U5b, U6a, U6b) and a child instance that
//!   reads it (U5b). `build`, `dump --core` and `test` stop at them with E0200 and with nothing else (no internal error); the first diagnostic is at the first place
//!   of the file that has such a form (§18.1: the order of the diagnostics).
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

/// The forms that stay E0200 after U5a, each with the line of its first form: the head of a chain (line 6), a conversion flow that reads it in its body (the flow `g` and its call,
/// line 1 is the first place of a form), and a child instance of a module that reads it (U5b). The chain and the conversion flow are the later units (U6a, U6b).
#[test]
fn a_chain_a_conversion_flow_and_a_child_that_read_sample_tick_are_e0200_until_the_later_units() {
    /// The main file, the other files and the line of the first form.
    type Source<'a> = (&'a str, &'a [(&'a str, &'a str)], Option<u64>);
    let sources: [Source; 3] = [
        (
            "flow pass_u32(g: U32 at sample) -> U32 at sample {\n  g\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  pass_u32~(sample_tick()).down~(4) at sample\n}\n",
            &[],
            Some(6),
        ),
        (
            "flow g(x: F32 at (sample * 2)) -> F32 at sample {\n  x[1] * F32.round_from(sample_tick())\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x).down~(2) at sample\n}\n",
            &[],
            Some(1),
        ),
        (
            "use ticks\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  ticks.elapsed~(x)\n}\n",
            &[("ticks.onsa", "pub flow elapsed(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n")],
            None,
        ),
    ];
    for (k, (flows, others, first)) in sources.iter().enumerate() {
        assert_e0200(&format!("sample_tick_e0200_{k}"), flows, others, *first);
    }
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
