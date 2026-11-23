//! `sample_tick()` in the commands of `onsa` (W7-09 U4b/t, W7-16 U5a/t, U5b2/t, U6a3/t; spec §11.4, §11.3, §11.9, §18.1, `spec/tools.md` §1.1; S-565, S-567 (K6), S-1129 (1), S-1217, Q-09):
//! what the case files in `tests/spec/flow_clock/` and `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow that reads `sample_tick()` with no modifier (in a `let`, the output, a `par`, the first argument of a delay), and a child instance with no modifier that reads it (in the flow of the
//!   package or of a module, in its output or in a stage of `sample / N`, in a grandchild), is lowered by `build`, `dump --core` and `test` (W7-16 U5a, U5b2: the counter of the phase is a field of
//!   the state and the time is the time of the parent); `check` reads it with no diagnostic and `onsa interface` ends with 0.
//! - A chain of `.down~(N)` over a part that does not read `sample_tick()` is lowered even when its argument does (the argument is read in the caller, at the tick of the input; W7-16 U6a1/t).
//! - A chain of `.down~(N)` over a part that reads `sample_tick()` (the part, a child of it, also a conversion flow) is lowered and gives the number of the outermost flow divided by N, cut to `U32` last (§11.4; W7-16 U6a3/t,
//!   S-1217). The values of the chains are in `tests/spec/flow_semantics/down_chain_time_values.onsa`; the cases here are the commands: the package is lowered and its test passes.
//! - `sample_tick()` read at a `sample * N` of the caller (an argument of a port at it, alone, in an operation, a block or an `if`, the head of a chain whose port is one in its frame, the head of an
//!   `.up~(N)`) is the `sample` value of the body it is written in, and a `sample` value is not given there: E0815 at `check` (S-1218), every command stops with it and no internal error, and the
//!   note names the conversion flow that writes the time (§11.3). Read at a port of `sample / N` it is the time of the caller (§11.4). The explicit forms (a time bundle, a held time) are lowered and
//!   give their values (`tests/spec/flow_semantics/sample_tick_explicit_burst_values.onsa`).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::{assert_lowers, error_lines, package};
use crate::test_support::{Dir, diagnostics, doc_of, record, run, str_of, test_json};

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

/// A chain with an `.up~(N)` over a part that reads `sample_tick()` is lowered (W7-16 U6b3, S-1217; it was E0200 until then): the time of the part is the number of the outermost flow, changed from the outermost modifier in
/// (§11.4: "`.up~(N)` の本体では N 倍して何歩目か（0 から N − 1）を足し、`.down~(N)` の本体では N で割って切り捨て"). `.down~(2).up~(2)`: the up makes 2 t + j in the frame t and the down divides it, the part runs at j = 0:
/// 0 1 2 3. `.up~(2).down~(4)`: the part of the down reads v at the frame 4 v, the up makes 2 v + j, the 2 outputs are dealt to the frames c and c + 2 and held: 0 0 1 1 2 2 3 3.
#[test]
fn a_chain_with_an_up_over_a_part_that_reads_sample_tick_gives_n_times_the_time_plus_the_step() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow f() -> U32 at sample {\n  tk~().down~(2).up~(2) at sample\n}\n\npub flow g() -> U32 at sample {\n  tk~().up~(2).down~(4) at sample\n}\n\ntest \"time in an up\" {\n  var a: [U32; 4] = [9; 4]\n  var b: [U32; 8] = [9; 8]\n  var sa = f.init(8.0)\n  var sb = g.init(8.0)\n  f.process(inout sa, inout a)\n  g.process(inout sb, inout b)\n  assert a == [0, 1, 2, 3]\n  assert b == [0, 0, 1, 1, 2, 2, 3, 3]\n}\n";
    assert_lowers_and_passes("sample_tick_up_values", flows, "time in an up");
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

/// The flows of the forms of S-1218: a port at `sample * 2` (`g2`), at `sample * 8` under `.down~(4)` (`g8`, `sample * 2` in the frame of the call), and a port at `sample` under `.up~(2)`.
const BURST_PORTS: &str = "flow g2(x: U32 at (sample * 2)) -> U32 at sample {\n  x[0] +% x[1] *% 10\n}\n\nflow g8(x: U32 at (sample * 8)) -> U32 at sample {\n  x[0]\n}\n\nflow pass(x: U32 at sample) -> U32 at sample {\n  x\n}\n\n";

/// `sample_tick()` read at a `sample * N` of the caller, however the argument holds it, is the `sample` value of the body (S-1218; §11.4: "書いた場所の `sample_rate()` の刻みの数", §11.3: "`sample * N` へは、変換の
/// flow で書く"), and a `sample` value is not given to a port at `sample * N` (§11.9): `check`, `build`, `dump --core` and `test` stop with E0815 and nothing else, and no command ends with an internal error.
/// Only the stop is pinned, no value.
#[test]
fn sample_tick_read_at_a_sample_times_n_of_the_caller_is_e0815_at_every_command() {
    let forms = [
        "g2~(sample_tick())",
        "g2~(sample_tick() *% 2)",
        "g2~({ sample_tick() })",
        "g2~(if p { sample_tick() } else { 0 })",
        "g8~(sample_tick()).down~(4) at sample",
        "g2~(pass~(sample_tick()).up~(2))",
    ];
    for (k, form) in forms.iter().enumerate() {
        let flows = format!("{BURST_PORTS}pub flow f(p: Bool at block) -> U32 at sample {{\n  {form}\n}}\n");
        let d = package(&format!("sample_tick_burst_{k}"), &flows, &[]);
        let dir = d.arg();
        let commands: [Vec<&str>; 4] =
            [vec!["check"], vec!["build", "--target", "host"], vec!["dump", "--core", dir.as_str()], vec!["test"]];
        for args in commands {
            let out = run(d.root(), &args);
            let both = format!("{}{}", out.stdout, out.stderr);
            assert_eq!(out.code, 1, "{form}: {args:?}: {both}");
            assert!(!both.contains("internal error"), "{form}: {args:?}: {both}");
            let lines = error_lines(&both);
            assert!(!lines.is_empty() && lines.iter().all(|l| l.contains("error[E0815]")), "{form}: {args:?}: {both}");
        }
    }
}

/// The note of the E0815 of `g2~(sample_tick())` says where the time goes: it is written with a conversion flow (§11.3: "`sample * N` へは、変換の flow で書く", S-1218 "時間の束や複製は変換の flow で書く"),
/// so a note names the conversion flow. The words of the note are not fixed by the spec, so only that it is there and says "conversion flow" is read. One error at the line of the argument (`check --json`).
#[test]
fn the_e0815_of_sample_tick_at_a_sample_times_n_of_the_caller_notes_the_conversion_flow() {
    let flows = format!("{BURST_PORTS}pub flow f() -> U32 at sample {{\n  g2~(sample_tick())\n}}\n");
    let d = package("sample_tick_burst_note", &flows, &[]);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    let ds = diagnostics(&doc);
    assert_eq!(ds.len(), 1, "one diagnostic: {doc}");
    assert_eq!(str_of(&ds[0], "code"), "E0815", "{doc}");
    let notes: Vec<String> = ds[0]["notes"]
        .as_array()
        .unwrap_or_else(|| panic!("no `notes` array: {doc}"))
        .iter()
        .map(|n| str_of(n, "message").to_string())
        .collect();
    assert!(notes.iter().any(|n| n.contains("conversion flow")), "a note names the conversion flow: {notes:?}");
}

/// The two explicit ways that give the time to a port at `sample * 2` (S-1218, §11.3, §11.4): a time bundle `mkt` (the elements 2 k and 2 k + 1 of the frame k) and a held time `hold2` (`[k, k]`), each read
/// by `gw` (element 0 times 1000 plus element 1) are lowered by every command and give 1 2003 4005 6007 (2002 k + 1) and 0 1001 2002 3003 (1001 k).
#[test]
fn the_explicit_forms_of_a_time_for_a_port_at_a_sample_times_n_are_lowered_and_give_their_values() {
    let flows = "flow gw(x: U32 at (sample * 2)) -> U32 at sample {\n  x[0] *% 1000 +% x[1]\n}\n\nflow mkt() -> U32 at (sample * 2) {\n  let t = sample_tick()\n  [t *% 2, t *% 2 +% 1]\n}\n\nflow hold2(x: U32 at sample) -> U32 at (sample * 2) {\n  [x, x]\n}\n\npub flow bundle() -> U32 at sample {\n  gw~(mkt~())\n}\n\npub flow held() -> U32 at sample {\n  gw~(hold2~(sample_tick()))\n}\n\ntest \"explicit time\" {\n  var a: [U32; 4] = [9; 4]\n  var b: [U32; 4] = [9; 4]\n  var sa = bundle.init(8.0)\n  var sb = held.init(8.0)\n  bundle.process(inout sa, inout a)\n  held.process(inout sb, inout b)\n  assert a == [1, 2003, 4005, 6007]\n  assert b == [0, 1001, 2002, 3003]\n}\n";
    assert_lowers_and_passes("sample_tick_explicit_burst_values", flows, "explicit time");
}

/// `sample_tick()` passed to a port of `sample / 4` is read at its tick and is the time of the caller (§11.4: "書いた場所の `sample_rate()` の刻みの数", "`sample / N` の段で読んでも同じ数"): 0, 4, 8 at the
/// ticks, each held 4 frames by `at sample`. It is not a `sample * N` of the caller, so it is lowered as before S-1218.
#[test]
fn sample_tick_passed_to_a_slow_port_gives_the_time_of_the_caller() {
    let flows = "flow hold4(x: U32 at (sample / 4)) -> U32 at (sample / 4) {\n  x\n}\n\npub flow f() -> U32 at sample {\n  hold4~(sample_tick()) at sample\n}\n\ntest \"slow port time\" {\n  var out: [U32; 12] = [9; 12]\n  var st = f.init(8.0)\n  f.process(inout st, inout out)\n  assert out == [0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8]\n}\n";
    assert_lowers_and_passes("sample_tick_slow_port_values", flows, "slow port time");
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
