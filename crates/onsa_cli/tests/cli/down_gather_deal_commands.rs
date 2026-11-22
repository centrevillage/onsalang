//! A chain of `.down~(N)` that gathers or deals at its first boundary, over a part that reads no `sample_tick()`, in the commands of `onsa` (W7-16 U6a2/t; spec §11.9, §11.6, §12.4, §18.1; S-1207, S-1208, S-1214, S-1204,
//! Q-09): what the case `tests/spec/flow_semantics/down_gather_deal_values.onsa` cannot pin.
//!
//! - `build`, `dump --core` and `test` end with 0 and no internal error for a head with a port at `sample * M` under `.down~(N)` (the input gathered, the output dealt), for a conversion flow that is only declared, and for
//!   the forms in `par~`, `if~`, `match~` and inside a part under `.down~`. What stays E0200 is U6b: a chain whose boundary past the first one gathers or deals (`g4~(p).down~(2).down~(2)`, S-1214), a chain with an up,
//!   and a call of a conversion flow with no chain that takes or gives a burst. A head that reads `sample_tick()` under such a chain is lowered (U6a3, S-1217; `sample_tick_commands.rs` and `down_chain_time_values.onsa`).
//! - `onsa interface` of the parent has the ring of each gathered input as `<node>._gather_<boundary>_<input>` and the array of the dealt output as `<node>._deal_<boundary>`, after the state of the child, the boundary
//!   counted over the `.down~` and `.up~` of the chain and the input by its place in the declaration of the head (S-1208, §11.6); the state of a conversion flow has a known size (§12.4).
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::slow_stage_commands::{assert_e0200_in, assert_lowers, bytes_of, state_fields, state_size};
use crate::test_support::{Dir, run};

/// The heads and a part: gathers of 4 and 2 samples, two inputs, deals of 4 and 2, a head with a block input before its ports, a struct with a `Default` by hand, and `acc`.
const HEADS: &str = "\
flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

flow g2(x: F32 at (sample * 2)) -> F32 at sample {
  x[0] + x[1] * 10.0
}

flow g22(a: F32 at (sample * 2), b: F32 at (sample * 2)) -> F32 at sample {
  a[0] + b[1]
}

flow mk4(p: F32 at block) -> F32 at (sample * 4) {
  [p, p + 1.0, p + 2.0, p + 3.0]
}

flow mk2(p: F32 at block) -> F32 at (sample * 2) {
  [p, p + 1.0]
}

flow id4(x: F32 at (sample * 4)) -> F32 at (sample * 4) {
  x
}

flow acc(v: F32 at block) -> F32 at sample {
  let n = v + prev~(^n)
  n
}

pub struct Pt {
  x: F32,
  y: F32,
}

impl Default for Pt {
  rt fn default() -> Pt {
    Pt { x: 1.5, y: -2.5 }
  }
}

flow mkpt(p: F32 at block) -> Pt at (sample * 2) {
  [Pt { x: p, y: p }, Pt { x: p, y: p }]
}

";

/// Packages, each a flow `f` over `HEADS`, that `check` reads and the three commands lower.
const FORMS: [&str; 15] = [
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  g4~(x).down~(4) at sample\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  let h = acc~(p).down~(2)\n  g2~(h).down~(4) at sample\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  g22~(x, x * 2.0).down~(2) at sample\n}\n",
    "pub flow f(p: F32 at block, i: F32 at init) -> F32 at sample {\n  (g4~(p).down~(4) at sample) + (g4~(i).down~(4) at sample) + (g4~(3.0).down~(4) at sample)\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  mk4~(p).down~(4)\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  mk2~(p).down~(4) at sample\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  id4~(x).down~(4)\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  let h = acc~(p).down~(2)\n  g4~(h).down~(4).down~(2) at sample\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  let ys = par~ i in 0 ..< 2 { g4~(x * F32.round_from(i + 1)).down~(4) at sample }\n  ys[0] + ys[1]\n}\n",
    "pub flow f(c: Bool at block, x: F32 at sample) -> F32 at sample {\n  if~ c { g4~(x).down~(4) at sample } else { mk4~(1.0).down~(4) }\n}\n",
    "pub flow f(k: U32 at block, x: F32 at sample) -> F32 at sample {\n  match~ k {\n    0 => g4~(x).down~(4) at sample,\n    n => g4~(x + F32.round_from(n)).down~(4) at sample,\n  }\n}\n",
    "flow inner(p: F32 at block) -> F32 at sample {\n  g4~(p).down~(4) at sample\n}\n\npub flow f(p: F32 at block) -> F32 at sample {\n  inner~(p).down~(2) at sample\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  g4~(mk4~(p).down~(4)).down~(4) at sample\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  let q = mkpt~(p).down~(2)\n  q.x * 1000.0 + q.y\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n",
];

/// §11.9 (S-1207, S-1214): a chain of downs whose first boundary gathers an input at `sample * M` and deals an output at `sample * M`, with the ports read at a slower clock of the caller (`g2~(h).down~(4)`), a
/// value of `block`, `init` or a constant for a port, a boundary past the first one that gathers and deals nothing, the forms in `par~`, `if~`, `match~` and in a part under `.down~`, a head that gathers what another dealt, and
/// a struct that has its `Default` by hand: `check` reads each with no diagnostic, `build`, `dump --core` and `test` end with 0 and no internal error, and the test of the package runs. The last form only declares the
/// conversion flows (a body with a port at `sample * N` is lowered, W7-16 U6a2).
#[test]
fn a_chain_that_gathers_or_deals_at_its_first_boundary_is_lowered_by_build_dump_core_and_test() {
    for (k, body) in FORMS.iter().enumerate() {
        assert_lowers(&format!("gather_deal_lowers_{k}"), &format!("{HEADS}{body}"), &[]);
    }
}

const PARTS: &str = "\
pub flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

pub flow mk4(p: F32 at block) -> F32 at (sample * 4) {
  [p, p + 1.0, p + 2.0, p + 3.0]
}

pub flow both(p: F32 at block, x: F32 at (sample * 2), y: F32 at (sample * 2)) -> F32 at (sample * 2) {
  [x[0] + y[1] + p, x[1] + y[0]]
}

pub flow mixed(x: F32 at (sample * 4), y: F32 at (sample * 2)) -> F32 at (sample * 8) {
  let v = x[3] + y[1]
  [v, v, v, v, v, v, v, v]
}

flow acc(f: F32 at block) -> F32 at sample {
  let n = f + prev~(^n)
  n
}

pub flow gather(x: F32 at sample) -> F32 at sample {
  let y = g4~(x).down~(4)
  y at sample
}

pub flow deal(p: F32 at block) -> F32 at sample {
  mk4~(p).down~(4)
}

pub flow both_chain(x: F32 at sample, p: F32 at block) -> F32 at sample {
  both~(p, x, x * 2.0).down~(2)
}

pub flow mixed_chain(f: F32 at block) -> F32 at sample {
  let a = acc~(f).down~(2)
  let b = acc~(f).down~(4)
  mixed~(a, b).down~(8) at sample
}

pub flow nested_chain(f: F32 at block) -> F32 at sample {
  let h = acc~(f).down~(2)
  g4~(h).down~(4).down~(2) at sample
}
";

/// The names of the fields of `<flow>.State` that are a ring or an array of a chain, with their line.
fn chain_fields(text: &str, flow: &str) -> Vec<(String, u64, String)> {
    state_fields(text, flow).into_iter().filter(|f| f.0.contains("._gather_") || f.0.contains("._deal_")).collect()
}

/// S-1208 and §11.6: the ring of an input is `<node>._gather_<boundary>_<input>` and the array of the output `<node>._deal_<boundary>`, the boundary counted over the `.down~` and `.up~` of the chain from 0 (also
/// when there is one) and the input by its place among the inputs of the head (also the `block` ones: `both` has `p` at 0, so its ports are 1 and 2), the rings in the order of the inputs and the array last; they come
/// after the state of the child (`Own`) and before `_poisoned`, in the line of the node; each is an array of the values of the port (`[T; 2^k]`), so 16 bytes for 4 of `F32`, 8 for 2, 32 for 8, with the alignment
/// of `F32`. A boundary of the chain that gathers nothing has no field (`.down~(4).down~(2)` has `_gather_0_0` only). The state of the head does not have them.
#[test]
fn the_interface_names_the_ring_and_the_array_of_a_chain_after_the_state_of_the_child() {
    let d = Dir::pkg("gather_deal_interface");
    d.write("m.onsa", PARTS);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);

    // (flow, the node of the call, the head it calls, the fields of the chain with their sizes)
    type Case<'a> = (&'a str, &'a str, &'a str, &'a [(&'a str, u64)]);
    let cases: [Case; 5] = [
        ("gather", "y.g4_0", "g4", &[("y.g4_0._gather_0_0", 16)]),
        ("deal", "_out.mk4_0", "mk4", &[("_out.mk4_0._deal_0", 16)]),
        (
            "both_chain",
            "_out.both_0",
            "both",
            &[("_out.both_0._gather_0_1", 8), ("_out.both_0._gather_0_2", 8), ("_out.both_0._deal_0", 8)],
        ),
        (
            "mixed_chain",
            "_out.mixed_0",
            "mixed",
            &[("_out.mixed_0._gather_0_0", 16), ("_out.mixed_0._gather_0_1", 8), ("_out.mixed_0._deal_0", 32)],
        ),
        ("nested_chain", "_out.g4_0", "g4", &[("_out.g4_0._gather_0_0", 16)]),
    ];
    for (flow, node, head, want) in cases {
        let all = state_fields(&out.stdout, flow);
        let names: Vec<&str> = all.iter().map(|f| f.0.as_str()).collect();
        let fields = chain_fields(&out.stdout, flow);
        let got: Vec<(&str, u64)> = fields.iter().map(|f| (f.0.as_str(), bytes_of(&f.2))).collect();
        assert_eq!(got, want, "{flow}: the rings and the array, in order, with their sizes: {names:?}");
        let at = |n: &str| {
            names.iter().position(|x| *x == n).unwrap_or_else(|| panic!("{flow}: a field `{n}` in {names:?}"))
        };
        assert_eq!(
            at(want[0].0),
            at(node) + 1,
            "{flow}: the first ring is just after the state of the child: {names:?}"
        );
        for w in want.windows(2) {
            assert_eq!(at(w[1].0), at(w[0].0) + 1, "{flow}: the fields of the chain are in a row: {names:?}");
        }
        assert_eq!(names[names.len() - 2..], ["_poisoned", "_initialized"], "{flow}: {names:?}");
        assert_eq!(
            bytes_of(&all[at(node)].2),
            state_size(&out.stdout, head),
            "{flow}: the field of the child is its state, which has no ring: {}",
            all[at(node)].2
        );
        for f in &fields {
            assert!(f.2.contains("align 4"), "{flow}: the alignment of F32: {}", f.2);
            let before = &all[at(&f.0) - 1];
            assert!(
                f.1 >= before.1 + bytes_of(&before.2),
                "{flow}: `{}` does not overlap the field before it: {all:?}",
                f.0
            );
        }
    }
    // The heads have no ring and no array of their own (their states keep what §11.3 and §11.6 put there: the
    // hoisted `block` value of `mk4`, the copy of the input `p` of `both`).
    for head in ["g4", "mk4", "both", "mixed"] {
        assert!(chain_fields(&out.stdout, head).is_empty(), "{head}: {:?}", state_fields(&out.stdout, head));
    }
}

/// §12.4 and §11.6: the state of a conversion flow (a port at `sample * N` or an output at `sample * N`) has a size that `onsa interface` writes: the memory of its body and the two flags, with no field for a port (a port
/// at `sample * N` is an array the body reads, not a value that is stored). A flow of 2 flags is 2 bytes with the alignment 1, one with a delay of `F32` 8 bytes with the alignment 4.
#[test]
fn the_interface_of_a_conversion_flow_has_the_size_of_its_state() {
    let src = "pub flow fold4(x: F32 at (sample * 4)) -> F32 at sample {
  (x[0] + x[1] + x[2] + x[3]) * 0.25
}

pub flow dup2(x: F32 at sample) -> F32 at (sample * 2) {
  [x, x]
}

pub flow fold_lp(x: F32 at (sample * 2)) -> F32 at sample {
  let m = x[0] + x[1]
  m * 0.5 + prev~(m) * 0.5
}
";
    let d = Dir::pkg("gather_deal_conversion_state");
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    for flow in ["fold4", "dup2"] {
        let names: Vec<String> = state_fields(&out.stdout, flow).into_iter().map(|f| f.0).collect();
        assert_eq!(names, ["_poisoned", "_initialized"], "{flow}");
        assert_eq!(state_size(&out.stdout, flow), 2, "{flow}: {}", out.stdout);
    }
    let lp = state_fields(&out.stdout, "fold_lp");
    let names: Vec<&str> = lp.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(names, ["_out.prev_0", "_poisoned", "_initialized"], "the delay of the body and the flags");
    assert_eq!(state_size(&out.stdout, "fold_lp"), 8, "{}", out.stdout);
}

/// What U6a2 does not lower stays E0200 and nothing else, in the flow that has the form (§18.1: a flow is checked alone), and the flows beside it that gather at their first boundary are lowered: a boundary past the first
/// one that gathers (`g4~(p).down~(2).down~(2)`: the first boundary gathers at the clock of its caller's `sample * 2`, S-1214 (1)) and one that deals (`mk4~(p).down~(2).down~(2)`) are U6b.
#[test]
fn a_chain_that_gathers_or_deals_past_its_first_boundary_is_e0200_until_u6b() {
    let flows = "flow g4(x: F32 at (sample * 4)) -> F32 at sample {
  x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0
}

flow mk4(p: F32 at block) -> F32 at (sample * 4) {
  [p, p + 1.0, p + 2.0, p + 3.0]
}

pub flow outer_gather(p: F32 at block) -> F32 at sample {
  g4~(p).down~(2).down~(2) at sample
}

pub flow ok(x: F32 at sample, p: F32 at block) -> F32 at sample {
  (g4~(x).down~(4) at sample) + mk4~(p).down~(4)
}

pub flow outer_deal(p: F32 at block) -> F32 at sample {
  mk4~(p).down~(2).down~(2)
}
";
    assert_e0200_in("gather_deal_outer_e0200", flows, &["outer_gather", "outer_deal"]);
}
