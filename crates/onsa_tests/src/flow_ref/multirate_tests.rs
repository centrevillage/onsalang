//! The tests of the rates of the evaluator (W7-09 U2a): the stage of a tick slower than `sample` (§11.3, §11.9), the order of the ticks of a position
//! (S-578, S-1079, S-1088), the fields a tick writes and a faster stage reads (§11.3, S-1158 (c), S-1186), `.down~(N)` and `.up~(N)` with their chains and
//! the time they run in (§11.4, §11.9, S-566, S-567), and `sample_tick()` (S-1127 (1)). The values are worked out by hand from the spec, in the comment of
//! each test. A flow that has no `sample` input is run in calls of the frames each is given, with the `block` inputs it gets.
//! `cnt~(k)` is the running sum of its input: `n[i] = k + n[i - 1]` (§11.4), so its output says how many times it ran, and with what.

use super::expr::Frame;
use super::expr_tests::{def_named, with_checked};
use super::flow::{Ctx, Instance, Outcome, PanicAt, Plans};
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::state::{InstState, Run};
use super::state_tests::{f32s, same};
use super::value::{IntKind, Value};

const CNT: &str = "flow cnt(k: F32 at sample) -> F32 at sample {
  let n = k + prev~(^n)
  n
}
flow tk() -> U32 at sample { sample_tick() }
flow rate_of() -> F32 at sample { sample_rate() }
";

type Block = Vec<(&'static str, Value)>;

/// The outputs of the flow `name` (no `sample` input) for the calls `(block inputs, frames)`, one after the other on one instance; `reset` before the call
/// with `None` for its inputs of `block` is not made here (see `again`). The inputs of `init` are `config`.
fn calls(src: &str, name: &'static str, config: Block, calls: Vec<(Block, usize)>) -> Vec<Value> {
    with_checked(src, true, move |a| {
        let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &config, None).expect("init");
        calls
            .into_iter()
            .flat_map(|(params, n)| me.process(&params, &[], n, None).expect("process"))
            .collect::<Vec<_>>()
    })
}

fn p(x: f32) -> Block {
    vec![("p", Value::F32(x))]
}

fn u32s(vs: &[Value]) -> Vec<i128> {
    vs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("not an integer: {v:?}") }).collect()
}

/// `n` frames of the flow `name` with `p`, in the calls of the sizes `sizes` (their sum is `n`).
fn split(src: &str, name: &'static str, x: f32, sizes: &[usize]) -> Vec<f32> {
    f32s(&calls(src, name, vec![], sizes.iter().map(|n| (p(x), *n)).collect()))
}

#[test]
fn a_delay_of_a_tick_runs_at_the_multiples_of_n_and_the_output_holds_until_the_next() {
    // §11.9: `sample / 4` ticks when the counter is a multiple of 4, the first frame included; §11.4: `prev~` gives its stored value at the tick and
    // stores its argument (`p` of `block`, read at the tick), here `init` 1.0. `prev~(p at (sample / 4), 1.0) at sample` is read at every frame and holds.
    // p = 3.0, 5.0, 7.0 for the calls of 4, 4 and 3 frames: the ticks are c = 0, 4, 8 and give 1.0 (init), 3.0, 5.0: 1 1 1 1 3 3 3 3 5 5 5.
    let src = "flow tick1(p: F32 at block) -> F32 at sample { prev~(p at (sample / 4), 1.0) at sample }";
    let given = vec![(p(3.0), 4), (p(5.0), 4), (p(7.0), 3)];
    same(&f32s(&calls(src, "tick1", vec![], given)), &[1.0, 1.0, 1.0, 1.0, 3.0, 3.0, 3.0, 3.0, 5.0, 5.0, 5.0]);
    // §13.4: the ticks do not depend on where the calls of `process` are cut. p = 2.0: 1 1 1 1 2 2 2 2 2 2 2 whatever the cuts.
    let want = [1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0];
    for sizes in [&[11][..], &[3, 5, 3], &[1; 11], &[4, 0, 4, 3], &[7, 4]] {
        same(&split(src, "tick1", 2.0, sizes), &want);
    }
}

#[test]
fn reset_puts_the_ticks_back_to_the_first_frame_and_the_next_frame_is_a_tick() {
    // §11.6, §11.9: `reset` makes every delay as `init` made it and the counter 0, and the frame with the counter 0 is a tick of every ratio and writes
    // the fields before they are read: after 6 frames of p = 2.0 (1 1 1 1 2 2), `reset`, the 5 frames are 1 1 1 1 2 again, not a continuation (2 2 2 2 2).
    let src = "flow tick1(p: F32 at block) -> F32 at sample { prev~(p at (sample / 4), 1.0) at sample }";
    let outs = with_checked(src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "tick1"), 48000.0, &[], None).expect("init");
        let run = |me: &mut Instance, n| f32s(&me.process(&p(2.0), &[], n, None).expect("process"));
        let first = run(&mut me, 6);
        me.reset();
        (first, run(&mut me, 5))
    });
    same(&outs.0, &[1.0, 1.0, 1.0, 1.0, 2.0, 2.0]);
    same(&outs.1, &[1.0, 1.0, 1.0, 1.0, 2.0]);
}

#[test]
fn the_ticks_of_a_position_run_from_the_larger_n_to_the_smaller_and_each_reads_the_one_before() {
    // §11.9, S-1079: at a position the ticks run in the order `sample / 4`, `sample / 2`, `sample`. `a = prev~(p at (sample / 4))`, `b = prev~(a at (sample / 2))`
    // (a slower value read at a faster tick with `at`, init 0.0). p is 1, 2, 3, 4 in the four calls of 4 frames, so `a` is 0, 1, 2, 3 at c = 0, 4, 8, 12. `b`
    // stores the `a` that is there when it ticks, at c = 0, 2, 4, ...: at c = 4 `a` is already the new 1 (the larger N first), so `b` stores 0, 0, 1, 1, 2, 2,
    // 3, 3 at c = 0 .. 14 and gives the one before: 0 (init) 0 0 1 1 2 2 3 at c = 0 .. 14, held for two frames each: 0 0 | 0 0 | 0 0 | 1 1 | 1 1 | 2 2 | 2 2 | 3 3.
    // (The other order has `b` store the old `a` at c = 4 and gives 0 0 0 0 0 0 0 0 1 1 ...)
    let src = "flow two(p: F32 at block) -> F32 at sample {
  let a = prev~(p at (sample / 4))
  let b = prev~(a at (sample / 2))
  b at sample
}";
    let given = (1..=4).map(|j| (p(j as f32), 4)).collect();
    let want = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 3.0];
    same(&f32s(&calls(src, "two", vec![], given)), &want);
}

#[test]
fn a_computed_part_of_a_tick_is_made_at_the_tick_and_a_faster_stage_reads_the_value_kept() {
    // §11.3: a part computed from a tick, read at a faster stage, is evaluated at the tick and its value is kept in a field that the faster stage reads:
    // `(lf * q) at sample`, `lf = prev~(p at (sample / 4), 1.0)` (`block` p, q). p, q are 1, 2 for 2 frames, then 3, 10 for 6 frames, then 3, 10 for 3: `lf` is 1
    // (init) at c = 0, then the stored p = 1 at c = 4, 3 at c = 8. The part is made at c = 0 with q = 2 (2.0), at c = 4 with q = 10 (10.0), at c = 8 (30.0) and held:
    // 2 2 2 2 | 10 10 10 10 | 30 30 30. At c = 2 and 3 the name `q` is 10 but the field is the 2.0 made at c = 0 (reading `q` at each frame would give 10).
    // A tick `let` read at the faster stage is its last value (`lf at sample` is 1 1 1 1 1 1 1 1 3 3 3, what the first test shows with the delay itself).
    let src = "flow field(p: F32 at block, q: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  (lf * q) at sample
}
flow node(p: F32 at block, q: F32 at block) -> F32 at sample { (prev~(p at (sample / 4), 1.0) * q) at sample }
flow name(p: F32 at block, q: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  (lf at sample) * q
}";
    let pq = |p: f32, q: f32| vec![("p", Value::F32(p)), ("q", Value::F32(q))];
    for name in ["field", "node"] {
        let given = vec![(pq(1.0, 2.0), 2), (pq(3.0, 10.0), 6), (pq(3.0, 10.0), 3)];
        let want = [2.0, 2.0, 2.0, 2.0, 10.0, 10.0, 10.0, 10.0, 30.0, 30.0, 30.0];
        same(&f32s(&calls(src, name, vec![], given)), &want);
    }
    // `(lf at sample) * q` reads a tick at `sample`: the product is of `sample`, made at each frame with the `q` of that frame, and not a field of the tick
    // (§11.3: "`(lf at sample) * 2.0` は `sample` で計算する"): 2 2 | 10 10 | 10 10 10 10 | 30 30 30 (`lf` is 1, 1, 3 and `q` is 2 for c = 0, 1 and 10 after).
    let given = vec![(pq(1.0, 2.0), 2), (pq(3.0, 10.0), 6), (pq(3.0, 10.0), 3)];
    let want = [2.0, 2.0, 10.0, 10.0, 10.0, 10.0, 10.0, 10.0, 30.0, 30.0, 30.0];
    same(&f32s(&calls(src, "name", vec![], given)), &want);
}

#[test]
fn a_part_of_a_tick_under_a_condition_of_init_or_of_a_constant_is_made_only_when_it_holds() {
    // §11.3: a computed part of a tick under a condition decided by constants, `init` and the same tick is made at the tick, only when the condition holds
    // (`if d != 0 { (m / d) at sample } else { 0 }`: a division by `d = 0` that is made would panic, §3.4, §9.2). `m = prev~(p at (sample / 2), 4)`, p = 10:
    // m is 4 at c = 0 and 10 at c = 2, 4. With d = 0 and with the constant K = 0 nothing is made and the output is 0 for the 6 frames and no panic; with d = 2
    // it is 4 / 2 = 2 at c = 0, 10 / 2 = 5 at c = 2 and 4: 2 2 5 5 5 5. A condition of the same tick (`g at (sample / 2)`, `g` of `block`) with the whole `if` read at
    // `sample`: g false, d = 0 gives 0 and no panic; g true, d = 2 gives 2 2 5 5 5 5.
    let src = "const K: I32 = 0
flow cg(d: I32 at init, p: I32 at block) -> I32 at sample {
  let m = prev~(p at (sample / 2), 4)
  if d != 0 { (m / d) at sample } else { 0 }
}
flow kg(p: I32 at block) -> I32 at sample {
  let m = prev~(p at (sample / 2), 4)
  if K != 0 { (m / K) at sample } else { 0 }
}
flow sg(g: Bool at block, d: I32 at block, p: I32 at block) -> I32 at sample {
  let m = prev~(p at (sample / 2), 4)
  (if (g at (sample / 2)) { m / d } else { 0 }) at sample
}";
    let int = |n: i128| Value::int(IntKind::I32, n);
    let ints = |vs: &[Value]| u32s(vs);
    let ten = vec![("p", int(10))];
    let d = |n| vec![("d", int(n))];
    assert_eq!(ints(&calls(src, "cg", d(0), vec![(ten.clone(), 6)])), [0; 6]);
    assert_eq!(ints(&calls(src, "cg", d(2), vec![(ten.clone(), 6)])), [2, 2, 5, 5, 5, 5]);
    assert_eq!(ints(&calls(src, "kg", vec![], vec![(ten.clone(), 6)])), [0; 6]);
    let sg = |g: bool, n: i128| vec![("g", Value::Bool(g)), ("d", int(n)), ("p", int(10))];
    assert_eq!(ints(&calls(src, "sg", vec![], vec![(sg(false, 0), 6)])), [0; 6]);
    assert_eq!(ints(&calls(src, "sg", vec![], vec![(sg(true, 2), 6)])), [2, 2, 5, 5, 5, 5]);
}

#[test]
fn a_down_chain_runs_its_instance_at_the_ticks_of_the_ratio_and_the_value_holds() {
    // §11.9: `cnt~(p).down~(4)` runs `cnt` at c = 0, 4, 8 (a tick of `sample / 4`) with the `block` input of that frame; its output is a value of `sample / 4`
    // that the caller reads at `sample` with `at` and that holds. p = 1.0: n = 1, 2, 3 at the ticks: 1 1 1 1 2 2 2 2 3 3. `.down~(2).down~(2)` is 1/4 as well
    // (the ratios multiply). With p = 1.0 for 5 frames and 10.0 for 5: c = 0, 4 give 1, 2 and c = 8 (p = 10.0) gives 12: 1 1 1 1 2 2 2 2 12 12.
    // `.down~(2).up~(2)` (S-1207: the up wraps the down) runs `cnt` at every frame, 1 2 3 4 5 6: the run 0 of the up in each frame is the tick of the down, whose input is at `sample` and gathers nothing.
    let src = format!(
        "{CNT}flow d4(p: F32 at block) -> F32 at sample {{
  let a = cnt~(p).down~(4)
  a at sample
}}
flow d22(p: F32 at block) -> F32 at sample {{
  let a = cnt~(p).down~(2).down~(2)
  a at sample
}}
flow du(p: F32 at block) -> F32 at sample {{ cnt~(p).down~(2).up~(2) }}"
    );
    let want = [1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 3.0];
    for name in ["d4", "d22"] {
        for sizes in [&[10][..], &[3, 4, 3], &[1; 10]] {
            same(&split(&src, name, 1.0, sizes), &want);
        }
    }
    let given = vec![(p(1.0), 5), (p(10.0), 5)];
    same(&f32s(&calls(&src, "d4", vec![], given)), &[1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 12.0, 12.0]);
    same(&split(&src, "du", 1.0, &[6]), &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
}

#[test]
fn a_down_chain_runs_at_a_tick_of_its_own_and_a_flow_inside_a_chain_keeps_the_counter_of_its_own() {
    // §11.4, §11.9: the body of `.down~(N)` runs at 1/N of the rate and its counter counts its own frames: `sample_rate()` is 48000 / 4 = 12000.0 and
    // `sample_tick()` is c / 4 (0 0 0 0 1 1 1 1 2 2). `.down~(2).down~(2)` gives the same, `.down~(2).up~(2)` is the counter of the caller (0 1 2 3 ...: the run 0 of the up in each frame is the tick of the down).
    // A flow with no modifier, called inside `.down~(2)`, shares its counter, and a `.down~(2)` in the body of `.up~(2)` ticks when the counter of the
    // `.up~` instance (2 c + j) is even, j = 0, with the tick (2 c) / 2 = c: the instance gives the last of its two frames, j = 1, whose held `g` is c.
    let src = format!(
        "{CNT}flow dr() -> F32 at sample {{
  let a = rate_of~().down~(4)
  a at sample
}}
flow dt() -> U32 at sample {{
  let a = tk~().down~(4)
  a at sample
}}
flow dtt() -> U32 at sample {{
  let a = tk~().down~(2).down~(2)
  a at sample
}}
flow dtu() -> U32 at sample {{ tk~().down~(2).up~(2) }}
flow upd() -> U32 at sample {{
  let g = tk~().down~(2)
  g at sample
}}
flow topup() -> U32 at sample {{
  let _ = upd~().up~(2)
  sample_tick()
}}"
    );
    same(&f32s(&calls(&src, "dr", vec![], vec![(vec![], 4)])), &[12000.0; 4]);
    for name in ["dt", "dtt"] {
        let got = u32s(&calls(&src, name, vec![], vec![(vec![], 6), (vec![], 4)]));
        assert_eq!(got, [0, 0, 0, 0, 1, 1, 1, 1, 2, 2], "{name}");
    }
    assert_eq!(u32s(&calls(&src, "dtu", vec![], vec![(vec![], 5)])), [0, 1, 2, 3, 4]);
    // The instance of `.up~(2)` is read in the state: the output of its last frame after each of the frames of the caller.
    let lasts = with_checked(&src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "topup"), 48000.0, &[], None).expect("init");
        let mut lasts = Vec::new();
        for _ in 0..5 {
            me.process(&[], &[], 1, None).expect("process");
            lasts.extend(u32s(&me.me.state.children.values().map(|c| c.out.clone()).collect::<Vec<_>>()));
        }
        lasts
    });
    assert_eq!(lasts, [0, 1, 2, 3, 4]);
}

#[test]
fn an_up_chain_runs_its_instance_n_times_in_a_frame_at_n_times_the_rate() {
    // §11.4, §11.9: `.up~(4)` runs the instance 4 times in a frame of its caller, in a time of 4 times the rate (`sample_rate()` is 192000.0) whose counter is
    // 4 c + j for j = 0 .. 3. The output is a value of `sample * 4` (the array of the four; the evaluator keeps the last of them, which a conversion flow
    // will read with the others, U2b). After frame c the last is: for `tk`, 4 c + 3 = 3, 7, 11; for `cnt~(1.0)`, which counts its runs, 4 (c + 1) = 4, 8, 12;
    // for `rate_of`, 192000.0. `cnt~(1.0).up~(2).down~(2)` is no call with no modifier (S-1207, S-1214 (3)): the down gathers the 2 values of its input before its tick, `1.0` in each frame, the
    // up runs `cnt` twice in the block and the down deals the two outputs to the frames of the block (the stream of the call, not the last run). The first block has `T.default()` = 0.0: the
    // runs add 0, 0, then 1, 1, then 1, 1 ...: the outputs 0 0 | 1 2 | 3 4 (two frames each) at c = 0 .. 5, a delay of 2 frames (`cnt~(1.0)` alone is 1 2 3 4 5 6).
    let src = format!(
        "{CNT}flow ut() -> U32 at sample {{
  let _ = tk~().up~(4)
  sample_tick()
}}
flow uc() -> F32 at sample {{
  let _ = cnt~(1.0).up~(4)
  0.0
}}
flow ur() -> F32 at sample {{
  let _ = rate_of~().up~(4)
  0.0
}}
flow ud() -> F32 at sample {{
  let a = cnt~(1.0).up~(2).down~(2)
  a at sample
}}"
    );
    let lasts = |name: &'static str| {
        with_checked(&src, true, move |a| {
            let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
            let mut lasts = Vec::new();
            for _ in 0..3 {
                me.process(&[], &[], 1, None).expect("process");
                lasts.extend(me.me.state.children.values().map(|c| c.out.clone()));
            }
            lasts
        })
    };
    assert_eq!(u32s(&lasts("ut")), [3, 7, 11]);
    same(&f32s(&lasts("uc")), &[4.0, 8.0, 12.0]);
    same(&f32s(&lasts("ur")), &[192000.0; 3]);
    let block = vec![(vec![], 6)];
    same(&f32s(&calls(&src, "ud", vec![], block)), &[0.0, 0.0, 1.0, 2.0, 3.0, 4.0]);
}

#[test]
fn the_ticks_of_a_flow_with_no_modifier_are_those_of_its_caller_and_a_modifier_over_it_makes_them_its_own() {
    // §11.9, S-1088: the ticks in the body of a flow that is called with no modifier are in the stage of its caller at the same position; a chain gives the
    // instance a time of its own. `inner` has `a = cnt~(p).down~(4)`. `outer` calls it plain: `a` ticks at c = 0, 4, 8 of the caller (1 1 1 1 2 2 2 2 3 3).
    // `outer2` calls it under `.down~(2)`: `inner` runs at c = 0, 2, 4, ... with the counter c / 2, so its `.down~(4)` ticks when that is a multiple of 4,
    // at c = 0, 8, 16: 1 for c = 0 .. 7, 2 for 8 .. 15, 3 for 16, 17. In `outer3` (`inner` plain in `.down~(2)` and the `.down~(2)` inside it) the same 1/8.
    let src = format!(
        "{CNT}flow inner(p: F32 at block) -> F32 at sample {{
  let a = cnt~(p).down~(4)
  a at sample
}}
flow outer(p: F32 at block) -> F32 at sample {{ inner~(p) }}
flow outer2(p: F32 at block) -> F32 at sample {{
  let i = inner~(p).down~(2)
  i at sample
}}
flow outer3(p: F32 at block) -> F32 at sample {{
  let i = inner2~(p).down~(2)
  i at sample
}}
flow inner2(p: F32 at block) -> F32 at sample {{ inner~(p) }}
flow slow_in(p: F32 at block) -> F32 at sample {{ prev~(p at (sample / 4), 1.0) at sample }}
flow outer4(p: F32 at block) -> F32 at sample {{ slow_in~(p) }}"
    );
    same(&split(&src, "outer", 1.0, &[10]), &[1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 3.0]);
    // A delay of a tick in the body of a flow called with no modifier ticks and stores with its caller's counter: `slow_in` is the first test's flow (p = 2.0).
    same(&split(&src, "outer4", 2.0, &[11]), &[1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0]);
    let eights = [vec![1.0; 8], vec![2.0; 8], vec![3.0; 2]].concat();
    for name in ["outer2", "outer3"] {
        same(&split(&src, name, 1.0, &[18]), &eights);
        same(&split(&src, name, 1.0, &[5, 6, 7]), &eights);
    }
}

#[test]
fn a_chain_in_a_par_and_in_an_if_tilde_runs_for_each_replica_and_in_every_branch() {
    // §11.5, §11.9: `par~` makes an instance of the body for each replica, `if~` evaluates every branch. Two replicas of `cnt~(p).down~(2)` each count 1, 2, 3, 4 at
    // c = 0, 2, 4, 6, so the sum is 2, 4, 6, 8, held for two frames: 2 2 4 4 6 6 8 8. In `if~ s { cnt~(p).down~(2) } else { 0.0 }` the branch not taken runs as well, so with `s` false at
    // first (call 1, 2 frames) and then true (call 2, 4 frames) the counter has run at c = 0 already when it is first taken, at c = 2 (n = 2), and then n = 3 at
    // c = 4: 0 0 | 2 2 | 3 3 (a branch that was not run would give 1 1 | 2 2).
    let src = format!(
        "{CNT}flow parr(p: F32 at block) -> F32 at sample {{
  let r = par~ i in 0 ..< 2 {{ cnt~(p).down~(2) }}
  (r[0] + r[1]) at sample
}}
flow ifn(p: F32 at block, s: Bool at block) -> F32 at sample {{
  let y = if~ s {{ cnt~(p).down~(2) }} else {{ 0.0 }}
  y at sample
}}"
    );
    same(&split(&src, "parr", 1.0, &[8]), &[2.0, 2.0, 4.0, 4.0, 6.0, 6.0, 8.0, 8.0]);
    let given = vec![
        (vec![("p", Value::F32(1.0)), ("s", Value::Bool(false))], 2),
        (vec![("p", Value::F32(1.0)), ("s", Value::Bool(true))], 4),
    ];
    same(&f32s(&calls(&src, "ifn", vec![], given)), &[0.0, 0.0, 2.0, 2.0, 3.0, 3.0]);
}

#[test]
fn sample_tick_in_a_tick_is_the_counter_of_the_instance_at_that_position() {
    // §11.4: `sample_tick()` is of the clock of the place that reads it and gives the counter of the instance, so in a `let` of `sample / 4` it is c at c = 0, 4,
    // 8. `t = prev~(n at (sample / 4)) + sample_tick()` (`n` a `U32` of `block`, 1) is 0 + 0 at c = 0 (init), 1 + 4 = 5 at c = 4, 1 + 8 = 9 at c = 8, held:
    // 0 0 0 0 5 5 5 5 9 (a `let` of the clock `sample` would give 0 1 2 3 ...).
    let src = "flow amb(n: U32 at block) -> U32 at sample {
  let t = prev~(n at (sample / 4)) + sample_tick()
  t at sample
}";
    let one = vec![("n", Value::int(IntKind::U32, 1))];
    assert_eq!(u32s(&calls(src, "amb", vec![], vec![(one, 9)])), [0, 0, 0, 0, 5, 5, 5, 5, 9]);
}

#[test]
fn a_panic_of_a_part_of_a_tick_is_of_the_frame_of_the_tick() {
    // §9.2, §11.3, §11.6: the part is made at the tick, so its panic is the panic of that frame, not of a later one that only reads the field. `(m / d) at sample`
    // with `m = prev~(p at (sample / 4), 5)`: the call of 2 frames has d = 1 (the tick at c = 0 is 5 / 1), the next of 6 frames has d = 0, which the frames
    // c = 2, 3 read without making the part again; the tick c = 4 is the frame 2 of that call and makes 2 / 0 (the p stored at c = 0): a panic `DivZero` at `Sample(2)`, the part
    // being the division (a part read at each frame would panic at the frame 0 of the call, c = 2).
    let src = "flow pz(d: I32 at block, p: I32 at block) -> I32 at sample {
  let m = prev~(p at (sample / 4), 5)
  (m / d) at sample
}";
    let at = with_checked(src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "pz"), 48000.0, &[], None).expect("init");
        let int = |n| Value::int(IntKind::I32, n);
        let first = me.process_outcome(&[("d", int(1)), ("p", int(2))], &[], 2, None).expect("a call");
        assert!(matches!(first, Outcome::Ok(ref outs) if u32s(outs) == [5, 5]), "{first:?}");
        match me.process_outcome(&[("d", int(0)), ("p", int(2))], &[], 6, None).expect("a call") {
            Outcome::Panic { at, stop } => (at, stop.fault),
            other => panic!("not a panic: {other:?}"),
        }
    });
    assert_eq!(at, (PanicAt::Sample(2), Fault::Panic(PanicKind::DivZero)));
}

#[test]
fn a_loop_whose_clock_is_a_tick_ticks_with_it() {
    // §11.3: a loop has the clock that enters from outside, and one that a tick enters through no `at` ticks with `sample / 4`: c = 0, 4, 8, and its delay counts those ticks. The tick may
    // enter as the second operand, as a name, or as the delay's own argument. `lf` (`prev~(p at (sample / 4))`, init 0) is 0 at c = 0, then the p of the tick before: p = 2, 5, 7 for calls of
    // 4 frames gives 0, 2, 5. `s = prev~(^s) + lf` adds it to the `s` of the tick before: 0, 2, 7, each held 4 frames (`s at sample`). `s = prev~(lf + ^s)` is the `lf + s` of the tick before: 0
    // (nothing before), 0 (c = 0 stored 0 + 0), 2 (c = 4 stored 2 + 0): 0 0 0 0 0 0 0 0 2 2 2 2.
    let loops = [
        ("let s = prev~(^s) + (prev~(p at (sample / 4)))", [0.0, 2.0, 7.0]),
        ("let lf = prev~(p at (sample / 4))\n  let s = prev~(^s) + lf", [0.0, 2.0, 7.0]),
        ("let lf = prev~(p at (sample / 4))\n  let s = prev~(lf + ^s)", [0.0, 0.0, 2.0]),
    ];
    for (body, ticks) in loops {
        let src = format!("flow lp(p: F32 at block) -> F32 at sample {{\n  {body}\n  s at sample\n}}");
        let given = vec![(p(2.0), 4), (p(5.0), 4), (p(7.0), 4)];
        let want: Vec<f32> = ticks.iter().flat_map(|v| [*v; 4]).collect();
        same(&f32s(&calls(&src, "lp", vec![], given)), &want);
        // §13.4: not what the calls are cut at.
        let given = vec![(p(2.0), 3), (p(2.0), 1), (p(5.0), 4), (p(7.0), 4)];
        same(&f32s(&calls(&src, "lp", vec![], given)), &want);
    }
}

#[test]
fn a_loop_that_a_tick_enters_under_an_at_to_sample_ticks_with_sample() {
    // §11.3: the clock of a loop is that of what enters it from outside, and an `at` gives the clock it names ("`at` で付けたクロックは ... 帰還の輪（輪のクロック）
    // ... に効く"), so `(lf at sample) + prev~(^u)` is a loop of `sample`: `u` is `lf` plus the `u` of the frame before, at every frame, whatever the clock of `lf`.
    // `lf = prev~(p at (sample / 4), 1.0)`, p = 2, 5, 7 for three calls of 4 frames: `lf` is 1 (init) at c = 0 .. 3, then the p of c = 0 (2) at c = 4 .. 7 and the p of
    // c = 4 (5) at c = 8 .. 11. u = 1 2 3 4 | 6 8 10 12 | 17 22 27 32. The delay written in the loop as it is (`(prev~(...) at sample)`) is the same.
    let src = "flow lp(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let u = (lf at sample) + prev~(^u)
  u
}
flow direct(p: F32 at block) -> F32 at sample {
  let u = (prev~(p at (sample / 4), 1.0) at sample) + prev~(^u)
  u
}";
    let want = [1.0, 2.0, 3.0, 4.0, 6.0, 8.0, 10.0, 12.0, 17.0, 22.0, 27.0, 32.0];
    for name in ["lp", "direct"] {
        let given = vec![(p(2.0), 4), (p(5.0), 4), (p(7.0), 4)];
        same(&f32s(&calls(src, name, vec![], given)), &want);
    }
    // §13.4: not what the calls of `process` are cut at: p = 1.0 for 8 frames in one call and in eight is 1 2 3 4 5 6 7 8 (`lf` is 1 all the way).
    for sizes in [&[8][..], &[1; 8], &[3, 5]] {
        same(&split(src, "lp", 1.0, sizes), &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]);
    }
}

#[test]
fn a_down_then_up_chain_has_the_ticks_of_its_instance_in_the_stage_of_its_caller() {
    // §11.9, S-566, S-1088, S-1207: `slow_in~(p).down~(2).up~(2)` runs `slow_in` at the time of its caller (the run 0 of the up in each frame is the tick of the down, and the input is `block`, which nothing gathers),
    // so its tick (`sample / 4`, the first test's `prev~`) is the caller's, at c = 0, 4, 8: the same series as the call with no modifier, p = 2.0: 1 1 1 1 2 2 2 2 2 2 2. `.up~(4).down~(4)` (the up runs
    // the body 4 times in the frame of the tick of the down, which deals the 4 outputs to the next 4 frames, nothing gathered) gives the same series: the body runs at the counter 4 c' + j of the block c' = c / 4,
    // its tick is the run j = 0 of each block. (A tick that nobody runs gives the init all the way.)
    let src = "flow slow_in(p: F32 at block) -> F32 at sample { prev~(p at (sample / 4), 1.0) at sample }
flow plain(p: F32 at block) -> F32 at sample { slow_in~(p) }
flow ratio0(p: F32 at block) -> F32 at sample { slow_in~(p).down~(2).up~(2) }
flow ratio0b(p: F32 at block) -> F32 at sample { slow_in~(p).up~(4).down~(4) }";
    let want = [1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0];
    for name in ["plain", "ratio0", "ratio0b"] {
        same(&split(src, name, 2.0, &[11]), &want);
        same(&split(src, name, 2.0, &[5, 6]), &want);
    }
}

#[test]
fn a_caller_with_a_tick_of_its_own_does_not_run_the_ticks_of_an_instance_of_another_rate() {
    // §11.9, S-1088: the ticks in the body of an instance that a chain of ratio other than 0 runs are its own (its time is 1/N of its caller's). A caller that has a tick
    // of its own (`lf` of `sample / 4`, so its stage of that tick is run) must not run the ticks of the instance in it. `inner` has `a = cnt~(p).down~(4)`; under
    // `.down~(2)` it runs at c = 0, 2, 4, ... with the counter c / 2, and its `.down~(4)` ticks at c = 0, 8, 16 (the counts 1 2 3: 1 for c = 0 .. 7, 2 for 8 .. 15, 3 for
    // 16, 17). `lf` is 1.0 all the way (p = 1.0, init 1.0), so the sum is 2 for 8 frames, 3 for 8 and 4 for 2.
    let src = format!(
        "{CNT}flow inner(p: F32 at block) -> F32 at sample {{
  let a = cnt~(p).down~(4)
  a at sample
}}
flow both(p: F32 at block) -> F32 at sample {{
  let lf = prev~(p at (sample / 4), 1.0)
  let i = inner~(p).down~(2)
  (lf at sample) + (i at sample)
}}"
    );
    let want = [vec![2.0; 8], vec![3.0; 8], vec![4.0; 2]].concat();
    same(&split(&src, "both", 1.0, &[18]), &want);
    same(&split(&src, "both", 1.0, &[5, 6, 7]), &want);
}

#[test]
fn the_clocks_of_sample_over_8_and_over_16_have_the_ratios_they_name() {
    // §11.9, §11.4: `sample / N` ticks when the counter is a multiple of N, whatever the N is (a power of 2 of 2 or more). `prev~(p at (sample / 8), 1.0) at sample` with
    // p = 2.0 is 1.0 for c = 0 .. 7 (the init, given at c = 0 where the 2.0 is stored) and 2.0 from c = 8 (20 frames: 8 of 1.0 and 12 of 2.0); with `sample / 16`, 18 frames are
    // 16 of 1.0 and 2 of 2.0.
    let src = "flow e8(p: F32 at block) -> F32 at sample { prev~(p at (sample / 8), 1.0) at sample }
flow e16(p: F32 at block) -> F32 at sample { prev~(p at (sample / 16), 1.0) at sample }";
    same(&split(src, "e8", 2.0, &[20]), &[vec![1.0; 8], vec![2.0; 12]].concat());
    same(&split(src, "e16", 2.0, &[18]), &[vec![1.0; 16], vec![2.0; 2]].concat());
}

#[test]
fn the_ticks_of_three_ratios_run_from_the_slowest_and_each_reads_the_one_before() {
    // §11.9, S-1079: at a position the ticks run `sample / 16`, `sample / 8`, then the rest. `a = prev~(p at (sample / 16), 0.0)`, `b = prev~(a at (sample / 8), 0.0)`, read at
    // `sample`. p = 1, 2, 3 for three calls of 16 frames: `a` is 0 for c = 0 .. 15 (it stores 1 at c = 0), 1 for 16 .. 31 (stores 2 at c = 16) and 2 for 32 .. 47. `b` ticks
    // at c = 0, 8, 16, 24, 32, 40 and stores the `a` of that moment (the slower tick is done: at c = 16 the `a` is the new 1): it stores 0, 0, 1, 1, 2, 2 and gives the one
    // before: 0 (init), 0, 0, 1, 1, 2 for the eight frames at each tick: 0 x 24, 1 x 16, 2 x 8. (If `b` ran before `a` at c = 16 it would store the old 0: 0 x 32, 1 x 8, ...)
    let src = "flow three(p: F32 at block) -> F32 at sample {
  let a = prev~(p at (sample / 16), 0.0)
  let b = prev~(a at (sample / 8), 0.0)
  b at sample
}";
    let given = (1..=3).map(|j| (p(j as f32), 16)).collect();
    let want = [vec![0.0; 24], vec![1.0; 16], vec![2.0; 8]].concat();
    same(&f32s(&calls(src, "three", vec![], given)), &want);
}

#[test]
fn an_argument_of_a_chain_that_is_slower_than_the_chain_is_made_at_its_own_tick() {
    // §11.3, §11.9: the argument `(lf + q) at (sample / 2)` of `cnt~(...).down~(2)` reads `lf`, a value of `sample / 8`, so it is made at the tick of `lf` (`at` promotes the
    // value and does not change the stage: "`e` は `e` の式の段で評価し") and `cnt` reads that value at each of its runs. `lf = prev~(q at (sample / 8), 0.0)` is 0.0 for the
    // 8 frames; at c = 0 the field is 0 + q = 1.0 (q = 1.0 of the first call), and the runs of `cnt` at c = 0, 2, 4, 6 add 1.0 each: n = 1 2 3 4, held two frames each: 1 1 2 2 3 3 4 4.
    // (The `q` of the later calls, 10.0 and 100.0, is not read by the runs: made again at each of them it would give 1 1 11 11 111 111 211 211.)
    let src = format!(
        "{CNT}flow slow_arg(q: F32 at block) -> F32 at sample {{
  let lf = prev~(q at (sample / 8), 0.0)
  let a = cnt~((lf + q) at (sample / 2)).down~(2)
  a at sample
}}"
    );
    let given = vec![
        (vec![("q", Value::F32(1.0))], 2),
        (vec![("q", Value::F32(10.0))], 2),
        (vec![("q", Value::F32(100.0))], 4),
    ];
    same(&f32s(&calls(&src, "slow_arg", vec![], given)), &[1.0, 1.0, 2.0, 2.0, 3.0, 3.0, 4.0, 4.0]);
}

#[test]
fn the_counter_of_a_down_chain_goes_on_where_its_caller_goes_round() {
    // §11.4: `sample_tick()` in the body of `.down~(N)` is the number of the outermost flow divided by N, rounded down ("割るのは `U32` に切る前の数なので、`.down~(N)` の本体でも
    // その刻みの 2^32 で一周し"), so it does not go back to 0 where the `U32` of the caller does. From 2^32 - 4 the caller's counter is 4294967292 .. 4294967295 and then 0 .. 3 (the whole one 2^32 .. 2^32 + 3): `tk~().down~(4)` runs at 2^32 - 4 and at 2^32
    // and reads 2^30 - 1 = 1073741823 for the first four frames and 2^30 = 1073741824 for the next four. `.down~(2).down~(2)` is the same.
    let src = format!(
        "{CNT}flow dt() -> U32 at sample {{
  let a = tk~().down~(4)
  a at sample
}}
flow dtt() -> U32 at sample {{
  let a = tk~().down~(2).down~(2)
  a at sample
}}"
    );
    for name in ["dt", "dtt"] {
        let got = with_checked(&src, true, |a| {
            let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
            me.ctx.tick = u32::MAX - 3;
            u32s(&me.process(&[], &[], 8, None).expect("process"))
        });
        assert_eq!(got, [vec![1073741823; 4], vec![1073741824; 4]].concat(), "{name}");
    }
}

#[test]
fn with_bindings_takes_the_replicas_and_the_scope_off_the_run_when_it_is_done() {
    // §11.4, §11.5: a delay in a `par~` saves the bindings it is read under, and a replica's are taken off when it is done, else each replica would carry
    // the ones of those before it (the saves would grow with the square of the replicas). Inside, the run holds the replicas and the bindings given; after, the
    // ones that were there.
    let src = "flow f(x: F32 at sample) -> F32 at sample { x }";
    with_checked(src, true, |a| {
        let (view, def) = (View::new(a), def_named(a, "f"));
        let body = view.body(def).expect("a body");
        let local = body.input("x").expect("the local of x");
        let mut f = Frame::new(body);
        f.run = Some(Run::new(InstState::default(), Ctx { sample_rate: 1.0, tick: 0, rounds: 0 }, 0, Plans::default()));
        let lens = |f: &Frame| f.run.as_ref().map(|r| (r.replicas.len(), r.scope.len())).expect("a run");
        assert_eq!(lens(&f), (0, 0));
        let inside = f
            .with_bindings(&[1], vec![(local, Value::F32(1.0))], |f| {
                let one = lens(f);
                f.with_bindings(&[2, 3], vec![(local, Value::F32(2.0))], |f| Ok((one, lens(f))))
            })
            .expect("bound");
        assert_eq!(inside, ((1, 1), (3, 2)));
        assert_eq!(lens(&f), (0, 0));
    });
}

#[test]
fn a_name_of_a_loop_under_an_at_has_a_clock_when_the_clock_of_the_loop_is_made() {
    // §11.3: the clock of a loop is that of what enters it from outside, and `(a at sample)` over a name of the loop is still a name that has a clock (the one the loop is given). p = 1.0 for the 12 frames, so `lf`
    // (`prev~(p at (sample / 4), 1.0)`) is 1.0 at every tick. `a = prev~(^b)` is the `b` of the frame before and `b = (a at sample) + (lf at sample)` is a loop of `sample` (an `at` to `sample` enters it): b = a + 1 =
    // 1, 2, 3 .. 12. With `(a at (sample / 4))` and `lf` it is a loop of `sample / 4`, whose `b` is the running sum of `lf` at c = 0, 4, 8: 1, 2, 3, each held 4 frames.
    let src = "flow at_sample(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = prev~(^b)
  let b = (a at sample) + (lf at sample)
  b
}
flow at_tick(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = prev~(^b)
  let b = (a at (sample / 4)) + lf
  b at sample
}";
    for sizes in [&[12][..], &[5, 0, 7], &[1; 12]] {
        let ones: Vec<f32> = (1..=12).map(|c| c as f32).collect();
        same(&split(src, "at_sample", 1.0, sizes), &ones);
        same(&split(src, "at_tick", 1.0, sizes), &[1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0, 3.0, 3.0, 3.0, 3.0]);
    }
}

#[test]
fn a_loop_is_clocked_after_the_loop_that_a_name_of_it_enters_and_before_the_loop_that_the_name_enters() {
    // §11.3: a loop has the clock of what enters it from outside, wherever the `let`s are written. `lf` ticks with `sample / 4` and enters the loop {a, b}; `c` (written between `a` and `b`) reads `a`, so it has the
    // clock of that loop and is not in it; {d, e} reads `c`, so it enters that loop. p = 2.0 for 12 frames: `lf` is 1.0 (init) at c = 0, then 2.0, 2.0. a(k) = b(k - 1) (0 at the first tick) and b(k) = a(k) + lf(k):
    // b = 1, 3, 5. c = a + 1 = 1, 2, 4. d(k) = e(k - 1) + c(k) and e = d + 0.0: e = 1, 3, 7, each held 4 frames. A value of `sample` that enters the first loop instead of `lf` makes all of it `sample`.
    let src = "flow three(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = prev~(^b)
  let c = a + 1.0
  let b = a + lf
  let d = prev~(^e) + c
  let e = d + 0.0
  e at sample
}";
    let want: Vec<f32> = [1.0, 3.0, 7.0].iter().flat_map(|v| [*v; 4]).collect();
    for sizes in [&[12][..], &[5, 0, 7], &[1; 12]] {
        same(&split(src, "three", 2.0, sizes), &want);
    }
}

#[test]
fn an_up_chain_runs_each_stage_of_its_body_in_the_stage_of_its_caller_that_the_ratio_gives() {
    // §11.9, S-1088: the body of `.up~(2)` runs 2 times in a frame of the caller with the counter n = 2 c + j, so its `sample / 8` ticks when n is a multiple of 8 (c a multiple of 4, j = 0: a tick of `sample / 4` of the caller) and
    // its `sample / 2` ticks when n is even (j = 0, every c). `h = prev~(p at (sample / 8), 7.0)` and `g = prev~(p at (sample / 2), 5.0)` hold the `p` of the tick before; the output of a run is `100 h + g` and `sum2` adds the two runs.
    // p = 1.0, 2.0, 3.0 in three calls of 4 frames: h is 7 for c = 0 .. 3 (init), 1.0 for c = 4 .. 7 (the p at n = 0) and 2.0 for c = 8 .. 11 (the p at n = 8, c = 4); g(c) is 5.0 (init) at c = 0 and the p of
    // the frame c - 1 after: 1 1 1 | 1 2 2 2 | 2 3 3 3 (c = 1 .. 11). 100 h + g: 705, 701 701 701, 101, 102 102 102, 202, 203 203 203; twice that for the two runs.
    let src = "flow sum2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] }
flow slow3(p: F32 at block) -> F32 at sample {
  let h = prev~(p at (sample / 8), 7.0)
  let g = prev~(p at (sample / 2), 5.0)
  (h at sample) * 100.0 + (g at sample)
}
flow up3(p: F32 at block) -> F32 at sample { sum2~(slow3~(p).up~(2)) }";
    let want = [1410.0, 1402.0, 1402.0, 1402.0, 202.0, 204.0, 204.0, 204.0, 404.0, 406.0, 406.0, 406.0];
    let given = || vec![(p(1.0), 4), (p(2.0), 4), (p(3.0), 4)];
    same(&f32s(&calls(src, "up3", vec![], given())), &want);
    // §13.4: not what the calls are cut at (the `p` of each frame is that of its call).
    let cut = vec![(p(1.0), 1), (p(1.0), 3), (p(2.0), 2), (p(2.0), 2), (p(3.0), 4)];
    same(&f32s(&calls(src, "up3", vec![], cut)), &want);
}

#[test]
fn reset_makes_the_stages_of_an_instance_run_again_in_the_frame_with_the_counter_0() {
    // §11.6, §11.9: `reset` puts the counter back to 0 and the stage of an instance that a chain runs in the frame with the counter 0 runs as it did the first time. `cnt~(p).down~(2)` runs at c = 0 with the `p` of that
    // call: p = 1.0 for the first frame gives 1; after `reset`, p = 5.0 for the first frame gives 5 (`cnt` starts again), not the 1 of the run before.
    let src = format!(
        "{CNT}flow dn(p: F32 at block) -> F32 at sample {{
  let a = cnt~(p).down~(2)
  a at sample
}}"
    );
    let outs = with_checked(&src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "dn"), 48000.0, &[], None).expect("init");
        let first = f32s(&me.process(&p(1.0), &[], 1, None).expect("process"));
        me.reset();
        (first, f32s(&me.process(&p(5.0), &[], 3, None).expect("process")))
    });
    same(&outs.0, &[1.0]);
    same(&outs.1, &[5.0, 5.0, 10.0]);
}

#[test]
fn the_lets_of_a_loop_that_sample_enters_are_clocked_in_the_order_they_are_written() {
    // §11.3: `a = prev~(^c)`, `b = a + p`, `c = b + 1.0` read one another (`a` reads `c` through `^c`, so the loop is entered from `a` to `c` to `b` and back), and `(p at sample)` enters it with `sample`; each `let`
    // has the clock of the operands it reads that are written before it. p = 1.0: a is the `c` of the frame before (0.0 at the first), b = a + 1, c = b + 1: c = 2, 4, 6, 8, 10, 12.
    let src = "flow three(p: F32 at block) -> F32 at sample {
  let a = prev~(^c)
  let b = a + (p at sample)
  let c = b + 1.0
  c
}";
    for sizes in [&[6][..], &[1; 6], &[2, 0, 4]] {
        same(&split(src, "three", 1.0, sizes), &[2.0, 4.0, 6.0, 8.0, 10.0, 12.0]);
    }
}

#[test]
fn a_call_in_what_a_delay_saves_reads_its_arguments_with_the_bindings_of_the_arm_it_is_in() {
    // §11.4, §11.5: a delay stores what its argument is in the second phase, and a call in it is read there: `match~ sample_tick() { n => pass~(n) }` binds `n` to the counter of the frame as the arm is evaluated,
    // and the call reads it. `d` is the stored value of the frame before: 0 (init), then the counter of the frame before: 0 0 1 2 3, whatever the calls of `process` are cut at.
    let src = "flow pass(x: U32 at sample) -> U32 at sample { x }
flow arm_in_save() -> U32 at sample {
  let d = prev~(match~ sample_tick() { n => pass~(n) }, 0)
  d
}";
    let got = with_checked(src, true, |a| {
        let mut me = Instance::init(View::new(a), def_named(a, "arm_in_save"), 48000.0, &[], None).expect("init");
        [3, 2].iter().flat_map(|n| me.process(&[], &[], *n, None).expect("process")).collect::<Vec<_>>()
    });
    assert_eq!(u32s(&got), [0, 0, 1, 2, 3]);
}

#[test]
fn a_delay_in_the_argument_of_a_stage_that_an_instance_runs_at_the_end_of_a_frame_stores_in_that_frame() {
    // §11.4: what a delay stores in a frame is what its argument is in that frame. `acc2` has an input at `sample` and an output at `sample / 2` (`half~(v).down~(2)`: the newest of the two values it took
    // before its tick, 0.0 at the first), and its `sample` stage runs at the end of the frame of its caller, reading `prev~(p at sample, 0.0)`: that delay stores `p` in the frame it is read. p = 1.0: the delay gives
    // 0 1 1 1 1 1 1 1, and `acc2` at c = 0, 2, 4, 6 gives 0 (nothing before), v(1) = 1, v(3) = 1, v(5) = 1, each held two frames: 0 0 1 1 1 1 1 1.
    let src = "flow half(x: F32 at (sample * 2)) -> F32 at sample { x[1] }
flow acc2(v: F32 at sample) -> F32 at (sample / 2) { half~(v).down~(2) }
flow late(p: F32 at block) -> F32 at sample { acc2~(prev~(p at sample, 0.0)) at sample }";
    for sizes in [&[8][..], &[1; 8], &[3, 0, 5]] {
        same(&split(src, "late", 1.0, sizes), &[0.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]);
    }
}
