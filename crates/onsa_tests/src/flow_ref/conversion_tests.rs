//! The tests of the conversion flows of the evaluator (W7-09 U2b): the ports at `sample * N` and `sample / N` (§11.9), what a `.down~(N)` chain gathers and deals
//! (position c gathers c - N .. c - 1, the frames c .. c + N - 1 read the array dealt, position 0 has `T.default()`), an `.up~(N)` chain that passes its N values as an
//! array, the ticks of an instance with no modifier whose ports are ticks (S-1088), and a loop through two `let`s that a tick enters (§11.3). The values are worked out by
//! hand from the spec, in the comment of each test. In every flow of a column `x` the frame c has the value `c + 1` unless said otherwise, so the values a tick gathers
//! are the ones of the frames before it (the frame c = 0 has 0 for all of them: `T.default()`).

use super::boundary::{Boundary, Status};
use super::expr_tests::{def_named, i32v, with_checked};
use super::flow::Instance;
use super::scalar::Fault;
use super::sema_view::View;
use super::state::Role;
use super::state_tests::{f32s, same};
use super::value::{IntKind, Value};
use onsa_syntax::ast::{ExprKind, StmtKind};

const CONV: &str = "
flow sum4(x: F32 at (sample * 4)) -> F32 at sample { x[0] + x[1] + x[2] + x[3] }
flow newest4(x: F32 at (sample * 4)) -> F32 at sample { x[3] }
flow oldest4(x: F32 at (sample * 4)) -> F32 at sample { x[0] }
flow pass4(x: F32 at (sample * 4)) -> F32 at (sample * 4) { x }
flow hold4(c: F32 at sample) -> F32 at (sample * 4) { [c, c, c, c] }
flow ramp4(c: F32 at sample) -> F32 at (sample * 4) { [c, c + 1.0, c + 2.0, c + 3.0] }
";

type Block = Vec<(&'static str, Value)>;

/// The outputs of the flow `name` for the calls `(block inputs, frames)` one after the other on one instance, the columns `cols` of the `sample` inputs cut across them; `reset` between the
/// calls whose list is `resets`.
fn run(
    src: &str,
    name: &'static str,
    calls: Vec<(Block, usize)>,
    cols: &[(&'static str, Vec<Value>)],
    resets: &[usize],
) -> Vec<Value> {
    let (cols, resets) = (cols.to_vec(), resets.to_vec());
    with_checked(src, true, move |a| {
        let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
        let (mut outs, mut at) = (Vec::new(), 0);
        for (i, (params, n)) in calls.into_iter().enumerate() {
            if resets.contains(&i) {
                me.reset();
            }
            let part: Vec<(&str, &[Value])> = cols.iter().map(|(name, c)| (*name, &c[at..at + n])).collect();
            outs.extend(me.process(&params, &part, n, None).expect("process"));
            at += n;
        }
        outs
    })
}

/// The column `c + 1` for `n` frames, and the one of the same kind that `f` makes.
fn ramp(n: usize) -> Vec<Value> {
    (0..n).map(|c| Value::F32(c as f32 + 1.0)).collect()
}

/// `x` for one `sample` input, with the calls cut at `sizes`.
fn go(src: &str, name: &'static str, x: Vec<Value>, sizes: &[usize]) -> Vec<f32> {
    f32s(&run(src, name, sizes.iter().map(|n| (vec![], *n)).collect(), &[("x", x)], &[]))
}

fn rep(parts: &[(f32, usize)]) -> Vec<f32> {
    parts.iter().flat_map(|(v, n)| std::iter::repeat_n(*v, *n)).collect()
}

fn p(x: f32) -> Block {
    vec![("p", Value::F32(x))]
}

const CUTS: [&[usize]; 4] = [&[12], &[5, 7], &[1; 12], &[3, 0, 9]];

#[test]
fn a_down_chain_gathers_the_n_values_of_the_sample_before_its_tick_and_the_first_tick_has_the_default() {
    // §11.9: the instance `sum4~(x).down~(4)` runs at c = 0, 4, 8 and its input at `sample * 4` is, at the tick c, the array of the values of c - 4 .. c - 1 with `x[3]` that of c - 1,
    // the value of the frame c itself not in it, and at the first tick (position 0) `T.default()` where there is no sample before. x[c] = c + 1: the tick c = 4 has [1, 2, 3, 4], c = 8 has
    // [5, 6, 7, 8]. `sum4` gives 0 (the four defaults), 10, 26; `newest4` (x[3]) gives 0, 4, 8 (the value of the frame 3 is 4, not that of the frame 4, which is 5); `oldest4` (x[0]) gives
    // 0, 1, 5. The value is of `sample / 4` and holds until the next tick: 4 frames each. The same for any cut of the calls of `process` (§13.4).
    let src = format!(
        "{CONV}flow g_sum(x: F32 at sample) -> F32 at sample {{ sum4~(x).down~(4) at sample }}
flow g_new(x: F32 at sample) -> F32 at sample {{ newest4~(x).down~(4) at sample }}
flow g_old(x: F32 at sample) -> F32 at sample {{ oldest4~(x).down~(4) at sample }}
flow g_let(x: F32 at sample) -> F32 at sample {{
  let m = sum4~(x).down~(4)
  x * 0.0 + (m at sample)
}}"
    );
    for sizes in CUTS {
        same(&go(&src, "g_sum", ramp(12), sizes), &rep(&[(0.0, 4), (10.0, 4), (26.0, 4)]));
        same(&go(&src, "g_let", ramp(12), sizes), &rep(&[(0.0, 4), (10.0, 4), (26.0, 4)]));
        same(&go(&src, "g_new", ramp(12), sizes), &rep(&[(0.0, 4), (4.0, 4), (8.0, 4)]));
        same(&go(&src, "g_old", ramp(12), sizes), &rep(&[(0.0, 4), (1.0, 4), (5.0, 4)]));
    }
}

#[test]
fn reset_puts_the_position_back_to_0_and_the_gathered_values_back_to_the_default() {
    // §11.9, §11.6: after `reset` the counter is 0 and the first tick is a position 0 again: the frames before it are `T.default()`, not the values the instance had gathered. 12 frames of x = 1 .. 12
    // (0 0 0 0 10 10 10 10 26 26 26 26), `reset`, then 8 frames of 100: the tick c = 0 has the four defaults (0), the tick c = 4 the four 100s (400): 0 0 0 0 400 400 400 400.
    let src = format!("{CONV}flow g_sum(x: F32 at sample) -> F32 at sample {{ sum4~(x).down~(4) at sample }}");
    let x: Vec<Value> = ramp(12).into_iter().chain(vec![Value::F32(100.0); 8]).collect();
    let got = f32s(&run(&src, "g_sum", vec![(vec![], 12), (vec![], 8)], &[("x", x)], &[1]));
    same(&got, &[rep(&[(0.0, 4), (10.0, 4), (26.0, 4)]), rep(&[(0.0, 4), (400.0, 4)])].concat());
}

#[test]
fn a_down_chain_deals_the_array_it_made_to_the_n_frames_from_its_tick_in_order() {
    // §11.9: the output at `sample * 4` of `ramp4~(p).down~(4)` is the array `[c, c + 1, c + 2, c + 3]` of the run at the tick c, and the frames c, c + 1, c + 2, c + 3 read its elements 0, 1, 2, 3 in order.
    // The argument `p` (`block`) is read at the tick: p = 10 for the calls of 4 frames, then 20, then 30: 10 11 12 13 | 20 21 22 23 | 30 31 32. With p = 10 all the way the same four values
    // repeat, whatever the cuts of the calls are. (A frame that read the array of the tick before, or each of them the last element, would differ.)
    let src = format!("{CONV}flow d_ramp(p: F32 at block) -> F32 at sample {{ ramp4~(p).down~(4) }}");
    let given = vec![(p(10.0), 4), (p(20.0), 4), (p(30.0), 3)];
    same(
        &f32s(&run(&src, "d_ramp", given, &[], &[])),
        &[10.0, 11.0, 12.0, 13.0, 20.0, 21.0, 22.0, 23.0, 30.0, 31.0, 32.0],
    );
    let four = [10.0, 11.0, 12.0, 13.0, 10.0, 11.0, 12.0, 13.0, 10.0, 11.0, 12.0];
    for sizes in [&[11][..], &[5, 6], &[1; 11], &[2, 0, 9]] {
        let calls = sizes.iter().map(|n| (p(10.0), *n)).collect();
        same(&f32s(&run(&src, "d_ramp", calls, &[], &[])), &four);
    }
}

#[test]
fn gather_and_deal_give_back_the_input_n_samples_late_as_delay_does() {
    // §11.9: "集めて配ると N サンプル遅れる（`delay~(x, N)` と同じ）". `pass4~(x).down~(4)` has both ports of one instance: the tick c gathers c - 4 .. c - 1 and deals them to c .. c + 3, so
    // the output of the frame c is the input of c - 4 (the first four frames, from the defaults, 0): 0 0 0 0 1 2 3 4 5 6 7 8, the output of `delay~(x, 4)`. Gathering with one instance and dealing with another,
    // `hold4~(sum4~(x).down~(4)).down~(4)`, is the sums of the blocks (0, 10, 26) dealt to the four frames from the tick: 0 x 4, 10 x 4, 26 x 4.
    let src = format!(
        "{CONV}flow late(x: F32 at sample) -> F32 at sample {{ pass4~(x).down~(4) }}
flow same_as(x: F32 at sample) -> F32 at sample {{ delay~(x, 4) }}
flow two(x: F32 at sample) -> F32 at sample {{ hold4~(sum4~(x).down~(4)).down~(4) }}"
    );
    let want: Vec<f32> = (0..12).map(|c| if c < 4 { 0.0 } else { c as f32 - 3.0 }).collect();
    for sizes in CUTS {
        same(&go(&src, "late", ramp(12), sizes), &want);
        same(&go(&src, "same_as", ramp(12), sizes), &want);
        same(&go(&src, "two", ramp(12), sizes), &rep(&[(0.0, 4), (10.0, 4), (26.0, 4)]));
    }
}

#[test]
fn an_up_chain_gives_the_array_of_its_n_runs_and_the_next_flow_takes_it_in_order() {
    // §11.9: the output of `.up~(2)` is a value of `sample * 2`, the array of its two runs in a frame (the j-th run is the element j), which a flow with an input at `sample * 2` takes; and
    // an input at `sample` of `.up~(2)` takes the element j of the array of `sample * 2` it is given at the run j. `dup2~(x)` makes `[x, 3x]`; `cnt~` runs twice a frame on its j-th element
    // (n = k + n of the run before); `fold2` is `x[1] * 10 + x[0]`. x = 1, 2, 3: frame 0 [1, 3] gives n = 1, 4: [1, 4] and 41; frame 1 [2, 6] gives n = 6, 12: 126; frame 2 [3, 9] gives 15, 24: 255.
    // (The elements in the other order give 43 for the frame 0, and only the last output of the runs is no array.) `.up~(2)` of a stateless flow: the array of `proc~` (`v + 1`) of the two: x = 2: [3, 7] gives 73.
    let src = "flow dup2(x: F32 at sample) -> F32 at (sample * 2) { [x, x * 3.0] }
flow cnt(k: F32 at sample) -> F32 at sample {
  let n = k + prev~(^n)
  n
}
flow proc(v: F32 at sample) -> F32 at sample { v + 1.0 }
flow fold2(x: F32 at (sample * 2)) -> F32 at sample { x[1] * 10.0 + x[0] }
flow ud(x: F32 at sample) -> F32 at sample { fold2~(cnt~(dup2~(x)).up~(2)) }
flow up_proc(x: F32 at sample) -> F32 at sample { fold2~(proc~(dup2~(x)).up~(2)) }";
    for sizes in [&[3][..], &[1, 2], &[1; 3]] {
        let x = vec![Value::F32(1.0), Value::F32(2.0), Value::F32(3.0)];
        same(&go(src, "ud", x, sizes), &[41.0, 126.0, 255.0]);
    }
    same(&go(src, "up_proc", vec![Value::F32(2.0); 2], &[2]), &[73.0, 73.0]);
}

#[test]
fn an_instance_with_no_modifier_reads_a_tick_input_and_gives_a_tick_output_at_its_own_ticks() {
    // §11.9, S-1088: a flow with no modifier runs at the rate of its caller, and a port at `sample / 4` is a tick of the caller: `slow_gain(g at (sample / 4), x)` reads `g` at the tick c = 0, 4, 8
    // (the `lf` of the caller: 1 from the init, then the p of the tick before: p = 3, 5, 7 give 1 1 1 1 3 3 3 3 5 5 5) and `x * (g at sample)` holds it in between: x = 2 gives 2 2 2 2 6 6 6 6 10 10 10.
    // `acc(lf at (sample / 4)) -> F32 at (sample / 4) { lf + prev~(lf) }` has a state of its own that counts its ticks (S-1182 (a)): 1 + 0 = 1, 3 + 1 = 4, 5 + 3 = 8, held: 1 x 4, 4 x 4, 8 x 3.
    let src = "flow slow_gain(g: F32 at (sample / 4), x: F32 at sample) -> F32 at sample { x * (g at sample) }
flow sg(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  slow_gain~(lf, x)
}
flow acc(lf: F32 at (sample / 4)) -> F32 at (sample / 4) { lf + prev~(lf) }
flow use_acc(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = acc~(lf)
  a at sample
}";
    let given = || vec![(p(3.0), 4), (p(5.0), 4), (p(7.0), 3)];
    let x = vec![Value::F32(2.0); 11];
    same(&f32s(&run(src, "sg", given(), &[("x", x)], &[])), &rep(&[(2.0, 4), (6.0, 4), (10.0, 3)]));
    same(&f32s(&run(src, "use_acc", given(), &[], &[])), &rep(&[(1.0, 4), (4.0, 4), (8.0, 3)]));
    // §13.4: not what the calls are cut at. p = 3 all the way: lf is 1, 3, 3, so acc is 1 + 0, 3 + 1, 3 + 3: 1 x 4, 4 x 4, 6 x 3.
    let calls = [3, 5, 3].iter().map(|n| (p(3.0), *n)).collect();
    same(&f32s(&run(src, "use_acc", calls, &[], &[])), &rep(&[(1.0, 4), (4.0, 4), (6.0, 3)]));
}

#[test]
fn the_control_path_reads_the_new_average_at_the_position_of_the_tick() {
    // §11.9, S-1088: `ramp~(ctl~(avg4~(x)).down~(4))` (the shape of `lin_up32~(ctl~(avg_down32~(x)).down~(32))`): `avg4` has an output at `sample / 4` (a tick of the caller: the sum of the four frames
    // before it, `x` of the frame c + 1: 0 at c = 0, 10 at c = 4, 26 at c = 8) and runs with no modifier, so its tick is in the stage of the caller, before the `ctl` that reads it at the same
    // position: `ctl` adds 100 (100, 110, 126) and `ramp` halves the value it reads at `sample / 4`: 50 x 4, 55 x 4, 63 x 4. (`ctl` reading the average of the tick before gives 50 at c = 4.)
    let src = format!(
        "{CONV}flow avg4(x: F32 at sample) -> F32 at (sample / 4) {{ sum4~(x).down~(4) }}
flow ctl(a: F32 at sample) -> F32 at sample {{ a + 100.0 }}
flow half(v: F32 at (sample / 4)) -> F32 at sample {{ (v at sample) * 0.5 }}
flow path(x: F32 at sample) -> F32 at sample {{ half~(ctl~(avg4~(x)).down~(4)) }}
flow just(x: F32 at sample) -> F32 at sample {{ avg4~(x) at sample }}
flow acc4(x: F32 at (sample * 4)) -> F32 at sample {{
  let s = x[3] + prev~(^s)
  s
}}
flow cum(x: F32 at sample) -> F32 at (sample / 4) {{ acc4~(x).down~(4) }}
flow cum_at(x: F32 at sample) -> F32 at sample {{ cum~(x) at sample }}"
    );
    for sizes in CUTS {
        same(&go(&src, "path", ramp(12), sizes), &rep(&[(50.0, 4), (55.0, 4), (63.0, 4)]));
        same(&go(&src, "just", ramp(12), sizes), &rep(&[(0.0, 4), (10.0, 4), (26.0, 4)]));
        // A tick that is the output of an instance runs once at the position (its state counts it once): `cum` is the running sum of the `x[3]` of `acc4`, 0, 4, 12.
        same(&go(&src, "cum_at", ramp(12), sizes), &rep(&[(0.0, 4), (4.0, 4), (12.0, 4)]));
    }
}

#[test]
fn a_stereo_port_at_sample_times_n_is_an_array_of_pairs() {
    // §11.9, S-1204: `[F32; 2] at (sample * 2)` is `[[F32; 2]; 2]` in the body, `x[1]` the newest pair. `st2~([l, r]).down~(2)` takes the pairs of the two frames before its tick: l = c + 1, r = 100 (c + 1).
    // The tick c = 2 has [[1, 100], [2, 200]] and gives [2 * 10 + 1, 200 * 10 + 100] = [21, 2100]; c = 4 has [[3, 300], [4, 400]]: [43, 4300]; c = 0 has the defaults: [0, 0].
    let src = "flow st2(x: [F32; 2] at (sample * 2)) -> [F32; 2] at sample { [x[1][0] * 10.0 + x[0][0], x[1][1] * 10.0 + x[0][1]] }
flow stereo(l: F32 at sample, r: F32 at sample) -> [F32; 2] at sample { st2~([l, r]).down~(2) at sample }";
    let (l, r) = (
        ramp(6),
        ramp(6).into_iter().map(|v| Value::F32(if let Value::F32(x) = v { x * 100.0 } else { 0.0 })).collect(),
    );
    let got = run(src, "stereo", vec![(vec![], 6)], &[("l", l), ("r", r)], &[]);
    let pair = |a: f32, b: f32| Value::Array(vec![Value::F32(a), Value::F32(b)]);
    let want = [
        pair(0.0, 0.0),
        pair(0.0, 0.0),
        pair(21.0, 2100.0),
        pair(21.0, 2100.0),
        pair(43.0, 4300.0),
        pair(43.0, 4300.0),
    ];
    assert!(got.len() == 6 && got.iter().zip(&want).all(|(g, w)| g.same(w)), "{got:?}");
}

#[test]
fn the_body_of_a_conversion_flow_has_the_rate_the_counter_and_the_ticks_of_its_own() {
    // §11.9, §11.4: the `sample` of the body is the instance's: `.down~(4)` runs it at 48000 / 4 = 12000 with the counter b = c / 4, so `sample_rate()` is 12000 (also in a body that deals an array: 12000,
    // 24000, 36000, 48000 for its `[r, 2r, 3r, 4r]`), `sample_tick()` is b: 0 x 4, 1 x 4, 2 x 4. A `sample / 2` state of the body ticks at b = 0, 2, 4 = c = 0, 8, 16 (S-1182 (a)): `lf = prev~(p at (sample / 2), 0)`
    // stores the p of that frame (p = 1 for c = 0 .. 7, 2 for 8 .. 15, 3 for 16 .. 23) and is 0, 0, 1, 1, 2, 2 for b = 0 .. 5, and `x[3]` is the value of the frame c - 1 (that is c) at the tick c = 4 b, 0 for b = 0:
    // the output x[3] + lf is 0, 4, 9, 13, 18, 22 for b = 0 .. 5, each held for four frames.
    let src = "flow sr4(x: F32 at (sample * 4)) -> F32 at sample { sample_rate() }
flow st4(x: F32 at (sample * 4)) -> U32 at sample { sample_tick() }
flow dsr(c: F32 at sample) -> F32 at (sample * 4) { [sample_rate(), sample_rate() * 2.0, sample_rate() * 3.0, sample_rate() * 4.0] }
flow cs(x: F32 at (sample * 4), p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 2), 0.0)
  x[3] + (lf at sample)
}
flow r1(x: F32 at sample) -> F32 at sample { sr4~(x).down~(4) at sample }
flow t1(x: F32 at sample) -> U32 at sample { st4~(x).down~(4) at sample }
flow d1(p: F32 at block) -> F32 at sample { dsr~(p).down~(4) }
flow bs(x: F32 at sample, p: F32 at block) -> F32 at sample { cs~(x, p).down~(4) at sample }";
    same(&go(src, "r1", ramp(8), &[8]), &[12000.0; 8]);
    let ticks = run(src, "t1", vec![(vec![], 12)], &[("x", ramp(12))], &[]);
    let ticks: Vec<i128> =
        ticks.iter().map(|v| if let Value::Int(IntKind::U32, n, _) = v { *n } else { panic!("{v:?}") }).collect();
    assert_eq!(ticks, [vec![0; 4], vec![1; 4], vec![2; 4]].concat());
    same(
        &f32s(&run(src, "d1", vec![(p(0.0), 8)], &[], &[])),
        &[12000.0, 24000.0, 36000.0, 48000.0, 12000.0, 24000.0, 36000.0, 48000.0],
    );
    let given = vec![(p(1.0), 8), (p(2.0), 8), (p(3.0), 8)];
    let want = rep(&[(0.0, 4), (4.0, 4), (9.0, 4), (13.0, 4), (18.0, 4), (22.0, 4)]);
    same(&f32s(&run(src, "bs", given, &[("x", ramp(24))], &[])), &want);
    // The same when the calls are cut across the ticks: p changes at c = 8 and 16, which are ticks of the body's `sample / 2`.
    let given = vec![(p(1.0), 3), (p(1.0), 5), (p(2.0), 11), (p(3.0), 5)];
    same(&f32s(&run(src, "bs", given, &[("x", ramp(24))], &[])), &want);
}

#[test]
fn a_conversion_flow_in_a_par_a_branch_and_another_conversion_flow_keeps_a_state_for_each() {
    // §11.5, §11.9: `par~` makes the instance (and the ring of its gather) for each replica, and the argument of the gather is read with the index of the replica: r[0] sums x (0, 10, 26), r[1] sums
    // x + 1 (0, 14, 30): 0, 24, 56 for the four frames each. `if~ g { acc4~(x).down~(4) at sample } else { 0.0 }` runs the branch that is not taken as well (§11.5): `acc4` is the running sum of its
    // `x[3]`, 0, 4, 12 at c = 0, 4, 8, and g is false for the first 8 frames and true for the last 4, so the output is 0 for 8 frames and then 12 (a branch run from c = 8 only gives 8).
    // A conversion flow in the body of another: `pair~(x[3]).down~(2)` in `outer` (run each 4 frames: its body frame b has the counter b) gathers the `x[3]` of its two frames before the tick b (even):
    // x[3] of b is 4 b (0 at b = 0), the tick b = 2 gathers [0, 4] and gives 4, b = 4 gathers [8, 12] and gives 20: 0 0 4 4 20 20 for b = 0 .. 5, each for four frames of the caller.
    let src = "flow sum4(x: F32 at (sample * 4)) -> F32 at sample { x[0] + x[1] + x[2] + x[3] }
flow pg(x: F32 at sample) -> F32 at sample {
  let ks = [0.0, 1.0]
  let r = par~ i in 0 ..< 2 { sum4~(x + ks[i]).down~(4) at sample }
  r[0] + r[1]
}
flow acc4(x: F32 at (sample * 4)) -> F32 at sample {
  let s = x[3] + prev~(^s)
  s
}
flow ib(g: Bool at block, x: F32 at sample) -> F32 at sample { if~ g { acc4~(x).down~(4) at sample } else { 0.0 } }
flow pair(y: F32 at (sample * 2)) -> F32 at sample { y[1] + y[0] }
flow outer(x: F32 at (sample * 4)) -> F32 at sample { pair~(x[3]).down~(2) at sample }
flow nest(x: F32 at sample) -> F32 at sample { outer~(x).down~(4) at sample }";
    same(&go(src, "pg", ramp(12), &[12]), &rep(&[(0.0, 4), (24.0, 4), (56.0, 4)]));
    same(&go(src, "pg", ramp(12), &[5, 7]), &rep(&[(0.0, 4), (24.0, 4), (56.0, 4)]));
    let g = |g: bool| vec![("g", Value::Bool(g))];
    let got = run(src, "ib", vec![(g(false), 8), (g(true), 4)], &[("x", ramp(12))], &[]);
    same(&f32s(&got), &rep(&[(0.0, 8), (12.0, 4)]));
    same(&go(src, "nest", ramp(24), &[24]), &rep(&[(0.0, 8), (4.0, 8), (20.0, 8)]));
    same(&go(src, "nest", ramp(24), &[7, 10, 7]), &rep(&[(0.0, 8), (4.0, 8), (20.0, 8)]));
}

#[test]
fn a_gather_of_a_delay_call_keeps_the_ring_and_the_delay_apart() {
    // §11.9, §11.4: the argument that a gather takes may be a call of a delay itself. `prev~(x)` of x = c + 1 is c at the frame c (0 at the first), so the tick c = 4 gathers the frames 0 .. 3: 0 1 2 3 and
    // `x[3]` is 3; the tick c = 8 gathers 4 .. 7: 7 (a ring that took the place of the delay would give 4 and 8). `sum4` gives 0, 6, 22. `delay~(x, 2)` is 0 0 1 2 | 3 4 5 6: `x[3]` is 2, 6; `delay~(x, 3)` is
    // 0 0 0 1 | 2 3 4 5: 1, 5 (the delay of a ring and the one of one place are different cells). In a `par~` each replica has the ring and the delay: `prev~(x + ks[i])` is 0, 2, 3, 4 (c + 1 from the second
    // frame) for i = 1: `x[3]` 3 and 4, then 7 and 8: the sums 7, 15.
    let src = format!(
        "{CONV}flow t1(x: F32 at sample) -> F32 at sample {{ newest4~(prev~(x)).down~(4) at sample }}
flow t2(x: F32 at sample) -> F32 at sample {{ newest4~(delay~(x, 2)).down~(4) at sample }}
flow t3(x: F32 at sample) -> F32 at sample {{ newest4~(delay~(x, 3)).down~(4) at sample }}
flow ts(x: F32 at sample) -> F32 at sample {{ sum4~(prev~(x)).down~(4) at sample }}
flow tpar(x: F32 at sample) -> F32 at sample {{
  let ks = [0.0, 1.0]
  let r = par~ i in 0 ..< 2 {{ newest4~(prev~(x + ks[i])).down~(4) at sample }}
  r[0] + r[1]
}}"
    );
    for sizes in CUTS {
        same(&go(&src, "t1", ramp(12), sizes), &rep(&[(0.0, 4), (3.0, 4), (7.0, 4)]));
        same(&go(&src, "t2", ramp(12), sizes), &rep(&[(0.0, 4), (2.0, 4), (6.0, 4)]));
        same(&go(&src, "t3", ramp(12), sizes), &rep(&[(0.0, 4), (1.0, 4), (5.0, 4)]));
        same(&go(&src, "ts", ramp(12), sizes), &rep(&[(0.0, 4), (6.0, 4), (22.0, 4)]));
        same(&go(&src, "tpar", ramp(12), sizes), &rep(&[(0.0, 4), (7.0, 4), (15.0, 4)]));
    }
}

#[test]
fn a_chain_with_an_instance_at_two_ticks_reads_each_input_at_its_own_tick() {
    // §11.9: `two~(p at (sample / 4), p at (sample / 8)).down~(2)`: the body's `a` at `sample / 2` ticks at the instance's frames 0, 2, 4 (the caller's c = 0, 4, 8: its `p at (sample / 4)`) and `b` at
    // `sample / 4` at the instance's frames 0, 4 (c = 0, 8: its `p at (sample / 8)`), each read in the frame of the call at its own tick. The output at `sample` runs at c = 0, 2, 4, 6 and holds. p = 10
    // for 8 frames: a + b = 20 all the way. p = 10 for the first 4 frames and 20 for the next 4: `a` is 10 at c = 0 and 20 at c = 4, `b` stays 10 (its next tick is c = 8): 20 20 20 20 30 30 30 30.
    let src =
        "flow two(a: F32 at (sample / 2), b: F32 at (sample / 4)) -> F32 at sample { (a at sample) + (b at sample) }
flow t(p: F32 at block) -> F32 at sample { two~(p at (sample / 4), p at (sample / 8)).down~(2) at sample }";
    same(&f32s(&run(src, "t", vec![(p(10.0), 8)], &[], &[])), &[20.0; 8]);
    same(&f32s(&run(src, "t", vec![(p(10.0), 3), (p(10.0), 5)], &[], &[])), &[20.0; 8]);
    let changing = vec![(p(10.0), 4), (p(20.0), 4)];
    same(&f32s(&run(src, "t", changing, &[], &[])), &rep(&[(20.0, 4), (30.0, 4)]));
}

#[test]
fn an_output_at_a_tick_of_an_instance_a_chain_runs_holds_until_its_own_next_tick() {
    // §11.9: `acc2~(p).down~(2)` runs `acc2` at the caller's c = 0, 2, 4, ... (its `sample` is the caller's `sample / 2`); its output at `sample / 2` is a tick of that: the instance's frames 0, 2, 4, the
    // caller's c = 0, 4, 8, and "`.down~(N)` の出力は ... 次の自分の刻みまで前の値" (4 frames of the caller). Inside, `half~(v).down~(2)` gathers the two values of `v` before its tick and gives the newest
    // (`x[1]`): at the instance's frame 0 the defaults, 0; at the frame 2 `v` of the frame 1, which is the `p` of the caller's c = 2. p = 10 all the way: 0 0 0 0 10 10 10 10 and then 10. With p = 10, 20, 30
    // for calls of 4 frames the frame 1 reads the p of c = 2 (10), the frame 3 the p of c = 6 (20): 0 0 0 0 | 10 10 10 10 | 20 20 20 20 (the intermediate frames of the instance run at their time: a `v`
    // read at c = 4 would give 20 at the second tick). An input at the tick, `lf` at `sample / 2` of `acc3`, is read at c = 0, 4, 8 (3, 5, 7) and `lf + prev~(lf)` is 3, 8, 12: 3 x 4, 8 x 4, 12 x 4.
    let src = "flow half(x: F32 at (sample * 2)) -> F32 at sample { x[1] }
flow acc2(v: F32 at sample) -> F32 at (sample / 2) { half~(v).down~(2) }
flow c(p: F32 at block) -> F32 at sample { acc2~(p).down~(2) at sample }
flow acc3(lf: F32 at (sample / 2)) -> F32 at (sample / 2) { lf + prev~(lf) }
flow c3(p: F32 at block) -> F32 at sample { acc3~(p at (sample / 4)).down~(2) at sample }
flow tk(lf: F32 at (sample / 2)) -> F32 at (sample / 2) {
  let n = prev~(^n) + lf
  n
}
flow c4(p: F32 at block) -> F32 at sample { tk~(p at (sample / 4)).down~(2) at sample }";
    let five = vec![(p(10.0), 8)];
    same(&f32s(&run(src, "c", five, &[], &[])), &rep(&[(0.0, 4), (10.0, 4)]));
    let cut = vec![(p(10.0), 3), (p(10.0), 4), (p(10.0), 4)];
    same(&f32s(&run(src, "c", cut, &[], &[])), &rep(&[(0.0, 4), (10.0, 4), (10.0, 3)]));
    let three = vec![(p(10.0), 4), (p(20.0), 4), (p(30.0), 4)];
    same(&f32s(&run(src, "c", three, &[], &[])), &rep(&[(0.0, 4), (10.0, 4), (20.0, 4)]));
    let given = vec![(p(3.0), 4), (p(5.0), 4), (p(7.0), 4)];
    same(&f32s(&run(src, "c3", given, &[], &[])), &rep(&[(3.0, 4), (8.0, 4), (12.0, 4)]));
    // A tick of a state that counts (`n = prev~(^n) + lf`, a loop of the clock `sample / 2` of the instance) runs once at each of its ticks, not once more with the frames of the chain: 3, 3 + 5, 8 + 7.
    let given = vec![(p(3.0), 4), (p(5.0), 4), (p(7.0), 4)];
    same(&f32s(&run(src, "c4", given, &[], &[])), &rep(&[(3.0, 4), (8.0, 4), (15.0, 4)]));
}

#[test]
fn an_output_at_sample_times_n_of_a_down_chain_is_read_as_the_array_of_its_frame() {
    // §11.9: `hold4~(p).down~(2)` runs `hold4` (`[q, q + 1, q + 2, q + 3]`, the output at `sample * 4`) every 2 frames of the caller, so for the caller its value is at `sample * 2`: "配る出力は位置 c 〜 c + N − 1 の
    // `sample` の刻みが順に読む" for the 4 values over the 2 frames, in the order of time: the frame c (even) reads [q, q + 1] and the frame c + 1 [q + 2, q + 3]. `sum2` of it (x[0] + x[1]) is 2q + 1 and 2q + 5:
    // p = 10 gives 21 25 21 25 ...; p = 10 for 4 frames and 20 for 4 gives 21 25 21 25 41 45 41 45 (the run at c = 4 reads p = 20). The input side is the same reading: `w4~(hold4~(p).down~(2)).down~(2)`
    // gathers the frames c - 2 and c - 1 of the caller (2 values each, in the order of time), so the tick c = 2 has [10, 11, 12, 13] and `w4` (x[0] + 10 x[1] + 100 x[2] + 1000 x[3]) is 14320, the tick c = 0 has
    // the defaults (0): 0 0 | 14320 x 6. (The order of the elements reversed gives 11233.)
    let src = format!(
        "{CONV}flow sum2(x: F32 at (sample * 2)) -> F32 at sample {{ x[0] + x[1] }}
flow w4(x: F32 at (sample * 4)) -> F32 at sample {{ x[0] + x[1] * 10.0 + x[2] * 100.0 + x[3] * 1000.0 }}
flow o2(p: F32 at block) -> F32 at sample {{ sum2~(ramp4~(p).down~(2)) }}
flow i2(p: F32 at block) -> F32 at sample {{ w4~(ramp4~(p).down~(2)).down~(2) at sample }}"
    );
    let alt = |a: f32, b: f32, n: usize| (0..n).map(|i| if i % 2 == 0 { a } else { b }).collect::<Vec<f32>>();
    for sizes in [&[8][..], &[3, 5], &[1; 8]] {
        let calls = sizes.iter().map(|n| (p(10.0), *n)).collect();
        same(&f32s(&run(&src, "o2", calls, &[], &[])), &alt(21.0, 25.0, 8));
    }
    let two = vec![(p(10.0), 4), (p(20.0), 4)];
    same(&f32s(&run(&src, "o2", two, &[], &[])), &[21.0, 25.0, 21.0, 25.0, 41.0, 45.0, 41.0, 45.0]);
    for sizes in [&[8][..], &[3, 5], &[1; 8]] {
        let calls = sizes.iter().map(|n| (p(10.0), *n)).collect();
        same(&f32s(&run(&src, "i2", calls, &[], &[])), &rep(&[(0.0, 2), (14320.0, 6)]));
    }
}

#[test]
fn a_burst_is_of_the_type_of_the_table_when_each_of_its_values_is_and_an_array_of_them_is_not() {
    // §11.9: the table gives the call `ramp4~(p).down~(2)`, a value of `sample * 2` in the caller's frame, the type of one value (`F32`), and the value that the caller reads of it is a burst (`Value::Burst`) of its 2 values:
    // it is of that type when each of its values is (the length is the input boundary's to check, `unit_inputs`), and an array of them is not (the `[F32; 2]` of the body of a flow is another value). A value of another
    // type in it is not. One value of the type is (a value of the parameter kinds is read at any clock).
    let src = format!(
        "{CONV}flow sum2(x: F32 at (sample * 2)) -> F32 at sample {{ x[0] + x[1] }}
flow t(p: F32 at block) -> F32 at sample {{
  let r = ramp4~(p).down~(2)
  let s = sum2~(r)
  s
}}"
    );
    let (f, b) = (|x: f32| Value::F32(x), Value::Bool(true));
    let got = with_checked(&src, true, move |a| {
        let (view, def) = (View::new(a), def_named(a, "t"));
        let body = view.body(def).expect("the body");
        let ExprKind::Block(blk) = &body.ast.expr(view.flow(def).expect("the flow").body).kind else {
            panic!("a body")
        };
        let init = |n: usize| match &body.ast.stmt(blk.stmts[n]).kind {
            StmtKind::Let { init, .. } => *init,
            _ => panic!("a let"),
        };
        let ask =
            |n: usize, v: &Value| v.agrees(body.ty(init(n)).expect("the table"), view).expect("the table is whole");
        [
            ask(0, &Value::Burst(vec![f(1.0), f(2.0)])),
            ask(0, &Value::Burst(vec![f(1.0), f(2.0), f(3.0)])),
            ask(0, &Value::Burst(vec![f(1.0), b])),
            ask(0, &Value::Array(vec![f(1.0), f(2.0)])),
            ask(0, &f(1.0)),
            ask(1, &Value::Burst(vec![f(1.0), f(2.0)])),
            ask(1, &Value::Array(vec![f(1.0), f(2.0)])),
        ]
    });
    assert_eq!(got, [true, true, false, false, true, true, false]);
}

#[test]
fn a_port_that_the_caller_reads_at_a_tick_slower_than_its_sample_has_a_value_for_each_tick_of_that_tick() {
    // §11.9: the output at `sample * 2` of `hold2~(p).down~(4)` is dealt to the frames from the tick of the chain (c = 0, 4), 2 elements `[p, p + 1]` over 4 frames, so the caller reads it at its `sample / 2`: the element 0 for the
    // frames c, c + 1 and the element 1 for c + 2, c + 3 (the tick at c + 2 reads the next element). p is read at the tick of the chain, 10 and then 20: 10 10 11 11 | 20 20 21 21, for any cut of the calls that keeps the p of each frame (§13.4).
    // The input at `sample * 2` of `sum2~(p at (sample / 2)).down~(4)`, whose stream ticks at the frames 0, 2, 4, ..: S-1079 "入力のクロックの直前の M 刻み", the tick of the chain at c takes the M = 2 values of the ticks of
    // the stream before c (those at c - 4 and c - 2, `T.default()` where there are none), the position's own tick (c) is not in. p = 1, 2, 5, 7 over the frames 0 .. 3, 4 .. 7, .. : c = 0 has 0 + 0 = 0, c = 4 the p of the
    // frames 0 and 2, 1 + 1 = 2, c = 8 the p of 4 and 6, 2 + 2 = 4, c = 12 the p of 8 and 10, 5 + 5 = 10; each held for the 4 frames of the tick.
    let src = format!(
        "{CONV}flow sum2(x: F32 at (sample * 2)) -> F32 at sample {{ x[0] + x[1] }}
flow hold2(q: F32 at sample) -> F32 at (sample * 2) {{ [q, q + 1.0] }}
flow out(p: F32 at block) -> F32 at sample {{ hold2~(p).down~(4) at sample }}
flow inp(p: F32 at block) -> F32 at sample {{ sum2~(p at (sample / 2)).down~(4) at sample }}"
    );
    let calls = |cuts: &[(usize, f32)]| cuts.iter().map(|(n, v)| (p(*v), *n)).collect::<Vec<_>>();
    let out = [10.0, 10.0, 11.0, 11.0, 20.0, 20.0, 21.0, 21.0];
    for cuts in
        [&[(4, 10.0), (4, 20.0)][..], &[(1, 10.0), (3, 10.0), (2, 20.0), (2, 20.0)], &[(3, 10.0), (1, 10.0), (4, 20.0)]]
    {
        same(&f32s(&run(&src, "out", calls(cuts), &[], &[])), &out);
    }
    // The tick at c = 4 reads the p of its own frame: with the cut at 5 that is 10 (the value of the call of 5 frames), not the 20 of the next call.
    same(
        &f32s(&run(&src, "out", calls(&[(5, 10.0), (3, 20.0)]), &[], &[])),
        &[10.0, 10.0, 11.0, 11.0, 10.0, 10.0, 11.0, 11.0],
    );
    let (a, b, c, d) = ([0.0; 4], [2.0; 4], [4.0; 4], [10.0; 4]);
    let inp: Vec<f32> = [a, b, c, d].concat();
    for cuts in [
        &[(4, 1.0), (4, 2.0), (4, 5.0), (4, 7.0)][..],
        &[(2, 1.0), (2, 1.0), (3, 2.0), (1, 2.0), (4, 5.0), (1, 7.0), (3, 7.0)],
        &[(1, 1.0), (3, 1.0), (4, 2.0), (3, 5.0), (1, 5.0), (4, 7.0)],
    ] {
        same(&f32s(&run(&src, "inp", calls(cuts), &[], &[])), &inp);
    }
}

#[test]
fn a_ring_of_lets_that_a_tick_enters_ticks_with_that_tick_and_one_it_enters_under_at_sample_with_sample() {
    // §11.3: "互いに頼る `let` は一つのクロックを持ち、外から入る被演算子の刻みのクロックから決まる". The ring of `a` and `b` (the `b` reads `a` and `a` reads `^b`) has the clock of `lf`, a tick of `sample / 4`,
    // whichever `let` of the ring `lf` enters through, so both tick at c = 0, 4, 8 and the delay counts those ticks. `lf = prev~(p at (sample / 4), 1.0)` is 1 (init) at c = 0, then the p of the tick before:
    // p = 1 for 8 frames gives 1 1 (the `b` of c = 0 is 0 + 1 = 1, of c = 4 it is 1 + 1 = 2): `b at sample` 1 1 1 1 2 2 2 2. p = 2, 5, 7 for calls of 4 frames: lf is 1, 2, 5. `b = a + lf` with `a` the `b`
    // of the tick before: 1, 3, 8. A ring of three (`c = b + 1`, `a` the `c` before): a = 0, 2, 5; b = 1, 4, 10. `b = (a + 1) * lf`: 1, 4, 25. `lf` entering through `a` (`a = prev~(^b) + lf`, `b = a * 2`): a = 1, 4, 13;
    // b = 2, 8, 26. A loop of one `let` (`let s = prev~(^s) + lf`): 1, 3, 8. A tick held between (4 frames each). A member that reads the others only through `^` (`b = prev~(^c)`, with `a = prev~(^b) + lf` and `c = a + b`) has the tick of the ring as well: the `c` of the tick before, 0, 1, 3 (a = 1, 2, 6; c = 1, 3, 9).
    let ring = |lets: &str| {
        format!(
            "flow t(p: F32 at block) -> F32 at sample {{\n  let lf = prev~(p at (sample / 4), 1.0)\n{lets}\n  b at sample\n}}"
        )
    };
    let rings: [(&str, [f32; 3]); 7] = [
        ("  let a = prev~(^b)\n  let b = a + lf", [1.0, 3.0, 8.0]),
        ("  let a = prev~(^c)\n  let b = a + lf\n  let c = b + 1.0", [1.0, 4.0, 10.0]),
        ("  let a = prev~(^b, 0.0)\n  let b = (a + 1.0) * lf", [1.0, 4.0, 25.0]),
        ("  let a = prev~(^b) + lf\n  let b = a * 2.0", [2.0, 8.0, 26.0]),
        ("  let b = prev~(^b) + lf", [1.0, 3.0, 8.0]),
        ("  let a = prev~(^b)\n  let k = lf * 1.0\n  let b = a + k", [1.0, 3.0, 8.0]),
        ("  let a = prev~(^b) + lf\n  let b = prev~(^c)\n  let c = a + b", [0.0, 1.0, 3.0]),
    ];
    for (lets, ticks) in rings {
        let want: Vec<f32> = ticks.iter().flat_map(|v| [*v; 4]).collect();
        for calls in
            [vec![(p(2.0), 4), (p(5.0), 4), (p(7.0), 4)], vec![(p(2.0), 1), (p(2.0), 3), (p(5.0), 6), (p(7.0), 2)]]
        {
            same(&f32s(&run(&ring(lets), "t", calls, &[], &[])), &want);
        }
    }
    same(
        &f32s(&run(&ring("  let a = prev~(^b)\n  let b = a + lf"), "t", vec![(p(1.0), 8)], &[], &[])),
        &rep(&[(1.0, 4), (2.0, 4)]),
    );
    // `(lf at sample)` is of `sample` ("`at` で付けたクロックは ... 帰還の輪（輪のクロック）に効く"), so the ring ticks with `sample`: `b` is `a + lf` and `a` the `b` of the frame before: the running sum of `lf`
    // (1 for c < 4, 2 for 4 .. 7, 5 from 8, p = 2, 5, 7): 1 2 3 4 | 6 8 10 12 | 17 22 27 32, in any cut of the calls.
    let src = "flow t(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = prev~(^b)
  let b = a + (lf at sample)
  b
}
flow t3(p: F32 at block) -> F32 at sample {
  let lf = prev~(p at (sample / 4), 1.0)
  let a = prev~(^c)
  let c = a + 0.0
  let b = c + (lf at sample)
  b
}";
    let want = [1.0, 2.0, 3.0, 4.0, 6.0, 8.0, 10.0, 12.0, 17.0, 22.0, 27.0, 32.0];
    let calls = vec![(p(2.0), 4), (p(5.0), 4), (p(7.0), 4)];
    same(&f32s(&run(src, "t", calls, &[], &[])), &want);
    // §13.4: not what the calls are cut at: p = 1 for 8 frames is 1 2 3 4 5 6 7 8 in one call and in three.
    for sizes in [&[8][..], &[3, 3, 2], &[1; 8]] {
        let calls = sizes.iter().map(|n| (p(1.0), *n)).collect();
        same(&f32s(&run(src, "t", calls, &[], &[])), &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]);
    }
    // A ring of two `let`s that nothing from outside enters ticks with `sample` too (§11.3): `c` is always 0, the `b` outside it is `lf at sample`: 1 1 1 1 2 2 2 2 5 5 5 5.
    let calls = vec![(p(2.0), 4), (p(5.0), 4), (p(7.0), 4)];
    same(&f32s(&run(src, "t3", calls, &[], &[])), &rep(&[(1.0, 4), (2.0, 4), (5.0, 4)]));
}

#[test]
fn a_value_of_the_parameter_kinds_that_is_an_array_is_read_whole_by_each_of_the_values_of_an_input_at_sample_times_n() {
    // §11.3: a value of the parameter kinds is read at the clock where it is used, with no conversion; §11.9: the input at `sample * 2` of `f~([p, p + 1.0])` is 2 elements of `[F32; 2]` (the body sees `[[F32; 2]; 2]`), each the
    // array `[p, p + 1]`: it is no burst of 2 values (a burst of the 2 values `p` and `p + 1` would be a `F32` for the element of the type `[F32; 2]`). `x[0][0] + 10 x[1][1]` is p + 10 (p + 1) = 11 p + 10: 21 for p = 1,
    // 32 for p = 2. The input of the same kind that a chain gathers (`.down~(2)`: the elements of the 2 frames before the tick, `x[0][0] + 10 x[1][1]` of the arrays of the frames 0 and 1) is 0 at c = 0 and, at c = 2,
    // the p of the frames before: 1 for the first two frames of p = 1, 2: 1 + 10 (1 + 1) = 21, then (the frames 2 and 3 have p = 2) at c = 4: 2 + 10 (2 + 1) = 32, held for the 2 frames of a tick.
    let src = "flow f(x: [F32; 2] at (sample * 2)) -> F32 at sample { x[0][0] + 10.0 * x[1][1] }
flow whole(p: F32 at block) -> F32 at sample { f~([p, p + 1.0]) }
flow gathered(p: F32 at block) -> F32 at sample { f~([p, p + 1.0]).down~(2) at sample }";
    let calls = |cuts: &[(usize, f32)]| cuts.iter().map(|(n, v)| (p(*v), *n)).collect::<Vec<_>>();
    same(&f32s(&run(src, "whole", calls(&[(3, 1.0), (3, 2.0)]), &[], &[])), &[21.0, 21.0, 21.0, 32.0, 32.0, 32.0]);
    for cuts in [&[(2, 1.0), (2, 2.0), (2, 2.0)][..], &[(1, 1.0), (1, 1.0), (4, 2.0)]] {
        same(&f32s(&run(src, "gathered", calls(cuts), &[], &[])), &[0.0, 0.0, 21.0, 21.0, 32.0, 32.0]);
    }
}

#[test]
fn the_nodes_of_a_chain_that_gathers_and_deals_are_nodes_of_the_call_and_not_of_the_instance_or_of_its_arguments() {
    // §11.9: "集めた値は呼び出し側の値"、"配った値は呼び出し側の `sample` の値". In `mix~(prev~(x), x).down~(2)` the call keeps a ring for each of its two inputs at `sample * 2` (the second is the stream `x`, the first
    // the output of a delay, which has a node of its own that the ring does not meet), and the instance that the call makes has no node: its state is empty. The values (x = 1 .. 8; the window before the tick c = 2 t
    // is the frames c - 2, c - 1): the first input is the delay, `[x[c - 3], x[c - 2]]` (0 for the frames before the first), the second `[x[c - 2], x[c - 1]]`; `a[0] 1000 + a[1] 100 + b[0] 10 + b[1]` is
    // 0 at c = 0 (no frame before), 0 100 + 1 100 + 1 10 + 2 = 112 at c = 2 (a = 0 1, b = 1 2), 2334 at c = 4 (a = 2 3, b = 3 4) and 4556 at c = 6, each held for the 2 frames of a tick. A call that deals
    // (`twice~(p).down~(2)`, whose output is the array `[c, c + 1]` at `sample * 2`) has the array it deals as its node, and no ring (its input is at `sample`).
    let src = "flow mix(a: F32 at (sample * 2), b: F32 at (sample * 2)) -> F32 at sample { a[0] * 1000.0 + a[1] * 100.0 + b[0] * 10.0 + b[1] }
flow twice(c: F32 at sample) -> F32 at (sample * 2) { [c, c + 1.0] }
flow t(x: F32 at sample) -> F32 at sample { mix~(prev~(x), x).down~(2) at sample }
flow d(p: F32 at block) -> F32 at sample { twice~(p).down~(2) at sample }";
    let x: Vec<Value> = ramp(8);
    same(
        &f32s(&run(src, "t", vec![(vec![], 8)], &[("x", x.clone())], &[])),
        &[0.0, 0.0, 112.0, 112.0, 2334.0, 2334.0, 4556.0, 4556.0],
    );
    let nodes = with_checked(src, true, |a| {
        ["t", "d"].map(|name| {
            let me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).expect("init");
            let roles = me.me.state.cells.keys().map(|k| (k.call, k.replicas.clone(), k.role)).collect::<Vec<_>>();
            let child: Vec<usize> = me.me.state.children.values().map(|c| c.state.cells.len()).collect();
            (
                roles.iter().map(|r| r.2).collect::<Vec<_>>(),
                roles.windows(2).all(|w| w[0].0 != w[1].0 || w[0].2 != w[1].2),
                child,
            )
        })
    });
    assert_eq!(nodes[0], (vec![Role::Delay, Role::Gather(0), Role::Gather(1)], true, vec![0]));
    assert_eq!(nodes[1], (vec![Role::Deal], true, vec![0]));
    // The output of `d`: the tick at c reads the `p` of its frame, 10, 20, 30 for the calls of 2 frames, and deals `[p, p + 1]` to the frames c and c + 1, one element each: 10 11 20 21 30 31.
    let calls = vec![(p(10.0), 2), (p(20.0), 2), (p(30.0), 2)];
    same(&f32s(&run(src, "d", calls, &[], &[])), &[10.0, 11.0, 20.0, 21.0, 30.0, 31.0]);
}

#[test]
fn a_product_of_ratios_over_2_to_the_24_is_unavailable_at_init_and_one_at_the_limit_is_made() {
    // §11.9: "入れ子の比の積は 2^24 以内" (the lowering checks it, the check does not). The evaluator does not round a ratio it cannot hold: a chain of 2^25 (and one of 2^62: two of `.up~(2147483648)`, the largest N of a `U32`; the check stops one past 2^63, E0808; and one of 2^-62 over a part with a tick of `sample / 2^31`, whose stage in the caller would be 2^-93), and a chain of 2^14 in a part that a chain of 2^11
    // runs (2^25 in all) are `Unavailable` at `init` (the instance is not made), and the products 2^24 (2^11 inside 2^13) and a chain `.down~(16777216)` (2^24) are made. A frame of the instance of the
    // second kind (the slow chain: one tick at c = 0, and the value of `p` read there, 5) gives the 5 that the tick made, held; the 2^24 runs a frame of the first would make are not run here.
    let src = "flow leaf(q: F32 at sample) -> F32 at sample { q }
flow mid(p: F32 at block) -> F32 at sample { let _ = leaf~(p).up~(2048)
  0.0 }
flow within(p: F32 at block) -> F32 at sample { let _ = mid~(p).up~(8192)
  0.0 }
flow over(p: F32 at block) -> F32 at sample { let _ = mid~(p).up~(16384)
  0.0 }
flow single(p: F32 at block) -> F32 at sample { let _ = leaf~(p).up~(33554432)
  0.0 }
flow deep(p: F32 at block) -> F32 at sample { let _ = leaf~(p).up~(2147483648).up~(2147483648)
  0.0 }
flow slowb(p: F32 at block) -> F32 at sample {
  let n = prev~(p at (sample / 2147483648), 0.0) + 1.0
  n at sample
}
flow huge(p: F32 at block) -> F32 at sample { let _ = slowb~(p).down~(2147483648).down~(2147483648)
  0.0 }
flow slow(p: F32 at block) -> F32 at sample { leaf~(p).down~(16777216) at sample }";
    let made = |name: &'static str| {
        with_checked(src, true, move |a| {
            Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).map(|_| ()).map_err(|s| s.fault)
        })
    };
    assert!(made("within").is_ok());
    for name in ["over", "single", "deep", "huge"] {
        assert!(matches!(made(name), Err(Fault::Unavailable(_))), "{name}: {:?}", made(name));
    }
    same(&f32s(&run(src, "slow", vec![(p(5.0), 3)], &[], &[])), &[5.0, 5.0, 5.0]);
}

#[test]
fn a_panic_after_a_chain_stage_that_ran_in_the_frame_poisons_until_reset_which_runs_both_again() {
    // §9.2: a panic of a `process` poisons the instance, and the calls after it are zeros that evaluate nothing until `reset`; §11.6: `reset` puts every delay and the time back to the start, the instances inside too. The
    // part of `t` is run by `.down~(2)`: its `sample / 2` stage (the delay `prev~(p at (sample / 2), 0)`, whose tick is every 2 runs of the part, the frames c = 0, 4, 8, ..: the `p` that the tick before stored, 0 at the first)
    // is in the caller's stage of those frames, and its `sample` stage, which counts its runs (`c` = 1, 2, .. at the frames 0, 2, 4, ..) and has the `100 / ((p - 1) c)`, after it. p = 1: the frame 0 runs the first stage and panics in
    // the second (`100 / 0`): the outputs are 0 and the instance is poisoned, a call after it is 0 and stays so. After `reset`, p = 2: the frame 0 runs the first stage again (n = 0 + 1 = 1, the delay stores p = 2) and the second
    // gives 1 + 100 / 1 = 101 for the frames 0 and 1; the run at 2 has c = 2: 1 + 100 / 2 = 51 for 2 and 3; the tick at 4 has n = 2 + 1 = 3 and c = 3: 3 + 100 / 3 = 36 (33) for 4 and 5. It is the output of a new instance (a stage
    // that was not run again after `reset` would not have stored the 2: n = 1 and 34).
    let src = "flow dz(p: I32 at block) -> I32 at sample {
  let n = prev~(p at (sample / 2), 0) + 1
  let c = prev~(^c) + 1
  (n at sample) + 100 / ((p - 1) * c)
}
flow t(p: I32 at block) -> I32 at sample { dz~(p).down~(2) at sample }";
    let ints = |vs: Vec<Value>| {
        vs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("{v:?}") }).collect::<Vec<_>>()
    };
    let got = with_checked(src, true, move |a| {
        let mut b = Boundary::new(View::new(a), def_named(a, "t"), 48000.0);
        assert_eq!(b.init(&[], None).expect("init"), Status::Ok);
        let call = |b: &mut Boundary, p: i128, frames: usize| {
            let (status, outs) = b.process(&[("p", i32v(p))], &[], frames, None).expect("process");
            (status, ints(outs))
        };
        let (first, after) = (call(&mut b, 1, 4), call(&mut b, 2, 2));
        b.reset();
        let again = call(&mut b, 2, 6);
        (first, after, again, b.last_panic().is_none())
    });
    assert_eq!(got.0, (Status::Poisoned, vec![0; 4]));
    assert_eq!(got.1, (Status::Poisoned, vec![0; 2]));
    assert_eq!((got.2, got.3), ((Status::Ok, vec![101, 101, 51, 51, 36, 36]), true));
}

#[test]
fn the_array_a_chain_deals_is_counted_in_the_places_of_the_tree_for_each_of_its_elements() {
    // §11.9: the dealt array is the caller's (a node of its tree), `2^m` elements. The evaluator holds `Limits::most` (2^20) places for the whole tree: `bigd~(p).down~(262144)` deals the 2^18 elements of its output at
    // `sample * 262144` (262 144 places and the 8 of an instance and one for each step). Three of them (786 459) are made, and the first frame is the elements of the 3 arrays at the tick c = 0, `[p; 262144]` read at
    // the frame 0: p + 2 p + 3 p = 6 for p = 1; four (1 048 612) are over the limit: `Unavailable`. (An array that was not counted, 2^18 elements for nothing, would be made.)
    let src = "flow bigd(q: F32 at sample) -> F32 at (sample * 262144) { [q; 262144] }
flow deal3(p: F32 at block) -> F32 at sample {
  (bigd~(p).down~(262144) at sample) + (bigd~(p * 2.0).down~(262144) at sample) + (bigd~(p * 3.0).down~(262144) at sample)
}
flow deal4(p: F32 at block) -> F32 at sample {
  (bigd~(p).down~(262144) at sample) + (bigd~(p * 2.0).down~(262144) at sample) + (bigd~(p * 3.0).down~(262144) at sample) + (bigd~(p * 4.0).down~(262144) at sample)
}";
    same(&f32s(&run(src, "deal3", vec![(p(1.0), 1)], &[], &[])), &[6.0]);
    let stopped = with_checked(src, true, |a| {
        Instance::init(View::new(a), def_named(a, "deal4"), 48000.0, &[], None).map(|_| ()).map_err(|s| s.fault)
    });
    assert!(matches!(stopped, Err(Fault::Unavailable(_))), "{stopped:?}");
}

#[test]
fn an_array_that_is_the_value_of_a_plain_input_is_read_whole_with_a_chain_that_does_not_make_it_a_stream_of_them() {
    // §11.9, §11.3: an input at `sample` of the type `[F32; 2]` takes one array in each run, whatever it is run by; an array of `F32` is a value of the type of the input, not the burst of `F32`s that a call at `sample * 2` is.
    // `st` is `x[0] 10 + x[1]`: `st~([x, x + 1.0])` is 11 x + 1 (12, 23, 34 for x = 1, 2, 3), and `st~([p, p + 1.0]).down~(2)` (the array of the parameter kinds, read at the tick) is 11 p + 1 at the ticks c = 0, 2: p = 1
    // for the frames 0 and 1, 2 for 2 and 3: 12 12 23 23.
    let src = "flow st(x: [F32; 2] at sample) -> F32 at sample { x[0] * 10.0 + x[1] }
flow plain(x: F32 at sample) -> F32 at sample { st~([x, x + 1.0]) }
flow slow(p: F32 at block) -> F32 at sample { st~([p, p + 1.0]).down~(2) at sample }";
    same(&f32s(&run(src, "plain", vec![(vec![], 3)], &[("x", ramp(3))], &[])), &[12.0, 23.0, 34.0]);
    for cuts in [&[(2, 1.0), (2, 2.0)][..], &[(1, 1.0), (1, 1.0), (1, 2.0), (1, 2.0)]] {
        let calls = cuts.iter().map(|(n, v)| (p(*v), *n)).collect();
        same(&f32s(&run(src, "slow", calls, &[], &[])), &[12.0, 12.0, 23.0, 23.0]);
    }
}

/// The `[F32; 2]` outputs of a flow, flat: the two of each frame one after the other.
fn pairs(vs: &[Value]) -> Vec<f32> {
    vs.iter()
        .flat_map(|v| match v {
            Value::Array(es) => f32s(es),
            other => panic!("not an array of F32: {other:?}"),
        })
        .collect()
}

#[test]
fn a_gather_whose_argument_reads_an_arm_binding_keeps_the_ring_of_each_replica_with_the_binding_it_has_there() {
    // §11.9: the instance `sum2~(n).down~(2)` at the tick c gathers the values the argument had at c - 2 and c - 1 (`x[0] + 10 x[1]`), and §11.5: the replica `i` of a `par~` binds `n` of the arm of its `match~` to
    // `x + ks[i]` (`ks = [0, 1]`), so its ring is the stream `x + i`, not that of the replica that was run last. x[c] = c + 1: the tick c = 2 has frames 0, 1 (1 + k, 2 + k): 21 + 11 k = 21, 32; c = 4 frames 2, 3
    // (3 + k, 4 + k): 43 + 11 k = 43, 54; c = 6: 65 + 11 k = 65, 76; the tick c = 0 has no frame before: 0. Each is held for the 2 frames of a tick. The delay of the same form (`prev~(n)` is the `n` of the frame before:
    // x[c - 1] + k, 0 at the first frame) is 0 0 | 1 2 | 2 3 | 3 4 .. The part that is stateful in the object of the `match~` (`delay~(x, 2)` is `x[c - 2]`, 0 for the first two frames: with the arm bound to it the tick c = 4 has
    // the frames 2, 3 of it, 1 and 2: 1 + 20 = 21, and c = 6: 3 + 40 = 43) is saved once for each frame, or its ring would take two values for each: in a `par~` (+ k: 21, 32 and 43, 54) and alone. An arm with a guard
    // (`m` of the second, taken, arm is x: 0 0 21 21 43 43 65 65) and two arms inside one another (`m + n` = 2 x + 1: 3, 5 | 7, 9 | 11, 13: 3 + 50 = 53, 7 + 90 = 97, 141) are read with the arms around the call.
    let src = "flow sum2(x: F32 at (sample * 2)) -> F32 at sample { x[0] + x[1] * 10.0 }
flow plain(x: F32 at sample) -> [F32; 2] at sample {
  let ks = [0.0, 1.0]
  par~ i in 0 ..< 2 { match~ x + ks[i] { n => sum2~(n).down~(2) at sample } }
}
flow last(x: F32 at sample) -> [F32; 2] at sample {
  let ks = [0.0, 1.0]
  par~ i in 0 ..< 2 { match~ x + ks[i] { n => prev~(n) } }
}
flow staged(x: F32 at sample) -> [F32; 2] at sample {
  let ks = [0.0, 1.0]
  par~ i in 0 ..< 2 { match~ delay~(x + ks[i], 2) { n => sum2~(n).down~(2) at sample } }
}
flow single(x: F32 at sample) -> F32 at sample { match~ delay~(x, 2) { n => sum2~(n).down~(2) at sample } }
flow guarded(x: F32 at sample) -> F32 at sample { match~ x { n if n > 100.0 => 0.0, m => sum2~(m).down~(2) at sample } }
flow nested(x: F32 at sample) -> F32 at sample { match~ x { n => match~ n + 1.0 { m => sum2~(m + n).down~(2) at sample } } }";
    let held = |ps: &[[f32; 2]], n: usize| ps.iter().flat_map(|p| p.repeat(n)).collect::<Vec<f32>>();
    for sizes in [&[8][..], &[3, 5], &[1; 8], &[2, 0, 6]] {
        let calls = || sizes.iter().map(|n| (vec![], *n)).collect::<Vec<_>>();
        let out = |name: &'static str| run(src, name, calls(), &[("x", ramp(8))], &[]);
        same(&pairs(&out("plain")), &held(&[[0.0, 0.0], [21.0, 32.0], [43.0, 54.0], [65.0, 76.0]], 2));
        let delays = [[0.0, 0.0], [1.0, 2.0], [2.0, 3.0], [3.0, 4.0], [4.0, 5.0], [5.0, 6.0], [6.0, 7.0], [7.0, 8.0]];
        same(&pairs(&out("last")), &held(&delays, 1));
        same(&pairs(&out("staged")), &held(&[[0.0, 0.0], [0.0, 0.0], [21.0, 32.0], [43.0, 54.0]], 2));
        same(&f32s(&out("single")), &[0.0, 0.0, 0.0, 0.0, 21.0, 21.0, 43.0, 43.0]);
        same(&f32s(&out("guarded")), &[0.0, 0.0, 21.0, 21.0, 43.0, 43.0, 65.0, 65.0]);
        same(&f32s(&out("nested")), &[0.0, 0.0, 53.0, 53.0, 97.0, 97.0, 141.0, 141.0]);
    }
}

#[test]
fn an_input_at_sample_times_n_of_more_elements_than_the_evaluator_holds_is_unavailable_before_its_elements_are_made() {
    // §11.9: the input at `sample * N` of a call that no chain slows is N elements of the argument in each frame. The evaluator holds `Limits::most` (2^20) places and stops (`Unavailable`) at more, and does not make the
    // 2^21 or the 2^31 elements first (`x: F32 at (sample * 2147483648)` is a declaration the check passes: S-1089). One at the limit is made: the 2^20 elements of `p`, `x[0]` is `p` = 1. The ring that a gathering chain
    // keeps for the same declaration (`.down~(2)`: 2^31 elements of a window) is stopped at `init`, as it is made there.
    let src = "flow at_20(x: F32 at (sample * 1048576)) -> F32 at sample { x[0] }
flow at_21(x: F32 at (sample * 2097152)) -> F32 at sample { x[0] }
flow at_31(x: F32 at (sample * 2147483648)) -> F32 at sample { x[0] }
flow t20(p: F32 at block) -> F32 at sample { at_20~(p) }
flow t21(p: F32 at block) -> F32 at sample { at_21~(p) }
flow t31(p: F32 at block) -> F32 at sample { at_31~(p) }
flow g31(p: F32 at block) -> F32 at sample { at_31~(p).down~(2) at sample }";
    same(&f32s(&run(src, "t20", vec![(p(1.0), 2)], &[], &[])), &[1.0, 1.0]);
    let stopped = |name: &'static str| {
        with_checked(src, true, move |a| {
            let mut me = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).map_err(|s| s.fault)?;
            me.process(&p(1.0), &[], 1, None).map(|_| ()).map_err(|s| s.fault)
        })
    };
    for name in ["t21", "t31", "g31"] {
        assert!(matches!(stopped(name), Err(Fault::Unavailable(_))), "{name}: {:?}", stopped(name));
    }
}

#[test]
fn a_chain_that_deals_in_a_par_deals_the_array_of_each_replica_to_the_frames_after_its_tick() {
    // §11.9, §11.5: the output at `sample * 2` of `dl~(ks[i]).down~(2)` is the array `[2 n + 1 + w, 2 n + 2 + w]` of the run n (the counter `cnt` of the instance is n + 1 at its n-th run), the frames 2 n and 2 n + 1 read its
    // elements 0 and 1, and each replica of the `par~` has the array it dealt, with `w = ks[i]` (0, 100) its own: the frame e reads `e + 1 + w`: [1, 101], [2, 102], .. [8, 108].
    let src = "flow dl(w: F32 at block) -> F32 at (sample * 2) {
  let cnt = prev~(^cnt) + 1.0
  [cnt * 2.0 - 1.0 + w, cnt * 2.0 + w]
}
flow t(x: F32 at sample) -> [F32; 2] at sample {
  let ks = [0.0, 100.0]
  par~ i in 0 ..< 2 { dl~(ks[i]).down~(2) }
}";
    let want: Vec<f32> = (1..=8).flat_map(|e| [e as f32, e as f32 + 100.0]).collect();
    for sizes in [&[8][..], &[3, 5], &[1; 8], &[2, 0, 6]] {
        let calls = sizes.iter().map(|n| (vec![], *n)).collect();
        same(&pairs(&run(src, "t", calls, &[("x", ramp(8))], &[])), &want);
    }
}

#[test]
fn the_product_of_three_nested_chains_is_the_product_of_all_three_and_not_of_the_last_two() {
    // §11.9: "入れ子の比の積は 2^24 以内". `.up~(512)` three deep is 2^27 (each two of them 2^18 are within), `.up~(4096)` three deep 2^36: the evaluator stops them at `init` (`Unavailable`), where the instance that
    // makes the third is made, and does not round the product; `.up~(256)` three deep is 2^24 and is made (the same product of 2^11 inside 2^13 is made in the test of the limit). `.down~(4096)` inside `.down~(4096)`, a product of
    // 2^-24 and no more (S-1089: the evaluator holds the size of the product, a slower one too), is made too, and its tick at c = 0 reads `p`: 1 1.
    let up = |n: u32| {
        format!(
            "flow leaf(q: F32 at sample) -> F32 at sample {{ q }}
flow mid(p: F32 at block) -> F32 at sample {{ let _ = leaf~(p).up~({n})
  0.0 }}
flow top(p: F32 at block) -> F32 at sample {{ let _ = mid~(p).up~({n})
  0.0 }}
flow t(p: F32 at block) -> F32 at sample {{ let _ = top~(p).up~({n})
  0.0 }}"
        )
    };
    let made = |src: String| {
        with_checked(&src, true, move |a| {
            Instance::init(View::new(a), def_named(a, "t"), 48000.0, &[], None).map(|_| ()).map_err(|s| s.fault)
        })
    };
    assert!(made(up(256)).is_ok());
    for n in [512, 4096] {
        let got = made(up(n));
        assert!(matches!(got, Err(Fault::Unavailable(_))), "{n}: {got:?}");
    }
    let src = "flow leaf(x: F32 at sample) -> F32 at sample { x }
flow mid(x: F32 at (sample / 4096)) -> F32 at sample { leaf~(x).down~(4096) at sample }
flow t(p: F32 at block) -> F32 at sample { mid~(p).down~(4096) at sample }";
    same(&f32s(&run(src, "t", vec![(p(1.0), 2)], &[], &[])), &[1.0, 1.0]);
}

#[test]
fn the_clock_of_the_largest_power_of_two_of_a_u32_is_made_and_ticks_once_in_the_frames_of_a_run() {
    // §11.3: `p at (sample / 2147483648)` ticks once in 2^31 frames, the first at the frame 0 (the counter is 0, §11.9). Its delay `prev~(.., 0.0)` has the `0.0` it starts from there, so `n` is 1 and holds for
    // the frames that follow: 1 1 1. The N is the largest power of 2 a `U32` holds (2^31); one smaller has the same value, with a tick of its own.
    // SPEC-GAP(S-1089): the spec does not say the most of the N of a clock `sample / N`; the evaluator takes the one of a `U32` (the ratio is held in an `i32`).
    let src = "flow big(p: F32 at block) -> F32 at sample {
  let n = prev~(p at (sample / 2147483648), 0.0) + 1.0
  n at sample
}
flow less(p: F32 at block) -> F32 at sample {
  let n = prev~(p at (sample / 1073741824), 0.0) + 1.0
  n at sample
}";
    for name in ["big", "less"] {
        same(&f32s(&run(src, name, vec![(p(5.0), 3)], &[], &[])), &[1.0, 1.0, 1.0]);
    }
}

#[test]
fn the_index_of_a_par_is_the_index_of_the_replica_in_the_block_input_and_in_the_ring_of_a_gather_that_read_it_by_name()
{
    // §11.5: in the replica `i` of a `par~` the name `i` is its index (0, 1), for the call that reads it at `block` (`g~(i)` is `i + 5`: 5, 6 in every frame) and for the ring a `.down~(2)` call keeps of the stream `i`, a
    // value of the parameter kinds that the call gathers as it is (`s~(i).down~(2)` sums `x[0] + 10 x[1]` of the 2 elements before the tick: 0 for the first tick c = 0, then 11 i, and the next ticks are the same
    // 11 i): [0, 0] for the frames 0 and 1, [0, 11] for the others. `match~ i { j => .. }` gives the arm the index too: the same.
    let src = "flow g(w: U32 at block) -> U32 at sample { w + 5 }
flow s(x: U32 at (sample * 2)) -> U32 at sample { x[0] + x[1] * 10 }
flow block_index(x: F32 at sample) -> [U32; 2] at sample { par~ i in 0 ..< 2 { g~(i) } }
flow ring_index(x: F32 at sample) -> [U32; 2] at sample { par~ i in 0 ..< 2 { s~(i).down~(2) at sample } }
flow arm_index(x: F32 at sample) -> [U32; 2] at sample { par~ i in 0 ..< 2 { match~ i { j => s~(j).down~(2) at sample } } }";
    let ints = |name: &'static str| -> Vec<i128> {
        let calls = vec![(vec![], 3), (vec![], 5)];
        let out = run(src, name, calls, &[("x", ramp(8))], &[]);
        let one = |v: &Value| match v {
            Value::Int(_, n, _) => *n,
            other => panic!("not an integer: {other:?}"),
        };
        out.iter()
            .flat_map(|v| match v {
                Value::Array(es) => es.iter().map(one).collect::<Vec<_>>(),
                other => panic!("not an array: {other:?}"),
            })
            .collect()
    };
    assert_eq!(ints("block_index"), [5, 6].repeat(8));
    let rings: Vec<i128> = [[0, 0]; 2].into_iter().chain([[0, 11]; 6]).flatten().collect();
    assert_eq!(ints("ring_index"), rings);
    assert_eq!(ints("arm_index"), rings);
}
