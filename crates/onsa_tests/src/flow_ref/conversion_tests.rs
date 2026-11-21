//! The tests of the conversion flows of the evaluator (W7-09 U2b): the ports at `sample * N` and `sample / N` (§11.9), what a `.down~(N)` chain gathers and deals
//! (position c gathers c - N .. c - 1, the frames c .. c + N - 1 read the array dealt, position 0 has `T.default()`), an `.up~(N)` chain that passes its N values as an
//! array, the ticks of an instance with no modifier whose ports are ticks (S-1088), and a loop through two `let`s that a tick enters (§11.3). The values are worked out by
//! hand from the spec, in the comment of each test. In every flow of a column `x` the frame c has the value `c + 1` unless said otherwise, so the values a tick gathers
//! are the ones of the frames before it (the frame c = 0 has 0 for all of them: `T.default()`).

use super::expr::Frame;
use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::scalar::Fault;
use super::sema_view::View;
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
fn a_call_at_sample_times_n_has_n_values_of_the_type_of_one_and_nothing_else_is_taken_for_it() {
    // §11.9: the table gives the call `ramp4~(p).down~(2)`, a value of `sample * 2` in the caller's frame, the type of one value (`F32`), and its value is the array of its 2 values, each an `F32`. An array
    // of another length or of elements of another type, one value that is no array, and an array for a call whose clock is `sample` (`sum2~(...)`) are not the value of such a call.
    let src = format!(
        "{CONV}flow sum2(x: F32 at (sample * 2)) -> F32 at sample {{ x[0] + x[1] }}
flow t(p: F32 at block) -> F32 at sample {{
  let r = ramp4~(p).down~(2)
  let s = sum2~(r)
  s
}}"
    );
    let (f, b) = (|x: f32| Value::F32(x), Value::Bool(true));
    let arr = |vs: Vec<Value>| Value::Array(vs);
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
        let frame = Frame::new(body);
        let ask = |n: usize, v: &Value| frame.sample_times(init(n), v).expect("the table is whole");
        [
            ask(0, &arr(vec![f(1.0), f(2.0)])),
            ask(0, &arr(vec![f(1.0), f(2.0), f(3.0)])),
            ask(0, &arr(vec![f(1.0)])),
            ask(0, &arr(vec![f(1.0), b])),
            ask(0, &f(1.0)),
            ask(1, &arr(vec![f(1.0), f(2.0)])),
            ask(1, &arr(vec![f(1.0)])),
        ]
    });
    assert_eq!(got, [true, false, false, false, false, false, false]);
}

#[test]
fn a_port_that_no_chain_reads_in_the_frame_of_its_caller_has_no_value_here() {
    // §11.9 says no frame of the caller to read an input of `sample * 2` of `.down~(4)` (the caller's `sample / 2`: one value in two frames, which is no sample of the instance's `sample * 2`)
    // nor an output of `sample * 2` of `.down~(4)` (the same), so the evaluator stops with `Unavailable` at `init` and does not guess.
    let src = format!(
        "{CONV}flow sum2(x: F32 at (sample * 2)) -> F32 at sample {{ x[0] + x[1] }}
flow hold2(q: F32 at sample) -> F32 at (sample * 2) {{ [q, q + 1.0] }}
flow out(p: F32 at block) -> F32 at sample {{
  let _ = hold2~(p).down~(4)
  0.0
}}
flow inp(p: F32 at block) -> F32 at sample {{
  let _ = sum2~(p at (sample / 2)).down~(4)
  0.0
}}"
    );
    for name in ["out", "inp"] {
        let stopped =
            with_checked(&src, true, |a| Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None).err());
        assert!(matches!(stopped.map(|s| s.fault), Some(Fault::Unavailable(_))), "{name}");
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
