//! The tests of the delays and of `^` (W7-18 U1b): `prev~`, `delay~` and `vdelay~` by the formulas of §11.4, the two
//! phases of a tick (§11.4: the delays read before anything is stored; `^name` of §11.2), the clock a delay ticks with
//! (§11.3, §11.4), `init` and its default (§11.4, §6.4) and a run in pieces (§11.6). The values are worked out by hand
//! from the spec, in the comment of each test (a few of the sequences are those of `tests/spec/flow_semantics/`, which
//! were worked out the same way).

use onsa_sema::DefId;

use super::expr::LIMITS;
use super::expr::Stop;
use super::expr_tests::{def_named, i32v, panic_at, with_checked};
use super::flow::{Clock, Instance};
use super::flow_tests::{counted, counter, host, init_stop, with_flow};
use super::host::TableHost;
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::value::Value;

use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

pub(super) fn floats(xs: &[f32]) -> Vec<Value> {
    xs.iter().map(|x| Value::F32(*x)).collect()
}

/// The outputs of the flow `name` for the columns `cols` (by name), the inputs of `init` and the `block` ones given, in
/// calls of `calls` frames each (a call takes the next frames of every column; the sum of `calls` is their length).
/// `clean` is false for a source that has diagnostics of this version's check (E0200 of a form the spec has: a delay in
/// the first argument of a delay, an omitted `init` of a type that is not a number, a delay length that is a constant
/// expression and not a literal): the evaluator has the form, and its tables are whole, so it runs.
pub(super) fn run_with(
    clean: bool,
    src: &str,
    name: &'static str,
    config: Vec<(&'static str, Value)>,
    params: Vec<(&'static str, Value)>,
    cols: Vec<(&'static str, Vec<Value>)>,
    calls: Vec<usize>,
) -> Vec<Value> {
    with_checked(src, clean, move |a| {
        let (view, def) = (View::new(a), def_named(a, name));
        let mut me = Instance::init(view, def, 48000.0, &config, None).expect("init");
        let (mut outs, mut at) = (Vec::new(), 0);
        for n in calls {
            let ins: Vec<(&str, &[Value])> = cols.iter().map(|(c, v)| (*c, &v[at..at + n])).collect();
            outs.extend(me.process(&params, &ins, n, None).expect("process"));
            at += n;
        }
        outs
    })
}

pub(super) fn run(
    src: &str,
    name: &'static str,
    config: Vec<(&'static str, Value)>,
    params: Vec<(&'static str, Value)>,
    cols: Vec<(&'static str, Vec<Value>)>,
    calls: Vec<usize>,
) -> Vec<Value> {
    run_with(true, src, name, config, params, cols, calls)
}

/// A flow with the one input `x` at `sample`, run in one call (`go_open`: of a source with diagnostics, see `run_with`).
pub(super) fn go(src: &str, name: &'static str, xs: &[f32]) -> Vec<f32> {
    f32s(&run(src, name, vec![], vec![], vec![("x", floats(xs))], vec![xs.len()]))
}

pub(super) fn go_open(src: &str, name: &'static str, xs: &[f32]) -> Vec<f32> {
    f32s(&run_with(false, src, name, vec![], vec![], vec![("x", floats(xs))], vec![xs.len()]))
}

pub(super) fn f32s(vs: &[Value]) -> Vec<f32> {
    vs.iter().map(|v| if let Value::F32(x) = v { *x } else { panic!("not an F32: {v:?}") }).collect()
}

/// The same bits (a NaN is the same as any NaN), so that `-0.0` and `0.0` differ.
pub(super) fn same(got: &[f32], want: &[f32]) {
    let eq = |a: &f32, b: &f32| a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan());
    assert!(got.len() == want.len() && got.iter().zip(want).all(|(a, b)| eq(a, b)), "got {got:?}, want {want:?}");
}

#[test]
fn prev_gives_the_value_of_the_last_tick_and_starts_from_init() {
    // §11.4: out[0] = init, out[n] = e[n - 1]. `init` omitted is `+0.0`; a literal; `-0.0` (only an explicit one starts at
    // `-0.0`, §11.4); an input of `init` and an expression of it (4.0 * 2.0 + 1.0 = 9.0).
    let src = "flow one(x: F32 at sample) -> F32 at sample { prev~(x) }
flow lit(x: F32 at sample) -> F32 at sample { prev~(x, 5.0) }
flow neg(x: F32 at sample) -> F32 at sample { prev~(x, -0.0) }
flow cfg(x: F32 at sample, s: F32 at init) -> F32 at sample { prev~(x, s * 2.0 + 1.0) }";
    let xs = [1.0, 2.0, 3.0, 4.0];
    same(&go(src, "one", &xs), &[0.0, 1.0, 2.0, 3.0]);
    same(&go(src, "lit", &xs), &[5.0, 1.0, 2.0, 3.0]);
    same(&go(src, "neg", &xs), &[-0.0, 1.0, 2.0, 3.0]);
    let outs = run(src, "cfg", vec![("s", Value::F32(4.0))], vec![], vec![("x", floats(&xs))], vec![4]);
    same(&f32s(&outs), &[9.0, 1.0, 2.0, 3.0]);
    // An integer signal: the default is 0.
    let src = "flow i(x: I32 at sample) -> I32 at sample { prev~(x) }";
    let outs = run(src, "i", vec![], vec![], vec![("x", vec![i32v(5), i32v(6), i32v(7)])], vec![3]);
    assert!(outs.iter().zip([0, 5, 6]).all(|(o, w)| o.same(&i32v(w))), "{outs:?}");
}

#[test]
fn delay_by_n_gives_the_value_of_n_ticks_ago_and_the_ring_goes_round() {
    // §11.4: out[n] = e[n - N], the first N outputs are init, w = (w + 1) % N. N = 2 with no init; N = 3 with init 9.0,
    // 8 ticks (the ring goes round twice and more); N a `const` of 3; init of the `init` clock; N = 2, 7 ticks.
    let src = "const N: U32 = 3
flow two(x: F32 at sample) -> F32 at sample { delay~(x, 2) }
flow three(x: F32 at sample) -> F32 at sample { delay~(x, 3, 9.0) }
flow named(x: F32 at sample) -> F32 at sample { delay~(x, N, 9.0) }
flow cfg(x: F32 at sample, s: F32 at init) -> F32 at sample { delay~(x, 2, s) }";
    same(&go(src, "two", &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), &[0.0, 0.0, 1.0, 2.0, 3.0, 4.0]);
    let eight = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    let want = [9.0, 9.0, 9.0, 1.0, 2.0, 3.0, 4.0, 5.0];
    same(&go(src, "three", &eight), &want);
    same(&go(src, "named", &eight), &want);
    let outs = run(src, "cfg", vec![("s", Value::F32(4.0))], vec![], vec![("x", floats(&[1.0, 2.0, 3.0]))], vec![3]);
    assert!(outs.iter().zip([4.0, 4.0, 1.0]).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
}

#[test]
#[ignore = "W9-03: the check gives E0200 to the length of a delay that is a constant expression and not a literal"]
fn the_length_of_a_delay_is_a_constant_expression() {
    // §11.4: `N` and `MAX` are constant expressions (§4.5): `K = 1 + 2` is 3, so out[n] = x[n-3] and the first 3 are init.
    let src = "const K: U32 = 1 + 2
flow ck(x: F32 at sample) -> F32 at sample { delay~(x, K, 9.0) }
flow vk(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, K + 1, 9.0) }";
    let six = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
    same(&go_open(src, "ck", &six), &[9.0, 9.0, 9.0, 1.0, 2.0, 3.0]);
    // MAX = 4, d = 4: the first four outputs are init, then x[n-4].
    let outs = run_with(false, src, "vk", vec![], vec![("d", Value::F32(4.0))], vec![("x", floats(&six))], vec![6]);
    same(&f32s(&outs), &[9.0, 9.0, 9.0, 9.0, 1.0, 2.0]);
}

#[test]
fn delays_in_what_a_delay_stores_read_before_anything_is_stored() {
    // §11.4: "the delays inside `e` read the output before the store": a delay of a delay is two ticks late.
    // `p = prev~(x)` and `prev~(p)`: x[n-2], x = 1 2 3 4: 0 0 1 2. `delay~(p, 2)` over x = 1..5: p = 0 1 2 3 4,
    // out[n] = p[n-2]: 0 0 0 1 2. `q = prev~(x, 7.0)` and `prev~(q, 9.0)`: out[n] = q[n-1], q[n] = x[n-1] with q[0] = 7:
    // 9, 7, x0, x1 = 9 7 1 2. The two calls of `prev~(x, ..)` in the last flow each have a state (init 1.0 and 2.0):
    // 1 + 2 = 3, then 2 * x0 = 20, then 2 * x1 = 40.
    let src = "flow pl(x: F32 at sample) -> F32 at sample {
  let p = prev~(x)
  prev~(p)
}
flow dp(x: F32 at sample) -> F32 at sample {
  let p = prev~(x)
  delay~(p, 2)
}
flow pi(x: F32 at sample) -> F32 at sample {
  let q = prev~(x, 7.0)
  prev~(q, 9.0)
}
flow two(x: F32 at sample) -> F32 at sample { prev~(x, 1.0) + prev~(x, 2.0) }";
    same(&go(src, "pl", &[1.0, 2.0, 3.0, 4.0]), &[0.0, 0.0, 1.0, 2.0]);
    same(&go(src, "dp", &[1.0, 2.0, 3.0, 4.0, 5.0]), &[0.0, 0.0, 0.0, 1.0, 2.0]);
    same(&go(src, "pi", &[1.0, 2.0, 3.0, 4.0]), &[9.0, 7.0, 1.0, 2.0]);
    same(&go(src, "two", &[10.0, 20.0, 30.0]), &[3.0, 20.0, 40.0]);
}

#[test]
#[ignore = "W7-07: the check gives E0200 to a delay inside the first argument of a delay and leaves the tables of the body whole not"]
fn a_delay_written_inside_the_first_argument_of_a_delay_is_the_same_as_one_bound_by_a_let() {
    // §11.4: `prev~(prev~(x))` is `x[n-2]`, the same as `let p = prev~(x)` and `prev~(p)` (the test before). The inner
    // delay is evaluated in the second phase, where what the outer one stores is, so the second phase evaluates what
    // the delays found there save too. x = 1 2 3 4: `prev~(prev~(x))` 0 0 1 2; `prev~(prev~(x, 7.0), 9.0)` 9 7 1 2;
    // `delay~(prev~(x), 2)` over x = 1..5: 0 0 0 1 2. `prev~(x) + prev~(prev~(x) + 1.0)`: A = `prev~(x)` is 0 1 2, and
    // C = `prev~(prev~(x) + 1.0)` is (the inner `prev~(x)` of the tick before) + 1, from 0: 0, 0 + 1, 1 + 1 = 0 1 2:
    // A + C = 0 2 4.
    let src = "flow pp(x: F32 at sample) -> F32 at sample { prev~(prev~(x)) }
flow pi(x: F32 at sample) -> F32 at sample { prev~(prev~(x, 7.0), 9.0) }
flow dp(x: F32 at sample) -> F32 at sample { delay~(prev~(x), 2) }
flow m(x: F32 at sample) -> F32 at sample { prev~(x) + prev~(prev~(x) + 1.0) }";
    same(&go_open(src, "pp", &[1.0, 2.0, 3.0, 4.0]), &[0.0, 0.0, 1.0, 2.0]);
    same(&go_open(src, "pi", &[1.0, 2.0, 3.0, 4.0]), &[9.0, 7.0, 1.0, 2.0]);
    same(&go_open(src, "dp", &[1.0, 2.0, 3.0, 4.0, 5.0]), &[0.0, 0.0, 0.0, 1.0, 2.0]);
    same(&go_open(src, "m", &[1.0, 2.0, 3.0]), &[0.0, 2.0, 4.0]);
}

#[test]
fn two_delays_that_read_each_other_see_the_old_values() {
    // §11.4 (all the outputs are read first, then all stored), §11.2 (`^b` is the `b` of this tick, read to be stored):
    // `a = prev~(^b, 1.0)`, `b = prev~(a, 2.0)`: a[n] = b[n-1], b[n] = a[n-1], from a = 1 and b = 2.
    // a: 1 2 1 2 1, b: 2 1 2 1 2, so `a * 10 + b` is 12 21 12 21 12. No input: 5 frames of nothing.
    let src = "flow swap() -> F32 at sample {
  let a = prev~(^b, 1.0)
  let b = prev~(a, 2.0)
  a * 10.0 + b
}";
    let outs = run(src, "swap", vec![], vec![], vec![], vec![5]);
    assert!(outs.iter().zip([12.0, 21.0, 12.0, 21.0, 12.0]).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
}

#[test]
fn a_feedback_reference_is_read_at_the_end_of_the_tick_it_is_stored_in() {
    // §11.2, §11.4: `prev~(^y)` is y[n-1]. A running sum `y = x + prev~(^y)`: 1 3 6 10 for x = 1 2 3 4. A product
    // `g = prev~(^g, 1.0) * 2.0`: g[n] = 2 * g[n-1] from g[-1] = 1: 2 4 8 16. A counter `c = prev~(^c) + 1` of integers: 1 2 3 4.
    // The lowpass `y = 0.5 * x + 0.5 * prev~(^y)` for x = 1 0 0 0: .5 .25 .125 .0625.
    let src = "flow sum(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
flow prod() -> F32 at sample {
  let g = prev~(^g, 1.0) * 2.0
  g
}
flow count() -> I32 at sample {
  let c: I32 = prev~(^c) + 1
  c
}
flow lp(x: F32 at sample) -> F32 at sample {
  let y = 0.5 * x + 0.5 * prev~(^y)
  y
}";
    same(&go(src, "sum", &[1.0, 2.0, 3.0, 4.0]), &[1.0, 3.0, 6.0, 10.0]);
    same(&go(src, "lp", &[1.0, 0.0, 0.0, 0.0]), &[0.5, 0.25, 0.125, 0.0625]);
    let outs = run(src, "prod", vec![], vec![], vec![], vec![4]);
    assert!(outs.iter().zip([2.0, 4.0, 8.0, 16.0]).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
    let outs = run(src, "count", vec![], vec![], vec![], vec![4]);
    assert!(outs.iter().zip([1, 2, 3, 4]).all(|(o, w)| o.same(&i32v(w))), "{outs:?}");
}

#[test]
fn a_one_pole_reads_the_block_parameter_of_each_call() {
    // §11.2: `y = (1 - p) * x + p * prev~(^y)`; x = 1 1 | 1 1, p = 0.5 then 0.25 (all exact in an `F32`).
    // p = 0.5: y0 = 0.5, y1 = 0.5 + 0.5 * 0.5 = 0.75. p = 0.25: y2 = 0.75 + 0.25 * 0.75 = 0.9375, y3 = 0.75 + 0.25 * 0.9375
    // = 0.984375. The call of 0 frames between them changes nothing (no tick, no store).
    let src = "flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let y = (1.0 - p) * x + p * prev~(^y)
  y
}";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let one = floats(&[1.0, 1.0]);
        let a = me.process(&[("p", Value::F32(0.5))], &[("x", &one[..])], 2, None).expect("process");
        let z = me.process(&[("p", Value::F32(0.1))], &[("x", &[])], 0, None).expect("process");
        let b = me.process(&[("p", Value::F32(0.25))], &[("x", &one[..])], 2, None).expect("process");
        let outs: Vec<Value> = a.into_iter().chain(b).collect();
        assert!(z.is_empty() && me.ctx.tick == 4);
        assert!(outs.iter().zip([0.5, 0.75, 0.9375, 0.984375]).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
    });
}

#[test]
fn a_delay_ticks_with_the_clock_of_its_first_argument_which_is_sample_here() {
    // §11.3, §11.4: the result of a delay has the clock of its first argument, and a first argument that is of `block`
    // is `p at sample` (a name that decides nothing is read as `sample`: `^c`, a constant). So each of these `let`s is of
    // `sample` and ticks for each frame, not for each call: `ps = p at sample`, `a = prev~(ps)`, `b = prev~(p at sample)`,
    // `c = prev~(^c, 1.0)`, and the output `a + b` too.
    let src = "flow f(p: F32 at block) -> F32 at sample {
  let ps = p at sample
  let a = prev~(ps)
  let b = prev~(p at sample, 9.0)
  let c: F32 = prev~(^c, 1.0)
  a + b
}";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Sample; 5]);
        // Call 1: p = 1, 2 frames: a = 0, 1; b = 9, 1. Call 2: p = 2, 2 frames: a = 1, 2; b = 1, 2.
        // Call 3, 0 frames, p = 5: nothing. Call 4: p = 3, 1 frame: a = 2, b = 2.
        let mut outs = Vec::new();
        for (p, n) in [(1.0, 2), (2.0, 2), (5.0, 0), (3.0, 1)] {
            outs.extend(me.process(&[("p", Value::F32(p))], &[], n, None).expect("process"));
        }
        assert!(outs.iter().zip([9.0, 2.0, 2.0, 4.0, 4.0]).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
        assert_eq!(me.ctx.tick, 5);
    });
    // The output of an instance is of the clock the instance runs at (U1c), so is the output `prev~(x) * k`: the fastest.
    let src = "flow g(k: F32 at block, x: F32 at sample) -> F32 at sample {
  let a = k * 2.0
  let d = prev~(x)
  d * a
}";
    with_flow(src, "g", |view, def| {
        let me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Block, Clock::Sample, Clock::Sample]);
    });
}

#[test]
fn the_result_of_a_delay_of_a_name_bound_later_is_made_for_each_frame() {
    // `let y = x + prev~(^y)`: the first argument `^y` has the clock of nothing, `x` is `sample`; `prev~(^w)` alone is
    // of `sample` too (the body's `sample`), so a frame with no input still ticks it: the counter of 3 frames is 1 2 3.
    let src = "flow cnt() -> I32 at sample {
  let w: I32 = prev~(^w) + 1
  w
}";
    with_flow(src, "cnt", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Sample, Clock::Sample]);
        let outs = me.process(&[], &[], 3, None).expect("process");
        assert!(outs.iter().zip([1, 2, 3]).all(|(o, w)| o.same(&i32v(w))), "{outs:?}");
    });
}

#[test]
fn vdelay_interpolates_between_two_ticks_as_the_formula_has_it() {
    // §11.4: with L = MAX + 1, k = trunc(dc), f = dc - k, y = (1 - f) * e[n-k] + f * e[n-k-1] (before the store).
    // MAX = 4. x = 1..6, so e[m] = m + 1 and e[m] = 0 before the start.
    //   d = 2   (k 2, f 0):    out[n] = x[n-2]:                         0 0 1 2 3 4
    //   d = 1   (k 1, f 0):    out[n] = x[n-1]:                         0 1 2 3 4 5
    //   d = 1.5 (k 1, f .5):   .5 * x[n-1] + .5 * x[n-2]:              0 .5 1.5 2.5 3.5 4.5
    //   d = 2.25 (k 2, f .25): .75 * x[n-2] + .25 * x[n-3]:            0 0 .75 1.75 2.75 3.75
    // x = 2 4 6 8 10 12, d = 3.5 (k 3, f .5): .5 * x[n-3] + .5 * x[n-4]: 0 0 0 1 3 5.
    // x = 16 32 .. 112, d = 3.9375 (k 3, f .9375): .0625 * x[n-3] + .9375 * x[n-4]: 0 0 0 1 17 33 49.
    let src = "flow vd(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 4) }";
    let at = |d: f32, xs: &[f32]| {
        let outs = run(src, "vd", vec![], vec![("d", Value::F32(d))], vec![("x", floats(xs))], vec![xs.len()]);
        f32s(&outs)
    };
    let six = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
    same(&at(2.0, &six), &[0.0, 0.0, 1.0, 2.0, 3.0, 4.0]);
    same(&at(1.0, &six), &[0.0, 1.0, 2.0, 3.0, 4.0, 5.0]);
    same(&at(1.5, &six), &[0.0, 0.5, 1.5, 2.5, 3.5, 4.5]);
    same(&at(2.25, &six), &[0.0, 0.0, 0.75, 1.75, 2.75, 3.75]);
    same(&at(3.5, &[2.0, 4.0, 6.0, 8.0, 10.0, 12.0]), &[0.0, 0.0, 0.0, 1.0, 3.0, 5.0]);
    same(&at(3.9375, &[16.0, 32.0, 48.0, 64.0, 80.0, 96.0, 112.0]), &[0.0, 0.0, 0.0, 1.0, 17.0, 33.0, 49.0]);
}

#[test]
fn vdelay_goes_round_its_ring_and_starts_from_init() {
    // §11.4: the ring has MAX + 1 places. MAX = 3, d = 3 (k 3, f 0), 12 ticks: out[n] = x[n-3], 3 rounds of 4 places.
    // init 9.0, MAX = 4: d = 2: 9 9 1 2 3. d = 1.5 over x = 1 2 3: n0: .5 * 9 + .5 * 9 = 9; n1: .5 * x0 + .5 * 9 = 5;
    // n2: .5 * x1 + .5 * x0 = 1.5. d = 4 (= MAX, k 4, f 0) over x = 1..6: the first four outputs are init: 9 9 9 9 1 2.
    let src = "flow vd3(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 3) }
flow vi(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 4, 9.0) }";
    let at = |name: &'static str, d: f32, xs: &[f32]| {
        let outs = run(src, name, vec![], vec![("d", Value::F32(d))], vec![("x", floats(xs))], vec![xs.len()]);
        f32s(&outs)
    };
    let twelve: Vec<f32> = (1..=12).map(|n| n as f32).collect();
    same(&at("vd3", 3.0, &twelve), &[0.0, 0.0, 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]);
    same(&at("vi", 2.0, &[1.0, 2.0, 3.0, 4.0, 5.0]), &[9.0, 9.0, 1.0, 2.0, 3.0]);
    same(&at("vi", 1.5, &[1.0, 2.0, 3.0]), &[9.0, 5.0, 1.5]);
    same(&at("vi", 4.0, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), &[9.0, 9.0, 9.0, 9.0, 1.0, 2.0]);
}

#[test]
fn vdelay_saturates_d_to_one_and_max_and_a_nan_is_one() {
    // §11.4: dc = d >= 1 ? (d <= MAX ? d : MAX) : 1, so a d under 1 (0.5, 0, -0.0, -3, -inf), a NaN is `prev~`
    // (0 1 2 3 for x = 1 2 3 4), and a d over MAX (4.5, 100, inf) is a delay of MAX = 4 (0 0 0 0 1 2 3 4 for x = 1..8);
    // MAX = 1: a d of 0.5 and of 5.0 are one tick (0 1 2 3 4); an `F64` signal the same as an `F32` one: d = 1.5: 0 .5 1.5 2.5.
    let src = "flow vd(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 4) }
flow v1(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 1) }
flow v64(x: F64 at sample, d: F64 at block) -> F64 at sample { vdelay~(x, d, 4) }";
    let at = |name: &'static str, d: f32, xs: &[f32]| {
        let outs = run(src, name, vec![], vec![("d", Value::F32(d))], vec![("x", floats(xs))], vec![xs.len()]);
        f32s(&outs)
    };
    for d in [1.0, 0.5, 0.0, -0.0, -3.0, f32::NEG_INFINITY, f32::NAN] {
        same(&at("vd", d, &[1.0, 2.0, 3.0, 4.0]), &[0.0, 1.0, 2.0, 3.0]);
    }
    let eight = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    for d in [4.0, 4.5, 100.0, f32::INFINITY] {
        same(&at("vd", d, &eight), &[0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0, 4.0]);
    }
    for d in [0.5, 5.0] {
        same(&at("v1", d, &[1.0, 2.0, 3.0, 4.0, 5.0]), &[0.0, 1.0, 2.0, 3.0, 4.0]);
    }
    let xs = (0..4).map(|n| Value::F64(f64::from(n + 1))).collect();
    let outs = run(src, "v64", vec![], vec![("d", Value::F64(1.5))], vec![("x", xs)], vec![4]);
    assert!(outs.iter().zip([0.0, 0.5, 1.5, 2.5]).all(|(o, w)| o.same(&Value::F64(w))), "{outs:?}");
}

#[test]
fn vdelay_reads_a_d_that_changes_each_tick_and_a_delay_in_it() {
    // §11.4: `d` is read at each tick. MAX = 4, x = 1..6 (e[m] = m + 1, 0 before), d = 1 2 3 2 1 1.5:
    // n0: k1 a e[-1] = 0; n1: k2 a e[-1] = 0; n2: k3 a e[-1] = 0; n3: k2 f0 a e[1] = 2; n4: k1 a e[3] = 4;
    // n5: k1 f.5: .5 * e[4] + .5 * e[3] = 4.5. So 0 0 0 2 4 4.5.
    // With `prev~(d)` (the delay inside `d` reads the output of the tick before it is stored): `d` given as 2 2 3 3 1 1
    // is 0 2 2 3 3 1 (the 0 is read as 1) over x = 1..6: n0: k1 -> 0; n1: k2 a e[-1] -> 0; n2: k2 a e[0] -> 1; n3: k3 a e[0] -> 1;
    // n4: k3 a e[1] -> 2; n5: k1 a e[4] -> 5. So 0 0 1 1 2 5.
    let src = "flow vd(x: F32 at sample, d: F32 at sample) -> F32 at sample { vdelay~(x, d, 4) }
flow vp(x: F32 at sample, d: F32 at sample) -> F32 at sample { vdelay~(x, prev~(d), 4) }";
    let x = floats(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
    let at = |name: &'static str, d: &[f32]| {
        let cols = vec![("x", x.clone()), ("d", floats(d))];
        let outs = run(src, name, vec![], vec![], cols, vec![6]);
        f32s(&outs)
    };
    same(&at("vd", &[1.0, 2.0, 3.0, 2.0, 1.0, 1.5]), &[0.0, 0.0, 0.0, 2.0, 4.0, 4.5]);
    same(&at("vp", &[2.0, 2.0, 3.0, 3.0, 1.0, 1.0]), &[0.0, 0.0, 1.0, 1.0, 2.0, 5.0]);
}

#[test]
fn vdelay_in_a_feedback_loop_is_an_echo() {
    // §17.4's echo with MAX = 4 and d = 3: y[n] = x[n] + 0.5 * y[n-3]; the input is an impulse: 1 0 0 .5 0 0 .25 0 0 .125.
    let src = "flow echo(x: F32 at sample, d: F32 at block) -> F32 at sample {
  let line = vdelay~(^y, d, 4)
  let y = x + 0.5 * line
  y
}";
    let mut xs = vec![0.0; 10];
    xs[0] = 1.0;
    let outs = run(src, "echo", vec![], vec![("d", Value::F32(3.0))], vec![("x", floats(&xs))], vec![10]);
    let want = [1.0, 0.0, 0.0, 0.5, 0.0, 0.0, 0.25, 0.0, 0.0, 0.125];
    assert!(outs.iter().zip(want).all(|(o, w)| o.same(&Value::F32(w))), "{outs:?}");
}

#[test]
fn a_nan_and_an_infinity_pass_through_the_delays_by_the_formulas() {
    // §11.4, §13.4: a NaN or an infinity travels through a delay like any value (a tick later). `prev~` of 1 NaN 3: 0 1 NaN.
    // `delay~(x, 2)` of 1 inf -inf 2: 0 0 1 inf. The `vdelay~` formula multiplies both neighbours: d = 1 (k 1, f 0), x = inf 1 2 3:
    // n1: a = inf, b = 0: 1 * inf + 0 * 0 = inf; n2: a = 1, b = inf: 1 * 1 + 0 * inf = NaN; n3: a = 2, b = 1: 2: 0 inf NaN 2.
    // With a = -M and b = M (M = `F32::MAX`) and f = .5 (d = 1.5) the sum of the products is 0, not an overflow
    // (`a + f * (b - a)` would be an infinity): x = -M M 0 0: n0: 0; n1: a = -M, b = 0: -M / 2; n2: a = M, b = -M: 0;
    // n3: a = 0, b = M: M / 2.
    let src = "flow pv(x: F32 at sample) -> F32 at sample { prev~(x) }
flow dl(x: F32 at sample) -> F32 at sample { delay~(x, 2) }
flow vd(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 4) }";
    same(&go(src, "pv", &[1.0, f32::NAN, 3.0]), &[0.0, 1.0, f32::NAN]);
    same(&go(src, "dl", &[1.0, f32::INFINITY, f32::NEG_INFINITY, 2.0]), &[0.0, 0.0, 1.0, f32::INFINITY]);
    let at = |d: f32, xs: &[f32]| {
        let outs = run(src, "vd", vec![], vec![("d", Value::F32(d))], vec![("x", floats(xs))], vec![xs.len()]);
        f32s(&outs)
    };
    same(&at(1.0, &[f32::INFINITY, 1.0, 2.0, 3.0]), &[0.0, f32::INFINITY, f32::NAN, 2.0]);
    let m = f32::MAX;
    same(&at(1.5, &[-m, m, 0.0, 0.0]), &[0.0, -m / 2.0, 0.0, m / 2.0]);
}

#[test]
fn the_default_of_an_omitted_init_is_the_default_of_the_value_type() {
    // §11.4, §6.4: `Bool` false, an array and a tuple element by element, a struct the `Default` of its fields (the
    // declared value of a field, `b: I32 = 7`, is the field's).
    // Bool `was = prev~(x > 2.0)` for x = 1 3 1 3 3: was = f f t f t -> 0 0 1 0 1.
    // Array `p = prev~([x, x + 1.0])`, `p[0] + p[1]` for x = 1 2 3: [0, 0] -> 0; [1, 2] -> 3; [2, 3] -> 5.
    // Tuple `(a, b) = prev~((x, x * 2.0))`, `a * 10 + b`: (0, 0) -> 0; (1, 2) -> 12; (2, 4) -> 24.
    // Struct `P { a: F32, b: I32 }`, `q.a` and 100 when `q.b` is 2, for x = 10 20 30: P { 0, 0 } -> 0; { 10, 2 } -> 110;
    // { 20, 2 } -> 120. Struct `Q { a: F32, b: I32 = 7 }`, `q.a` and 1000 when `q.b` is 7: { 0, 7 } -> 1000; { 10, 2 } -> 10;
    // { 20, 2 } -> 20.
    let src = "struct P: Default {
  a: F32,
  b: I32,
}
struct Q: Default {
  a: F32,
  b: I32 = 7,
}
flow bl(x: F32 at sample) -> F32 at sample {
  let was = prev~(x > 2.0)
  if was { 1.0 } else { 0.0 }
}
flow ar(x: F32 at sample) -> F32 at sample {
  let p = prev~([x, x + 1.0])
  p[0] + p[1]
}
flow tu(x: F32 at sample) -> F32 at sample {
  let (a, b) = prev~((x, x * 2.0))
  a * 10.0 + b
}
flow sp(x: F32 at sample) -> F32 at sample {
  let q = prev~(P { a: x, b: 2 })
  q.a + (if q.b == 2 { 100.0 } else { 0.0 })
}
flow sq(x: F32 at sample) -> F32 at sample {
  let q = prev~(Q { a: x, b: 2 })
  q.a + (if q.b == 7 { 1000.0 } else { 0.0 })
}
flow ad(x: F32 at sample) -> F32 at sample {
  let r = delay~([x, x], 2)
  r[0] + r[1]
}";
    same(&go_open(src, "bl", &[1.0, 3.0, 1.0, 3.0, 3.0]), &[0.0, 0.0, 1.0, 0.0, 1.0]);
    same(&go_open(src, "ar", &[1.0, 2.0, 3.0]), &[0.0, 3.0, 5.0]);
    same(&go_open(src, "tu", &[1.0, 2.0, 3.0]), &[0.0, 12.0, 24.0]);
    same(&go_open(src, "sp", &[10.0, 20.0, 30.0]), &[0.0, 110.0, 120.0]);
    same(&go_open(src, "sq", &[10.0, 20.0, 30.0]), &[1000.0, 10.0, 20.0]);
    // `delay~` of arrays: [0, 0] twice, then the sum of [x0, x0] = 2 * x0 and 2 * x1 for x = 1 2 3 4: 0 0 2 4.
    same(&go_open(src, "ad", &[1.0, 2.0, 3.0, 4.0]), &[0.0, 0.0, 2.0, 4.0]);
}

#[test]
fn a_delay_is_made_in_the_forms_a_body_has_around_it() {
    // §11.2, §11.5: a delay in the condition of an `if` (a condition is always evaluated), as the argument of an `rt fn`
    // (`dbl`), around one, and in a field of a struct delayed. x = 1 2 3.
    // `if prev~(x) > 1.5 { 10.0 } else { 20.0 }`: prev = 0 1 2: 20 20 10.
    // `dbl(prev~(x))`: 0 2 4. `prev~(dbl(x))`: 0 2 4.
    let src = "rt fn dbl(v: F32) -> F32 { v * 2.0 }
flow c(x: F32 at sample) -> F32 at sample { if prev~(x) > 1.5 { 10.0 } else { 20.0 } }
flow a(x: F32 at sample) -> F32 at sample { dbl(prev~(x)) }
flow b(x: F32 at sample) -> F32 at sample { prev~(dbl(x)) }";
    let xs = [1.0, 2.0, 3.0];
    same(&go(src, "c", &xs), &[20.0, 20.0, 10.0]);
    same(&go(src, "a", &xs), &[0.0, 2.0, 4.0]);
    same(&go(src, "b", &xs), &[0.0, 2.0, 4.0]);
}

#[test]
fn a_run_in_pieces_is_the_run_in_one_call() {
    // §11.6: the state lives between the calls of `process` (a call of 0 frames too). A flow with `prev~` (init from the
    // input of `init`), `delay~` (init 7.0), a running sum of `x * g` (the `block` input) and a value of `init`: start = 3,
    // g = 2, x = 1 2 3 4: a = prev~(x, 3) = 3 1 2 3; d = delay~(x, 3, 7.0) = 7 7 7 1; c = 2 6 12 20; off = 6;
    // a + d + c + off = 18 20 27 30.
    let src = "flow rs(x: F32 at sample, g: F32 at block, start: F32 at init) -> F32 at sample {
  let a = prev~(x, start)
  let d = delay~(x, 3, 7.0)
  let c = x * g + prev~(^c)
  let off = start * 2.0
  a + d + c + off
}";
    let xs = floats(&[1.0, 2.0, 3.0, 4.0]);
    for calls in [vec![4], vec![2, 2], vec![1, 0, 3], vec![0, 1, 1, 1, 1, 0], vec![3, 1]] {
        let cfg = vec![("start", Value::F32(3.0))];
        let outs = run(src, "rs", cfg, vec![("g", Value::F32(2.0))], vec![("x", xs.clone())], calls.clone());
        assert!(outs.iter().zip([18.0, 20.0, 27.0, 30.0]).all(|(o, w)| o.same(&Value::F32(w))), "{calls:?}: {outs:?}");
    }
}

#[test]
fn the_init_of_a_delay_is_evaluated_once_at_init() {
    // §11.3: an `init` argument is of the clock `init` or less, so it is made once at `init` and kept (§11.4: "saved in the
    // state"). `bi(k)` is counted: once after `init`, and still once after three calls (and the output of the first frame is
    // its value, k = 5).
    counter!(row_i, N_I);
    let src =
        format!("{}flow f(k: I32 at init, x: I32 at sample) -> I32 at sample {{ prev~(x, bi(k)) }}", counted(&["bi"]));
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bi", row_i);
        let mut me = Instance::init(view, def, 48000.0, &[("k", i32v(5))], host(&mut table)).expect("init");
        assert_eq!(N_I.load(Relaxed), 1);
        let mut outs = Vec::new();
        for x in [1, 2, 3] {
            outs.extend(me.process(&[], &[("x", &[i32v(x)])], 1, host(&mut table)).expect("process"));
        }
        assert!(outs.iter().zip([5, 1, 2]).all(|(o, w)| o.same(&i32v(w))), "{outs:?}");
        assert_eq!(N_I.load(Relaxed), 1);
    });
    // A panic of an `init` expression is that of `init`, at the expression: 10 / 0.
    let src = "flow g(k: I32 at init, x: I32 at sample) -> I32 at sample { prev~(x, 10 / k) }";
    with_flow(src, "g", move |view, def| {
        let r = Instance::init(view, def, 48000.0, &[("k", i32v(0))], None).map(|_| Value::Unit);
        assert_eq!(panic_at(&r, src), (PanicKind::DivZero, "10 / k".to_string()));
    });
}

#[test]
fn a_delay_line_longer_than_the_evaluator_holds_is_unavailable() {
    // The spec has no bound under U32 and the `F32` one of 2^24 (§11.4): the evaluator keeps 2^20 places (`Limits::most`),
    // so a line of 2 000 000 and a `vdelay~` of 2^24 stop at `init` with `Unavailable`, and no memory is made for them.
    let src = "flow big(x: F32 at sample) -> F32 at sample { delay~(x, 2000000) }
flow vbig(x: F32 at sample, d: F32 at block) -> F32 at sample { vdelay~(x, d, 16777216) }
flow ok(x: F32 at sample) -> F32 at sample { delay~(x, 1000) }";
    for (name, ok) in [("big", false), ("vbig", false), ("ok", true)] {
        with_flow(src, name, move |view: View, def: DefId| {
            let r = Instance::init(view, def, 48000.0, &[], None);
            match (ok, r) {
                (true, Ok(_)) => {}
                (false, Err(Stop { fault: Fault::Unavailable(_), .. })) => {}
                (_, r) => panic!("{name}: {:?}", r.map(|_| ())),
            }
        });
    }
}

#[test]
fn the_delay_lines_of_an_instance_are_held_to_the_limit_in_all_and_not_each() {
    // The evaluator keeps `Limits::most` places (2^20) for all the delays of an instance, and stops at `init` with
    // `Unavailable` before it makes the memory of the one that goes over. `prev~(x)` holds 1 place, so a line of exactly
    // `most` places after it is over by one (and a line of `most` places alone is not); a `vdelay~` of `MAX` has `MAX + 1`.
    // The memory of the line that goes over is not made, so the test holds one place before it.
    let most = LIMITS.most;
    let src = format!(
        "flow over(x: F32 at sample) -> F32 at sample {{ prev~(x) + delay~(x, {most}) }}
flow vover(x: F32 at sample, d: F32 at block) -> F32 at sample {{ prev~(x) + vdelay~(x, d, {}) }}
flow under(x: F32 at sample) -> F32 at sample {{ prev~(x) + delay~(x, 1000) + delay~(x, 2000) }}",
        most - 1
    );
    for (name, ok) in [("over", false), ("vover", false), ("under", true)] {
        let r = init_stop(true, &src, name);
        match (ok, &r) {
            (true, None) | (false, Some((Fault::Unavailable(_), _))) => {}
            _ => panic!("{name}: {r:?}"),
        }
    }
}

#[test]
fn the_default_of_a_type_over_the_limit_is_unavailable_and_not_made() {
    // §6.4 gives the default of an array of arrays element by element: `[[F32; 1024]; 1025]` is 1 049 600 places, over
    // the 2^20 of `Limits::most` though each level is under it, and a tuple of two arrays of 600 000 is 1 200 000. They
    // stop at `init` with `Unavailable`, before the array is made. The check gives E0200 to the omitted `init` of a type
    // that is not a number, so the source is not clean (the evaluator has the form, `go_open`).
    let src = "flow big(x: F32 at sample) -> F32 at sample {
  let a = prev~([[x; 1024]; 1025])
  a[0][0]
}
flow two(x: F32 at sample) -> F32 at sample {
  let (a, b) = prev~(([x; 600000], [x; 600000]))
  a[0] + b[0]
}
flow small(x: F32 at sample) -> F32 at sample {
  let a = prev~([[x; 4]; 4])
  a[0][0]
}";
    for (name, ok) in [("big", false), ("two", false), ("small", true)] {
        let r = init_stop(false, src, name);
        match (ok, &r) {
            (true, None) | (false, Some((Fault::Unavailable(_), _))) => {}
            _ => panic!("{name}: {r:?}"),
        }
    }
}
