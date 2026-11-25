//! The order of the work of a stage on the evaluator (W7-11 U2b-e, S-1233, S-1206, S-1159, S-1126, S-1154, S-1128, S-1241, S-1242, §11.3, §3.5): in a stage the `let`s are walked from the top and the output last, the work of a call
//! (its arguments and conditions first, then its `init`, its `block` or its tick) is done where the call is written, whether its output is read or not, and what a delay saves is stored after, the delays in the order they are
//! written. It shows only in the second panic, so each test has two divisions that panic and says which is reported (the text of its expression), worked out by hand in the comment.

use super::expr_tests::i32v;
use super::flow::{Instance, Outcome, PanicAt};
use super::flow_tests::with_flow;
use super::reset_tests::outs;
use super::state_tests::same;
use super::value::{IntKind, Value};

const KIDS: &str = "flow kb(x: I32 at sample, b: I32 at block) -> I32 at sample { x * (100 / b) }
flow kn(x: I32 at sample, c: I32 at init) -> I32 at sample { x * (100 / c) }
flow ks(x: U32 at sample, b: U32 at block) -> U32 at sample {
  let t4 = sample_tick() at (sample / 4)
  let q = 100 / (t4 + b)
  x + (q at sample)
}
flow kc(x: I32 at sample, b: I32 at block) -> I32 at sample { x * (500 / b) }
flow kk(x: I32 at (sample * 4)) -> I32 at sample { x[3] }
flow kz(x: I32 at sample) -> I32 at (sample / 4) {
  let _ = 100 / x
  kk~(x).down~(4)
}
flow kx(x: I32 at sample) -> I32 at sample { x * (100 / x) }
flow keep(x: I32 at sample) -> I32 at sample { x }
";

/// The text of the expression the evaluator stops at, and the stage it is of, in `init` of the flow `f` (`config`) or in a `process` of the frames `xs` (`params`, the `sample` input `x` = `xs`).
fn stopped(
    src: &str,
    config: &[(&'static str, Value)],
    params: &[(&'static str, Value)],
    xs: &[Value],
) -> (String, PanicAt) {
    let (text, config, params, xs) = (format!("{KIDS}{src}"), config.to_vec(), params.to_vec(), xs.to_vec());
    let shown = text.clone();
    let (start, end, when) = with_flow(&text, "f", move |view, def| {
        let (at, when) = match Instance::init(view, def, 8.0, &config, None) {
            Err(stop) => (stop.at, PanicAt::Init),
            Ok(mut me) => match me.process_outcome(&params, &[("x", &xs[..])], xs.len(), None).expect("an outcome") {
                Outcome::Panic { at, stop } => (stop.at, at),
                Outcome::Ok(_) => panic!("no panic"),
            },
        };
        (at.start as usize, at.end as usize, when)
    });
    (shown[start..end].to_string(), when)
}

/// The text of the expression the evaluator stops at, for one frame of `x`.
fn first(src: &str, config: &[(&'static str, Value)], params: &[(&'static str, Value)], x: Value) -> String {
    stopped(src, config, params, std::slice::from_ref(&x)).0
}

#[test]
fn a_child_does_its_block_stage_where_it_is_written_before_or_after_a_part_of_the_stage_that_is_written_later_or_earlier()
 {
    // d = 0: `kb~(x, d)` divides by its input `b` in its `block` stage, `x * (200 / d)` has a part `200 / d` of `block`. In a stage the lets are walked from the top and the output is one of them:
    // what is written first is first, so the child's `100 / b` and the part `200 / d` (written before the call: `x * (200 / d) + kb~(x, d)`), each way. An output that does not read the child (`let _`) does it all the same.
    let after = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { kb~(x, d) + x * (200 / d) }";
    let before = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { x * (200 / d) + kb~(x, d) }";
    let unread =
        "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample {\n  let _ = kb~(x, d)\n  x * (200 / d)\n}";
    let d = [("d", i32v(0))];
    assert_eq!(first(after, &[], &d, i32v(1)), "100 / b");
    assert_eq!(first(before, &[], &d, i32v(1)), "200 / d");
    assert_eq!(first(unread, &[], &d, i32v(1)), "100 / b");
}

#[test]
fn the_calls_one_in_the_argument_of_the_other_do_their_work_inner_first_and_one_in_the_first_argument_of_a_delay_where_it_is_written()
 {
    // `kc~(kb~(x, d), d)`: the inner call is in the argument of the outer, so it does its `block` stage first (`100 / b`, not the outer's `500 / b`). The first argument of a delay is not read by the stage
    // that the call is in (§11.4: it is saved at the end), but the call in it does its work where the delay is written (S-1241): `prev~(kb~(x, d)) + x * (200 / d)` reports `100 / b`.
    let nested = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { kc~(kb~(x, d), d) }";
    let delay = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { prev~(kb~(x, d)) + x * (200 / d) }";
    let delay_later = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample { x * (200 / d) + prev~(kb~(x, d)) }";
    let d = [("d", i32v(0))];
    assert_eq!(first(nested, &[], &d, i32v(1)), "100 / b");
    assert_eq!(first(delay, &[], &d, i32v(1)), "100 / b");
    assert_eq!(first(delay_later, &[], &d, i32v(1)), "200 / d");
}

#[test]
fn the_init_of_a_delay_and_of_a_child_is_made_where_it_is_written_and_not_after_the_lets_of_init() {
    // n = 0: `let a = prev~(x, 100 / n)` has its `init` argument written before `let b = 200 / n` (S-1242); `let c = kn~(x, n)` has the child's `init` stage, `100 / c`, written before `let b` too (S-1233).
    let delay = "flow f(x: I32 at sample, n: I32 at init) -> I32 at sample {\n  let a = prev~(x, 100 / n)\n  let b = 200 / n\n  a + b\n}";
    let child = "flow f(x: I32 at sample, n: I32 at init) -> I32 at sample {\n  let a = kn~(x, n)\n  let b = 200 / n\n  a + b\n}";
    let below = "flow f(x: I32 at sample, n: I32 at init) -> I32 at sample {\n  let b = 200 / n\n  let a = kn~(x, n)\n  a + b\n}";
    let n = [("n", i32v(0))];
    assert_eq!(first(delay, &n, &[], i32v(1)), "100 / n");
    assert_eq!(first(child, &n, &[], i32v(1)), "100 / c");
    assert_eq!(first(below, &n, &[], i32v(1)), "200 / n");
}

#[test]
fn a_child_of_sample_over_4_does_its_tick_where_it_is_written_and_not_after_the_lets_of_the_tick_of_its_caller() {
    // b = 0: at the first tick the time is 0, so `ks`'s `100 / (t4 + b)` and the caller's `200 / (t + b)` both divide by 0 in the stage `sample / 4`. The call `ks~(x, b)` is written above the `let m`,
    // so its stage comes first (S-1206, S-1159: the child's tick is not run after the lets of the caller's tick); written below, `200 / (t + b)` is first.
    let above = "flow f(x: U32 at sample, b: U32 at block) -> U32 at sample {\n  let l = ks~(x, b)\n  let t = sample_tick() at (sample / 4)\n  let m = 200 / (t + b)\n  l + (m at sample)\n}";
    let below = "flow f(x: U32 at sample, b: U32 at block) -> U32 at sample {\n  let t = sample_tick() at (sample / 4)\n  let m = 200 / (t + b)\n  let l = ks~(x, b)\n  l + (m at sample)\n}";
    let b = [("b", Value::int(IntKind::U32, 0))];
    assert_eq!(first(above, &[], &b, Value::int(IntKind::U32, 1)), "100 / (t4 + b)");
    assert_eq!(first(below, &[], &b, Value::int(IntKind::U32, 1)), "200 / (t + b)");
}

#[test]
fn the_conditions_of_a_chain_are_read_after_its_arguments_and_the_leftmost_first() {
    // x = 0: `keep~(300 / x).reset_if~(100 / x > 3).when~(200 / x > 3)`: the argument first (`300 / x`), then the conditions in the order written, the `reset_if~`'s before the `when~`'s (S-1233, S-1221).
    // The same on a delay: `prev~(x).reset_if~(100 / x > 3).when~(200 / x > 3)`.
    let args = "flow f(x: I32 at sample) -> I32 at sample { keep~(300 / x).reset_if~(100 / x > 3).when~(200 / x > 3) }";
    let conds = "flow f(x: I32 at sample) -> I32 at sample { keep~(x).reset_if~(100 / x > 3).when~(200 / x > 3) }";
    let delay = "flow f(x: I32 at sample) -> I32 at sample { prev~(x).reset_if~(100 / x > 3).when~(200 / x > 3) }";
    assert_eq!(first(args, &[], &[], i32v(0)), "300 / x");
    assert_eq!(first(conds, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(delay, &[], &[], i32v(0)), "100 / x");
}

#[test]
fn what_a_delay_saves_is_made_in_the_order_the_delays_are_written_and_the_delays_in_it_after_it() {
    // x = 0: `prev~(prev~(x * (100 / x)))` saves the value of the inner delay, which does not panic, and the inner delay saves `x * (100 / x)`, which does; `prev~(x * (300 / x))` is written after both. The saves
    // are in the order the names are written, the inner one after the outer and before the next one (S-1154): `100 / x` is first, and `300 / x` after.
    let src = "flow f(x: I32 at sample) -> I32 at sample { prev~(prev~(x * (100 / x))) + prev~(x * (300 / x)) }";
    assert_eq!(first(src, &[], &[], i32v(0)), "100 / x");
    // A panic of what a delay saves is after a `let` that panics and is written after the delay (S-1126): the `let` first.
    let later =
        "flow f(x: I32 at sample) -> I32 at sample {\n  let a = prev~(x * (300 / x))\n  let b = 200 / x\n  a + b\n}";
    assert_eq!(first(later, &[], &[], i32v(0)), "200 / x");
}

#[test]
fn a_call_that_the_stage_does_not_read_does_its_work_of_sample_where_it_is_written() {
    // x = 0: `kz` has an output at `sample / 4` and a `let _ = 100 / x` of `sample`. A `let` of the tick that holds the call (`let a = kz~(x)`), or a part of the output kept by the tick (`kz~(x) at sample`), or a
    // `par~` of them, is not made by the stage of `sample` (its value is kept), but the work of the call in it is done where it is written (S-1206): above `200 / x` it panics first, below it second.
    let held = "flow f(x: I32 at sample) -> I32 at sample {\n  let a = kz~(x)\n  (a at sample) + 200 / x\n}";
    let above =
        "flow f(x: I32 at sample) -> I32 at sample {\n  let b = 200 / x\n  let a = kz~(x)\n  (a at sample) + b\n}";
    let kept = "flow f(x: I32 at sample) -> I32 at sample { (kz~(x) at sample) + 200 / x }";
    let kept_later = "flow f(x: I32 at sample) -> I32 at sample { 200 / x + (kz~(x) at sample) }";
    let par = "flow f(x: I32 at sample) -> I32 at sample {\n  let a = par~ j in 0 ..< 2 { kz~(x) }\n  (a at sample)[0] + 200 / x\n}";
    assert_eq!(first(held, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(above, &[], &[], i32v(0)), "200 / x");
    assert_eq!(first(kept, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(kept_later, &[], &[], i32v(0)), "200 / x");
    assert_eq!(first(par, &[], &[], i32v(0)), "100 / x");
}

#[test]
fn the_calls_and_the_conditions_in_the_first_argument_of_a_delay_are_done_where_the_delay_is_written() {
    // x = 0: `prev~(kx~(x)) + 200 / x`: the first argument of the delay is saved at the end of the stage, but the call in it does its work (`100 / x` of its body) where it is written (S-1241), before `200 / x`;
    // a condition of a modifier of a delay in it is read there too: `prev~(prev~(x).reset_if~(100 / x > 3)) + 200 / x`. What is saved is made in the order the delays are written, the outer first: the outer saves
    // `(the inner delay) * (200 / x)`, which panics in `200 / x`, before the inner delay's save `x * (100 / x)` (S-1154).
    let call = "flow f(x: I32 at sample) -> I32 at sample { prev~(kx~(x)) + 200 / x }";
    let cond = "flow f(x: I32 at sample) -> I32 at sample { prev~(prev~(x).reset_if~(100 / x > 3)) + 200 / x }";
    let outer = "flow f(x: I32 at sample) -> I32 at sample { prev~(prev~(x * (100 / x)).when~(x < 5) * (200 / x)) }";
    assert_eq!(first(call, &[], &[], i32v(0)), "100 / x");
    let modded = "flow f(x: I32 at sample) -> I32 at sample { prev~(kx~(x)).when~(x < 5) + 200 / x }";
    assert_eq!(first(modded, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(cond, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(outer, &[], &[], i32v(0)), "200 / x");
}

#[test]
fn a_call_in_a_branch_an_arm_a_par_or_a_block_in_the_first_argument_of_a_delay_is_done_where_the_delay_is_written() {
    // x = 0, S-1241 for any depth (§11.3, §11.5): the call `kx~(..)` does its work (`100 / x` of its body) where the delay is written, before the `200 / x` written after the delay, in
    // an arm of a `match~` (an arm that is not taken has `T.default()`: `{ 0 => 1, b => kx~(b) }` takes the first, b = 0 in the second, the call runs all the same), in a branch of an `if~` (every
    // branch is evaluated), in a `par~` (each replica) and in a block. The `200 / x` written before the delay is first, as written.
    let first_of = |first_arg: &str, after: &str| {
        let src = format!("flow f(x: I32 at sample) -> I32 at sample {{ {after} }}").replace("ARG", first_arg);
        first(&src, &[], &[], i32v(0))
    };
    for arg in [
        "match~ x { b => kx~(b) }",
        "match~ x { 0 => 1, b => kx~(b) }",
        "if~ x > 5 { kx~(x) } else { 7 }",
        "{ kx~(x) }",
        "if~ x > 5 { 1 } else if x < -5 { 2 } else { kx~(x) }",
    ] {
        assert_eq!(first_of(arg, "prev~(ARG) + 200 / x"), "100 / x", "{arg}");
        assert_eq!(first_of(arg, "200 / x + prev~(ARG)"), "200 / x", "{arg}");
    }
    assert_eq!(first_of("par~ i in 0 ..< 2 { kx~(x) }", "prev~(ARG)[0] + 200 / x"), "100 / x");
    assert_eq!(first_of("par~ i in 0 ..< 2 { kx~(x) }", "200 / x + prev~(ARG)[0]"), "200 / x");
    // The call in the condition of an `if` and in the object of a `match` (not a branch: E0811 keeps one out of those).
    assert_eq!(first_of("if kx~(x) > 0 { 1 } else { 2 }", "prev~(ARG) + 200 / x"), "100 / x");
    assert_eq!(first_of("match kx~(x) { 0 => 1, _ => 2 }", "prev~(ARG) + 200 / x"), "100 / x");
}

#[test]
fn a_call_beside_a_name_below_in_the_first_argument_of_a_delay_is_done_where_the_delay_is_written() {
    // x = 0: `prev~(kx~(x) + ^m)` has a `^m` beside the call (the name of a `let` below), and the call does its work where the delay is written (`^name` is no place of an instance, E0801): `100 / x` before the
    // `200 / x` of the output. In a `match~` of the first argument too.
    let beside =
        "flow f(x: I32 at sample) -> I32 at sample {\n  let p = prev~(kx~(x) + ^m)\n  let m = x + 3\n  p + 200 / x\n}";
    let arm = "flow f(x: I32 at sample) -> I32 at sample {\n  let p = prev~(match~ x { b => kx~(b) + ^m })\n  let m = x + 3\n  p + 200 / x\n}";
    assert_eq!(first(beside, &[], &[], i32v(0)), "100 / x");
    assert_eq!(first(arm, &[], &[], i32v(0)), "100 / x");
}

#[test]
fn the_argument_a_call_gathers_is_made_where_the_call_is_written_and_not_after_the_lets_of_the_stage() {
    // §11.9, §11.3, S-1233: `gu~((100 / t) at sample).down~(2)` gathers its argument at `sample`, whose part `100 / t` is of the stage `sample / 2` (`t` is its tick, 0 at the first frame). The call is read by `let r` of that
    // stage, so the part is made where `r` is written: above `let m = 200 / t` it is first, below it second.
    let above = "flow f(x: U32 at sample) -> U32 at sample {\n  let t = sample_tick() at (sample / 2)\n  let r = gu~((100 / t) at sample).down~(2)\n  let m = 200 / t\n  (r at sample) + (m at sample) + x\n}";
    let below = "flow f(x: U32 at sample) -> U32 at sample {\n  let t = sample_tick() at (sample / 2)\n  let m = 200 / t\n  let r = gu~((100 / t) at sample).down~(2)\n  (r at sample) + (m at sample) + x\n}";
    let (gu, one) = ("flow gu(a: U32 at (sample * 2)) -> U32 at sample { a[0] + a[1] }\n", Value::int(IntKind::U32, 1));
    assert_eq!(first(&format!("{gu}{above}"), &[], &[], one.clone()), "100 / t");
    assert_eq!(first(&format!("{gu}{below}"), &[], &[], one), "200 / t");
}

#[test]
fn a_part_that_reads_a_name_below_is_made_at_the_end_of_its_stage_whether_the_delay_is_read_or_not() {
    // S-1244, §11.2, §11.3: `100 / (d + ^m)` in the first argument of the delay is a part of `block` (`m` is a `let` of `block` below). It is made at the end of the stage, after the `let`s and the output, so it panics in the stage
    // `block` of a call of 0 frames (d = 0: `m` = 0), and a `let` of the stage that panics too, `200 / d` written below it, is first. The part of `init` (`n`, `m` of `init`) panics at `init`. Under the condition of
    // `block` that does not hold (`d != 0`) it is not made.
    let part = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample {\n  let q = prev~(x * (100 / (d + ^m)))\n  let m = d * 0\n  q\n}";
    let with_let = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample {\n  let q = prev~(x * (100 / (d + ^m)))\n  let m = d * 0\n  let w = 200 / d\n  q + w\n}";
    let at_init = "flow f(x: I32 at sample, n: I32 at init) -> I32 at sample {\n  let q = prev~(x * (100 / (n + ^m)))\n  let m = n * 0\n  q\n}";
    let guarded = "flow f(x: I32 at sample, d: I32 at block) -> I32 at sample {\n  let q = prev~(x * (if d != 0 { 100 / (d + ^m) } else { 0 }))\n  let m = d * 0\n  q\n}";
    let d = [("d", i32v(0))];
    assert_eq!(stopped(part, &[], &d, &[]), ("100 / (d + ^m)".to_string(), PanicAt::Block));
    assert_eq!(stopped(with_let, &[], &d, &[]), ("200 / d".to_string(), PanicAt::Block));
    assert_eq!(stopped(at_init, &[("n", i32v(0))], &[], &[]), ("100 / (n + ^m)".to_string(), PanicAt::Init));
    // d = 0 does not hold `d != 0`: the part is not made; the output (the stored value, 0) is 0 at both frames, and no panic.
    let guarded_ok = with_flow(&format!("{KIDS}{guarded}"), "f", move |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let out = me.process(&d, &[("x", &[i32v(5), i32v(6)][..])], 2, None).expect("process");
        out.iter().map(|v| matches!(v, Value::Int(_, 0, _))).collect::<Vec<_>>()
    });
    assert_eq!(guarded_ok, [true, true]);
}

#[test]
fn a_part_of_a_tick_that_reads_a_name_below_is_made_with_the_saves_in_the_order_they_are_written() {
    // S-1244, S-1154: at the first tick of `sample / 4` (t = 0, z = 0) both the part `100 / (t + ^z)` (a part of the tick in the first argument of `s`, a delay at `sample`) and what the delay `d` saves, `200 / t`,
    // panic in the end of the stage; in the order the delays are written, so the one of `s` first when `s` is written above `d`, the other when below.
    let head = "flow f(x: U32 at sample) -> U32 at sample {\n  let t = sample_tick() at (sample / 4)\n";
    let s = "  let s = prev~(x * ((100 / (t + ^z)) at sample))\n  let z = t - t\n";
    let d = "  let d = prev~(200 / t)\n";
    let tail = "  s + (d at sample)\n}";
    let one = [Value::int(IntKind::U32, 1)];
    let (above, below) = (format!("{head}{s}{d}{tail}"), format!("{head}{d}{s}{tail}"));
    assert_eq!(stopped(&above, &[], &[], &one).0, "100 / (t + ^z)");
    assert_eq!(stopped(&below, &[], &[], &one).0, "200 / t");
}

#[test]
fn a_part_of_a_tick_that_reads_a_name_below_is_kept_until_the_next_tick_and_goes_back_to_the_default_at_a_reset() {
    // S-1244, §11.3, §11.10: `k` counts 1 2 at the frames 0 and 4 (`sample / 4`), the part `^k + 1.0` is 2 then 3, made at the end of the tick and kept, and `q` is it a sample late: 0 2 2 2 2 (the 3 of the frame 4 is
    // saved at the end of that frame). A `reset_if~` at the frame 5 puts the delay, `k` and the field of the part back to `T.default()`: q is 0 at the frame 5, 0 at 6 and 7 (the field is 0.0 until the tick, not 0 + 1), and
    // 0 at 8 (the delay saved the field of the frame 7). At the frame 8 the tick makes k = 1 and the part 2: q is 2 at the frame 9.
    let src = "flow counted() -> F32 at sample {\n  let q = prev~((^k + 1.0) at sample)\n  let k = prev~(^k at (sample / 4)) + 1.0\n  q\n}\nflow top(r: Bool at sample) -> F32 at sample { counted~().reset_if~(r) }";
    let got = outs(src, "top", None, &[("r", &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0])]);
    same(&got, &[0.0, 2.0, 2.0, 2.0, 2.0, 0.0, 0.0, 0.0, 0.0, 2.0]);
}

#[test]
fn each_replica_of_a_par_has_the_field_of_its_own_for_the_part_that_reads_a_name_below() {
    // S-1244, S-1140: `k = p + 1` = 3 (p = 2) is of `block`; the parts `^k * round_from(i)` are 0 and 3 (replica 0, 1), each made at the end of `block` and kept by its replica. The delay of replica 1 gives x * 3 a sample late
    // (x = 1 2 3 4: 0 3 6 9), the one of replica 0 gives 0.
    let src = "flow f(x: U32 at sample, p: U32 at block) -> U32 at sample {\n  let qs = par~ i in 0 ..< 2 { prev~(x * (^k * i)) }\n  let k = p + 1\n  qs[0] + qs[1]\n}";
    let got = with_flow(&format!("{KIDS}{src}"), "f", move |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[], None).expect("init");
        let xs = [1, 2, 3, 4].map(|n| Value::int(IntKind::U32, n));
        let out = me.process(&[("p", Value::int(IntKind::U32, 2))], &[("x", &xs[..])], 4, None).expect("process");
        out.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { -1 }).collect::<Vec<_>>()
    });
    assert_eq!(got, [0, 3, 6, 9]);
}

#[test]
fn a_branch_whose_condition_reads_a_name_below_is_done_where_written() {
    // x = 0: the condition `^v > 0` of an `if~` has no value where the call is written, but every branch is evaluated whatever it is, so `kx~(x)` does its `100 / x` before the output's `200 / x`.
    // (An object `^v` of a `match~` is left to where the delay saves, and the walk of `init` reads `^v` with no value there: an internal error that is not of this unit, in the report.)
    let branch = "flow f(x: I32 at sample) -> I32 at sample {\n  let p = prev~(if~ ^v > 0 { kx~(x) } else { 1 })\n  let v: I32 = x\n  p + 200 / x\n}";
    assert_eq!(first(branch, &[], &[], i32v(0)), "100 / x");
}

#[test]
fn the_init_of_a_delay_that_reads_a_name_below_is_made_at_the_end_of_init() {
    // S-1244 (the same rule as the part of `block`): `prev~(x, ^k)` starts from `k = c + 1` = 5 of `init`, made at the end of `init`. The outer delay saves the output of the inner one: x = 1 2 3 gives the inner outputs 5 1 2, and
    // the outer 0 5 1.
    let src = "flow f(x: I32 at sample, c: I32 at init) -> I32 at sample {\n  let q = prev~(prev~(x, ^k))\n  let k = c + 1\n  q\n}";
    let got = with_flow(&format!("{KIDS}{src}"), "f", move |view, def| {
        let mut me = Instance::init(view, def, 8.0, &[("c", i32v(4))], None).expect("init");
        let xs = [i32v(1), i32v(2), i32v(3)];
        let out = me.process(&[], &[("x", &xs[..])], 3, None).expect("process");
        out.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { -1 }).collect::<Vec<_>>()
    });
    assert_eq!(got, [0, 5, 1]);
}

#[test]
fn the_d_of_a_vdelay_that_reads_a_name_below_is_read_where_it_is_saved_and_the_condition_where_written() {
    // S-1244: in `prev~(vdelay~(x, ^k, 8).reset_if~(100 / sample_tick() > 3))` with a `200 / sample_tick()` written below (the first frame) the condition of the modifier is read where the delay is written (`100 / sample_tick()`), the `d` (`^k`, no value there) where it is saved.
    let src = "flow f(x: F32 at sample) -> F32 at sample {\n  let p = prev~(vdelay~(x, ^k, 8).reset_if~(100 / sample_tick() > 3))\n  let k = x + 1.0\n  let _ = 200 / sample_tick()\n  p\n}";
    assert_eq!(first(src, &[], &[], Value::F32(0.0)), "100 / sample_tick()");
}
