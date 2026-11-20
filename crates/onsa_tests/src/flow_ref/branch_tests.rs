//! The tests of `par~`, `if~` and `match~` (W7-18 U2, §11.5): a `par~` makes a replica of its body for each value of its
//! index, with a state for each; `if~` and `match~` evaluate every branch (so that what has state in each moves, and a
//! panic in one is a panic) and take the value of one; the arm of a `match~` that is not taken has the locals of its
//! pattern at `T.default()`. The values are worked out by hand from the spec, in the comment of each test.
//!
//! The check of this version gives `if~` and `match~` E0200 (W7-06, the tables of the body are whole), so the sources
//! with them are run unclean (`run_with(false, ..)`); a `par~` with `..<` is clean.

use super::expr::Stop;
use super::expr_tests::{i32v, with_checked};
use super::flow::{Instance, Outcome};
use super::flow_tests::with_flow;
use super::scalar::{Fault, PanicKind};
use super::state_tests::run_with;
use super::value::{IntKind, Value};

fn doubles(xs: &[f64]) -> Vec<Value> {
    xs.iter().map(|x| Value::F64(*x)).collect()
}

fn f64s(vs: &[Value]) -> Vec<f64> {
    vs.iter().map(|v| if let Value::F64(x) = v { *x } else { panic!("not an F64: {v:?}") }).collect()
}

fn same64(got: &[f64], want: &[f64]) {
    assert!(
        got.len() == want.len() && got.iter().zip(want).all(|(a, b)| a.to_bits() == b.to_bits()),
        "got {got:?}, want {want:?}"
    );
}

/// The `F64`s of an array value.
fn row(v: &Value) -> Vec<f64> {
    let Value::Array(vs) = v else { panic!("not an array: {v:?}") };
    f64s(vs)
}

/// The arrays a flow gives for the column `x` (`F64`) of `n` frames, in one call.
fn rows(clean: bool, src: &str, name: &'static str, x: &[f64]) -> Vec<Vec<f64>> {
    let outs = run_with(clean, src, name, vec![], vec![], vec![("x", doubles(x))], vec![x.len()]);
    outs.iter().map(row).collect()
}

/// `acc~(x)` is the sum of the inputs so far (§11.4: `prev~` is the value of the last tick).
const ACC: &str = "flow acc(x: F64 at sample) -> F64 at sample {
  let s = x + prev~(^s)
  s
}
";

#[test]
fn a_par_makes_an_array_of_the_values_of_its_body_for_each_index() {
    // §11.5: `par~ i in a ..< b { e }` is `e` for i = a, a + 1, .., b - 1, as an array of `b - a`. `i` is a `U32`.
    // `x * ((i) as F64)` for x = 2.0 and 0.5 over i = 0 ..< 4 is [0, 2, 4, 6] and [0, 0.5, 1, 1.5]; the range
    // 3 ..< 6 is [3, 4, 5] (the index starts at `a`), and a range of one is an array of one.
    let src = "flow ramp(x: F64 at sample) -> [F64; 4] at sample { par i in 0 ..< 4 { x * ((i) as F64) } }
flow from3(x: F64 at sample) -> [F64; 3] at sample { par i in 3 ..< 6 { ((i) as F64) + x } }
flow one(x: F64 at sample) -> [F64; 1] at sample { par i in 7 ..< 8 { ((i) as F64) * x } }";
    assert_eq!(rows(true, src, "ramp", &[2.0, 0.5]), [vec![0.0, 2.0, 4.0, 6.0], vec![0.0, 0.5, 1.0, 1.5]]);
    assert_eq!(rows(true, src, "from3", &[0.0, 10.0]), [vec![3.0, 4.0, 5.0], vec![13.0, 14.0, 15.0]]);
    assert_eq!(rows(true, src, "one", &[1.0]), [vec![7.0]]);
}

#[test]
fn each_replica_of_a_par_has_a_state_of_its_own() {
    // §11.5: "a call in `e` is an instance for each replica". The replica k of `acc~(x * (k + 1))` is the running sum of
    // (k + 1) * x: x = 1, 1, 1 give [1, 2, 3], [2, 4, 6], [3, 6, 9]; one state for the three would give other sums.
    // The delays are the same: `prev~(x + i)` for x = 1, 10 is [0, 0, 0] (the default) and then [1, 2, 3] (the x + i of the
    // tick before: 1 + 0, 1 + 1, 1 + 2), and `delay~(x + i, 2)` for x = 1, 2, 3 is [0, 0, 0], [0, 0, 0], [1, 2, 3].
    let src = format!(
        "{ACC}flow sums(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ acc~(x * ((i + 1) as F64)) }} }}
flow lag(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ prev~(x + ((i) as F64)) }} }}
flow two(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ delay~(x + ((i) as F64), 2) }} }}"
    );
    let ones = [1.0; 3];
    assert_eq!(rows(true, &src, "sums", &ones), [vec![1.0, 2.0, 3.0], vec![2.0, 4.0, 6.0], vec![3.0, 6.0, 9.0]]);
    assert_eq!(rows(true, &src, "lag", &[1.0, 10.0]), [vec![0.0; 3], vec![1.0, 2.0, 3.0]]);
    assert_eq!(rows(true, &src, "two", &ones), [vec![0.0; 3], vec![0.0; 3], vec![1.0, 2.0, 3.0]]);
}

#[test]
fn what_a_delay_saves_in_a_replica_is_read_under_the_index_of_that_replica() {
    // §11.4, §11.5: a delay stores what its argument is for the tick, in the second phase; in a `par~` that is the value
    // under the index of its own replica (here `i + 1`, which is 1, 2, 3), not the last replica's. `prev~(x * (i + 1))` for
    // x = 1, 10 is [0, 0, 0] then [1, 2, 3]; with an instance in the argument, `prev~(acc~(x * (i + 1)))` for x = 1, 1, 1 is
    // [0, 0, 0], [1, 2, 3], [2, 4, 6]: the replica of the instance in the second phase is the replica of the delay.
    let src = format!(
        "{ACC}flow d(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ prev~(x * ((i + 1) as F64)) }} }}
flow e(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ prev~(acc~(x * ((i + 1) as F64))) }} }}"
    );
    assert_eq!(rows(true, &src, "d", &[1.0, 10.0]), [vec![0.0; 3], vec![1.0, 2.0, 3.0]]);
    assert_eq!(rows(true, &src, "e", &[1.0; 3]), [vec![0.0; 3], vec![1.0, 2.0, 3.0], vec![2.0, 4.0, 6.0]]);
}

#[test]
fn the_index_of_a_par_is_read_by_the_init_of_a_delay_and_by_the_inputs_of_an_instance_of_each_clock() {
    // §11.5: `i` is a value of the clock `init`: the `init` of a delay, an input of an instance at `init` and one at `block`
    // read it. `prev~(x, ((i) as F64))` for x = 5, 6 is [0, 1, 2] (the `init` of each replica) then [5, 5, 5]. `st`
    // has p[0] = start (`init`) and p[n + 1] = x[n]: `st~(((i) as F64), x)` gives the same. `gain~(x, ((i) as F64))`
    // is x * g with g = i at `block` (read by the `block` stage of each instance, with the index of its replica): x = 2.0
    // and 3.0 over three replicas is [0, 2, 4], [0, 3, 6].
    let src = "flow init_of(x: F64 at sample) -> [F64; 3] at sample { par~ i in 0 ..< 3 { prev~(x, ((i) as F64)) } }
flow st(start: F64 at init, x: F64 at sample) -> F64 at sample { prev~(x, start) }
flow starts(x: F64 at sample) -> [F64; 3] at sample { par~ i in 0 ..< 3 { st~(((i) as F64), x) } }
flow gain(x: F64 at sample, g: F64 at block) -> F64 at sample { x * g }
flow gains(x: F64 at sample) -> [F64; 3] at sample { par~ i in 0 ..< 3 { gain~(x, ((i) as F64)) } }";
    assert_eq!(rows(true, src, "init_of", &[5.0, 6.0]), [vec![0.0, 1.0, 2.0], vec![5.0; 3]]);
    assert_eq!(rows(true, src, "starts", &[5.0, 6.0]), [vec![0.0, 1.0, 2.0], vec![5.0; 3]]);
    assert_eq!(rows(true, src, "gains", &[2.0, 3.0]), [vec![0.0, 2.0, 4.0], vec![0.0, 3.0, 6.0]]);
}

#[test]
fn a_par_inside_a_par_has_the_state_of_each_pair_of_indexes() {
    // §11.5: replicas inside replicas: the replica (i, j) of `acc~(x * (3 i + j + 1))` is the running sum of that weight: the
    // weights are [[1, 2, 3], [4, 5, 6]]. For x = 1, 1: after one frame the sums are the weights, after two they are twice.
    // The output reads three of them, `g[0][1] + 10 g[1][0] + 100 g[1][2]` = 2 + 40 + 600 = 642, then 1284 (a swap of the
    // indexes, or a state shared by the replicas of an index, would read other numbers).
    let src = format!(
        "{ACC}flow nest(x: F64 at sample) -> F64 at sample {{
  let g = par~ i in 0 ..< 2 {{ par~ j in 0 ..< 3 {{ acc~(x * ((i * 3 + j + 1) as F64)) }} }}
  g[0][1] + 10.0 * g[1][0] + 100.0 * g[1][2]
}}"
    );
    same64(
        &f64s(&run_with(true, &src, "nest", vec![], vec![], vec![("x", doubles(&[1.0, 1.0]))], vec![2])),
        &[642.0, 1284.0],
    );
}

#[test]
fn reset_puts_the_state_of_every_replica_back_and_the_calls_in_a_call_of_each_replica_run_again() {
    // §11.6: `reset` sets every delay of every replica to its `init`. Over x = 1, 1 the replicas of `acc~` are [1, 2, 3] and
    // [2, 4, 6] as above; after `reset` the same two frames give them again, and a call split in two (1 frame and 1) does too.
    let src = format!(
        "{ACC}flow sums(x: F64 at sample) -> [F64; 3] at sample {{ par~ i in 0 ..< 3 {{ acc~(x * ((i + 1) as F64)) }} }}"
    );
    let got = with_flow(&src, "sums", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let one = doubles(&[1.0]);
        let mut all = Vec::new();
        for step in 0..5 {
            if step == 2 {
                me.reset();
            }
            all.extend(me.process(&[], &[("x", &one[..])], 1, None).expect("process").iter().map(row));
        }
        all
    });
    // Frames 0, 1 (the sums), `reset`, frames 2, 3 (the sums again) and 4 (the second frame of the second run).
    let (a, b) = (vec![1.0, 2.0, 3.0], vec![2.0, 4.0, 6.0]);
    assert_eq!(got, [a.clone(), b.clone(), a, b.clone(), vec![3.0, 6.0, 9.0]]);
}

#[test]
fn a_par_of_a_constant_clock_is_made_at_init_and_one_of_more_replicas_than_the_evaluator_holds_stops() {
    // §11.5, §11.3: `w` has no input in it, so it is made once (a value of `init`): [0, 0.25, 0.5, 0.75], and `w[2] * x` is
    // x / 2. A `par` of 2 000 000 replicas is more than the evaluator holds (`Limits::most`, 2^20): `Unavailable`, whatever
    // the body, before it makes one.
    let src = "flow table(x: F64 at sample) -> F64 at sample {
  let w = par i in 0 ..< 4 { ((i) as F64) * 0.25 }
  w[2] * x
}
flow wide(x: F64 at sample) -> F64 at sample {
  let w = par i in 0 ..< 2000000 { x }
  w[0]
}";
    same64(
        &f64s(&run_with(true, src, "table", vec![], vec![], vec![("x", doubles(&[2.0, 4.0]))], vec![2])),
        &[1.0, 2.0],
    );
    // `wide` has no state in its `par` (it makes no node at `init`) and reads `x`, so it stops in the first frame.
    let r = with_flow(src, "wide", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        me.process(&[], &[("x", &doubles(&[1.0])[..])], 1, None)
    });
    assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{r:?}");
}

#[test]
fn a_closed_range_has_one_replica_more_and_ends_at_b() {
    // §11.5: `par~ i in a ..= b { e }` is `b - a + 1` replicas, the last with i = b: `0 ..= 2` is [0, 1, 2] and `5 ..= 5` one.
    let src = "flow closed(x: F64 at sample) -> [F64; 3] at sample { par i in 0 ..= 2 { ((i) as F64) + x } }
flow single(x: F64 at sample) -> [F64; 1] at sample { par i in 5 ..= 5 { ((i) as F64) + x } }";
    assert_eq!(rows(false, src, "closed", &[0.0]), [vec![0.0, 1.0, 2.0]]);
    assert_eq!(rows(false, src, "single", &[0.5]), [vec![5.5]]);
}

#[test]
fn if_tilde_evaluates_every_branch_and_takes_the_value_of_one() {
    // §11.5: "evaluates all the branches and chooses one". `if~ c { acc~(x) } else { 0.0 - x }` over c = F, T, F, T and
    // x = 1: the instance runs in each frame (1, 2, 3, 4), the value is -1 where c is false and the sum where it is true:
    // [-1, 2, -1, 4]. With a plain `if` the instance would run in the frames it is taken only (1, 2).
    let src = format!(
        "{ACC}flow sel(x: F64 at sample, c: Bool at sample) -> F64 at sample {{ if~ c {{ acc~(x) }} else {{ 0.0 - x }} }}"
    );
    let c = [false, true, false, true].map(Value::Bool).to_vec();
    let outs = run_with(false, &src, "sel", vec![], vec![], vec![("x", doubles(&[1.0; 4])), ("c", c)], vec![4]);
    same64(&f64s(&outs), &[-1.0, 2.0, -1.0, 4.0]);
}

#[test]
fn an_else_if_chain_of_if_tilde_evaluates_all_its_branches_and_takes_the_first_true() {
    // §11.5: "`~` covers the whole chain". `if~ c1 { acc~(x) } else if c2 { acc~(x * 10.0) } else { acc~(x * 100.0) }` over
    // x = 1 has the three sums 1, 2, 3, 4, 5 / 10, 20, 30, 40, 50 / 100, 200, 300, 400, 500. The first true branch is taken:
    // (c1, c2) = (F, F) takes the else, (F, T) the second, (T, F) and (T, T) the first, and (F, T) again takes the second,
    // the sum of which has gone on in the frame where the first was taken: [100, 20, 3, 4, 50].
    let src = format!(
        "{ACC}flow chain(x: F64 at sample, c1: Bool at sample, c2: Bool at sample) -> F64 at sample {{
  if~ c1 {{ acc~(x) }} else if c2 {{ acc~(x * 10.0) }} else {{ acc~(x * 100.0) }}
}}"
    );
    let c1 = [false, false, true, true, false].map(Value::Bool).to_vec();
    let c2 = [false, true, false, true, true].map(Value::Bool).to_vec();
    let cols = vec![("x", doubles(&[1.0; 5])), ("c1", c1), ("c2", c2)];
    same64(&f64s(&run_with(false, &src, "chain", vec![], vec![], cols, vec![5])), &[100.0, 20.0, 3.0, 4.0, 50.0]);
}

#[test]
fn a_panic_in_a_branch_not_taken_is_a_panic_of_if_tilde_and_not_of_if() {
    // §11.5: all the branches are evaluated, so `100 / d` of the branch not taken panics with d = 0 (DivZero, at the
    // expression); a plain `if` with the same branches does not, and an `if` inside the branch of the `if~` is the way to
    // evaluate part of a branch only: `if d != 0 { 100 / d } else { 0 }` is 0 with d = 0.
    let src = "flow tilde(c: Bool at sample, d: I32 at sample) -> I32 at sample { if~ c { 1 } else { 100 / d } }
flow plain(c: Bool at sample, d: I32 at sample) -> I32 at sample { if c { 1 } else { 100 / d } }
flow inner(c: Bool at sample, d: I32 at sample) -> I32 at sample { if~ c { 1 } else { if d != 0 { 100 / d } else { 0 } } }";
    let run = |name: &'static str| {
        let text = src.to_string();
        with_checked(src, false, move |a| {
            let (view, def) = (super::sema_view::View::new(a), super::expr_tests::def_named(a, name));
            let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
            let (c, d) = (vec![Value::Bool(true)], vec![i32v(0)]);
            match me.process_outcome(&[], &[("c", &c[..]), ("d", &d[..])], 1, None).expect("an outcome") {
                Outcome::Ok(outs) => format!(
                    "{:?}",
                    outs.iter().map(|o| matches!(o, Value::Int(_, n, _) if *n == 1)).collect::<Vec<_>>()
                ),
                Outcome::Panic { stop, .. } => {
                    format!("{:?} {}", stop.fault, &text[stop.at.start as usize..stop.at.end as usize])
                }
            }
        })
    };
    assert_eq!(run("tilde"), format!("{:?} 100 / d", Fault::Panic(PanicKind::DivZero)));
    assert_eq!(run("plain"), "[true]");
    assert_eq!(run("inner"), "[true]");
}

#[test]
fn match_tilde_evaluates_every_arm_and_takes_the_arm_a_match_takes() {
    // §11.5: every arm is evaluated, and the arm taken is the first that the pattern and the guard choose. Over x = 1 the
    // sums of the three arms are 1, 2, 3, 4 / 10, 20, 30, 40 / 100, 200, 300, 400: k = 0, 1, 2, 0 takes the first, the second,
    // the last (`_`) and the first: [1, 20, 300, 4]. With a guard (`n if n > 5`): k = 7, 1, 9, 2 take the first arm where the
    // guard is true (the sums 1, 2, 3, 4 then the weight of the binding n) and the second otherwise: the arm taken has the
    // value of the scrutinee in its binding: [1 + 7, 20 + 1, 3 + 9, 40 + 2] = [8, 21, 12, 42].
    let src = format!(
        "{ACC}flow arms(x: F64 at sample, k: I32 at sample) -> F64 at sample {{
  match~ k {{ 0 => acc~(x), 1 => acc~(x * 10.0), _ => acc~(x * 100.0) }}
}}
flow guarded(x: F64 at sample, k: I32 at sample) -> F64 at sample {{
  match~ k {{
    n if n > 5 => acc~(x) + ((n) as F64),
    n => acc~(x * 10.0) + ((n) as F64),
  }}
}}"
    );
    let cols = |ks: [i128; 4]| vec![("x", doubles(&[1.0; 4])), ("k", ks.map(i32v).to_vec())];
    same64(
        &f64s(&run_with(false, &src, "arms", vec![], vec![], cols([0, 1, 2, 0]), vec![4])),
        &[1.0, 20.0, 300.0, 4.0],
    );
    same64(
        &f64s(&run_with(false, &src, "guarded", vec![], vec![], cols([7, 1, 9, 2]), vec![4])),
        &[8.0, 21.0, 12.0, 42.0],
    );
}

#[test]
fn the_binding_of_an_arm_not_taken_is_the_default_of_its_type() {
    // §11.5: "the binding of an arm that is not taken is `T.default()`". `Some(v) => prev~(v)` stores v each frame; when the
    // arm is not taken v is 0.0 (the default of `F64`), so what it stores in that frame is 0.0, not the v of the frame
    // before. With x = 3, 0, 5, 7 and the option Some where k = 1 (k = 1, 0, 1, 1): the first frame reads the `init` 0.0
    // (stores 3), the second reads 3 (the arm is not taken: stores 0.0), the third reads that 0.0 (stores 5), the fourth reads
    // 5: [0, 0, 0, 5] (a binding that keeps the last value would give 3 in the third).
    let src = "flow opt(x: F64 at sample, k: I32 at sample) -> F64 at sample {
  let m = if k > 0 { Some(x) } else { None }
  match~ m { Some(v) => prev~(v), None => 0.0 }
}";
    let cols = vec![("x", doubles(&[3.0, 0.0, 5.0, 7.0])), ("k", [1, 0, 1, 1].map(i32v).to_vec())];
    same64(&f64s(&run_with(false, src, "opt", vec![], vec![], cols, vec![4])), &[0.0, 0.0, 0.0, 5.0]);
}

#[test]
fn a_panic_in_an_arm_not_taken_is_a_panic_of_match_tilde() {
    // §11.5: every arm is evaluated: `100 / d` of the last arm panics with d = 0 though k = 0 takes the first.
    let src = "flow arms(k: I32 at sample, d: I32 at sample) -> I32 at sample { match~ k { 0 => 1, _ => 100 / d } }";
    let r = with_checked(src, false, |a| {
        let (view, def) = (super::sema_view::View::new(a), super::expr_tests::def_named(a, "arms"));
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        me.process(&[], &[("k", &[i32v(0)][..]), ("d", &[i32v(0)][..])], 1, None).err().map(|s| s.fault)
    });
    assert_eq!(r, Some(Fault::Panic(PanicKind::DivZero)));
}

#[test]
fn what_a_delay_saves_in_an_arm_of_a_par_is_read_under_the_binding_of_the_arm_and_the_index() {
    // §11.4, §11.5: `match~ k + i { n => prev~(n) }` in a `par~`: the n of the arm is the k + i of the replica, and a delay
    // reads its argument in the second phase, under the n and the i of the replica it is in. For k = 3, 5 the first frame is
    // the `init` ([0, 0]) and the second the first frame's n: [3, 4] (the n of the last replica would give [4, 4]). With the i
    // in the stored value as well (`n + i`: [3, 5]) the index is read under its replica too.
    let src = "flow f(k: U32 at sample) -> [F64; 2] at sample {
  par~ i in 0 ..< 2 { match~ k + i { n => prev~((n as F64)) } }
}
flow g(k: U32 at sample) -> [F64; 2] at sample {
  par~ i in 0 ..< 2 { match~ k + i { n => prev~((n as F64) + (i as F64)) } }
}";
    let ks = || vec![("k", [3, 5].map(|k| Value::int(IntKind::U32, k)).to_vec())];
    let rows = |name: &'static str| {
        run_with(false, src, name, vec![], vec![], ks(), vec![2]).iter().map(row).collect::<Vec<_>>()
    };
    assert_eq!(rows("f"), [vec![0.0, 0.0], vec![3.0, 4.0]]);
    assert_eq!(rows("g"), [vec![0.0, 0.0], vec![3.0, 5.0]]);
}

/// `init` of the flow `name` with `config`, then one `process` of the frames `xs` (a source that has the E0200 of `match~`
/// runs: the evaluator has the form and its tables are whole).
fn open_run(
    src: &str,
    name: &'static str,
    config: Vec<(&'static str, Value)>,
    params: Vec<(&'static str, Value)>,
    xs: &[f64],
) -> Result<Vec<f64>, Stop> {
    let xs = doubles(xs);
    with_checked(src, false, move |a| {
        let (view, def) = (super::sema_view::View::new(a), super::expr_tests::def_named(a, name));
        let mut me = Instance::init(view, def, 48000.0, &config, None)?;
        me.process(&params, &[("x", &xs[..])], xs.len(), None).map(|outs| f64s(&outs))
    })
}

#[test]
fn the_results_of_nested_pars_are_held_to_the_limit_before_they_are_all_made() {
    // §11.5: the evaluator holds `Limits::most` (2^20 = 1 048 576) places in a value (the spec has no limit, so a value over
    // it is `Unavailable` and not a wrong value), as `[e; N]` does for `N` times the places of `e`; a `par~` of n replicas that
    // have p places each is n p. `cube` is 128 * 128 * 128 = 2 097 152 values: over, and `Unavailable` once the first of its 128
    // rows (16 384 values) shows it (a count of one `par~` at a time sees 128, 128 and 128 and builds 2 million values).
    // `wide` is 2000 rows of `[x; 1000]`, 2 000 000: over too. `small` is 32 * 32 * 32 = 32 768, under: its last value
    // is x + 31 = 36 for x = 5.
    let src = "flow cube(x: I64 at sample) -> I64 at sample {
  (par i in 0 ..< 128 { par j in 0 ..< 128 { par k in 0 ..< 128 { x + ((k) as I64) } } })[0][0][0]
}
flow wide(x: I64 at sample) -> I64 at sample { (par i in 0 ..< 2000 { [x; 1000] })[0][0] }
flow small(x: I64 at sample) -> I64 at sample {
  (par i in 0 ..< 32 { par j in 0 ..< 32 { par k in 0 ..< 32 { x + ((k) as I64) } } })[31][31][31]
}";
    let run = |name: &'static str| {
        with_flow(src, name, |view, def| {
            let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
            let x = [Value::int(IntKind::I64, 5)];
            me.process(&[], &[("x", &x[..])], 1, None)
        })
    };
    for name in ["cube", "wide"] {
        let r = run(name);
        assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{name}: {r:?}");
    }
    assert!(matches!(&run("small"), Ok(o) if o[0].same(&Value::int(IntKind::I64, 36))), "{:?}", run("small"));
}

#[test]
fn a_match_arm_binding_read_by_a_block_or_init_argument_is_unavailable_and_not_an_internal_error() {
    // S-1131 (provisional reading (1) of the evaluator: it does not evaluate it): a `match~` arm is evaluated in the `sample` stage,
    // so a binding of it (`n`) has no value in the `block` stage of an instance in the arm, which reads the argument of its
    // `block` input, or at `init`, which reads those of the `init` inputs of an instance or a delay. The spec does not say
    // at which stage the binding's value is made: that is not an internal error of the evaluator but a form it has not. No
    // value is written (the spec has none).
    // The same forms that do not read the binding of an arm do run: `k` itself (the `block` argument `lp~(x, k)` is 3.0,
    // x * g = 2.0 * 3.0 = 6.0), a `match` inside the argument that binds its own `m`, the binding read in a `sample` input (`mul~`
    // multiplies x = 2.0 by n = 3.0: 6.0), and the `init` of a delay that reads `k` (`prev~(x, 3.0)` starts from 3.0).
    let src = "flow lp(x: F64 at sample, g: F64 at block) -> F64 at sample { x * g }
flow mul(x: F64 at sample, y: F64 at sample) -> F64 at sample { x * y }
flow st(a: F64 at init, x: F64 at sample) -> F64 at sample { x + a }
flow blk(x: F64 at sample, k: U32 at block) -> F64 at sample { match~ k { n => lp~(x, (n as F64)), } }
flow blk_k(x: F64 at sample, k: U32 at block) -> F64 at sample { match~ k { n => lp~(x, (k as F64)), } }
flow blk_own(x: F64 at sample, k: U32 at block) -> F64 at sample { lp~(x, match k { m => (m as F64), }) }
flow blk_sample(x: F64 at sample, k: U32 at block) -> F64 at sample { match~ k { n => mul~(x, (n as F64)), } }
flow ini_delay(k: U32 at init, x: F64 at sample) -> F64 at sample { match~ k { n => prev~(x, (n as F64)), } }
flow ini_inst(k: U32 at init, x: F64 at sample) -> F64 at sample { match~ k { n => st~((n as F64), x), } }
flow ini_k(k: U32 at init, x: F64 at sample) -> F64 at sample { match~ k { n => prev~(x, (k as F64)), } }";
    let k = |name| (name, Value::int(IntKind::U32, 3));
    let unavailable = |r: Result<Vec<f64>, Stop>| matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. }));
    let by_block = |name: &'static str| open_run(src, name, vec![], vec![k("k")], &[2.0]);
    let by_init = |name: &'static str| open_run(src, name, vec![k("k")], vec![], &[2.0]);
    assert!(unavailable(by_block("blk")), "{:?}", by_block("blk"));
    assert!(unavailable(by_init("ini_delay")), "{:?}", by_init("ini_delay"));
    assert!(unavailable(by_init("ini_inst")), "{:?}", by_init("ini_inst"));
    same64(&by_block("blk_k").expect("a block argument that reads k"), &[6.0]);
    same64(&by_block("blk_own").expect("a match of the argument that binds its own"), &[6.0]);
    same64(&by_block("blk_sample").expect("a sample argument that reads the arm binding"), &[6.0]);
    same64(&by_init("ini_k").expect("an init argument that reads k"), &[3.0]);
}
