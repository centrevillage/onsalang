//! The tests of the instance of a flow (W7-18 U1a): the stage each `let` is made in (§11.3), the order of the `let`s
//! (§11.2), `at` (§11.3), the entries `init` and `process` (§11.6, a call of 0 frames too) and the counter of §11.9.
//! The values and the counts are worked out by hand from the spec, in the comment of each test.
//!
//! The evaluator has no side effect to count, so the tests count the calls of a function the host gives (`counted`): a
//! function with a statement in its body is not evaluated by the evaluator but handed to the host (`call_tests.rs`), and
//! the host's row adds one to the count of its own test and gives back its argument.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use onsa_sema::DefId;
use onsa_syntax::ast::ExprKind;

use super::expr::Stop;
use super::expr_tests::{def_named, i32v, is, panic_at, with_checked};
use super::flow::{Clock, Ctx, Instance, clock_of, join};
use super::host::{FnHost, TableHost};
use super::scalar::{Fault, PanicKind};
use super::sema_view::View;
use super::value::Value;

/// A static count and the row of the host that adds one to it and gives its first argument back.
macro_rules! counter {
    ($row:ident, $count:ident) => {
        static $count: AtomicU32 = AtomicU32::new(0);
        fn $row(a: &[Value]) -> Result<Value, Fault> {
            $count.fetch_add(1, Relaxed);
            Ok(a[0].clone())
        }
    };
}
pub(super) use counter;

/// `rt fn <name>(x: I32) -> I32`s that have a statement, so that the evaluator hands them to the host.
pub(super) fn counted(names: &[&str]) -> String {
    names.iter().map(|n| format!("rt fn {n}(x: I32) -> I32 {{\n  var d = x\n  d = d + 0\n  d\n}}\n")).collect()
}

pub(super) fn host(h: &mut TableHost) -> Option<&mut dyn FnHost> {
    Some(h)
}

/// Check `src` and run `go` on the flow `name` (on the thread of a large stack: the check and the evaluation are).
pub(super) fn with_flow<T: Send + 'static>(
    src: &str,
    name: &'static str,
    go: impl FnOnce(View, DefId) -> T + Send + 'static,
) -> T {
    with_checked(src, true, move |a| go(View::new(a), def_named(a, name)))
}

fn counts(cs: [&AtomicU32; 3]) -> [u32; 3] {
    cs.map(|c| c.load(Relaxed))
}

#[test]
fn a_let_is_made_at_the_stage_of_its_clock() {
    // §11.3: a value of `init` is made once at `init`, one of `block` once for each call of `process`, one of `sample`
    // for each frame. `k + q + s` reads the three: it is of `sample`, and the output of a frame is made after its `let`s.
    counter!(row_i, N_I);
    counter!(row_b, N_B);
    counter!(row_s, N_S);
    let src = format!(
        "{}flow f(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let k = bi(a)
  let q = bb(p)
  let s = bs(x)
  k + q + s
}}",
        counted(&["bi", "bb", "bs"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bi", row_i).with("t.bb", row_b).with("t.bs", row_s);
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(1000))], host(&mut table)).expect("init");
        // The clock of each `let` and of the output (`k + q + s`, the fastest of the three is `sample`).
        assert_eq!(me.clocks(), [Clock::Init, Clock::Block, Clock::Sample, Clock::Sample]);
        // After `init`: the `init` one has been made, the others not.
        assert_eq!(counts([&N_I, &N_B, &N_S]), [1, 0, 0]);
        assert_eq!(me.ctx, Ctx { sample_rate: 48000.0, tick: 0 });
        // Three frames, `p = 100`: 1000 + 100 + x for x = 1, 2, 3; the `block` one once, the `sample` one three times.
        let xs = [i32v(1), i32v(2), i32v(3)];
        let outs = me.process(&[("p", i32v(100))], &[("x", &xs[..])], 3, host(&mut table)).expect("process");
        assert!(outs.iter().zip([1101, 1102, 1103]).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
        assert_eq!(counts([&N_I, &N_B, &N_S]), [1, 1, 3]);
        assert_eq!(me.ctx.tick, 3);
        // The next call: `block` once again, `init` not again, and the value of `init` is still read: 1000 + 200 + 10.
        let outs = me.process(&[("p", i32v(200))], &[("x", &[i32v(10)])], 1, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(1210)), "{outs:?}");
        assert_eq!(counts([&N_I, &N_B, &N_S]), [1, 2, 4]);
        // A call of 0 frames is a call: the `block` one is made once (§11.6), the `sample` one is not, and no frame is done.
        let outs = me.process(&[("p", i32v(300))], &[("x", &[])], 0, host(&mut table)).expect("process");
        assert!(outs.is_empty());
        assert_eq!(counts([&N_I, &N_B, &N_S]), [1, 3, 4]);
        assert_eq!(me.ctx, Ctx { sample_rate: 48000.0, tick: 4 });
    });
}

#[test]
fn a_let_of_a_faster_clock_reads_the_latest_value_of_a_slower_one() {
    // `a` is of `block`, `b` and `c` of `sample`: `c = b * a`, and `b = a + x` in each frame reads the `a` of the call.
    // Call 1: p = 1.5, a = 3.0; x = 1.0, 2.0: b = 4.0, 5.0; c = 12.0, 15.0.
    // Call 2: p = 0.5, a = 1.0; x = 4.0: b = 5.0; c = 5.0 (the `a` of call 1 is not read again).
    let src = "flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let a = p * 2.0
  let b = a + x
  let c = b * a
  c
}";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 44100.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Block, Clock::Sample, Clock::Sample, Clock::Sample]);
        let xs = [Value::F32(1.0), Value::F32(2.0)];
        let outs = me.process(&[("p", Value::F32(1.5))], &[("x", &xs[..])], 2, None).expect("process");
        assert!(outs[0].same(&Value::F32(12.0)) && outs[1].same(&Value::F32(15.0)), "{outs:?}");
        let outs = me.process(&[("p", Value::F32(0.5))], &[("x", &[Value::F32(4.0)])], 1, None).expect("process");
        assert!(outs[0].same(&Value::F32(5.0)), "{outs:?}");
    });
}

#[test]
fn the_lets_run_in_the_order_they_are_written_and_the_stages_in_the_order_of_the_clocks() {
    // §11.2: in the order written. Both `let`s are of `block`: with z = 0 and w = 0 the first to panic is `1 / z`; with
    // z = 1 and w = 0 it is `2 / w`; with z = 1 and w = 1 the output is 1 + 2 = 3.
    let both = "flow f(z: I32 at block, w: I32 at block) -> I32 at sample {
  let a = 1 / z
  let b = 2 / w
  a + b
}";
    with_flow(both, "f", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        for (z, w, at) in [(0, 0, "1 / z"), (1, 0, "2 / w")] {
            let r = me.process(&[("z", i32v(z)), ("w", i32v(w))], &[], 1, None);
            assert_eq!(panic_at(&r.map(|_| Value::Unit), both), (PanicKind::DivZero, at.to_string()));
        }
        let outs = me.process(&[("z", i32v(1)), ("w", i32v(1))], &[], 2, None).expect("process");
        assert!(outs.iter().all(|o| is(&Ok(o.clone()), &i32v(3))), "{outs:?}");
    });
    // §11.3, §11.9: the `block` stage of a call is before its frames, whatever the order written: `s` (of `sample`) is
    // written first, and with z = 0 and y = 0 the panic is that of `7 / z` (block); with z = 1 it is `5 / y` (sample).
    let stages = "flow f(z: I32 at block, y: I32 at sample) -> I32 at sample {
  let s = 5 / y
  let b = 7 / z
  s + b
}";
    with_flow(stages, "f", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        for (z, at) in [(0, "7 / z"), (1, "5 / y")] {
            let r = me.process(&[("z", i32v(z))], &[("y", &[i32v(0)])], 1, None);
            assert_eq!(panic_at(&r.map(|_| Value::Unit), stages), (PanicKind::DivZero, at.to_string()));
        }
        // z = 1, y = 2, 5: 5 / 2 + 7 = 9 and 5 / 5 + 7 = 8 (the division truncates toward zero, §3.4).
        let r = me.process(&[("z", i32v(1))], &[("y", &[i32v(2), i32v(5)])], 2, None).expect("process");
        assert!(is(&Ok(r[0].clone()), &i32v(9)) && is(&Ok(r[1].clone()), &i32v(8)), "{r:?}");
    });
}

#[test]
fn a_let_of_constants_is_made_once_at_init() {
    // `k = 2 * 3` and `bc(k + 1)` read no input: the clock of a constant, made at `init` once (7 comes back from `bc`).
    // The output `x * m` is of `sample`: 1 * 7 and 2 * 7 in the first call, 3 * 7 in the second; `bc` was called once.
    counter!(row_c, N_C);
    let src = format!(
        "{}flow f(x: I32 at sample) -> I32 at sample {{
  let k = 2 * 3
  let m = bc(k + 1)
  x * m
}}",
        counted(&["bc"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bc", row_c);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        assert_eq!(me.clocks(), [Clock::Const, Clock::Const, Clock::Sample]);
        assert_eq!(N_C.load(Relaxed), 1);
        let outs = me.process(&[], &[("x", &[i32v(1), i32v(2)])], 2, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(7)) && is(&Ok(outs[1].clone()), &i32v(14)), "{outs:?}");
        let outs = me.process(&[], &[("x", &[i32v(3)])], 1, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(21)), "{outs:?}");
        assert_eq!(N_C.load(Relaxed), 1);
    });
}

#[test]
fn at_gives_the_clock_k_and_changes_neither_the_value_nor_the_stage_of_what_it_reads() {
    // §11.3, S-1196: `e at k` has the clock `k` for the checks and for what it decides; the value does not change (5) and
    // the stage is that of its values when they are of the parameter kinds alone: `a` is `bq(p)`, of `block` (made once for
    // each call). `q = a at sample` reads `a` (`block`) and nothing of a tick, so it is of `block` too (its read clock is
    // `sample`), and so are `r` and the output: `bq` is called once for each call, not for each frame.
    counter!(row_q, N_Q);
    let src = format!(
        "{}flow f(p: I32 at block) -> I32 at sample {{
  let a = bq(p)
  let q = a at sample
  let r = q at sample
  r
}}",
        counted(&["bq"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bq", row_q);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        assert_eq!(me.clocks(), [Clock::Block; 4]);
        let outs = me.process(&[("p", i32v(5))], &[], 4, host(&mut table)).expect("process");
        assert!(outs.len() == 4 && outs.iter().all(|o| is(&Ok(o.clone()), &i32v(5))), "{outs:?}");
        assert_eq!(N_Q.load(Relaxed), 1);
        me.process(&[("p", i32v(6))], &[], 2, host(&mut table)).expect("process");
        assert_eq!(N_Q.load(Relaxed), 2);
    });
}

#[test]
fn a_let_of_the_parameter_kinds_made_faster_with_at_has_the_stage_of_its_values() {
    // §11.3, S-1196: `ps = p at sample` is of `block` (the stage its value decides; `at` gives it the clock `sample` for what reads it),
    // so `r = 100 / ps` is made once for each call, a call of 0 frames too: with p = 0 it panics at `100 / ps` there. With p = 4 and
    // x = 1, 2: 100 / 4 = 25, so 26 and 27.
    let src = "flow f(p: I32 at block, x: I32 at sample) -> I32 at sample {
  let ps = p at sample
  let r = 100 / ps
  x + r
}";
    with_flow(src, "f", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Block, Clock::Block, Clock::Sample]);
        let r = me.process(&[("p", i32v(0))], &[("x", &[])], 0, None);
        assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, "100 / ps".to_string()));
        let outs = me.process(&[("p", i32v(4))], &[("x", &[i32v(1), i32v(2)])], 2, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(26)) && is(&Ok(outs[1].clone()), &i32v(27)), "{outs:?}");
    });
    // `q = a at block` takes a value of `init` to the clock `block`, and it is a value of `init`: with a = 0, `100 / q` is made by `init`.
    let src = "flow g(a: I32 at init, x: I32 at sample) -> I32 at sample {
  let q = a at block
  let r = 100 / q
  x + r
}";
    with_flow(src, "g", move |view, def| {
        let r = Instance::init(view, def, 48000.0, &[("a", i32v(0))], None).map(|_| Value::Unit);
        assert_eq!(panic_at(&r, src), (PanicKind::DivZero, "100 / q".to_string()));
    });
    // `K at init` takes a constant to the clock `init`: the `let` of it is a constant (no stage), and `x + k` is of `sample`.
    let src = "const K: I32 = 3
flow h(x: I32 at sample) -> I32 at sample {
  let k = K at init
  x + k
}";
    with_flow(src, "h", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        assert_eq!(me.clocks(), [Clock::Const, Clock::Sample]);
        let outs = me.process(&[], &[("x", &[i32v(4)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(7)), "{outs:?}");
    });
}

#[test]
fn a_conditional_form_is_made_at_the_clock_its_condition_is_decided_by_with_at_counted() {
    // §11.3, S-1166, S-1196: the value of `g` is of the parameter kinds alone, so it is of `block` (its read clock is `sample`); a
    // conditional form is made at the clock its conditions decide, `at` counted, so `if g { .. }` and `if (d != 0) at sample { .. }`
    // are of `sample` whole, though all their values are of `block`; `(d + 1) at sample` is of `block`; a tick read keeps its clock.
    let src = "flow f(d: I32 at block, x: I32 at sample) -> I32 at sample {
  let g = (d != 0) at sample
  let y = if g { 100 / (d - 1) } else { 0 }
  let z = if (d != 0) at sample { d } else { 0 }
  let w = (d + 1) at sample
  let t = prev~(x)
  x + y + z + w + t
}";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let [b, s] = [Clock::Block, Clock::Sample];
        assert_eq!(me.clocks(), [b, s, s, b, s, s]);
        // d = 1 does not divide in a call of 0 frames, and gives y = 0 for the frame that takes the else branch.
        me.process(&[("d", i32v(1))], &[("x", &[])], 0, None).expect("0 frames does not panic");
        let outs = me.process(&[("d", i32v(0))], &[("x", &[i32v(5)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(6)), "{outs:?}");
    });
}

#[test]
fn a_local_that_has_no_clock_is_an_internal_error_and_not_a_constant() {
    // A name of a local that the clocks so far do not have, and that is not bound inside the expression, is a leak of the
    // evaluator: an internal error, whatever the expression. With the clock of `x` known, `x` is of that clock.
    let src = "flow f(x: I32 at sample) -> I32 at sample { x }";
    with_flow(src, "f", |view, def| {
        let (body, decl) = (view.body(def).expect("body"), view.flow(def).expect("flow"));
        let ExprKind::Block(b) = &body.ast.expr(decl.body).kind else { panic!("a body") };
        let tail = b.tail.expect("the output");
        let r = clock_of(&body, &HashMap::new(), tail, tail);
        assert!(matches!(r, Err(Fault::Internal(_))), "{r:?}");
        let known = HashMap::from([(body.input("x").expect("x"), super::flow::Seen::both(Clock::Block))]);
        assert!(matches!(clock_of(&body, &known, tail, tail), Ok(Clock::Block)));
    });
}

#[test]
fn the_locals_of_a_let_that_is_taken_apart_have_the_clock_of_the_let() {
    // SPEC-GAP(S-1119): the locals of a `let` taken apart have the clock of the whole right side (the other reading is
    // that of the element each is bound to; `v` below would be of `block`). The values are the same, the counts differ.
    // `(a, b) = (p, p + 1)` reads `p` (block): `a` and `b` are of `block`, and so is `c = bd(a)` (made once for each
    // call: the clock of a name that is not known would be that of a constant, made at `init` with no `a` to read).
    // `((m, n), z) = ((a, 2), 3)` reads `a`: block too. `(u, v) = (x, p)` reads `x` (sample): both locals are of `sample`
    // (the whole expression has one clock, §11.3), so `w = be(v)` is made for each frame.
    // p = 10, x = 1, 2: a = 10, b = 11, c = 10, m = 10, n = 2, z = 3, v = 10, w = 10, u = x.
    // Output: x + b + c + m + n + z + w + u = 2x + 11 + 10 + 10 + 2 + 3 + 10 = 2x + 46, that is 48 and 50.
    counter!(row_d, N_D);
    counter!(row_e, N_E);
    let src = format!(
        "{}flow f(p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let (a, b) = (p, p + 1)
  let c = bd(a)
  let ((m, n), z) = ((a, 2), 3)
  let (u, v) = (x, p)
  let w = be(v)
  x + b + c + m + n + z + w + u
}}",
        counted(&["bd", "be"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bd", row_d).with("t.be", row_e);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        let b = Clock::Block;
        assert_eq!(me.clocks(), [b, b, b, Clock::Sample, Clock::Sample, Clock::Sample]);
        let outs = me.process(&[("p", i32v(10))], &[("x", &[i32v(1), i32v(2)])], 2, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(48)) && is(&Ok(outs[1].clone()), &i32v(50)), "{outs:?}");
        assert_eq!((N_D.load(Relaxed), N_E.load(Relaxed)), (1, 2));
    });
}

#[test]
fn only_the_branch_that_is_taken_is_made_and_a_generic_function_goes_to_the_host() {
    // §11.5: `match` and `if` evaluate the arm taken only. `g` is of `block` (sel is): sel = 1 takes `b1(2)`, so g = 2;
    // sel = 0 takes `b0(1)`, g = 1. `y` is of `sample`: `bp(x) * g` when x > 0, else `bn(x) * g`. `id` is generic, so
    // the host has it (`ident` gives back what it is given): `id(x)` is x. sel = 1 and x = 2, -3, 0, 4: y = 4, -6, 0, 8.
    // Counts: b0, b1, b2 = 0, 1, 0; bp = 2 (x = 2, 4); bn = 2 (x = -3, 0). Then sel = 0, x = 1: g = 1, y = 1; b0 = 1, bp = 3.
    counter!(row_0, N_0);
    counter!(row_1, N_1);
    counter!(row_2, N_2);
    counter!(row_p, N_P);
    counter!(row_n, N_N);
    counter!(row_id, N_ID);
    let src = format!(
        "{}rt fn id[T](x: T) -> T {{ x }}
flow f(sel: I32 at block, x: I32 at sample) -> I32 at sample {{
  let g = match sel {{ 0 => b0(1), 1 => b1(2), _ => b2(3) }}
  let y = if x > 0 {{ bp(id(x)) * g }} else {{ bn(x) * g }}
  y
}}",
        counted(&["b0", "b1", "b2", "bp", "bn"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.b0", row_0).with("t.b1", row_1).with("t.b2", row_2);
        table = table.with("t.bp", row_p).with("t.bn", row_n).with("t.id", row_id);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        let xs = [i32v(2), i32v(-3), i32v(0), i32v(4)];
        let outs = me.process(&[("sel", i32v(1))], &[("x", &xs[..])], 4, host(&mut table)).expect("process");
        let want = [4, -6, 0, 8];
        assert!(outs.iter().zip(want).all(|(o, w)| is(&Ok(o.clone()), &i32v(w))), "{outs:?}");
        assert_eq!([&N_0, &N_1, &N_2, &N_P, &N_N].map(|c| c.load(Relaxed)), [0, 1, 0, 2, 2]);
        assert_eq!(N_ID.load(Relaxed), 2);
        let outs = me.process(&[("sel", i32v(0))], &[("x", &[i32v(1)])], 1, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(1)), "{outs:?}");
        assert_eq!([&N_0, &N_1, &N_2, &N_P, &N_N].map(|c| c.load(Relaxed)), [1, 1, 0, 3, 2]);
    });
}

#[test]
fn the_counter_goes_up_for_each_frame_and_the_sample_rate_is_the_one_init_was_given() {
    // §11.9: the counter is 0 at `init` and goes up by one for each frame: 2 and 3 frames make 5, a call of 0 frames none.
    let src = "flow f(x: I32 at sample) -> I32 at sample { x }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 22050.0, &[], None).expect("init");
        let mut ticks = vec![me.ctx.tick];
        for n in [2, 3, 0, 1] {
            let column = vec![i32v(1); n];
            me.process(&[], &[("x", &column)], n, None).expect("process");
            ticks.push(me.ctx.tick);
        }
        assert_eq!(ticks, [0, 2, 5, 5, 6]);
        assert_eq!(me.ctx.sample_rate, 22050.0);
    });
}

#[test]
fn the_clock_of_two_operands_is_the_faster_of_them() {
    // §11.3: constant < init < block < sample, and an expression of two clocks has the faster; the same clock twice is
    // that clock. The ranks are written out here, and not read from the order of the type.
    use Clock::*;
    let all = [Const, Init, Block, Sample];
    let rank = |c: Clock| match c {
        Const => 0,
        Init => 1,
        Block => 2,
        Sample => 3,
    };
    for a in all {
        for b in all {
            let want = all[rank(a).max(rank(b))];
            assert_eq!(join(a, b), Some(want), "{a:?} {b:?}");
            assert_eq!(join(a, b), join(b, a), "{a:?} {b:?}");
        }
    }
}

/// What `Instance::init` of the flow `name` stops with, as the fault and the text of the source it stops at; none when
/// it makes the instance. `clean` is as for `with_checked`.
pub(super) fn init_stop(clean: bool, src: &str, name: &'static str) -> Option<(Fault, String)> {
    let text = src.to_string();
    with_checked(src, clean, move |a| {
        let r = Instance::init(View::new(a), def_named(a, name), 48000.0, &[], None);
        r.err().map(|s| (s.fault, text[s.at.start as usize..s.at.end as usize].to_string()))
    })
}

#[test]
fn a_form_the_evaluator_has_not_is_unavailable_at_init_and_not_in_a_frame() {
    // A string literal (`"abc".len()`, §11.5) is a form the evaluator has not: `Instance::init` stops with `Unavailable` at
    // the form, whatever the values, and so there is no instance for a call of 0 frames (which would have given an empty
    // answer) or for a frame (which would have stopped late) to be made on. One in the `init` argument of a delay (`g1`) is
    // found as well, and in a `let` after the delays (`after`), and in a flow that another calls (`up`, `deep`), at the
    // `init` of the instance that is made for it. Nothing in such a form is looked into.
    let src = "flow c6(x: F32 at sample) -> F32 at sample {
  let n = \"abc\".len()
  prev~(x) + F32.round_from(n)
}
flow g1(x: F32 at sample) -> F32 at sample { prev~(x, F32.round_from(\"ab\".len())) }
flow after(x: F32 at sample) -> F32 at sample {
  let a = prev~(x)
  let b = delay~(x, 2)
  let n = \"abcd\".len()
  a + b + F32.round_from(n)
}
flow up(x: F32 at sample) -> F32 at sample { c6~(x) }
flow deep(x: F32 at sample) -> F32 at sample { prev~(up~(x)) }";
    for (name, at) in
        [("c6", "\"abc\""), ("g1", "\"ab\""), ("after", "\"abcd\""), ("up", "\"abc\""), ("deep", "\"abc\"")]
    {
        let r = init_stop(true, src, name);
        assert!(matches!(&r, Some((Fault::Unavailable(_), text)) if text == at), "{name}: {r:?}");
    }
}

#[test]
fn a_body_the_check_rules_out_is_not_made_an_instance_of() {
    // E0401 (an `I32` and a `F32`), E0302 (a name that is not there), E0801 (a name before its `let`): the tables are
    // not whole, so `init` gives `Unavailable` and does not guess. A declaration that is not a flow is the same.
    for src in [
        "flow f(x: F32 at sample, n: I32 at sample) -> F32 at sample { x * n }",
        "flow f(x: F32 at sample) -> F32 at sample {\n  let a = x * nothing_here\n  a\n}",
        "flow f(x: F32 at sample) -> F32 at sample {\n  let a = b + x\n  let b = x\n  a\n}",
    ] {
        let r = with_checked(src, false, |a| {
            assert!(!a.diagnostics.is_empty(), "the check rules the source out");
            Instance::init(View::new(a), def_named(a, "f"), 48000.0, &[], None).err()
        });
        assert!(matches!(r, Some(Stop { fault: Fault::Unavailable(_), .. })), "{src}: {r:?}");
        // The stop is at the name of the declaration, not at a place that is no place of the source.
        let Some(Stop { at, .. }) = r else { unreachable!() };
        assert_eq!(&src[at.start as usize..at.end as usize], "f", "{src}");
    }
    let src = "rt fn f(x: I32) -> I32 { x }";
    let r = with_checked(src, true, |a| Instance::init(View::new(a), def_named(a, "f"), 48000.0, &[], None).err());
    assert!(matches!(r, Some(Stop { fault: Fault::Unavailable(_), .. })), "{r:?}");
    let Some(Stop { at, .. }) = r else { unreachable!() };
    assert_eq!(&src[at.start as usize..at.end as usize], "f");
}

#[test]
fn the_inputs_given_are_the_inputs_of_the_flow_by_clock() {
    // The number and the names of the inputs of each clock come from the types of §11.6: one left out, one added, one of
    // another clock are internal errors, not a value; a column of another length is the panic of the start of the call (§11.6).
    let src = "flow f(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample { a + p + x }";
    with_flow(src, "f", |view, def| {
        let internal = |r: Result<Instance<'_>, Stop>| matches!(r.err(), Some(Stop { fault: Fault::Internal(_), .. }));
        assert!(internal(Instance::init(view, def, 48000.0, &[], None)));
        assert!(internal(Instance::init(view, def, 48000.0, &[("a", i32v(1)), ("p", i32v(1))], None)));
        assert!(internal(Instance::init(view, def, 48000.0, &[("p", i32v(1))], None)));
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(1))], None).expect("init");
        let bad = |r: Result<Vec<Value>, Stop>| matches!(r, Err(Stop { fault: Fault::Internal(_), .. }));
        let xs = [i32v(1), i32v(2)];
        assert!(bad(me.process(&[], &[("x", &xs[..])], 2, None)), "p left out");
        assert!(bad(me.process(&[("p", i32v(1))], &[], 2, None)), "x left out");
        let long = me.process(&[("p", i32v(1))], &[("x", &xs[..])], 3, None);
        assert!(matches!(long, Err(Stop { fault: Fault::Panic(PanicKind::Length), .. })), "a column of 2 for 3 frames");
        assert!(
            bad(me.process(&[("a", i32v(1))], &[("x", &xs[..])], 2, None)),
            "an input of `init` given at `process`"
        );
        // A call of 0 frames checks the inputs of `sample` as a call of frames does.
        assert!(bad(me.process(&[("p", i32v(1))], &[], 0, None)), "x left out, 0 frames");
        assert!(bad(me.process(&[("p", i32v(1))], &[("zzz", &[])], 0, None)), "a name that is not an input, 0 frames");
        assert!(bad(me.process(&[("p", i32v(1))], &[("p", &[])], 0, None)), "an input of `block` as one of `sample`");
        assert!(bad(me.process(&[("p", i32v(1))], &[("x", &[]), ("zzz", &[])], 0, None)), "one added, 0 frames");
        assert!(me.process(&[("p", i32v(1))], &[("x", &[])], 0, None).is_ok());
        let outs = me.process(&[("p", i32v(10))], &[("x", &xs[..])], 2, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(12)) && is(&Ok(outs[1].clone()), &i32v(13)), "{outs:?}");
    });
}

#[test]
fn a_let_of_no_name_of_a_stage_is_made() {
    // S-1093 (1), decided: the value of a `let` is made at its stage, read or not.
    // A `let` that is not read is a `let _` (a named one is an E0309, §5.1). `let _ = 100 / n` (block) is read by
    // nothing, and n = 0 panics: at `process`, a call of 0 frames too. With n = 5 it is 20, and nothing else changes.
    // At `init` the same of an `init` input: a = 0 panics in `init`.
    let src = "flow f(a: I32 at init, n: I32 at block) -> I32 at sample {
  let _ = 100 / a
  let _ = 100 / n
  7
}";
    with_flow(src, "f", move |view, def| {
        let r = Instance::init(view, def, 48000.0, &[("a", i32v(0))], None);
        assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, "100 / a".to_string()));
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(5))], None).expect("init");
        let r = me.process(&[("n", i32v(0))], &[], 0, None);
        assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, "100 / n".to_string()));
        let outs = me.process(&[("n", i32v(5))], &[], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(7)), "{outs:?}");
    });
}

#[test]
fn the_output_of_a_stage_is_made_whether_or_not_it_is_read() {
    // S-1093 (1), decided: the same for the output expression, the last of the body, as for a `let` (§11.3: a
    // `let` or not, the stage and the result are the same). `100 / n` of `block` panics at `process` with n = 0, a call
    // of 0 frames too; with n = 5 a call of 0 frames makes none, and 2 frames give 20, 20. `100 / a` of `init` panics at
    // `init`.
    let src = "flow f(n: I32 at block) -> I32 at sample { 100 / n }
flow g(a: I32 at init, x: I32 at sample) -> I32 at sample { 100 / a }";
    with_flow(src, "f", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let r = me.process(&[("n", i32v(0))], &[], 0, None);
        assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, "100 / n".to_string()));
        assert!(me.process(&[("n", i32v(5))], &[], 0, None).expect("0 frames").is_empty());
        let outs = me.process(&[("n", i32v(5))], &[], 2, None).expect("process");
        assert!(outs.iter().all(|o| is(&Ok(o.clone()), &i32v(20))) && outs.len() == 2, "{outs:?}");
    });
    with_flow(src, "g", move |view, def| {
        let r = Instance::init(view, def, 48000.0, &[("a", i32v(0))], None);
        assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, "100 / a".to_string()));
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(4))], None).expect("init");
        let outs = me.process(&[], &[("x", &[i32v(1)])], 1, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(25)), "{outs:?}");
    });
}

#[test]
fn a_panic_of_the_clock_of_a_constant_is_the_panic_of_init_here() {
    // §11.3: a value of the clock of a constant is made at compile time, and a panic of it is E0419 in the spec. The
    // evaluator has no compile time: it makes the value at `init`, so `init` gives the panic (the entry of the comparison
    // reads it as an error of the compile time, W7-19). The `let` and the output expression are the same.
    let src = "flow f(x: I32 at sample) -> I32 at sample {
  let k = 1 / 0
  x + k
}
flow g(x: I32 at sample) -> I32 at sample { 100 / 0 }";
    for (name, at) in [("f", "1 / 0"), ("g", "100 / 0")] {
        with_flow(src, name, move |view, def| {
            let r = Instance::init(view, def, 48000.0, &[], None);
            assert_eq!(panic_at(&r.map(|_| Value::Unit), src), (PanicKind::DivZero, at.to_string()), "{name}");
        });
    }
}

#[test]
fn the_local_of_a_match_arm_has_no_clock_of_its_own() {
    // §11.3: the clock of an expression is that of the names it reads. `m = match sel { 0 => 1, n => bm(n) * 2 }` reads
    // `sel` (block): the `n` of the arm is bound inside the expression and has no clock to join, so `m` is of `block`,
    // and `bm` is called once for each call of `sel` that takes the second arm (the arm taken only is made, §11.5).
    // sel = 3, x = 1, 2: m = 6, output x + m = 7, 8 (bm: 1). sel = 0, x = 5: m = 1, 6 (bm: 1, the first arm). sel = 3
    // and no frame: bm: 2.
    counter!(row_m, N_M);
    let src = format!(
        "{}flow f(sel: I32 at block, x: I32 at sample) -> I32 at sample {{
  let m = match sel {{ 0 => 1, n => bm(n) * 2 }}
  x + m
}}",
        counted(&["bm"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bm", row_m);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        assert_eq!(me.clocks(), [Clock::Block, Clock::Sample]);
        let outs =
            me.process(&[("sel", i32v(3))], &[("x", &[i32v(1), i32v(2)])], 2, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(7)) && is(&Ok(outs[1].clone()), &i32v(8)), "{outs:?}");
        assert_eq!(N_M.load(Relaxed), 1);
        let outs = me.process(&[("sel", i32v(0))], &[("x", &[i32v(5)])], 1, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(6)), "{outs:?}");
        assert_eq!(N_M.load(Relaxed), 1);
        me.process(&[("sel", i32v(3))], &[("x", &[])], 0, host(&mut table)).expect("process");
        assert_eq!(N_M.load(Relaxed), 2);
    });
}

#[test]
fn the_locals_of_a_struct_pattern_are_of_the_clock_of_the_let_too() {
    // §11.2, §11.3 and the gap S-1119 as above: `P { a: a, b: (c, _) } = P { a: p, b: (p + 1, x) }` reads `p` and `x`:
    // `a` and `c` are of `sample` (the whole right side), so `bs(a)` is called for each frame. p = 10, x = 1, 2: a = 10,
    // c = 11, output a + c + x = 22, 23; two calls of `bs`.
    counter!(row_s, N_S);
    let src = format!(
        "{}struct P {{ a: I32, b: (I32, I32) }}
flow f(p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let P {{ a: a, b: (c, _) }} = P {{ a: p, b: (p + 1, x) }}
  let d = bs(a)
  d + c + x
}}",
        counted(&["bs"])
    );
    with_flow(&src, "f", |view, def| {
        let mut table = TableHost::default().with("t.bs", row_s);
        let mut me = Instance::init(view, def, 48000.0, &[], host(&mut table)).expect("init");
        assert_eq!(me.clocks(), [Clock::Sample; 3]);
        let outs = me.process(&[("p", i32v(10))], &[("x", &[i32v(1), i32v(2)])], 2, host(&mut table)).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(22)) && is(&Ok(outs[1].clone()), &i32v(23)), "{outs:?}");
        assert_eq!(N_S.load(Relaxed), 2);
    });
}

#[test]
fn the_counter_goes_round_at_2_pow_32() {
    // §11.9: the counter is a `U32` that goes round: from 2^32 - 1 one frame makes 0, and the next 1; the outputs are
    // those of the inputs (the counter is not read by the frame, and the frames after the round go on).
    let src = "flow f(x: I32 at sample) -> I32 at sample { x + 1 }";
    with_flow(src, "f", |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        me.ctx.tick = u32::MAX;
        let outs = me.process(&[], &[("x", &[i32v(1), i32v(2)])], 2, None).expect("process");
        assert!(is(&Ok(outs[0].clone()), &i32v(2)) && is(&Ok(outs[1].clone()), &i32v(3)), "{outs:?}");
        assert_eq!(me.ctx.tick, 1);
        me.ctx.tick = u32::MAX;
        me.process(&[], &[("x", &[i32v(1)])], 1, None).expect("process");
        assert_eq!(me.ctx.tick, 0);
    });
}
