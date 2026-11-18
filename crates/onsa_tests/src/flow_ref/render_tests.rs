//! The tests of `render` and of the outcome of a call (W7-18 U1d): the stage a panic is at (`init`, `block`, the frame
//! `n` of a `process`, §9.2, §11.6) and `render` as `init` and one `process` (§11.6, a call of 0 frames too). The values
//! and the stages are worked out by hand from the spec, in the comment of each test.

use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::expr::Stop;
use super::expr_tests::i32v;
use super::flow::{Call, Instance, Outcome, PanicAt};
use super::flow_tests::{counted, counter, host, with_flow};
use super::host::TableHost;
use super::scalar::{Fault, PanicKind};
use super::state_tests::{f32s, floats};
use super::value::Value;

/// An outcome as the tests compare it: the integers of the outputs, or the panic with its stage, kind and the text of the
/// expression it is at, or the fault that is no outcome.
#[derive(Debug, PartialEq)]
enum Seen {
    Ints(Vec<i128>),
    Floats(Vec<f32>),
    Panic(PanicAt, PanicKind, String),
    Error(Fault),
}

fn seen(src: &str, r: Result<Outcome, Stop>) -> Seen {
    let text = |s: &Stop| src[s.at.start as usize..s.at.end as usize].to_string();
    match r {
        Ok(Outcome::Ok(outs)) => match outs.first() {
            Some(Value::F32(_)) => Seen::Floats(f32s(&outs)),
            _ => Seen::Ints(
                outs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { panic!("{v:?}") }).collect(),
            ),
        },
        Ok(Outcome::Panic { at, stop: Stop { fault: Fault::Panic(kind), at: span } }) => {
            Seen::Panic(at, kind, text(&Stop { fault: Fault::Panic(kind), at: span }))
        }
        Ok(Outcome::Panic { stop, .. }) => panic!("a panic outcome that is no panic: {stop:?}"),
        Err(stop) => Seen::Error(stop.fault),
    }
}

fn ints(xs: &[i128]) -> Vec<Value> {
    xs.iter().map(|x| i32v(*x)).collect()
}

/// `render` of the flow `name` of `src` for the `init` input `a`, the `block` input `p` and the column `xs`.
fn render_ints(src: &str, name: &'static str, (a, p): (i128, i128), xs: &[i128]) -> Seen {
    let (text, xs) = (src.to_string(), ints(xs));
    with_flow(src, name, move |view, def| {
        let r = Instance::render(
            view,
            def,
            48000.0,
            &Call { config: &[("a", i32v(a))], params: &[("p", i32v(p))], inputs: &[("x", &xs[..])], frames: None },
            None,
        );
        seen(&text, r)
    })
}

/// A flow with a division by an input of each clock, and a flow that calls it: the stage of a panic is the stage of the
/// `let` that makes it, whatever the call it is in.
const STAGES: &str = "flow stages(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample {
  let k = 10 / a
  let q = 100 / p
  let s = 1000 / x
  k + q + s
}
flow top(a: I32 at init, p: I32 at block, x: I32 at sample) -> I32 at sample { stages~(a, p, x) + 1 }
";

#[test]
fn a_call_without_a_panic_is_the_outputs_and_a_panic_is_the_stage_it_is_at() {
    // §9.2, §11.6: a = 5 gives k = 10 / 5 = 2 and p = 10 gives q = 100 / 10 = 10, and the frames x = 1000, 500, 250 give
    // s = 1, 2, 4: the outputs are k + q + s = 13, 14, 16 (the flow that calls it adds 1: 14, 15, 17). A zero for the input of
    // a clock is the panic of that stage: a = 0 the panic of `init`, p = 0 that of `block` (the frames are not run), and a
    // zero in the frame n is `Sample(n)`: x = 1000, 500, 0, 250 is `Sample(2)`, and the first of two zeros wins. The stage
    // that comes first wins when more than one would panic (init before block before sample), and it is the same in the
    // flow that is called (the child's expressions are the places).
    for (name, add) in [("stages", 0), ("top", 1)] {
        let at = |a, p, xs: &[i128]| render_ints(STAGES, name, (a, p), xs);
        assert_eq!(at(5, 10, &[1000, 500, 250]), Seen::Ints(vec![13 + add, 14 + add, 16 + add]), "{name}");
        let div = PanicKind::DivZero;
        assert_eq!(at(0, 10, &[1000]), Seen::Panic(PanicAt::Init, div, "10 / a".into()), "{name}");
        assert_eq!(at(0, 0, &[0]), Seen::Panic(PanicAt::Init, div, "10 / a".into()), "{name}: init before block");
        assert_eq!(at(5, 0, &[1000, 500]), Seen::Panic(PanicAt::Block, div, "100 / p".into()), "{name}");
        assert_eq!(at(5, 0, &[0]), Seen::Panic(PanicAt::Block, div, "100 / p".into()), "{name}: block before sample");
        let frame = |n| Seen::Panic(PanicAt::Sample(n), div, "1000 / x".into());
        assert_eq!(at(5, 10, &[1000, 500, 0, 250]), frame(2), "{name}");
        assert_eq!(at(5, 10, &[0, 0]), frame(0), "{name}: the first of two");
        assert_eq!(at(5, 10, &[1000, 500, 250, 0]), frame(3), "{name}: the last frame");
    }
}

#[test]
fn a_call_of_0_frames_has_its_block_stage_and_so_its_panic() {
    // §11.6: "a call of length 0 evaluates the `block` stage once, and not the `sample` stage": p = 0 with no frame is the
    // panic of `block` (no frame has made it first), and p = 10 is the empty outputs, not a panic.
    assert_eq!(
        render_ints(STAGES, "stages", (5, 0), &[]),
        Seen::Panic(PanicAt::Block, PanicKind::DivZero, "100 / p".into())
    );
    assert_eq!(render_ints(STAGES, "stages", (5, 10), &[]), Seen::Ints(vec![]));
}

#[test]
fn the_frame_of_a_panic_is_counted_in_its_call_and_not_from_init() {
    // §11.6: the frame `n` of `Sample(n)` is the n-th of the `process` that panics (the time `tick` goes on across calls). A
    // call of 2 frames (x = 1000, 500: 13, 14... with a = 5, p = 10 the outputs are 13, 14), then one of x = 1000, 0 is
    // `Sample(1)`, not `Sample(3)`; the `process` that returns the stop gives the same stop and no stage.
    let text = STAGES.to_string();
    let (first, second, third) = with_flow(STAGES, "stages", move |view, def| {
        let mut me = Instance::init(view, def, 48000.0, &[("a", i32v(5))], None).expect("init");
        let (p, one) = ([("p", i32v(10))], ints(&[1000, 500]));
        let first = me.process_outcome(&p, &[("x", &one[..])], 2, None);
        let two = ints(&[1000, 0]);
        let second = me.process_outcome(&p, &[("x", &two[..])], 2, None);
        let third = me.process(&p, &[("x", &two[..])], 2, None).map(Outcome::Ok);
        (seen(&text, first), seen(&text, second), seen(&text, third))
    });
    assert_eq!(first, Seen::Ints(vec![13, 14]));
    assert_eq!(second, Seen::Panic(PanicAt::Sample(1), PanicKind::DivZero, "1000 / x".into()));
    assert_eq!(third, Seen::Error(Fault::Panic(PanicKind::DivZero)));
}

#[test]
fn a_fault_that_is_no_panic_is_an_error_and_not_an_outcome() {
    // An unavailable form (a string literal) is `Err`, whatever the stage: it is not the program's.
    let src = "flow p(x: F32 at sample) -> F32 at sample { x + F32.round_from(\"ab\".len()) }";
    let text = src.to_string();
    let got = with_flow(src, "p", move |view, def| {
        let xs = floats(&[1.0]);
        seen(&text, Instance::render(view, def, 48000.0, &Call { inputs: &[("x", &xs[..])], ..Call::default() }, None))
    });
    assert!(matches!(got, Seen::Error(Fault::Unavailable(_))), "{got:?}");
}

#[test]
fn a_column_of_another_length_than_the_frames_is_a_panic_of_the_start_of_the_call_and_moves_no_state() {
    // §11.6: the lengths of the `sample` spans must be equal, and "differ is a panic; the lengths are compared at the start of
    // the call, once, before any state is moved". `sum` is `s = x + prev~(^s)` with `b = cb(p)` of `block` and the output `s`:
    // a call of x = 1, 2 is 1, 3 (`Ok`); one of the columns x = 1, 2, 3 with `frames` 2 (and one of x = 1, 2 with `frames` 3)
    // is the panic `Length` at `PanicAt::Start`, whichever is longer; it did not move the state: the `block` stage has not run
    // (`cb` was called once, by the first call), the time is still 2, and the next call of x = 4 gives 3 + 4 = 7.
    // `Fault::Panic(Length)` is also what `process` (no outcome) returns.
    counter!(row_b, N_B);
    let src = format!(
        "{}flow sum(p: I32 at block, x: I32 at sample) -> I32 at sample {{
  let b = cb(p)
  let s = x + prev~(^s) + 0 * b
  s
}}",
        counted(&["cb"])
    );
    let got = with_flow(&src, "sum", move |view, def| {
        let mut t = TableHost::default().with("t.cb", row_b);
        let mut me = Instance::init(view, def, 48000.0, &[], None).expect("init");
        let p = [("p", i32v(1))];
        let mut call = |me: &mut Instance, xs: &[i128], frames| {
            let col = ints(xs);
            me.process_outcome(&p, &[("x", &col[..])], frames, host(&mut t))
        };
        let first = call(&mut me, &[1, 2], 2);
        let (longer, shorter) = (call(&mut me, &[1, 2, 3], 2), call(&mut me, &[1, 2], 3));
        let state = (N_B.load(Relaxed), me.ctx.tick);
        let next = call(&mut me, &[4], 1);
        let as_error = me.process(&p, &[("x", &ints(&[1])[..])], 2, host(&mut t)).map(|_| ());
        (first, longer, shorter, state, next, as_error)
    });
    assert!(
        matches!(&got.0, Ok(Outcome::Ok(o)) if matches!(o[..], [Value::Int(_, 1, _), Value::Int(_, 3, _)])),
        "{:?}",
        got.0
    );
    for r in [&got.1, &got.2] {
        let Ok(Outcome::Panic { at, stop }) = r else { panic!("not a panic outcome: {r:?}") };
        assert_eq!((*at, stop.fault), (PanicAt::Start, Fault::Panic(PanicKind::Length)));
    }
    assert_eq!(got.3, (1, 2));
    assert!(matches!(&got.4, Ok(Outcome::Ok(o)) if matches!(o[..], [Value::Int(_, 7, _)])), "{:?}", got.4);
    assert_eq!(got.5.map_err(|s| s.fault), Err(Fault::Panic(PanicKind::Length)));
}

#[test]
fn render_is_init_and_one_process_and_the_init_input_reaches_the_output() {
    // §11.6: `render(cfg, params, ..)` is `init(cfg)` and one `process`. `ramp` has p[0] = start (the `init` input) and
    // p[n + 1] = p[n] + step (`block`), and its output is p. start = 2.0, step = 0.5 over 4 frames: 2.0, 2.5, 3.0, 3.5;
    // start = 10.0, step = -1.0 over 3: 10.0, 9.0, 8.0. It is what `init` then `process` give (one call of 4 frames).
    let src = "flow ramp(start: F32 at init, step: F32 at block) -> F32 at sample {
  let p = prev~(^q, start)
  let q = p + step
  p
}";
    let text = src.to_string();
    let got = with_flow(src, "ramp", move |view, def| {
        let render = |start, step, n| {
            let r = Instance::render(
                view,
                def,
                48000.0,
                &Call { config: &[("start", start)], params: &[("step", step)], frames: Some(n), ..Call::default() },
                None,
            );
            seen(&text, r)
        };
        let by_hand = {
            let mut me = Instance::init(view, def, 48000.0, &[("start", Value::F32(2.0))], None).expect("init");
            Seen::Floats(f32s(&me.process(&[("step", Value::F32(0.5))], &[], 4, None).expect("process")))
        };
        (render(Value::F32(2.0), Value::F32(0.5), 4), by_hand, render(Value::F32(10.0), Value::F32(-1.0), 3))
    });
    assert_eq!(got.0, Seen::Floats(vec![2.0, 2.5, 3.0, 3.5]));
    assert_eq!(got.0, got.1);
    assert_eq!(got.2, Seen::Floats(vec![10.0, 9.0, 8.0]));
}

#[test]
fn render_makes_the_init_once_the_block_stage_once_and_the_frames_it_is_given() {
    // §11.6: `init` once, `block` once for the whole call (the `block` input is constant over it), `sample` for each frame,
    // and with 0 frames the first two only. a = 1000 (`init`), p = 100 (`block`), the `let` of `sample` counts its frames:
    // c = 1, 2, 3, so the output k + b + s = 1000 + 100 + c: 1101, 1102, 1103; the counts are [1, 1, 3]; for 0 frames the
    // outputs are empty and the counts [1, 1, 0].
    counter!(row_i, N_I);
    counter!(row_b, N_B);
    counter!(row_s, N_S);
    let src = format!(
        "{}flow cnt(a: I32 at init, p: I32 at block) -> I32 at sample {{
  let k = ci(a)
  let b = cb(p)
  let c = prev~(^c) + 1
  let s = cs(c)
  k + b + s
}}",
        counted(&["ci", "cb", "cs"])
    );
    let counts = || [&N_I, &N_B, &N_S].map(|c| c.swap(0, Relaxed));
    let text = src.clone();
    let got = with_flow(&src, "cnt", move |view, def| {
        let mut t = TableHost::default().with("t.ci", row_i).with("t.cb", row_b).with("t.cs", row_s);
        let mut at = |n| {
            let call =
                Call { config: &[("a", i32v(1000))], params: &[("p", i32v(100))], frames: Some(n), ..Call::default() };
            let r = Instance::render(view, def, 48000.0, &call, host(&mut t));
            (seen(&text, r), counts())
        };
        (at(3), at(0))
    });
    assert_eq!(got.0, (Seen::Ints(vec![1101, 1102, 1103]), [1, 1, 3]));
    assert_eq!(got.1, (Seen::Ints(vec![]), [1, 1, 0]));
}

#[test]
fn render_takes_the_frames_from_the_columns_of_a_flow_with_sample_inputs_and_from_frames_otherwise() {
    // §11.6: "a flow with `sample` inputs takes no `frames`, and uses the length of the `Span`s". `dbl` of x = 1, 2, 3, 4, 5 and
    // g = 3.0 is 3, 6, 9, 12, 15 (5 frames, from the column); with a column of 0 values the outputs are empty. A `frames` for
    // a flow that has a `sample` input, and none for one that has not, are not a call the API has: an error of the call.
    let src = "flow dbl(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }
flow none(g: F32 at block) -> F32 at sample { g }";
    let text = src.to_string();
    let got = with_flow(src, "dbl", {
        let text = text.clone();
        move |view, def| {
            let g = [("g", Value::F32(3.0))];
            let col = floats(&[1.0, 2.0, 3.0, 4.0, 5.0]);
            let render = |col: &[Value], frames| {
                seen(
                    &text,
                    Instance::render(
                        view,
                        def,
                        48000.0,
                        &Call { params: &g, inputs: &[("x", col)], frames, ..Call::default() },
                        None,
                    ),
                )
            };
            (render(&col, None), render(&[], None), render(&col, Some(5)))
        }
    });
    assert_eq!(got.0, Seen::Floats(vec![3.0, 6.0, 9.0, 12.0, 15.0]));
    assert_eq!(got.1, Seen::Ints(vec![]));
    assert!(matches!(got.2, Seen::Error(Fault::Internal(_))), "{:?}", got.2);
    let got = with_flow(src, "none", move |view, def| {
        let g = [("g", Value::F32(3.0))];
        let r = |frames| {
            seen(&text, Instance::render(view, def, 48000.0, &Call { params: &g, frames, ..Call::default() }, None))
        };
        (r(Some(2)), r(None))
    });
    assert_eq!(got.0, Seen::Floats(vec![3.0, 3.0]));
    assert!(matches!(got.1, Seen::Error(Fault::Internal(_))), "{:?}", got.1);
}
