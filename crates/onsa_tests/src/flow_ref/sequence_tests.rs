//! The calls of `init`, `process` and `reset` on a state, run by `walk.rs` (W7-19 U2b): the states a test holds by their
//! locals, the part of a buffer a `slice` is, and the stop at the first `Err`. Every value is worked out by hand from the
//! flows below (§11.6, §11.4: `prev~` gives 0.0 before the first value).

use super::flow::PanicAt;
use super::interp_host::Wrappers;
use super::walk::{Panic, Skip, TestRun, Verdict, run_case};
use onsa_driver::PackageInput;

// `acc` is a running sum: 1 2 3 4 gives 1 3 6 10. `gain` multiplies by a `block` value, `off` adds an `init` one, `inv` is
// 10 / x (it panics for 0), `ib` is x + 100 / n (it panics in `init` for n = 0), `closed` is E0200 (a `.reset_if~` in an `.up~` whose tick is past `sample / 2^31` there, S-1225, a limit of this version) and has a `par` of
// more elements than the evaluator holds (`Limits::most`), `chans` has two
// channels (an output of views).
const FLOWS: &str = "
flow acc(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
flow gain(g: F32 at block, x: F32 at sample) -> F32 at sample { x * g }
flow off(c: F32 at init, x: F32 at sample) -> F32 at sample { x + c }
flow inv(x: I32 at sample) -> I32 at sample { 10 / x }
flow ib(n: I32 at init, x: F32 at sample) -> F32 at sample {
  let k = 100 / n
  x + F32.round_from(k)
}
flow one() -> F32 at sample { 1.0 }
flow first2(x: F32 at (sample * 2)) -> F32 at sample { x[0] }
flow closed(x: F32 at sample) -> [F32; 1] at sample {
  [x + first2~(one~().reset_if~(true at (sample / 2147483648)).up~(2)) + (par i in 0 ..< 2097152 { x })[0]]
}
flow chans(x: F32 at sample) -> [F32; 2] at sample { [x, x + 1.0] }
fn ramp() -> [F32; 3] { [1.0, 2.0, 3.0] }
";

fn one(tests: &str) -> TestRun {
    let src = format!("{FLOWS}{tests}");
    let run = onsa_diag::stack::run(move || run_case(PackageInput::single_file("t.onsa", &src), &Wrappers::default()));
    let mut got = run.expect("the case is read").tests;
    assert_eq!(got.len(), 1);
    got.remove(0)
}

#[test]
fn a_run_split_over_slices_writes_back_only_its_part_and_keeps_the_state() {
    // The first call fills out[0..2] with 1 3 and leaves out[2] = 0; the second goes on from the sum 3: 3 + 3 = 6, 6 + 4 =
    // 10. A call of 0 frames between them (`slice(2, 2)`) changes nothing.
    let r = one("test \"split\" {
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var out: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs.slice(0, 2), inout out.slice(0, 2))
  assert out[0] == 1.0
  assert out[1] == 3.0
  assert out[2] == 0.0
  acc.process(inout st, xs.slice(2, 2), inout out.slice(2, 2))
  acc.process(inout st, xs.slice(2, 4), inout out.slice(2, 4))
  assert out[2] == 6.0
  assert out[3] == 10.0
}");
    assert_eq!((r.verdict, r.asserts, r.panic), (Verdict::Ok, 5, None));
}

#[test]
fn reset_puts_the_state_back_and_two_states_of_a_flow_are_apart() {
    // Without the reset the second run of `a` would go on from the sum 10 and end at 20 (11 13 16 20); with it, it ends at 10
    // again. `a` and `b` count apart: 10 and 100 after four frames.
    let r = one("test \"reset\" {
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  let ys: [F32; 4] = [10.0, 20.0, 30.0, 40.0]
  var out: [F32; 4] = [0.0; 4]
  var a = acc.init(8.0)
  var b = acc.init(8.0)
  acc.process(inout a, xs, inout out)
  assert out[3] == 10.0
  acc.reset(inout a)
  acc.process(inout a, xs, inout out)
  assert out[3] == 10.0
  var other: [F32; 4] = [0.0; 4]
  acc.process(inout b, ys, inout other)
  assert other[3] == 100.0
  acc.process(inout a, xs, inout out)
  assert out[3] == 20.0
}");
    assert_eq!((r.verdict, r.asserts, r.panic), (Verdict::Ok, 4, None));
}

#[test]
fn the_config_the_params_and_a_call_as_the_input_reach_the_instance() {
    // `off` adds the config 10: 1 2 3 give 11 12 13 (ramp is 1 2 3). `gain` takes the params of each call: 2 then 3.
    let r = one("test \"args\" {
  var out: [F32; 3] = [0.0; 3]
  var st = off.init(off.Config { c: 10.0 }, 8.0)
  off.process(inout st, ramp(), inout out)
  assert out[0] == 11.0
  assert out[2] == 13.0
  var s = gain.init(8.0)
  gain.process(inout s, gain.Params { g: 2.0 }, ramp(), inout out)
  assert out[2] == 6.0
  gain.process(inout s, gain.Params { g: 3.0 }, ramp(), inout out)
  assert out[2] == 9.0
}");
    assert_eq!((r.verdict, r.asserts, r.panic), (Verdict::Ok, 4, None));
}

#[test]
fn a_panic_ends_the_test_at_its_call_with_the_stage_and_nothing_runs_after_it() {
    // `inv` of 5 gives 2, of 0 panics (§9.2) in the frame 1, so the assert after it is not counted. `ib` with n = 0 panics in
    // `init` (the `let` of the clock `init`). A `slice` past the end is a panic of the test itself (§5.3).
    let run = |mark: &str, body: &str| one(&format!("test \"boom\" {{ //~ {mark} \"boom\"\n{body}\n}}"));
    let r = run(
        "TESTFAIL",
        "  let xs: [I32; 2] = [5, 0]\n  var o: [I32; 2] = [0; 2]\n  var st = inv.init(8.0)\n  inv.process(inout st, xs, inout o)\n  assert false",
    );
    assert_eq!((r.verdict, r.panic, r.asserts), (Verdict::Ok, Some(Panic::Call(PanicAt::Sample(1))), 0));
    // The call that ends the test (the tail of its block) is run too: here it is the one that panics.
    let r = run(
        "TESTFAIL",
        "  let xs: [I32; 2] = [5, 0]\n  var o: [I32; 2] = [0; 2]\n  var st = inv.init(8.0)\n  inv.process(inout st, xs, inout o)",
    );
    assert_eq!((r.verdict, r.panic), (Verdict::Ok, Some(Panic::Call(PanicAt::Sample(1)))));
    let r = run("TESTFAIL", "  var st = ib.init(ib.Config { n: 0 }, 8.0)\n  ib.reset(inout st)\n  assert false");
    assert_eq!((r.verdict, r.panic, r.asserts), (Verdict::Ok, Some(Panic::Call(PanicAt::Init)), 0));
    let r = run(
        "PANIC",
        "  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]\n  var o: [F32; 4] = [0.0; 4]\n  var st = acc.init(8.0)\n  acc.process(inout st, xs.slice(0, 5), inout o.slice(0, 4))\n  assert false",
    );
    assert_eq!((r.verdict, r.panic, r.asserts), (Verdict::Ok, Some(Panic::Eval), 0));
}

#[test]
fn an_unavailable_call_stops_the_test_and_a_wrong_assert_after_a_run_fails_it() {
    // `closed` has a `par` of 2^21 elements, more than the evaluator holds, so the body of the frame is the evaluator's `Unavailable` (`init` and `reset` go on, the frame does not) and `assert false` after it is not reached.
    let r = one(
        "test \"wait\" {\n  let xs: [F32; 1] = [1.0]\n  let o = closed.render(xs, 8.0)\n  assert o.out[0][0] == 1.0\n  assert false\n}",
    );
    assert_eq!((r.asserts, matches!(r.verdict, Verdict::Unavailable(_))), (0, true), "{r:?}");
    let r = one("test \"wrong\" {
  let xs: [F32; 2] = [1.0, 2.0]
  var o: [F32; 2] = [0.0; 2]
  var st = acc.init(8.0)
  acc.process(inout st, xs, inout o)
  assert o[1] == 4.0
}");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m.contains("assert 1")), "{r:?}");
}

#[test]
fn lengths_that_differ_are_a_panic_at_start_and_an_array_of_buffers_is_a_layout() {
    // The input has 4 frames and the output 2: the lengths of the `Span`s of a call differ, which is a panic of the call
    // before its first block (§11.6, the stage `start`). An array of buffers as the output is a layout (W7-12).
    let r = one("test \"lengths\" { //~ TESTFAIL \"lengths\"
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var o: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs, inout o.slice(0, 2))
}");
    assert_eq!((&r.verdict, r.panic), (&Verdict::Ok, Some(Panic::Call(PanicAt::Start))), "{r:?}");
    let r = one("test \"planar\" {
  let xs: [F32; 2] = [1.0, 2.0]
  var a: [F32; 2] = [0.0; 2]
  var b: [F32; 2] = [0.0; 2]
  var st = chans.init(8.0)
  chans.process(inout st, xs, inout [a, b])
}");
    assert_eq!(r.verdict, Verdict::Skipped(Skip::Layout));
}
