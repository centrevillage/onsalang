//! The extraction of `walk.rs` on small cases: the forms of an assert, the marks, each reason to skip, and the cases that
//! are not run. Every value is worked out by hand from the flows in the comment of the test.

use super::flow::PanicAt;
use super::interp_host::Wrappers;
use super::walk::{CaseRun, Event, Panic, Skip, TestRun, Verdict, run_case};
use onsa_driver::PackageInput;

const FLOWS: &str = "use std.math.is_nan

struct Pair { l: F32, r: F32 }
flow dbl(x: F32 at sample) -> F32 at sample { x * 2.0 }
flow same(x: F32 at sample) -> F32 at sample { x }
flow chans(x: F32 at sample) -> [F32; 2] at sample { [x, x + 1.0] }
flow pair(x: F32 at sample) -> Pair at sample { Pair { l: x, r: x * 3.0 } }
flow inv(x: I32 at sample) -> I32 at sample { 10 / x }
flow closed(x: F32 at sample) -> [F32; 1] at sample {
  let a = par~ i in 0 ..< 1 { prev~(^y) }
  let y = x
  a
}
flow acc(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
";

fn run(tests: &str) -> Result<CaseRun, String> {
    let src = format!("{FLOWS}{tests}");
    onsa_diag::stack::run(move || run_case(PackageInput::single_file("t.onsa", &src), &Wrappers::default()))
}

fn one(tests: &str) -> TestRun {
    let mut got = run(tests).expect("the case is read").tests;
    assert_eq!(got.len(), 1);
    got.remove(0)
}

#[test]
fn the_forms_of_an_assert_on_the_outputs_are_read_from_the_tables() {
    // dbl doubles: 1 2 3 -> 2 4 6 (4.0 is 0x40800000 = 1082130432); a NaN stays a NaN; chans is [x, x + 1]: for 1 and 3
    // channel 1 gives 2 and channel 0 gives 3; pair is { l: x, r: 3 x }: l[1] = 2, r[2] = 9.
    let r = one("test \"forms\" {
  let xs: [F32; 3] = [1.0, 2.0, 3.0]
  let o = dbl.render(xs, 8.0)
  assert o.out[0] == 2.0
  assert o.out[2] == 6.0
  assert o.out.len() == 3
  assert o.out[1].to_bits() == 1082130432
  let n: [F32; 1] = [F32.NAN]
  let q = same.render(n, 8.0)
  assert is_nan(q.out[0])
  let c = chans.render(xs, 8.0)
  assert c.out[1][0] == 2.0
  assert c.out[0][2] == 3.0
  let p = pair.render(xs, 8.0)
  assert p.l[1] == 2.0
  assert p.r[2] == 9.0
}");
    assert_eq!((r.verdict, r.asserts, r.panic), (Verdict::Ok, 9, None));
}

#[test]
fn a_false_assert_or_a_panic_that_is_not_marked_fails_the_test() {
    // dbl(1) is 2, not 3. `inv` is 10 / x: 5 gives 2, and 0 panics (§9.2) in the frame 1.
    let r = one("test \"false\" {
  let xs: [F32; 1] = [1.0]
  let o = dbl.render(xs, 8.0)
  assert o.out[0] == 3.0
}");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m.contains("assert 1")), "{r:?}");
    let r = one("test \"boom\" {
  let xs: [I32; 2] = [5, 0]
  let o = inv.render(xs, 8.0)
  assert o.out[0] == 2
}");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m.contains("panic")), "{r:?}");
}

#[test]
fn a_marked_test_must_panic_and_a_panic_is_taken_at_its_frame() {
    let marked = |body: &str| one(&format!("test \"boom\" {{ //~ TESTFAIL \"boom\"\n{body}\n}}"));
    let r = marked("  let xs: [I32; 2] = [5, 0]\n  let o = inv.render(xs, 8.0)\n  assert o.out[0] == 2");
    assert_eq!((r.verdict, r.panic, r.asserts), (Verdict::Ok, Some(Panic::Call(PanicAt::Sample(1))), 0));
    let r = marked("  let xs: [I32; 1] = [5]\n  let o = inv.render(xs, 8.0)\n  assert o.out[0] == 2");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m == "no panic"), "{r:?}");
    // A `PANIC` mark is a panic too: the index 5 of 1 frame is out of the outputs (§9.2), in the test itself.
    let r = one(
        "test \"far\" { //~ PANIC \"far\"\n  let xs: [F32; 1] = [1.0]\n  let o = dbl.render(xs, 8.0)\n  assert o.out[5] == 0.0\n}",
    );
    assert_eq!((r.verdict, r.panic), (Verdict::Ok, Some(Panic::Eval)));
}

#[test]
fn what_is_not_run_is_skipped_with_its_reason() {
    // a `for` is no statement of this unit; a test that calls no function of a flow compares nothing of the evaluator; a
    // `Span` is a view.
    let reason = |t: TestRun| match t.verdict {
        Verdict::Skipped(s) => s,
        other => panic!("not skipped: {other:?}"),
    };
    assert_eq!(reason(one("test \"loop\" {\n  for i in 0 ..< 2 { assert i < 2 }\n}")), Skip::Statement);
    assert_eq!(reason(one("test \"none\" {\n  assert 1 + 1 == 2\n}")), Skip::NoCall);
    assert_eq!(
        reason(one(
            "test \"view\" {\n  let xs: [F32; 2] = [1.0, 2.0]\n  let _: Span[F32] = xs.slice(0, 1)\n  assert true\n}"
        )),
        Skip::Layout
    );
}

#[test]
fn a_body_the_tables_do_not_cover_is_unavailable_and_the_case_is_waiting() {
    // A feedback reference `^y` inside a `par~` is E0200 today: the case is read and lowers no more, and the test that
    // renders it is counted.
    let got = run("test \"closed\" {\n  let xs: [F32; 1] = [1.0]\n  let o = closed.render(xs, 8.0)\n  assert o.out[0][0] == 1.0\n}")
        .expect("the case is read");
    assert!(got.e0200 && !got.lowered, "{got:?}");
    assert!(matches!(got.tests[0].verdict, Verdict::Unavailable(_)), "{:?}", got.tests);
}

#[test]
fn a_case_the_checker_refuses_is_not_read() {
    let err = run("test \"x\" { assert nope == 1 }").expect_err("a diagnostic that is not E0200");
    assert!(err.contains("E0"), "{err}");
}

#[test]
fn a_render_a_helper_calls_is_run_on_the_evaluator_with_its_event_and_its_panic() {
    // dbl doubles (1 2 3 gives 2 4 6), chans is [x, x + 1] (channel 1 of 1 2 3 is 2 3 4), pair is { l: x, r: 3 x } (r of 1
    // 2 3 is 3 6 9), inv is 10 / x (it panics for 0, at the frame 1 of 5 0).
    let helpers = "fn first_is_two(xs: [F32; 3]) -> Bool uses {Alloc} {
  let o = dbl.render(xs, 8.0)
  o.out[0] == 2.0
}
fn channel_one(xs: [F32; 3]) -> F32 uses {Alloc} {
  let c = chans.render(xs, 8.0)
  c.out[1][2]
}
fn right_of(xs: [F32; 3]) -> F32 uses {Alloc} {
  let p = pair.render(xs, 8.0)
  p.r[2]
}
fn quotient(xs: [I32; 2]) -> I32 uses {Alloc} {
  let o = inv.render(xs, 8.0)
  o.out[0]
}
";
    let r = one(&format!(
        "{helpers}test \"through a helper\" {{
  let xs: [F32; 3] = [1.0, 2.0, 3.0]
  let ys: [F32; 3] = [5.0, 2.0, 3.0]
  assert first_is_two(xs)
  assert first_is_two(ys) == false
  assert channel_one(xs) == 4.0
  assert right_of(xs) == 9.0
}}"
    ));
    let renders = r.events.iter().filter(|e| matches!(e, Event::Render { .. })).count();
    assert_eq!((&r.verdict, r.asserts, r.panic, renders), (&Verdict::Ok, 4, None, 4), "{r:?}");
    // The panic of the render in a helper is the test's, at its stage.
    let r = one(&format!(
        "{helpers}test \"boom\" {{ //~ TESTFAIL \"boom\"
  let xs: [I32; 2] = [5, 0]
  assert quotient(xs) == 2
}}"
    ));
    assert_eq!((&r.verdict, r.panic, r.asserts), (&Verdict::Ok, Some(Panic::Call(PanicAt::Sample(1))), 1), "{r:?}");
}

#[test]
fn slices_of_other_lengths_are_a_panic_at_start_and_not_a_layout() {
    // §11.6: the lengths of all the `Span`s of a call are equal, else it panics. The input has 2 frames and the output 3.
    let r = one("test \"mismatched slices\" { //~ TESTFAIL \"mismatched slices\"
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var out: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs.slice(0, 2), inout out.slice(0, 3))
}");
    assert_eq!((&r.verdict, r.panic), (&Verdict::Ok, Some(Panic::Call(PanicAt::Start))), "{r:?}");
    // An unmarked test that panics fails, and an assert that fails in a marked one is no panic of a call: it fails too.
    let r = one("test \"unmarked\" {
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var out: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs.slice(0, 2), inout out.slice(0, 3))
}");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m.contains("panic")), "{r:?}");
    let r = one("test \"false\" { //~ TESTFAIL \"false\"
  let xs: [F32; 3] = [1.0, 2.0, 3.0]
  let o = acc.render(xs, 8.0)
  assert o.out[0] == 99.0
}");
    assert!(matches!(&r.verdict, Verdict::Failed(m) if m.contains("assert 1")), "{r:?}");
}

#[test]
fn a_let_of_what_a_render_gave_is_a_value_of_the_test_and_not_a_layout() {
    // acc is a running sum: 1 2 3 gives 1 3 6, so `z` is 6.0.
    let r = one("test \"let from out\" {
  let xs: [F32; 3] = [1.0, 2.0, 3.0]
  let o = acc.render(xs, 8.0)
  let z = o.out[2]
  assert z == 6.0
}");
    assert_eq!((&r.verdict, r.asserts, r.panic), (&Verdict::Ok, 1, None), "{r:?}");
}

#[test]
fn a_render_has_the_leaves_of_its_output_type_even_with_no_frames() {
    // A struct output { l, r } has the leaves `.l` and `.r` though no value of it is made (0 frames); an array of 2 channels has
    // `[0]` and `[1]` (so the data of a call of 0 frames keeps `out.l=[]`); a scalar output is one leaf.
    let leaves = |flow: &str, frames: usize, read: &str| {
        let xs = vec!["1.0"; frames].join(", ");
        let r = one(&format!(
            "test \"leaves\" {{\n  let xs: [F32; {frames}] = [{xs}]\n  let o = {flow}.render(xs, 8.0)\n  assert {read}\n}}"
        ));
        match &r.events[..] {
            [Event::Render { run, .. }] if r.verdict == Verdict::Ok => {
                (run.shape.clone(), run.outs.clone().map(|o| o.len()))
            }
            other => panic!("{:?} {other:?}", r.verdict),
        }
    };
    let (shape, frames) = leaves("pair", 0, "o.l.len() == 0");
    assert_eq!((shape, frames), (vec![(".l".into(), None), (".r".into(), None)], Some(0)));
    assert_eq!(leaves("chans", 2, "o.out[0][0] == 1.0").0, vec![(String::new(), Some(2))]);
    assert_eq!(leaves("dbl", 2, "o.out[1] == 2.0").0, vec![(String::new(), None)]);
}
