//! `compare.rs` on small cases: what the evaluator gave is run through the interpreter and agrees; then one thing the
//! evaluator "gave" is changed by hand (an output, an input, a panic), and the comparison fails at that call, leaf and
//! frame. The values in the cases are worked out from §11.4 and §11.6 (a running sum, a delay of a sample, `100 / x`).

use onsa_driver::PackageInput;
use onsa_tests::flow_ref::interp_host::Wrappers;
use onsa_tests::flow_ref::value::{IntKind, Value};
use onsa_tests::flow_ref::walk::{CaseRun, Event, Panic, Skip, Verdict, run_case};

use super::compare::{Compared, compare_case};

const SOURCE: &str = r#"
flow acc(x: F32 at sample) -> F32 at sample {
  let y = x + prev~(^y)
  y
}
flow widen(x: F32 at sample) -> [F32; 2] at sample {
  [x, prev~(x)]
}
flow quot(x: I32 at sample) -> I32 at sample {
  100 / x
}
test "a sum" {
  let xs: [F32; 3] = [1.0, 2.0, 3.0]
  let o = acc.render(xs, 8.0)
  assert o.out[2] == 6.0
}
test "a state that is reset" {
  let xs: [F32; 2] = [1.0, 2.0]
  var out: [F32; 2] = [0.0; 2]
  var st = acc.init(8.0)
  acc.process(inout st, xs, inout out)
  acc.reset(inout st)
  acc.process(inout st, xs, inout out)
  assert out[1] == 3.0
}
test "two channels" {
  let xs: [F32; 2] = [1.0, 2.0]
  let o = widen.render(xs, 8.0)
  assert o.out[1][1] == 1.0
}
test "a quotient" {
  let xs: [I32; 2] = [5, 20]
  let o = quot.render(xs, 8.0)
  assert o.out[1] == 5
}
test "a process over slices" {
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var out: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs.slice(0, 2), inout out.slice(1, 3))
  acc.process(inout st, xs.slice(2, 4), inout out.slice(2, 4))
  assert out[3] == 10.0
}
test "slices of other lengths" {
  let xs: [F32; 4] = [1.0, 2.0, 3.0, 4.0]
  var out: [F32; 4] = [0.0; 4]
  var st = acc.init(8.0)
  acc.process(inout st, xs.slice(0, 2), inout out.slice(0, 3))   //~ PANIC "slices of other lengths"
}
test "a zero divides" {
  let xs: [I32; 2] = [5, 0]
  let o = quot.render(xs, 8.0)   //~ PANIC "a zero divides"
  assert o.out[0] == 20
}
"#;

/// The case through the evaluator, `tamper`ed with, then through the interpreter.
fn compared(tamper: impl FnOnce(&mut CaseRun) + Send) -> Compared {
    onsa_diag::stack::run(move || {
        let input = PackageInput::single_file("zz.onsa", SOURCE);
        let mut run = run_case(input.clone(), &Wrappers::default()).expect("the case is read");
        tamper(&mut run);
        compare_case("zz.onsa", input, &run)
    })
}

fn test_named<'r>(run: &'r mut CaseRun, name: &str) -> &'r mut onsa_tests::flow_ref::walk::TestRun {
    run.tests.iter_mut().find(|t| t.name == name).expect("the test")
}

/// The outputs the call number `at` of the test gave.
fn outs<'r>(run: &'r mut CaseRun, test: &str, at: usize) -> &'r mut Vec<Value> {
    match &mut test_named(run, test).events[at] {
        Event::Process { run, .. } | Event::Render { run, .. } => run.outs.as_mut().expect("it gave outputs"),
        e => panic!("{e:?} gives no output"),
    }
}

#[test]
fn what_the_evaluator_gave_passes_in_the_interpreter_and_the_panic_is_compared_too() {
    let c = compared(|_| {});
    assert_eq!((c.ran, c.panicked, c.failures), (7, 2, Vec::<String>::new()));
    assert!(c.unprintable.is_empty());
}

#[test]
fn a_changed_output_fails_at_its_call_its_leaf_and_its_frame() {
    // The sum 1 3 6: the frame 2 of the first render is 6.0 (0x40c00000); say it was 7.0.
    let c = compared(|r| outs(r, "a sum", 0)[2] = Value::F32(7.0));
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    let m = &c.failures[0];
    assert!(m.starts_with("zz.onsa: \"a sum\": #0 render zz.acc, out frame 2 (line "), "{m}");
    assert!(m.contains("assert o0.out[2].to_bits() == 0x40e00000"), "{m}");
}

#[test]
fn a_channel_and_a_call_after_a_reset_are_named_in_the_failure() {
    // widen gives x and x one sample late: channel 1 is 0.0 1.0, so its frame 1 is 1.0.
    let c = compared(|r| outs(r, "two channels", 0)[1] = Value::Array(vec![Value::F32(2.0), Value::F32(5.0)]));
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"two channels\": #0 render zz.widen, out[1] frame 1"), "{:?}", c.failures);
    // The second `process` after `reset` gives the first run's 1 3 again; say its frame 1 is 6.0 (the state not reset).
    let c = compared(|r| outs(r, "a state that is reset", 3)[1] = Value::F32(6.0));
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"a state that is reset\": #3 process 0, out frame 1"), "{:?}", c.failures);
}

#[test]
fn a_process_over_slices_is_given_the_slices_and_lengths_that_differ_panic_at_the_call() {
    // The first slice is 1 2 (a sum 1 3), the second 3 4 (a sum 6 10): a call each, with the state between them.
    let c = compared(|r| outs(r, "a process over slices", 2)[1] = Value::F32(11.0));
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"a process over slices\": #2 process 0, out frame 1"), "{:?}", c.failures);
    // The input of 2 frames and the output of 3 (§11.6) panic at the `process`, as the evaluator's `panic start`: the
    // interpreter that gets the output one frame shorter does not.
    let c = compared(|r| {
        if let Event::Process { run, .. } = &mut test_named(r, "slices of other lengths").events[1] {
            run.frames = Some(2);
        }
    });
    assert_eq!(c.failures, ["zz.onsa: \"slices of other lengths\": it did not panic at #1 process 0"]);
}

#[test]
fn a_changed_input_is_found_as_a_changed_output() {
    // The evaluator's quotients of 5 and 20 are 20 and 5; give the interpreter the input 4 instead of 5.
    let c = compared(|r| {
        if let Event::Render { run, .. } = &mut test_named(r, "a quotient").events[0] {
            run.inputs[0].1[0] = Value::int(IntKind::I32, 4);
        }
    });
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"a quotient\": #0 render zz.quot, out frame 0"), "{:?}", c.failures);
}

#[test]
fn a_panic_the_interpreter_does_not_make_and_one_it_makes_alone_both_fail() {
    // The input 0 that panics is made 2: the interpreter gives 50 and 5, and does not panic at the render.
    let c = compared(|r| {
        if let Event::Render { run, .. } = &mut test_named(r, "a zero divides").events[0] {
            run.inputs[0].1[1] = Value::int(IntKind::I32, 2);
        }
    });
    assert_eq!(c.failures, ["zz.onsa: \"a zero divides\": it did not panic at #0 render zz.quot"]);
    // The evaluator says the same render does not panic (its test has no panic), and the interpreter panics at it.
    let c = compared(|r| test_named(r, "a zero divides").panic = None);
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].starts_with("zz.onsa: \"a zero divides\": #0 render zz.quot (line "), "{:?}", c.failures);
}

#[test]
fn a_panic_of_an_expression_of_the_test_is_not_compared_and_what_is_not_evaluated_is_not_run() {
    let c = compared(|r| {
        test_named(r, "a zero divides").panic = Some(Panic::Eval);
        test_named(r, "a sum").verdict = Verdict::Skipped(Skip::Layout);
    });
    // Six tests ran (the skipped one did not); the render of "a zero divides" is printed with no assert, and the
    // interpreter panics at it, which the test (a panic of an expression) does not expect: it is a failure.
    assert_eq!(c.ran, 6);
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"a zero divides\": #0 render zz.quot (line"), "{:?}", c.failures);
}

#[test]
fn a_case_with_nothing_evaluated_runs_nothing() {
    let c = compared(|r| r.tests.iter_mut().for_each(|t| t.verdict = Verdict::Skipped(Skip::NoCall)));
    assert_eq!((c.ran, c.panicked, c.failures), (0, 0, Vec::<String>::new()));
}

#[test]
fn a_form_no_literal_writes_is_counted_with_its_reason_and_is_no_failure() {
    let c = compared(|r| {
        if let Event::Render { run, .. } = &mut test_named(r, "a sum").events[0] {
            run.inputs[0].1[0] = Value::Char('a');
        }
    });
    assert_eq!(c.ran, 6);
    assert_eq!(c.unprintable.values().sum::<usize>(), 1, "{:?}", c.unprintable);
    assert!(c.failures.is_empty(), "{:?}", c.failures);
}
