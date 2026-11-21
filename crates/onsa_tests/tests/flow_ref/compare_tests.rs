//! `compare.rs` on small cases: what the evaluator gave is run through the interpreter and agrees; then one thing the
//! evaluator "gave" is changed by hand (an output, an input, a panic), and the comparison fails at that call, leaf and
//! frame. The values in the cases are worked out from §11.4 and §11.6 (a running sum, a delay of a sample, `100 / x`).

use onsa_driver::{ManifestForm, ManifestSource, PackageInput, SourceFile};
use onsa_tests::flow_ref::flow::PanicAt;
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
    compared_in(PackageInput::single_file("zz.onsa", SOURCE), tamper)
}

fn compared_in(input: PackageInput, tamper: impl FnOnce(&mut CaseRun) + Send) -> Compared {
    onsa_diag::stack::run(move || {
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
    assert!(m.contains("assert flow_ref_o0.out[2].to_bits() == 0x40e00000"), "{m}");
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

/// `v` with one bit changed: a value that the interpreter does not give (a NaN is any NaN, so it is not changed).
fn flipped(v: &Value) -> Option<Value> {
    match v {
        Value::Bool(b) => Some(Value::Bool(!b)),
        Value::Int(k, n, _) => Some(Value::int(*k, if *n == k.range().1 { n - 1 } else { n + 1 })),
        Value::F32(x) if !x.is_nan() => Some(Value::F32(f32::from_bits(x.to_bits() ^ 1))),
        Value::F64(x) if !x.is_nan() => Some(Value::F64(f64::from_bits(x.to_bits() ^ 1))),
        _ => None,
    }
}

#[test]
fn a_changed_value_fails_on_the_files_of_the_corpus_too() {
    // The comparison of the files of `tests/flow_ref/corpus/` is not silent: in each, one output of the evaluator is changed
    // (the first call of a test that gave a value to change) and exactly that test fails, at that call.
    let root = onsa_tests::case::repo_root();
    let files = onsa_tests::case::onsa_files(&root, "tests/flow_ref/corpus").expect("the corpus");
    assert!(files.len() >= 3, "{files:?}");
    for file in files {
        let path = onsa_tests::case::rel_path(&root, &file);
        let text = std::fs::read_to_string(&file).expect("the file");
        let (c, at) = onsa_diag::stack::run(move || {
            let input = PackageInput::single_file(&path, &text);
            let mut run = run_case(input.clone(), &Wrappers::default()).expect("the file is read");
            let mut changed = None;
            'tests: for t in run.tests.iter_mut() {
                for (at, e) in t.events.iter_mut().enumerate() {
                    if let Event::Render { run, .. } | Event::Process { run, .. } = e
                        && let Some(outs) = run.outs.as_mut()
                        && let Some(v) = outs.first().and_then(flipped)
                    {
                        outs[0] = v;
                        changed = Some(format!("\"{}\": #{at} ", t.name));
                        break 'tests;
                    }
                }
            }
            (compare_case(&path, input, &run), changed.expect("a test with a value to change"))
        });
        assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
        assert!(c.failures[0].contains(&at), "{at} {:?}", c.failures);
    }
}

#[test]
fn a_corpus_that_lost_a_test_or_a_file_or_panics_in_init_fails() {
    // The counts the evaluator gave are compared with those written down (`CORPUS_COUNTS`): a test or a file that went
    // away, a test no longer evaluated, a file that does not lower, and a test that panics in `init` (E0419, §11.3) each fail.
    let tally = |tests, evaluated| crate::Tally { tests, evaluated, ..crate::Tally::default() };
    let file = |t| vec![("tests/flow_ref/corpus/a.onsa".to_string(), t)];
    let check = |t, tests, evaluated| crate::corpus_failures(&file(t), &[("a.onsa", tests, evaluated)]);
    assert_eq!(check(tally(5, 5), 5, 5), Vec::<String>::new());
    assert_eq!(check(tally(4, 4), 5, 5).len(), 1, "a test went away");
    assert_eq!(check(tally(5, 4), 5, 5).len(), 1, "a test is no longer evaluated");
    assert_eq!(
        crate::corpus_failures(&file(tally(5, 5)), &[("a.onsa", 5, 5), ("b.onsa", 1, 1)]).len(),
        1,
        "a file went away"
    );
    assert_eq!(crate::corpus_failures(&file(tally(5, 5)), &[]).len(), 1, "a file is not written down");
    let mut lowered = tally(5, 5);
    lowered.waiting = 1;
    assert_eq!(check(lowered, 5, 5).len(), 1, "a file that does not lower");
    let mut init = tally(5, 5);
    init.at_init = vec!["a.onsa: \"t\"".into()];
    assert_eq!(check(init, 5, 5).len(), 1, "a panic in init");
}

/// A panic of each stage of a call (§9.2, §11.6): at a frame, in the `block` stage, in `init`, and at the start of a
/// `process` (a column of 2 and an output of 3). The divisions by zero are §3.4's; `render` is `init` and one `process`.
const STAGES: &str = r#"
flow quot(x: I32 at sample) -> I32 at sample {
  100 / x
}
flow blocky(d: I32 at block, x: I32 at sample) -> I32 at sample {
  let k = 100 / d
  x + k
}
flow started(c: I32 at init) -> I32 at sample {
  let k = 100 / c
  k
}
test "at a frame" {
  let xs: [I32; 3] = [1, 0, 2]
  let _ = quot.render(xs, 8.0)   //~ PANIC "at a frame"
}
test "at a block" {
  let xs: [I32; 2] = [1, 2]
  let _ = blocky.render(blocky.Params { d: 0 }, xs, 8.0)   //~ PANIC "at a block"
}
test "at init" {
  let _ = started.render(started.Config { c: 0 }, 2, 8.0)   //~ PANIC "at init"
}
test "at the start" {
  let xs: [I32; 2] = [1, 2]
  var out: [I32; 3] = [0; 3]
  var st = quot.init(8.0)
  quot.process(inout st, xs, inout out)   //~ PANIC "at the start"
}
test "an earlier call" {
  let xs: [I32; 2] = [5, 20]
  let ys: [I32; 2] = [4, 0]
  let a = quot.render(xs, 8.0)
  let _ = quot.render(ys, 8.0)   //~ PANIC "an earlier call"
  assert a.out[0] == 20
}
"#;

fn stages(tamper: impl FnOnce(&mut CaseRun) + Send) -> Compared {
    compared_in(PackageInput::single_file("zz.onsa", STAGES), tamper)
}

#[test]
fn a_panic_is_compared_by_its_stage_too_whichever_frame_it_is_at() {
    // Each panic of the four first tests is at its own stage in both, and the interpreter's is told by the place it is at
    // (the expression of a `let` of the clock, the call of the test at the start): all agree, any frame of `Sample(n)`.
    let c = stages(|_| {});
    assert_eq!((c.ran, c.panicked, c.failures), (5, 5, Vec::<String>::new()));
    let c = stages(|r| test_named(r, "at a frame").panic = Some(Panic::Call(PanicAt::Sample(41))));
    assert_eq!((c.panicked, c.failures), (5, Vec::<String>::new()));
    // Any other stage the evaluator names for the same call is a failure that says both.
    let all = [PanicAt::Init, PanicAt::Start, PanicAt::Block, PanicAt::Sample(0)];
    let cases = [
        ("at a frame", 3, "Some(Tick(0))"),
        ("at a block", 2, "Some(Block)"),
        ("at init", 0, "Some(Init)"),
        ("at the start", 1, "None"),
    ];
    for (name, right, shown) in cases {
        for (k, at) in all.into_iter().enumerate().filter(|(k, _)| *k != right) {
            let c = stages(move |r| test_named(r, name).panic = Some(Panic::Call(at)));
            assert_eq!(c.failures.len(), 1, "{name} {at:?}: {:?}", c.failures);
            let m = &c.failures[0];
            assert!(
                m.contains(&format!("it panicked at {shown}, the evaluator at "))
                    && m.contains(&format!("{:?}", at.stage())),
                "{name} {k}: {m}"
            );
        }
    }
}

#[test]
fn a_panic_of_an_earlier_call_than_the_evaluators_is_a_failure_at_that_call() {
    // The evaluator says the second render panics (4 and 0); the first gets the input 0 for 5 here, and the interpreter
    // panics at it, before the call the evaluator says. It is no agreement of the two panics.
    let c = stages(|r| {
        if let Event::Render { run, .. } = &mut test_named(r, "an earlier call").events[0] {
            run.inputs[0].1[0] = Value::int(IntKind::I32, 0);
        }
    });
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].starts_with("zz.onsa: \"an earlier call\": #0 render zz.quot (line "), "{:?}", c.failures);
}

/// A package of files (the module of each is its stem), with a manifest.
fn package(files: &[(&str, &str)]) -> PackageInput {
    let text = "[package]\nname = \"zz\"\nedition = \"2026\"\n".to_string();
    PackageInput {
        manifest: Some(ManifestSource { path: "onsa.toml".into(), text, form: ManifestForm::File }),
        files: files.iter().map(|(p, t)| SourceFile { path: p.to_string(), text: t.to_string() }).collect(),
        ..PackageInput::default()
    }
}

#[test]
fn a_flow_is_written_as_the_test_writes_it_and_not_as_the_last_word_of_its_path() {
    // `a.dup` gives x and `b.dup` gives 2 x: the same last word in two modules. The test `use`s `a.dup` and calls both: the
    // names it writes (`dup`, `b.dup`) are printed, so each call is of the flow the evaluator ran (§15.1: a `use` of a
    // name, the path of a module); a test that has only `use b` has no `dup` in scope, and `b.dup` is what it writes.
    let a = "pub flow dup(x: F32 at sample) -> F32 at sample { x }\n";
    let b = "pub flow dup(x: F32 at sample) -> F32 at sample { x * 2.0 }\n";
    let both = "use a.dup\nuse b\ntest \"both\" {\n  let xs: [F32; 2] = [1.0, 2.0]\n  let p = dup.render(xs, 8.0)\n  \
                let q = b.dup.render(xs, 8.0)\n  assert p.out[1] == 2.0\n  assert q.out[1] == 4.0\n}\n";
    let only_b = both
        .replace("use a.dup\n", "")
        .replace("  let p = dup.render(xs, 8.0)\n", "")
        .replace("  assert p.out[1] == 2.0\n", "");
    for check in [both.to_string(), only_b] {
        let c = compared_in(package(&[("a.onsa", a), ("b.onsa", b), ("check.onsa", &check)]), |_| {});
        assert_eq!(
            (c.ran, c.asserts, &c.failures),
            (1, if check.contains("p.out") { 4 } else { 2 }, &Vec::<String>::new())
        );
    }
}

#[test]
fn the_locals_of_a_printed_test_do_not_clash_with_the_names_of_the_case() {
    // Flows named `s0`, `o0` and `i0_0` (the names the printed locals had) are no clash now; a case that writes a name that
    // starts with the prefix `flow_ref_` is not printed, and its tests are counted as not printed, with the reason.
    let flows = "flow s0(x: I32 at sample) -> I32 at sample { x + 1 }\nflow o0(x: I32 at sample) -> I32 at sample { x + 2 }\n\
                 flow i0_0(x: I32 at sample) -> I32 at sample { x + 3 }\n";
    let tests = "test \"t\" {\n  let xs: [I32; 2] = [1, 2]\n  var st = s0.init(8.0)\n  var out: [I32; 2] = [0; 2]\n  \
                 s0.process(inout st, xs, inout out)\n  let o = o0.render(xs, 8.0)\n  let p = i0_0.render(xs, 8.0)\n  \
                 assert out[1] == 3\n  assert o.out[1] == 4\n  assert p.out[1] == 5\n}\n";
    let c = compared_in(PackageInput::single_file("zz.onsa", format!("{flows}{tests}")), |_| {});
    assert_eq!((c.ran, c.asserts, &c.failures), (1, 6, &Vec::<String>::new()));
    let named = format!("{flows}flow flow_ref_s0(x: I32 at sample) -> I32 at sample {{ x }}\n{tests}");
    let c = compared_in(PackageInput::single_file("zz.onsa", named), |_| {});
    assert_eq!((c.ran, c.failures.len(), c.unprintable.values().sum::<usize>()), (0, 0, 1), "{:?}", c.unprintable);
}

const WIDE: &str = r#"
flow wide(x: F64 at sample) -> F64 at sample {
  x * 2.0
}
flow rate() -> F32 at sample {
  sample_rate()
}
test "an f64" {
  let xs: [F64; 2] = [1.5, 2.5]
  let o = wide.render(xs, 8.0)
  assert o.out[1] == 5.0
}
test "the rate" {
  let o = rate.render(2, 48000.0)
  assert o.out[0] == 48000.0
}
"#;

#[test]
fn an_f64_that_changed_and_a_rate_that_is_not_the_usual_fail_in_the_interpreter() {
    let wide = || PackageInput::single_file("zz.onsa", WIDE);
    let c = compared_in(wide(), |_| {});
    assert_eq!((c.ran, c.asserts, &c.failures), (2, 4, &Vec::<String>::new()));
    // The F64 5.0 with its last bit changed: the comparison is of the bits, as an F32's is.
    let c = compared_in(wide(), |r| outs(r, "an f64", 0)[1] = Value::F64(f64::from_bits(5.0f64.to_bits() ^ 1)));
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"an f64\": #0 render zz.wide, out frame 1"), "{:?}", c.failures);
    assert!(c.failures[0].contains("to_bits() == 0x4014000000000001"), "{:?}", c.failures);
    // The rate of the call is the one the render is given (48000), whatever the printed test says: made 8 here, the
    // interpreter's output (8.0) is not the evaluator's (48000.0).
    let c = compared_in(wide(), |r| {
        if let Event::Render { sample_rate, .. } = &mut test_named(r, "the rate").events[0] {
            *sample_rate = 8.0;
        }
    });
    assert_eq!(c.failures.len(), 1, "{:?}", c.failures);
    assert!(c.failures[0].contains("\"the rate\": #0 render zz.rate, out frame 0"), "{:?}", c.failures);
}
