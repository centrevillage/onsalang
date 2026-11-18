//! The writer of `data.rs` on small runs built by hand: how a value is written, the leaves of the outputs, the lines of a
//! panic and of a test that is skipped or unavailable, and the counts of the head. Each text is worked out from `FORMAT.md`.

use super::data::{Counts, case_text, manifest};
use super::flow::PanicAt;
use super::value::{IntKind, Value};
use super::walk::{CaseRun, Event, Panic, Run, Skip, TestRun, Types, Verdict};

fn f(x: f32) -> Value {
    Value::F32(x)
}

/// A run whose output has the leaves `shape` (a path and its channels).
fn shaped(shape: &[(&str, Option<usize>)], inputs: Vec<(String, Vec<Value>)>, outs: Option<Vec<Value>>) -> Run {
    let shape = shape.iter().map(|(p, c)| (p.to_string(), *c)).collect();
    Run {
        shape,
        types: Types::default(),
        config: vec![("k".into(), Value::int(IntKind::I32, -3))],
        params: vec![],
        frames: None,
        inputs,
        outs,
    }
}

fn run(inputs: Vec<(String, Vec<Value>)>, outs: Option<Vec<Value>>) -> Run {
    shaped(&[("", None)], inputs, outs)
}

fn test(name: &str, verdict: Verdict, panic: Option<Panic>, events: Vec<Event>) -> TestRun {
    TestRun { name: name.into(), file: String::new(), asserts: 0, panic, verdict, events }
}

fn case(tests: Vec<TestRun>) -> CaseRun {
    CaseRun { tests, lowered: true, e0200: false }
}

fn render(run: Run) -> Event {
    Event::Render { flow: "m.f".into(), written: None, sample_rate: 8.0, run }
}

#[test]
fn a_value_is_its_bits_and_only_a_result_that_is_a_nan_is_nan() {
    // 1.0 is 0x3f800000, -0.0 is 0x80000000, a NaN input keeps its bits (0x7fc00000), a NaN result is `nan`; an F64 has 16
    // digits (1.0 is 0x3ff0000000000000); the integer is decimal.
    let ins =
        vec![("x".to_string(), vec![f(1.0), f(-0.0), f(f32::NAN), Value::F64(1.0), Value::int(IntKind::U8, 200)])];
    let outs = vec![f(f32::NAN), f(-0.0), Value::Bool(true)];
    let (text, _) =
        case_text("a.onsa", &case(vec![test("t", Verdict::Ok, None, vec![render(run(ins, Some(outs)))])]), false);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines[2],
        "render m.f sr=0x41000000 cfg k=-3 in x=[0x3f800000 0x80000000 0x7fc00000 0x3ff0000000000000 200]"
    );
    assert_eq!(lines[3], "out=[nan 0x80000000 true]");
}

#[test]
fn the_outputs_are_a_line_for_each_channel_and_each_field() {
    // Channels [x, x + 1] of 1 and 2: channel 0 is 1 2 (0x3f800000 0x40000000), channel 1 is 2 3. A struct { l, r } of 1 and
    // 2 is `.l` = 1 2 and `.r`; a field that is an array has its channels, `.l[0]`.
    let ch = |a: f32, b: f32| Value::Array(vec![f(a), f(b)]);
    let two = [("", Some(2))];
    let one = |outs| case(vec![test("t", Verdict::Ok, None, vec![render(shaped(&two, vec![], Some(outs)))])]);
    let (text, _) = case_text("a", &one(vec![ch(1.0, 2.0), ch(2.0, 3.0)]), false);
    assert!(text.ends_with("out[0]=[0x3f800000 0x40000000]\nout[1]=[0x40000000 0x40400000]\n"), "{text}");
    let s = |l: Value, r: f32| Value::Struct(vec![l, f(r)]);
    let leaves = [(".l", Some(2)), (".r", None)];
    let named = render(shaped(&leaves, vec![], Some(vec![s(ch(1.0, 2.0), 5.0), s(ch(3.0, 4.0), 6.0)])));
    let (text, _) = case_text("a", &case(vec![test("t", Verdict::Ok, None, vec![named])]), false);
    let rows: Vec<&str> = text.lines().skip(3).collect();
    assert_eq!(
        rows,
        ["out.l[0]=[0x3f800000 0x40400000]", "out.l[1]=[0x40000000 0x40800000]", "out.r=[0x40a00000 0x40c00000]"]
    );
}

#[test]
fn a_call_that_panicked_gives_no_output_and_the_panic_is_the_last_line() {
    let at = |p| test("t", Verdict::Ok, Some(p), vec![render(run(vec![], None))]);
    let panics = [
        (Panic::Call(PanicAt::Init), "panic init"),
        (Panic::Call(PanicAt::Start), "panic start"),
        (Panic::Call(PanicAt::Block), "panic block"),
        (Panic::Call(PanicAt::Sample(2)), "panic sample 2"),
        (Panic::Eval, "panic eval"),
    ];
    for (p, line) in panics {
        let (text, _) = case_text("a", &case(vec![at(p)]), false);
        assert_eq!(text.lines().last(), Some(line), "{text}");
        assert!(!text.contains("out="), "{text}");
    }
}

#[test]
fn a_test_not_evaluated_is_one_line_with_its_reason_and_the_head_counts_it() {
    // A name with a tab or a newline is one line. The head counts the verdicts; `waiting` is 1 for a case that waits.
    let tests = vec![
        test("a\tb\nc", Verdict::Unavailable("a form"), None, vec![]),
        test("lay", Verdict::Skipped(Skip::Layout), None, vec![]),
        test("none", Verdict::Skipped(Skip::NoCall), None, vec![]),
        test("ok", Verdict::Ok, None, vec![Event::Reset { state: 3 }]),
    ];
    let (text, counts) = case_text("p.onsa", &case(tests), true);
    assert_eq!(
        text,
        "# flow_ref 1 source=p.onsa tests=4 evaluated=1 unavailable=1 skipped=2 waiting=1\n\
         ? a b c\tunavailable a form\n- lay\tskipped layout\n- none\tskipped nocall\n@ ok\nreset 3\n"
    );
    assert_eq!(counts, Counts { tests: 4, evaluated: 1, unavailable: 1, skipped: 2, waiting: 1 });
    // The same case with one test moved from evaluated to skipped is another text: the head changes, so the data fails.
    let moved = vec![test("ok", Verdict::Skipped(Skip::Layout), None, vec![])];
    assert_ne!(case_text("p.onsa", &case(moved), true).0.lines().next(), text.lines().next());
}

#[test]
fn the_manifest_gives_the_lines_of_each_file_and_the_sum() {
    let one = |n: usize| (format!("c{n}"), "x\ny\n".repeat(n), Counts { tests: n, evaluated: n, ..Counts::default() });
    let got = manifest(&[one(1), one(2)]);
    assert!(got.contains("file c1.tsv rows=2 tests=1 evaluated=1 unavailable=0 skipped=0 waiting=0\n"), "{got}");
    assert!(got.contains("file c2.tsv rows=4 tests=2"), "{got}");
    assert!(got.ends_with("total files=2 rows=6 tests=3 evaluated=3 unavailable=0 skipped=0 waiting=0\n"), "{got}");
}

#[test]
fn a_call_of_no_frames_has_a_line_for_each_leaf_of_its_type() {
    // The leaves come from the type of the output, not from a value: a struct { l, r } with 0 frames is `out.l=[]` and
    // `out.r=[]`, and an array of 2 channels is `out[0]=[]` and `out[1]=[]`. A call of `process` has the names too.
    let one = |event| case(vec![test("t", Verdict::Ok, None, vec![event])]);
    let leaves = [(".l", None), (".r", None)];
    let (text, _) = case_text("a", &one(render(shaped(&leaves, vec![], Some(vec![])))), false);
    assert!(text.ends_with("out.l=[]\nout.r=[]\n"), "{text}");
    let (text, _) = case_text("a", &one(render(shaped(&[("", Some(2))], vec![], Some(vec![])))), false);
    assert!(text.ends_with("out[0]=[]\nout[1]=[]\n"), "{text}");
    let process = Event::Process { state: 0, run: shaped(&leaves, vec![], Some(vec![])) };
    let (text, _) = case_text("a", &one(process), false);
    assert!(text.ends_with("process 0 cfg k=-3\nout.l=[]\nout.r=[]\n"), "{text}");
}
