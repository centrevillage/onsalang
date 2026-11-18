//! `print.rs` on events built by hand: each text is worked out from §11.6 (the generated API: the order of the arguments,
//! `Config`, `Params`, `In`, `Out`) and §3.4 (the bits of a float, a NaN is not equal to itself).

use onsa_tests::flow_ref::flow::PanicAt;
use onsa_tests::flow_ref::value::{IntKind, Value};
use onsa_tests::flow_ref::walk::{Event, Panic, Run, TestRun, Types, Verdict};

use super::print::{Origin, Printed, print_test};

fn f(x: f32) -> Value {
    Value::F32(x)
}

fn run(shape: &[(&str, Option<usize>)], leaves: &[&str], inputs: &[(&str, &str, Vec<Value>)]) -> Run {
    Run {
        shape: shape.iter().map(|(p, c)| (p.to_string(), *c)).collect(),
        types: Types {
            inputs: inputs.iter().map(|(_, t, _)| t.to_string()).collect(),
            leaves: leaves.iter().map(|t| t.to_string()).collect(),
        },
        config: vec![],
        params: vec![],
        frames: None,
        inputs: inputs.iter().map(|(n, _, c)| (n.to_string(), c.clone())).collect(),
        outs: None,
    }
}

fn test(events: Vec<Event>, panic: Option<Panic>) -> TestRun {
    TestRun { name: "t".into(), file: String::new(), asserts: 0, panic, verdict: Verdict::Ok, events }
}

fn printed(events: Vec<Event>, panic: Option<Panic>) -> Printed {
    print_test(7, &test(events, panic)).expect("printable")
}

/// The text without its head and its closing line.
fn body(p: &Printed) -> Vec<&str> {
    let lines: Vec<&str> = p.text.lines().collect();
    assert_eq!((lines[0], lines[lines.len() - 1]), ("test \"flow_ref#0007 t\" {", "}"));
    lines[1..lines.len() - 1].to_vec()
}

#[test]
fn a_render_of_a_scalar_has_the_bits_of_its_input_and_an_assert_for_each_frame() {
    // acc sums its input: 1 2 3 gives 1 3 6 = 0x3f800000 0x40400000 0x40c00000; the rate 8.0 is 0x41000000.
    let mut r = run(&[("", None)], &["F32"], &[("x", "F32", vec![f(1.0), f(2.0), f(3.0)])]);
    r.outs = Some(vec![f(1.0), f(3.0), f(6.0)]);
    let p = printed(vec![Event::Render { flow: "m.acc".into(), sample_rate: 8.0, run: r }], None);
    assert_eq!(
        body(&p),
        [
            "let i0_0: [F32; 3] = [F32.from_bits(0x3f800000), F32.from_bits(0x40000000), F32.from_bits(0x40400000)]",
            "let o0 = acc.render(i0_0, F32.from_bits(0x41000000))",
            "assert o0.out[0].to_bits() == 0x3f800000",
            "assert o0.out[1].to_bits() == 0x40400000",
            "assert o0.out[2].to_bits() == 0x40c00000",
        ]
    );
    assert_eq!(p.panic_call, None);
}

#[test]
fn a_nan_is_not_equal_to_itself_and_the_sign_of_a_zero_is_in_its_bits() {
    let mut r = run(&[("", None)], &["F32"], &[("x", "F32", vec![f(f32::NAN), f(-0.0)])]);
    r.outs = Some(vec![f(f32::NAN), f(-0.0)]);
    let p = printed(vec![Event::Render { flow: "acc".into(), sample_rate: 8.0, run: r }], None);
    let asserts: Vec<&str> = body(&p).into_iter().filter(|l| l.starts_with("assert")).collect();
    assert_eq!(asserts, ["assert o0.out[0] != o0.out[0]", "assert o0.out[1].to_bits() == 0x80000000"]);
}

#[test]
fn an_f64_is_written_by_its_sixteen_digits_and_an_integer_or_a_bool_is_compared_with_equal() {
    let mut r = run(&[("", None)], &["I32"], &[]);
    r.frames = Some(2);
    r.params = vec![("g".into(), Value::F64(1.0)), ("on".into(), Value::Bool(true))];
    r.outs = Some(vec![Value::int(IntKind::I32, -3), Value::int(IntKind::I32, 7)]);
    let p = printed(vec![Event::Render { flow: "gen".into(), sample_rate: 8.0, run: r }], None);
    assert_eq!(
        body(&p),
        [
            "let o0 = gen.render(gen.Params { g: F64.from_bits(0x3ff0000000000000), on: true }, 2, F32.from_bits(0x41000000))",
            "assert o0.out[0] == -3",
            "assert o0.out[1] == 7",
        ]
    );
}

#[test]
fn a_state_is_made_with_its_config_and_read_by_process_and_reset() {
    // `rs` of reset_replay: init(Config { start: 3.0 }, 8.0), process with Params { g: 2.0 } over 2 frames, then reset.
    let mut p0 = run(&[("", None)], &["F32"], &[("x", "F32", vec![f(1.0), f(2.0)])]);
    p0.frames = Some(2);
    p0.params = vec![("g".into(), f(2.0))];
    p0.outs = Some(vec![f(18.0), f(20.0)]);
    let events = vec![
        Event::Init { state: 0, flow: "m.rs".into(), sample_rate: 8.0, config: vec![("start".into(), f(3.0))] },
        Event::Process { state: 0, run: p0 },
        Event::Reset { state: 0 },
    ];
    let p = printed(events, None);
    assert_eq!(
        body(&p),
        [
            "var s0 = rs.init(rs.Config { start: F32.from_bits(0x40400000) }, F32.from_bits(0x41000000))",
            "let i1_0: [F32; 2] = [F32.from_bits(0x3f800000), F32.from_bits(0x40000000)]",
            "var o1_0: [F32; 2] = [0.0; 2]",
            "rs.process(inout s0, rs.Params { g: F32.from_bits(0x40000000) }, i1_0, inout o1_0)",
            "assert o1_0[0].to_bits() == 0x41900000",
            "assert o1_0[1].to_bits() == 0x41a00000",
            "rs.reset(inout s0)",
        ]
    );
}

#[test]
fn channels_and_the_fields_of_a_struct_output_are_buffers_of_their_own() {
    // swap-like flow: two inputs (an `In`), and a struct output of a field `l` and a field `r` of two channels.
    let ins = [("a", "F32", vec![f(1.0)]), ("b", "F32", vec![f(2.0)])];
    let mut r = run(&[(".l", None), (".r", Some(2))], &["F32", "F32"], &ins);
    r.frames = Some(1);
    r.outs = Some(vec![Value::Struct(vec![f(1.0), Value::Array(vec![f(2.0), f(0.0)])])]);
    let events = vec![
        Event::Init { state: 0, flow: "swap".into(), sample_rate: 8.0, config: vec![] },
        Event::Process { state: 0, run: r },
    ];
    let p = printed(events, None);
    assert_eq!(
        body(&p),
        [
            "var s0 = swap.init(F32.from_bits(0x41000000))",
            "let i1_0: [F32; 1] = [F32.from_bits(0x3f800000)]",
            "let i1_1: [F32; 1] = [F32.from_bits(0x40000000)]",
            "var o1_0: [F32; 1] = [0.0; 1]",
            "var o1_1: [[F32; 1]; 2] = [[0.0; 1]; 2]",
            "swap.process(inout s0, swap.In { a: i1_0, b: i1_1 }, inout swap.Out { l: o1_0, r: o1_1 })",
            "assert o1_0[0].to_bits() == 0x3f800000",
            "assert o1_1[0][0].to_bits() == 0x40000000",
            "assert o1_1[1][0].to_bits() == 0x00000000",
        ]
    );
}

#[test]
fn a_call_with_no_frames_has_empty_columns_of_the_type_the_flow_declares() {
    let mut r = run(&[("", None)], &["I32"], &[("x", "I32", vec![])]);
    r.frames = Some(0);
    r.outs = Some(vec![]);
    let events = vec![
        Event::Init { state: 0, flow: "z".into(), sample_rate: 8.0, config: vec![] },
        Event::Process { state: 0, run: r },
    ];
    let p = printed(events, None);
    let text = body(&p);
    assert_eq!(&text[1..3], ["let i1_0: [I32; 0] = []", "var o1_0: [I32; 0] = [0; 0]"]);
    assert!(text.iter().all(|l| !l.starts_with("assert")));
}

#[test]
fn a_call_that_panicked_has_no_assert_and_the_printed_test_has_to_panic_at_it() {
    let r = run(&[("", None)], &["F32"], &[("x", "F32", vec![f(f32::NAN)])]);
    let events = vec![Event::Render { flow: "boom".into(), sample_rate: 8.0, run: r }];
    let p = printed(events, Some(Panic::Call(PanicAt::Sample(0))));
    // The result of the call is not read, so it is bound to `_` (§5.1).
    assert_eq!(body(&p)[1], "let _ = boom.render(i0_0, F32.from_bits(0x41000000))");
    assert_eq!(p.panic_call.as_deref(), Some("#0 render boom"));
    // A panic of an expression of the test is not a call: nothing is to panic in the interpreter.
    let r = run(&[("", None)], &["F32"], &[("x", "F32", vec![f(1.0)])]);
    let events = vec![Event::Render { flow: "boom".into(), sample_rate: 8.0, run: r }];
    assert_eq!(printed(events, Some(Panic::Eval)).panic_call, None);
}

#[test]
fn a_state_no_call_reads_is_bound_to_underscore() {
    let events = vec![Event::Init {
        state: 0,
        flow: "bad".into(),
        sample_rate: 8.0,
        config: vec![("n".into(), Value::int(IntKind::U32, 0))],
    }];
    let p = printed(events, Some(Panic::Call(PanicAt::Init)));
    assert_eq!(body(&p), ["let _ = bad.init(bad.Config { n: 0 }, F32.from_bits(0x41000000))"]);
}

#[test]
fn every_line_goes_back_to_its_call_and_an_assert_to_its_leaf_and_frame() {
    let mut r = run(&[("", Some(2))], &["F32"], &[("x", "F32", vec![f(1.0)])]);
    r.outs = Some(vec![Value::Array(vec![f(1.0), f(0.0)])]);
    let events = vec![
        Event::Init { state: 0, flow: "m.w".into(), sample_rate: 8.0, config: vec![] },
        Event::Render { flow: "m.w".into(), sample_rate: 8.0, run: r },
    ];
    let p = printed(events, None);
    assert_eq!(p.lines.len(), p.text.lines().count());
    let at = |i: usize| p.lines[i].clone();
    assert_eq!(at(0), Origin::default());
    assert_eq!(at(1), Origin { call: "#0 init 0 m.w".into(), assert: None });
    // `let _ = ..` for the state (no call reads it), then the input, the render and its two channels' asserts.
    assert_eq!(at(3), Origin { call: "#1 render m.w".into(), assert: None });
    assert_eq!(at(4), Origin { call: "#1 render m.w".into(), assert: Some("out[0] frame 0".into()) });
    assert_eq!(at(5), Origin { call: "#1 render m.w".into(), assert: Some("out[1] frame 0".into()) });
    assert!(p.text.contains("assert o1.out[1][0].to_bits() == 0x00000000"));
}

#[test]
fn a_value_no_literal_writes_makes_the_test_unprintable_with_the_reason() {
    let mut r = run(&[("", None)], &["Char"], &[("x", "F32", vec![Value::Char('a')])]);
    r.outs = Some(vec![]);
    let e = vec![Event::Render { flow: "c".into(), sample_rate: 8.0, run: r }];
    let why = print_test(0, &test(e, None)).unwrap_err();
    assert!(why.contains("no float, integer or Bool"), "{why}");
    let mut r = run(&[("", None)], &["Char"], &[]);
    r.frames = Some(1);
    r.outs = Some(vec![]);
    let e = vec![
        Event::Init { state: 0, flow: "c".into(), sample_rate: 8.0, config: vec![] },
        Event::Process { state: 0, run: r },
    ];
    assert_eq!(print_test(0, &test(e, None)).unwrap_err(), "an output of the type Char");
}
