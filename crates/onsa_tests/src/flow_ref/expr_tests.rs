//! The tests of the expressions of the evaluator (W7-01 U3): a small source is checked
//! (the entry of `api.md` 1.3), a `const` or the body of a flow is evaluated, and the value
//! is compared with the one worked out by hand from the spec. A source that the check
//! rules out is not evaluated.

use onsa_driver::{Analyzed, Loaded, PackageInput, analyze_loaded};
use onsa_sema::ty::FloatKind;
use onsa_sema::{ConstValue, DefId, DefKind, Target, Ty};

use super::expr::{Eval, Frame, LIMITS, Limits, Stop, from_const};
use super::scalar::{Fault, PanicKind};
use super::sema_view::{Body, Stage, View, input_stage};
use super::value::{IntKind, Value};

/// Check `src` as one file in a thread with a large stack (`rules/common.md` 3.4) and run `f` on it.
/// `clean`: the check has no diagnostic.
pub(super) fn with_checked<T: Send + 'static>(
    src: &str,
    clean: bool,
    f: impl FnOnce(&Analyzed) -> T + Send + 'static,
) -> T {
    let src = src.to_string();
    onsa_diag::stack::run(move || {
        let mut loaded = Loaded::from_input(PackageInput::single_file("t.onsa", &src)).expect("the input loads");
        let analyzed = analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        if clean {
            let text = onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics);
            assert!(analyzed.diagnostics.is_empty(), "the source has diagnostics:\n{text}");
        }
        f(&analyzed)
    })
}

pub(super) fn def_named(a: &Analyzed, name: &str) -> DefId {
    let module = a.analysis.module_of_file(a.pkg.modules[0].file).expect("the module of the file");
    a.analysis
        .defs_of_module(module)
        .find(|(_, d)| d.name == name)
        .map(|(id, _)| id)
        .expect("a declaration of the name")
}

/// The values of the initializers of the constants `names`, evaluated by the evaluator (not read from the table).
pub(super) fn consts(src: &str, names: &'static [&'static str]) -> Vec<Eval> {
    consts_with(src, names, || LIMITS)
}

/// [`consts`] under the limits `limits` gives, called on the thread of the evaluation (where the stack is measured).
pub(super) fn consts_with(src: &str, names: &'static [&'static str], limits: fn() -> Limits) -> Vec<Eval> {
    with_checked(src, true, move |a| {
        let view = View::new(a);
        names
            .iter()
            .map(|n| {
                let (body, init) = view.const_init(def_named(a, n)).expect("a const with its tables");
                let mut frame = Frame::new(body);
                frame.limits = limits();
                frame.eval(init)
            })
            .collect()
    })
}

/// The body of the flow `name` with the inputs bound by name.
pub(super) fn flow(src: &str, name: &'static str, inputs: Vec<(&'static str, Value)>) -> Eval {
    flow_with(src, name, inputs, || LIMITS)
}

/// [`flow`] under the limits `limits` gives, called on the thread of the evaluation (where the stack is measured).
pub(super) fn flow_with(
    src: &str,
    name: &'static str,
    inputs: Vec<(&'static str, Value)>,
    limits: fn() -> Limits,
) -> Eval {
    with_checked(src, true, move |a| {
        let (view, def) = (View::new(a), def_named(a, name));
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("{name} is not a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let mut frame = Frame::new(body);
        frame.limits = limits();
        for (input, v) in inputs {
            frame.locals.insert(body.input(input).expect("an input of the flow"), v);
        }
        frame.eval(decl.body)
    })
}

pub(super) fn is(r: &Eval, want: &Value) -> bool {
    matches!(r, Ok(v) if v.same(want))
}

/// The panic of `r`, with the text of the expression it is at.
pub(super) fn panic_at(r: &Eval, src: &str) -> (PanicKind, String) {
    match r {
        Err(Stop { fault: Fault::Panic(kind), at }) => (*kind, src[at.start as usize..at.end as usize].to_string()),
        other => panic!("not a panic: {other:?}"),
    }
}

pub(super) fn i32v(v: i128) -> Value {
    Value::int(IntKind::I32, v)
}

const OPERATORS: &str = "
const V_A: I32 = 7 * 6 - 2 * 3
const V_B: I8 = -128
const V_C: F32 = 0.5 + 0.25
const V_D: F32 = 16777216.0 + 1.0
const V_E: F64 = 1.0 / 3.0
const V_Z: F32 = -0.0
const V_SHL: U8 = 1 << 7
const V_SHL2: I8 = 64 << 1
const V_WRAP: U8 = 250 +% 10
const V_SAT: U8 = 250 +| 10
const V_SATS: I8 = -100 -| 100
const V_AND: U8 = 12 & 10
const V_OR: U8 = 12 | 10
const V_XOR: U8 = 12 ^ 10
const V_NOT: U8 = !0
const V_LT: Bool = 3 < 4
const V_TF: Bool = true && false
const V_CH: Bool = 'a' < 'b'
";

#[test]
fn literals_and_operators_by_hand() {
    let names = &[
        "V_A", "V_B", "V_C", "V_D", "V_E", "V_Z", "V_SHL", "V_SHL2", "V_WRAP", "V_SAT", "V_SATS", "V_AND", "V_OR",
        "V_XOR", "V_NOT", "V_LT", "V_TF", "V_CH",
    ];
    let u8v = |v| Value::int(IntKind::U8, v);
    let want = [
        // §3.1: `*` binds tighter than `-`: 42 - 6.
        i32v(36),
        // §4.7: the `-` of `-128` is a part of the literal, which is out of the range of an `I8` without it.
        Value::int(IntKind::I8, -128),
        Value::F32(0.75),
        // §3.4: 2^24 + 1 is half way between 2^24 and 2^24 + 2, and the even one is 2^24.
        Value::F32(16777216.0),
        // 1/3 in binary64 is 0x3FD5555555555555 (the 53 bits of 0.0101..., rounded to nearest).
        Value::F64(f64::from_bits(0x3FD5_5555_5555_5555)),
        // The sign of a zero literal is kept (§3.4).
        Value::F32(-0.0),
        u8v(128),
        // §3.4: `<<` drops the bits that leave the type: 0b0100_0000 << 1 is 0b1000_0000, -128 in an `I8`.
        Value::int(IntKind::I8, -128),
        u8v(4),
        u8v(255),
        Value::int(IntKind::I8, -128),
        u8v(8),
        u8v(14),
        u8v(6),
        u8v(255),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(true),
    ];
    let got = consts(OPERATORS, names);
    for ((name, got), want) in names.iter().zip(&got).zip(&want) {
        assert!(is(got, want), "{name}: got {got:?}, want {want:?}");
    }
}

#[test]
fn constants_that_read_constants_and_the_associated_ones() {
    let src = "
const V_K: I16 = 100
const V_KF: F32 = V_K as F32
const V_K64: I64 = V_K as I64
const V_K1: I32 = (V_K as I32) + 1
const V_A: I32 = 5 * 5
const V_B: I32 = V_A + 1
const V_C: I32 = V_B + 1
const V_INF: F32 = F32.INFINITY
const V_NEG_INF: F32 = -F32.INFINITY
const V_NAN_EQ: Bool = F32.NAN == F32.NAN
const V_NAN_NE: Bool = F32.NAN != F32.NAN
const V_PI: F32 = F32.PI
";
    let names = &["V_KF", "V_K64", "V_K1", "V_B", "V_C", "V_INF", "V_NEG_INF", "V_NAN_EQ", "V_NAN_NE", "V_PI"];
    let want = [
        // §3.3: `I16` into `F32` loses nothing, and the value does not change.
        Value::F32(100.0),
        Value::int(IntKind::I64, 100),
        i32v(101),
        // `V_A` is 25 and has no value in the checker's table (`*` is not evaluated there): its initializer is.
        i32v(26),
        i32v(27),
        // `F32.INFINITY` is `1.0 / 0.0` in std, and §3.4: a non-zero number over 0 is an infinity of its sign.
        Value::F32(f32::INFINITY),
        Value::F32(f32::NEG_INFINITY),
        // §3.4: NaN is equal to nothing, itself included.
        Value::Bool(false),
        Value::Bool(true),
        // pi in binary32 is 0x40490FDB.
        Value::F32(f32::from_bits(0x4049_0FDB)),
    ];
    let got = consts(src, names);
    for ((name, got), want) in names.iter().zip(&got).zip(&want) {
        assert!(is(got, want), "{name}: got {got:?}, want {want:?}");
    }
}

#[test]
fn the_value_of_the_table_and_the_initializer_are_the_same_value() {
    // `F32.PI` has a row in the checker's table, and its initializer is a literal: the evaluator reads
    // the row for the name and evaluates the literal for the same constant, and they agree.
    let src = "const V_PI: F32 = F32.PI\nconst V_BIG: I64 = 9000000000000000000";
    let (by_row, by_init, big_row, big_init) = with_checked(src, true, |a| {
        let view = View::new(a);
        let (body, init) = view.const_init(def_named(a, "V_PI")).unwrap();
        let by_row = Frame::new(body).eval(init);
        let Target::Const { def, .. } = body.target(init).unwrap() else { panic!("a const name") };
        assert!(view.const_value(*def).is_some(), "F32.PI has a row");
        let (std_body, std_init) = view.const_init(*def).unwrap();
        let by_init = Frame::new(std_body).eval(std_init);
        let (big, big_expr) = view.const_init(def_named(a, "V_BIG")).unwrap();
        (by_row, by_init, Frame::new(big).eval(big_expr), view.const_value(def_named(a, "V_BIG")).is_some())
    });
    assert!(is(&by_row, &Value::F32(f32::from_bits(0x4049_0FDB))), "{by_row:?}");
    assert!(is(&by_init, &Value::F32(f32::from_bits(0x4049_0FDB))), "{by_init:?}");
    assert!(is(&big_row, &Value::int(IntKind::I64, 9_000_000_000_000_000_000)), "{big_row:?}");
    assert!(big_init, "an integer literal has a row");
}

#[test]
fn a_flow_body_with_lets_and_inputs() {
    // x = 1.5: a = 3.0, b = 4.0, and b * b = 16.0.
    let src = "flow f(x: F32 at sample) -> F32 at sample {\n  let a = x * 2.0\n  let b = a + 1.0\n  b * b\n}";
    let r = flow(src, "f", vec![("x", Value::F32(1.5))]);
    assert!(is(&r, &Value::F32(16.0)), "{r:?}");
    // `at` changes neither the value nor the stage (§11.3), and a `block` value is read by a `sample` one.
    let src = "flow g(p: F32 at block) -> F32 at sample {\n  let q = p at sample\n  q * 2.0\n}";
    let r = flow(src, "g", vec![("p", Value::F32(1.5))]);
    assert!(is(&r, &Value::F32(3.0)), "{r:?}");
}

#[test]
fn the_clock_of_an_input_is_read_in_one_place() {
    let src = "flow f(a: I32 at init, b: F32 at block, c: F32 at sample) -> F32 at sample { c }";
    let stages = with_checked(src, true, |a| {
        let def = def_named(a, "f");
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("a flow") };
        decl.inputs.iter().map(input_stage).collect::<Vec<_>>()
    });
    assert_eq!(stages, [Stage::Init, Stage::Block, Stage::Sample]);
}

const PANICKY: &str = "
flow div(a: I32 at sample, b: I32 at sample) -> I32 at sample { a / b }
flow both(a: I32 at sample, b: I32 at sample, c: I32 at sample, d: I32 at sample) -> I32 at sample {
  (a / b) + (c / d)
}
flow order(a: I32 at sample, d: I32 at sample) -> I32 at sample { (a + 1) + (100 / d) }
flow and_(z: I32 at sample, c: Bool at sample) -> Bool at sample { c && 1 / z == 0 }
flow or_(z: I32 at sample, c: Bool at sample) -> Bool at sample { c || 1 / z == 0 }
flow pick(c: Bool at sample, d: Bool at sample, z: I32 at sample) -> I32 at sample {
  if c { 1 } else if d { 100 / z } else { 3 }
}
flow only(c: Bool at sample, z: I32 at sample) -> I32 at sample { if c { 100 / z } else { 7 } }
";

fn panicky(name: &'static str, inputs: Vec<(&'static str, Value)>) -> Eval {
    flow(PANICKY, name, inputs)
}

#[test]
fn a_panic_is_the_fault_at_the_expression() {
    // §3.4: `a / 0` panics; the span is of the division.
    let r = panicky("div", vec![("a", i32v(7)), ("b", i32v(0))]);
    assert_eq!(panic_at(&r, PANICKY), (PanicKind::DivZero, "a / b".to_string()));
    // 7 / 2 truncates toward zero, and -7 / 2 too.
    assert!(is(&panicky("div", vec![("a", i32v(7)), ("b", i32v(2))]), &i32v(3)));
    assert!(is(&panicky("div", vec![("a", i32v(-7)), ("b", i32v(2))]), &i32v(-3)));
    // `I32.MIN / -1` does not fit: overflow, at the same expression.
    let r = panicky("div", vec![("a", i32v(i32::MIN.into())), ("b", i32v(-1))]);
    assert_eq!(panic_at(&r, PANICKY), (PanicKind::Overflow, "a / b".to_string()));
}

#[test]
fn the_operands_are_evaluated_from_the_left() {
    // §3.5: the first expression that panics is reported. Both divisions panic; the left one is reported.
    let both = |a, b, c, d| panicky("both", vec![("a", i32v(a)), ("b", i32v(b)), ("c", i32v(c)), ("d", i32v(d))]);
    assert_eq!(panic_at(&both(1, 0, 1, 0), PANICKY), (PanicKind::DivZero, "a / b".to_string()));
    // Only the right one panics: it is reported (and the left, 4 / 2, is not the panic).
    assert_eq!(panic_at(&both(4, 2, 1, 0), PANICKY), (PanicKind::DivZero, "c / d".to_string()));
    assert!(is(&both(4, 2, 9, 3), &i32v(5)));
    // The left `a + 1` overflows (an overflow) and the right `100 / d` divides by zero: the left comes first.
    let r = panicky("order", vec![("a", i32v(i32::MAX.into())), ("d", i32v(0))]);
    assert_eq!(panic_at(&r, PANICKY), (PanicKind::Overflow, "a + 1".to_string()));
}

#[test]
fn the_right_of_a_short_circuit_is_evaluated_only_when_it_is_needed() {
    let (t, f) = (Value::Bool(true), Value::Bool(false));
    let and_ = |z, c: &Value| panicky("and_", vec![("z", i32v(z)), ("c", c.clone())]);
    let or_ = |z, c: &Value| panicky("or_", vec![("z", i32v(z)), ("c", c.clone())]);
    // §3.5: `false && 1 / z == 0` and `true || 1 / z == 0` do not evaluate `1 / z`, so z = 0 does not panic.
    assert!(is(&and_(0, &f), &f));
    assert!(is(&or_(0, &t), &t));
    // The right is evaluated when the left does not decide, and then it panics, at `1 / z`.
    assert_eq!(panic_at(&and_(0, &t), PANICKY), (PanicKind::DivZero, "1 / z".to_string()));
    assert_eq!(panic_at(&or_(0, &f), PANICKY), (PanicKind::DivZero, "1 / z".to_string()));
    // And its value is the value of the right: 1 / 1 == 0 is false, 1 / 2 == 0 is true.
    assert!(is(&and_(1, &t), &f));
    assert!(is(&or_(2, &f), &t));
}

#[test]
fn only_the_branch_that_is_taken_is_evaluated() {
    let (t, f) = (Value::Bool(true), Value::Bool(false));
    let only = |c: &Value, z| panicky("only", vec![("c", c.clone()), ("z", i32v(z))]);
    // §3.5, §11.5: the branch that is not taken may panic and does not.
    assert!(is(&only(&f, 0), &i32v(7)));
    assert!(is(&only(&t, 4), &i32v(25)));
    assert_eq!(panic_at(&only(&t, 0), PANICKY), (PanicKind::DivZero, "100 / z".to_string()));
    // The `else if`: the first condition decides, and the middle branch is not evaluated when it is not taken.
    let pick = |c: &Value, d: &Value, z| panicky("pick", vec![("c", c.clone()), ("d", d.clone()), ("z", i32v(z))]);
    assert!(is(&pick(&t, &t, 0), &i32v(1)));
    assert!(is(&pick(&f, &f, 0), &i32v(3)));
    assert!(is(&pick(&f, &t, 5), &i32v(20)));
    assert_eq!(panic_at(&pick(&f, &t, 0), PANICKY), (PanicKind::DivZero, "100 / z".to_string()));
}

#[test]
fn a_value_that_is_not_of_the_type_of_the_table_is_an_internal_error() {
    let src = "flow f(x: F32 at sample) -> F32 at sample { x }\nflow g(x: F32 at sample) -> F32 at sample { x * 2.0 }";
    // A `F64` bound to a `F32` name: the value of the name is of another type than the table says.
    let r = flow(src, "f", vec![("x", Value::F64(1.0))]);
    assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
    // The operands that do not agree: the evaluator does not guess a value.
    let r = flow(src, "g", vec![("x", i32v(1))]);
    assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
    // An input that is not bound is not a value either.
    let r = flow(src, "f", vec![]);
    assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
    // Not even for a type with one value: an unbound input of type `()` is not `()` (it is the `Unit` that agrees).
    let unit = "flow f(u: () at init) -> I32 at sample {\n  let v = u\n  1\n}";
    let r = flow(unit, "f", vec![]);
    assert!(matches!(r, Err(Stop { fault: Fault::Internal(_), .. })), "{r:?}");
    assert!(is(&flow(unit, "f", vec![("u", Value::Unit)]), &i32v(1)));
}

#[test]
fn the_forms_of_the_later_units_are_unavailable() {
    let src = "
flow call(x: F32 at sample) -> F32 at sample { prev~(x) }
rt fn twice(x: F32) -> F32 { x * 2.0 }
flow plain(x: F32 at sample) -> F32 at sample { twice(x) }
";
    for name in ["call", "plain"] {
        let r = flow(src, name, vec![("x", Value::F32(1.0))]);
        assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{name}: {r:?}");
    }
}

#[test]
fn a_body_the_check_rules_out_is_not_evaluated() {
    // A type error (E0401, an `I32` and a `F32`), and a name that is not there (E0302): the tables are not whole.
    for src in [
        "flow f(x: F32 at sample, n: I32 at sample) -> F32 at sample { x * n }",
        "flow f(x: F32 at sample) -> F32 at sample { let a = x * nothing_here\n a }",
    ] {
        let src = src.to_string();
        let r = with_checked(&src, false, |a| {
            assert!(!a.diagnostics.is_empty(), "the check rules the source out");
            View::new(a).body(def_named(a, "f")).err()
        });
        assert!(matches!(r, Some(Fault::Unavailable(_))), "{src}: {r:?}");
    }
}

#[test]
fn an_if_without_else_is_the_unit_when_it_is_not_taken() {
    // §7: an `if` without `else` has the type `()`, and its value is `()` when the condition is false.
    let src = "flow f(c: Bool at sample, x: F32 at sample) -> F32 at sample {\n  let u = if c { () }\n  x\n}";
    let r = flow(src, "f", vec![("c", Value::Bool(false)), ("x", Value::F32(2.5))]);
    assert!(is(&r, &Value::F32(2.5)), "{r:?}");
    // Taken, its value is the `()` of the branch, and the flow goes on.
    let r = flow(src, "f", vec![("c", Value::Bool(true)), ("x", Value::F32(2.5))]);
    assert!(is(&r, &Value::F32(2.5)), "{r:?}");
}

#[test]
fn a_float_literal_is_rounded_once_to_its_type() {
    // §2.3: the decimal value is rounded once, not through `F64`. 1.000000178813934326171875 is half way between
    // 0x3F800001 and 0x3F800002 (1 + 1.5 * 2^-23); the literal is a hair below it, so it is 0x3F800001, whereas
    // `F64` holds the half way exactly and rounding that to even gives 0x3F800002.
    let src = "const V_R: F32 = 1.00000017881393432617187499999\nconst V_N: F32 = -1.00000017881393432617187499999";
    let got = consts(src, &["V_R", "V_N"]);
    assert!(is(&got[0], &Value::F32(f32::from_bits(0x3F80_0001))), "{:?}", got[0]);
    assert!(is(&got[1], &Value::F32(f32::from_bits(0xBF80_0001))), "{:?}", got[1]);
}

// The depth: a body nests up to 256 levels (§2.5), and the evaluator is called in a thread of a large stack
// (`with_checked` is one, `onsa_diag::stack::run`). None of them overflows a stack on purpose (`rules/common.md` 3.1).

/// The flow `f(x: I32)` with `body` for its body, evaluated at x = 7.
fn at_seven(body: &str) -> Eval {
    flow(&format!("flow f(x: I32 at sample) -> I32 at sample {{ {body} }}"), "f", vec![("x", i32v(7))])
}

#[test]
fn a_deep_nesting_of_parentheses_and_operators_is_evaluated() {
    // 250 parentheses and the body block: 251 levels, under the 256 of §2.5.
    let parens = format!("{}x{}", "(".repeat(250), ")".repeat(250));
    assert!(is(&at_seven(&parens), &i32v(7)), "{:?}", at_seven(&parens));
    // §3.1: `+` is left associative, so 250 of them are a tree 250 high on the left; 7 + 250 = 257.
    let chain = format!("x{}", " + 1".repeat(250));
    assert!(is(&at_seven(&chain), &i32v(257)), "{:?}", at_seven(&chain));
    // 120 pairs of a parenthesis and a `+` on the right: 240 levels. 7 + 120 = 127.
    let nest = format!("{}x{}", "(1 + ".repeat(120), ")".repeat(120));
    assert!(is(&at_seven(&nest), &i32v(127)), "{:?}", at_seven(&nest));
    // 100 `if` with a block each, nested (200 levels): the values go through each level unchanged.
    let blocks = format!("{}x{}", "if true { ".repeat(100), " } else { 0 }".repeat(100));
    assert!(is(&at_seven(&blocks), &i32v(7)), "{:?}", at_seven(&blocks));
}

/// `C0 = 1 + 0` and `Ck = C(k-1) + 1`, for k up to `n`: the value of `Ck` is k + 1.
fn chain_of_constants(n: u32) -> String {
    let mut src = String::from("const C0: I32 = 1 + 0\n");
    for k in 1..=n {
        src += &format!("const C{k}: I32 = C{} + 1\n", k - 1);
    }
    src
}

#[test]
fn a_chain_of_constants_is_followed_to_the_limit_of_the_evaluator_and_not_past_it() {
    // The limit of the evaluator is 256 constants that read constants, not a limit of the spec: the chain of 256
    // has its value, and the one that is a constant longer stops with `Unavailable`, not with a wrong value.
    // (`1 + 0` has no row in the table of the checker, so each constant is evaluated here, not read.)
    let src = chain_of_constants(257);
    let names: &'static [&'static str] = &["C1", "C128", "C255", "C256", "C257"];
    let got = consts(&src, names);
    for ((name, got), want) in names.iter().zip(&got).zip([2, 129, 256, 257]) {
        assert!(is(got, &i32v(want)), "{name}: {got:?}");
    }
    assert!(matches!(got[4], Err(Stop { fault: Fault::Unavailable(_), .. })), "C257: {:?}", got[4]);
}

fn kinds() -> Vec<(Value, Ty)> {
    use IntKind::*;
    vec![
        (Value::int(I32, 1), Ty::Int(I32)),
        (Value::int(I8, 1), Ty::Int(I8)),
        (Value::int(U64, 1), Ty::Int(U64)),
        (Value::F32(1.0), Ty::Float(FloatKind::F32)),
        (Value::F64(1.0), Ty::Float(FloatKind::F64)),
        (Value::Bool(true), Ty::Bool),
        (Value::Char('a'), Ty::Char),
        (Value::Unit, Ty::Unit),
    ]
}

#[test]
fn a_value_agrees_with_its_own_type_and_no_other() {
    // Each scalar value agrees with the type of its kind and with none of the others: the kinds of the integers,
    // the two floats, `Char` and `()` are told apart (`Bool` is not a `Char`, `()` is not a `Bool`).
    let all = kinds();
    with_checked("", true, move |a| {
        for (i, (v, _)) in all.iter().enumerate() {
            for (j, (_, ty)) in all.iter().enumerate() {
                assert_eq!(v.agrees(ty, View::new(a)), Ok(i == j), "{v:?} against {ty:?}");
            }
        }
    });
}

#[test]
fn a_scalar_value_does_not_agree_with_a_type_that_is_not_a_scalar() {
    // U4 brings the aggregates; until then a scalar value for a tuple, a struct or a type that is not resolved is a
    // mistake of the evaluator, not a pass.
    with_checked("struct P { a: I32 }", true, |a| {
        let others = [Ty::Tuple(vec![]), Ty::Named(def_named(a, "P"), vec![]), Ty::Param(0), Ty::Error];
        for (v, _) in kinds() {
            for ty in &others {
                assert_eq!(v.agrees(ty, View::new(a)), Ok(false), "{v:?} against {ty:?}");
            }
        }
    });
}

#[test]
fn a_constant_of_the_table_is_read_as_the_type_says() {
    with_checked("", true, |a| scalar_rows(View::new(a)));
}

fn scalar_rows(view: View) {
    use IntKind::*;
    let f32t = Ty::Float(FloatKind::F32);
    let read = |c: ConstValue, ty: &Ty| from_const(view, &c, ty).expect("a value of the table");
    assert!(read(ConstValue::Int(-5), &Ty::Int(I16)).same(&Value::int(I16, -5)));
    assert!(read(ConstValue::Int(255), &Ty::Int(U8)).same(&Value::int(U8, 255)));
    assert!(read(ConstValue::Bool(true), &Ty::Bool).same(&Value::Bool(true)));
    assert!(read(ConstValue::Bool(false), &Ty::Bool).same(&Value::Bool(false)));
    assert!(read(ConstValue::Char('é'), &Ty::Char).same(&Value::Char('é')));
    assert!(read(ConstValue::Unit, &Ty::Unit).same(&Value::Unit));
    // A float of the table is held exactly: an `F64` keeps all its bits, an `F32` is the value of that width.
    assert!(read(ConstValue::Float(0.1), &Ty::Float(FloatKind::F64)).same(&Value::F64(0.1)));
    assert!(read(ConstValue::Float(f64::from(0.1f32)), &f32t).same(&Value::F32(0.1)));
    assert!(read(ConstValue::Float(-0.0), &f32t).same(&Value::F32(-0.0)));
    // A value of another kind than the type is not read as one: the table and the type must agree.
    for (c, ty) in [
        (ConstValue::Bool(true), Ty::Int(I32)),
        (ConstValue::Int(1), Ty::Bool),
        (ConstValue::Char('a'), Ty::Unit),
        (ConstValue::Unit, Ty::Char),
        (ConstValue::Float(1.0), Ty::Int(I32)),
    ] {
        assert!(matches!(from_const(view, &c, &ty), Err(Fault::Unavailable(_))), "{c:?} as {ty:?}");
    }
}

#[test]
fn an_expression_with_no_type_in_the_table_is_not_a_value() {
    // The type of the table is looked up for the value of every form: a form that has a value and no type is
    // `Unavailable`, not passed on (here the body block has none, and its tail `x` has).
    let src = "flow f(x: F32 at sample) -> F32 at sample { x }";
    let r = with_checked(src, true, |a| {
        let (view, def) = (View::new(a), def_named(a, "f"));
        let DefKind::Flow(decl) = &a.analysis.def(def).kind else { panic!("a flow") };
        let body = view.body(def).expect("a flow with its tables");
        let mut info = body.info.clone();
        assert!(info.expr_types.remove(&decl.body).is_some(), "the block has a type");
        let mut frame = Frame::new(Body { info: &info, ..body });
        frame.locals.insert(body.input("x").unwrap(), Value::F32(1.0));
        frame.eval(decl.body)
    });
    assert!(matches!(r, Err(Stop { fault: Fault::Unavailable(_), .. })), "{r:?}");
}

#[test]
fn the_inputs_of_a_flow_are_its_parameters_and_not_its_lets() {
    let src = "flow f(x: I32 at sample, y: I32 at block) -> I32 at sample {\n  let a = x\n  a + y\n}";
    let found = with_checked(src, true, |a| {
        let body = View::new(a).body(def_named(a, "f")).expect("a flow with its tables");
        ["x", "y", "a", "nothing"].map(|n| body.input(n).is_some())
    });
    // A `let` is a local too, and not an input: the name `a` is found among the locals, not among the parameters.
    assert_eq!(found, [true, true, false, false]);
}
