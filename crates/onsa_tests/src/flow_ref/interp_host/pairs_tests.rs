//! The evaluator through the interpreter host against the interpreter called directly (W7-19 U1, the sweep of the
//! break side kept as a test, `rules/leader.md` 4.9). Each case is a `const Cn: T = <expr>` the evaluator evaluates
//! (the calls go to the host) and an `rt fn dn() -> T { <expr> }` the interpreter runs in the Core of the case; both
//! are written as text bit by bit (a float by its bits, so a NaN and its payload and the sign of a zero are told),
//! and the two texts are compared. No value is written down here: the expectation is that the two sides are the same,
//! or both panic. The ends of the integers and the special bits of the floats are fixed, not drawn.

use super::*;
use crate::flow_ref::expr::Frame;
use crate::flow_ref::expr_tests::{def_named, with_checked};
use crate::flow_ref::sema_view::View;

/// An integer of the evaluator, a float by its bits, and the rest by its shape.
fn shown(v: &Value) -> String {
    let all = |vs: &[Value]| vs.iter().map(shown).collect::<Vec<_>>().join(",");
    match v {
        Value::Int(k, n, _) => format!("{}:{n}", k.name()),
        Value::F32(x) => format!("F32:{:08x}", x.to_bits()),
        Value::F64(x) => format!("F64:{:016x}", x.to_bits()),
        Value::Bool(b) => format!("B:{b}"),
        Value::Char(c) => format!("C:{}", *c as u32),
        Value::Unit => "()".into(),
        Value::Tuple(xs, _) => format!("T({})", all(xs)),
        Value::Array(xs) => format!("A[{}]", all(xs)),
        Value::Struct(xs) => format!("S{{{}}}", all(xs)),
        Value::Enum { tag, fields } => format!("E{tag}({})", all(fields)),
    }
}

/// The same text for a value of the interpreter (it is written from the interpreter's own variants).
fn shown_interp(v: &IValue) -> String {
    let all = |xs: &[IValue]| xs.iter().map(shown_interp).collect::<Vec<_>>().join(",");
    match v {
        IValue::I8(x) => format!("I8:{x}"),
        IValue::I16(x) => format!("I16:{x}"),
        IValue::I32(x) => format!("I32:{x}"),
        IValue::I64(x) => format!("I64:{x}"),
        IValue::U8(x) => format!("U8:{x}"),
        IValue::U16(x) => format!("U16:{x}"),
        IValue::U32(x) => format!("U32:{x}"),
        IValue::U64(x) => format!("U64:{x}"),
        IValue::F32(x) => format!("F32:{:08x}", x.to_bits()),
        IValue::F64(x) => format!("F64:{:016x}", x.to_bits()),
        IValue::Bool(b) => format!("B:{b}"),
        IValue::Char(c) => format!("C:{}", *c as u32),
        IValue::Unit => "()".into(),
        IValue::Tuple(xs) => format!("T({})", all(xs)),
        IValue::Array(a) => {
            format!("A[{}]", (0..a.len()).map(|i| shown_interp(&a.get(i))).collect::<Vec<_>>().join(","))
        }
        IValue::Struct(xs) => format!("S{{{}}}", all(xs)),
        IValue::Enum { tag, fields } => format!("E{tag}({})", all(fields)),
        _ => "OTHER".into(),
    }
}

const INTS: [(&str, &str, &str); 8] = [
    ("I8", "-128", "127"),
    ("I16", "-32768", "32767"),
    ("I32", "-2147483648", "2147483647"),
    ("I64", "-9223372036854775808", "9223372036854775807"),
    ("U8", "0", "255"),
    ("U16", "0", "65535"),
    ("U32", "0", "4294967295"),
    ("U64", "0", "18446744073709551615"),
];
/// Special bits of an F32: 0, -0.0, 1.0, +inf, a NaN with a payload, the least subnormal, the greatest finite.
const F32_BITS: [u32; 7] = [0, 0x8000_0000, 0x3f80_0000, 0x7f80_0000, 0xffc0_0001, 1, 0x7f7f_ffff];
/// The same for an F64.
const F64_BITS: [u64; 6] =
    [1 << 63, 0x3ff0_0000_0000_0000, 0xfff0_0000_0000_0000, 0xfff8_0000_0000_0001, 1, 0x7fef_ffff_ffff_ffff];

/// The cases: the type and the expression. The first part is the round trip of the values through a function with a
/// `for` (which the interpreter runs), the second the std functions through their wrappers.
fn cases() -> Vec<(String, String)> {
    let mut cs: Vec<(String, String)> = vec![];
    let mut add = |t: &str, e: String| cs.push((t.to_string(), e));
    for (t, lo, hi) in INTS {
        let at = |v: &str| {
            format!("keep_{}({})", t.to_lowercase(), if v.starts_with('-') { format!("({v})") } else { v.to_string() })
        };
        add(t, at(lo));
        add(t, at(hi));
    }
    for b in F32_BITS {
        add("F32", format!("keep_f32(F32.from_bits({b}))"));
    }
    for b in F64_BITS {
        add("F64", format!("keep_f64(F64.from_bits({b}))"));
    }
    add("[[F32; 2]; 2]", "keep_a([[1.0, -0.0], [F32.from_bits(4290772993), 2.5]])".into());
    add("P", "keep_p(P { x: -128, y: F64.from_bits(9223372036854775808), z: [255, 0] })".into());
    add("Mode", "keep_m(Mode.Both(18446744073709551615, F32.from_bits(2147483648)))".into());
    add("Option[Option[F32]]", "keep_o(Some(Some(-0.0)))".into());
    // std: the floats, through `target` functions, ones with a body and ones that are generic.
    for b in &F32_BITS[..5] {
        let x = format!("F32.from_bits({b})");
        for f in ["sqrt", "floor", "round", "abs", "exp"] {
            add("F32", format!("{f}({x})"));
        }
        add("U32", format!("{x}.to_bits()"));
    }
    for b in &F64_BITS[..3] {
        let x = format!("F64.from_bits({b})");
        for f in ["ceil", "trunc", "log2"] {
            add("F64", format!("{f}({x})"));
        }
    }
    let (nan, one) = ("F32.from_bits(2143289344)", "1.0");
    for f in ["pow", "min", "max"] {
        add("F32", format!("{f}({nan}, {one})"));
        add("F32", format!("{f}({one}, F32.from_bits(2147483648))"));
    }
    add("F32", "sum([1.0, F32.from_bits(2147483648), 3.5])".into());
    // std: the integers, `checked_*` among them (a body of expressions that calls a private `target` function).
    for (t, _, _) in INTS {
        let (lo, hi) = (format!("MIN_{t}"), format!("MAX_{t}"));
        add(&format!("Option[{t}]"), format!("{hi}.checked_add(1)"));
        add(&format!("Option[{t}]"), format!("{lo}.checked_sub(1)"));
        add(&format!("Option[{t}]"), format!("{lo}.checked_mul(2)"));
    }
    add("Option[I8]", "MAX_I8.checked_div(0)".into());
    add("Option[I8]", "MIN_I8.checked_neg()".into());
    add("Option[I16]", "I16.narrow_from(32768)".into());
    add("Option[U8]", "U8.narrow_from(200)".into());
    add("I8", "abs(MIN_I8)".into());
    add("I32", "I32.trunc_from(F32.from_bits(2143289344))".into());
    add("I32", "I32.trunc_sat_from(F32.from_bits(2143289344))".into());
    add("F32", "F32.round_from(16777217)".into());
    add("U32", "[1, 2, 3].len()".into());
    add("Option[U8]", "[255, 2].get(2)".into());
    add("U8", "Some(255).unwrap()".into());
    cs
}

fn source(cs: &[(String, String)]) -> String {
    let mut src = String::from("struct P { x: I8, y: F64, z: [U8; 2] }\nenum Mode { Off, On(I32), Both(U64, F32) }\n");
    for f in "exp log2 sqrt floor ceil trunc round abs pow min max sum".split(' ') {
        src.push_str(&format!("use std.math.{f}\n"));
    }
    let keep = |name: &str, t: &str| {
        format!("rt fn keep_{name}(x: {t}) -> {t} {{\n  var y = x\n  for _ in 0..<1 {{ y = y }}\n  y\n}}\n")
    };
    for (t, lo, hi) in INTS {
        src.push_str(&format!("const MIN_{t}: {t} = {lo}\nconst MAX_{t}: {t} = {hi}\n"));
        src.push_str(&keep(&t.to_lowercase(), t));
    }
    for (name, t) in [
        ("f32", "F32"),
        ("f64", "F64"),
        ("a", "[[F32; 2]; 2]"),
        ("p", "P"),
        ("m", "Mode"),
        ("o", "Option[Option[F32]]"),
    ] {
        src.push_str(&keep(name, t));
    }
    for (i, (t, e)) in cs.iter().enumerate() {
        src.push_str(&format!("const C{i}: {t} = {e}\nrt fn d{i}() -> {t} {{ {e} }}\n"));
    }
    src
}

/// For each case, what the evaluator gives and what the interpreter gives, as text (`PANIC` for a panic of either).
fn run_all(cs: Vec<(String, String)>, core: bool) -> Vec<(String, String)> {
    let src = source(&cs);
    with_checked(&src, true, move |a| {
        let module = onsa_driver::lower_core(a).expect("the case lowers");
        let wrappers = Wrappers::default();
        let mut host = InterpHost::new(core.then_some(&module), &wrappers);
        let interp = Interp::new(&module);
        let view = View::new(a);
        (0..cs.len())
            .map(|i| {
                let (body, init) = view.const_init(def_named(a, &format!("C{i}"))).expect("a const with its tables");
                let mut frame = Frame::new(body);
                frame.host = Some(&mut host as &mut dyn FnHost);
                let evaluated = match frame.eval(init) {
                    Ok(v) => shown(&v),
                    Err(s) if matches!(s.fault, Fault::Panic(_)) => "PANIC".into(),
                    Err(s) => format!("{:?}", s.fault),
                };
                let at = module.fns.iter().position(|f| f.name == format!("t.d{i}")).expect("the function of the case");
                let direct = match onsa_driver::guard(|| interp.call(FnId(at as u32), vec![])) {
                    Ok(Ok(v)) => shown_interp(&v),
                    Ok(Err(Failure::Panic(_))) => "PANIC".into(),
                    Ok(Err(Failure::Unsupported(_))) => "UNSUPPORTED".into(),
                    Err(_) => "INTERNAL".into(),
                };
                (evaluated, direct)
            })
            .collect()
    })
}

#[test]
fn the_evaluator_through_the_host_is_the_interpreter_on_the_ends_of_the_values_and_the_std_functions() {
    let cs = cases();
    assert!(cs.len() > 90, "{} cases", cs.len());
    for core in [true, false] {
        // A case with no Core (the host has none of the case): the std functions are the same, the round trips are
        // functions of the case and `Unavailable`; only the std part is compared.
        let got = run_all(cs.clone(), core);
        let rows = cs.iter().zip(&got).filter(|((_, e), _)| core || !e.starts_with("keep_"));
        let bad: Vec<String> = rows
            .filter(|(_, (evaluated, direct))| evaluated != direct)
            .map(|((t, e), (evaluated, direct))| format!("{e}: {t}\n  evaluator {evaluated}\n  interpreter {direct}"))
            .collect();
        assert!(bad.is_empty(), "core {core}: {} cases differ:\n{}", bad.len(), bad.join("\n"));
    }
}
