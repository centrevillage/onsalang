//! Tests of the one grammar of the numbers ([`crate::literal::number`]),
//! the reading of the `.` after an integer (S-350), the values of the
//! literals (R-20, R-45, S-211) and the candidates of the rows of the
//! numbers written as in other languages (S-62, S-63): each candidate takes
//! one form away, so that applying them one after the other ends with a
//! number of Onsa.

use onsa_diag::FileId;

use crate::literal::{
    Base, FloatRange, FloatWidth, Form, Invalid, Point, canonical_number, float_key, float_value, int_value, number,
    point_after_int,
};

#[test]
fn the_canonical_spelling_of_each_number() {
    // `spec/tools.md` §3.2 (S-62, S-126): each rule of the closed list, and what stays.
    let cases = [
        ("0X1f", "0x1F"),
        ("0xff_ff", "0xFF_FF"),
        ("0x_1F", "0x1F"),
        ("0x001F", "0x001F"),
        ("0B1__0_", "0b1_0"),
        ("1__000", "1_000"),
        ("1_", "1"),
        ("0", "0"),
        ("42", "42"),
        ("1E3", "1e3"),
        ("1e+3", "1e3"),
        ("1E+0_3", "1e0_3"),
        ("1e-03", "1e-03"),
        ("1e_3", "1e3"),
        ("01.5", "1.5"),
        ("00.5", "0.5"),
        ("0_0_1_000.0", "1_000.0"),
        ("1.50", "1.50"),
        ("1_.5_", "1.5"),
        ("1.0_e_3", "1.0e3"),
        ("0.0", "0.0"),
    ];
    for (text, want) in cases {
        assert_eq!(canonical_number(text).as_deref(), Some(want), "{text}");
        // Idempotent, and the same token.
        assert_eq!(canonical_number(want).as_deref(), Some(want), "{want}");
        assert_eq!(number(want).form, number(text).form, "{text}");
    }
    for text in ["0o17", "017", "1u8", "1.", "1.e3", "0x", "", "t", "1e3x"] {
        assert_eq!(canonical_number(text), None, "{text}");
    }
}

#[test]
fn the_key_of_a_float_is_its_exact_value() {
    // `spec/tools.md` §3.5: every spelling of a value has one key.
    for text in ["1.0e3", "1000.0", "1_000.0", "10e2", "1E+3", "01000.000", "0.001e6", "1e0_3"] {
        assert_eq!(float_key(text), "1e3", "{text}");
    }
    for (text, want) in [("0.0", "0e0"), ("00.000e-9", "0e0"), ("2.5e-7", "25e-8"), ("0.1", "1e-1"), ("120.0", "12e1")]
    {
        assert_eq!(float_key(text), want, "{text}");
    }
    // An exponent of any length: the spellings of one value have one key (no machine integer
    // overflows), and two values two keys.
    let big = "170141183460469231731687303715884105728"; // 2^127, one more than `i128::MAX`
    assert_eq!(float_key(&format!("1e{big}")), float_key(&format!("1E+{big}")));
    assert_eq!(float_key(&format!("1e{big}")), format!("1e{big}"));
    assert_eq!(float_key(&format!("0.5E-{big}")), float_key("5e-170141183460469231731687303715884105729"));
    assert_eq!(float_key(&format!("0.5E-{big}")), "5e-170141183460469231731687303715884105729");
    assert_ne!(float_key(&format!("1e{big}")), float_key("1e170141183460469231731687303715884105729"));
    assert_eq!(
        float_key("10e99999999999999999999999999999999999999999"),
        float_key("1e1_00000000000000000000000000000000000000000")
    );
    assert_eq!(float_key("100.0e-1"), "1e1");
    assert_eq!(float_key("0.01e1"), "1e-1");
    assert_eq!(float_key("1.5e-0"), "15e-1");
    // A float whose power of ten is 0 is no integer: `1.0` is `1e0`, the integer `1` is `1`.
    assert_eq!(float_key("1.0"), "1e0");
    // Two values a rounding to `f64` would make one keep two keys.
    assert_ne!(float_key("1.0"), float_key("1.00000000000000000001"));
    assert_ne!(float_key("0.1"), float_key("0.1000000000000000055511151231257827"));
}

#[test]
fn the_form_of_each_number() {
    use Form::*;
    let cases: &[(&str, Form, &str)] = &[
        ("42", Int, "42"),
        ("0", Int, "0"),
        ("0_", Int, "0_"),
        ("1__000", Int, "1__000"),
        ("0X1f", Int, "0X1f"),
        ("0B101", Int, "0B101"),
        ("0x_1F", Int, "0x_1F"),
        ("1.5", Float, "1.5"),
        ("48e3", Float, "48e3"),
        ("1E+3", Float, "1E+3"),
        ("1e_3", Float, "1e_3"),
        ("1e3_", Float, "1e3_"),
        ("01.5", Float, "01.5"),
        ("017e3", Float, "017e3"),
        ("1u8", Suffix, "1"),
        ("1_000_u32", Suffix, "1_000"),
        ("0x1F_u8", Suffix, "0x1F"),
        ("100ul", Suffix, "100"),
        ("1ULL", Suffix, "1"),
        ("1f32", Suffix, "1"),
        ("2.5f", Suffix, "2.5"),
        ("1e3F", Suffix, "1e3"),
        ("0o17u8", Suffix, "0o17"),
        ("017u8", Suffix, "017"),
        ("1.e3f", Suffix, "1.e3"),
        ("0o17", Octal, "0o17"),
        ("0O1_7", Octal, "0O1_7"),
        ("017", LeadingZero, "017"),
        ("00", LeadingZero, "00"),
        ("0_7", LeadingZero, "0_7"),
        ("08", LeadingZero, "08"),
        ("089", LeadingZero, "089"),
        ("0_17", LeadingZero, "0_17"),
        ("2.5_e1", Float, "2.5_e1"),
        ("1_e3", Float, "1_e3"),
        ("0b11f32", Suffix, "0b11"),
        ("1.", TrailingDot, "1."),
        ("1.e3", DotExponent, "1.e3"),
        ("1.E3", DotExponent, "1.E3"),
        ("1.e-3", DotExponent, "1.e-3"),
        ("1.e+3", DotExponent, "1.e+3"),
    ];
    for &(text, form, body) in cases {
        let n = number(text);
        assert_eq!((n.form, &text[..n.body], n.len), (form, body, text.len()), "{text}");
    }
    // The 16 digits of hexadecimal take `f`: `0x1f32` is an integer.
    assert_eq!(number("0x1f32").form, Int);
    assert_eq!(number("0x1F").base, Base::Hex);
    // The number ends before a `.` that is no point (S-350), and a
    // hexadecimal or binary one before any `.`.
    for (text, len) in [("1.abs()", 1), ("1.(x)", 1), ("1.f", 1), ("1..<4", 1), ("0x1F.5", 4), ("0b1.0", 3)] {
        assert_eq!(number(text).len, len, "{text}");
    }
}

#[test]
fn a_number_of_no_form_is_e0001_at_its_error() {
    let cases: &[(&str, Invalid, (usize, usize))] = &[
        ("123abc", Invalid::Suffix, (3, 6)),
        ("1lu", Invalid::Suffix, (1, 3)),
        ("1U8", Invalid::Suffix, (1, 3)),
        ("1I32", Invalid::Suffix, (1, 4)),
        ("1F32", Invalid::Suffix, (1, 4)),
        ("1Ul", Invalid::Suffix, (1, 3)),
        ("1f16", Invalid::Suffix, (1, 4)),
        ("1e", Invalid::Suffix, (1, 2)),
        ("0x_", Invalid::NoDigits, (0, 3)),
        ("0b", Invalid::NoDigits, (0, 2)),
        ("0o", Invalid::NoDigits, (0, 2)),
        ("0xG", Invalid::NoDigits, (0, 3)),
        ("0o19", Invalid::OctalDigit, (0, 4)),
        ("0o8u8", Invalid::OctalDigit, (0, 5)),
    ];
    for &(text, why, error) in cases {
        let n = number(text);
        assert_eq!((n.form, n.error), (Form::Invalid(why), error), "{text}");
    }
}

#[test]
fn the_point_after_an_integer() {
    use Point::*;
    for (rest, want) in [
        (".5", Fraction),
        (".e3", Exponent),
        (".E3", Exponent),
        (".e-3", Exponent),
        (".e+3", Exponent),
        (".e", Member),
        (".e_3", Member),
        (".abs()", Member),
        (".f", Member),
        (".(x)", Member),
        ("..<4", Range),
        ("...", Range),
        (".", TrailingDot),
        (".)", TrailingDot),
        (".[0]", TrailingDot),
        (".*x", TrailingDot),
    ] {
        assert_eq!(point_after_int(rest), want, "{rest}");
    }
}

#[test]
fn the_values() {
    assert_eq!(int_value("0X1F"), Some(31));
    assert_eq!(int_value("0B101"), Some(5));
    assert_eq!(int_value("0o1_7"), Some(15));
    assert_eq!(int_value("017"), Some(17));
    assert_eq!(int_value("18446744073709551616"), None);
    // R-20: the F32 value is the text rounded once, not through F64.
    let text = "1.0000000596046447753906250001";
    let once = float_value(text, FloatWidth::F32).unwrap();
    assert_eq!(once, f64::from(1.000_000_1_f32));
    assert_ne!(once, f64::from(text.parse::<f64>().unwrap() as f32));
    assert_eq!(float_value("1_0E+1", FloatWidth::F64), Ok(100.0));
    // R-45, S-211: out of the range, and a literal that is not 0 rounding to 0.
    assert_eq!(float_value("1.0e40", FloatWidth::F32), Err(FloatRange::TooLarge));
    assert_eq!(float_value("1.0e40", FloatWidth::F64), Ok(1.0e40));
    assert_eq!(float_value("1.0e-50", FloatWidth::F32), Err(FloatRange::ToZero));
    assert_eq!(float_value("1e-400", FloatWidth::F64), Err(FloatRange::ToZero));
    assert!(float_value("1.0e-40", FloatWidth::F32).is_ok_and(|v| v > 0.0));
    assert_eq!(float_value("0.0e-999", FloatWidth::F32), Ok(0.0));
    assert_eq!(float_value("3.4028235e38", FloatWidth::F32), Ok(f64::from(f32::MAX)));
    assert_eq!(float_value("1.5abc", FloatWidth::F64), Err(FloatRange::Malformed));
}

/// The source after the first candidate of the first diagnostic of each
/// step, to a source with no diagnostic (S-62, S-63: one form at a time).
#[track_caller]
fn converge(src: &str, want: &[&str]) {
    let mut text = src.to_string();
    let mut steps = Vec::new();
    for _ in 0..want.len() + 1 {
        let p = crate::parse(FileId(0), &text);
        let Some(d) = p.diagnostics.iter().min_by(|a, b| a.order_in_file().cmp(&b.order_in_file())) else { break };
        let fix = d.fixes.first().unwrap_or_else(|| panic!("{text}: no candidate: {d:?}"));
        text = onsa_diag::apply_text(&text, &fix.edits().iter().collect::<Vec<_>>()).unwrap();
        steps.push(text.clone());
    }
    let wrap = |s: &str| format!("fn f() -> F32 {{\n  {s}\n}}\n");
    let want: Vec<String> = want.iter().map(|s| wrap(s)).collect();
    assert_eq!(steps, want, "{src}");
    assert!(crate::parse(FileId(0), &text).diagnostics.is_empty(), "{text}");
}

#[test]
fn each_candidate_takes_one_form_away() {
    let f = |s: &str| format!("fn f() -> F32 {{\n  {s}\n}}\n");
    converge(&f("0o17u8"), &["0o17", "15"]);
    converge(&f("017u8"), &["017", "17"]);
    converge(&f("1.e3f"), &["1.e3", "1.0e3"]);
    converge(&f(".5f"), &["0.5f", "0.5"]);
    converge(&f("0_17"), &["17"]);
    converge(&f("1.e-3"), &["1.0e-3"]);
    converge(&f("00"), &["0"]);
    // S-457: the number, then the callee.
    converge(&f("017(2)"), &["17(2)", "17.(2)"]);
    converge(&f(".5(2)"), &["0.5(2)", "0.5.(2)"]);
}

#[test]
fn a_candidate_parses_again_only_for_a_unit_near_the_limit() {
    // The block and `parens` groups, then the call `.(` the candidate makes
    // (§2.5): at 254 groups it reaches 256 and is made without the parse,
    // at 255 it would reach 257, and the parse finds its E0006.
    let src = |parens: usize| format!("fn f() -> I32 {{\n  {}5(2){}\n}}\n", "(".repeat(parens), ")".repeat(parens));
    let run = |parens: usize| {
        onsa_diag::stack::run(move || {
            let before = crate::nesting::PARSES.get();
            let p = crate::parse(FileId(0), &src(parens));
            let callee = p.diagnostics.iter().find(|d| d.found.as_deref() == Some("5(")).cloned();
            (callee.map(|d| d.fixes.len()), crate::nesting::PARSES.get() - before)
        })
    };
    assert_eq!(run(254), (Some(1), 0));
    assert_eq!(run(255), (Some(0), 1));
    // Three such units in one file: each parses again once, and no parse
    // of the check parses again inside another (R-213; a broken guard made
    // the time exponential in the units).
    let three: String =
        (0..3).map(|i| format!("fn f{i}() -> I32 {{\n  {}5(2){}\n}}\n", "(".repeat(255), ")".repeat(255))).collect();
    let got = onsa_diag::stack::run(move || {
        let before = crate::nesting::PARSES.get();
        let p = crate::parse(FileId(0), &three);
        let fixes: Vec<usize> =
            p.diagnostics.iter().filter(|d| d.found.as_deref() == Some("5(")).map(|d| d.fixes.len()).collect();
        (fixes, crate::nesting::PARSES.get() - before)
    });
    assert_eq!(got, (vec![0, 0, 0], 3));
}

#[test]
fn an_integer_and_its_member_call_have_candidates() {
    // S-350: the three forms W3-20 left without a candidate; after the
    // candidate, the syntax stage reports nothing (the call of an integer is
    // an error of the types stage).
    let f = |s: &str| format!("fn f() -> I32 {{\n  {s}\n}}\n");
    for (src, want) in [("5(2)", "5.(2)"), ("1 .(2)", "1.(2)"), ("1 . (2)", "1.(2)"), ("1i32.(2)", "1.(2)")] {
        let p = crate::parse(FileId(0), &f(src));
        let d = p.diagnostics.iter().min_by(|a, b| a.order_in_file().cmp(&b.order_in_file())).unwrap();
        assert_eq!(d.code, onsa_diag::Code::E0020, "{src}: {d:?}");
        let after = onsa_diag::apply_text(&f(src), &d.fixes[0].edits().iter().collect::<Vec<_>>()).unwrap();
        assert_eq!(after, f(want), "{src}");
        assert!(crate::parse(FileId(0), &after).diagnostics.is_empty(), "{after}");
    }
    // The candidates of the leading zero (S-63, readings C): one when the
    // octal reading is none or the same value.
    for (src, want) in [("08", &["8"][..]), ("089", &["89"]), ("0_17", &["17", "15"]), ("07", &["7"])] {
        let p = crate::parse(FileId(0), &f(src));
        let d = p.diagnostics.iter().min_by(|a, b| a.order_in_file().cmp(&b.order_in_file())).unwrap();
        let got: Vec<String> = d.fixes.iter().map(|x| x.edits()[0].replace.clone()).collect();
        assert_eq!((d.code, got), (onsa_diag::Code::E0020, want.iter().map(|s| s.to_string()).collect()), "{src}");
    }
    // S-456: a float suffix on an integer of another base has no candidate
    // (the row's E0002), called or not.
    for src in ["0b11f32", "0b101_f32", "0o17f", "0b11f32(2)"] {
        let p = crate::parse(FileId(0), &f(src));
        let d = p.diagnostics.iter().min_by(|a, b| a.order_in_file().cmp(&b.order_in_file())).unwrap();
        assert!(
            d.fixes.is_empty() && d.span.end - d.span.start == src.find('(').unwrap_or(src.len()) as u32,
            "{src}: {d:?}"
        );
    }
    // S-457: a number of these forms that is called is the callee's E0020
    // too, from the number to its `(`, after the number's.
    for (src, callee) in [("017(2)", "017("), ("0o17(2)", "0o17("), (".5(2)", ".5(")] {
        let p = crate::parse(FileId(0), &f(src));
        let found: Vec<_> = p.diagnostics.iter().map(|d| (d.code, d.found.as_deref(), d.fixes.len())).collect();
        assert!(found.contains(&(onsa_diag::Code::E0020, Some(callee), 1)), "{src}: {found:?}");
    }
    // Readings E: the `.` after a hexadecimal integer is a member (`.5` a tuple index).
    assert!(crate::parse(FileId(0), &f("0x1F.5")).diagnostics.is_empty());
    // The check that a candidate stays in the nesting limit parses the file
    // again only for a unit that the parser read near the limit: shallow
    // units make no such parse (one per unit was quadratic in the units, and
    // a parse inside that parse exponential).
    let many: String = (0..24).map(|i| format!("fn f{i}() -> I32 {{\n  5(2)\n}}\n")).collect();
    let before = crate::nesting::PARSES.get();
    let p = crate::parse(FileId(0), &many);
    assert_eq!(p.diagnostics.iter().filter(|d| d.fixes.len() == 1).count(), 24, "{:?}", p.diagnostics);
    assert_eq!(crate::nesting::PARSES.get(), before);
    // S-302: a candidate that would join the `.` after it has none; nor the
    // blanks around a `.` taken out where the integer and the `.` would read
    // as a float (`1.e3`, S-350, S-452).
    for src in ["1u8.5", "0o17.5", "1u8.)", "1 .e3", "1 . e3", "1 .e-3", "1 .E+3", "1_0 .e3", "1 . 5"] {
        let p = crate::parse(FileId(0), &f(src));
        assert!(p.diagnostics.iter().all(|d| d.fixes.is_empty()), "{src}: {:?}", p.diagnostics);
    }
    for src in ["1 .e", "1 .abs()", "0x1 .e3"] {
        let p = crate::parse(FileId(0), &f(src));
        assert!(p.diagnostics.iter().any(|d| d.fixes.len() == 1), "{src}: {:?}", p.diagnostics);
    }
}

#[test]
fn a_negative_pattern_names_the_form_of_its_number() {
    // The candidates of the number after the `-`, as in an expression (§2.4, §18.1).
    let f = |p: &str| format!("fn f(x: I32) -> I32 {{\n  match x {{\n    {p} => 1,\n    _ => 0,\n  }}\n}}\n");
    for (src, want) in [("-017", &["17", "15"][..]), ("-1u8", &["1"]), ("-0o17", &["15"])] {
        let p = crate::parse(FileId(0), &f(src));
        let d = p.diagnostics.iter().min_by(|a, b| a.order_in_file().cmp(&b.order_in_file())).unwrap();
        let got: Vec<String> = d.fixes.iter().map(|x| x.edits()[0].replace.clone()).collect();
        assert_eq!((d.code, got), (onsa_diag::Code::E0020, want.iter().map(|s| s.to_string()).collect()), "{src}");
    }
}
