//! The derived clock `at (sample / N)` and `at (sample * N)` in the syntax stage and the names stage (W7-09 U1/t; spec
//! §11.3, §2.2, §18.1, `spec/tools.md` §3; S-1078, S-1077, S-1082): what the case files cannot pin because the runner of
//! the cases does not compare notes and the text after a candidate. Their files are
//! `flow_clock/derived_clock_forms_parse.onsa`, `negative/syntax_clock_ratio_forms.onsa`, `negative/syntax_postfix_when.onsa`,
//! `negative/names_clock_ratio_outside_flow.onsa` and `fixes/e0002_clock_ratio_*`, `fixes/e0011_clock_ratio_*`,
//! `fixes/e0020_clock_ratio_moves.onsa`.
//!
//! The notes are read for the words that tell what they show (the two forms, the chain), not their text, which the spec
//! does not fix; the texts after a candidate are compared without blanks (the spec fixes the tokens and the line breaks of
//! a candidate, not the amount of blank, as in `flow_syntax_decisions.rs`). Expected texts are written from the spec; none
//! is taken from the output of the compiler. The files are checked in this process (`check_input_out`), none is written.

use crate::test_support::fmt::{Fmt, expect_fmt, format};
use crate::test_support::sweep::check_input_out;
use crate::test_support::{apply, code_of, diagnostics, doc_of, edits_of, fixes_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

fn diags(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("a.onsa", text));
    assert!(out.code == 0 || out.code == 1, "onsa check ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// A flow `f` with the head `sig` (`(..) -> ..`) and the body `body`, after a constant `K` and a flow `lp`.
fn flow(sig: &str, body: &str) -> String {
    format!(
        "const K: U32 = 4\n\npub flow lp(x: F32 at sample) -> F32 at sample {{\n  x\n}}\n\npub flow f{sig} {{\n  {body}\n}}\n"
    )
}

fn squeeze(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

fn notes_text(d: &Value) -> String {
    notes_of(d).iter().map(|n| str_of(n, "message")).collect::<Vec<_>>().join("\n")
}

/// The only diagnostic of `text` (a unit holds one error, §18.1) with its code asserted.
fn only(text: &str, wanted: &str) -> Value {
    let ds = diags(text);
    assert_eq!(ds.len(), 1, "one error in the unit, got {ds:?}\n{text}");
    assert_eq!(code_of(&ds[0]), wanted, "{}\n{text}", ds[0]);
    ds[0].clone()
}

/// The texts after each candidate of the only diagnostic of `text`, without blanks, sorted.
fn candidates(text: &str, wanted: &str) -> Vec<String> {
    let d = only(text, wanted);
    let mut v: Vec<String> = fixes_of(&d).into_iter().map(|f| squeeze(&apply(text, &edits_of(f)))).collect();
    v.sort();
    v
}

#[test]
fn a_ratio_that_is_not_one_of_the_two_forms_is_e0002_with_a_note_of_the_two_forms() {
    let forms = [
        "(sample + 4)",
        "(sample - K)",
        "(4 / sample)",
        "(sample / K * 2)",
        "(sample / 4 / 2)",
        "(sample * K / 2)",
        "(sample)",
        "((sample / 4))",
        "(sample /)",
        "(/ 4)",
        "(a.b / 4)",
    ];
    for form in forms {
        let places = [
            ("an input", flow(&format!("(x: F32 at {form}) -> F32 at sample"), "x")),
            ("an output", flow(&format!("(x: F32 at sample) -> F32 at {form}"), "x")),
            ("an expression", flow("(p: F32 at block) -> F32 at sample", &format!("let a = p at {form}\n  a"))),
        ];
        for (place, text) in places {
            let d = only(&text, "E0002");
            let notes = notes_text(&d);
            assert!(
                notes.contains("sample / ") && notes.contains("sample * "),
                "{form} in {place}: the two forms in a note: {notes:?}"
            );
            if form == "(sample)" {
                assert!(fixes_of(&d).is_empty(), "{form} in {place}: no candidate (S-1078): {d}");
            }
        }
    }
}

#[test]
fn a_bare_ratio_in_a_declaration_is_e0002_and_the_one_candidate_wraps_it() {
    let sig = |i: &str, o: &str| format!("(x: F32 at {i}) -> F32 at {o}");
    let cases = [
        (sig("sample / 4", "sample"), sig("(sample / 4)", "sample")),
        (sig("sample", "sample * 2"), sig("sample", "(sample * 2)")),
        (sig("sample / K", "sample"), sig("(sample / K)", "sample")),
    ];
    for (bare, wrapped) in cases {
        let (before, after) = (flow(&bare, "x"), flow(&wrapped, "x"));
        assert_eq!(candidates(&before, "E0002"), [squeeze(&after)], "{bare}");
        // The wrapped form is read: the syntax stage reports nothing of the ratio (a gate of a later stage may).
        assert!(diags(&after).iter().all(|d| !matches!(code_of(d), "E0002" | "E0011")), "{wrapped}");
    }
}

#[test]
fn a_bare_ratio_in_an_expression_is_e0011_and_a_division_by_an_integer_has_the_clock_candidate() {
    let sig = "(p: F32 at block, x: F32 at sample) -> F32 at sample";
    let of = |body: &str| flow(sig, body);
    // `/` and an integer literal on the right: the `at` expression in a parenthesis and the clock in a parenthesis.
    for n in ["2", "8", "32"] {
        let got = candidates(&of(&format!("p at sample / {n}")), "E0011");
        let mut want =
            vec![squeeze(&of(&format!("(p at sample) / {n}"))), squeeze(&of(&format!("p at (sample / {n})")))];
        want.sort();
        assert_eq!(got, want, "p at sample / {n}");
    }
    // Everywhere else the one candidate the syntax offers today (the `at` expression in a parenthesis).
    for (bare, wrapped) in [
        ("p at sample / x", "(p at sample) / x"),
        ("p at sample / 2.0", "(p at sample) / 2.0"),
        ("p at sample * 2", "(p at sample) * 2"),
        ("p at sample + x", "(p at sample) + x"),
    ] {
        assert_eq!(candidates(&of(bare), "E0011"), [squeeze(&of(wrapped))], "{bare}");
    }
}

#[test]
fn a_division_by_a_constant_name_has_the_clock_candidate_too() {
    let sig = "(p: F32 at block) -> F32 at sample";
    let got = candidates(&flow(sig, "p at sample / K"), "E0011");
    let mut want = vec![squeeze(&flow(sig, "(p at sample) / K")), squeeze(&flow(sig, "p at (sample / K)"))];
    want.sort();
    assert_eq!(got, want);
}

#[test]
fn a_derived_clock_outside_a_flow_is_e0821_whatever_the_base_and_n_are() {
    for clock in ["(sample / 2)", "(sample * 2)", "(nope / 2)", "(block / 2)"] {
        let sources = [
            format!("pub fn f(x: F32) -> F32 {{\n  x at {clock}\n}}\n"),
            format!("pub fn f(x: F32 at {clock}) -> F32 {{\n  x\n}}\n"),
            format!("pub fn f(x: F32) -> F32 at {clock} {{\n  x\n}}\n"),
        ];
        for text in sources {
            only(&text, "E0821");
        }
    }
}

#[test]
fn the_e0020_candidate_moves_the_whole_derived_clock_or_removes_it() {
    let in_flow = |body: &str| {
        format!(
            "pub flow f(p: F32 at block, x: F32 at sample, t: (F32, F32) at block) -> F32 at sample {{\n  {body}\n  x\n}}\n"
        )
    };
    let cases = [
        (in_flow("let y: F32 at (sample / 4) = p"), in_flow("let y: F32 = p at (sample / 4)")),
        (in_flow("let y at (sample * 2) = p"), in_flow("let y = p at (sample * 2)")),
        (in_flow("let (a, b) at (sample / 4) = t"), in_flow("let (a, b) = t at (sample / 4)")),
        (in_flow("let y at (sample / 4) = x + x"), in_flow("let y = (x + x) at (sample / 4)")),
        // The value is already an `at` expression: the clock of the binding goes.
        (in_flow("let y: F32 at (sample / 4) = p at block"), in_flow("let y: F32 = p at block")),
        (
            in_flow("let ys = par i at (sample / 4) in 0 ..< 2 {\n    x\n  }"),
            in_flow("let ys = par i in 0 ..< 2 {\n    x\n  }"),
        ),
        (
            "pub flow f(x: Option[F32 at (sample / 4)]) -> F32 at sample {\n  0.5\n}\n".to_string(),
            "pub flow f(x: Option[F32] at (sample / 4)) -> F32 at sample {\n  0.5\n}\n".to_string(),
        ),
        (
            "pub fn f(x: Option[F32 at (sample / 4)]) -> F32 {\n  0.5\n}\n".to_string(),
            "pub fn f(x: Option[F32]) -> F32 {\n  0.5\n}\n".to_string(),
        ),
        ("pub struct S {\n  a: F32 at (sample * 2),\n}\n".to_string(), "pub struct S {\n  a: F32,\n}\n".to_string()),
    ];
    for (before, after) in cases {
        assert_eq!(candidates(&before, "E0020"), [squeeze(&after)], "{before}");
    }
}

#[test]
fn a_postfix_when_is_e0002_with_a_note_of_the_chain_and_is_no_e0200() {
    // S-1082 is open: this is its provisional reading (2).
    let sig = "(x: F32 at sample, c: Bool at sample) -> F32 at sample";
    for (body, word) in [
        ("lp~(x) when c", "when"),
        ("prev~(x) when c", "when"),
        ("let y = lp~(x) when c\n  y", "when"),
        ("lp~(x) reset_if c", "reset_if"),
    ] {
        let d = only(&flow(sig, body), "E0002");
        let notes = notes_text(&d);
        assert!(notes.contains(&format!(".{word}~(")), "{body}: the chain `.{word}~(c)` in a note: {notes:?}");
    }
}

#[test]
fn fmt_writes_the_derived_clock_with_one_space_round_the_operator_and_none_inside() {
    let sig = |i: &str, o: &str| format!("pub flow f(x: F32 at {i}) -> F32 at {o} {{\n  x\n}}\n");
    let body = |e: &str| format!("pub flow f(p: F32 at block) -> F32 at sample {{\n  {e}\n}}\n");
    let cases: Vec<(&str, String, String)> = vec![
        ("inside spaces", sig("( sample/4 )", "sample"), sig("(sample / 4)", "sample")),
        ("a product", sig("sample", "(sample*2)"), sig("sample", "(sample * 2)")),
        ("many spaces", sig("(  sample  /  K  )", "sample"), sig("(sample / K)", "sample")),
        ("a parenthesis as N", sig("(sample/(K*2))", "sample"), sig("(sample / (K * 2))", "sample")),
        ("a prefix minus", sig("(sample/-4)", "sample"), sig("(sample / -4)", "sample")),
        ("no space after at", body("p at(sample/4)"), body("p at (sample / 4)")),
        ("in an expression", body("p  at  ( sample * 2 )"), body("p at (sample * 2)")),
        ("canonical stays", sig("(sample / U32.BITS)", "(sample * 2)"), sig("(sample / U32.BITS)", "(sample * 2)")),
    ];
    let cases: Vec<(&str, &str, &str)> = cases.iter().map(|(w, i, e)| (*w, i.as_str(), e.as_str())).collect();
    expect_fmt("derived_clock", &cases);
}

#[test]
fn fmt_stops_at_a_ratio_that_is_a_syntax_error() {
    for text in [
        "pub flow f(x: F32 at sample / 4) -> F32 at sample {\n  x\n}\n",
        "pub flow f(x: F32 at (sample + 4)) -> F32 at sample {\n  x\n}\n",
        "pub flow f(p: F32 at block) -> F32 at sample {\n  p at sample / 2\n}\n",
    ] {
        assert!(matches!(format("a.onsa", text), Fmt::Syntax(_)), "fmt refuses the syntax error:\n{text}");
    }
}

// ------------------------------------------------------------ the regressions of W7-09 U1/b (`rules/leader.md` 4.9)

/// A diagnostic of a stage after the syntax: of a code no syntax stage reports (the E0821 of a clock outside a flow, the
/// E0810 of an input with no clock), or the gate of the derived clocks (E0200 of this version, its message names them).
fn later(d: &Value) -> bool {
    let code = onsa_diag::Code::parse(code_of(d)).unwrap_or_else(|| panic!("a registered code: {d}"));
    !code.stages().contains(&onsa_diag::Stage::Syntax)
        || (code_of(d) == "E0200" && str_of(d, "message").contains("derived clock"))
}

/// The candidates of the diagnostics of `text`: for each, its title and the diagnostics of its text that are of the
/// syntax stage or one before it (§18.1: none, where the original is the only error of its unit). The number of the
/// candidates is the second.
fn left_by_candidates(text: &str) -> (Vec<(String, Vec<Value>)>, usize) {
    let mut out = Vec::new();
    for d in diags(text) {
        for f in fixes_of(&d) {
            let after = apply(text, &edits_of(f));
            let left: Vec<Value> = diags(&after).into_iter().filter(|e| !later(e)).collect();
            out.push((format!("{} `{}`", code_of(&d), str_of(f, "title")), left));
        }
    }
    let n = out.len();
    (out.into_iter().filter(|(_, left)| !left.is_empty()).collect(), n)
}

/// The places of a type with a clock: `{}` is the clock and what follows it. The first three are where a clock goes; in
/// the last three the candidate of the E0020 removes the clock with its ratio (W7-09 U1/b P1).
const BARE_PLACES: [(&str, &str); 9] = [
    ("an input", "pub flow f(x: F32 at sample{}) -> F32 at sample {\n  0.5\n}\n"),
    ("an output", "pub flow f(x: F32 at sample) -> F32 at sample{} {\n  0.5\n}\n"),
    ("a parameter of fn", "pub fn g(x: F32 at sample{}) -> F32 {\n  0.5\n}\n"),
    ("a let annotation", "pub flow f(x: F32 at sample) -> F32 at sample {\n  let y: F32 at sample{} = x\n  y\n}\n"),
    ("a tuple", "pub flow f(x: (F32 at sample{}, F32)) -> F32 at sample {\n  0.5\n}\n"),
    ("a type argument", "pub flow f(x: Option[F32 at sample{}]) -> F32 at sample {\n  0.5\n}\n"),
    ("a field", "pub struct S {\n  a: F32 at sample{},\n}\n"),
    ("a constant", "const C: U32 at sample{} = 4\n"),
    ("a variant", "pub enum E {\n  A(F32 at sample{}),\n}\n"),
];

#[test]
fn a_candidate_of_a_bare_ratio_after_a_type_leaves_no_error_of_the_syntax_or_there_is_none() {
    // N one operand, then the end of the clock: where a clock goes, the candidate wraps it.
    let one =
        [" / 4", " * 2", " / K", " / cfg.N", " / (K * 2)", " / -4", " / g(2)", " / a[0]", " / a.0", " / U32.BITS"];
    // N and more after it, or the operator at the head of a line (§2.5).
    let more = [
        " / 4 / 2",
        " * 2 * 2",
        " / cfg . N",
        " / 4 + 1",
        " / 4 as U32",
        " / 4 at block",
        " / a .b",
        " / a.b.",
        " / 4 .abs()",
        " / K\n  * 2",
        "\n  / 4",
    ];
    let mut problems = Vec::new();
    for (k, (place, frame)) in BARE_PLACES.iter().enumerate() {
        for ratio in one.iter().chain(&more) {
            let text = format!("const K: U32 = 4\n\n{}", frame.replacen("{}", ratio, 1));
            let (left, n) = left_by_candidates(&text);
            if k < 3 && one.contains(ratio) && !ratio.contains('\n') && n == 0 {
                problems.push(format!("{place}, `{ratio}`: no candidate wraps it"));
            }
            // In a type argument the `/` makes the element an expression (R-417), where a member `.` with a blank is
            // an E0020 of its own that hides the E0011 of the chain: of no clock, and the same with `as`.
            // After a constant's type a line break ends the line, and the `/` at the head of the next is an error of
            // its own, of no ratio (the same with no clock): it is no bare ratio to wrap or to remove.
            let own = |fix: &str| {
                (place == &"a type argument" && fix.ends_with("`remove the space`"))
                    || (place == &"a constant" && ratio.starts_with('\n'))
            };
            let left = left.into_iter().filter(|(fix, _)| !own(fix));
            problems.extend(left.map(|(fix, left)| format!("{place}, `{ratio}`: {fix} leaves {left:?}")));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn an_operator_at_the_head_of_a_line_in_a_derived_clock_is_e0020_as_outside_the_parenthesis() {
    let places = [
        ("an input", "pub flow f(x: F32 at {}) -> F32 at sample {\n  x\n}\n"),
        ("an output", "pub flow f(x: F32 at sample) -> F32 at {} {\n  x\n}\n"),
        ("an expression", "pub flow f(x: F32 at block) -> F32 at sample {\n  let y = x at {}\n  y\n}\n"),
    ];
    for (place, frame) in places {
        for clock in ["(sample\n  / 4)", "(sample\n  * 2)", "(sample // c\n  / 4)"] {
            let text = frame.replacen("{}", clock, 1);
            let d = only(&text, "E0020");
            assert!(str_of(&d, "message").contains("line"), "{place}, `{clock}`: {d}");
            let (left, n) = left_by_candidates(&text);
            assert!(n > 0 && left.is_empty(), "{place}, `{clock}`: {n} candidates, left {left:?}");
            assert!(
                matches!(format("a.onsa", &text), Fmt::Syntax(_)),
                "{place}, `{clock}`: fmt refuses it as check does"
            );
        }
        // A line break after the `(`, the operator or before the `)` is a blank there.
        for clock in ["(\n  sample / 4)", "(sample /\n  4)", "(sample / 4\n  )"] {
            let text = frame.replacen("{}", clock, 1);
            assert!(diags(&text).iter().all(later), "{place}, `{clock}`: {:?}", diags(&text));
        }
    }
}

/// The parts of the tokens in the parenthesis of a derived clock ([`a_derived_clock_reads_by_the_model_of_its_parts`]).
const PARTS: [&str; 8] = ["sample", "K", "4", "(K * 2)", "-4", "/", "*", "+"];

#[test]
fn a_derived_clock_reads_by_the_model_of_its_parts() {
    // The model of S-1078: a name, `/` or `*`, one operand N. The first part that is a name is a base the syntax reads
    // (the names stage looks it up); the operand is any part but an operator. Where the model reads a form, a place
    // with a code stops at that code, and an expression (no gate since W7-09 U2r1) has only errors of later stages.
    let model = |s: &[&str]| {
        s.len() == 3
            && ["sample", "K"].contains(&s[0])
            && ["/", "*"].contains(&s[1])
            && !["/", "*", "+"].contains(&s[2])
    };
    let places = [
        ("an input", "pub flow f(x: F32 at ({})) -> F32 at sample {\n  x\n}\n", None),
        ("an expression", "pub flow f(x: F32 at block) -> F32 at sample {\n  let y = x at ({})\n  y\n}\n", None),
        ("an input of fn", "pub fn g(x: F32 at ({})) -> F32 {\n  x\n}\n", Some("E0821")),
    ];
    // Every sequence of 3 parts, and of 4 by a fixed stride (the model has none of them read), in each place.
    let mut seqs: Vec<Vec<&str>> = Vec::new();
    for (k, i) in (0..PARTS.len().pow(4)).enumerate() {
        let digits = [i % 8, i / 8 % 8, i / 64 % 8, i / 512];
        if i < 512 || k % 61 == 0 {
            seqs.push(digits[..if i < 512 { 3 } else { 4 }].iter().map(|&d| PARTS[d]).collect());
        }
    }
    let (mut read, mut problems) = (0, Vec::new());
    for (place, frame, gate) in places {
        for (k, seq) in seqs.iter().enumerate() {
            // Each place takes a third of the sequences of 3, and all of those the model reads.
            if !model(seq) && k % 3 != places.iter().position(|p| p.0 == place).unwrap_or(0) {
                continue;
            }
            // What the model reads of the clock of an input is the declaration of a conversion flow, which W7-09 U4a reads
            // by its own rules (a_derived_clock_of_an_input_reads_by_the_model_of_its_parts): only the forms it does not read stay here.
            if place == "an input" && model(seq) {
                continue;
            }
            let text = format!("const K: U32 = 4\n\n{}", frame.replacen("{}", &seq.join(" "), 1));
            let found = diags(&text);
            let codes: Vec<String> = found.iter().map(|d| code_of(d).to_string()).collect();
            read += usize::from(model(seq));
            let (fits, want) = match (model(seq), gate) {
                (true, Some(gate)) => (codes == [gate], gate),
                (true, None) => {
                    (found.iter().all(|d| later(d) || code_of(d) == "E0200"), "no error of the syntax stage")
                }
                (false, _) => (codes == ["E0002"], "E0002"),
            };
            if !fits {
                problems.push(format!("{place}, `{}`: {codes:?}, the model says {want}", seq.join(" ")));
            }
        }
    }
    assert_eq!(read, 2 * 2 * 2 * 5, "the sequences the model reads, in the places but an input");
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// The clock of an input, once the declaration of a conversion flow is read (W7-09 U4a, S-1078, S-1077): the same forms
/// that the model of the test above reads, with a body that reads no port (`0.5`), by what each part is. A base that is
/// not a name of the clocks (`K`) is E0302 whatever N is; the base `sample` with N the literal `4` or the constant `K` is
/// no error in either operator; N that needs arithmetic (`(K * 2)`) is E0200 until W9-03; a prefix `-` is E0401; the name
/// `sample` as N is a name of no constant (an error that is not of the syntax: E0002 is for the forms the model does not read).
#[test]
fn a_derived_clock_of_an_input_reads_by_the_model_of_its_parts() {
    let mut problems = Vec::new();
    for base in ["sample", "K"] {
        for op in ["/", "*"] {
            for n in ["sample", "K", "4", "(K * 2)", "-4"] {
                let clock = format!("{base} {op} {n}");
                let text =
                    format!("const K: U32 = 4\n\npub flow f(x: F32 at ({clock})) -> F32 at sample {{\n  0.5\n}}\n");
                let codes: Vec<String> = diags(&text).iter().map(|d| code_of(d).to_string()).collect();
                let fits = match (base, n) {
                    ("K", _) => codes.iter().any(|c| c == "E0302") && !codes.iter().any(|c| c == "E0002"),
                    (_, "4" | "K") => codes.is_empty(),
                    (_, "(K * 2)") => codes == ["E0200"],
                    (_, "-4") => codes == ["E0401"],
                    _ => !codes.is_empty() && !codes.iter().any(|c| c == "E0002"),
                };
                if !fits {
                    problems.push(format!("`{clock}`: {codes:?}"));
                }
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn a_form_of_another_language_as_n_is_the_e0020_it_is_where_an_expression_goes() {
    for n in ["4u32", "017", "1.", "0o17", "1f32", "0x1F_u8", "&x", "~x"] {
        let ratio = format!("pub flow f(x: F32 at (sample / {n})) -> F32 at sample {{\n  x\n}}\n");
        let length = format!("pub fn g(x: F32) -> [F32; 2] {{\n  let a = [0.0; {n}]\n  [x, x]\n}}\n");
        let (d, e) = (only(&ratio, "E0020"), only(&length, "E0020"));
        let titles = |d: &Value| fixes_of(d).iter().map(|f| str_of(f, "title").to_string()).collect::<Vec<_>>();
        assert_eq!(str_of(&d, "message"), str_of(&e, "message"), "`{n}`: the form of the table, as in a length");
        assert!(!titles(&d).is_empty() && titles(&d) == titles(&e), "`{n}`: {:?} and {:?}", titles(&d), titles(&e));
        let (left, _) = left_by_candidates(&ratio);
        assert!(left.is_empty(), "`{n}`: {left:?}");
    }
}
