//! The shapes of names (spec §2.3, the family S-650): what the case files in `tests/spec/` cannot pin about
//! the candidates of an E0320 and about the commands that read the names (W4-14 U3).
//!
//! The runner of the cases compares the text after a candidate only for the cases that keep a `.fixK`
//! (which the test role does not write for a new case), and it does not tell a diagnostic that has no
//! candidate from one that has. These tests say both from the spec: the number of candidates, that the
//! candidate leaves the program without an E0320 (the unit is clean, §18.1), the two spellings the spec
//! names (`[_e]` becomes `e`, `let _x` becomes `x`, §2.3), the keyword case (a `_` at the end), and no
//! candidate where the name in the shape is not an identifier (`_0`). The spelling of the other
//! candidates, the words of a note and the position inside a line are not fixed by the spec.
//!
//! What the spec fixes, and so what is checked here:
//! - a name that starts with `_` is E0320 for every kind, the kind read from the position or from the first
//!   letter after the `_` (S-648); one candidate; after it the program has no diagnostic (R-168, R-240);
//! - a `_` at the end is fine in every shape, and no internal error comes from it (R-260);
//! - the name without its `_` is a keyword: the candidate ends with `_` (`type_`, `match_`, `Self_`,
//!   `inout_`) and a note shows how to avoid a keyword (S-651);
//! - the name in its shape is not an identifier (`_0`, `__`, `_1`): E0320 with no candidate (R-262);
//! - `onsa build` of a package with `voice._f` and `voice_.f`, or with `_util.onsa` and `onsa_util.onsa`,
//!   stops at E0320 and does not reach the C compiler (R-261);
//! - an exported function whose name starts with `_` is E0320 in `check` (R-263; needs `@export`).
//!
//! The tests the implementation does not pass yet carry `#[ignore = "<work>"]`.
//!
//! Not written here: the candidate that collides with a name already there (S-652, W4-04), the end `_` of an
//! exported name (S-653, W4-02), a keyword written as a name (S-654).

mod test_support;

use serde_json::Value;
use test_support::*;

const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";
const EXPORT_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"t_\"\n\n[targets.host]\nkind = \"staticlib\"\nplatform = \"host\"\nprovides = []\n";

/// One edit: a range as (line, column in characters), 1-based, and the new text.
struct Edit {
    start: (usize, usize),
    end: (usize, usize),
    replace: String,
}

fn edits_of(fix: &Value) -> Vec<Edit> {
    let pos = |s: &Value, l: &str, c: &str| -> (usize, usize) {
        let get = |k: &str| usize::try_from(s[k].as_u64().unwrap_or_else(|| panic!("no `{k}` in {s}"))).unwrap();
        (get(l), get(c))
    };
    fix["edits"]
        .as_array()
        .expect("`edits` is an array")
        .iter()
        .map(|e| Edit {
            start: pos(&e["span"], "line", "col"),
            end: pos(&e["span"], "end_line", "end_col"),
            replace: e["replace"].as_str().expect("`replace` is a string").to_string(),
        })
        .collect()
}

fn offset(text: &str, (line, col): (usize, usize)) -> usize {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n').expect("a line past the end of the file") + 1;
    }
    let rest = &text[start..];
    let line_len = rest.find('\n').unwrap_or(rest.len());
    match rest[..line_len].char_indices().nth(col - 1) {
        Some((i, _)) => start + i,
        None => start + line_len,
    }
}

fn apply(text: &str, edits: &[Edit]) -> String {
    let mut spans: Vec<(usize, usize, &str)> =
        edits.iter().map(|e| (offset(text, e.start), offset(text, e.end), e.replace.as_str())).collect();
    spans.sort_by_key(|&(a, b, _)| (a, b));
    let mut out = text.to_string();
    for &(a, b, r) in spans.iter().rev() {
        out.replace_range(a..b, r);
    }
    out
}

/// `onsa check --json main.onsa` of a single file (no manifest above it): the exit code and the document.
fn check_file(tag: &str, source: &str) -> (Out, Value) {
    let d = Dir::bare(tag);
    d.write("main.onsa", source);
    let out = run(d.root(), &["check", "--json", "main.onsa"]);
    let doc = doc_of(&out);
    (out, doc)
}

fn fixes_of(d: &Value) -> Vec<&Value> {
    match d.get("fixes") {
        None => vec![],
        Some(f) => f.as_array().expect("`fixes` is an array").iter().collect(),
    }
}

fn code_of(d: &Value) -> &str {
    str_of(d, "code")
}

/// The only diagnostic of a source, which must be one E0320.
fn the_e0320<'a>(tag: &str, out: &Out, doc: &'a Value) -> &'a Value {
    assert_eq!(out.code, 1, "{tag}: {}{}", out.stdout, out.stderr);
    let ds = diagnostics(doc);
    assert_eq!(ds.len(), 1, "{tag}: one diagnostic expected: {doc}");
    assert_eq!(code_of(&ds[0]), "E0320", "{tag}: {doc}");
    &ds[0]
}

/// The source after the only candidate of the only E0320, and the check of that text (it must be clean).
fn after_the_candidate(tag: &str, source: &str) -> String {
    let (out, doc) = check_file(tag, source);
    let d = the_e0320(tag, &out, &doc);
    let fixes = fixes_of(d);
    assert_eq!(fixes.len(), 1, "{tag}: one candidate expected: {d}");
    let fixed = apply(source, &edits_of(fixes[0]));
    assert_ne!(fixed, source, "{tag}: the candidate changes the source: {d}");
    let (out, doc) = check_file(&format!("{tag}_after"), &fixed);
    assert_eq!(out.code, 0, "{tag}: after the candidate {fixed:?}: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{tag}: after the candidate {fixed:?}: {doc}");
    fixed
}

// ---- a leading `_` (S-648, S-650; R-168, R-240) ---------------------------------------------------

/// §2.3, §7: a name that starts with `_` is E0320, for a function, a parameter, a binding, a pattern name,
/// a struct, a variant, a constant, a type alias, a type parameter and an effect-row variable. The kind
/// comes from the position, or from the first letter after the `_`. One candidate, after which the program
/// is clean (the uses are renamed too, so there is no E0302).
#[test]
fn a_leading_underscore_is_e0320_with_one_candidate_that_leaves_the_program_clean() {
    let sources: [(&str, &str); 14] = [
        ("fn_name", "pub fn _g() -> I32 {\n  1\n}\n\npub fn h() -> I32 {\n  _g()\n}\n"),
        ("struct_name", "pub struct _P {\n  x: I32,\n}\n\npub fn rd(p: _P) -> I32 {\n  p.x\n}\n"),
        ("field", "pub struct Q {\n  _x: I32,\n}\n\npub fn rd(q: Q) -> I32 {\n  q._x\n}\n"),
        ("variant", "pub enum F {\n  _A,\n  B,\n}\n\npub fn mk() -> F {\n  F._A\n}\n"),
        ("param", "pub fn p(_a: I32) -> I32 {\n  _a + 1\n}\n"),
        ("let", "pub fn l() -> I32 {\n  let _x = 1\n  _x + 1\n}\n"),
        ("let_typed", "pub fn b(x: I64) -> I64 {\n  let _z: I64 = 5\n  x + _z\n}\n"),
        ("var", "pub fn v() -> I32 {\n  var _y = 0\n  _y = _y + 1\n  _y\n}\n"),
        ("match_name", "pub fn m(o: Option[I32]) -> I32 {\n  match o {\n    Some(_k) => _k,\n    None => 0,\n  }\n}\n"),
        ("tuple_name", "pub fn t(p: (I32, I32)) -> I32 {\n  let (_a, b) = p\n  _a + b\n}\n"),
        ("const", "const _MAX: U32 = 8\n\npub fn m() -> U32 {\n  _MAX * 2\n}\n"),
        ("alias", "type _Alias = I32\n\npub fn al(x: _Alias) -> _Alias {\n  x\n}\n"),
        ("type_param", "pub fn id1[_T](x: _T) -> _T {\n  x\n}\n"),
        ("effect_var", "pub fn ap[T, _e](f: fn(T) -> T uses {_e}, x: T) -> T uses {_e} {\n  f(x)\n}\n"),
    ];
    for (tag, source) in sources {
        after_the_candidate(tag, source);
    }
}

/// §2.3 names two spellings outright: `[_e]` is an effect-row variable and the candidate is `e`; `let _x = 1`
/// is a binding and the candidate is `x`. The result is the same text without the `_`.
#[test]
fn the_candidates_the_spec_names_drop_the_underscore() {
    let fixed =
        after_the_candidate("spec_e", "pub fn ap[T, _e](f: fn(T) -> T uses {_e}, x: T) -> T uses {_e} {\n  f(x)\n}\n");
    assert_eq!(fixed, "pub fn ap[T, e](f: fn(T) -> T uses {e}, x: T) -> T uses {e} {\n  f(x)\n}\n");
    let fixed = after_the_candidate("spec_x", "pub fn l() -> I32 {\n  let _x = 1\n  _x + 1\n}\n");
    assert_eq!(fixed, "pub fn l() -> I32 {\n  let x = 1\n  x + 1\n}\n");
}

/// R-168: `let _x = 1` is E0320 at the name; it is not an E0302 "cannot find". The position is the line of
/// the binding, and the diagnostic is the only one of the unit.
#[test]
fn a_binding_with_a_leading_underscore_is_not_an_e0302() {
    let (out, doc) = check_file("r168", "pub fn l() -> I32 {\n  let _x = 1\n  _x\n}\n");
    let d = the_e0320("r168", &out, &doc);
    assert_eq!(span_of(&d["span"]).line, 2, "{d}");
}

// ---- a `_` at the end (S-650; R-260) --------------------------------------------------------------

/// §2.3: a `_` at the end is a spelling that avoids a keyword and is fine in every shape: `Self_`,
/// `inout_` as an effect-row variable (R-260 gave a candidate that changed nothing, an internal error in
/// the debug build), `match_`, `type_`, a field, a parameter, a binding, a constant.
#[test]
fn a_name_with_an_underscore_at_the_end_is_fine_in_every_shape() {
    let sources: [(&str, &str); 8] = [
        ("self_type", "pub struct Self_ {\n  x: I32,\n}\n"),
        ("inout_var", "pub fn f[T, inout_](g: fn(T) -> T uses {inout_}, x: T) -> T uses {inout_} {\n  g(x)\n}\n"),
        ("fn_names", "pub fn match_(type_: I32) -> I32 {\n  let self_ = type_ + 1\n  self_\n}\n"),
        ("field", "pub struct P {\n  x_: I32,\n}\n"),
        ("type_param", "pub fn id1[T_](x: T_) -> T_ {\n  x\n}\n"),
        ("const", "const MAX_: U32 = 8\n"),
        ("variant", "pub enum K {\n  Red_,\n  Blue,\n}\n"),
        ("flow", "pub flow lp_(x: F32 at sample) -> F32 at sample {\n  x\n}\n"),
    ];
    for (tag, source) in sources {
        let (out, doc) = check_file(tag, source);
        assert_eq!(out.code, 0, "{tag}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc).is_empty(), "{tag}: {doc}");
    }
}

// ---- the name without its `_` is a keyword (S-651) ------------------------------------------------

/// §2.3: when the name in its shape is a keyword (`_type` is `type`), the candidate is the name with a `_`
/// at the end, and a note shows that a `_` at the end avoids a keyword.
#[test]
fn the_candidate_of_a_keyword_ends_with_an_underscore_and_has_a_note() {
    let cases: [(&str, &str, &str); 4] = [
        ("type", "pub fn l() -> I32 {\n  let _type = 1\n  _type\n}\n", "type_"),
        ("match", "pub fn _match() -> I32 {\n  1\n}\n", "match_"),
        ("self_upper", "pub struct _Self {\n  x: I32,\n}\n", "Self_"),
        ("inout", "pub fn p(_inout: I32) -> I32 {\n  _inout\n}\n", "inout_"),
    ];
    for (tag, source, want) in cases {
        let fixed = after_the_candidate(tag, source);
        assert!(fixed.contains(want), "{tag}: {want:?} is not in {fixed:?}");
        let (_, doc) = check_file(tag, source);
        let d = &diagnostics(&doc)[0];
        assert!(!array_of(d, "notes").is_empty(), "{tag}: a note shows how to avoid a keyword: {d}");
    }
}

// ---- no candidate where the name in its shape is not an identifier (R-262) ------------------------

/// §2.3: `_0` without its `_` is `0`, `__` made one `_` is the hole, `_1` is `1`: not identifiers, so the
/// diagnostic has no candidate (and is not an internal error).
#[test]
fn a_name_that_cannot_be_an_identifier_after_the_rule_has_no_candidate() {
    let cases: [(&str, &str); 6] = [
        ("struct_0", "pub struct _0 {\n  x: I32,\n}\n"),
        ("variant_0", "pub enum C {\n  _0,\n  D,\n}\n"),
        ("const_0", "const _0: I32 = 1\n"),
        ("const_1", "pub const _1: I32 = 1\n"),
        ("struct_dd", "pub struct __ {\n  x: I32,\n}\n"),
        ("fn_2", "pub fn _2() -> I32 {\n  1\n}\n"),
    ];
    for (tag, source) in cases {
        let (out, doc) = check_file(tag, source);
        let d = the_e0320(tag, &out, &doc);
        assert!(fixes_of(d).is_empty(), "{tag}: no candidate: {d}");
    }
}

// ---- the C names (R-261, R-263) -------------------------------------------------------------------

/// R-261, §11.6, §2.3: `voice._f` and `voice_.f` were both `voice___f`, and `_util.f` and `onsa_util.f` were
/// both `onsa_util__f`. A name does not start with `_`, so `pub fn _f` and the file `_util.onsa` are E0320 and
/// `onsa build` stops at them: exit code 1 with the diagnostics, not an internal error of the C compiler.
#[test]
fn build_stops_at_the_names_that_would_have_made_one_c_name() {
    let d = Dir::bare("r261");
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", "use voice\nuse voice_\nuse _util\nuse onsa_util\n\npub fn g() -> I32 {\n  voice._f() + voice_.f() + _util.f() + onsa_util.f()\n}\n");
    d.write("voice.onsa", "pub fn _f() -> I32 {\n  1\n}\n");
    d.write("voice_.onsa", "pub fn f() -> I32 {\n  2\n}\n");
    d.write("_util.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    d.write("onsa_util.onsa", "pub fn f() -> I32 {\n  2\n}\n");

    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    let got: Vec<(String, String)> =
        diagnostics(&doc).iter().map(|dg| (code_of(dg).to_string(), span_of(&dg["span"]).file)).collect();
    assert_eq!(
        got,
        [("E0320".to_string(), "_util.onsa".to_string()), ("E0320".to_string(), "voice.onsa".to_string())],
        "{doc}"
    );

    let out = run(d.root(), &["build", "--target", "host"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.lines().any(|l| l.starts_with("voice.onsa:1:") && l.contains("error[E0320]")), "{}", out.stdout);
    assert!(out.stdout.lines().any(|l| l.starts_with("_util.onsa:1:1: error[E0320]: ")), "{}", out.stdout);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
}

/// R-263, §14.2, §2.3: an exported function `_g` would have had the C name `t_onsa_g`, not `t__g`. A name does
/// not start with `_`, so `check` reports an E0320 at the declaration whatever the target is. (This needs
/// `@export`, which the compiler does not read yet.)
#[test]
#[ignore = "W4-02: needs `@export` (S-639); the leading `_` is E0320 since W4-14 U3 (R-263)"]
fn an_exported_function_whose_name_starts_with_an_underscore_is_e0320_in_check() {
    let d = Dir::bare("r263");
    d.write("onsa.toml", EXPORT_MANIFEST);
    d.write("main.onsa", "@export\npub fn _g() -> I32 {\n  1\n}\n\n@export\npub fn h() -> I32 {\n  2\n}\n");
    let out = run(d.root(), &["check", "--json"]);
    let doc = doc_of(&out);
    let d0 = the_e0320("r263", &out, &doc);
    assert_eq!(span_of(&d0["span"]).line, 2, "{d0}");
}

// ---- the name by the rule is a name there already (S-652) -----------------------------------------

/// §2.3, §18.1, S-652: when the name by the rule would clash where the declaration is seen (an E0304),
/// the E0320 has no candidate, and a note shows the name by the rule (the spelling of S-243 included).
/// A name in a scope apart (a block closed before the other binding) is no clash.
#[test]
fn a_name_by_the_rule_that_clashes_has_no_candidate_and_a_note() {
    let cases: [(&str, &str, &str); 6] = [
        ("items", "pub fn a__b() -> I32 {\n  1\n}\n\npub fn a_b() -> I32 {\n  2\n}\n", "a_b"),
        ("type_params", "pub fn f[_T, T](x: T) -> T {\n  x\n}\n", "T"),
        ("locals", "pub fn g(_x: I32, x: I32) -> I32 {\n  x + _x\n}\n", "x"),
        ("binding_and_item", "pub fn gain() -> I32 {\n  1\n}\n\npub fn h(Gain: I32) -> I32 {\n  Gain\n}\n", "gain"),
        ("reserved", "pub fn clock_() -> I32 {\n  1\n}\n\npub fn Clock() -> I32 {\n  2\n}\n", "clock_"),
        ("fields", "pub struct S {\n  aB: I32,\n  a_b: I32,\n}\n", "a_b"),
    ];
    for (tag, source, name) in cases {
        let (out, doc) = check_file(tag, source);
        let d = the_e0320(tag, &out, &doc);
        assert!(fixes_of(d).is_empty(), "{tag}: no candidate expected: {d}");
        let notes = d["notes"].as_array().expect("`notes` is an array");
        assert!(notes.iter().any(|n| str_of(n, "message").contains(&format!("`{name}`"))), "{tag}: {d}");
    }
    let apart = "pub fn f() -> I32 {\n  let a = {\n    let _w = 1\n    _w\n  }\n  let w = 3\n  a + w\n}\n";
    assert_eq!(after_the_candidate("apart", apart), apart.replace("_w", "w"));
}
