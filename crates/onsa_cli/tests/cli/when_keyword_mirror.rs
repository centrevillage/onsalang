//! `when` and `reset_if` out of a modifier are keywords as `in` is (W7-17 L4b; spec §2.2, §2.3, §11.10, §18.1; S-1082, S-654): written where a name, a type, an attribute, an arm or a
//! declaration goes, each diagnostic of the unit is the one of the same unit with `in` in their place (the code, the number of the candidates and the number of the notes). After an expression (the same line, or
//! the head of the next line where a binary operator would go on with it, §2.5), they are a postfix clause: the same codes as with `in`, no candidate, and the note of the chain (`.when~(c)`). A statement or a
//! declaration that ends no operand (the body of a function, a `for`), a type (of a field, of a type alias), a variant and the head of the next arm of a `match` are no expression before them.
//!
//! The forms are those of the sweep of the break side of L4 (`rules/leader.md` 4.9), with the forms found there of a note after no expression (L-1) and the `for` and `while` of the same line. Each is written with
//! `when` and run with it, with `reset_if` and with `in` in its place, in this process on texts (`run_texts`), no file written.

use crate::slow_written_forms::run_texts;
use crate::test_support::{diagnostics, doc_of, fixes_of, notes_of, str_of};

/// A form, its text written with `when`, and whether `when` stands after an expression there.
const FORMS: &[(&str, &str, bool)] = &[
    (
        "pat_after",
        "pub fn f(x: Option[I32]) -> I32 {\n  match x {\n    Some(v) when v > 0 => 1,\n    _ => 0,\n  }\n}\n",
        false,
    ),
    ("type_after", "pub fn f(x: I32) -> I32 {\n  let y: I32 when x = x\n  y\n}\n", false),
    ("attr_when", "@when\npub fn f(x: I32) -> I32 { x }\n", false),
    ("doc_then_when", "pub fn f(x: I32) -> I32 { x }\n/// doc\nwhen\n", false),
    ("use_when", "use std.when\npub fn f(x: I32) -> I32 { x }\n", false),
    ("named_arg", "pub fn g(a: I32) -> I32 { a }\npub fn f(s: I32) -> I32 { g(when: s) }\n", false),
    ("closure_param", "pub fn f(s: I32) -> I32 {\n  let h = |when: I32| when\n  h(s)\n}\n", false),
    (
        "pattern_bind",
        "pub fn f(x: Option[I32]) -> I32 {\n  match x {\n    Some(when) => 1,\n    _ => 0,\n  }\n}\n",
        false,
    ),
    ("enum_variant", "pub enum E { when, B }\npub fn f(s: I32) -> I32 { s }\n", false),
    ("generic_param", "pub fn f[when](s: I32) -> I32 { s }\n", false),
    ("after_comma_arg", "pub fn g(a: I32, b: I32) -> I32 { a }\npub fn f(x: I32) -> I32 {\n  g(x, when)\n}\n", false),
    ("head_of_stmt", "pub fn f(x: I32) -> I32 {\n  when x\n}\n", false),
    ("after_let_eq", "pub fn f(x: I32) -> I32 {\n  let y = when\n  y\n}\n", false),
    ("after_closing_brace", "pub fn f(x: I32) -> I32 {\n  let y = if x > 0 { 1 } else { 2 } when x\n  y\n}\n", true),
    ("after_call_plain", "pub fn g(x: I32) -> I32 { x }\npub fn f(x: I32) -> I32 {\n  g(x) when x\n}\n", true),
    ("after_index", "pub fn f(x: [I32; 2]) -> I32 {\n  x[0] when x\n}\n", true),
    (
        "after_struct_lit",
        "pub struct S { a: I32 }\npub fn f(x: I32) -> I32 {\n  let t = S { a: x } when x\n  1\n}\n",
        true,
    ),
    ("in_const", "pub const K: I32 = 1 when 2\n", true),
    ("top_after_fn", "pub fn f(x: I32) -> I32 { x }\nwhen\n", false),
    ("top_after_struct", "pub struct S { a: I32 }\nwhen\n", false),
    ("top_after_type_alias", "pub type T = I32\nwhen\n", false),
    ("after_open_brace", "pub fn f(x: I32) -> I32 {\n  when x\n}\n", false),
    ("after_param", "pub fn f(x: I32 when c) -> I32 { x }\n", false),
    ("flow_ret_clock", "pub flow f(x: F32 at sample) -> F32 at sample when c { x }\n", false),
    ("top_after_const", "pub const K: I32 = 1\nwhen\n", true),
    ("top_after_let", "pub fn f(x: I32) -> I32 {\n  let a: I32 = 1\n  when\n  a\n}\n", true),
    ("after_block_close", "pub fn f(x: I32) -> I32 {\n  if x > 0 { 1 } else { 2 }\n  when x\n}\n", true),
    (
        "inst_ok",
        "pub flow lp(x: F32 at sample) -> F32 at sample { x }\npub flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  lp~(x) when c\n}\n",
        true,
    ),
    (
        "inst_nl_when",
        "pub flow lp(x: F32 at sample) -> F32 at sample { x }\npub flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  lp~(x)\n  when c\n}\n",
        true,
    ),
    (
        "inst_doc_between",
        "pub flow lp(x: F32 at sample) -> F32 at sample { x }\npub flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  lp~(x)\n  /// doc\n  when c\n}\n",
        true,
    ),
    (
        "inside_call_arg",
        "pub flow lp(x: F32 at sample) -> F32 at sample { x }\npub flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  lp~(x when c)\n}\n",
        true,
    ),
    ("arm_newline_binding", "pub fn f(x: I32) -> I32 {\n  match x {\n    1 => 2\n    when => 3\n  }\n}\n", false),
    ("arm_comma_binding", "pub fn f(x: I32) -> I32 {\n  match x {\n    1 => 2,\n    when => 3,\n  }\n}\n", false),
    ("enum_variants_newline", "pub enum E {\n  A\n  when\n}\n", false),
    ("fields_newline", "pub struct S {\n  a: I32\n  when: I32\n}\n", false),
    ("params_newline", "pub fn f(\n  a: I32,\n  when: I32\n) -> I32 { a }\n", false),
    ("fn_after_attr_newline", "pub fn f(x: I32) -> I32 { x }\npub fn when(a: I32) -> I32 { a }\n", false),
    ("struct_field_default", "pub struct S {\n  a: I32 = 1,\n  when: I32 = 2,\n}\n", false),
    ("after_return_value_nl", "pub fn f(x: I32) -> I32 {\n  return x\n  when\n}\n", true),
    ("for_same_line", "pub fn f(x: I32) -> I32 {\n  for i in 0 ..< 3 { } when x\n  x\n}\n", false),
    ("while_same_line", "pub fn f(x: I32) -> I32 {\n  while x > 0 { } when x\n  x\n}\n", false),
];

/// `text` with every identifier `when` written `word`.
fn written(text: &str, word: &str) -> String {
    let mut out = String::new();
    let mut ident = String::new();
    for c in text.chars().chain(std::iter::once('\n')) {
        if c.is_alphanumeric() || c == '_' {
            ident.push(c);
            continue;
        }
        out.push_str(if ident == "when" { word } else { &ident });
        ident.clear();
        out.push(c);
    }
    out.pop();
    out
}

/// The diagnostics of `check` of `text`: the code, the candidates and the notes of each (the messages of the notes).
fn diags(text: &str) -> Vec<(String, usize, Vec<String>)> {
    let out = run_texts(&["check", "--json"], text);
    assert_eq!(out.code, 1, "check of\n{text}\nended with {}: {}", out.code, out.stderr);
    let doc = doc_of(&out);
    let notes = |d: &serde_json::Value| notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect();
    diagnostics(&doc).iter().map(|d| (str_of(d, "code").to_string(), fixes_of(d).len(), notes(d))).collect()
}

#[test]
fn when_and_reset_if_out_of_a_modifier_are_the_diagnostics_of_in_or_a_postfix_clause() {
    let mut postfix = 0;
    for &(name, text, after_an_expression) in FORMS {
        let mirror = diags(&written(text, "in"));
        let counted = |ds: &[(String, usize, Vec<String>)]| {
            ds.iter().map(|(c, f, n)| (c.clone(), *f, n.len())).collect::<Vec<_>>()
        };
        for word in ["when", "reset_if"] {
            let ds = diags(&written(text, word));
            let chain = format!(".{word}~(");
            if !after_an_expression {
                assert_eq!(counted(&ds), counted(&mirror), "{name} with `{word}` and with `in`:\n{text}");
                // The numbers are the same, and the notes are no note of the chain (in it, either modifier).
                let of_chain = |n: &String| n.contains(".when~(") || n.contains(".reset_if~(");
                assert!(!ds.iter().any(|d| d.2.iter().any(of_chain)), "{name}: no note of the chain: {ds:?}");
                continue;
            }
            let codes = |ds: &[(String, usize, Vec<String>)]| ds.iter().map(|d| d.0.clone()).collect::<Vec<_>>();
            assert_eq!(codes(&ds), codes(&mirror), "{name} with `{word}` and with `in`:\n{text}");
            let noted = ds.iter().any(|(c, _, n)| c == "E0002" && n.iter().any(|n| n.contains(&chain)));
            assert!(
                noted && ds.iter().all(|d| d.1 == 0),
                "{name}: the postfix `{word}` has the note of `{chain}…)` and no candidate: {ds:?}"
            );
            postfix += 1;
        }
    }
    assert_eq!(postfix, 2 * FORMS.iter().filter(|f| f.2).count());
    assert!(postfix > 0 && postfix < 2 * FORMS.len(), "both kinds of forms");
}
