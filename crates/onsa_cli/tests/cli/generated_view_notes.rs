//! The notes of the E0710 of a generated type (`pair.Out`, `pair.In`) that is bound or put where a second-class value
//! cannot be, and of a row that a tail makes owned (R-476, R-477, S-218 (b), spec §4.5, §5.3, §5.4; W7-12 U2b/t).
//!
//! The case files do not compare notes, so what the notes of these two registered gaps promise is asked here.
//!
//! - R-477: the E0710 of a type argument that became a generated type (`Option[pair.Out]`, `Some(k)`, `id(o)`,
//!   `Wrap { x: o }`, `id::[pair.Out](o)`) must not tell the writer to give the type parameter `?Escape`: a
//!   generated type is not a type argument of a `?Escape` parameter either (S-927, §4.5: "flow の生成型 `In` / `Out`、
//!   §11.6 は E0710"), so the way out that the note of a `Span` shows (§4.5: "型パラメータに `?Escape` を付ける形を示す")
//!   does not work for it. The test asks what the decision says (a note that shows `?Escape` as a way out is not
//!   given): a note that mentions `?Escape` must be one that is about the generated type (it says `generated`). The
//!   words of the notes are not fixed by the spec, so nothing else of their text is asked. The same forms with a `Span`
//!   keep the note (the control).
//! - R-476: the E0710 of a binding whose initializer is an `if` with a tail that makes the row owned
//!   (`let k = if c { xs } else { b.slice(0, 1) }`) is "at the value that is put at the place of the binding" (§5.4), and the
//!   tail that made the row owned (the `b.slice(0, 1)`, a part of a local array) must be shown: the diagnostic or one of its
//!   notes points at it. One E0710 is given for the function (P-01). A `match` or `for` heading is not here: its
//!   binding may be made of any place (§5.4: "`match x` の腕の束縛（`x` は任意の場所か、破棄の要らない値）"), a part of a local
//!   array included, so such a heading is no error unless a tail is an `inout` argument (flow_gen_bind_if_heading.onsa).
//! - The place of the E0710 of a generated type written as a type argument after a name (`e::[pair.Out](o)`,
//!   `let g = id::[pair.Out]`, `mk::[pair.Out]()`): the type argument written, as before W7-12 U2b (the fix 1 of its
//!   break side, L2-3), since no type parameter takes a generated type (S-927, R-477); one that is inferred (`id(o)`) is
//!   at the call, and one in a type, of a `?Escape` parameter (`Handler[pair.Out]`), at the type argument. The case
//!   files see lines only, so the column is asked here. The E0710 written and the one
//!   inferred tell the same rule (R-477): a note says that no type parameter takes a generated type, and none shows
//!   `?Escape` as a way out.
//!
//! Every input is checked in this process (`check_input_out`), nothing is written to the disk.

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, notes_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

/// A flow with two inputs and a struct output (`pair.In`, `pair.Out`), a generic struct and a generic function.
const PRELUDE: &str = "pub struct Stereo {\n  l: F32,\n  r: F32,\n}\n\n\
     pub flow pair(l: F32 at sample, r: F32 at sample) -> Stereo at sample {\n  Stereo { l: l, r: r }\n}\n\n\
     pub struct Wrap[T] {\n  x: T,\n}\n\n\
     fn id[T](x: T) -> U32 {\n  1\n}\n\n";

/// The diagnostics of `PRELUDE` and `tail` (the document `onsa check --json` prints).
fn diagnostics_of(tail: &str) -> Vec<Value> {
    let text = format!("{PRELUDE}{tail}");
    let out = check_input_out(&PackageInput::single_file("main.onsa", &text));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

fn notes(d: &Value) -> Vec<String> {
    notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect()
}

fn codes(diags: &[Value]) -> Vec<&str> {
    diags.iter().map(code_of).collect()
}

/// The forms of R-477 with a generated type: what the type is, and the program (a function `f`).
const GENERATED: [(&str, &str); 6] = [
    ("a type argument written in a signature", "pub fn f(x: Option[pair.Out]) -> U32 {\n  1\n}\n"),
    ("a constructor of a bound name", "pub fn f(o: pair.Out) -> U32 {\n  let k = o\n  let s = Some(k)\n  1\n}\n"),
    ("a generic function, the Out", "pub fn f(o: pair.Out) -> U32 {\n  id(o)\n}\n"),
    ("a generic function, the In", "pub fn f(i: pair.In) -> U32 {\n  id(i)\n}\n"),
    ("a generic struct", "pub fn f(o: pair.Out) -> U32 {\n  let w = Wrap { x: o }\n  1\n}\n"),
    ("a type argument written in a call", "pub fn f(o: pair.Out) -> U32 {\n  id::[pair.Out](o)\n}\n"),
];

#[test]
fn the_e0710_of_a_generated_type_given_to_a_type_parameter_does_not_show_escape_as_a_way_out() {
    let mut failed = Vec::new();
    for (what, tail) in GENERATED {
        let diags = diagnostics_of(tail);
        let e0710: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0710").collect();
        if diags.len() != 1 || e0710.len() != 1 {
            failed.push(format!("{what}: want one E0710 and nothing else, got {:?}", codes(&diags)));
            continue;
        }
        for n in notes(e0710[0]) {
            if n.contains("?Escape") && !n.contains("generated") {
                failed.push(format!("{what}: a note shows `?Escape` for a generated type: {n:?}"));
            }
        }
    }
    assert!(failed.is_empty(), "{} of {} forms:\n  {}", failed.len(), GENERATED.len(), failed.join("\n  "));
}

#[test]
fn the_e0710_of_a_span_given_to_a_type_parameter_keeps_the_note_of_escape() {
    // §4.5: "修正候補は無く、note で `Span` を総称で受ける形（`xs: Span[T]`、`xs: [Span[T]; N]`）と、型パラメータに `?Escape` を付ける形を示す"
    // for the type argument that an expression made (`id(s)`, `Some(s)`).
    let forms = [
        ("a generic function", "pub fn f(s: Span[F32]) -> U32 {\n  id(s)\n}\n"),
        ("a constructor", "pub fn f(s: Span[F32]) -> U32 {\n  let o = Some(s)\n  1\n}\n"),
        ("a generic struct", "pub fn f(s: Span[F32]) -> U32 {\n  let w = Wrap { x: s }\n  1\n}\n"),
    ];
    for (what, tail) in forms {
        let diags = diagnostics_of(tail);
        let e0710: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0710").collect();
        assert!(
            diags.len() == 1 && e0710.len() == 1,
            "{what}: want one E0710 and nothing else, got {:?}",
            codes(&diags)
        );
        assert!(
            notes(e0710[0]).iter().any(|n| n.contains("?Escape")),
            "{what}: the note of `?Escape` for a `Span`: {:?}",
            notes(e0710[0])
        );
    }
}

/// The (line, column) of the first character of `needle` in `text`, from 1, the column in characters.
fn position_of(text: &str, needle: &str) -> (u64, u64) {
    let at = text.find(needle).unwrap_or_else(|| panic!("`{needle}` is not in the program"));
    let before = &text[..at];
    let line = before.matches('\n').count() as u64 + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) as u64 + 1;
    (line, col)
}

/// The start of a `span` object.
fn start_of(span: &Value) -> (u64, u64) {
    (span["line"].as_u64().expect("a line"), span["col"].as_u64().expect("a column"))
}

/// One E0710 for the program, and the tail `cause` that made the row owned is pointed at by the diagnostic or by one
/// of its notes.
fn check_cause_is_shown(what: &str, tail: &str, cause: &str) {
    let text = format!("{PRELUDE}{tail}");
    let want = position_of(&text, cause);
    let diags = diagnostics_of(tail);
    let e0710: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0710").collect();
    assert!(diags.len() == 1 && e0710.len() == 1, "{what}: want one E0710 and nothing else, got {:?}", codes(&diags));
    let d = e0710[0];
    let mut starts = vec![start_of(&d["span"])];
    starts.extend(notes_of(d).iter().filter_map(|n| n.get("span")).map(start_of));
    assert!(
        starts.contains(&want),
        "{what}: neither the diagnostic nor a note points at the tail `{cause}` {want:?}: {starts:?} ({d})"
    );
}

#[test]
fn a_let_that_picks_a_part_of_a_local_array_shows_the_tail_that_made_the_row_owned() {
    check_cause_is_shown(
        "a Span",
        "pub fn f(xs: Span[F32], c: Bool) -> U32 {\n  var b: [F32; 4] = [0.0; 4]\n  b[0] = 1.0\n  \
         let k = if c { xs } else { b.slice(0, 1) }\n  k.len()\n}\n",
        "b.slice(0, 1)",
    );
}

#[test]
fn a_let_that_picks_an_out_or_a_literal_shows_the_tail_that_made_the_row_owned() {
    check_cause_is_shown(
        "an Out",
        "pub fn f(o: pair.Out, c: Bool) -> U32 {\n  var x: [F32; 2] = [0.0; 2]\n  var y: [F32; 2] = [0.0; 2]\n  \
         let k = if c { o } else { pair.Out { l: x, r: y } }\n  k.l.len()\n}\n",
        "pair.Out { l: x, r: y }",
    );
}

/// The forms of a type argument written after a name: what it is, the program (a function `f` and what it calls), and
/// the text the E0710 starts at.
const WRITTEN: [(&str, &str, &str); 7] = [
    (
        "a field of a type with a `?Escape` parameter",
        "pub struct Handler[T: ?Escape] {\n  f: fn(T) -> F32,\n}\n\npub struct Holder {\n  h: Handler[pair.Out],\n}\n",
        "pair.Out]",
    ),
    (
        "the type of a parameter with a `?Escape` parameter",
        "pub struct Handler[T: ?Escape] {\n  f: fn(T) -> F32,\n}\n\npub fn f(h: Handler[pair.Out]) -> U32 {\n  1\n}\n",
        "pair.Out]",
    ),
    (
        "a call of a `?Escape` parameter",
        "fn e[T: ?Escape](x: T) -> U32 {\n  1\n}\n\npub fn f(o: pair.Out) -> U32 {\n  e::[pair.Out](o)\n}\n",
        "pair.Out](o)",
    ),
    ("a call", "pub fn f(o: pair.Out) -> U32 {\n  id::[pair.Out](o)\n}\n", "pair.Out](o)"),
    ("a function value", "pub fn f(o: pair.Out) -> U32 {\n  let g = id::[pair.Out]\n  1\n}\n", "pair.Out]\n"),
    (
        "a call with no argument",
        "fn mk[T]() -> U32 {\n  1\n}\n\npub fn f() -> U32 {\n  mk::[pair.Out]()\n}\n",
        "pair.Out]()",
    ),
    ("an inferred type argument, at the call", "pub fn f(o: pair.Out) -> U32 {\n  id(o)\n}\n", "id(o)"),
];

#[test]
fn the_e0710_of_a_generated_type_written_as_a_type_argument_is_at_the_type_written() {
    let mut failed = Vec::new();
    for (what, tail, at) in WRITTEN {
        let want = position_of(&format!("{PRELUDE}{tail}"), at);
        let diags = diagnostics_of(tail);
        match diags.as_slice() {
            [d] if code_of(d) == "E0710" && start_of(&d["span"]) == want => {
                let ns = notes(d);
                if !ns.iter().any(|n| n.contains("generated") && n.contains("no type parameter takes it")) {
                    failed.push(format!("{what}: no note of the rule of a generated type (R-477): {ns:?}"));
                }
                if ns.iter().any(|n| n.contains("?Escape") && !n.contains("generated")) {
                    failed.push(format!("{what}: a note shows `?Escape` for a generated type: {ns:?}"));
                }
            }
            _ => failed.push(format!(
                "{what}: want one E0710 at {want:?}, got {:?}",
                diags.iter().map(|d| (code_of(d), start_of(&d["span"]))).collect::<Vec<_>>()
            )),
        }
    }
    assert!(failed.is_empty(), "{} of {} forms:\n  {}", failed.len(), WRITTEN.len(), failed.join("\n  "));
}
