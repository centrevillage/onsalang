//! The note of S-874 (W6-01 U3/t; spec §8.1, §4.1, §5.2, §18.1): an E0401 of two function types that
//! differ in the mode of a parameter between the default and `move` alone (the numbers, the types, the
//! `inout`, the result are the same, and the effect row and `rt` meet rules 2 and 3) gets a note that
//! shows how to mend it, by the form of what was found:
//! - a constructor whose elements are Dup: an anonymous function that wraps it (`fn(x) { Mode.Gain(x) }`);
//! - a function of the program (an associated one, one with the type arguments written) whose parameters
//!   are Copy and no function types: the mode of its declaration, or the wrapping function;
//! - an anonymous function with no candidate (a place of an annotation, a `move` to be taken off): how the
//!   mode of a parameter is written;
//! - anything else (a variable, a parameter of a function type, the result of a call, a field, a function
//!   whose parameter is no Copy, a constructor with an Affine element): the parameters that differ, named,
//!   and no wrapping function (it would capture, and a capture cannot be kept, E0710, §5.2).
//!
//! No note is given when a candidate is (an anonymous function written as the argument, with `move`
//! expected), when `inout` differs, when the number or the types of the parameters or the result differ,
//! when the effect row is not within the expected one or `rt` is expected and not found, and when the
//! function type that differs is inside the result or a type argument (`Option[fn(move U32) -> U32]`).
//!
//! The runner of the case files does not compare notes, so they are pinned here; the cases of the same
//! diagnostics are `negative/ctor_fn_value_default_mode.onsa` and `negative/lambda_move_no_candidate.onsa`
//! (their codes and places stay). The candidate that U2a gave new, "add `move`" to an anonymous function
//! that writes `uses {}`, is `fixes/e0401_lambda_move_uses_empty.onsa`.
//!
//! The inputs are programs in memory (`check_input_out`, nothing is written, `rules/common.md` 3.7). A line
//! that ends with `//~ E0401 <tag> <positions>` is where the E0401 is expected, and the tag tells what its
//! notes (and candidates) are:
//! - `wrap`: a note shows a wrapping anonymous function (`fn(` with a body in braces);
//! - `fix`: a note shows the wrapping function, and a note speaks of the declaration;
//! - `mode`: a note speaks of `move` (how the mode of a parameter is written);
//! - `name`: a note, none with a body in braces, so no wrapping function;
//! - `note`: a note;
//! - `none`: no note and no candidate;
//! - `cand`: one candidate and no note.
//!
//! Then the positions (from 1) of the parameters that differ, that a note names (by the number or the
//! ordinal; the programs that name positions write no digit in the types).
//!
//! Each test checks the words that tell what the note shows, not its text, which the spec does not fix
//! (§18.1). Nothing is said of what other notes an E0401 has.

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{code_of, diagnostics, doc_of, fixes_of, notes_of, span_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

// ---- the harness ------------------------------------------------------------------------------------

struct Want {
    line: u64,
    tag: String,
    positions: Vec<u32>,
}

/// The expectations written at the ends of the lines of `src`.
fn wants(src: &str) -> Vec<Want> {
    let mut out = Vec::new();
    for (i, line) in src.lines().enumerate() {
        let Some((_, tail)) = line.split_once("//~ E0401") else { continue };
        let mut words = tail.split_whitespace();
        let tag = words.next().unwrap_or_else(|| panic!("line {}: no tag", i + 1)).to_string();
        let positions = words.map(|w| w.parse().unwrap_or_else(|_| panic!("line {}: position {w}", i + 1))).collect();
        out.push(Want { line: i as u64 + 1, tag, positions });
    }
    out
}

fn notes(d: &Value) -> Vec<String> {
    notes_of(d).iter().map(|n| str_of(n, "message").to_string()).collect()
}

fn shows_wrap(n: &str) -> bool {
    n.contains("fn(") && n.contains('{') && n.contains('}')
}

fn speaks_of_the_declaration(n: &str) -> bool {
    n.to_lowercase().contains("declar")
}

fn speaks_of_move(n: &str) -> bool {
    n.contains("move")
}

/// True when the notes name the parameter at `k` (from 1), by the number or the ordinal. The numbers of
/// the sections (`§4.1`) are not counted.
fn names_position(notes: &[String], k: u32) -> bool {
    let mut text = String::new();
    let mut in_section = false;
    for c in notes.join("\n").chars() {
        in_section = c == '§' || (in_section && (c.is_ascii_digit() || c == '.'));
        if !in_section {
            text.push(c);
        }
    }
    let lower = text.to_lowercase();
    let ordinals: [&[&str]; 3] = [&["1st", "first"], &["2nd", "second"], &["3rd", "third"]];
    text.contains(&k.to_string()) || ordinals[k as usize - 1].iter().any(|w| lower.contains(w))
}

/// What is wrong with the notes and candidates of the E0401 `d` for the expectation `w`; empty when right.
fn judge(d: &Value, w: &Want) -> Vec<String> {
    let notes = notes(d);
    let fixes = fixes_of(d).len();
    let mut bad = Vec::new();
    let mut want = |ok: bool, what: &str| {
        if !ok {
            bad.push(what.to_string());
        }
    };
    match w.tag.as_str() {
        "wrap" => want(notes.iter().any(|n| shows_wrap(n)), "no note shows a wrapping function"),
        "fix" => {
            want(notes.iter().any(|n| shows_wrap(n)), "no note shows a wrapping function");
            want(notes.iter().any(|n| speaks_of_the_declaration(n)), "no note speaks of the declaration");
        }
        "mode" => want(notes.iter().any(|n| speaks_of_move(n)), "no note speaks of `move`"),
        "name" => {
            want(!notes.is_empty(), "no note");
            want(!notes.iter().any(|n| n.contains('{')), "a note shows a body in braces (a wrapping function)");
        }
        "note" => want(!notes.is_empty(), "no note"),
        "none" => {
            want(notes.is_empty(), "a note");
            want(fixes == 0, "a candidate");
        }
        "cand" => {
            want(notes.is_empty(), "a note beside the candidate");
            want(fixes == 1, "not one candidate");
        }
        other => panic!("line {}: the tag {other}", w.line),
    }
    for &k in &w.positions {
        want(names_position(&notes, k), &format!("no note names the parameter {k}"));
    }
    let shown = if notes.is_empty() { String::from("(no notes)") } else { format!("{notes:?}") };
    bad.into_iter().map(|b| format!("{b}; notes: {shown}")).collect()
}

/// The diagnostics of the package of `input` (the document `onsa check --json` prints).
fn diagnostics_of_input(input: &PackageInput) -> Vec<Value> {
    let out = check_input_out(input);
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

/// Check the marked E0401 of the diagnostics of a file `name` of the package; `texts` is the whole package.
fn check_marked(texts: &Texts, name: &str) {
    let src = &texts[name];
    let diags = diagnostics_of_input(&input_of("demo", texts));
    let wants = wants(src);
    // The shape of the program: the E0401 of the marked lines of the file and nothing else.
    let got: Vec<(String, u64)> = diags.iter().map(|d| (code_of(d).to_string(), span_of(&d["span"]).line)).collect();
    let mut expected: Vec<(String, u64)> = wants.iter().map(|w| ("E0401".to_string(), w.line)).collect();
    let mut got_sorted = got.clone();
    got_sorted.sort();
    expected.sort();
    assert_eq!(got_sorted, expected, "{name}: the diagnostics are not the marked E0401 alone: {diags:?}");
    let lines: Vec<&str> = src.lines().collect();
    let mut problems = Vec::new();
    for w in &wants {
        let d = diags.iter().find(|d| span_of(&d["span"]).line == w.line).expect("the diagnostic of the line");
        for b in judge(d, w) {
            problems.push(format!("{name}:{} [{}] `{}`: {b}", w.line, w.tag, lines[w.line as usize - 1].trim()));
        }
    }
    assert!(problems.is_empty(), "{} of {} lines are wrong:\n{}", problems.len(), wants.len(), problems.join("\n"));
}

/// Check the marked E0401 of a program of one file.
fn check_program(src: &str) {
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), src.to_string());
    check_marked(&texts, "main.onsa");
}

// ---- 1. a constructor whose elements are Dup: the wrapping function ---------------------------------------

const CONSTRUCTORS: &str = r#"use std.array

pub enum Shape {
  Circle(F32),
  Point,
}

pub enum Mode {
  Off,
  Gain(F32),
}

pub enum Low {
  Bad,
  Worse(U32),
}

pub enum High {
  Wrapped(Low),
  Other,
}

pub enum Pair {
  Both(Bool, Low),
  Nope,
}

pub enum Slot[T: ?Dup] {
  Full(T),
  Empty,
}

pub struct Maker {
  make: fn(F32) -> Shape,
}

pub fn build(make: fn(F32) -> Mode) -> Mode {
  make.(1.0)
}

pub fn build_rt(make: rt fn(F32) -> Mode) -> Mode {
  make.(1.0)
}

pub fn build_pair(make: fn(Bool, Low) -> Pair) -> Pair {
  make.(true, Low.Bad)
}

pub fn build_pair_one_default(make: fn(move Bool, Low) -> Pair) -> Pair {
  make.(true, Low.Bad)
}

pub fn as_an_argument() -> Mode {
  build(Mode.Gain)                                               //~ E0401 wrap
}

pub fn as_an_argument_where_rt_is_expected() -> Mode {
  build_rt(Mode.Gain)                                            //~ E0401 wrap
}

pub fn in_an_annotated_let() -> Shape {
  let f: fn(F32) -> Shape = Shape.Circle                         //~ E0401 wrap
  f.(1.0)
}

pub fn some_in_an_annotated_let() -> Option[U32] {
  let wrap: fn(U32) -> Option[U32] = Some                        //~ E0401 wrap
  wrap.(1)
}

pub fn err_of_a_copy_enum_in_an_annotated_let() -> Result[U32, Low] {
  let f: fn(Low) -> Result[U32, Low] = Err                       //~ E0401 wrap
  f.(Low.Bad)
}

pub fn a_variant_of_a_copy_enum_in_an_annotated_let() -> High {
  let f: fn(Low) -> High = High.Wrapped                          //~ E0401 wrap
  f.(Low.Bad)
}

pub fn a_generic_variant_in_an_annotated_let() -> Slot[U32] {
  let f: fn(U32) -> Slot[U32] = Slot.Full                        //~ E0401 wrap
  f.(1)
}

pub fn in_a_field() -> Shape {
  let m = Maker { make: Shape.Circle }                           //~ E0401 wrap
  m.make.(1.0)
}

pub fn as_the_result_of_a_function() -> fn(F32) -> Shape {
  Shape.Circle                                                   //~ E0401 wrap
}

pub fn from_fn_of_some() -> [Option[U32]; 3] {
  array.from_fn(Some)                                            //~ E0401 wrap
}

pub fn two_payloads_that_both_differ() -> Pair {
  build_pair(Pair.Both)                                          //~ E0401 wrap
}

pub fn one_of_two_payloads_that_differs() -> Pair {
  build_pair_one_default(Pair.Both)                              //~ E0401 wrap
}

pub fn a_shared_element() -> U32 uses {Alloc} {
  let f: fn(Str) -> Option[Str] = Some                           //~ E0401 wrap
  match f.("a") {
    Some(t) => t.len(),
    None => 0,
  }
}

pub fn in_a_branch(c: Bool) -> Option[U32] {
  let f: fn(U32) -> Option[U32] = if c { Some } else { fn(x: U32) -> Option[U32] { None } }   //~ E0401 wrap
  f.(1)
}

pub fn in_an_arm(c: Bool) -> Option[U32] {
  let f: fn(U32) -> Option[U32] = match c {
    true => Some,                                                //~ E0401 wrap
    false => fn(x: U32) -> Option[U32] { None },
  }
  f.(1)
}

pub fn as_the_result_of_an_anonymous_function() -> Option[U32] {
  let make = fn(c: Bool) -> fn(U32) -> Option[U32] {
    Some                                                         //~ E0401 wrap
  }
  make.(true).(1)
}

pub fn in_a_generic_function[T: Copy](x: T) -> Slot[T] {
  let f: fn(T) -> Slot[T] = Slot.Full                            //~ E0401 wrap
  f.(x)
}

pub fn fine() -> Mode {
  let f: fn(F32) -> Mode = fn(x) { Mode.Gain(x) }
  f.(1.0)
}
"#;

#[test]
fn a_constructor_with_dup_elements_in_the_wrong_mode_notes_the_wrapping_function() {
    // §8.1: "要素が Dup の構築子なら無名関数で包む形". A constructor is `rt fn(move …)` (§4.4), so it is found in
    // the default mode of an argument, an annotated `let`, a field, a result, a branch, an arm, the result of an
    // anonymous function, a generic function; the `rt` side is no reason for another note (§8.1 rule 3 is met).
    check_program(CONSTRUCTORS);
}

#[test]
fn a_constructor_in_a_package_of_two_modules_notes_the_wrapping_function() {
    // The constructors of another module (`use lib.Mode`), the same note.
    let mut texts = Texts::new();
    texts.insert(
        "lib.onsa".to_string(),
        "pub enum Mode {\n  Off,\n  Gain(F32),\n}\n\npub fn build(make: fn(F32) -> Mode) -> Mode {\n  make.(1.0)\n}\n"
            .to_string(),
    );
    texts.insert(
        "main.onsa".to_string(),
        "use lib.{Mode, build}\n\npub fn run() -> Mode {\n  build(Mode.Gain)                                               //~ E0401 wrap\n}\n"
            .to_string(),
    );
    check_marked(&texts, "main.onsa");
}

// ---- 2. a function of the program with Copy parameters: the declaration or the wrapping function ----------

const ITEMS: &str = r#"pub enum Low {
  Bad,
  Worse(U32),
}

pub enum High {
  Wrapped(Low),
  Other,
}

pub struct Calc {
  n: U32,
}

impl Calc {
  pub fn bump(x: U32) -> U32 {
    x + 1
  }
}

pub struct Op {
  f: fn(U32) -> U32,
}

pub fn read_low() -> Result[U32, Low] {
  Ok(1)
}

pub fn convert_by_borrow(e: Low) -> High {
  High.Wrapped(e)
}

pub fn call(f: fn(U32) -> U32, x: U32) -> U32 {
  f.(x)
}

pub fn apply(f: fn(move U32) -> U32, x: U32) -> U32 {
  f.(x)
}

pub fn k_default(x: U32) -> U32 {
  x + 1
}

pub fn k_move(move x: U32) -> U32 {
  x + 1
}

pub fn id[T: Copy](x: T) -> T {
  x
}

pub fn norm(p: (F32, F32)) -> F32 {
  p.0
}

pub fn call_pair(f: fn(move (F32, F32)) -> F32) -> F32 {
  f.((1.0, 2.0))
}

pub fn both(a: Bool, b: Low) -> High {
  High.Other
}

pub fn call_both(f: fn(move Bool, move Low) -> High) -> High {
  f.(true, Low.Bad)
}

pub fn call_first(f: fn(move Bool, Low) -> High) -> High {
  f.(true, Low.Bad)
}

pub fn three(move a: Bool, inout b: Bool, c: Bool) -> Bool {
  b = c
  b
}

pub fn call_three(f: fn(Bool, inout Bool, move Bool) -> Bool) -> Bool {
  var v = true
  f.(true, inout v, false)
}

pub fn into_map_err() -> Result[U32, High] {
  read_low().map_err(convert_by_borrow)                          //~ E0401 fix
}

pub fn default_into_move() -> U32 {
  apply(k_default, 2)                                            //~ E0401 fix
}

pub fn move_into_default() -> U32 {
  call(k_move, 2)                                                //~ E0401 fix
}

pub fn in_an_annotated_let() -> U32 {
  let f: fn(move U32) -> U32 = k_default                         //~ E0401 fix
  f.(1)
}

pub fn an_associated_function() -> U32 {
  apply(Calc.bump, 2)                                            //~ E0401 fix
}

pub fn a_generic_function_with_the_type_argument() -> U32 {
  apply(id::[U32], 2)                                            //~ E0401 fix
}

pub fn a_tuple() -> F32 {
  call_pair(norm)                                                //~ E0401 fix
}

pub fn two_parameters_that_both_differ() -> High {
  call_both(both)                                                //~ E0401 fix
}

pub fn one_of_two_parameters_that_differs() -> High {
  call_first(both)                                               //~ E0401 fix
}

pub fn an_inout_that_is_the_same_in_both() -> Bool {
  call_three(three)                                              //~ E0401 note
}

pub fn in_a_field() -> U32 {
  let o = Op { f: k_move }                                       //~ E0401 fix
  o.f.(1)
}

pub fn as_the_result_of_a_function() -> fn(U32) -> U32 {
  k_move                                                         //~ E0401 fix
}

pub fn in_a_branch(c: Bool) -> U32 {
  let f: fn(move U32) -> U32 = if c { k_default } else { k_move }   //~ E0401 fix
  f.(1)
}

pub fn as_the_element_of_a_constructor() -> Option[U32] {
  let o: Option[fn(U32) -> U32] = Some(k_move)                   //~ E0401 fix
  match o {
    Some(f) => Some(f.(1)),
    None => None,
  }
}

pub fn in_an_anonymous_function() -> U32 {
  let make = fn(c: Bool) -> fn(move U32) -> U32 {
    k_default                                                    //~ E0401 fix
  }
  make.(true).(1)
}

pub fn fine() -> U32 {
  apply(fn(move x: U32) -> U32 { k_default(x) }, 2)
}
"#;

#[test]
fn a_function_of_the_program_with_copy_parameters_notes_the_declaration_and_the_wrapping_function() {
    // §8.1: "引数の型が Copy の名前で定義した関数なら宣言のモードを揃えるか包む形". Both directions (the default
    // given to a `move`, `move` to the default), an associated function, one with the type arguments written, a
    // tuple, one or both of two parameters, in the places of §8.1.
    check_program(ITEMS);
}

// ---- 3. an anonymous function with no candidate: how the mode of a parameter is written ---------------------

const LAMBDAS: &str = r#"pub struct Holder {
  f: fn(move Bool) -> Bool,
}

pub fn call(f: fn(Bool) -> Bool) -> Bool {
  f.(true)
}

pub fn apply(f: fn(move Bool) -> Bool) -> Bool {
  f.(true)
}

pub fn in_the_place_of_the_annotation() -> Bool {
  let f: fn(move Bool) -> Bool = fn(k: Bool) -> Bool { k }       //~ E0401 mode
  f.(true)
}

pub fn move_where_the_default_is_expected() -> Bool {
  call(fn(move k: Bool) -> Bool { k })                           //~ E0401 mode
}

pub fn in_a_field() -> Bool {
  let h = Holder { f: fn(k: Bool) -> Bool { k } }                //~ E0401 mode
  h.f.(true)
}

pub fn as_the_result_of_a_function() -> fn(move Bool) -> Bool {
  fn(k: Bool) -> Bool { k }                                      //~ E0401 mode
}

pub fn two_parameters_that_differ_in_the_place_of_the_annotation() -> Bool {
  let f: fn(move Bool, Bool, move Bool) -> Bool = fn(a: Bool, b: Bool, c: Bool) -> Bool { a }   //~ E0401 mode 1 3
  f.(true, true, true)
}

pub fn move_taken_off_two_parameters() -> Bool {
  let f: fn(Bool, move Bool, Bool) -> Bool = fn(move a: Bool, move b: Bool, move c: Bool) -> Bool { a }   //~ E0401 mode 1 3
  f.(true, true, true)
}

pub fn fine() -> Bool {
  apply(fn(move k: Bool) -> Bool { k })
}
"#;

#[test]
fn an_anonymous_function_with_no_candidate_notes_how_the_mode_of_a_parameter_is_written() {
    // §8.1: "候補の無い無名関数なら引数のモードの書き方". The place of the annotation of a `let`, a `move` to be
    // taken off, a field and a result (not an argument); with more than one parameter the ones that differ.
    check_program(LAMBDAS);
}

// ---- 4. the rest: the parameters that differ, named, and no wrapping function --------------------------------

const REST: &str = r#"pub struct Holder {
  f: fn(Bool) -> Bool,
}

pub fn apply(f: fn(move Bool) -> Bool) -> Bool {
  f.(true)
}

pub fn apply_three(f: fn(move Bool, Bool, move Bool) -> Bool) -> Bool {
  f.(true, true, true)
}

pub fn call(f: fn(Bool) -> Bool) -> Bool {
  f.(true)
}

pub fn flip(b: Bool) -> Bool {
  b
}

pub fn pick() -> fn(Bool) -> Bool {
  flip
}

pub fn a_variable_that_holds_an_anonymous_function() -> Bool {
  let l = fn(x: Bool) -> Bool { x }
  apply(l)                                                       //~ E0401 name
}

pub fn a_parameter_of_a_function_type(g: fn(Bool) -> Bool) -> Bool {
  apply(g)                                                       //~ E0401 name
}

pub fn a_parameter_of_a_function_type_that_is_move(move g: fn(move Bool) -> Bool) -> Bool {
  call(g)                                                        //~ E0401 name
}

pub fn the_result_of_a_call() -> Bool {
  apply(pick())                                                  //~ E0401 name
}

pub fn a_field(h: Holder) -> Bool {
  apply(h.f)                                                     //~ E0401 name
}

pub fn three_parameters_of_which_two_differ(g: fn(Bool, Bool, Bool) -> Bool) -> Bool {
  apply_three(g)                                                 //~ E0401 name 1 3
}

pub fn fine() -> Bool {
  apply(fn(move x) { flip(x) })
}
"#;

#[test]
fn a_variable_a_parameter_a_call_a_field_and_the_rest_note_the_parameters_that_differ_and_no_wrapping_function() {
    // §8.1: "それ以外（変数、関数型の引数など）は違う引数を名指すだけである（変数と関数型の引数を包むと捕捉になり、
    // 保存する位置で E0710 になる、§5.2）". The positions of the parameters that differ are named when there are
    // more than one.
    check_program(REST);
}

const REST_OF_OTHER_KINDS: &str = r#"pub enum Boxed {
  Item(Buf[F32]),
  Empty,
}

pub fn apply_taking(f: fn(move fn(Bool) -> Bool) -> Bool) -> Bool {
  true
}

pub fn use_buf(f: fn(Buf[F32]) -> Boxed) -> Bool {
  true
}

pub fn use_str(f: fn(move Str) -> Bool) -> Bool {
  true
}

pub fn run_one(f: fn(Bool) -> Bool) -> Bool {
  f.(true)
}

pub fn len_is_zero(s: Str) -> Bool {
  true
}

pub fn a_function_whose_parameter_is_no_copy() -> Bool {
  use_str(len_is_zero)                                           //~ E0401 name
}

pub fn a_function_whose_parameter_is_a_function_type() -> Bool {
  apply_taking(run_one)                                          //~ E0401 name
}

pub fn a_constructor_with_an_affine_element() -> Bool {
  use_buf(Boxed.Item)                                            //~ E0401 name
}
"#;

#[test]
fn a_parameter_that_is_no_copy_and_an_affine_element_note_the_parameters_that_differ() {
    // §8.1 reads: a constructor "要素が Dup" and a function of the program "引数の型が Copy" are the forms of the
    // wrapping function; "それ以外" names the parameters that differ. A `Str` is Shared (Dup, not Copy), a function
    // type is no Copy of this kind (S-874), and a `Buf` is Affine. The wrapped form of these would not be a
    // mending (an owned `Str` needs `Alloc` to be dropped, a function type captured is E0710, an Affine value
    // cannot be given by a borrowing function), so no wrapping function is shown.
    check_program(REST_OF_OTHER_KINDS);
}

#[test]
fn what_the_note_does_not_show_cannot_be_wrapped_to_be_kept() {
    // §5.2 (the reason of the note above): a function that wraps a variable or a parameter of a function type
    // captures it, and where the function is kept (`move f` that is returned) that is an E0710. The note is
    // not a candidate, so the program itself has the E0401, and the wrapped form has the E0710: this pins that
    // the wrapped form is no mending for these forms.
    let src = r#"pub fn store(move f: fn(move U32) -> U32) -> fn(move U32) -> U32 {
  f
}

pub fn wrapped_variable() -> U32 {
  let l = fn(x: U32) -> U32 { x + 1 }
  let s = store(fn(move y: U32) -> U32 { l.(y) })                //~ E0710
  s.(1)
}
"#;
    let diags = diagnostics_of_input(&input_of("demo", &Texts::from([("main.onsa".to_string(), src.to_string())])));
    let codes: Vec<&str> = diags.iter().map(code_of).collect();
    assert_eq!(codes, ["E0710"], "{diags:?}");
}

// ---- 5. no note ------------------------------------------------------------------------------------------

const NONE: &str = r#"pub enum Shape {
  Circle(F32),
  Rect(F32, F32),
  Point,
}

pub enum Low {
  Bad,
  Worse(U32),
}

pub enum High {
  Wrapped(Low),
  Other,
}

pub fn read_low() -> Result[U32, Low] {
  Ok(1)
}

pub fn call(f: fn(U32) -> U32, x: U32) -> U32 {
  f.(x)
}

pub fn apply(f: fn(move U32) -> U32, x: U32) -> U32 {
  f.(x)
}

pub fn apply_inout(f: fn(inout U32) -> U32, inout x: U32) -> U32 {
  f.(inout x)
}

pub fn apply_move_inout(f: fn(inout U32, move U32) -> U32, inout x: U32) -> U32 {
  f.(inout x, 1)
}

pub fn apply_pure_move(f: fn(move U32) -> U32) -> U32 {
  f.(1)
}

pub fn apply_alloc(f: fn(move U32) -> U32 uses {Alloc}) -> U32 uses {Alloc} {
  f.(1)
}

pub rt fn apply_rt(f: rt fn(move U32) -> U32) -> U32 {
  f.(1)
}

pub fn apply_shape(f: fn(move F32, move F32) -> Shape) -> Shape {
  f.(1.0, 2.0)
}

pub fn apply_one_shape(f: fn(F32) -> Shape) -> Shape {
  f.(1.0)
}

pub fn k_default(x: U32) -> U32 {
  x + 1
}

pub fn k_move(move x: U32) -> U32 {
  x + 1
}

pub fn k_inout(inout x: U32) -> U32 {
  x
}

pub fn k_alloc(move x: U32) -> U32 uses {Alloc} {
  x
}

pub fn k_bool(x: Bool) -> U32 {
  1
}

pub fn k_shape(x: U32) -> Shape {
  Shape.Point
}

pub fn k_two(x: U32, y: U32) -> U32 {
  x
}

pub fn mk_move() -> fn(move U32) -> U32 {
  k_move
}

pub fn use_result(f: fn() -> fn(U32) -> U32) -> U32 {
  f.().(1)
}

// ---------------------------------------------------------------- the candidate of S-872 is the help

pub fn the_candidate_with_a_lambda_argument() -> U32 {
  apply(fn(k: U32) -> U32 { k + 1 }, 2)                          //~ E0401 cand
}

pub fn the_candidate_before_a_map_err() -> Result[U32, High] {
  read_low().map_err(fn(e: Low) -> High { High.Wrapped(e) })     //~ E0401 cand
}

pub fn the_candidate_of_a_lambda_that_writes_an_empty_row() -> U32 {
  apply_alloc(fn(x: U32) -> U32 uses {} { x })                   //~ E0401 cand
}

// ---------------------------------------------------------------- inout

pub fn the_default_where_inout_is_expected(inout n: U32) -> U32 {
  apply_inout(k_default, inout n)                                //~ E0401 none
}

pub fn move_where_inout_is_expected(inout n: U32) -> U32 {
  apply_inout(k_move, inout n)                                   //~ E0401 none
}

pub fn inout_where_move_is_expected() -> U32 {
  apply(k_inout, 2)                                              //~ E0401 none
}

pub fn inout_where_the_default_is_expected() -> U32 {
  call(k_inout, 2)                                               //~ E0401 none
}

pub fn a_constructor_where_inout_is_expected(inout x: F32) -> Shape {
  let f: fn(inout F32) -> Shape = Shape.Circle                   //~ E0401 none
  f.(inout x)
}

pub fn inout_differs_and_the_mode_of_another_parameter_too(inout n: U32) -> U32 {
  apply_move_inout(k_default_inout, inout n)                     //~ E0401 none
}

pub fn k_default_inout(x: U32, y: U32) -> U32 {
  x
}

// ---------------------------------------------------------------- the number, the types and the result

pub fn another_number_of_parameters_of_a_constructor() -> Shape {
  apply_shape(Shape.Circle)                                      //~ E0401 none
}

pub fn another_number_of_parameters_of_a_function() -> U32 {
  apply(k_two, 1)                                                //~ E0401 none
}

pub fn another_number_of_parameters_of_a_lambda() -> U32 {
  apply(fn(k: U32, m: U32) -> U32 { k }, 2)                      //~ E0401 none
}

pub fn another_parameter_type() -> U32 {
  apply(k_bool, 2)                                               //~ E0401 none
}

pub fn another_parameter_type_of_a_lambda() -> U32 {
  apply(fn(k: Bool) -> U32 { 1 }, 2)                             //~ E0401 none
}

pub fn another_result_type() -> Shape {
  apply_one_shape(k_shape)                                       //~ E0401 none
}

pub fn another_result_type_of_a_constructor() -> Shape {
  let f: fn(F32) -> U32 = Shape.Circle                           //~ E0401 none
  f.(1.0)
}

// ---------------------------------------------------------------- the effect row and rt (rules 2 and 3)

pub fn an_effect_row_that_is_not_within_the_expected() -> U32 {
  apply_pure_move(k_alloc)                                       //~ E0401 none
}

pub fn an_effect_row_that_is_not_within_the_expected_for_a_lambda() -> U32 {
  apply_pure_move(fn(x: U32) -> U32 uses {Alloc} { x })          //~ E0401 none
}

pub fn a_function_that_is_no_rt_where_rt_is_expected() -> U32 {
  apply_rt(k_default)                                            //~ E0401 none
}

// ---------------------------------------------------------------- the function type inside the result or a type argument

pub fn inside_the_result() -> U32 {
  use_result(mk_move)                                            //~ E0401 none
}

pub fn inside_a_type_argument(o: Option[fn(move U32) -> U32]) -> Option[fn(U32) -> U32] {
  o                                                              //~ E0401 none
}

pub fn inside_an_array(a: [fn(move U32) -> U32; 2]) -> [fn(U32) -> U32; 2] {
  a                                                              //~ E0401 none
}

pub fn fine() -> U32 {
  apply(k_move, 2)
}
"#;

#[test]
fn no_note_is_given_where_the_modes_do_not_alone_make_the_error() {
    // §8.1: the note is for an E0401 "数・型・返り値・`inout` は同じで、効果行と `rt` は規則 2・3 を満たす". The forms
    // with a candidate ("候補の付く形には note を付けない") and the forms that more than the mode of a parameter
    // between the default and `move` separates have no note, and no candidate besides S-872's (§8.1).
    check_program(NONE);
}

#[test]
fn the_candidate_of_an_empty_row_adds_move_and_the_program_is_clean() {
    // S-872 (§8.1) after U2a: `uses {}` written by an anonymous function given where
    // `fn(move U32) -> U32 uses {Alloc}` is expected is within the row (rule 2), so the modes alone are what
    // differ and the candidate adds `move` to the parameter, as for a function with no row.
    let src = "pub fn take_m(f: fn(move U32) -> U32 uses {Alloc}) -> U32 uses {Alloc} {\n  f.(1)\n}\n\n\
               pub fn run() -> U32 uses {Alloc} {\n  take_m(fn(x: U32) -> U32 uses {} { x })\n}\n";
    let diags = diagnostics_of_input(&input_of("demo", &Texts::from([("main.onsa".to_string(), src.to_string())])));
    let e0401: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0401").collect();
    assert_eq!(diags.len(), 1, "{diags:?}");
    assert_eq!(e0401.len(), 1, "{diags:?}");
    assert_eq!(fixes_of(e0401[0]).len(), 1, "the candidate: {:?}", e0401[0]);
    let edits = crate::test_support::edits_of(fixes_of(e0401[0])[0]);
    assert!(edits.iter().any(|e| e.replace.contains("move")), "the candidate adds `move`");
}

// ---- the checks themselves ----------------------------------------------------------------------------------

fn diag_with(notes: &[&str], fixes: usize) -> Value {
    let notes: Vec<Value> = notes.iter().map(|m| serde_json::json!({ "message": m })).collect();
    let fixes: Vec<Value> = (0..fixes).map(|_| serde_json::json!({ "title": "add `move`", "edits": [] })).collect();
    serde_json::json!({ "code": "E0401", "notes": notes, "fixes": fixes })
}

fn want(tag: &str, positions: &[u32]) -> Want {
    Want { line: 1, tag: tag.to_string(), positions: positions.to_vec() }
}

#[test]
fn the_checks_take_the_notes_of_the_shapes_the_spec_shows_and_refuse_the_others() {
    // The notes the spec shows in §8.1 (wording is free, §18.1): they pass, so that a test that fails after
    // the work fails for a note that is not there. The checks refuse what they must tell apart.
    let wrap = diag_with(&["wrap it: `fn(x) { Mode.Gain(x) }`"], 0);
    assert!(judge(&wrap, &want("wrap", &[])).is_empty());
    assert!(!judge(&wrap, &want("name", &[])).is_empty(), "a wrapping function is no naming alone");
    assert!(!judge(&wrap, &want("none", &[])).is_empty());
    let both = diag_with(&["align the mode in its declaration, or wrap it: `fn(move x) { conv(x) }`"], 0);
    assert!(judge(&both, &want("fix", &[])).is_empty());
    assert!(!judge(&wrap, &want("fix", &[])).is_empty(), "the declaration is spoken of by `fix`");
    let named = diag_with(&["the parameters 1 and 3 differ in the mode (§4.1)"], 0);
    assert!(judge(&named, &want("name", &[1, 3])).is_empty());
    assert!(!judge(&named, &want("name", &[2])).is_empty(), "the section number is no position");
    assert!(!judge(&named, &want("wrap", &[])).is_empty());
    let ordinal = diag_with(&["the first and the third parameter differ"], 0);
    assert!(judge(&ordinal, &want("name", &[1, 3])).is_empty());
    let section_only = diag_with(&["the modes differ (§4.12)"], 0);
    assert!(!judge(&section_only, &want("name", &[1])).is_empty());
    assert!(!judge(&section_only, &want("name", &[2])).is_empty());
    let mode = diag_with(&["write `move` before the parameter"], 0);
    assert!(judge(&mode, &want("mode", &[])).is_empty());
    assert!(judge(&diag_with(&[], 0), &want("none", &[])).is_empty());
    assert!(judge(&diag_with(&[], 1), &want("cand", &[])).is_empty());
    assert!(!judge(&diag_with(&["a note"], 1), &want("cand", &[])).is_empty(), "no note beside a candidate");
    assert!(!judge(&diag_with(&[], 1), &want("none", &[])).is_empty(), "`none` has no candidate");
}
