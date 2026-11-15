//! The notes of an E0601 (spec §8.1, §5.4, §12.2, §18.1; decisions S-783 (C1), S-613, R-83 (3), R-256, and the
//! details S-1050 and S-1052; W6-03 U6a/t), and of an anonymous function (§8.1, §10 rule 1; the detail S-1041 (2)
//! and (3), with the E0901 of an `rt` function; W6-03 U6b/i). The case files cannot pin them (the runner of the
//! cases compares the code and the line, and no note), and the spec fixes the places of the notes but not their
//! text or order.
//!
//! One package of two files is checked once (`check --json` as the command runs it, in this process, no file
//! written), and each function of it is one unit that gets one report. The Onsa text carries the expected
//! values as comments `//@ ...` at the end of its lines, as the case files do with `//~`:
//!
//! - `//@ case <name> [none] [code=E0601] [fixes=N] [others=N] [names=A,B] [g=group,...]` starts a case (the lines
//!   up to the next header). `none`: no diagnostic. `fixes`: the number of candidates of the report.
//!   `others`: at least that many notes that point at a place. `names`: the type parameters the function writes.
//! - `//@ main <text with a bar>`: the report is at the line of the marker, at the column of the bar in the
//!   first place the text (without the bar) is found in the line.
//! - `//@ note`: a note points at this line (the lines the spec decides: the drop points away from the place the
//!   value is written, the other uses of the effect, the first element of a literal). A marker is a lower bound:
//!   other notes may be there. `//@ note~`: the same for a note of a detail that has a test of its own
//!   (S-1050, decided (2): an `rt` function and an anonymous function notes the other uses too; S-1041, decided:
//!   where the row of an anonymous function comes from, at its line, and the type to write at the `let` of one). `//@ nonote`: no
//!   note points at this line (the line is no drop point of the value, or the use is of another scope or element).
//! - Markers on one line are separated by `;`.
//!
//! What the test compares (§18.1: the text and the order of a note are not fixed): the code, the place (line and
//! column) and the number of candidates of the report; the lines of the notes that point at a place (not their
//! columns: the place of the end of a scope is an empty range that the spec does not give a column); the number
//! of notes for S-1052; for R-256 that the message holds no `<digit>` and holds the names written. The
//! expectations are those of the test work (W6-03 U6a/t); the details that were open then (S-1050, S-1041) are
//! decided (2026-11-15), and the marker of such a detail is `note~`, with a test of its own.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use serde_json::Value;

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{Span, code_of, diagnostics, doc_of, fixes_of, notes_of, span_of, str_of};

const M: &str = r####"//@ case helpers none
use std.test.{check, gen}

fn helper(x: I32) -> I32 { x }

fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }

fn pass(move s: Str) -> Str { s }

fn g2(p: (Str, Str, Str, F32)) -> U32 { p.0.len() }

struct P { name: Str, v: F32, w: Str, x: Str }

struct Pair { a: Buf[F32], b: Buf[F32] }

struct W[T] { v: T }

//@ case two_points fixes=1 g=points
fn two_points(n: U32, move s: Str) -> U32 {
  let t = move s       //@ main let |t
  if n > 3 {
    return 1           //@ note
  }
  t.len()
}                      //@ note

//@ case param_exit fixes=1 g=points
fn param_exit(n: U32, move s: Str) -> U32 {   //@ main move |s
  if n > 3 {
    return 1           //@ note
  }
  s.len()
}                      //@ note

//@ case try_exit fixes=1 g=points
fn try_exit(move s: Str, r: Result[U32, U32]) -> Result[U32, U32] {
  let t = move s       //@ main let |t
  let k = r?           //@ note
  Ok(k + t.len())
}                      //@ note

//@ case loop_break fixes=1 g=points
fn loop_break(move xs: [Str; 2], c: Bool) -> U32 {
  var n: U32 = 0
  for x in move xs {   //@ main for |x
    if c {
      break            //@ note
    }
    n = n + x.len()
  }                    //@ note
  n
}

//@ case loop_local fixes=1 g=points
fn loop_local(n: U32, c: Bool) -> U32 {
  var m: U32 = 0
  while m < n {
    let t = mk(m)      //@ main let |t ; note
    m = m + 1
    if c {
      continue         //@ note
    }
    m = m + t.len()
  }                    //@ note
  m
}

//@ case one_branch fixes=1 g=points
fn one_branch(c: Bool, move s: Str) -> Str {
  let t = move s       //@ main let |t
  if c {
    return t           //@ nonote
  }
  "abc"
}                      //@ note

//@ case outer_local fixes=1 g=points
fn outer_local(c: Bool, move s: Str) -> U32 {
  let t = move s       //@ main let |t
  var m: U32 = 0
  while m < 3 {
    m = m + 1
    if c {
      continue         //@ nonote
    }
  }                    //@ nonote
  m + t.len()
}                      //@ note

//@ case temp_value fixes=1 g=quiet
fn temp_value(s: Str) -> U32 {
  pass(s).len()        //@ main |pass(
}

//@ case underscore fixes=1 g=quiet
fn underscore(move s: Str) -> U32 {
  let _ = move s       //@ main let |_
  1
}

//@ case rest_taken fixes=1 g=quiet
fn rest_taken(move p: Pair) -> Buf[F32] {
  p.a                  //@ main |p.a
}

//@ case calls_only fixes=1 g=other_fn
fn calls_only(n: U32) -> U32 {
  let x = mk(n).len()  //@ main |mk(
  x + mk(n).len()      //@ note
}

//@ case fn_other_uses fixes=1 g=other_fn others=3
fn fn_other_uses(n: U32) -> U32 {
  let a = mk(n)        //@ main let |a ; note
  let b = mk(n)        //@ note
  n
}

//@ case rt_other_uses fixes=0 g=other_rt
rt fn rt_other_uses(n: U32) -> U32 {
  let b: Buf[F32] = Buf.zeroed(n)   //@ main let |b ; note~
  let c: Buf[F32] = Buf.zeroed(n)   //@ note~
  b.len() + c.len()
}

//@ case r83_no_row fixes=1 g=other_fn others=3
fn no_row(n: U32) -> U32 {
  let a = mk(n)        //@ main let |a ; note
  let b = mk(n)        //@ note
  n
}

//@ case r83_alloc_in_rt fixes=0 g=other_rt
rt fn alloc_in_rt(n: U32) -> I32 {
  let b = mk(n)        //@ main let |b ; note~
  helper(1)
}

//@ case r83_calls_plain code=E0901 fixes=0
rt fn calls_plain() -> I32 {
  helper(1)            //@ main |helper(
}

//@ case closure_other_uses fixes=0 g=other_closure
fn closure_other_uses(n: U32) -> U32 uses {Alloc} {
  let z = mk(n)        //@ nonote
  let l = fn(y: U32) -> U32 {
    let a = mk(y)      //@ main let |a ; note~
    let b = mk(y)      //@ note~
    y
  }
  l.(n) + z.len()
}

//@ case rt_closure_other_uses fixes=0 g=other_closure
fn rt_closure_other_uses(n: U32) -> U32 uses {Alloc} {
  let l: rt fn(U32) -> U32 = fn(y: U32) -> U32 {
    let a: Buf[F32] = Buf.zeroed(y)   //@ main let |a ; note~
    let b: Buf[F32] = Buf.zeroed(y)   //@ note~
    y
  }
  l.(n)
}

//@ case lit_bound fixes=1 g=lit
fn lit_bound(s: Str, t: Str, v: F32) -> U32 {
  let p = (            //@ main let |p
    "a",               //@ nonote
    s,                 //@ note
    t,                 //@ nonote
    v
  )
  p.1.len()
}

//@ case lit_bound_rt fixes=0 g=lit
rt fn lit_bound_rt(s: Str, t: Str, v: F32) -> U32 {
  let p = (            //@ main let |p
    "a",               //@ nonote
    s,                 //@ note
    t,                 //@ nonote
    v
  )
  p.1.len()
}

//@ case lit_temp fixes=1 g=lit
fn lit_temp(s: Str, t: Str, v: F32) -> U32 {
  g2((                 //@ main g2(|(
    "a",               //@ nonote
    s,                 //@ note
    t,                 //@ nonote
    v
  ))
}

//@ case lit_struct fixes=1 g=lit
fn lit_struct(s: Str, t: Str, v: F32) -> U32 {
  let p = P {          //@ main let |p
    name: "a",         //@ nonote
    v: v,              //@ nonote
    w: s,              //@ note
    x: t               //@ nonote
  }
  p.w.len()
}

//@ case lit_nested fixes=1 g=lit
fn lit_nested(s: Str, t: Str, v: F32) -> U32 {
  let p = (            //@ main let |p
    ("a", v),          //@ nonote
    (v, s),            //@ note
    t                  //@ nonote
  )
  p.2.len()
}

//@ case lit_static none
fn lit_static(v: F32) -> U32 {
  let p = ("a", v)
  p.0.len()
}

//@ case gen_plain names=T fixes=1 g=s1052,names
fn gen_plain[T](move x: T, n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_plain_rt names=T fixes=0 g=s1052,names
rt fn gen_plain_rt[T](move x: T, n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_dup names=T fixes=1 g=s1052,names
fn gen_dup[T: ?Dup](move x: T, n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_inside names=T fixes=1 g=s1052,names
fn gen_inside[T](move x: (T, U32), n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_option names=T fixes=1 g=s1052,names
fn gen_option[T](move x: Option[T], n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_pair names=T fixes=1 g=s1052_control,names
fn gen_pair[T](move x: (T, Str), n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_pair_rt names=T fixes=0 g=s1052_control,names
rt fn gen_pair_rt[T](move x: (T, Str), n: U32) -> U32 {   //@ main move |x
  n
}

//@ case gen_copy none
fn gen_copy[T: Copy](move x: T, n: U32) -> U32 {
  n
}

//@ case names_fn fixes=1 names=T g=names
fn names_fn[T](move v: T, s: Str) -> U32 {
  let p = (s, v)       //@ main let |p
  p.0.len()
}

//@ case names_rt fixes=0 names=T g=names
rt fn names_rt[T](move v: T, s: Str) -> U32 {
  let p = (s, v)       //@ main let |p
  p.0.len()
}

//@ case names_two fixes=1 names=A,B g=names
fn names_two[A, B](move a: A, move b: B, s: Str) -> U32 {
  let p = (s, a, b)    //@ main let |p
  p.0.len()
}

//@ case names_method fixes=1 names=Item g=names
impl[Item] W[Item] {
  fn names_method(move self, n: U32) -> U32 {   //@ main move |self
    n
  }
}
//@ case s1041_helpers none
fn alloc_len(n: U32) -> U32 uses {Alloc} { mk(n).len() }

fn ap_plain(f: fn(U32) -> U32, x: U32) -> U32 { f.(x) }

fn ap_rt(f: rt fn(U32) -> U32, x: U32) -> U32 { f.(x) }

//@ case row_written fixes=0 g=s1041
fn row_written(n: U32) -> U32 uses {Alloc} {
  let l = fn(y: U32) -> U32 uses {} {   //@ note~
    let b = mk(y)                       //@ main let |b
    b.len()
  }
  l.(n)
}

//@ case row_expected fixes=0 g=s1041
fn row_expected(n: U32) -> U32 {
  ap_plain(fn(y: U32) -> U32 {          //@ note~
    let b = mk(y)                       //@ main let |b
    b.len()
  }, n)
}

//@ case row_none_expected fixes=0 g=s1041
fn row_none_expected(n: U32) -> U32 uses {Alloc} {
  let l = fn(y: U32) -> U32 {           //@ note~
    let b = mk(y)                       //@ main let |b
    b.len()
  }
  l.(n)
}

//@ case row_joining fixes=0 g=s1041
fn row_joining(c: Bool, n: U32) -> U32 uses {Alloc} {
  let j = if c { alloc_len } else {
    fn(x: U32) -> U32 {                 //@ note~
      alloc_len(x)                      //@ main |alloc_len(
    }
  }
  j.(n)
}

//@ case rt_calls_closure code=E0901 fixes=0 g=s1041_rt
rt fn rt_calls_closure(n: U32) -> U32 {
  let l = fn(y: U32) -> U32 { y }       //@ note~
  l.(n)                                 //@ main |l.(
}

//@ case rt_closure_rule1 fixes=0
fn rt_closure_rule1(n: U32) -> U32 {
  ap_rt(fn(y: U32) -> U32 {
    let b: Buf[F32] = Buf.zeroed(y)     //@ main let |b
    b.len()
  }, n)
}

//@ case rt_closure_control fixes=0
fn rt_closure_control(n: U32) -> U32 {
  ap_plain(fn(y: U32) -> U32 {
    let b: Buf[F32] = Buf.zeroed(y)     //@ main let |b
    b.len()
  }, n)
}

//@ case random_plain fixes=0 g=random
fn random_plain() {
  check(10, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })   //@ main |check(
}

//@ case random_alloc_row fixes=0 g=random
fn random_alloc_row() uses {Alloc} {
  check(10, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })   //@ main |check(
}

//@ case random_closure fixes=0 g=random
fn random_closure() -> U32 uses {Alloc} {
  let l = fn(n: U32) -> U32 {
    check(n, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })   //@ main |check(
    n
  }
  l.(1)
}

//@ case random_test_closure fixes=0 g=random
test "random in a closure of a test body" {
  let l = fn(n: U32) -> U32 {
    check(n, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })   //@ main |check(
    n
  }
  let _ = l.(1)
}

//@ case random_rt fixes=0 g=random,random_rt
rt fn random_rt() {
  check(10, gen.u32(0, 9), fn(x: U32) -> Bool { x < 10 })   //@ main |check(
}

//@ case rule1_alloc_rt fixes=0 g=rule1
rt fn rule1_alloc_rt(n: U32) -> U32 {
  let b: Buf[F32] = Buf.zeroed(n)   //@ main let |b
  b.len()
}

//@ case rule1_alloc_plain fixes=1 g=rule1
fn rule1_alloc_plain(n: U32) -> U32 {
  let b: Buf[F32] = Buf.zeroed(n)   //@ main let |b
  b.len()
}
"####;

const INNER: &str = r####"//@ case inner_helpers none
fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }

//@ case inner_points fixes=1 g=points
pub fn inner_points(n: U32, move s: Str) -> U32 {
  let t = move s       //@ main let |t
  if n > 3 {
    return 1           //@ note
  }
  t.len()
}                      //@ note

//@ case inner_other_uses fixes=1 g=other_fn
pub fn inner_other_uses(n: U32) -> U32 {
  let a = mk(n)        //@ main let |a ; note
  let b = mk(n)        //@ note
  n
}
"####;

// ------------------------------------------------------------------------------------------------ the cases

#[derive(Default)]
struct Case {
    file: &'static str,
    name: String,
    /// The lines of the case, from its header to the line before the next one (from 1).
    first: usize,
    last: usize,
    code: String,
    fixes: Option<usize>,
    none: bool,
    groups: Vec<String>,
    names: Vec<String>,
    others: usize,
    main: Option<(usize, usize)>,
    note: Vec<usize>,
    detail: Vec<usize>,
    nonote: Vec<usize>,
}

fn parse(file: &'static str, text: &str, cases: &mut Vec<Case>) {
    assert!(text.is_ascii(), "{file}: columns are counted by bytes");
    let mut cur: Option<Case> = None;
    let total = text.lines().count();
    for (i, line) in text.lines().enumerate() {
        let no = i + 1;
        if let Some(rest) = line.strip_prefix("//@ case ") {
            if let Some(mut c) = cur.take() {
                c.last = no - 1;
                cases.push(c);
            }
            let mut words = rest.split_whitespace();
            let mut c = Case { file, name: words.next().expect("a name").to_string(), first: no, ..Case::default() };
            c.code = "E0601".to_string();
            for w in words {
                let list = |v: &str| v.split(',').map(str::to_string).collect::<Vec<_>>();
                match w.split_once('=') {
                    None if w == "none" => c.none = true,
                    Some(("code", v)) => c.code = v.to_string(),
                    Some(("fixes", v)) => c.fixes = Some(v.parse().expect("a number")),
                    Some(("others", v)) => c.others = v.parse().expect("a number"),
                    Some(("names", v)) => c.names = list(v),
                    Some(("g", v)) => c.groups = list(v),
                    _ => panic!("{file}:{no}: the word {w:?} of a header is not known"),
                }
            }
            cur = Some(c);
            continue;
        }
        let Some(at) = line.find("//@ ") else { continue };
        let c = cur.as_mut().unwrap_or_else(|| panic!("{file}:{no}: a marker before the first case"));
        let code = &line[..at];
        for m in line[at + 4..].split(';').map(str::trim) {
            if let Some(w) = m.strip_prefix("main ") {
                let bar = w.find('|').unwrap_or_else(|| panic!("{file}:{no}: no bar in {m:?}"));
                let pat = w.replace('|', "");
                let idx = code.find(&pat).unwrap_or_else(|| panic!("{file}:{no}: {pat:?} is not in the line"));
                c.main = Some((no, idx + bar + 1));
            } else {
                match m {
                    "note" => c.note.push(no),
                    "note~" => c.detail.push(no),
                    "nonote" => c.nonote.push(no),
                    _ => panic!("{file}:{no}: the marker {m:?} is not known"),
                }
            }
        }
    }
    let mut c = cur.expect("a case");
    c.last = total;
    cases.push(c);
}

struct Run {
    cases: Vec<Case>,
    diags: Vec<Value>,
}

/// The package checked once: the cases and the diagnostics.
fn run() -> &'static Run {
    static RUN: OnceLock<Run> = OnceLock::new();
    RUN.get_or_init(|| {
        let mut cases = Vec::new();
        parse("m.onsa", M, &mut cases);
        parse("inner.onsa", INNER, &mut cases);
        let texts: Texts = [("m.onsa", M), ("inner.onsa", INNER)].map(|(f, t)| (f.to_string(), t.to_string())).into();
        let out = check_input_out(&input_of("demo", &texts));
        assert!(out.code == 0 || out.code == 1, "the check ended with {}: {}", out.code, out.stderr);
        let diags = diagnostics(&doc_of(&out)).clone();
        Run { cases, diags }
    })
}

fn case<'a>(r: &'a Run, name: &str) -> &'a Case {
    r.cases.iter().find(|c| c.name == name).unwrap_or_else(|| panic!("no case {name}"))
}

/// The cases of a group, which must not be empty (a group that selects nothing would pass).
fn group<'a>(r: &'a Run, g: &str, at_least: usize) -> Vec<&'a Case> {
    let v: Vec<&Case> = r.cases.iter().filter(|c| c.groups.iter().any(|x| x == g)).collect();
    assert!(v.len() >= at_least, "the group {g} has {} cases, not {at_least}", v.len());
    v
}

/// The diagnostics inside the lines of a case.
fn found<'a>(r: &'a Run, c: &Case) -> Vec<&'a Value> {
    let inside = |s: &Span| s.file == c.file && (c.first..=c.last).contains(&(s.line as usize));
    r.diags.iter().filter(|d| inside(&span_of(&d["span"]))).collect()
}

fn the_diag<'a>(r: &'a Run, c: &Case) -> &'a Value {
    let v = found(r, c);
    assert_eq!(v.len(), 1, "{}: one report for the function: {v:?}", c.name);
    v[0]
}

/// The places the notes of a diagnostic point at.
fn note_spans(d: &Value) -> Vec<Span> {
    notes_of(d).iter().filter_map(|n| n.get("span").map(span_of)).collect()
}

fn describe(d: &Value) -> String {
    let notes: Vec<String> = notes_of(d)
        .iter()
        .map(|n| {
            let at = n.get("span").map(span_of).map(|s| format!("{}:{}", s.line, s.col)).unwrap_or_default();
            format!("[{at}] {}", str_of(n, "message"))
        })
        .collect();
    format!("{} {}\n  notes: {notes:#?}", code_of(d), str_of(d, "message"))
}

/// The lines of `c` that a note points at (in its file).
fn noted_lines(c: &Case, d: &Value) -> BTreeSet<usize> {
    note_spans(d).iter().filter(|s| s.file == c.file).map(|s| s.line as usize).collect()
}

/// The lines in `want` must all have a note, and no line of `nowhere` may: the faults, one text each.
fn lines_noted(c: &Case, d: &Value, want: &[usize], nowhere: &[usize]) -> Vec<String> {
    let have = noted_lines(c, d);
    let mut faults = Vec::new();
    for l in want.iter().filter(|l| !have.contains(l)) {
        faults.push(format!("{}: no note points at line {l} (the lines noted: {have:?})\n{}", c.name, describe(d)));
    }
    for l in nowhere.iter().filter(|l| have.contains(l)) {
        faults.push(format!("{}: a note points at line {l}, which it must not\n{}", c.name, describe(d)));
    }
    faults
}

/// The test fails with all the faults of its cases, so that one run shows what is missing.
fn none_of(faults: Vec<String>) {
    assert!(faults.is_empty(), "{} faults:\n{}", faults.len(), faults.join("\n"));
}

// ----------------------------------------------------------------------------------------------- the tests

#[test]
fn each_function_gets_one_report_at_the_place_its_rule_gives() {
    // What the unit does not change: the code, the place and the number of candidates (§8.1: the place is
    // where the value is written; `rt` and an anonymous function get no candidate). Also a control of the
    // cases: a function with `none` gets no report, so a case of the other tests that were written wrong
    // does not pass by having no diagnostic.
    let r = run();
    assert!(r.cases.len() >= 40, "{} cases", r.cases.len());
    let mut reports = 0;
    for c in &r.cases {
        let v = found(r, c);
        if c.none {
            assert!(v.is_empty(), "{}: no report expected: {v:?}", c.name);
            continue;
        }
        let d = the_diag(r, c);
        reports += 1;
        assert_eq!(code_of(d), c.code, "{}: {}", c.name, describe(d));
        let (line, col) = c.main.unwrap_or_else(|| panic!("{}: no `main` marker", c.name));
        let s = span_of(&d["span"]);
        assert_eq!((s.line as usize, s.col as usize), (line, col), "{}: {}", c.name, describe(d));
        if let Some(n) = c.fixes {
            assert_eq!(fixes_of(d).len(), n, "{}: the number of candidates: {}", c.name, describe(d));
        }
        // The report does not note its own place (the use that it is at is not an "other" one).
        if c.code == "E0601" {
            let own = note_spans(d).into_iter().find(|n| (n.line, n.col) == (s.line, s.col));
            assert!(own.is_none(), "{}: a note at the place of the report: {}", c.name, describe(d));
        }
    }
    assert!(reports >= 34, "{reports} reports compared");
}

#[test]
fn the_notes_of_a_function_lie_in_the_function() {
    // §8.1: the notes of an E0601 show uses, points and elements of the same body.
    let r = run();
    let mut seen = 0;
    for c in r.cases.iter().filter(|c| !c.none && c.code == "E0601") {
        for s in note_spans(the_diag(r, c)) {
            assert!(
                s.file == c.file && (c.first..=c.last).contains(&(s.line as usize)),
                "{}: a note points outside the function: {s:?}",
                c.name
            );
            seen += 1;
        }
    }
    assert!(seen >= 5, "{seen} notes seen");
}

#[test]
fn a_drop_point_away_from_where_the_value_is_written_is_noted_at_its_line() {
    // S-783 C1, §8.1: "書いた所と別の所で破棄される値は、破棄の点を位置付きの note で示す". A value that is
    // dropped at the end of its scope, or at an early exit (`return`, `?`, `break`, `continue`), has a note at
    // each such point, once for the value however many points it has (the report is one). A point where the
    // value is moved on, a `continue` that does not leave its scope, and the end of a loop that the value
    // is declared outside of, are no drop points, and nothing is noted there.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "points", 8) {
        assert!(!c.note.is_empty() || !c.nonote.is_empty(), "{}: a case of this group has marked lines", c.name);
        faults.extend(lines_noted(c, the_diag(r, c), &c.note, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn a_value_dropped_where_it_is_written_has_no_note_of_a_point() {
    // S-783: a temporary value, what `_` binds and the rest of a value taken out are dropped in the place
    // they are written (the statement ends there), so there is no other place to show. The functions have no
    // other use of `Alloc` and are not `rt`, so no note points at a place.
    let r = run();
    for c in group(r, "quiet", 3) {
        let d = the_diag(r, c);
        assert!(note_spans(d).is_empty(), "{}: no note at a place expected: {}", c.name, describe(d));
    }
}

#[test]
fn a_function_without_rt_notes_the_other_uses_of_the_effect() {
    // §8.1, R-83 (3): the report is the first use, and the other uses of `Alloc` of the function (a call, a
    // drop, each use once) are noted at their places. The place of the report is not one of them.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "other_fn", 4) {
        let d = the_diag(r, c);
        faults.extend(lines_noted(c, d, &c.note, &c.nonote));
        let n = note_spans(d).len();
        if n < c.others {
            faults.push(format!("{}: {n} notes at a place, at least {} expected\n{}", c.name, c.others, describe(d)));
        }
    }
    none_of(faults);
}

#[test]
fn an_rt_function_notes_the_other_uses_of_the_effect_too() {
    // S-1050 (decided (2)): the same other uses as for a function without `rt`, besides the note of
    // the rule 1 of §10 (which points at the name of the function, not at one of these lines).
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "other_rt", 2) {
        faults.extend(lines_noted(c, the_diag(r, c), &c.detail, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn an_anonymous_function_notes_the_other_uses_of_its_own_scope_alone() {
    // R-83 (3) for the scopes of the bodies and the anonymous functions (§8.1: the uses of the body of an
    // anonymous function are not counted in the function around it): the uses of the anonymous function
    // (and of an `rt` one) are noted, and the use of the function around (`z`, which its row `Alloc` gives)
    // is not. The spec says it of the function without `rt` (R-83 (3)) and of the `rt` function (S-1050,
    // decided (2): the `rt` function and the anonymous function note them too), so the same reading is used.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "other_closure", 2) {
        faults.extend(lines_noted(c, the_diag(r, c), &c.detail, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn the_first_element_that_makes_a_literal_owned_is_named() {
    // S-613, §8.1: the E0601 of an aggregate literal that is dropped notes the first element that makes it
    // owned (the first that cannot be an element of a literal that needs no drop: here the borrowed `Str`
    // `s`, not the static `"a"`, the Copy `v`, or the second `Str` `t`). It is the literal a binding is
    // initialized with, the temporary one, a struct literal, and the inner literal of a nested one; in an
    // `rt` function too. The candidate of the report stays (`uses {Alloc}`): the note has none.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "lit", 5) {
        faults.extend(lines_noted(c, the_diag(r, c), &c.note, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn a_type_parameter_that_copy_would_free_from_allocating_is_noted() {
    // S-1052 (decided (2)), §12.2: the drop of a `T` (no bound, or `?Dup`), of a `(T, U32)` and of
    // an `Option[T]` needs `Alloc` only because `T` may need it, so a note shows that `[T: Copy]` fixes it. A
    // `(T, Str)` needs `Alloc` for the `Str` whatever `T` is, so it has no such note. Each form differs from the
    // control of its kind (`gen_pair` for a function, `gen_pair_rt` for an `rt` one) in the type of `x` alone,
    // so the other notes (the drop point at the end of the body, S-783 C1; the rule 1 of §10) are the same, and
    // the form has one note more than its control.
    let r = run();
    let notes = |name: &str| notes_of(the_diag(r, case(r, name))).len();
    let mut faults = Vec::new();
    let mut expect = |name: &str, control: &str, what: &str| {
        let (n, c) = (notes(name), notes(control));
        if n != c + 1 {
            faults.push(format!(
                "{name} ({what}): {n} notes, one more than the {c} of {control} expected\n{}",
                describe(the_diag(r, case(r, name)))
            ));
        }
    };
    for name in ["gen_plain", "gen_dup", "gen_inside", "gen_option"] {
        expect(name, "gen_pair", "the note of `[T: Copy]`");
    }
    expect("gen_plain_rt", "gen_pair_rt", "`T` in an `rt` function: the note of `[T: Copy]`");
    group(r, "s1052", 5);
    none_of(faults);
}

#[test]
fn a_type_parameter_is_shown_by_the_name_it_is_written_with() {
    // R-256: the message of a drop shows `(Str, T)` for the type written `(Str, T)`, not `(Str, <0>)`. The
    // names are those the function (or the `impl` of a method) writes, in a `fn`, an `rt fn`, two parameters
    // and a method, and in the messages of S-1052. The text is not fixed, so: no `<digit>`, and each name as a
    // word of its own.
    let r = run();
    let word = |msg: &str, w: &str| {
        let bytes = msg.as_bytes();
        msg.match_indices(w).any(|(i, _)| {
            let ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
            (i == 0 || !ident(bytes[i - 1])) && bytes.get(i + w.len()).is_none_or(|b| !ident(*b))
        })
    };
    let mut faults = Vec::new();
    for c in group(r, "names", 4 + 7) {
        let msg = str_of(the_diag(r, c), "message");
        let numbered = msg.match_indices('<').any(|(i, _)| msg.as_bytes().get(i + 1).is_some_and(u8::is_ascii_digit));
        if numbered {
            faults.push(format!("{}: a numbered type parameter in {msg:?}", c.name));
        }
        for n in c.names.iter().filter(|n| !word(msg, n)) {
            faults.push(format!("{}: the name {n} is not in {msg:?}", c.name));
        }
    }
    none_of(faults);
}

#[test]
fn an_anonymous_function_notes_where_its_row_comes_from() {
    // §8.1 ("修正候補は無く、note で効果行の決まり方を示す") and S-1041 (2) (decided: no candidate, the text is
    // not fixed): the row an anonymous function writes (`uses {}` too), that of the function type expected where
    // it is, none where none is expected (an unannotated `let`), and none in a later branch of a merge (§4.7).
    // Each has a note at the line of the anonymous function.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "s1041", 4) {
        faults.extend(lines_noted(c, the_diag(r, c), &c.detail, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn an_rt_function_that_calls_an_anonymous_function_with_no_type_notes_the_type_to_write() {
    // §10 ("`rt` の関数の中で `rt` でない無名関数を呼ぶと E0901 で、`rt fn` の型の注釈を書く") and S-1041 (3): the
    // E0901 of the call of a local that an unannotated `let` binds to an anonymous function has a note at the
    // `let`.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "s1041_rt", 1) {
        faults.extend(lines_noted(c, the_diag(r, c), &c.detail, &c.nonote));
    }
    none_of(faults);
}

#[test]
fn an_rt_anonymous_function_notes_the_rule_1_of_rt() {
    // §10 rule 1, as of an `rt` function: an anonymous function that is `rt` by the type expected cannot have
    // `Alloc`. The control differs in the type expected alone (`fn` for `rt fn`), so its other notes (where the
    // row comes from, the drop point, the other use) are the same, and the `rt` one has one note more.
    let r = run();
    let notes = |name: &str| notes_of(the_diag(r, case(r, name))).len();
    let (n, c) = (notes("rt_closure_rule1"), notes("rt_closure_control"));
    assert_eq!(n, c + 1, "one note more than the control\n{}", describe(the_diag(r, case(r, "rt_closure_rule1"))));
}

#[test]
fn a_random_report_has_a_note_and_no_candidate() {
    // S-97, D-08, §8.1 and §11.8: `check` uses `Random`, which only the body of a `test` is given in this version
    // (`uses {Random}` is an E0200, S-74), so the E0601 of a use of `Random` has no candidate (an insert would
    // be an E0200 in the function) and has a note that says where `Random` is given. The text is not fixed
    // (§18.1), so: a note at least (one that has no place counts), and no candidate. The functions: a function
    // with no row, with a row of `Alloc`, an anonymous function in a function and in a `test` body, and an
    // `rt` function.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "random", 5) {
        let d = the_diag(r, c);
        if notes_of(d).is_empty() {
            faults.push(format!("{}: no note: {}", c.name, describe(d)));
        }
        if !fixes_of(d).is_empty() {
            faults.push(format!("{}: a candidate for a use of `Random`: {}", c.name, describe(d)));
        }
    }
    none_of(faults);
}

#[test]
fn the_random_report_of_an_rt_function_has_no_note_of_rule_1_of_rt() {
    // §10 rule 1 is about `Alloc` ("効果行に `Alloc` を含まない（E0902）。したがって ... 効果行に無い効果の使用として
    // E0601 になる"), so the E0601 of an `rt` function that uses `Alloc` has a note of the rule more than the same
    // function without `rt` (`rule1_alloc_rt` and `rule1_alloc_plain`, which differ in `rt` alone). The
    // E0601 of a use of `Random` is not about `Alloc`: the `rt` function and the function without `rt` have the same
    // notes (`random_rt` and `random_plain`). The text is not fixed (§18.1), so the notes are counted, as the test of
    // an `rt` anonymous function does.
    let r = run();
    let notes = |name: &str| notes_of(the_diag(r, case(r, name))).len();
    let (rt_alloc, plain_alloc) = (notes("rule1_alloc_rt"), notes("rule1_alloc_plain"));
    assert_eq!(
        rt_alloc,
        plain_alloc + 1,
        "the control: the note of the rule 1 of `rt`\n{}",
        describe(the_diag(r, case(r, "rule1_alloc_rt")))
    );
    group(r, "random_rt", 1);
    let (rt_random, plain_random) = (notes("random_rt"), notes("random_plain"));
    assert_eq!(
        rt_random,
        plain_random,
        "the `Random` of an `rt` function has no note of the rule 1\n{}",
        describe(the_diag(r, case(r, "random_rt")))
    );
}
