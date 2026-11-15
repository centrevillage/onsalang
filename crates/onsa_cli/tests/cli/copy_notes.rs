//! The notes of an E0601 whose value was copied where it could not be moved (spec §5.2, §5.4, §8.1, §12.2, §18.1;
//! decisions S-1035 (2), S-1030, S-783; W6-04 U3/t). An owned `Dup` value (a `Str`, an `Option[Str]`, an
//! `Array[Str]`) that is put in a consuming position is copied, not moved, when the position is not its last use
//! (a later use, a read in another argument of the same call, the next iteration of a loop) or when the binding
//! is a borrow (the arm of `match o`, the element of `for s in xs`). The owner is then dropped at the end of its
//! scope and the drop needs `Alloc`, so the E0601 shows the place of the copy (S-1035 (2): "複製した位置と
//! 理由"). The case files cannot pin it (the runner of the cases compares the code and the line, and no note),
//! and the spec fixes the places of the notes but not their text or order (§18.1).
//!
//! One package of one file is checked once (`check --json` as the command runs it, in this process, no file
//! written), and each function of it is one unit that gets one report. The Onsa text carries the expected
//! values as comments `//@ ...` at the end of its lines (as `effect_notes.rs` does):
//!
//! - `//@ case <name> [none] [code=E0601] [fixes=N] [ctl=<name>] [g=group,...]` starts a case (the lines up to the
//!   next header). `none`: no diagnostic. `fixes`: the number of candidates of the report. `ctl`: the case of
//!   the same drop without the copy (the notes of a case that copies are more than those of its control).
//! - `//@ main <text with a bar>`: the report is at the line of the marker, at the column of the bar in the
//!   first place the text (without the bar) is found in the line.
//! - `//@ note`: a note points at this line, the place of the copy. A marker is a lower bound (other notes
//!   may be there). `//@ nonote`: no note points at this line (the consumption there is a move).
//!
//! What the test compares (§18.1: the text and the order of a note are not fixed): the code, the place (line and
//! column) and the number of candidates of the report; the lines the notes point at (not their columns); and,
//! for the forms the decision names, that the report has at least one note more than the control that drops
//! the same value without the copy.
//!
//! What it does not compare: the line of the note that shows `match move o` (`for s in move xs`) (S-1035 does
//! not fix whether it points at the heading or at the copy), the line of the later use that is the reason, and
//! the notes of a value that is copied more than once.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use serde_json::Value;

use crate::test_support::sweep::{Texts, check_input_out, input_of};
use crate::test_support::{Span, code_of, diagnostics, doc_of, fixes_of, notes_of, span_of, str_of};

const M: &str = r####"//@ case helpers none
enum W { A(Str), B }

fn pass(move s: Str) -> Str { s }

rt fn rpass(move s: Str) -> Str { s }

fn passo(move o: Option[Str]) -> Option[Str] { o }

fn pair(move s: Str, n: U32) -> W { W.A(s) }

rt fn rpair(move s: Str, n: U32) -> W { W.A(s) }

fn pair_r(n: U32, move s: Str) -> W { W.A(s) }

rt fn rpair_r(n: U32, move s: Str) -> W { W.A(s) }

// The two callees that consume a `Str` and return a `U32`: a `Str` that is taken and dropped needs `Alloc`
// where it is dropped, so each is an E0601 of its own (no note of a copy: its `s` is a `move` parameter).

//@ case sink fixes=1 g=callee
fn sink(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

//@ case rsink fixes=0 g=callee
rt fn rsink(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

// The controls: the same drop with no copy (the value is read and never put in a consuming position).

//@ case ctl_fn fixes=1 g=control
fn ctl_fn(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

//@ case ctl_rt fixes=0 g=control
rt fn ctl_rt(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

// A later use: the consumption is not the last use of `s`, so the argument is copied and `s` is dropped at the
// end of the function (s.5.2, S-1030).

//@ case later_fn fixes=1 ctl=ctl_fn g=copied,later
fn later_fn(move s: Str) -> U32 {   //@ main move |s
  let n = sink(s)                   //@ note
  n + s.len()
}

//@ case later_rt fixes=0 ctl=ctl_rt g=copied,later
rt fn later_rt(move s: Str) -> U32 {   //@ main move |s
  let n = rsink(s)                     //@ note
  n + s.len()
}

//@ case later_let fixes=1 ctl=ctl_fn g=copied,later
fn later_let(a: Str) -> U32 {
  let s = pass(a)                   //@ main let |s
  let n = sink(s)                   //@ note
  n + s.len()
}

//@ case later_let_rt fixes=0 ctl=ctl_rt g=copied,later
rt fn later_let_rt(a: Str) -> U32 {
  let s = rpass(a)                  //@ main let |s
  let n = rsink(s)                  //@ note
  n + s.len()
}

//@ case later_lit fixes=1 ctl=ctl_fn g=copied,later
fn later_lit(move s: Str) -> (W, U32) {   //@ main move |s
  (W.A(s), s.len())                       //@ note
}

//@ case later_lit_rt fixes=0 ctl=ctl_rt g=copied,later
rt fn later_lit_rt(move s: Str) -> (W, U32) {   //@ main move |s
  (W.A(s), s.len())                             //@ note
}

//@ case later_branch fixes=1 ctl=ctl_fn g=copied,later
fn later_branch(move s: Str, c: Bool) -> U32 {   //@ main move |s
  let n = if c { sink(s) } else { 0 }            //@ note
  n + s.len()
}

// The same call: `s` is the argument that consumes, and `s.len()` of the later argument reads it, so the
// consumption cannot take a `move` (s.5.2, E0704 as of `take2(move b, b.len())`) and is a copy. Where the read
// is in the earlier argument (`pair_r(s.len(), s)`) the `move` can be put (`take2r(b.len(), move b)`), so
// `s` is moved and there is no report at all.

//@ case same_call_fn fixes=1 ctl=ctl_fn g=copied,call
fn same_call_fn(move s: Str) -> W {   //@ main move |s
  pair(s, s.len())                    //@ note
}

//@ case same_call_rt fixes=0 ctl=ctl_rt g=copied,call
rt fn same_call_rt(move s: Str) -> W {   //@ main move |s
  rpair(s, s.len())                      //@ note
}

//@ case same_call_after_fn none g=quiet
fn same_call_after_fn(move s: Str) -> W {
  pair_r(s.len(), s)
}

//@ case same_call_after_rt none g=quiet
rt fn same_call_after_rt(move s: Str) -> W {
  rpair_r(s.len(), s)
}

// A loop: the next iteration uses `s` again (E0704 of a `move` there), so the consumption in the body is a copy.

//@ case loop_fn fixes=1 ctl=ctl_fn g=copied,loop
fn loop_fn(move s: Str, n: U32) -> U32 {   //@ main move |s
  var k: U32 = 0
  var total: U32 = 0
  while k < n {
    total = total + sink(s)                //@ note
    k = k + 1
  }
  total
}

//@ case loop_rt fixes=0 ctl=ctl_rt g=copied,loop
rt fn loop_rt(move s: Str, n: U32) -> U32 {   //@ main move |s
  var k: U32 = 0
  var total: U32 = 0
  while k < n {
    total = total + rsink(s)                  //@ note
    k = k + 1
  }
  total
}

//@ case loop_for fixes=1 ctl=ctl_fn g=copied,loop
fn loop_for(move s: Str, n: U32) -> U32 {   //@ main move |s
  var total: U32 = 0
  for i in 0 ..< n {
    total = total + sink(s)                 //@ note
  }
  total
}

//@ case loop_for_rt fixes=0 ctl=ctl_rt g=copied,loop
rt fn loop_for_rt(move s: Str, n: U32) -> U32 {   //@ main move |s
  var total: U32 = 0
  for i in 0 ..< n {
    total = total + rsink(s)                      //@ note
  }
  total
}

// A borrowed heading: the binding of an arm of `match o` and of `for s in xs` is a borrow (s.5.4), so the
// consumption of `s` is a copy whatever comes after it, and the owner `o` (`xs`) is dropped.

//@ case match_ctor_fn fixes=1 ctl=ctl_fn g=copied,heading
fn match_ctor_fn(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => W.A(s),                         //@ note
    None => W.B
  }
}

//@ case match_ctor_rt fixes=0 ctl=ctl_rt g=copied,heading
rt fn match_ctor_rt(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => W.A(s),                            //@ note
    None => W.B
  }
}

//@ case match_sink_fn fixes=1 ctl=ctl_fn g=copied,heading
fn match_sink_fn(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) => sink(s),                          //@ note
    None => 0
  }
}

//@ case match_sink_rt fixes=0 ctl=ctl_rt g=copied,heading
rt fn match_sink_rt(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) => rsink(s),                            //@ note
    None => 0
  }
}

//@ case match_let fixes=1 ctl=ctl_fn g=copied,heading
fn match_let(a: Option[Str]) -> W {
  let o = passo(a)                             //@ main let |o
  match o {
    Some(s) => W.A(s),                         //@ note
    None => W.B
  }
}

//@ case for_heading_fn fixes=1 ctl=ctl_fn g=copied,heading
fn for_heading_fn(move xs: Array[Str]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in xs {
    t = t + sink(s)                               //@ note
  }
  t
}

//@ case for_heading_rt fixes=0 ctl=ctl_rt g=copied,heading
rt fn for_heading_rt(move xs: Array[Str]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in xs {
    t = t + rsink(s)                                 //@ note
  }
  t
}

// What is no copy. A consumption that is the last use is a move: the report of the function is for another
// value, or there is none.

//@ case last_use_fn none g=quiet
fn last_use_fn(move s: Str) -> U32 {
  sink(s)
}

//@ case last_use_rt none g=quiet
rt fn last_use_rt(move s: Str) -> U32 {
  rsink(s)
}

//@ case read_then_move none g=quiet
fn read_then_move(move s: Str) -> U32 {
  let n = s.len()
  n + sink(s)
}

//@ case mixed_fn fixes=1 g=moved
fn mixed_fn(move s: Str, move t: Str) -> U32 {   //@ main move |t
  let a = sink(s)                                //@ nonote
  a + t.len()
}

//@ case mixed_rt fixes=0 g=moved
rt fn mixed_rt(move s: Str, move t: Str) -> U32 {   //@ main move |t
  let a = rsink(s)                                  //@ nonote
  a + t.len()
}

// `return` leaves the loop, so the consumption is the last use on its path (a move); `s` is still dropped on
// the path that falls through.

//@ case loop_return_fn fixes=1 g=moved
fn loop_return_fn(move s: Str, n: U32) -> U32 {   //@ main move |s
  var k: U32 = 0
  while k < n {
    if k == 3 {
      return sink(s)                              //@ nonote
    }
    k = k + 1
  }
  0
}

//@ case loop_return_rt fixes=0 g=moved
rt fn loop_return_rt(move s: Str, n: U32) -> U32 {   //@ main move |s
  var k: U32 = 0
  while k < n {
    if k == 3 {
      return rsink(s)                                //@ nonote
    }
    k = k + 1
  }
  0
}

// A function with `Alloc` in its row has no report.

//@ case later_alloc none g=quiet
fn later_alloc(move s: Str) -> U32 uses {Alloc} {
  let n = sink(s)
  n + s.len()
}

// An owned heading (`match move o`, `for s in move xs`): the arm binding is owned and its last use is a move.
// `match move o` has nothing left to drop. `for s in move xs` drops the container when it is left (s.5.4), so it
// has a report at `xs` (S-1058: after the `move`) and no copy.

//@ case match_move_fn none g=quiet
fn match_move_fn(move o: Option[Str]) -> U32 {
  match move o {
    Some(s) => sink(s),
    None => 0
  }
}

//@ case match_move_rt none g=quiet
rt fn match_move_rt(move o: Option[Str]) -> U32 {
  match move o {
    Some(s) => rsink(s),
    None => 0
  }
}

//@ case for_move_fn fixes=1 g=moved
fn for_move_fn(move xs: Array[Str]) -> U32 {
  var t: U32 = 0
  for s in move xs {   //@ main move |xs
    t = t + sink(s)    //@ nonote
  }
  t
}

//@ case for_move_rt fixes=0 g=moved
rt fn for_move_rt(move xs: Array[Str]) -> U32 {
  var t: U32 = 0
  for s in move xs {   //@ main move |xs
    t = t + rsink(s)   //@ nonote
  }
  t
}

// A borrowed owner: a copy of a borrow has no owner to drop, so no report.

//@ case match_param none g=quiet
fn match_param(o: Option[Str]) -> U32 {
  match o {
    Some(s) => sink(s),
    None => 0
  }
}

//@ case for_param none g=quiet
fn for_param(xs: Array[Str]) -> U32 {
  var t: U32 = 0
  for s in xs {
    t = t + sink(s)
  }
  t
}
"####;

// ------------------------------------------------------------------------------------------------ the cases

#[derive(Default)]
struct Case {
    name: String,
    /// The lines of the case, from its header to the line before the next one (from 1).
    first: usize,
    last: usize,
    code: String,
    fixes: Option<usize>,
    none: bool,
    control: Option<String>,
    groups: Vec<String>,
    main: Option<(usize, usize)>,
    note: Vec<usize>,
    nonote: Vec<usize>,
}

const FILE: &str = "m.onsa";

fn parse(text: &str) -> Vec<Case> {
    assert!(text.is_ascii(), "columns are counted by bytes");
    let mut cases = Vec::new();
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
            let mut c = Case { name: words.next().expect("a name").to_string(), first: no, ..Case::default() };
            c.code = "E0601".to_string();
            for w in words {
                match w.split_once('=') {
                    None if w == "none" => c.none = true,
                    Some(("code", v)) => c.code = v.to_string(),
                    Some(("fixes", v)) => c.fixes = Some(v.parse().expect("a number")),
                    Some(("ctl", v)) => c.control = Some(v.to_string()),
                    Some(("g", v)) => c.groups = v.split(',').map(str::to_string).collect(),
                    _ => panic!("{no}: the word {w:?} of a header is not known"),
                }
            }
            cur = Some(c);
            continue;
        }
        let Some(at) = line.find("//@ ") else { continue };
        let c = cur.as_mut().unwrap_or_else(|| panic!("{no}: a marker before the first case"));
        let code = &line[..at];
        for m in line[at + 4..].split(';').map(str::trim) {
            if let Some(w) = m.strip_prefix("main ") {
                let bar = w.find('|').unwrap_or_else(|| panic!("{no}: no bar in {m:?}"));
                let pat = w.replace('|', "");
                let idx = code.find(&pat).unwrap_or_else(|| panic!("{no}: {pat:?} is not in the line"));
                c.main = Some((no, idx + bar + 1));
            } else {
                match m {
                    "note" => c.note.push(no),
                    "nonote" => c.nonote.push(no),
                    _ => panic!("{no}: the marker {m:?} is not known"),
                }
            }
        }
    }
    let mut c = cur.expect("a case");
    c.last = total;
    cases.push(c);
    cases
}

struct Run {
    cases: Vec<Case>,
    diags: Vec<Value>,
}

/// The package checked once: the cases and the diagnostics.
fn run() -> &'static Run {
    static RUN: OnceLock<Run> = OnceLock::new();
    RUN.get_or_init(|| {
        let cases = parse(M);
        let texts: Texts = [(FILE.to_string(), M.to_string())].into();
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
    let inside = |s: &Span| s.file == FILE && (c.first..=c.last).contains(&(s.line as usize));
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

/// The lines of the file that a note points at.
fn noted_lines(d: &Value) -> BTreeSet<usize> {
    note_spans(d).iter().filter(|s| s.file == FILE).map(|s| s.line as usize).collect()
}

/// The lines in `want` must all have a note, and no line of `nowhere` may: the faults, one text each.
fn lines_noted(c: &Case, d: &Value, want: &[usize], nowhere: &[usize]) -> Vec<String> {
    let have = noted_lines(d);
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
    // What the unit does not change: the code, the place and the number of candidates (§8.1: the place is where
    // the owned value is written, a parameter or the name of a `let`, or the source of a `for` that consumes;
    // an `rt` function gets no candidate; S-1035 (2) adds no candidate). Also a control of the cases: a function
    // with `none` gets no report, so a case of the other tests that was written wrong does not pass by having
    // no diagnostic.
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
    }
    assert!(reports >= 30, "{reports} reports compared");
}

#[test]
fn a_consumption_that_was_copied_is_noted_at_its_line() {
    // S-1035 (2), S-1030: the drop of an owned `Dup` value that the report is about needs `Alloc` because a
    // consumption of it was copied, and the report notes where: the argument that is read later (`sink(s)` and
    // then `s.len()`), the literal and the constructor (`(W.A(s), s.len())`), the argument whose call reads it in
    // a later argument (`pair(s, s.len())`), the body of a loop that the next iteration uses `s` in, and the arm
    // and the body of a borrowed heading (`match o { Some(s) => W.A(s) }`, `for s in xs`). In an `rt` function
    // the same report has the same note. The note points at the line of the copy (a lower bound: the notes of
    // the drop point and of the rule 1 of §10 stay).
    let r = run();
    let mut faults = Vec::new();
    for g in ["later", "call", "loop", "heading"] {
        for c in group(r, g, 2) {
            assert!(!c.note.is_empty(), "{}: a case of this group has a marked line", c.name);
            faults.extend(lines_noted(c, the_diag(r, c), &c.note, &c.nonote));
        }
    }
    assert_eq!(group(r, "copied", 20).len(), r.cases.iter().filter(|c| !c.note.is_empty()).count());
    none_of(faults);
}

#[test]
fn a_copy_adds_a_note_to_the_report_of_the_same_drop_without_it() {
    // The control of each case drops the same kind of owner without any consumption of `s`, so its notes are the
    // drop point (and, in an `rt` function, the rule 1 of §10). A copy has at least one note more (the place of
    // the copy; the text is not fixed). This also holds where the note may be two (the heading forms: the copy
    // and `match move o`): the count is a lower bound of one.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "copied", 20) {
        let ctl = c.control.as_deref().unwrap_or_else(|| panic!("{}: no `ctl=`", c.name));
        let (n, base) = (notes_of(the_diag(r, c)).len(), notes_of(the_diag(r, case(r, ctl))).len());
        if n < base + 1 {
            faults.push(format!("{}: {n} notes, at least {} (one more than {ctl}) expected", c.name, base + 1));
        }
    }
    none_of(faults);
}

#[test]
fn a_consumption_that_is_moved_has_no_note_of_a_copy() {
    // S-1030 (definition X): a consumption that can take a `move` (the last use, with `return` leaving a loop
    // too) moves the value, so a report of the same function that is about another value (`mixed_*`), about the
    // path that falls through (`loop_return_*`) or about the container of an owned `for` (`for_move_*`) has no
    // note at that line.
    let r = run();
    let mut faults = Vec::new();
    for c in group(r, "moved", 6) {
        assert!(!c.nonote.is_empty(), "{}: a case of this group has a marked line", c.name);
        faults.extend(lines_noted(c, the_diag(r, c), &[], &c.nonote));
    }
    none_of(faults);
}

#[test]
fn a_function_that_moves_or_borrows_the_owner_has_no_report() {
    // The cases with no report: a last-use consumption (`sink(s)` alone, a read before it, `match move o`,
    // `pair_r(s.len(), s)` where the read is in the earlier argument), a function with `Alloc` in its row, and a
    // borrowed owner (a parameter that is not `move`, whose copy has nothing to drop). The first test checks
    // that each of them has none; this one checks that the group is not empty.
    let r = run();
    for c in group(r, "quiet", 10) {
        assert!(found(r, c).is_empty(), "{}: a report: {:?}", c.name, found(r, c));
    }
}
