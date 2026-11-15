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
//! The unit U12 (R-466, W6-04 U12/t) adds the package `N` and the tests `u12_*` at the end of the file: the
//! copies of a path, of a place a `for` or a guard holds, of a chain of borrowed headings, of the drop of an
//! assignment, and of the second binding that one report joins, which have no note yet. The tests of them carry
//! `#[ignore]` of W6-04 U12 (the unit's implementation takes it off); the other `u12_*` tests pass today and keep
//! what does not change. The markers are those above, with `//@ more`, `//@ once` and `same=<case>` (see `N`).
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

/// The package of the unit U12 (R-466): the forms whose copy has no note yet, in the same markers as `M`, and the
/// forms that are not to change. `//@ more` is a line that needs a note in the group `more` only (the copy of the
/// second binding that one report joins, S-783); `//@ once` is a line that no more than one note of the report
/// points at; `same=<case>` is a case whose report has the notes of the other case, line by line (relative to the
/// first line of each case).
const N: &str = r####"//@ case helpers none
enum W { A(Str), B }

struct P { name: Str, n: U32 }

struct Q { p: P, k: U32 }

fn eat(move s: Str) -> W { W.A(s) }

rt fn reat(move s: Str) -> W { W.A(s) }

fn look(s: Str) -> U32 { s.len() }

rt fn rlook(s: Str) -> U32 { s.len() }

fn pair(move s: Str, n: U32) -> W { W.A(s) }

rt fn rpair(move s: Str, n: U32) -> W { W.A(s) }

fn mk(n: U32) -> P { P { name: "a", n: n } }

// The callees that consume a value and return a `U32`: the value that is taken and dropped needs `Alloc`
// where it is dropped, so each is an E0601 of its own (no note of a copy: its parameter is a `move` one). The
// first of each kind is also the control of the cases below: the same drop with no copy.

//@ case sink fixes=1 g=callee
fn sink(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

//@ case rsink fixes=0 g=callee
rt fn rsink(move s: Str) -> U32 {   //@ main move |s
  s.len()
}

//@ case sink_xs fixes=1 g=callee
fn sink_xs(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  xs.len()
}

//@ case rsink_xs fixes=0 g=callee
rt fn rsink_xs(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  xs.len()
}

//@ case sink_o fixes=1 g=callee
fn sink_o(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) => s.len(),
    None => 0
  }
}

//@ case rsink_o fixes=0 g=callee
rt fn rsink_o(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) => s.len(),
    None => 0
  }
}

// ---------------------------------------------------------------------------------------------- (1) paths
// A field or an element path (`p.name`, `self.s`, `t.0`, `xs[0]`) of an owned binding that is put in a consuming
// position is a copy, and the drop of the whole stays (s.5.2: a path of a field or an element is a copy
// and the drop of the whole stays). The report of the drop shows the line of the copy.

//@ case path_arg fixes=1 ctl=sink g=path
fn path_arg(move p: P) -> W {   //@ main move |p
  eat(p.name)                   //@ note
}

//@ case rpath_arg fixes=0 ctl=rsink g=path
rt fn rpath_arg(move p: P) -> W {   //@ main move |p
  reat(p.name)                      //@ note
}

//@ case path_let_move fixes=1 ctl=sink g=path
fn path_let_move(move p: P) -> Str {   //@ main move |p
  let s = move p.name                  //@ note
  s
}

//@ case rpath_let_move fixes=0 ctl=rsink g=path
rt fn rpath_let_move(move p: P) -> Str {   //@ main move |p
  let s = move p.name                      //@ note
  s
}

//@ case path_self fixes=1 ctl=sink g=path
impl P {
  fn path_self(move self) -> W {   //@ main move |self
    eat(self.name)                 //@ note
  }
}

//@ case rpath_self fixes=0 ctl=rsink g=path
impl P {
  rt fn rpath_self(move self) -> W {   //@ main move |self
    reat(self.name)                    //@ note
  }
}

//@ case path_deep fixes=1 ctl=sink g=path
fn path_deep(move q: Q) -> W {   //@ main move |q
  eat(q.p.name)                  //@ note
}

//@ case rpath_deep fixes=0 ctl=rsink g=path
rt fn rpath_deep(move q: Q) -> W {   //@ main move |q
  reat(q.p.name)                     //@ note
}

//@ case path_tuple fixes=1 ctl=sink g=path
fn path_tuple(move t: (Str, U32)) -> Str {   //@ main move |t
  t.0                                        //@ note
}

//@ case rpath_tuple fixes=0 ctl=rsink g=path
rt fn rpath_tuple(move t: (Str, U32)) -> Str {   //@ main move |t
  t.0                                            //@ note
}

//@ case path_elem fixes=1 ctl=sink g=path
fn path_elem(move xs: [Str; 2]) -> Str {   //@ main move |xs
  xs[0]                                    //@ note
}

//@ case rpath_elem fixes=0 ctl=rsink g=path
rt fn rpath_elem(move xs: [Str; 2]) -> Str {   //@ main move |xs
  xs[0]                                        //@ note
}

//@ case path_branch fixes=1 ctl=sink g=path
fn path_branch(move p: P, c: Bool) -> W {   //@ main move |p
  if c {
    eat(p.name)                             //@ note
  } else {
    W.B
  }
}

//@ case rpath_branch fixes=0 ctl=rsink g=path
rt fn rpath_branch(move p: P, c: Bool) -> W {   //@ main move |p
  if c {
    reat(p.name)                                //@ note
  } else {
    W.B
  }
}

// A path whose root is a borrowed binding (the arm of `match o`, the element of `for p in ps`) is a path first:
// the copy is noted at its line (what `match move o` would fix is not what the path needs).

//@ case path_borrow_head fixes=1 ctl=sink g=path
fn path_borrow_head(move o: Option[P]) -> W {   //@ main move |o
  match o {
    Some(p) => eat(p.name),                     //@ note
    None => W.B
  }
}

//@ case rpath_borrow_head fixes=0 ctl=rsink g=path
rt fn rpath_borrow_head(move o: Option[P]) -> W {   //@ main move |o
  match o {
    Some(p) => reat(p.name),                        //@ note
    None => W.B
  }
}

//@ case path_borrow_for fixes=1 ctl=sink g=path
fn path_borrow_for(move ps: [P; 2]) -> U32 {   //@ main move |ps
  var t: U32 = 0
  for p in ps {
    t = t + sink(p.name)                       //@ note
  }
  t
}

// An owned arm binding (`match move o`) is dropped at the end of the arm, and its path is a copy.

//@ case path_owned_head fixes=1 ctl=sink g=path
fn path_owned_head(move o: Option[P]) -> W {
  match move o {
    Some(p) => {      //@ main Some(|p
      eat(p.name)     //@ note
    },
    None => W.B
  }
}

//@ case rpath_owned_head fixes=0 ctl=rsink g=path
rt fn rpath_owned_head(move o: Option[P]) -> W {
  match move o {
    Some(p) => {      //@ main Some(|p
      reat(p.name)    //@ note
    },
    None => W.B
  }
}

// A path of the scrutinee itself (`match q.0`): the arm binding is a borrow of the owner `q`, so its consumption
// is a copy and the drop of `q` shows it (S-1035 (2) says it of every copy that leaves a drop; the table of
// R-466 does not name this heading, so this case has a group of its own).

//@ case path_head_scrut fixes=1 ctl=sink g=headpath
fn path_head_scrut(move q: (Option[Str], U32)) -> W {   //@ main move |q
  match q.0 {
    Some(s) => W.A(s),                                  //@ note
    None => W.B
  }
}

// A combination: an anonymous function owns its parameter, and its drop is its own report (no candidate).

//@ case path_closure fixes=0 g=path
fn path_closure(n: U32) -> U32 {
  let g = fn(move p: P) -> W {   //@ main move |p
    eat(p.name)                  //@ note
  }
  n
}

// A path is a copy even where the other consumption of the function is the last use of its whole binding (that
// one moves, so its line has no note and the value is not dropped).

//@ case path_mixed fixes=1 g=path,moved
fn path_mixed(move p: P, move s: Str) -> U32 {   //@ main move |p
  let a = sink(p.name)                           //@ note
  let b = sink(s)                                //@ nonote
  a + b + p.n
}

//@ case rpath_mixed fixes=0 g=path,moved
rt fn rpath_mixed(move p: P, move s: Str) -> U32 {   //@ main move |p
  let a = rsink(p.name)                              //@ note
  let b = rsink(s)                                   //@ nonote
  a + b + p.n
}

// ----------------------------------------------------------------------------- (2) places a for or a guard holds
// A borrowing `for` and a guard hold their place (s.5.2: a place that a borrowing `for` or a guard holds is not
// one to move from): a consumption of `xs` in the body of `for x in xs` and a consumption of `o` in the guard of an arm of
// `match o` is a copy.

//@ case holds_for fixes=1 ctl=sink g=holds
fn holds_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var n: U32 = 0
  for x in xs {
    n = n + look(x) + sink_xs(xs)          //@ note
  }
  n
}

//@ case rholds_for fixes=0 ctl=rsink g=holds
rt fn rholds_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var n: U32 = 0
  for x in xs {
    n = n + rlook(x) + rsink_xs(xs)            //@ note
  }
  n
}

//@ case holds_guard fixes=1 ctl=sink g=holds
fn holds_guard(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) if sink_o(o) > s.len() => 1,       //@ note
    _ => 0
  }
}

//@ case rholds_guard fixes=0 ctl=rsink g=holds
rt fn rholds_guard(move o: Option[Str]) -> U32 {   //@ main move |o
  match o {
    Some(s) if rsink_o(o) > s.len() => 1,          //@ note
    _ => 0
  }
}

// ------------------------------------------------------------------------------------- (3) chains of headings
// A binding that a borrowed heading makes and that is passed on (`let t = s`, an inner `match`, an inner `for`,
// a `match` in a `for`) is still a borrow of the owner, so its consumption is a copy at its own line.

//@ case chain_let fixes=1 ctl=sink g=chain
fn chain_let(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => {
      let t = s
      W.A(t)                               //@ note
    },
    None => W.B
  }
}

//@ case rchain_let fixes=0 ctl=rsink g=chain
rt fn rchain_let(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => {
      let t = s
      W.A(t)                                   //@ note
    },
    None => W.B
  }
}

//@ case chain_match fixes=1 ctl=sink g=chain
fn chain_match(move o: Option[Option[Str]]) -> W {   //@ main move |o
  match o {
    Some(i) => match i {
      Some(s) => W.A(s),                             //@ note
      None => W.B
    },
    None => W.B
  }
}

//@ case rchain_match fixes=0 ctl=rsink g=chain
rt fn rchain_match(move o: Option[Option[Str]]) -> W {   //@ main move |o
  match o {
    Some(i) => match i {
      Some(s) => W.A(s),                                 //@ note
      None => W.B
    },
    None => W.B
  }
}

//@ case chain_for fixes=1 ctl=sink g=chain
fn chain_for(move rows: [[Str; 2]; 2]) -> U32 {   //@ main move |rows
  var t: U32 = 0
  for row in rows {
    for s in row {
      t = t + sink(s)                             //@ note
    }
  }
  t
}

//@ case rchain_for fixes=0 ctl=rsink g=chain
rt fn rchain_for(move rows: [[Str; 2]; 2]) -> U32 {   //@ main move |rows
  var t: U32 = 0
  for row in rows {
    for s in row {
      t = t + rsink(s)                                //@ note
    }
  }
  t
}

//@ case chain_for_match fixes=1 ctl=sink g=chain
fn chain_for_match(move xs: [Option[Str]; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for o in xs {
    match o {
      Some(s) => { t = t + sink(s) },                    //@ note
      None => {}
    }
  }
  t
}

//@ case rchain_for_match fixes=0 ctl=rsink g=chain
rt fn rchain_for_match(move xs: [Option[Str]; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for o in xs {
    match o {
      Some(s) => { t = t + rsink(s) },                       //@ note
      None => {}
    }
  }
  t
}

// An owner that was made by a `let` first (`let b = a`, the move of `a` is its last use): the heading is `b`.

//@ case chain_let_first fixes=1 g=kept
fn chain_let_first(move a: Option[Str]) -> W {
  let b = a                                   //@ main let |b
  match b {
    Some(s) => W.A(s),                        //@ note
    None => W.B
  }
}

//@ case rchain_let_first fixes=0 g=kept
rt fn rchain_let_first(move a: Option[Str]) -> W {
  let b = a                                       //@ main let |b
  match b {
    Some(s) => W.A(s),                            //@ note
    None => W.B
  }
}

// -------------------------------------------------------------------------- (4) the drop of an assignment
// The assignment `v = t` drops the old value of `v` (S-1038), so it is the report when the old value is held
// because a consumption of it was copied (a later read, the same call): the report is at the target of the
// assignment (s.8.1: the target of the assignment) and shows the line of the copy.

//@ case over_after fixes=1 g=over
fn over_after(move s: Str, t: Str) -> (W, Str, U32) {
  var v = s
  let w = eat(v)                                    //@ note
  let n = look(v)
  v = t                                             //@ main |v
  (w, v, n)
}

//@ case rover_after fixes=0 g=over
rt fn rover_after(move s: Str, t: Str) -> (W, Str, U32) {
  var v = s
  let w = reat(v)                                       //@ note
  let n = rlook(v)
  v = t                                                 //@ main |v
  (w, v, n)
}

//@ case over_call fixes=1 g=over
fn over_call(move s: Str, t: Str) -> (W, Str) {
  var v = s
  let w = pair(v, look(v))                          //@ note
  v = t                                             //@ main |v
  (w, v)
}

//@ case rover_call fixes=0 g=over
rt fn rover_call(move s: Str, t: Str) -> (W, Str) {
  var v = s
  let w = rpair(v, rlook(v))                            //@ note
  v = t                                                 //@ main |v
  (w, v)
}

// With the copy that is the last use of the value there is no old value to drop: the consumption moves it.

//@ case over_moved none g=quiet
fn over_moved(move s: Str, t: Str) -> (W, Str) {
  var v = s
  let w = eat(v)
  v = t
  (w, v)
}

// The assignment is the main report, and the same binding is copied three times in the function and assigned
// three times (m = c = 3): the note of each copy is once in the report (the notes of the other drops and of the
// main one read the same copies of `v`). The first copy is the one the first assignment drops. The lines of the
// copies each have one reason, the read after them, which is another line.

//@ case over_many fixes=1 g=over
fn over_many(move s: Str, t: Str) -> (W, W, W, Str, U32) {
  var v = s
  let a = eat(v)                                    //@ note; once
  let ra = look(v)
  v = t                                             //@ main |v
  let b = eat(v)                                    //@ once
  let rb = look(v)
  v = t
  let c = eat(v)                                    //@ once
  let rc = look(v)
  v = t
  (a, b, c, v, ra + rb + rc)
}

//@ case rover_many fixes=0 g=over
rt fn rover_many(move s: Str, t: Str) -> (W, W, W, Str, U32) {
  var v = s
  let a = reat(v)                                       //@ note; once
  let ra = rlook(v)
  v = t                                                 //@ main |v
  let b = reat(v)                                       //@ once
  let rb = rlook(v)
  v = t
  let c = reat(v)                                       //@ once
  let rc = rlook(v)
  v = t
  (a, b, c, v, ra + rb + rc)
}

// ---------------------------------------------------------- the drops that the report joins (S-783: one report)
// Two bindings dropped after a copy are one report (the first by position), and the notes of the first copy
// are the main's own. The copy of the second binding is noted at its line too.

//@ case more_two fixes=1 g=kept,more
fn more_two(move a: Str, move b: Str) -> U32 {   //@ main move |a
  let x = sink(a)                                //@ note
  let y = sink(b)                                //@ more
  x + y + a.len() + b.len()
}

//@ case rmore_two fixes=0 g=kept,more
rt fn rmore_two(move a: Str, move b: Str) -> U32 {   //@ main move |a
  let x = rsink(a)                                   //@ note
  let y = rsink(b)                                   //@ more
  x + y + a.len() + b.len()
}

//@ case more_path fixes=1 g=kept,more
fn more_path(move a: Str, move p: P) -> U32 {   //@ main move |a
  let x = sink(a)                               //@ note
  let y = sink(p.name)                          //@ more
  x + y + a.len() + p.n
}

//@ case more_heading fixes=1 g=kept,more
fn more_heading(move a: Str, move o: Option[Str]) -> W {   //@ main move |a
  let x = sink(a)                                          //@ note
  let y = a.len() + x
  match o {
    Some(s) if y > 0 => W.A(s),                            //@ more
    _ => W.B
  }
}

// ------------------------------------------------------------------------------------- (5) a parenthesis
// A parenthesis is its content (s.5.2 for a `move` operand, s.5.4 for the initializer): the heading `(o)` is the
// heading `o`, so the report has the notes of the same function written without it.

//@ case paren_match fixes=1 same=plain_match ctl=sink g=paren
fn paren_match(move o: Option[Str]) -> W {   //@ main move |o
  match (o) {
    Some(s) => W.A(s),                       //@ note
    None => W.B
  }
}

//@ case plain_match fixes=1 g=kept
fn plain_match(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => W.A(s),                       //@ note
    None => W.B
  }
}

//@ case rparen_match fixes=0 same=rplain_match ctl=rsink g=paren
rt fn rparen_match(move o: Option[Str]) -> W {   //@ main move |o
  match (o) {
    Some(s) => W.A(s),                           //@ note
    None => W.B
  }
}

//@ case rplain_match fixes=0 g=kept
rt fn rplain_match(move o: Option[Str]) -> W {   //@ main move |o
  match o {
    Some(s) => W.A(s),                           //@ note
    None => W.B
  }
}

//@ case paren_for fixes=1 same=plain_for ctl=sink g=paren
fn paren_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in (xs) {
    t = t + sink(s)                        //@ note
  }
  t
}

//@ case plain_for fixes=1 g=kept
fn plain_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in xs {
    t = t + sink(s)                        //@ note
  }
  t
}

//@ case rparen_for fixes=0 same=rplain_for ctl=rsink g=paren
rt fn rparen_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in (xs) {
    t = t + rsink(s)                           //@ note
  }
  t
}

//@ case rplain_for fixes=0 g=kept
rt fn rplain_for(move xs: [Str; 2]) -> U32 {   //@ main move |xs
  var t: U32 = 0
  for s in xs {
    t = t + rsink(s)                           //@ note
  }
  t
}

// ----------------------------------------------------------------------------------------- what does not change
// A copy of a borrowed argument has nothing to drop (no report). A path of a temporary value (`mk(n).name`) has
// no binding as its root, so its report (the drop of the temporary) has the notes of the same drop of a field that
// is read (`mk(n).n`). A heading that is an `if` has no `move` place to show, so only the position of the report
// is fixed (the first of its owners by position).

//@ case borrowed_arg none g=quiet
fn borrowed_arg(s: Str) -> W {
  W.A(s)
}

//@ case borrowed_path none g=quiet
fn borrowed_path(p: P) -> W {
  eat(p.name)
}

//@ case path_alloc none g=quiet
fn path_alloc(move p: P) -> W uses {Alloc} {
  eat(p.name)
}

//@ case destructure none g=quiet
fn destructure(move t: (Str, U32)) -> Str {
  let (s, _) = move t
  s
}

//@ case temp_path fixes=1 same=temp_read g=temp
fn temp_path(n: U32) -> Str {
  mk(n).name   //@ main |mk(n)
}

//@ case temp_read fixes=1 g=temp
fn temp_read(n: U32) -> U32 {
  mk(n).n   //@ main |mk(n)
}

//@ case if_head fixes=1 g=ifhead
fn if_head(move a: Option[Str], move b: Option[Str], c: Bool) -> W {   //@ main move |a
  match if c { a } else { b } {
    Some(s) => W.A(s),
    None => W.B
  }
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
    /// The lines that need a note of the copy only in the group `more` (the second binding of a report).
    more: Vec<usize>,
    /// The lines that no more than one note of the report points at.
    once: Vec<usize>,
    /// The case whose report has the same notes (the same number, at the same lines of its own).
    same: Option<String>,
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
                    Some(("same", v)) => c.same = Some(v.to_string()),
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
                    "more" => c.more.push(no),
                    "once" => c.once.push(no),
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

/// A package checked: the cases and the diagnostics.
fn check_package(text: &str) -> Run {
    let cases = parse(text);
    let texts: Texts = [(FILE.to_string(), text.to_string())].into();
    let out = check_input_out(&input_of("demo", &texts));
    assert!(out.code == 0 || out.code == 1, "the check ended with {}: {}", out.code, out.stderr);
    let diags = diagnostics(&doc_of(&out)).clone();
    Run { cases, diags }
}

/// The package of the unit U3 (`M`), checked once.
fn run() -> &'static Run {
    static RUN: OnceLock<Run> = OnceLock::new();
    RUN.get_or_init(|| check_package(M))
}

/// The package of the unit U12 (`N`), checked once.
fn run12() -> &'static Run {
    static RUN: OnceLock<Run> = OnceLock::new();
    RUN.get_or_init(|| check_package(N))
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

// ------------------------------------------------------------------------------- the unit U12 (R-466): the table
//
// The package `N` is the forms of R-466 (W6-04 U12/t). The note of a copy is read from one table that every
// copy of an owned binding of the body writes: a path (`p.name`, `t.0`, `xs[0]`), the place a borrowing `for` or a
// guard holds, a chain of borrowed headings, a drop by an assignment, the second binding of one report, and a
// heading in a parenthesis. What the tests compare is what the tests above compare (the code, the place and the
// number of candidates of the report, and the lines the notes point at, not their columns or text), with the
// number of the notes of the control and of the same function written without the parenthesis. They do not
// compare: the line of the note of the reason of a heading (its own line or the line of the copy), the note of
// `match move o` (a path is noted first, so a borrowed binding's path has no `match move` note, and an `if`
// heading has none), and the reason (a later use, the next iteration, a hold).

/// The faults of a case in the test of the group `g`: the lines that need a note (the `more` lines in the group
/// `more`, none in the group `moved`, whose cases are there for their `nonote` lines), the lines that must have
/// none, the lines that no more than one note points at, one note more than the control, and the same notes as
/// the case of `same=`.
fn faults_of(r: &Run, c: &Case, g: &str) -> Vec<String> {
    let d = the_diag(r, c);
    let mut want = if g == "moved" { Vec::new() } else { c.note.clone() };
    if g == "more" {
        want.extend(&c.more);
    }
    let mut faults = lines_noted(c, d, &want, &c.nonote);
    if g == "moved" {
        return faults;
    }
    let spans = note_spans(d);
    for l in &c.once {
        let n = spans.iter().filter(|s| s.file == FILE && s.line as usize == *l).count();
        if n > 1 {
            faults.push(format!("{}: {n} notes point at line {l}, once expected\n{}", c.name, describe(d)));
        }
    }
    if let Some(ctl) = c.control.as_deref() {
        let (n, base) = (notes_of(d).len(), notes_of(the_diag(r, case(r, ctl))).len());
        if n < base + 1 {
            faults.push(format!("{}: {n} notes, at least {} (one more than {ctl}) expected", c.name, base + 1));
        }
    }
    if let Some(other) = c.same.as_deref() {
        let o = case(r, other);
        let rel = |c: &Case, d: &Value| -> Vec<i64> {
            let mut v: Vec<i64> = note_spans(d).iter().map(|s| s.line as i64 - c.first as i64).collect();
            v.sort();
            v
        };
        let (mine, theirs) = (rel(c, d), rel(o, the_diag(r, o)));
        if mine != theirs || notes_of(d).len() != notes_of(the_diag(r, o)).len() {
            faults.push(format!(
                "{}: the notes are at the lines {mine:?} of the case, {other} has {theirs:?}\n{}",
                c.name,
                describe(d)
            ));
        }
    }
    faults
}

fn group_faults(g: &str, at_least: usize) -> Vec<String> {
    let r = run12();
    group(r, g, at_least).into_iter().flat_map(|c| faults_of(r, c, g)).collect()
}

#[test]
fn u12_each_function_gets_one_report_at_the_place_its_rule_gives() {
    // The code, the place and the number of candidates of the report, as of the first test of the unit U3 (§8.1:
    // the place is where the owned value is written: a parameter, `self`, the name of a `let` or of an arm, the
    // target of an assignment that drops the old value, the expression of a value that no binding has; an `rt`
    // function gets no candidate, an anonymous function none; S-783, S-1035). A function with `none` gets no
    // report, so a case that is written wrong does not pass by having no diagnostic.
    let r = run12();
    assert!(r.cases.len() >= 60, "{} cases", r.cases.len());
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
    assert!(reports >= 50, "{reports} reports compared");
}

#[test]
fn u12_a_consumption_that_is_moved_has_no_note_of_a_copy() {
    // S-1030: the consumption that is the last use of its binding moves the value, so a report of the function
    // that is about another binding (`path_mixed`: the whole `s`, whose line has no note) has no note at that line.
    let r = run12();
    assert!(group(r, "moved", 2).iter().all(|c| !c.nonote.is_empty()));
    none_of(group_faults("moved", 2));
}

#[test]
fn u12_the_notes_of_the_copies_that_are_noted_today_stay() {
    // The copies of the four reasons (a heading `match o`, `for s in xs`) and the first binding of a report that
    // joins two. The unit does not change them; it must keep them after the table is one.
    none_of(group_faults("kept", 6));
}

#[test]
fn u12_the_report_that_joins_no_drop_has_no_report() {
    // The forms that have no report: a borrowed argument (a copy of a borrow has nothing to drop), a path of a
    // borrowed binding, a function with `Alloc` in its row, and a destructuring `let` that takes the whole value
    // (`let (s, _) = move t`: the `s` moves, the discarded `U32` needs no drop), and a drop that no copy holds
    // (the value that `eat(v)` takes is the last use before the assignment). The first test checks that each has
    // none; this one checks that the group is not empty.
    let r = run12();
    for c in group(r, "quiet", 5) {
        assert!(found(r, c).is_empty(), "{}: a report: {:?}", c.name, found(r, c));
    }
}

#[test]
fn u12_the_drop_of_a_temporary_value_has_the_notes_of_a_read_field() {
    // `mk(n).name` has no binding as its root: no row of a copy, so the report of the drop of the temporary
    // has the notes of `mk(n).n` (the report of the same drop, whose field is read: no copy).
    let r = run12();
    let c = case(r, "temp_path");
    none_of(faults_of(r, c, "temp"));
}

#[test]
fn u12_an_if_heading_has_a_report_at_the_first_of_its_owners() {
    // The report is at `a`, the first by position of the two the heading may be (§18.1); the drop of `b` is a note
    // of it. What the notes show for the copy is not fixed (a reason may be there, `match move` cannot be).
    let r = run12();
    assert_eq!(group(r, "ifhead", 1).len(), 1);
}

#[test]
fn u12_a_path_consumption_is_noted_at_its_line() {
    // R-466 (1): `eat(p.name)`, `let s = move p.name`, `self.name` of `move self`, `q.p.name`, `t.0`, `xs[0]`,
    // a path in a branch, the path of a borrowed binding (`match o { Some(p) => eat(p.name) }`, `for p in ps`),
    // of an owned arm binding (`match move o`), of the scrutinee `match q.0`, and of the parameter of an anonymous
    // function, in an `fn` and an `rt fn` (§5.2: "フィールドと要素の経路（`p.0`、`self.s`）は複製で、全体の破棄が
    // 残る"). The note is at the line of the path, and the report has at least one note more than the control.
    none_of(group_faults("path", 20));
}

#[test]
fn u12_the_scrutinee_that_is_a_path_has_the_note_of_the_copy_of_its_arm_binding() {
    // S-1035 (2): the arm binding of `match q.0` is a borrow of the owner, and its copy is a place the report of
    // the drop of `q` shows. R-466 names no such heading (its (3) is the chain of a binding), so a reading that
    // leaves it out is the one case of this file to drop.
    none_of(group_faults("headpath", 1));
}

#[test]
fn u12_a_place_a_for_or_a_guard_holds_is_noted_at_its_line() {
    // R-466 (2): `sink_xs(xs)` in the body of `for x in xs` and `sink_o(o)` in the guard of `match o` cannot
    // move (§5.2: "借用の `for` とガードが持つ場所でない"), so they are copies.
    none_of(group_faults("holds", 4));
}

#[test]
fn u12_a_chain_of_borrowed_headings_is_noted_at_the_copy() {
    // R-466 (3): the binding of an inner `match`, of an inner `for`, of a `match` in a `for`, and a `let` of a
    // borrowed binding is a borrow of the owner, so its consumption is a copy at its own line. (The line of the
    // reason of the outermost heading is not compared.)
    none_of(group_faults("chain", 8));
}

#[test]
fn u12_the_drop_of_an_assignment_is_noted_with_the_copy() {
    // R-466 (4): `v = t` drops the old value of `v` (S-1038), so the report at its target shows the copy of `v`
    // that holds it (`let w = eat(v)` and a later `look(v)`; `pair(v, look(v))`); and one copy is noted once in a
    // report whose drops are three assignments of a binding copied three times (F3).
    none_of(group_faults("over", 6));
}

#[test]
fn u12_the_second_binding_of_a_report_is_noted_at_its_copy() {
    // R-466 F3 (S-783: the drops of one range are one report, the first by position; the others are notes): the
    // copy of the second binding is noted, as the copy of the first is (a plain consumption, a path, a heading).
    none_of(group_faults("more", 4));
}

#[test]
fn u12_a_heading_in_a_parenthesis_has_the_notes_of_the_heading_without_it() {
    // R-466 F5 (§5.2, §5.4: a parenthesis is its content): `match (o)` and `for s in (xs)` have the notes of
    // `match o` and `for s in xs` (the same number, at the same lines). That the note of the copy shows `match
    // move o` is in its text, which §18.1 does not fix, so this test cannot see the fault of F5 (today the text of
    // the note of `match (o)` does not name `match move o`); it keeps the number and the lines equal.
    none_of(group_faults("paren", 4));
}

#[test]
fn u12_the_notes_of_one_heading_of_many_roots_grow_with_the_copies_alone() {
    // W6-04 U12/b (`grow3.py`): `match match c { R arms } { Some(s) => n × eat(s) }` copies `s`, a borrow of each of
    // the R roots, at n places: one report of R × n copies (F3: each root once in it). A note names the heading by
    // its kind and points at it (once a root), so no note grows with the text of the heading (before: each of the
    // R × n notes had the text of the R arms, 16 MB at 100 × 100). Bounded: each note, and their number.
    let (r, n) = (100, 100);
    let params: Vec<String> = (0..r).map(|i| format!("move a{i}: Option[Str]")).collect();
    let arm = |i: usize| if i + 1 < r { format!("    {i} => a{i},\n") } else { format!("    _ => a{i},\n") };
    let (arms, body): (String, String) = ((0..r).map(arm).collect(), "      x = x + eat(s)\n".repeat(n));
    let text = format!(
        "pub fn eat(move s: Str) -> U32 uses {{Alloc}} {{ s.len() }}\npub fn t(c: U32, {}) -> U32 {{\n  var x: U32 = 0\n  match match c {{\n{arms}  }} {{\n    Some(s) => {{\n{body}    }},\n    None => {{}},\n  }}\n  x\n}}\n",
        params.join(", ")
    );
    let out = check_input_out(&input_of("demo", &[(FILE.to_string(), text)].into()));
    assert_eq!(out.code, 1, "{}", out.stderr);
    let doc = doc_of(&out);
    let notes: Vec<usize> = diagnostics(&doc).iter().flat_map(notes_of).map(|m| str_of(m, "message").len()).collect();
    let longest = notes.iter().copied().max().unwrap_or(0);
    assert!(notes.len() >= r * n, "{} notes, fewer than the copies", notes.len());
    assert!(notes.len() <= r * n + 4 * (r + n) && longest <= 200, "{} notes, the longest {longest}", notes.len());
}
