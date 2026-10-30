//! The unit tests of the new modes stage (W4-07): the flow of the moves
//! (U1) and the table of consumption (U2a) (§5.2, §5.4, §7), from sources
//! parsed in memory. Each runs the whole
//! analysis (the old modes stage included), then the new `check_all`, and
//! reads only the diagnostics it adds (review 10).

use std::collections::BTreeSet;

use onsa_diag::{Code, FileId, Span, Stage};

use super::check::{Walker, check_all};
use super::flow::Run;
use super::state::{Delta, LoopSum, Status};
use super::walk::Pos;
use crate::body::LocalId;

const PRELUDE: &str = "pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(1) }
pub fn take(move b: Buf[F32]) uses {Alloc} {}
pub fn take_all(move xs: [Buf[F32]; 2]) uses {Alloc} {}
pub fn eat(move b: Buf[F32]) -> Bool uses {Alloc} { true }
pub fn make_array() -> [Buf[F32]; 2] uses {Alloc} { [Buf.zeroed(1), Buf.zeroed(2)] }
pub fn mko() -> Option[Buf[F32]] uses {Alloc} { Some(Buf.zeroed(1)) }
pub struct Holder { buf: Buf[F32], n: U32 }
pub fn tk(move n: U32) {}
pub fn ts(move s: Str) uses {Alloc} {}
pub fn len_of(b: Buf[F32]) -> U32 { b.len() }
pub const K: U32 = 1
pub fn rd(xs: Span[F32]) -> U32 { xs.len() }
pub fn planes(xs: [Span[F32]; 2]) {}
pub fn apply(g: fn(U32) -> U32) -> U32 { g.(1) }
pub struct Stereo { l: F32, r: F32 }
pub flow pair(l: F32 at sample, r: F32 at sample) -> Stereo at sample { Stereo { l: l, r: r } }
pub fn mkr() -> Result[Buf[F32], U32] uses {Alloc} { Ok(Buf.zeroed(1)) }
pub fn keep[T: ?Dup](move x: T) {}
pub fn useout(o: pair.Out) {}
";

/// The analysis of the one module `src`. A diagnostic of a stage before
/// the modes in it fails the test: the new stage would not read the body.
fn analyzed(src: &str) -> (crate::Package, crate::Analysis) {
    let parsed = onsa_syntax::parse(FileId(0), src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let modules = vec![crate::Module { segments: vec!["main".into()], file: FileId(0), text: src.into(), parsed }];
    let pkg = crate::Package::new("t", modules, vec![crate::flow_tests::std_package()]);
    let a = crate::analyze(&pkg);
    let modes = Stage::Modes.check_rank().expect("a check stage");
    let early: Vec<_> = (a.diagnostics.iter())
        .filter(|d| d.span.file == FileId(0) && d.stage.check_rank().is_none_or(|r| r < modes))
        .collect();
    assert!(early.is_empty(), "{early:?}");
    (pkg, a)
}

/// What the new stage reports for the functions `body` after [`PRELUDE`]:
/// each diagnostic by its code, its line in `body` (from 1) and whether it
/// says "previous iteration" (`via_loop`); and the names of the moved locals.
fn seen(body: &str) -> (Vec<(Code, usize, bool)>, BTreeSet<String>) {
    let src = format!("{PRELUDE}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    let moved = check_all(&pkg, &mut a);
    let line = |s: Span| {
        assert!(s.start as usize >= PRELUDE.len(), "in the prelude: {s:?}");
        src[PRELUDE.len()..s.start as usize].matches('\n').count() + 1
    };
    let diags = (a.diagnostics[before..].iter())
        .filter(|d| d.span.file == FileId(0))
        .map(|d| (d.code, line(d.span), d.message.contains("previous iteration")))
        .collect();
    let names = (moved.iter())
        .filter(|(def, _)| a.def(**def).span.file == FileId(0))
        .flat_map(|(def, ls)| ls.iter().map(|l| a.bodies[def].locals[l.0 as usize].name.clone()))
        .collect();
    (diags, names)
}

fn diags(body: &str) -> Vec<(Code, usize, bool)> {
    seen(body).0
}

const MOVED: (Code, bool) = (Code::E0704, false);
const BY_LOOP: (Code, bool) = (Code::E0704, true);

fn at(line: usize, (code, via_loop): (Code, bool)) -> (Code, usize, bool) {
    (code, line, via_loop)
}

#[test]
fn a_move_on_one_branch_of_an_if() {
    let src = "pub fn t(c: Bool) uses {Alloc} {
  let b = mk()
  if c { take(move b) }
  let n = b.len()
}
pub fn both(c: Bool) uses {Alloc} {
  let b = mk()
  if c { take(move b) } else { take(move b) }
}
";
    assert_eq!(diags(src), [at(4, MOVED)]);
}

#[test]
fn a_move_in_one_arm_of_a_match() {
    let src = "pub fn t(o: Option[U32]) uses {Alloc} {
  let b = mk()
  match o {
    Some(_) => take(move b),
    None => {},
  }
  take(move b)
}
";
    assert_eq!(diags(src), [at(7, MOVED)]);
}

#[test]
fn a_move_on_the_right_of_and_and_or() {
    let src = "pub fn and(c: Bool) uses {Alloc} {
  let b = mk()
  if c && eat(move b) {}
  take(move b)
}
pub fn or(c: Bool) uses {Alloc} {
  let b = mk()
  let d = c || eat(move b)
  take(move b)
}
";
    assert_eq!(diags(src), [at(4, MOVED), at(9, MOVED)]);
}

#[test]
fn a_move_in_a_previous_iteration() {
    let src = "pub fn w(n: U32) uses {Alloc} {
  let b = mk()
  var i: U32 = 0
  while i < n {
    take(move b)
    i = i + 1
  }
}
pub fn f(n: U32) uses {Alloc} {
  let b = mk()
  for i in 0 ..< n {
    take(move b)
  }
}
";
    assert_eq!(diags(src), [at(5, BY_LOOP), at(12, BY_LOOP)]);
}

#[test]
fn a_var_assigned_again_is_live() {
    let src = "pub fn t(n: U32) uses {Alloc} {
  var b = mk()
  for i in 0 ..< n {
    take(move b)
    b = mk()
  }
  take(move b)
}
";
    assert_eq!(diags(src), []);
}

#[test]
fn the_exits_of_a_loop() {
    let src = "pub fn by_break(n: U32) uses {Alloc} {
  let b = mk()
  for i in 0 ..< n {
    take(move b)
    break
  }
  take(move b)
}
pub fn by_continue(c: Bool, n: U32) uses {Alloc} {
  let b = mk()
  for i in 0 ..< n {
    if c {
      take(move b)
      continue
    }
  }
}
pub fn by_return(c: Bool) uses {Alloc} {
  let b = mk()
  if c {
    take(move b)
    return
  }
  take(move b)
}
";
    assert_eq!(diags(src), [at(7, MOVED), at(13, BY_LOOP)]);
}

#[test]
fn nested_loops() {
    let src = "pub fn inner(n: U32) uses {Alloc} {
  var b = mk()
  for i in 0 ..< n {
    for j in 0 ..< n {
      take(move b)
    }
    b = mk()
  }
}
pub fn outer(n: U32) uses {Alloc} {
  var b = mk()
  for i in 0 ..< n {
    for j in 0 ..< n {}
    take(move b)
  }
}
pub fn revived(n: U32) uses {Alloc} {
  var b = mk()
  for i in 0 ..< n {
    while true {
      take(move b)
      break
    }
    b = mk()
  }
  take(move b)
}
";
    assert_eq!(diags(src), [at(5, BY_LOOP), at(14, BY_LOOP)]);
}

/// Review 1: the back edge of a `while` goes through its condition.
#[test]
fn a_move_in_the_condition_of_a_while() {
    let src = "pub fn cond_moves() uses {Alloc} {
  var x: Buf[F32] = Buf.zeroed(1)
  while eat(move x) {
    x = Buf.zeroed(2)
  }
}
pub fn cond_moves_bad() uses {Alloc} {
  var x: Buf[F32] = Buf.zeroed(1)
  while eat(move x) {
  }
}
";
    assert_eq!(diags(src), [at(9, BY_LOOP)]);
}

/// R-251: the bindings of a head on a value that is no place are owned, and
/// can be moved in the arm and the body (each iteration binds a new one).
#[test]
fn the_owned_bindings_of_a_head_on_a_value() {
    let src = "pub fn arm() uses {Alloc} {
  match mko() {
    Some(z) => take(move z),
    None => {},
  }
}
pub fn body() uses {Alloc} {
  for z in make_array() {
    take(move z)
  }
}
";
    let (d, moved) = seen(src);
    assert_eq!(d, []);
    assert_eq!(moved, BTreeSet::from(["z".to_string()]));
}

/// R-29: `for … in move xs` consumes `xs` (not by the loop: the head is
/// walked once), and its binding is new at each iteration. The two cases
/// are those of `tests/spec/values/binding_heading_owned_move_loop.onsa`
/// and `binding_heading_loop_run.onsa` (pending until the switch, U4).
#[test]
fn a_for_over_a_moved_value() {
    let src = "pub fn t() uses {Alloc} {
  let xs = make_array()
  for s in move xs {
    take(move s)
  }
  take_all(move xs)
}
pub fn for_moves_the_element() uses {Alloc} {
  for z in make_array() {
    take(move z)
  }
}
fn make_pair(v: F32) -> [Buf[F32]; 2] uses {Alloc} {
  var a: Buf[F32] = Buf.zeroed(1)
  var b: Buf[F32] = Buf.zeroed(1)
  a[0] = v
  b[0] = v * 2.0
  [move a, move b]
}
fn value_of(move b: Buf[F32]) -> F32 uses {Alloc} {
  b[0]
}
fn for_moves_the_elements(v: F32) -> F32 uses {Alloc} {
  var total: F32 = 0.0
  for z in make_pair(v) {
    total = total + value_of(move z)
  }
  total
}
";
    let (d, moved) = seen(src);
    assert_eq!(d, [at(6, MOVED)]);
    let names = ["a", "b", "s", "xs", "z"].map(String::from);
    assert_eq!(moved, BTreeSet::from(names));
}

/// A Dup value marked `move` is copied (§5.2): not moved, not in the moved
/// locals. One diagnostic for each body, the first in its order (§18.1).
#[test]
fn copies_and_one_diagnostic_for_a_body() {
    let src = "pub fn copy() uses {Alloc} {
  let n: U32 = 1
  let m = move n
  let k = n + m
}
pub fn twice() uses {Alloc} {
  let b = mk()
  take(move b)
  take(move b)
  let n = b.len()
}
";
    let (d, moved) = seen(src);
    assert_eq!(d, [at(9, MOVED)]);
    assert_eq!(moved, BTreeSet::from(["b".to_string()]));
}

/// Memo 3: the head `x ⊔ G` is the least solution of `h = x ⊔ back(h)`,
/// against the iteration from `x` (the statuses, without the loop's mark).
#[test]
fn the_head_of_a_loop_is_its_least_fixpoint() {
    let (l, at) = (LocalId, |n| Span::new(FileId(0), n, n + 1));
    let mut entry = Delta::start();
    entry.set(l(0), Status::Moved { at: at(1), via_loop: false });
    entry.set(l(2), Status::Stale { changed: at(2) });
    let mut back = Delta::start();
    back.revive(l(1));
    back.set(l(1), Status::Moved { at: at(5), via_loop: false });
    back.revive(l(2));
    back.set(l(3), Status::Stale { changed: at(3) });
    back.set(l(0), Status::Moved { at: at(7), via_loop: false });
    let plain = |d: &Delta| {
        (0..5)
            .map(|i| {
                d.status(l(i)).map(|s| match s {
                    Status::Moved { at, .. } => Status::Moved { at, via_loop: false },
                    s => s,
                })
            })
            .collect::<Vec<_>>()
    };
    let head = entry.then(&LoopSum::head(&back));
    let mut again = entry.clone();
    again.join(&head.then(&back));
    assert_eq!(plain(&head), plain(&again), "a solution");
    let mut x = entry.clone();
    for _ in 0..4 {
        let mut next = entry.clone();
        next.join(&x.then(&back));
        x = next;
    }
    assert_eq!(plain(&head), plain(&x), "the least");
}

/// Memo 3: a body of 120 nested loops visits each expression at most twice
/// (the summaries are made once; walking a loop's body twice to check a
/// fixpoint would be 2^120). A `while` is two levels of §2.5's 256, so 200
/// cannot be written. On a large stack (rules 3.4).
#[test]
fn nested_loops_visit_each_expression_at_most_twice() {
    const DEPTH: usize = 120;
    let run = || {
        let depth = DEPTH;
        let mut src = String::from(PRELUDE);
        src.push_str("pub fn deep(n: U32) uses {Alloc} {\n  var b = mk()\n");
        src.push_str(&"while n > 0 {\n".repeat(depth));
        src.push_str("take(move b)\nb = mk()\n");
        src.push_str(&"}\n".repeat(depth));
        src.push_str("}\n");
        let (pkg, a) = analyzed(&src);
        let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == "deep").expect("deep");
        let root = crate::body::root_of(&a, id).expect("a body");
        let ast = &crate::module_of_def(&pkg, &a, id).expect("its module").parsed.ast;
        let mut w = Walker::new(&a, (ast, &src), &a.names[&id], &a.bodies[&id], Vec::new());
        w.expr(&mut Run::new(), root, Pos::Return);
        let (mut nodes, mut todo) = (0, vec![root]);
        while let Some(e) = todo.pop() {
            nodes += 1;
            todo.extend(ast.sub_exprs(e));
        }
        (w.m.visits, nodes, w.m.loops.len())
    };
    let (visits, nodes, loops) = onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
    assert_eq!(loops, DEPTH);
    assert!(visits <= 2 * nodes, "{visits} visits of {nodes} expressions");
}

/// A diagnostic by its code and its line, and each of its candidates by its
/// title and that line after its edits.
type Found = (Code, usize, Vec<(String, String)>);

/// What the new stage reports for `body` after [`PRELUDE`]: each diagnostic
/// by its code and its line in `body`, and each of its candidates by its
/// title and that line after its edits (trimmed).
fn fixes(body: &str) -> Vec<Found> {
    let src = format!("{PRELUDE}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let skip = PRELUDE.matches('\n').count();
    (a.diagnostics[before..].iter())
        .filter(|d| d.span.file == FileId(0))
        .map(|d| {
            let line = src[PRELUDE.len()..d.span.start as usize].matches('\n').count() + 1;
            let fixed = (d.fixes.iter()).map(|f| {
                let mut text = src.clone();
                for e in f.edits().iter().rev() {
                    text.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
                }
                (f.title().to_string(), text.lines().nth(skip + line - 1).unwrap_or_default().trim().to_string())
            });
            (d.code, line, fixed.collect())
        })
        .collect()
}

/// The diagnostics of `body` with no candidate, by code and line.
fn bare(code: Code, lines: &[usize]) -> Vec<Found> {
    lines.iter().map(|&l| (code, l, Vec::new())).collect()
}

/// R-117, S-41: an Affine value in an `inout` parameter is not moved out
/// (E0711, no candidate), marked or not, a path, a split, a return, a tail;
/// a Dup one is copied. `take(b)` is U3a's (the mode of the callee).
#[test]
fn an_inout_parameter_is_not_moved_out() {
    let src = "pub fn whole(inout b: Buf[F32]) uses {Alloc} {
  let c = b
}
pub fn marked(inout b: Buf[F32]) uses {Alloc} {
  let c = move b
}
pub fn field(inout h: Holder) uses {Alloc} {
  let x = h.buf
}
pub fn split(inout p: (Buf[F32], U32)) uses {Alloc} {
  let (a, n) = p
}
pub fn argument(inout b: Buf[F32]) uses {Alloc} {
  take(move b)
}
pub fn returned(inout b: Buf[F32]) -> Buf[F32] uses {Alloc} {
  b
}
pub fn tail(inout b: Buf[F32], k: Bool) uses {Alloc} {
  let c = if k { b } else { mk() }
}
pub fn copied(inout n: U32, inout h: Holder) -> U32 {
  let a = n
  let m = move n
  let k = move h.n
  n
}
";
    assert_eq!(fixes(src), bare(Code::E0711, &[2, 5, 8, 11, 14, 17, 20]));
}

/// §5.2, §5.4: nor out of a borrow (a parameter, a borrow binding, a `for`
/// over it, a `match move`); a Dup one is copied.
#[test]
fn a_borrow_is_not_moved_out() {
    let src = "pub fn marked(b: Buf[F32]) uses {Alloc} {
  let c = move b
}
pub fn derived(b: Buf[F32]) uses {Alloc} {
  let c = b
  take(move c)
}
pub fn returned(b: Buf[F32]) -> Buf[F32] uses {Alloc} {
  b
}
pub fn iterated(xs: [Buf[F32]; 2]) uses {Alloc} {
  for x in move xs {}
}
pub fn matched(o: Option[Buf[F32]]) uses {Alloc} {
  match move o { Some(b) => take(move b), None => {} }
}
pub fn copied(n: U32, s: Str) -> U32 uses {Alloc} {
  let m = move n
  let t = move s
  n
}
";
    assert_eq!(fixes(src), bare(Code::E0711, &[2, 6, 9, 12, 15]));
}

/// §5.2: an owned value is not moved out of an element (E0711), nor out of
/// a field until W4-09 (S-85; the partial move of now), marked or not; a
/// Dup one is copied and leaves its root.
#[test]
fn a_path_of_an_owned_value() {
    let src = "pub fn element(move xs: [Buf[F32]; 2]) uses {Alloc} {
  let y = move xs[0]
}
pub fn element_unmarked(move xs: [Buf[F32]; 2]) uses {Alloc} {
  let y = xs[1]
}
pub fn field(move h: Holder) uses {Alloc} {
  let y = move h.buf
}
pub fn field_returned(move h: Holder) -> Buf[F32] uses {Alloc} {
  h.buf
}
pub fn copied(move h: Holder, move t: (U32, U32)) uses {Alloc} {
  let n = h.n
  let m = move t.0
  take(move h.buf)
}
";
    assert_eq!(fixes(src), bare(Code::E0711, &[2, 5, 8, 11, 16]));
}

/// §5.2: a whole owned Affine local is moved where it is marked and where
/// it is returned; unmarked at a consuming position, E0711 with the
/// candidate that writes `move` (before the parentheses, in a tail).
#[test]
fn a_whole_owned_local() {
    let src = "pub fn unmarked() uses {Alloc} {
  let b = mk()
  let c = b
}
pub fn element() -> (Buf[F32], U32) uses {Alloc} {
  let b = mk()
  (b, 1)
}
pub fn parenthesized() uses {Alloc} {
  let b = mk()
  var c = (b)
}
pub fn tail(k: Bool) uses {Alloc} {
  let b = mk()
  let c = if k { b } else { mk() }
}
pub fn moves(k: Bool) -> Buf[F32] uses {Alloc} {
  let a = mk()
  let b = mk()
  let c = move a
  if k { return move b }
  b
}
";
    let add = |l: usize, line: &str| (Code::E0711, l, vec![("add `move`".to_string(), line.to_string())]);
    let expected = [
        add(3, "let c = move b"),
        add(7, "(move b, 1)"),
        add(11, "var c = move (b)"),
        add(15, "let c = if k { move b } else { mk() }"),
    ];
    let (d, moved) = seen(src);
    assert_eq!(fixes(src), expected);
    assert_eq!(d.len(), 4);
    assert_eq!(moved, BTreeSet::from(["a".to_string(), "b".to_string()]));
}

/// S-609: a Dup value marked `move` on a `move` argument is E0703 with the
/// candidate that removes the mark and its blanks (a local, a parameter, a
/// field, a Shared value); at a consuming position the mark is kept.
#[test]
fn a_dup_value_marked_on_a_move_argument() {
    let src = "pub fn local() {
  let n: U32 = 1
  tk(move   n)
}
pub fn parameter(n: U32) {
  tk(move n)
}
pub fn field(t: (U32, U32)) {
  tk(move t.0)
}
pub fn shared(s: Str) uses {Alloc} {
  ts(move s)
}
pub fn kept(n: U32) -> U32 {
  let m = move n
  let t = (move n, 1)
  return move n
}
";
    let remove = |l: usize, line: &str| (Code::E0703, l, vec![("remove `move`".to_string(), line.to_string())]);
    assert_eq!(fixes(src), [remove(3, "tk(n)"), remove(6, "tk(n)"), remove(9, "tk(t.0)"), remove(12, "ts(s)")]);
}

/// R-198: `move` on a value that is no place is E0711 at any position, with
/// no candidate (W4-09 adds those of a block and an `if`): a call, a
/// literal, a constant, a function item, a block, an `if`, on a `move`
/// argument and a `for` head. It moves nothing. (The types stage reports
/// the `move e` of the other positions, E0711 too.)
#[test]
fn a_move_on_a_value_that_is_no_place() {
    let src = "pub fn call() uses {Alloc} {
  take(move mk())
}
pub fn literal() {
  tk(move 1)
}
pub fn constant() {
  tk(move K)
}
pub fn block() uses {Alloc} {
  let b = mk()
  take(move { b })
  take(move b)
}
pub fn branches(k: Bool) uses {Alloc} {
  let b = mk()
  take(move if k { b } else { mk() })
}
pub fn head() uses {Alloc} {
  for x in move make_array() {}
}
";
    let (_, moved) = seen(src);
    assert_eq!(fixes(src), bare(Code::E0711, &[2, 5, 8, 12, 17, 20]));
    assert_eq!(moved, BTreeSet::from(["b".to_string()]));
}

/// The E0200 of a `move` on a tail where no value is consumed (W4-09 makes
/// it S-605's E0703): an operand, a borrowed argument.
#[test]
fn a_move_where_no_value_is_consumed() {
    let src = "pub fn operand(n: U32) -> U32 {
  let x = ({ move n }) + 1
  x
}
pub fn argument(k: Bool) -> U32 uses {Alloc} {
  let b = mk()
  len_of(if k { move b } else { mk() })
}
";
    assert_eq!(fixes(src), bare(Code::E0200, &[2, 7]));
}

/// Review 2: an erroneous consumption moves nothing, so the same local is
/// live after it (all the walk found, before the one of the body).
#[test]
fn an_erroneous_consumption_moves_nothing() {
    let mut src = String::from(PRELUDE);
    src.push_str(
        "pub fn t(inout h: Buf[F32]) uses {Alloc} {
  let b = mk()
  let c = b
  take(move b)
  let d = move h
  let n = h.len()
}
",
    );
    let (pkg, a) = analyzed(&src);
    let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == "t").expect("t");
    let root = crate::body::root_of(&a, id).expect("a body");
    let ast = &crate::module_of_def(&pkg, &a, id).expect("its module").parsed.ast;
    let mut w = Walker::new(&a, (ast, &src), &a.names[&id], &a.bodies[&id], Vec::new());
    w.expr(&mut Run::new(), root, Pos::Return);
    let lines: Vec<_> =
        w.m.found
            .iter()
            .map(|d| (d.code, src[PRELUDE.len()..d.span.start as usize].matches('\n').count() + 1))
            .collect();
    assert_eq!(lines, [(Code::E0711, 3), (Code::E0711, 5)]);
}

/// R-30, §4.6: a `T: ?Dup` value is Affine (an unbounded `T` is Shared).
#[test]
fn a_maybe_dup_value_is_affine() {
    let src = "pub fn inout_[T: ?Dup](inout v: T) {
  let c = move v
}
pub fn owned[T: ?Dup](move v: T) {
  let c = v
}
pub fn unbounded[T](move v: T) {
  let c = v
}
";
    let add = (Code::E0711, 5, vec![("add `move`".to_string(), "let c = move v".to_string())]);
    assert_eq!(fixes(src), [(Code::E0711, 2, Vec::new()), add]);
}

/// The places of the walk and their overlap (memo 1.2, §5.2).
#[test]
fn places_overlap() {
    use super::place::{Place, Proj, overlaps};
    let p = |root, proj: Vec<Proj>| Place { root: LocalId(root), proj };
    let f = |n: &str| Proj::Field(n.to_string());
    assert!(overlaps(&p(0, vec![f("a")]), &p(0, vec![f("a"), Proj::Index])));
    assert!(overlaps(&p(0, vec![Proj::Index, f("a")]), &p(0, vec![Proj::Index, f("a")])));
    assert!(overlaps(&p(0, vec![]), &p(0, vec![Proj::Elem(1)])));
    assert!(!overlaps(&p(0, vec![f("a")]), &p(0, vec![f("b")])));
    assert!(!overlaps(&p(0, vec![Proj::Elem(0)]), &p(0, vec![Proj::Elem(1)])));
    assert!(!overlaps(&p(0, vec![]), &p(1, vec![])));
}

/// The second-class values (memo 2.6, §5.3, §5.4; S-217): a `Span` from a
/// borrow binds at a borrow row (`let`, `for`), and the name stays
/// second-class: stored, a `var`, a `Span` of an `inout` parameter or of an
/// owned row, a `move` of one, are E0710 at the value placed there.
#[test]
fn a_span_binds_at_a_borrow_row_only() {
    let src = "pub fn bound(input: [Span[F32]; 2], xs: Span[F32], n: U32) -> U32 {
  let ch = input[0]
  let half = xs.slice(0, n)
  for c in input { let m = rd(c) }
  rd(ch) + rd(half) + ch.len() + input[1].len()
}
pub fn stored(input: [Span[F32]; 2]) {
  let ch = input[0]
  let p = (ch, 1)
}
pub fn var_(xs: Span[F32]) {
  var s = xs
}
pub fn of_inout(inout xs: Span[F32], n: U32) {
  let half = xs.slice(0, n)
}
pub fn owned_row(input: [Span[F32]; 2]) {
  let (l, r) = (input[0], input[1])
}
pub fn moved(input: [Span[F32]; 2]) {
  let ch = move input[0]
}
pub fn whole(input: [Span[F32]; 2]) {
  for c in move input {}
}
pub fn returned() {
  let g = fn(x: Span[F32]) { x }
}
pub fn move_arg(xs: Span[F32]) {
  keep(move xs)
}
";
    assert_eq!(fixes(src), bare(Code::E0710, &[9, 12, 15, 18, 21, 24, 27, 30]));
}

/// R-334: a generated `Out` is not counted second-class until W7-03 makes
/// `Rendered` apart from it (`render` returns the type `Out`, and its result
/// binds, §11.6): it is an Affine value of the table of §5.2 (R-325's
/// `let k = o` of an `inout` one is E0711 with no candidate, R-117). A
/// borrow binds the `Span` field of a borrowed one (S-788).
#[test]
fn a_generated_value_is_affine_until_w7_03() {
    let src = "pub fn bound(o: pair.Out) {
  let k = o
}
pub fn of_inout(inout o: pair.Out) {
  let k = o
}
pub fn field(o: pair.Out) -> U32 {
  let l = o.l
  rd(l) + l.len() + o.r.len() + rd(o.r)
}
pub fn stored(o: pair.Out) {
  var p = (o, 1)
}
pub fn move_arg(o: pair.Out) {
  keep(move o)
}
pub fn returned() {
  let g = fn(o: pair.Out) { o }
}
pub flow gain(x: F32 at sample) -> F32 at sample { x }
pub fn rendered() -> F32 uses {Alloc} {
  let xs: [F32; 2] = [1.0, 2.0]
  let o = gain.render(gain.Config {}, gain.Params {}, xs, 48000.0)
  let p = move o
  p.out[0]
}
";
    assert_eq!(fixes(src), bare(Code::E0711, &[5, 12, 15, 18]));
}

/// §5.3: an anonymous function that captures stands at an argument only;
/// one with no capture is a first-class value.
#[test]
fn a_closure_that_captures_stands_at_an_argument() {
    let src = "pub fn bound(k: U32) {
  let g = fn(i: U32) -> U32 { k * i }
}
pub fn argument(k: U32) -> U32 {
  apply(fn(i: U32) -> U32 { k * i })
}
pub fn plain() -> U32 {
  let g = fn(i: U32) -> U32 { i }
  apply(g)
}
pub fn var_(k: U32) {
  var g = fn(i: U32) -> U32 { k * i }
}
pub fn returned(k: U32) -> fn(U32) -> U32 {
  fn(i: U32) -> U32 { k * i }
}
";
    assert_eq!(fixes(src), bare(Code::E0710, &[2, 12, 15]));
}

/// Review of U2a, finding 1 (§5.3): the elements of a planar literal at a
/// borrowed argument stand at the argument: not moved, used after.
#[test]
fn a_planar_literal_at_an_argument_borrows_its_elements() {
    let src = "pub fn owned() uses {Alloc} {
  let a = mk()
  let b = mk()
  planes([a, b])
  take(move a)
  let n = b.len()
}
pub fn borrowed(a: Buf[F32], b: Buf[F32]) {
  planes([a, b])
}
pub fn not_planar() uses {Alloc} {
  let a = mk()
  take_all([a, mk()])
}
";
    let (_, moved) = seen(src);
    assert_eq!(
        fixes(src),
        [(Code::E0711, 13, vec![("add `move`".to_string(), "take_all([move a, mk()])".to_string())])]
    );
    assert_eq!(moved, BTreeSet::from(["a".to_string()]));
}

/// S-784, S-786 (§9.1, §5.2): the operand of `?` is consumed with no mark:
/// an owned Affine local moves (E0704 after, and in the next iteration of a
/// loop), a borrowed or `inout` one is E0711 with no candidate (by the kind
/// of the whole type), a Dup one and a value that is no place are fine.
#[test]
fn the_operand_of_try_is_consumed() {
    let src = "pub fn twice() -> Result[U32, U32] uses {Alloc} {
  let r = mkr()
  let b = r?
  let c = r?
  Ok(b.len())
}
pub fn after() -> Result[U32, U32] uses {Alloc} {
  let r = mkr()
  let b = r?
  let p = (r, 1)
  Ok(b.len())
}
pub fn borrowed(r: Result[Buf[F32], U32]) -> Result[U32, U32] uses {Alloc} {
  let b = r?
  Ok(b.len())
}
pub fn inout_(inout r: Result[Buf[F32], U32]) -> Result[U32, U32] uses {Alloc} {
  let b = r?
  Ok(b.len())
}
pub fn err_affine(r: Result[U32, Buf[F32]]) -> Result[U32, Buf[F32]] uses {Alloc} {
  let n = r?
  Ok(n)
}
pub fn dup(r: Result[U32, U32]) -> Result[U32, U32] {
  let a = r?
  let b = r?
  Ok(a + b)
}
pub fn call() -> Result[U32, U32] uses {Alloc} {
  let b = mkr()?
  Ok(b.len())
}
pub fn looped(n: U32) -> Result[U32, U32] uses {Alloc} {
  let r = mkr()
  for i in 0 ..< n {
    let b = r?
  }
  Ok(0)
}
";
    let (diags, moved) = seen(src);
    let e0711 = (Code::E0711, false);
    assert_eq!(diags, [at(4, MOVED), at(10, MOVED), at(14, e0711), at(18, e0711), at(22, e0711), at(37, BY_LOOP)]);
    assert_eq!(fixes(src).iter().filter(|f| !f.2.is_empty()).count(), 0);
    let (pkg, mut a) = analyzed(&format!("{PRELUDE}{src}"));
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let rules = a.diagnostics[before..].iter().filter(|d| d.code == Code::E0711 && d.span.file == FileId(0));
    assert!(rules.map(|d| d.notes.len()).eq([1, 1, 1]), "a note to read it with `match`");
    assert_eq!(moved, BTreeSet::from(["r".to_string()]));
}

/// The message of each diagnostic the new stage reports for `body`.
fn messages(body: &str) -> Vec<String> {
    let src = format!("{PRELUDE}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    a.diagnostics[before..].iter().filter(|d| d.span.file == FileId(0)).map(|d| d.message.clone()).collect()
}

/// S-789: "assign it before the loop ends" is said of a binding that can be
/// written only.
#[test]
fn the_note_of_a_move_in_a_previous_iteration() {
    let lets = messages(
        "pub fn t(n: U32) uses {Alloc} {
  let b = mk()
  for i in 0 ..< n { take(move b) }
}
",
    );
    let vars = messages(
        "pub fn t(n: U32) uses {Alloc} {
  var b = mk()
  for i in 0 ..< n { take(move b) }
}
",
    );
    assert_eq!(lets, ["`b` is moved here in a previous iteration of the loop (§5.2)"]);
    assert_eq!(vars, ["`b` is moved here in a previous iteration of the loop; assign it before the loop ends (§5.2)"]);
}

/// R-198: one message for `move` on a value that is no place, in the types
/// stage (`let y = move mk()`) and in the modes stage (`take(move mk())`).
#[test]
fn one_message_for_a_move_on_no_place() {
    let modes = messages("pub fn t() uses {Alloc} {\n  take(move mk())\n}\n");
    let src = format!("{PRELUDE}pub fn t() uses {{Alloc}} {{\n  let y = move mk()\n}}\n");
    let parsed = onsa_syntax::parse(FileId(0), &src);
    let modules = vec![crate::Module { segments: vec!["main".into()], file: FileId(0), text: src.clone(), parsed }];
    let a = crate::analyze(&crate::Package::new("t", modules, vec![crate::flow_tests::std_package()]));
    let types: Vec<_> = (a.diagnostics.iter()).filter(|d| d.code == Code::E0711).map(|d| d.message.clone()).collect();
    assert_eq!(modes, [crate::body::MOVE_NEEDS_A_PLACE]);
    assert_eq!(types, [crate::body::MOVE_NEEDS_A_PLACE]);
}

/// A `var` declared in a block of a loop and left by `break` (memo 1.3:
/// `forget` at the end of its block, `revive` at its declaration, `join` at
/// the exit): live at each iteration, gone after the loop; a move of an
/// outer binding on the path of the `break` is seen after the loop.
#[test]
fn a_var_of_a_block_left_by_break() {
    let src = "pub fn t(n: U32) uses {Alloc} {
  var i: U32 = 0
  while i < n {
    var v = mk()
    if i == 1 {
      take(move v)
      break
    }
    take(move v)
    i = i + 1
  }
}
pub fn u(n: U32) uses {Alloc} {
  let b = mk()
  var i: U32 = 0
  while i < n {
    var v = mk()
    if i == 1 {
      take(move b)
      break
    }
    take(move v)
    i = i + 1
  }
  let k = b.len()
}
";
    assert_eq!(diags(src), [at(25, MOVED)]);
}

/// S-217: a `for` or `match` head (a borrow row) on a place of an `inout`
/// parameter binds no `Span` (E0710 at the value); one that binds none (`_`,
/// the elements of a `Span`) is fine, and so is one on a borrow (§5.3, §5.4).
#[test]
fn a_head_on_an_inout_parameter_binds_no_span() {
    let src = "pub fn for_arr(inout xs: [Span[F32]; 2]) {
  for s in xs { let n = rd(s) }
}
pub fn match_span(inout xs: Span[F32]) -> U32 {
  match xs { s => rd(s) }
}
pub fn match_idx(inout xs: [Span[F32]; 2]) -> U32 {
  match xs[0] { s => rd(s) }
}
pub fn match_view(inout xs: Span[F32], n: U32) -> U32 {
  match xs.slice(0, n) { s => rd(s) }
}
pub fn wild(inout xs: Span[F32]) -> U32 {
  match xs { _ => 1 }
}
pub fn elements(inout xs: Span[F32], n: U32) -> F32 {
  var t: F32 = 0.0
  for v in xs { t = t + v }
  for v in xs.slice(0, n) { t = t + v }
  t
}
pub fn borrowed(xs: [Span[F32]; 2], n: U32) -> U32 {
  for s in xs { let m = rd(s) }
  match xs[0].slice(0, n) { s => rd(s) }
}
";
    assert_eq!(fixes(src), bare(Code::E0710, &[2, 5, 8, 11]));
}

/// S-784: the note of `?` is of an element of an array and of a borrowed or
/// `inout` Affine place, not of a field of an owned value (S-85, W4-09).
#[test]
fn the_note_of_try_on_a_field() {
    let src = "pub struct W { r: Result[Buf[F32], U32] }
pub fn field(move w: W) -> Result[U32, U32] uses {Alloc} {
  let a = w.r?
  Ok(a.len())
}
pub fn element(move w: [Result[Buf[F32], U32]; 2]) -> Result[U32, U32] uses {Alloc} {
  let a = w[0]?
  Ok(a.len())
}
";
    let (pkg, mut a) = analyzed(&format!("{PRELUDE}{src}"));
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let notes: Vec<_> = (a.diagnostics[before..].iter())
        .filter(|d| d.span.file == FileId(0))
        .map(|d| (d.code, d.notes.len()))
        .collect();
    assert_eq!(notes, [(Code::E0711, 0), (Code::E0711, 1)]);
}
