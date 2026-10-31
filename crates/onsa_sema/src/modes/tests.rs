//! The unit tests of the modes stage (W4-07): the flow of the moves (U1),
//! the table of consumption (U2), the calls (U3a), the writes (U3b) and the
//! captures (U4) (§5.1, §5.2, §5.4, §7), from sources parsed in memory. Each
//! runs the whole analysis, then `check_all` once more or the walk of one
//! body, and reads only what that adds.

use std::collections::BTreeSet;

use onsa_diag::{Code, FileId, Span, Stage};
use onsa_syntax::ast::ExprId;

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
/// the modes in it fails the test: the stage would not read the body.
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

/// The walk of the function `name` in `src`, before the one diagnostic of
/// the body is chosen (its index of §7 made by `Walker::new`), and what `f`
/// reads of it, its syntax tree and its root.
fn walked<R>(src: &str, name: &str, f: impl FnOnce(&Walker<'_>, &onsa_syntax::ast::Ast, ExprId) -> R) -> R {
    let (pkg, a) = analyzed(src);
    let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == name).expect("the function");
    let root = crate::body::root_of(&a, id).expect("a body");
    let ast = &crate::module_of_def(&pkg, &a, id).expect("its module").parsed.ast;
    let mut w = Walker::new(&a, (ast, src), (&a.names[&id], &a.bodies[&id], root), Vec::new());
    w.expr(&mut Run::new(), root, Pos::Return);
    f(&w, ast, root)
}

/// What the stage reports for the functions `body` after [`PRELUDE`]:
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
/// and `binding_heading_loop_run.onsa`.
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
    let stale = |n| Status::Stale { changes: std::collections::BTreeMap::from([(n, at(n))]) };
    entry.set(l(2), stale(2));
    entry.set(l(4), stale(4));
    let mut back = Delta::start();
    back.revive(l(1));
    back.set(l(1), Status::Moved { at: at(5), via_loop: false });
    back.revive(l(2));
    back.set(l(3), stale(3));
    back.set(l(4), stale(6));
    back.set(l(0), Status::Moved { at: at(7), via_loop: false });
    let plain = |d: &Delta| {
        (0..5)
            .map(|i| {
                d.status(l(i)).map(|s| match s {
                    Status::Moved { at, .. } => Status::Moved { at: *at, via_loop: false },
                    s => s.clone(),
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
    // Of two stale, the changes of both (S-803).
    assert_eq!(
        head.status(l(4)),
        Some(&Status::Stale { changes: std::collections::BTreeMap::from([(4, at(4)), (6, at(6))]) })
    );
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
        walked(&src, "deep", |w, ast, root| {
            let (mut nodes, mut todo) = (0, vec![root]);
            while let Some(e) = todo.pop() {
                nodes += 1;
                todo.extend(ast.sub_exprs(e));
            }
            (w.m.visits, nodes, w.m.loops.len())
        })
    };
    let (visits, nodes, loops) = onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
    assert_eq!(loops, DEPTH);
    assert!(visits <= 2 * nodes, "{visits} visits of {nodes} expressions");
}

/// A diagnostic by its code and its line, and each of its candidates by its
/// title and that line after its edits.
type Found = (Code, usize, Vec<(String, String)>);

/// What the stage reports for `body` after [`PRELUDE`]: each diagnostic
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
/// a Dup one is copied. `take(b)` is in `the_carried_forms_of_calls`.
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

/// §5.2: an owned value is not moved out of an element (E0711), marked or
/// not; a field of it is taken out, and its root moves (S-85); a Dup one is
/// copied and leaves its root.
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
    assert_eq!(fixes(src), bare(Code::E0711, &[2, 5]));
    assert_eq!(seen(src).1, BTreeSet::from(["h".to_string()]));
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
/// field, a Shared value); at a head and a return the mark is kept, where a
/// value is put it is E0703 too (S-795, its words).
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
    let expected = [
        remove(3, "tk(n)"),
        remove(6, "tk(n)"),
        remove(9, "tk(t.0)"),
        remove(12, "ts(s)"),
        remove(16, "let t = (n, 1)"),
    ];
    assert_eq!(fixes(src), expected);
    let said = messages("pub fn kept(n: U32) -> U32 {\n  let t = (move n, 1)\n  t.0\n}\n");
    assert_eq!(said, ["`n` is Copy, so it is copied; `move` here moves nothing (§5.2)"]);
}

/// R-198: `move` on a value that is no place is E0711 at any position (the
/// modes stage's, the types stage does not ask): a call, a literal, a
/// constant, a block, an `if`, on a `move` argument and a `for` head. It
/// moves nothing. The candidate removes it, and of a block and an `if` at a
/// consuming position writes it on the owned Affine tails (S-807).
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
    let fix = |l: usize, title: &str, line: &str| (Code::E0711, l, vec![(title.to_string(), line.to_string())]);
    let (remove, tails) = ("remove `move`", "write `move` on the tails");
    let expected = [
        fix(2, remove, "take(mk())"),
        fix(5, remove, "tk(1)"),
        fix(8, remove, "tk(K)"),
        fix(12, tails, "take({ move b })"),
        fix(17, tails, "take(if k { move b } else { mk() })"),
        fix(20, remove, "for x in make_array() {}"),
    ];
    assert_eq!(fixes(src), expected);
    assert_eq!(moved, BTreeSet::from(["b".to_string()]));
}

/// R-198's candidate (S-807, §5.2): at a consuming position (a head, where a
/// value is put, a `move` argument) the `move` goes onto each owned Affine
/// tail (a path of fields too, before its parentheses), at a borrowed
/// argument and a return it goes only; a Dup tail takes none; a borrowed
/// Affine tail, and an element at a consuming position, leave no candidate.
/// Each, applied, leaves no diagnostic of the stage (§18.1), so it stops.
#[test]
fn the_candidates_of_a_move_on_no_place() {
    let src = "pub fn own(c: Bool, move x: Buf[F32]) -> U32 uses {Alloc} {
  let z = move if c { x } else { mk() }
  z.len()
}
pub fn value(move x: Buf[F32]) -> U32 uses {Alloc} {
  let t = (move { x }, 1)
  t.1
}
pub fn arm(c: Bool, move x: Buf[F32], move h: Holder) uses {Alloc} {
  take(move match c { true => (x), false => h.buf })
}
pub fn borrowed_arg(c: Bool, move x: Buf[F32], move y: Buf[F32]) -> U32 uses {Alloc} {
  len_of(move if c { x } else { y })
}
pub fn returned(c: Bool, move x: Buf[F32]) -> Buf[F32] uses {Alloc} {
  move if c { x } else { mk() }
}
pub fn dup(c: Bool, n: U32) -> U32 {
  let z = move if c { n } else { 1 }
  z
}
pub fn exits(c: Bool, move x: Buf[F32]) uses {Alloc} {
  take(move if c { x } else { return })
}
pub fn borrowed_tail(c: Bool, x: Buf[F32]) uses {Alloc} {
  take(move if c { x } else { mk() })
}
pub fn element(c: Bool, move xs: [Buf[F32]; 2]) uses {Alloc} {
  take(move if c { xs[0] } else { mk() })
}
pub fn element_read(c: Bool, move xs: [Buf[F32]; 2]) -> U32 uses {Alloc} {
  len_of(move if c { xs[0] } else { mk() })
}
pub fn element_returned(c: Bool, move xs: [Buf[F32]; 2]) -> Buf[F32] uses {Alloc} {
  move if c { xs[0] } else { mk() }
}
pub fn commented(c: Bool, move x: Buf[F32]) uses {Alloc} {
  take(move if c { ( // c
    x // d
  ) } else { mk() })
}
";
    let fix = |l: usize, title: &str, line: &str| (Code::E0711, l, vec![(title.to_string(), line.to_string())]);
    let (remove, tails) = ("remove `move`", "write `move` on the tails");
    let expected = [
        fix(2, tails, "let z = if c { move x } else { mk() }"),
        fix(6, tails, "let t = ({ move x }, 1)"),
        fix(10, tails, "take(match c { true => move (x), false => move h.buf })"),
        fix(13, remove, "len_of(if c { x } else { y })"),
        fix(16, remove, "if c { x } else { mk() }"),
        fix(19, remove, "let z = if c { n } else { 1 }"),
        fix(23, tails, "take(if c { move x } else { return })"),
        (Code::E0711, 26, Vec::new()),
        (Code::E0711, 29, Vec::new()),
        fix(32, remove, "len_of(if c { xs[0] } else { mk() })"),
        // The break side of U3: an element taken at a return, a comment in the parentheses.
        (Code::E0711, 35, Vec::new()),
        (Code::E0711, 38, Vec::new()),
    ];
    assert_eq!(call_fixes(src), expected);
    each_fix_clears(src);
}

/// S-605, S-343: a `move` on a tail where no value is consumed is E0703, with
/// the candidate that removes it: an operand, a borrowed argument.
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
    let remove = |l: usize, line: &str| (Code::E0703, l, vec![("remove `move`".to_string(), line.to_string())]);
    assert_eq!(fixes(src), [remove(2, "let x = ({ n }) + 1"), remove(7, "len_of(if k { b } else { mk() })")]);
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
    let lines: Vec<_> = walked(&src, "t", |w, _, _| {
        (w.m.found.iter())
            .map(|d| (d.code, src[PRELUDE.len()..d.span.start as usize].matches('\n').count() + 1))
            .collect()
    });
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
    use super::place::{Deps, Place, Proj};
    let overlaps = |a: &Place, b: &Place| Deps::default().meets(a, b);
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

/// The message of each diagnostic the stage reports for `body`.
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

/// R-198: one message for `move` on a value that is no place, of the modes
/// stage only (`analyzed` fails on one of the types stage), at an argument
/// (`take(move mk())`) and at a `let` (`let y = move mk()`).
#[test]
fn one_message_for_a_move_on_no_place() {
    let modes = messages(
        "pub fn t() uses {Alloc} {\n  take(move mk())\n}\npub fn u() uses {Alloc} {\n  let y = move mk()\n}\n",
    );
    assert_eq!(modes, [crate::body::MOVE_NEEDS_A_PLACE; 2]);
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
/// `inout` Affine place; a field of an owned value is taken out (S-85).
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
    assert_eq!(notes, [(Code::E0711, 1)]);
}

/// The types of the calls of U3a: a struct whose methods take `self` in
/// each mode, and a function of an `inout` parameter.
const CALLEES: &str = "pub struct W { b: Buf[F32] }
impl W {
  pub fn peek(self) -> U32 { 1 }
  pub fn poke(inout self) {}
  pub fn eat(move self) -> U32 uses {Alloc} { 1 }
  pub fn put(self, move b: Buf[F32]) uses {Alloc} {}
  pub fn m(self, xs: [Span[F32]; 2]) {}
}
pub fn io(inout x: Buf[F32]) {}
";

/// [`fixes`] of [`CALLEES`] and `body`, by the lines of `body`.
fn call_fixes(body: &str) -> Vec<Found> {
    let skip = CALLEES.matches('\n').count();
    let found = fixes(&format!("{CALLEES}{body}"));
    found.into_iter().map(|(c, l, f)| (c, l - skip, f)).collect()
}

/// §18.1: each candidate of [`CALLEES`] and `body`, applied alone, leaves
/// no error before the modes stage and one diagnostic fewer of the new one.
fn each_fix_clears(body: &str) {
    let body = format!("{CALLEES}{body}");
    let src = format!("{PRELUDE}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let found: Vec<_> = a.diagnostics[before..].iter().filter(|d| d.span.file == FileId(0)).cloned().collect();
    for f in found.iter().flat_map(|d| d.fixes.iter()) {
        let mut text = src.clone();
        for e in f.edits().iter().rev() {
            text.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
        }
        assert_eq!(diags(&text[PRELUDE.len()..]).len(), found.len() - 1, "{}", f.title());
    }
}

/// A candidate by its title and its line after its edits.
fn fix(title: &str, line: &str) -> Vec<(String, String)> {
    vec![(title.to_string(), line.to_string())]
}

/// Memo 2.5, §5.2: the mark of an argument against the mode of its
/// parameter, the nine cells; the position is the parameter's, so each
/// candidate leaves no error the call had not. `inout` on a `move`
/// parameter is removed for a Dup value only (an Affine place: no one fix).
#[test]
fn the_marks_against_the_modes() {
    let src = "pub fn fine() uses {Alloc} {
  var c = mk()
  let n: U32 = 1
  let k = len_of(c)
  io(inout c)
  tk(n)
  take(move c)
}
pub fn borrow_inout(inout c: Buf[F32]) -> U32 {
  len_of(inout c)
}
pub fn borrow_move(c: Buf[F32]) -> U32 {
  len_of(move c)
}
pub fn inout_none(inout c: Buf[F32]) {
  io(c)
}
pub fn inout_move(inout c: Buf[F32]) {
  io(move c)
}
pub fn move_inout_dup(n: U32) {
  tk(inout n)
}
pub fn move_inout_affine() uses {Alloc} {
  var c = mk()
  take(inout c)
}
pub fn move_none() uses {Alloc} {
  let c = mk()
  take(c)
}
pub fn move_move_dup(n: U32) {
  tk(move n)
}
";
    let e0703 = |l: usize, f: Vec<(String, String)>| (Code::E0703, l, f);
    let expected = [
        e0703(10, fix("remove `inout`", "len_of(c)")),
        e0703(13, fix("remove `move`", "len_of(c)")),
        e0703(16, fix("add `inout`", "io(inout c)")),
        e0703(19, fix("replace `move` with `inout`", "io(inout c)")),
        e0703(22, fix("remove `inout`", "tk(n)")),
        e0703(26, Vec::new()),
        e0703(30, fix("add `move`", "take(move c)")),
        e0703(33, fix("remove `move`", "tk(n)")),
    ];
    assert_eq!(call_fixes(src), expected);
    each_fix_clears(src);
}

/// Memo 2.5: what each callee takes, by a missing `move` (E0703) on each: a
/// function, a method (and its `move self` receiver, consumed with no
/// mark), a function value, a generic function; a builtin method borrows;
/// a constructor takes elements (E0711, consumed). `move` on a borrowed
/// parameter of each is E0703 too.
#[test]
fn what_each_callee_takes() {
    let src = "pub fn method() uses {Alloc} {
  let w = W { b: mk() }
  let b = mk()
  w.put(b)
}
pub fn value(g: fn(move Buf[F32]) -> U32) -> U32 uses {Alloc} {
  let b = mk()
  g.(b)
}
pub fn generic() uses {Alloc} {
  let b = mk()
  keep(b)
}
pub fn builtin(xs: Buf[F32], i: U32) -> U32 {
  let o = xs.get(move i)
  0
}
pub fn variant() -> Option[Buf[F32]] uses {Alloc} {
  let b = mk()
  Some(b)
}
pub fn by_mark(g: fn(Buf[F32]) -> U32, b: Buf[F32]) -> U32 {
  g.(move b)
}
";
    let add = |l: usize, code: Code, line: &str| (code, l, fix("add `move`", line));
    let expected = [
        add(4, Code::E0703, "w.put(move b)"),
        add(8, Code::E0703, "g.(move b)"),
        add(12, Code::E0703, "keep(move b)"),
        (Code::E0703, 15, fix("remove `move`", "let o = xs.get(i)")),
        add(20, Code::E0711, "Some(move b)"),
        (Code::E0703, 23, fix("remove `move`", "g.(b)")),
    ];
    assert_eq!(call_fixes(src), expected);
    each_fix_clears(src);
}

/// §5.2: the `!` of a call. An `inout self` method needs it (E0713), a user
/// one and a builtin one; a method of `self` does not (E0714). Each
/// candidate is the one fix. (A constructor is NEW's.)
#[test]
fn the_bang_of_a_call() {
    let src = "pub fn user() uses {Alloc} {
  var w = W { b: mk() }
  w.poke()
}
pub fn builtin(inout xs: Buf[F32]) {
  xs.fill(0.0)
}
pub fn marked(inout xs: Buf[F32]) uses {Alloc} {
  var w = W { b: mk() }
  w.poke!()
  xs.fill!(0.0)
}
pub fn not_inout(w: W) -> U32 {
  w.peek!()
}
";
    let expected = [
        (Code::E0713, 3, fix("add `!`", "w.poke!()")),
        (Code::E0713, 6, fix("add `!`", "xs.fill!(0.0)")),
        (Code::E0714, 14, fix("remove `!`", "w.peek()")),
    ];
    assert_eq!(call_fixes(src), expected);
    each_fix_clears(src);
}

/// S-785, S-786 (§5.2, §9.1): a `move self` receiver, the builtin `unwrap`
/// of `Option` and `Result` and a user's method, is consumed with no mark:
/// an owned Affine one moves (E0704 after, and in the next iteration), a
/// borrowed or `inout` one is E0711 with no candidate, a Dup one is copied.
#[test]
fn a_move_self_receiver_is_consumed() {
    let src = "pub fn twice() -> U32 uses {Alloc} {
  let w = mko()
  let x = w.unwrap()
  let y = w.unwrap()
  x.len()
}
pub fn result() -> U32 uses {Alloc} {
  let r = mkr()
  let x = r.unwrap()
  let p = (r, 1)
  x.len()
}
pub fn borrowed(w: Option[Buf[F32]]) -> U32 {
  let x = w.unwrap()
  x.len()
}
pub fn inout_(inout w: Option[Buf[F32]]) -> U32 {
  let x = w.unwrap()
  x.len()
}
pub fn dup(w: Option[U32], r: Result[U32, U32]) -> U32 {
  w.unwrap() + w.unwrap() + r.unwrap()
}
pub fn looped(n: U32) uses {Alloc} {
  let w = mko()
  for i in 0 ..< n {
    let x = w.unwrap()
  }
}
pub fn user() -> U32 uses {Alloc} {
  let v = W { b: mk() }
  let a = v.eat()
  v.peek()
}
pub fn user_borrowed(v: W) -> U32 uses {Alloc} {
  v.eat()
}
";
    let skip = CALLEES.matches('\n').count();
    let (diags, moved) = seen(&format!("{CALLEES}{src}"));
    let diags: Vec<_> = diags.into_iter().map(|(c, l, v)| (c, l - skip, v)).collect();
    let e0711 = (Code::E0711, false);
    let expected =
        [at(4, MOVED), at(10, MOVED), at(14, e0711), at(18, e0711), at(27, BY_LOOP), at(33, MOVED), at(36, e0711)];
    assert_eq!(diags, expected.map(|(c, l, v)| (c, l, v)));
    assert_eq!(call_fixes(src).iter().filter(|f| !f.2.is_empty()).count(), 0);
    let names = ["r", "v", "w"].map(String::from);
    assert_eq!(moved, BTreeSet::from(names));
}

/// The forms carried to U3a: an element of a constructor is consumed (a
/// `Span` is E0710, R-325; a Dup one marked `move` is E0703, S-795); `take(b)` of an `inout` Affine `b` is E0711 with no candidate
/// (R-117); a planar literal at a borrowed parameter of a method and of a
/// generic function; the tails of
/// an `if` at a `move` parameter (§5.2); a place moved and borrowed in one
/// call, E0702 whatever the order (§5.2, S-787; U4a, was E0704 from the left).
#[test]
fn the_carried_forms_of_calls() {
    let src = "pub fn span(xs: Span[F32]) -> U32 {
  let k = Some(xs)
  0
}
pub fn dup_marked(n: U32) -> Option[U32] {
  Some(move n)
}
pub fn inout_arg(inout b: Buf[F32]) uses {Alloc} {
  take(b)
}
pub fn planar(w: W, a: Buf[F32], b: Buf[F32]) {
  w.m([a, b])
}
pub fn tails(c: Bool) uses {Alloc} {
  let a = mk()
  let b = mk()
  take(if c { move a } else { move b })
}
pub fn two(move x: Buf[F32]) uses {Alloc} {
  w2(move x, x)
}
pub fn w2(move x: Buf[F32], y: Buf[F32]) uses {Alloc} {}
pub fn gp[T: Copy](xs: [Span[T]; 2]) {}
pub fn generic(a: Buf[F32], b: Buf[F32]) {
  gp([a, b])
}
";
    let skip = CALLEES.matches('\n').count();
    let (diags, moved) = seen(&format!("{CALLEES}{src}"));
    let lines: Vec<_> = diags.into_iter().map(|(c, l, _)| (c, l - skip)).collect();
    assert_eq!(lines, [(Code::E0710, 2), (Code::E0703, 6), (Code::E0711, 9), (Code::E0702, 20)]);
    assert_eq!(call_fixes(src).iter().filter(|f| !f.2.is_empty()).count(), 1);
    assert_eq!(moved, BTreeSet::from(["a", "b", "x"].map(String::from)));
}

/// §18.1: of a callee the walk does not know (here its record removed, as
/// of a value of the error type), the marks and the moves are not checked.
#[test]
fn a_callee_not_known_checks_nothing() {
    let mut src = String::from(PRELUDE);
    src.push_str(
        "pub fn t() uses {Alloc} {
  let b = mk()
  take(b)
  take(move b)
  take(b)
}
",
    );
    let (pkg, mut a) = analyzed(&src);
    let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == "t").expect("t");
    a.bodies.get_mut(&id).expect("a body").targets.retain(|_, t| !matches!(t, crate::body::Target::Fn { .. }));
    let before = a.diagnostics.len();
    let moved = check_all(&pkg, &mut a);
    assert!(a.diagnostics[before..].iter().all(|d| d.span.file != FileId(0)));
    assert!(!moved.contains_key(&id));
}

/// Each diagnostic the stage reports for [`CALLEES`] and `body` (after
/// [`PRELUDE`]), by its code, its line in `body` and its message, and each
/// of its candidates by the line its first edit is on, after its edits
/// (trimmed; R-161's edits the `let`, not the line of the write).
fn writes(body: &str) -> Vec<(Code, usize, String, Vec<String>)> {
    let src = format!("{PRELUDE}{CALLEES}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let start = PRELUDE.len() + CALLEES.len();
    let line = |at: u32| src[start..at as usize].matches('\n').count() + 1;
    (a.diagnostics[before..].iter())
        .filter(|d| d.span.file == FileId(0))
        .map(|d| {
            let fixed = (d.fixes.iter()).map(|f| {
                let mut text = src.clone();
                for e in f.edits().iter().rev() {
                    text.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
                }
                let skip = src[..start].matches('\n').count();
                text.lines().nth(skip + line(f.edits()[0].span.start) - 1).unwrap_or_default().trim().to_string()
            });
            (d.code, line(d.span.start), d.message.clone(), fixed.collect())
        })
        .collect()
}

/// Memo 2.4's table (§5.1, §5.2, §5.4): the E0701 of a write to a place
/// that cannot be changed says what its root is (of a partial view, its
/// base's, R-31); the words of the write, by what writes.
#[test]
fn the_places_that_cannot_be_changed() {
    let src = "pub struct V { n: U32 }
impl V {
  pub fn s(self) {
    self.n = 1
  }
}
pub fn param(b: U32) {
  b = 2
}
pub fn closure_param() -> U32 {
  apply(fn(x: U32) -> U32 {
    x = 1
    x
  })
}
pub fn let_owned() uses {Alloc} {
  let b = mk()
  b = mk()
}
pub fn let_static() {
  let k = 1
  bump(inout k)
}
pub fn borrow_let(h: Holder) uses {Alloc} {
  let c = h.buf
  c.fill!(0.0)
}
pub fn borrow_for(xs: [Buf[F32]; 2]) uses {Alloc} {
  for c in xs { c = mk() }
}
pub fn borrow_arm(o: Option[U32]) {
  match o { Some(v) => { v = 1 }, None => {} }
}
pub fn owned_for() uses {Alloc} {
  for c in make_array() { c = mk() }
}
pub fn owned_arm() uses {Alloc} {
  match mko() { Some(c) => { c = mk() }, None => {} }
}
pub fn ios(inout xs: Span[F32]) {}
pub fn view_of_borrowed(xs: Span[F32]) {
  ios(inout xs.slice(0, 1))
}
pub fn view_receiver(xs: Span[F32]) {
  xs.slice(0, 1).fill!(0.0)
}
pub fn bump(inout n: U32) {}
";
    let (assign, inout, bang) = ("cannot assign", "cannot pass as `inout`", "cannot call an `inout self` method");
    let expected = [
        (4, assign, "`self` is borrowed; declare the method with `inout self`"),
        (8, assign, "`b` is a borrowed parameter; declare it `inout b`"),
        (12, assign, "`x` is a borrowed parameter; declare it `inout x`"),
        (18, assign, "`b` is immutable (`let`); declare it with `var`"),
        (22, inout, "`k` is immutable (`let`); declare it with `var`"),
        (26, bang, "`c` is a borrow binding (§5.4), read-only"),
        (29, assign, "`c` is a borrow binding (§5.4), read-only"),
        (32, assign, "`v` is a borrow binding (§5.4), read-only"),
        (35, assign, "`c` is a `for` variable, read-only"),
        (38, assign, "`c` is a `match` binding, read-only"),
        // A partial view writes its base (W4-08 U2, R-31): by what its root is.
        (42, inout, "`xs` is a borrowed parameter; declare it `inout xs`"),
        (45, bang, "`xs` is a borrowed parameter; declare it `inout xs`"),
    ];
    let found = writes(src);
    assert_eq!(found.len(), expected.len(), "{found:?}");
    for ((code, line, message, fixes), (l, how, why)) in found.iter().zip(expected) {
        assert_eq!((*code, *line), (Code::E0701, l), "{message}");
        assert!(message.starts_with(how) && message.contains(why), "{message}");
        // R-161's candidate: of the two `let`s that can be `var` only.
        assert_eq!(fixes.len(), usize::from(l == 18 || l == 22), "{message}");
    }
}

/// R-161 (memo 2.4): `var` for the `let` of the place written, the one fix
/// when the `let` binds the name alone and `var` takes its value with no
/// error: of a Copy borrow, an owned value, a static value, at an
/// assignment, an `inout` argument and a `!` receiver. Applied, every write
/// to the binding passes (§18.1).
#[test]
fn the_candidate_that_writes_var() {
    let src = "pub fn copy_borrow(h: Holder) -> U32 {
  let n = h.n
  n = 2
  n = 3
  n
}
pub fn owned() uses {Alloc} {
  let b = mk()
  io(inout b)
  b = mk()
  b.fill!(0.0)
}
pub fn static_value() -> U32 {
  let k = 1
  k = 2
  k
}
pub fn shared(s: Str) -> U32 uses {Alloc} {
  let t = s
  t = \"x\"
  t.len()
}
";
    let to_var = |l: usize, line: &str| (Code::E0701, l, vec![line.to_string()]);
    let found: Vec<_> = writes(src).into_iter().map(|(c, l, _, f)| (c, l, f)).collect();
    let expected =
        [to_var(3, "var n = h.n"), to_var(9, "var b = mk()"), to_var(15, "var k = 1"), to_var(20, "var t = s")];
    assert_eq!(found, expected);
    each_fix_clears(src);
}

/// R-161's conditions (memo 2.4): no candidate for a split `let`, a binding
/// of a `for` or `match` head, a write in an anonymous function that
/// captures the `let`, a borrowed Affine value (`var` would consume it,
/// E0711), a second-class one, and a `let` another binding derives from
/// (after `var`, the write would leave it unusable, §7). (A `let` with an
/// attribute is an error of the signatures stage in a function, before.)
#[test]
fn no_candidate_where_var_is_not_the_fix() {
    let src = "pub fn split() uses {Alloc} {
  let (a, c) = (mk(), 1)
  a = mk()
}
pub fn captured() -> U32 {
  let k = 1
  apply(fn(x: U32) -> U32 {
    k = x
    k + x
  })
}
pub fn borrowed_affine(h: Holder) uses {Alloc} {
  let b = h.buf
  b = mk()
}
pub fn second_class(xs: Span[F32]) {
  let s = xs
  ios(inout s)
}
pub fn derived() -> U32 uses {Alloc} {
  let o = mko()
  match o {
    Some(b) => {
      o = None
      len_of(b)
    },
    None => 0,
  }
}
pub fn ios(inout xs: Span[F32]) {}
";
    let found: Vec<_> = writes(src).into_iter().map(|(c, l, _, f)| (c, l, f.len())).collect();
    assert_eq!(found, [3, 8, 14, 18, 24].map(|l| (Code::E0701, l, 0)));
}

/// All the walk of the function `t` in `body` (after [`PRELUDE`] and
/// [`CALLEES`]) found, before the one of the body is chosen: each by its
/// code, its line in `body` and the text it is at.
fn all_found(body: &str) -> Vec<(Code, usize, String)> {
    let found = walk_found(&format!("{PRELUDE}{CALLEES}"), body);
    found.into_iter().map(|(c, l, t, _, _)| (c, l, t)).collect()
}

/// §5.1, §5.2: a `let` is E0701 at an `inout` argument and at the receiver
/// of an `inout self` method. The E0701 stands at the argument whatever its
/// mark (the position is the parameter's, U3a): it is there before the
/// candidate of E0703 that adds `inout`, so that candidate makes no error.
#[test]
fn a_let_at_an_inout_argument_and_a_receiver() {
    let src = "pub fn argument() uses {Alloc} {
  let x = mk()
  io(inout x)
}
pub fn receiver() uses {Alloc} {
  let x = mk()
  x.fill!(0.0)
}
pub fn method() uses {Alloc} {
  let w = W { b: mk() }
  w.poke!()
}
";
    let found: Vec<_> = writes(src).into_iter().map(|(c, l, _, f)| (c, l, f)).collect();
    let to_var = |l: usize, line: &str| (Code::E0701, l, vec![line.to_string()]);
    assert_eq!(found, [to_var(3, "var x = mk()"), to_var(7, "var x = mk()"), to_var(11, "var w = W { b: mk() }")]);
    let unmarked = "pub fn t() uses {Alloc} {\n  let x = mk()\n  io(x)\n}\n";
    let x = |code| (code, 3, "x".to_string());
    assert_eq!(all_found(unmarked), [x(Code::E0703), x(Code::E0701)]);
    let marked = unmarked.replace("io(x)", "io(inout x)");
    assert_eq!(all_found(&marked), [x(Code::E0701)]);
}

/// §5.2, S-789: a `var` moved and assigned as a whole is live again, on a
/// branch and in a loop; a write to a part of it is a use (E0704), and so
/// are an `inout` argument and a `!` receiver, which assign nothing whole.
#[test]
fn a_write_revives_a_whole_var_only() {
    let src = "pub fn whole(c: Bool) uses {Alloc} {
  var b = mk()
  if c {
    take(move b)
    b = mk()
  }
  while c {
    take(move b)
    b = mk()
  }
  take(move b)
}
pub fn th(move h: Holder) uses {Alloc} {}
pub fn field() uses {Alloc} {
  var h = Holder { buf: mk(), n: 1 }
  th(move h)
  h.buf = mk()
}
pub fn element() uses {Alloc} {
  var xs = make_array()
  take_all(move xs)
  xs[0] = mk()
}
pub fn inout_arg() uses {Alloc} {
  var b = mk()
  take(move b)
  io(inout b)
  take(move b)
}
pub fn bang() uses {Alloc} {
  var b = mk()
  take(move b)
  b.fill!(0.0)
  take(move b)
}
pub fn io(inout x: Buf[F32]) {}
";
    assert_eq!(diags(src), [at(17, MOVED), at(22, MOVED), at(27, MOVED), at(33, MOVED)]);
}

/// §7, S-42, R-118: changing the scrutinee of a borrowed `match` in an arm
/// leaves the bindings of the place it changed, and those derived from them
/// (§5.4), unusable (E0704): by an assignment, an `inout` argument and a
/// move, on one path of an `if` too. W4-16 U1b's F4: a `let` of the tails of
/// a `match` derives from each (S-604). Another field does not overlap.
#[test]
fn a_change_of_the_place_a_binding_derives_from() {
    let src = "pub fn tko(move o: Option[Buf[F32]]) uses {Alloc} {}
pub fn ioo(inout o: Option[Buf[F32]]) {}
pub fn in_arm() -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      o = None
      len_of(b)
    },
    None => 0,
  }
}
pub fn after_match(d: Buf[F32]) -> U32 uses {Alloc} {
  var o: Option[Buf[F32]] = Some(Buf.zeroed(2))
  let t = match o { Some(b) => b, None => d }
  o = None
  t.len()
}
pub fn disjoint_field() -> U32 uses {Alloc} {
  var p: (Buf[F32], Buf[F32]) = (Buf.zeroed(1), Buf.zeroed(2))
  match p {
    (a, c) => {
      p.1 = Buf.zeroed(3)
      a.len()
    },
  }
}
pub fn same_field() -> U32 uses {Alloc} {
  var p: (Buf[F32], Buf[F32]) = (Buf.zeroed(1), Buf.zeroed(2))
  match p {
    (a, c) => {
      p.0 = Buf.zeroed(3)
      a.len()
    },
  }
}
pub fn derived_twice(c: Bool) -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      let t = b
      let u = t
      if c { ioo(inout o) }
      len_of(u)
    },
    None => 0,
  }
}
pub fn moved(h: Holder) -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      tko(move o)
      len_of(b)
    },
    None => 0,
  }
}
";
    let stale = (Code::E0704, false);
    assert_eq!(diags(src), [at(8, stale), at(17, stale), at(33, stale), at(44, stale), at(54, stale)]);
}

/// §7: a Copy binding holds the value it was bound to, and the bindings of
/// a `for` are not in the index (review 5: a change of the iterated place is
/// E0715, which changes nothing). An E0701 write changes nothing, so it
/// leaves no E0704 at the head of a loop before it (review 2).
#[test]
fn what_a_change_leaves_usable() {
    let src = "pub fn copy() -> U32 uses {Alloc} {
  var p: (U32, Buf[F32]) = (1, mk())
  match p {
    (n, _) => {
      p.0 = 2
      n
    },
  }
}
pub fn erroneous(o: Option[Buf[F32]], d: Buf[F32], c: Bool) -> U32 uses {Alloc} {
  let t = match o { Some(b) => b, None => d }
  var n: U32 = 0
  while c {
    n = len_of(t)
    o = None
  }
  n
}
";
    assert_eq!(diags(src), [at(15, (Code::E0701, false))]);
    let a_for = "pub fn t() -> U32 uses {Alloc} {
  var xs = make_array()
  var n: U32 = 0
  for b in xs {
    xs[0] = mk()
    n = len_of(b)
  }
  n
}
";
    assert_eq!(diags(a_for), [at(5, (Code::E0715, false))]);
}

/// S-604: a `let` of the tails of an `if` derives from the place of each,
/// so a change of either leaves it unusable.
#[test]
fn a_binding_of_tails_derives_from_each() {
    let src = "pub fn t(c: Bool) -> U32 uses {Alloc} {
  var o = mko()
  var q = mko()
  match o {
    Some(a) => match q {
      Some(b) => {
        let r = if c { a } else { b }
        q = None
        len_of(r)
      },
      None => 0,
    },
    None => 0,
  }
}
";
    assert_eq!(diags(src), [at(9, (Code::E0704, false))]);
}

/// §5.3, memo 2.7 (U4a): at the first read of a value an anonymous function
/// captures, in this order: an `inout` parameter (of any kind) or an Affine
/// value is one E0712 of the function, naming the first such read (S-722);
/// a second-class value E0710 (R-331, S-217: an unbound `Span` parameter, a
/// bound element and a view); a Shared one E0200 (R-85 (5), S-80: by its
/// type, a static value and a `T` with no bound too). A Copy one is copied.
/// The first read in a loop is the walk's that reports, not the summary's.
#[test]
fn what_an_anonymous_function_captures() {
    let src = "pub fn inout_first(inout k: U32, b: Buf[F32]) -> U32 {
  apply(fn(x: U32) -> U32 { k + b.len() + x })
}
pub fn affine_first(inout k: U32, b: Buf[F32]) -> U32 {
  apply(fn(x: U32) -> U32 { b.len() + k + x })
}
pub fn inout_copy(inout n: U32) -> U32 {
  apply(fn(x: U32) -> U32 { n + x })
}
pub fn span_param(xs: Span[F32]) -> U32 {
  apply(fn(n: U32) -> U32 { xs.len() + n })
}
pub fn bound_element(xs: [Span[F32]; 2]) -> U32 {
  let ch = xs[0]
  apply(fn(n: U32) -> U32 { ch.len() + n })
}
pub fn bound_view(xs: Span[F32]) -> U32 {
  let half = xs.slice(0, 1)
  apply(fn(n: U32) -> U32 { n + half.len() })
}
pub fn shared(s: Str) -> U32 {
  apply(fn(n: U32) -> U32 { s.len() + n })
}
pub fn static_value() -> U32 {
  let s = \"abc\"
  apply(fn(n: U32) -> U32 { s.len() + n })
}
pub fn see[T](t: T) -> U32 { 1 }
pub fn unbounded[T](t: T) -> U32 {
  apply(fn(n: U32) -> U32 { see(t) + n })
}
pub fn copied(k: U32, h: Holder) -> U32 {
  let m = h.n
  apply(fn(n: U32) -> U32 { k + m + n })
}
pub fn moved_capture() -> U32 uses {Alloc} {
  let b = mk()
  apply(fn(n: U32) -> U32 {
    take(move b)
    n
  })
}
pub fn in_a_loop(xs: Span[F32], c: Bool) -> U32 {
  apply(fn(n: U32) -> U32 {
    var k = n
    while c { k = k + xs.len() }
    k
  })
}
";
    let found: Vec<_> = writes(src).into_iter().map(|(c, l, m, f)| (c, l, m, f.len())).collect();
    let lines: Vec<_> = found.iter().map(|(c, l, _, n)| (*c, *l, *n)).collect();
    let (e0712, e0710, e0200) = ((Code::E0712, 0), (Code::E0710, 0), (Code::E0200, 0));
    let expected = [(e0712, 2), (e0712, 5), (e0712, 8), (e0710, 11), (e0710, 15), (e0710, 19), (e0200, 22)];
    let expected = [&expected[..], &[(e0200, 26), (e0200, 30), (e0712, 38), (e0710, 46)]].concat();
    assert_eq!(lines, expected.iter().map(|&((c, n), l)| (c, l, n)).collect::<Vec<_>>());
    let says = |i: usize, s: &str| assert!(found[i].2.contains(s), "{}", found[i].2);
    says(0, "`k` is an `inout` parameter");
    says(1, "`b` is Affine");
    says(2, "`n` is an `inout` parameter");
    says(3, "cannot be captured");
    says(6, "the capture of a Shared value");
    says(9, "`b` is Affine");
}

/// R-25 (§5.3): a value an anonymous function captures is read-only in it,
/// whatever its binding: an assignment, an `inout` argument and a `!`
/// receiver, of a `let` and a `var`, of a field and an element, from a
/// nested function, are E0701 with R-25's words and no candidate (`var`
/// leaves it). The function's own bindings are written.
#[test]
fn a_captured_value_is_not_written() {
    let src = "pub struct P { x: U32, y: U32 }
impl P {
  pub fn inc(inout self) {}
}
pub fn bump(inout z: U32) {}
pub fn assign_var() -> U32 {
  var y: U32 = 1
  apply(fn(n: U32) -> U32 {
    y = 3
    n + y
  })
}
pub fn assign_let() -> U32 {
  let y: U32 = 1
  apply(fn(n: U32) -> U32 {
    y = n
    n
  })
}
pub fn field() -> U32 {
  var p = P { x: 1, y: 2 }
  apply(fn(n: U32) -> U32 {
    p.x = n
    p.y
  })
}
pub fn element() -> U32 {
  var xs: [U32; 2] = [1, 2]
  apply(fn(n: U32) -> U32 {
    xs[0] = n
    n
  })
}
pub fn inout_arg(move k: U32) -> U32 {
  apply(fn(n: U32) -> U32 {
    bump(inout k)
    n
  })
}
pub fn bang() -> U32 {
  let p = P { x: 1, y: 2 }
  apply(fn(n: U32) -> U32 {
    p.inc!()
    n
  })
}
pub fn nested() -> U32 {
  apply(fn(n: U32) -> U32 {
    var k = n
    k = k + 1
    bump(inout k)
    apply(fn(m: U32) -> U32 {
      k = m
      m
    }) + k
  })
}
";
    let found = writes(src);
    let lines: Vec<_> = found.iter().map(|(c, l, _, f)| (*c, *l, f.len())).collect();
    assert_eq!(lines, [9, 16, 23, 30, 36, 43, 53].map(|l| (Code::E0701, l, 0)));
    let verbs = ["cannot assign", "cannot assign", "cannot assign", "cannot assign", "cannot pass as `inout`"];
    for ((_, _, message, _), verb) in found.iter().zip(verbs.into_iter().chain(["cannot call", "cannot assign"])) {
        assert!(
            message.starts_with(verb) && message.ends_with("is captured by a closure, read-only (§5.3)"),
            "{message}"
        );
    }
    // An `inout` argument with no mark: R-25's E0701 stands at the argument
    // before the candidate of E0703 adds the mark (U3a), so it leaves it.
    let unmarked = "pub fn bump(inout z: U32) {}
pub fn t() -> U32 {
  var k: U32 = 1
  apply(fn(n: U32) -> U32 {
    bump(k)
    n
  })
}
";
    let k = |code| (code, 5, "k".to_string());
    assert_eq!(all_found(unmarked), [k(Code::E0703), k(Code::E0701)]);
}

/// The callees of [`overlapping`]'s cases.
const OVERLAPS: &str = "pub fn ii(inout x: Buf[F32], inout y: Buf[F32]) {}
pub fn ib(inout x: Buf[F32], y: Buf[F32]) {}
pub fn bi(x: Buf[F32], inout y: Buf[F32]) {}
pub fn im(inout x: Buf[F32], move y: Buf[F32]) uses {Alloc} {}
pub fn bm(x: Buf[F32], move y: Buf[F32]) uses {Alloc} {}
pub fn mb(move x: Buf[F32], y: Buf[F32]) uses {Alloc} {}
pub fn mbh(move h: Holder, y: Buf[F32]) uses {Alloc} {}
pub fn inm(inout n: U32, move b: Buf[F32]) uses {Alloc} {}
pub fn ibn(inout b: Buf[F32], n: U32) {}
pub fn ip(inout p: (Buf[F32], Buf[F32]), a: Buf[F32]) {}
pub fn fo(b: Buf[F32], inout o: Option[Buf[F32]]) -> U32 { b.len() }
pub fn go(inout o: Option[Buf[F32]], b: Buf[F32]) -> U32 { b.len() }
pub fn gn(inout o: Option[Buf[F32]], n: U32) -> U32 { n }
pub fn fk(k: U32, inout o: Option[U32]) -> U32 { k }
pub fn gk(inout o: Option[U32], k: U32) -> U32 { k }
pub fn fs(s: Str, inout o: Option[Str]) -> U32 { 1 }
pub fn gs(inout o: Option[Str], s: Str) -> U32 { 1 }
pub fn mks() -> Option[Str] { Some(\"abc\") }
pub struct Two { a: Option[Buf[F32]], c: Option[Buf[F32]] }
pub fn mk2() -> Two uses {Alloc} { Two { a: mko(), c: mko() } }
";

/// Each diagnostic the stage reports for [`OVERLAPS`] and `body`, by
/// its code and its line in `body`, and the lines of its notes.
fn overlapping(body: &str) -> Vec<(Code, usize, Vec<usize>)> {
    let src = format!("{PRELUDE}{CALLEES}{OVERLAPS}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let start = PRELUDE.len() + CALLEES.len() + OVERLAPS.len();
    let line = |s: Span| src[start..s.start as usize].matches('\n').count() + 1;
    (a.diagnostics[before..].iter())
        .filter(|d| d.span.file == FileId(0))
        .map(|d| (d.code, line(d.span), d.notes.iter().filter_map(|n| n.span.map(line)).collect()))
        .collect()
}

/// E0702 (§5.2, S-787): of one call, two places that overlap, one passed as
/// `inout` or `move`, whatever the order: twice `inout`, `inout` and
/// borrowed, `move` and anything; an Affine field's path moved stands for
/// its root (`inm(inout h.n, move h.buf)`); a receiver. At the later one,
/// noted at the earlier one. `mb(move x, x)` and `mbh(move h, h.buf)` are
/// the E0702 only, not the E0704 of the use after the move it holds.
#[test]
fn the_places_of_one_call_overlap() {
    let src = "pub fn twice() uses {Alloc} {
  var x = mk()
  ii(inout x, inout x)
}
pub fn inout_borrow() uses {Alloc} {
  var x = mk()
  ib(inout x, x)
}
pub fn borrow_inout() uses {Alloc} {
  var x = mk()
  bi(x, inout x)
}
pub fn inout_move() uses {Alloc} {
  var x = mk()
  im(inout x, move x)
}
pub fn borrow_move() uses {Alloc} {
  var x = mk()
  bm(x, move x)
}
pub fn move_borrow() uses {Alloc} {
  var x = mk()
  mb(move x, x)
}
pub fn move_path(move h: Holder) uses {Alloc} {
  mbh(move h, h.buf)
}
pub fn field_moved() uses {Alloc} {
  var h = Holder { buf: mk(), n: 1 }
  inm(inout h.n, move h.buf)
}
pub fn elements() uses {Alloc} {
  var xs = make_array()
  ii(inout xs[0], inout xs[1])
}
pub fn receiver(move w: W) uses {Alloc} {
  w.put(move w.b)
}
pub fn builtin(inout xs: [Span[F32]; 2]) {
  xs[0].copy_from!(xs[1])
}
";
    let found = overlapping(src);
    let lines = [3, 7, 11, 15, 19, 23, 26, 30, 34, 37, 40];
    assert_eq!(found, lines.map(|l| (Code::E0702, l, vec![l])));
    let messages = writes(&format!("{OVERLAPS}{src}"));
    let says = |i: usize, s: &str| assert!(messages[i].2.contains(s), "{}", messages[i].2);
    says(0, "`x` is passed as `inout` twice in one call");
    says(1, "`x` is passed as `inout` and borrowed in the same call");
    says(2, "`x` is passed as `inout` and borrowed in the same call");
    says(3, "`x` is passed as `inout` and as `move` in the same call");
    says(4, "`x` is passed as `move` and borrowed in the same call");
    says(9, "`w` is passed as `move` and borrowed in the same call");
}

/// §5.2: places that do not overlap: other fields, a value made of the
/// place (`ibn(inout b, b.len())`), other locals, a Copy field at a `move`
/// parameter (not its root, S-787); and a value moved then read to make another
/// (`mb(move x, x.len())`) stays the E0704 of the walk from the left (§3.5).
#[test]
fn the_places_of_one_call_that_do_not_overlap() {
    let src = "pub fn fields() uses {Alloc} {
  var h = Holder { buf: mk(), n: 1 }
  ibn(inout h.buf, h.n)
}
pub fn value_of_it() uses {Alloc} {
  var b = mk()
  ibn(inout b, b.len())
  b.fill!(b[0] * 2.0)
}
pub fn other_locals() uses {Alloc} {
  var x = mk()
  var y = mk()
  im(inout x, move y)
}
pub fn fl(move b: Buf[F32], n: U32) uses {Alloc} {}
pub fn moved_then_read() uses {Alloc} {
  var x = mk()
  fl(move x, x.len())
}
pub fn mn(inout b: Buf[F32], move n: U32) {}
pub fn copy_field_moved() uses {Alloc} {
  var h = Holder { buf: mk(), n: 1 }
  mn(inout h.buf, h.n)
}
";
    assert_eq!(overlapping(src), [(Code::E0704, 18, vec![18])]);
}

/// S-801 (§5.2): a Dup value at a `move` parameter, and a Dup `move self`
/// receiver, is copied and counts as a read of its place, as at a borrowed
/// one: two reads do not overlap (`mmn(n, n)`, `bmn(n, n)`, a `Str` arm
/// binding twice, `p.plus(p.x)`); with an `inout` one it is E0702, noted
/// as copied (`imn(inout n, n)`).
#[test]
fn a_dup_value_at_a_move_parameter_is_a_read() {
    let src = "pub fn mmn(move a: U32, move b: U32) -> U32 { a + b }
pub fn bmn(a: U32, move b: U32) -> U32 { a + b }
pub fn imn(inout a: U32, move b: U32) { a = a + b }
pub fn sbm(s: Str, move t: Str) -> U32 { s.len() + t.len() }
pub struct Pt { x: U32, y: U32 }
impl Pt {
  pub fn plus(move self, k: U32) -> Pt {
    self.x = self.x + k
    self
  }
}
pub fn reads() -> U32 {
  var n: U32 = 1
  n = 2
  mmn(n, n) + bmn(n, n)
}
pub fn payload() -> U32 {
  var o = mks()
  o = mks()
  match o { Some(s) => sbm(s, s), None => 0 }
}
pub fn receiver() -> U32 {
  var p = Pt { x: 1, y: 2 }
  p.y = 3
  p.plus(p.x).x
}
pub fn inout_and_copy() -> U32 {
  var n: U32 = 1
  imn(inout n, n)
  n
}
";
    assert_eq!(overlapping(src), [(Code::E0702, 29, vec![29, 29])]);
    let messages = writes(&format!("{OVERLAPS}{src}"));
    assert!(messages[0].2.contains("`n` is passed as `inout` and borrowed"), "{}", messages[0].2);
}

/// S-796 (§5.2, §5.4): a borrow binding that is not Copy (of an arm, and
/// derived from one: a `let`, a nested `match`, an or-pattern, the tails of
/// an `if`) stands for the places it derives from, so with an `inout` of
/// that place it is E0702 whatever the order, noted at the earlier argument
/// and at the binding; of an `inout` parameter too, and of a Shared value.
/// An arm's place is the scrutinee's with the paths of tuples and structs,
/// a payload the whole value.
#[test]
fn a_borrow_binding_stands_for_its_place() {
    let src = "pub fn after() -> U32 uses {Alloc} {
  var o = mko()
  match o { Some(b) => fo(b, inout o), None => 0 }
}
pub fn before() -> U32 uses {Alloc} {
  var o = mko()
  match o { Some(b) => go(inout o, b), None => 0 }
}
pub fn derived() -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      let c = b
      go(inout o, c)
    },
    None => 0,
  }
}
pub fn inout_param(inout o: Option[Buf[F32]]) -> U32 {
  match o { Some(b) => fo(b, inout o), None => 0 }
}
pub fn shared() -> U32 {
  var o = mks()
  match o { Some(s) => gs(inout o, s), None => 0 }
}
pub fn tails(c: Bool, d: Buf[F32]) -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      let t = if c { b } else { d }
      fo(t, inout o)
    },
    None => 0,
  }
}
pub fn same_field() -> U32 uses {Alloc} {
  var w = mk2()
  match w.a { Some(b) => go(inout w.a, b), None => 0 }
}
pub fn whole() -> U32 uses {Alloc} {
  var p: (Buf[F32], Buf[F32]) = (mk(), mk())
  match p { (a, _) => { ip(inout p, a)
    0 } }
}
pub fn element(inout p: (Buf[F32], Buf[F32])) {
  match p { (a, _) => p.0.copy_from!(a) }
}
";
    let found = overlapping(src);
    let lines: Vec<_> = found.iter().map(|(c, l, _)| (*c, *l)).collect();
    assert_eq!(lines, [3, 7, 14, 20, 24, 31, 38, 42, 46].map(|l| (Code::E0702, l)));
    // Noted at the earlier argument and at the binding (`c` of `before`'s
    // second arm: the `let`).
    assert_eq!(found[1].2, [7, 7]);
    assert_eq!(found[2].2, [14, 13]);
}

/// S-796: what a borrow binding does not overlap: a Copy binding (it holds
/// its value, §5.4), another field, another element of a tuple; and a
/// value made of it (`gn(inout o, len_of(b))`), as the place it derives
/// from changes after the call (§7): a use after the call is E0704.
#[test]
fn what_a_borrow_binding_does_not_overlap() {
    let src = "pub fn copy() -> U32 {
  var n: Option[U32] = Some(1)
  match n { Some(k) => fk(k, inout n), None => 0 }
}
pub fn copy_before() -> U32 {
  var n: Option[U32] = Some(1)
  match n { Some(k) => gk(inout n, k), None => 0 }
}
pub fn other_field() -> U32 uses {Alloc} {
  var w = mk2()
  match w.a { Some(b) => fo(b, inout w.c), None => 0 }
}
pub fn other_element() uses {Alloc} {
  var p: (Buf[F32], Buf[F32]) = (mk(), mk())
  match p { (a, _) => ib(inout p.1, a) }
}
pub fn value_made() -> U32 uses {Alloc} {
  var o = mko()
  match o { Some(b) => gn(inout o, len_of(b)), None => 0 }
}
pub fn used_after() -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      let n = gn(inout o, len_of(b))
      n + len_of(b)
    },
    None => 0,
  }
}
";
    let lines: Vec<_> = overlapping(src).into_iter().map(|(c, l, _)| (c, l)).collect();
    assert_eq!(lines, [(Code::E0704, 26)]);
}

/// §7 (S-796): a direct argument changes its place after the call: the
/// receiver of a `!` and a `move` argument too (`w.sw!(Buf.zeroed(bb.len()))`
/// reads `bb` before).
#[test]
fn a_direct_argument_changes_its_place_after_the_call() {
    let src = "pub struct WB { b: Buf[F32] }
impl WB {
  pub fn sw(inout self, move b: Buf[F32]) uses {Alloc} {}
}
pub fn receiver() uses {Alloc} {
  var w = WB { b: mk() }
  match w { WB { b: bb } => w.sw!(Buf.zeroed(bb.len())) }
}
pub fn tko(move o: Option[Buf[F32]], n: U32) -> U32 uses {Alloc} { n }
pub fn moved() -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => {
      let n = tko(move o, len_of(b))
      n + len_of(b)
    },
    None => 0,
  }
}
";
    let lines: Vec<_> = overlapping(src).into_iter().map(|(c, l, _)| (c, l)).collect();
    assert_eq!(lines, [(Code::E0704, 15)]);
}

/// S-797 (§5.4, §7): a binding derived from another derives from its place
/// with the paths composed: after a change of `w.h.n`, `c = hh.buf` is
/// usable, and `hh.buf` too (S-803: a path of a binding is the place it
/// derives from, the steps composed), and `hh` whole is not; after a change
/// of `w.h.buf`, neither is.
#[test]
fn a_derived_binding_composes_the_paths() {
    let src = "pub struct Wrap { h: Holder, k: U32 }
pub fn io_n(inout n: U32) {}
pub fn other_field() -> U32 uses {Alloc} {
  var w = Wrap { h: Holder { buf: mk(), n: 1 }, k: 2 }
  match w {
    Wrap { h: hh, k: kk } => {
      let c = hh.buf
      io_n(inout w.h.n)
      len_of(c)
    },
  }
}
pub fn the_parent() -> U32 uses {Alloc} {
  var w = Wrap { h: Holder { buf: mk(), n: 1 }, k: 2 }
  match w {
    Wrap { h: hh, k: kk } => {
      let c = hh.buf
      io_n(inout w.h.n)
      len_of(hh.buf)
    },
  }
}
pub fn the_same_field() -> U32 uses {Alloc} {
  var w = Wrap { h: Holder { buf: mk(), n: 1 }, k: 2 }
  match w {
    Wrap { h: hh, k: kk } => {
      let c = hh.buf
      w.h.buf = mk()
      len_of(c)
    },
  }
}
pub fn use_h(h: Holder) -> U32 { 1 }
pub fn the_whole() -> U32 uses {Alloc} {
  var w = Wrap { h: Holder { buf: mk(), n: 1 }, k: 2 }
  match w {
    Wrap { h: hh, k: kk } => {
      let c = hh.buf
      io_n(inout w.h.n)
      use_h(hh)
    },
  }
}
";
    let lines: Vec<_> = overlapping(src).into_iter().map(|(c, l, _)| (c, l)).collect();
    assert_eq!(lines, [(Code::E0704, 29), (Code::E0704, 40)]);
}

/// The forms of S-796's table (`target/notes/87/s796/`) in U4a: a nested
/// `match`, an or-pattern, an `inout self` receiver in an `impl` (a Copy
/// field of a binding too: `self.upd!(v.n)`), a function value (the order
/// counts for nothing, `a_borrow_binding_stands_for_its_place`).
#[test]
fn the_forms_of_the_table_of_s796() {
    let src = "pub fn mkoo() -> Option[Option[Buf[F32]]] uses {Alloc} { Some(mko()) }
pub fn fo2(b: Buf[F32], inout o: Option[Option[Buf[F32]]]) -> U32 { b.len() }
pub fn nested() -> U32 uses {Alloc} {
  var o = mkoo()
  match o { Some(i) => match i { Some(b) => fo2(b, inout o), None => 0 }, None => 0 }
}
pub enum E { A(Buf[F32]), B(Buf[F32]), C }
pub fn ge(inout e: E, b: Buf[F32]) -> U32 { b.len() }
pub fn either() -> U32 uses {Alloc} {
  var e = E.A(mk())
  match e { E.A(b) | E.B(b) => ge(inout e, b), E.C => 0 }
}
pub struct S { v: Option[Holder] }
impl S {
  pub fn upd(inout self, n: U32) {}
  pub fn poke(inout self, b: Buf[F32]) {}
  pub fn copy_field(inout self) {
    match self.v { Some(v) => self.upd!(v.n), None => {} }
  }
  pub fn binding(inout self) {
    match self.v { Some(v) => self.poke!(v.buf), None => {} }
  }
}
pub fn value(fv: fn(Buf[F32], inout Option[Buf[F32]]) -> U32) -> U32 uses {Alloc} {
  var o = mko()
  match o { Some(b) => fv.(b, inout o), None => 0 }
}
";
    let lines: Vec<_> = overlapping(src).into_iter().map(|(c, l, _)| (c, l)).collect();
    assert_eq!(lines, [5, 11, 18, 21, 26].map(|l| (Code::E0702, l)));
}

/// The types and callees of the tests of S-803 (§7, U4b-1).
const S803: &str = "pub struct H2 { buf: Buf[F32], n: U32, m: U32, xs: [U32; 2], o: Option[Buf[F32]] }
pub struct W3 { h: H2, i: H2, k: U32 }
pub fn mkh() -> H2 uses {Alloc} { H2 { buf: mk(), n: 1, m: 2, xs: [1, 2], o: mko() } }
pub fn mkw() -> W3 uses {Alloc} { W3 { h: mkh(), i: mkh(), k: 3 } }
pub fn use_h(h: H2) -> U32 { 1 }
pub fn io_n(inout n: U32) {}
pub fn take3(move b: Buf[F32]) -> U32 uses {Alloc} { 1 }
pub fn fn3(h: H2, inout n: U32) {}
pub fn bm2(x: Buf[F32], move y: Buf[F32]) uses {Alloc} {}
";

/// What the stage reports for [`S803`] and `body`: each diagnostic by
/// its code, its line in `body`, the text it is at, its message and its
/// notes (the text each is at, and its message).
type Said = (Code, usize, String, String, Notes);

/// The notes of a diagnostic: the text each is at, and its message.
type Notes = Vec<(Option<String>, String)>;

fn said(body: &str) -> Vec<Said> {
    let src = format!("{PRELUDE}{S803}{body}");
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    check_all(&pkg, &mut a);
    let found = a.diagnostics[before..].iter().filter(|d| d.span.file == FileId(0));
    found.map(|d| said_of(&src, PRELUDE.len() + S803.len(), d)).collect()
}

/// The diagnostic `d` of `src` as [`Said`], its line from `start`.
fn said_of(src: &str, start: usize, d: &onsa_diag::Diagnostic) -> Said {
    let text = |s: Span| src[s.start as usize..s.end as usize].to_string();
    let line = src[start..d.span.start as usize].matches('\n').count() + 1;
    let notes = d.notes.iter().map(|n| (n.span.map(text), n.message.clone())).collect();
    (d.code, line, text(d.span), d.message.clone(), notes)
}

/// All the walk of the function `t` in `body` (after `prefix`) found,
/// before the one of the body is chosen, as [`Said`]: the walk of
/// [`walked`], which makes the index of §7.
fn walk_found(prefix: &str, body: &str) -> Vec<Said> {
    let src = format!("{prefix}{body}");
    walked(&src, "t", |w, _, _| w.m.found.iter().map(|d| said_of(&src, prefix.len(), d)).collect())
}

/// Each diagnostic of `body` by its code, its line and the text it is at.
fn said_at(body: &str) -> Vec<(Code, usize, String)> {
    said(body).into_iter().map(|(c, l, t, _, _)| (c, l, t)).collect()
}

/// S-803 (§7): after a change, a path of a binding is the place it derives
/// from with the steps composed, so a path that does not overlap the change
/// is usable: a field and a method's receiver, a Copy sibling, a hole; after
/// a change of an element; after a change in either branch; in a loop
/// before the change; through bindings derived from it (`let g`, tails of
/// an `if`); an element of an array of structs; after two changes. A head
/// reads the paths its patterns read (D1, D2, S-804): `_` none, the arms of
/// a `match` together; a variant at another place.
#[test]
fn a_path_that_does_not_overlap_the_change_is_usable() {
    let src = "pub fn fields() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => { w.h.n = 5
    len_of(hh.buf) + hh.m + hh.buf.len() } }
}
pub fn hole() -> Str uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => { w.h.n = 5
    \"{hh.m}\" } }
}
pub fn element() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => { w.h.xs[0] = 1
    len_of(hh.buf) } }
}
pub fn branches(c: Bool) -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    if c { w.h.n = 5 } else { w.h.m = 6 }
    len_of(hh.buf) } }
}
pub fn a_loop(c: Bool) -> U32 uses {Alloc} {
  var w = mkw()
  var n: U32 = 0
  match w { W3 { h: hh, i: _, k: _ } => {
    while c {
      n = n + len_of(hh.buf)
      w.h.n = 5
    }
    n } }
}
pub fn derived() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    let g = hh
    let g2 = g
    w.h.n = 5
    len_of(g2.buf) } }
}
pub fn tails(c: Bool) -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: ii, k: _ } => {
    let tt = if c { hh } else { ii }
    w.h.n = 5
    w.i.n = 6
    len_of(tt.buf) } }
}
pub fn array() -> U32 uses {Alloc} {
  var vs = [mkh(), mkh()]
  match vs[0] { hh => {
    vs[1].n = 5
    len_of(hh.buf) } }
}
pub fn two_changes() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    w.h.n = 5
    w.h.m = 6
    len_of(hh.buf) + hh.xs[0] } }
}
pub fn let_wild() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    w.h.n = 5
    let H2 { buf: bb, n: _, m: _, xs: _, o: _ } = hh
    len_of(bb) } }
}
pub fn match_wild() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    w.h.n = 5
    match hh { H2 { buf: bb, n: _, m: 1, xs: _, o: _ } => len_of(bb), H2 { buf: _, n: _, m: _, xs: _, o: None } => 1, _ => 0 } } }
}
pub fn match_path() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    w.h.n = 5
    match hh.buf { b2 => len_of(b2) } } }
}
pub fn variant_elsewhere() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    w.h.n = 5
    match hh.o { Some(b) => len_of(b), None => 0 } } }
}
";
    assert_eq!(said_at(src), []);
}

/// S-803 (§7): what overlaps the change is E0704 at the whole of the path
/// used: the field changed, an element of the array changed (two indexes
/// overlap, §5.2), the binding whole (an argument, `let g = hh`), a pattern
/// that binds or compares the field changed (D1, D2), the head's binding
/// whole, a variant at the place changed, the arms of a `match` together
/// (S-804), a hole; after a change of the parent and of a `!` receiver; in
/// the next iteration of a loop. An index in the path is walked before the
/// element is read (E1, §3.5). `take3(hh.buf)` is the E0711 of a borrow.
#[test]
fn a_path_that_overlaps_the_change_is_e0704() {
    let line = |b: &str| {
        format!(
            "pub fn t(c: Bool) -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => {{\n{b}\n  }} }}\n}}\n"
        )
    };
    // The body, the line of the E0704 in it (from 1) and the text it is at.
    let cases: &[(&str, usize, &str)] = &[
        ("    w.h.n = 5\n    hh.n", 2, "hh.n"),
        ("    w.h.xs[0] = 1\n    hh.xs[1]", 2, "hh.xs[1]"),
        ("    w.h.n = 5\n    use_h(hh)", 2, "hh"),
        ("    io_n(inout w.h.n)\n    let g = hh\n    use_h(g)", 2, "hh"),
        ("    w.h.n = 5\n    let H2 { buf: bb, n: nn, m: _, xs: _, o: _ } = hh\n    nn", 2, "hh"),
        ("    w.h.n = 5\n    match hh { H2 { buf: bb, n: 0, m: _, xs: _, o: _ } => 1, _ => 0 }", 2, "hh"),
        ("    w.h.n = 5\n    match hh { g => use_h(g) }", 2, "hh"),
        ("    w.h.o = None\n    match hh.o { Some(b) => len_of(b), None => 0 }", 2, "hh.o"),
        (
            "    w.h.n = 5\n    match hh { H2 { buf: bb, n: _, m: 0, xs: _, o: _ } => len_of(bb), H2 { buf: _, n: 0, m: _, xs: _, o: _ } => 1, _ => 0 }",
            2,
            "hh",
        ),
        ("    w.h = mkh()\n    len_of(hh.buf)", 2, "hh.buf"),
        ("    w.h.buf.fill!(0.0)\n    len_of(hh.buf)", 2, "hh.buf"),
        ("    var n: U32 = 0\n    while c {\n      n = n + hh.n\n      w.h.n = 5\n    }\n    n", 3, "hh.n"),
        ("    hh.xs[{ w.h.xs[0] = 1\n    0 }]", 1, "hh.xs[{ w.h.xs[0] = 1\n    0 }]"),
    ];
    for (b, n, text) in cases {
        assert_eq!(said_at(&line(b)), [(Code::E0704, 3 + n, text.to_string())], "{b}");
    }
    let s = "pub fn t() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => { w.h.n = 5
    take3(hh.buf) } }
}
";
    assert_eq!(said_at(s), [(Code::E0711, 4, "hh.buf".to_string())]);
    let hole = "pub fn t() -> Str uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => { w.h.n = 5
    \"{hh.n}\" } }
}
";
    assert_eq!(said_at(hole), [(Code::E0704, 4, "hh.n".to_string())]);
}

/// The texts of E0704 (§7, S-803): the path used as written (named by its
/// steps when a pattern reads it or it is on more than one line), the place
/// changed, noted where it changed and where the binding is bound; the note
/// with no place only when the path used ends before the place changed; a
/// head noted at the first element that reads the path (S-804).
#[test]
fn the_text_of_an_e0704_of_a_change() {
    let t = |b: &str| {
        let src = format!(
            "pub fn t() -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => {{\n    w.h.n = 5\n{b}\n  }} }}\n}}\n"
        );
        let found = said(&src);
        assert_eq!(found.len(), 1, "{found:?}");
        let (_, _, _, message, notes) = found.into_iter().next().unwrap_or_else(|| unreachable!());
        (message, notes)
    };
    let msg = |p: &str| {
        format!("`{p}` cannot be used after `w.h.n` changed: the place it borrows overlaps the changed place (§7)")
    };
    let note = |at: &str, m: &str| (Some(at.to_string()), m.to_string());
    let changed = note("w.h.n", "changed here");
    let bound = note("hh", "`hh` is bound here as a borrow of `w.h` (§5.4)");
    let rest = (None, "a path of `hh` that does not overlap `w.h.n` can still be used (§7)".to_string());
    assert_eq!(t("    hh.n"), (msg("hh.n"), vec![changed.clone(), bound.clone()]));
    assert_eq!(t("    use_h(hh)"), (msg("hh"), vec![changed.clone(), bound.clone(), rest]));
    let arms = "    match hh { H2 { buf: _, n: _, m: 0, xs: _, o: _ } => 1, H2 { buf: _, n: 0, m: _, xs: _, o: _ } => 2, _ => 0 }";
    let by = note("0", "read by this pattern");
    assert_eq!(t(arms), (msg("hh.n"), vec![changed.clone(), bound.clone(), by]));
    let multi = "pub fn t() -> U32 uses {Alloc} {\n  var w = mkw()\n  match w { W3 { h: hh, i: _, k: _ } => hh.xs[{ w.h.xs[0] = 1\n    0 }] }\n}\n";
    let (_, _, _, message, _) = said(multi).remove(0);
    let named =
        "`hh.xs[_]` cannot be used after `w.h.xs[0]` changed: the place it borrows overlaps the changed place (§7)";
    assert_eq!(message, named);
}

/// The texts of E0702 of a binding of the index (§5.2, S-796): the
/// arguments as written, noted where each binding is bound and at the
/// places it derives from directly (`or` between two; with no binding,
/// as before: `the_places_of_one_call_overlap`).
#[test]
fn the_text_of_an_e0702_of_a_binding() {
    let src = "pub fn t() uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => fn3(hh, inout w.h.n) }
}
";
    let (code, _, _, message, notes) = said(src).remove(0);
    assert_eq!(code, Code::E0702);
    assert_eq!(
        message,
        "`hh` is passed borrowed and `w.h.n` as `inout` in the same call; the places may overlap (§5.2)"
    );
    let note = |at: &str, m: &str| (Some(at.to_string()), m.to_string());
    assert_eq!(notes, [note("hh", "borrowed here"), note("hh", "`hh` is bound here as a borrow of `w.h` (§5.4)")]);
}

/// A place in the texts of E0704 and E0702 (§7, §5.2) is as written on
/// one line, else its name and path, an index `[_]`: the one rule of the
/// path used, the place changed, the source of a binding and an argument.
#[test]
fn a_place_on_more_than_one_line_is_named() {
    let index = "[if c {\n      0\n    } else {\n      1\n    }]";
    let changed = format!(
        "pub fn t(c: Bool) -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => {{\n    w.h.xs{index} = 1\n    use_h(hh)\n  }} }}\n}}\n"
    );
    let (_, _, _, message, notes) = said(&changed).remove(0);
    let stale = "cannot be used after `w.h.xs[_]` changed: the place it borrows overlaps the changed place (§7)";
    assert_eq!(message, format!("`hh` {stale}"));
    assert_eq!(notes[2].1, "a path of `hh` that does not overlap `w.h.xs[_]` can still be used (§7)");
    let source = format!(
        "pub fn t(c: Bool) -> U32 uses {{Alloc}} {{\n  var xs = make_array()\n  match xs{index} {{ b => {{\n    xs[0] = mk()\n    len_of(b)\n  }} }}\n}}\n"
    );
    let (_, _, _, message, notes) = said(&source).remove(0);
    assert_eq!(
        message,
        "`b` cannot be used after `xs[0]` changed: the place it borrows overlaps the changed place (§7)"
    );
    assert_eq!(notes[1].1, "`b` is bound here as a borrow of `xs[_]` (§5.4)");
    let argument = format!(
        "pub fn t(c: Bool) uses {{Alloc}} {{\n  var w = mkw()\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => fn3(hh, inout w.h.xs{index}) }}\n}}\n"
    );
    let (code, _, _, message, _) = said(&argument).remove(0);
    let both = "`hh` is passed borrowed and `w.h.xs[_]` as `inout` in the same call; the places may overlap (§5.2)";
    assert_eq!((code, message.as_str()), (Code::E0702, both));
}

/// §7, S-803: a change leaves unusable only the bindings in scope where it
/// is (one out of scope is declared again before any use), and the change
/// of a place is made once for all its positions: the judgment is that of
/// every binding. Each of many `match`es reads its own binding after its
/// change; a binding of a block that ended, or declared after the change,
/// or in the next iteration of a loop, is usable; one derived from a
/// binding out of scope there (`let b = { let a = w.h; a }`) is not. The
/// stage takes well under a second for 300 `match`es (W4-07 U4b-1's
/// review, finding 1: 0.5 s at 200).
#[test]
fn a_change_leaves_the_bindings_out_of_scope_as_they_are() {
    let arm = |k: usize| {
        format!("  match w {{ W3 {{ h: h{k}, i: _, k: _ }} => {{ w.h.n = {k}\n    acc = acc + h{k}.m }} }}\n")
    };
    let usable = format!(
        "pub fn t(c: Bool) -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  var acc: U32 = 0\n{}{}  match w {{ W3 {{ h: hh, i: _, k: _ }} => {{\n    {{ let g = hh\n      acc = acc + g.m }}\n    w.h.n = 3\n    match hh {{ H2 {{ buf: g2, n: _, m: _, xs: _, o: _ }} => {{ acc = acc + len_of(g2) }} }}\n  }} }}\n  w.h.n = 3\n  match w {{ W3 {{ h: h3, i: _, k: _ }} => {{ acc = acc + use_h(h3) }} }}\n  while c {{\n    match w {{ W3 {{ h: h4, i: _, k: _ }} => {{ acc = acc + use_h(h4)\n      w.h.n = 4 }} }}\n  }}\n  acc\n}}\n",
        arm(1),
        arm(2)
    );
    assert_eq!(said_at(&usable), []);
    let derived = |head: &str| {
        format!(
            "pub fn t() -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => {{\n    let b = {head}\n    w.h.n = 1\n    use_h(b)\n  }} }}\n}}\n"
        )
    };
    for head in ["{ let a = hh\n      a }", "match hh { a => a }"] {
        let lines = 6 + head.matches('\n').count();
        assert_eq!(said_at(&derived(head)), [(Code::E0704, lines, "b".to_string())], "{head}");
    }
    let mut many = String::from("pub fn t() -> U32 uses {Alloc} {\n  var w = mkw()\n  var acc: U32 = 0\n");
    (0..300).for_each(|k| many.push_str(&arm(k)));
    many.push_str("  acc\n}\n");
    let src = format!("{PRELUDE}{S803}{many}");
    let (pkg, mut a) = analyzed(&src);
    let (before, start) = (a.diagnostics.len(), std::time::Instant::now());
    check_all(&pkg, &mut a);
    let took = start.elapsed();
    assert_eq!(a.diagnostics.len(), before);
    assert!(took < std::time::Duration::from_secs(1), "{took:?}");
    let made = walked(&src, "t", |w, _, _| w.m.places.len());
    assert_eq!(made, 2, "a change of each of `w.h.n` and `acc`");
}

/// Memo 3 (W4-07 U4b-1's review, finding 3): a change reads the bindings
/// derived from its root only, so a write of another root changes nothing
/// for them, and a binding of two roots (`g`, from `hh` of `w` or from
/// `vi` of `v`) is unusable by a change of either where the paths overlap.
#[test]
fn a_change_of_another_root_leaves_a_binding_as_it_is() {
    let f = |b: &str| {
        format!(
            "pub fn t(c: Bool) -> U32 uses {{Alloc}} {{\n  var w = mkw()\n  var v = mkw()\n  var acc: U32 = 0\n  match w {{ W3 {{ h: hh, i: _, k: _ }} => match v {{ W3 {{ h: _, i: vi, k: _ }} => {{\n    let g = if c {{ hh }} else {{ vi }}\n{b}\n    acc\n  }} }} }}\n}}\n"
        )
    };
    let usable = "    acc = acc + 1\n    v.k = 2\n    acc = acc + g.n + hh.n\n    v.i.n = 3\n    acc = acc + len_of(g.buf) + hh.n";
    assert_eq!(said_at(&f(usable)), []);
    for (b, text) in [("    v.i.n = 3\n    acc = acc + g.n", "g.n"), ("    w.h.m = 3\n    acc = acc + g.m", "g.m")] {
        assert_eq!(said_at(&f(b)), [(Code::E0704, 8, text.to_string())], "{b}");
    }
}

/// Every walk of a unit test makes the index of §7 (`Walker::new`): the
/// helper that reads all the walk found sees an E0704 of §7 and an E0702
/// of a binding.
#[test]
fn a_walk_makes_its_index() {
    let body = "pub fn t() -> U32 uses {Alloc} {
  var w = mkw()
  match w { W3 { h: hh, i: _, k: _ } => {
    fn3(hh, inout w.h.n)
    w.h.n = 5
    use_h(hh)
  } }
}
";
    let codes: Vec<_> = all_said(&format!("{S803}{body}")).into_iter().map(|(c, t, _, _)| (c, t)).collect();
    assert_eq!(codes, [(Code::E0702, "w.h.n".to_string()), (Code::E0704, "hh".to_string())]);
}

/// Every diagnostic the walk of the function `t` of `body` (after
/// [`PRELUDE`]) found, before the one of the body is chosen: its code, the
/// text it is at, its message and its notes (the text each is at, and its
/// message).
fn all_said(body: &str) -> Vec<(Code, String, String, Notes)> {
    walk_found(PRELUDE, body).into_iter().map(|(c, _, t, m, n)| (c, t, m, n)).collect()
}

/// E0702 of two bindings of the index (§5.2, S-796, memo 3): each stands
/// for the places it derives from, the steps composed, along a chain of
/// sources of two; `t2` moved is a borrow (E0711) too.
#[test]
fn two_derived_bindings_overlap_by_their_places() {
    let types = "pub struct Q { buf: Buf[F32] }
pub struct P2 { a: Q, b: Q }
pub struct S3 { a: P2, b: P2, c: P2 }
pub fn bmq(x: Q, move y: Q) uses {Alloc} {}
";
    let body = |second: &str| {
        format!(
            "{types}pub fn t(c: Bool, s: S3) uses {{Alloc}} {{
  let t1 = if c {{ s.a }} else {{ s.b }}
  let t2 = if c {{ {second}.a }} else {{ {second}.b }}
  bmq(t1.a, move t2)
}}
"
        )
    };
    let found = all_said(&body("t1"));
    let codes: Vec<_> = found.iter().map(|(c, t, _, _)| (*c, t.as_str())).collect();
    assert_eq!(codes, [(Code::E0702, "t2"), (Code::E0711, "t2")]);
    let (_, _, message, notes) = &found[0];
    let expected = "`t1.a` is passed borrowed and `t2` as `move` in the same call; the places may overlap (§5.2)";
    assert_eq!(message, expected);
    let note = |at: &str, m: &str| (Some(at.to_string()), m.to_string());
    let t1 = note("t1", "`t1` is bound here as a borrow of `s.a` or `s.b` (§5.4)");
    let t2 = note("t2", "`t2` is bound here as a borrow of `t1.a` or `t1.b` (§5.4)");
    assert_eq!(notes, &[note("t1.a", "borrowed here"), t1, t2]);
    let apart = all_said(&body("s.c"));
    assert_eq!(apart.iter().map(|(c, _, _, _)| *c).collect::<Vec<_>>(), [Code::E0711]);
}

/// A chain of `depth` bindings from the borrowed parameter `s`, each from
/// the one before by the kind `kinds % 4` (then `kinds / 4` for the next):
/// the tails of an `if` (two sources), an or-pattern of a `match` (two),
/// a field, the payload of an `Option` (a `match`); the function `t`.
fn chain(depth: usize, mut kinds: u64) -> String {
    let mut src = String::new();
    for i in 0..depth {
        let n = if i + 1 == depth { "Buf[F32]".to_string() } else { format!("N{}", i + 1) };
        src.push_str(&format!("pub struct N{i} {{ a: {n}, b: {n}, o: Option[{n}] }}\n"));
    }
    src.push_str("pub fn t(c: Bool, t0: N0) -> U32 {\n");
    let mut close = String::new();
    for i in 1..depth {
        let (p, k) = (i - 1, kinds % 4);
        kinds /= 4;
        match k {
            0 => src.push_str(&format!("let t{i} = if c {{ t{p}.a }} else {{ t{p}.b }}\n")),
            1 => {
                src.push_str(&format!(
                    "match t{p} {{ N{p} {{ a: t{i}, b: _, o: _ }} | N{p} {{ a: _, b: t{i}, o: _ }} => {{\n"
                ));
                close.insert_str(0, "} }\n");
            }
            2 => src.push_str(&format!("let t{i} = t{p}.b\n")),
            _ => {
                src.push_str(&format!("match t{p}.o {{ Some(t{i}) => {{\n"));
                close.insert_str(0, "}, None => 0 }\n");
            }
        }
    }
    src.push_str("0\n");
    src.push_str(&close);
    src.push_str("}\n");
    src
}

/// The places the binding `l` stands for, made by the expansion U4a made
/// (the copy of its `resolve`, which grows as the product of the sources).
fn expanded(deps: &super::place::Deps, l: LocalId) -> Vec<super::place::Place> {
    let mut out = Vec::new();
    for s in deps.sources(l) {
        let from = match deps.indexed(s.place.root) {
            true => expanded(deps, s.place.root).iter().map(|q| q.then(&s.place.proj)).collect(),
            false => vec![s.place.clone()],
        };
        for q in from {
            if !out.contains(&q) {
                out.push(q);
            }
        }
    }
    out
}

/// Memo 3: the index answers as the expansion does, with U4a's `overlaps`
/// (the same root, the steps the same up to the shorter one): whether two
/// places meet (E0702), which bindings a change leaves unusable, whether a
/// path of one overlaps the change and ends before it (E0704 and its
/// note), on chains of depth 1 to 10 of each kind of step. On a large stack
/// (rules 3.4: a `match` in a `match`).
#[test]
fn the_index_answers_as_the_expansion() {
    use super::place::{Deps, Place, Proj};
    let overlaps = |a: &Place, b: &Place| a.root == b.root && a.proj.iter().zip(&b.proj).all(|(p, q)| p == q);
    let run = move || {
        let mut checked = 0;
        for depth in 1..=10 {
            for seed in [0x1B1B_1B1B_u64, 0xE4E4_E4E4, 0x3C3C_3C3C] {
                let src = format!("{PRELUDE}{}", chain(depth, seed >> (2 * (depth % 4))));
                let (pkg, a) = analyzed(&src);
                let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == "t").expect("t");
                let root = crate::body::root_of(&a, id).expect("a body");
                let ast = &crate::module_of_def(&pkg, &a, id).expect("its module").parsed.ast;
                let (names, info) = (&a.names[&id], &a.bodies[&id]);
                let deps = Deps::of_body((ast, names, info), root, |_| false);
                let locals = (0..info.locals.len() as u32).map(LocalId);
                let bound: Vec<LocalId> = locals.filter(|&l| deps.indexed(l)).collect();
                assert_eq!(bound.len(), depth - 1, "{src}");
                let s = LocalId(1); // `t0` (after `c`)
                assert!(!deps.indexed(s) && info.locals[1].name == "t0");
                let f = |n: &str| Proj::Field(n.to_string());
                // The places of `t0`: all of up to three steps of `a`, `b`, `o`, and longer ones.
                let mut paths: Vec<Vec<Proj>> = vec![vec![]];
                for _ in 0..3 {
                    let next: Vec<_> = (paths.iter())
                        .filter(|p| p.len() == paths.last().map_or(0, |l| l.len()))
                        .flat_map(|p| ["a", "b", "o"].map(|n| [p.clone(), vec![f(n)]].concat()))
                        .collect();
                    paths.extend(next);
                }
                for k in 4..=depth + 1 {
                    paths.push((0..k).map(|i| f(["b", "a"][i % 2])).collect());
                    paths.push(vec![f("b"); k]);
                }
                let roots: Vec<Place> = paths.iter().map(|p| Place { root: s, proj: p.clone() }).collect();
                let qs = [vec![], vec![f("a")], vec![f("b")], vec![f("o")], vec![f("b"), f("a")]];
                let uses: Vec<Place> =
                    bound.iter().flat_map(|&l| qs.iter().map(move |q| Place { root: l, proj: q.clone() })).collect();
                let made: std::collections::HashMap<LocalId, Vec<Place>> =
                    bound.iter().map(|&l| (l, expanded(&deps, l))).collect();
                let stands = |p: &Place| match made.get(&p.root) {
                    Some(e) => e.iter().map(|q| q.then(&p.proj)).collect(),
                    None => vec![p.clone()],
                };
                for w in &roots {
                    let change = deps.change(w);
                    for u in &uses {
                        let all = stands(u);
                        let hit: Vec<_> = all.iter().filter(|e| overlaps(e, w)).collect();
                        let want = (!hit.is_empty()).then(|| hit.iter().any(|e| e.proj.len() < w.proj.len()));
                        assert_eq!(change.reaches(u), want, "{u:?} after {w:?}\n{src}");
                        checked += 1;
                    }
                    for &l in &bound {
                        let want = stands(&Place { root: l, proj: vec![] }).iter().any(|e| overlaps(e, w));
                        assert_eq!(change.along.contains_key(&l), want, "{l:?} after {w:?}");
                    }
                }
                let short: Vec<&Place> = roots.iter().filter(|p| p.proj.len() <= 2).collect();
                for a in uses.iter().filter(|u| u.proj.len() <= 1) {
                    let xs = stands(a);
                    for b in uses.iter().chain(short.iter().copied()) {
                        let want = stands(b).iter().any(|y| xs.iter().any(|x| overlaps(x, y)));
                        assert_eq!(deps.meets(a, b), want, "{a:?} {b:?}\n{src}");
                        assert_eq!(deps.meets(b, a), want, "{b:?} {a:?}");
                        checked += 1;
                    }
                }
            }
        }
        checked
    };
    let checked = onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
    assert!(checked > 10_000, "{checked}");
}

/// Memo 3 (U4a's review, finding 1): a chain of 22 bindings of two sources
/// each (`gen_blow.py`'s form, 2^22 places expanded) from a `match` on an
/// `inout` parameter, a change, a use and an E0702 of its end: the stage
/// takes well under a second (U4a's took 15 s at 16).
#[test]
fn a_chain_of_two_sources_does_not_grow() {
    const D: usize = 24;
    let mut src = String::from(PRELUDE);
    for i in 0..D {
        let next = if i + 1 == D { "Buf[F32]".to_string() } else { format!("L{}", i + 1) };
        src.push_str(&format!("pub struct L{i} {{ a: {next}, b: {next} }}\n"));
    }
    src.push_str("pub fn io1(inout x: L1) {}\npub fn bi2(x: Buf[F32], inout y: L0) -> U32 { 1 }\n");
    src.push_str("pub fn t(c: Bool, inout s: L0) -> U32 uses {Alloc} {\n  match s { L0 { a: x0, b: y0 } => {\n");
    src.push_str("    let t1 = if c { x0.a } else { y0.b }\n");
    for i in 2..D - 1 {
        src.push_str(&format!("    let t{i} = if c {{ t{}.a }} else {{ t{}.b }}\n", i - 1, i - 1));
    }
    let last = D - 2;
    src.push_str(&format!(
        "    let n = bi2(t{last}.b, inout s)\n    io1(inout s.a)\n    n + len_of(t{last}.a)\n  }} }}\n}}\n"
    ));
    let (pkg, mut a) = analyzed(&src);
    let before = a.diagnostics.len();
    let start = std::time::Instant::now();
    check_all(&pkg, &mut a);
    let took = start.elapsed();
    let codes: Vec<_> = a.diagnostics[before..].iter().map(|d| d.code).collect();
    assert_eq!(codes, [Code::E0702], "the first of the E0702 and the E0704");
    assert!(took < std::time::Duration::from_secs(1), "{took:?}");
    let all: Vec<_> = all_said(&src[PRELUDE.len()..]).into_iter().map(|(c, t, _, _)| (c, t)).collect();
    assert_eq!(all, [(Code::E0702, "s".to_string()), (Code::E0704, format!("t{last}.a"))]);
}

/// S-799 (§3.5): the body of an anonymous function in an argument is not
/// evaluated with the arguments: its changes leave the record of the calls
/// the walk is in (here one, set before the walk), those around it stay.
#[test]
fn the_body_of_an_anonymous_function_is_not_in_the_window() {
    let src = format!(
        "{PRELUDE}pub fn cl() -> U32 {{
  var k: U32 = 1
  k = 2
  apply(fn(v: U32) -> U32 {{
    var j = v
    j = 3
    j
  }})
}}
"
    );
    let (pkg, a) = analyzed(&src);
    let id = (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == "cl").expect("the function");
    let root = crate::body::root_of(&a, id).expect("a body");
    let ast = &crate::module_of_def(&pkg, &a, id).expect("its module").parsed.ast;
    let mut w = Walker::new(&a, (ast, &src), (&a.names[&id], &a.bodies[&id], root), Vec::new());
    w.inside.calls = 1;
    w.expr(&mut Run::new(), root, Pos::Return);
    let changed: Vec<_> = w.inside.changes.iter().map(|(_, at)| &src[at.start as usize..at.end as usize]).collect();
    assert_eq!(changed, ["k"]);
    assert!(w.m.found.is_empty(), "{:?}", w.m.found);
}

/// S-193, S-799 (§3.5): two changes in the arguments of one call are not
/// compared with one another (`ys[next(inout k)] = next(inout k)` is the
/// same), and a change made out of the arguments is in no window.
#[test]
fn changes_are_not_compared_with_one_another() {
    let src = "pub fn nx(inout k: U32) -> U32 { k }
pub fn hk(a: U32, b: U32) -> U32 { a + b }
pub fn two() -> U32 {
  var k: U32 = 1
  hk(nx(inout k), nx(inout k))
}
pub fn out_of_the_call() -> U32 {
  var k: U32 = 1
  let v = nx(inout k)
  hk(k, v)
}
";
    assert_eq!(overlapping(src), []);
}

/// S-193, S-799 (§3.5): a change deep in nested calls is in the window of
/// each call around it, at the innermost argument; the walk does not grow
/// with the depth. Deeper than 20 levels: on a large stack (rules 3.4).
#[test]
fn a_change_deep_in_nested_calls() {
    const DEPTH: usize = 40;
    let run = || {
        let mut body = String::from(
            "pub fn nx(inout k: U32) -> U32 { k }\npub fn id(v: U32) -> U32 { v }\npub fn hk(a: U32, b: U32) -> U32 { a + b }\n",
        );
        body.push_str("pub fn deep() -> U32 {\n  var k: U32 = 1\n  hk(k, ");
        body.push_str(&"id(".repeat(DEPTH));
        body.push_str("nx(inout k)");
        body.push_str(&")".repeat(DEPTH));
        body.push_str(")\n}\n");
        overlapping(&body)
    };
    let found = onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
    assert_eq!(found, [(Code::E0702, 6, vec![6])]);
}

/// S-799 (§3.5, §5.2): the E0702 of a change in another argument stands at
/// the later of the change and the argument it overlaps, noted at the
/// earlier one, at the binding the argument derives from (S-796) and at a
/// Dup value copied to a `move` parameter (S-801); a change after a direct
/// `move` of its place is that E0702 too, not the E0704 of the move.
#[test]
fn the_notes_of_a_change_in_another_argument() {
    let src = "pub fn nx(inout k: U32) -> U32 { k }
pub fn hk(a: U32, b: U32) -> U32 { a + b }
pub fn mm(move a: U32, b: U32) -> U32 { a + b }
pub fn bn(b: Buf[F32], n: U32) -> U32 { n }
pub fn iol(inout b: Buf[F32]) -> U32 { 1 }
pub fn tk2(move b: Buf[F32], n: U32) -> U32 uses {Alloc} { n }
pub fn change_later() -> U32 {
  var k: U32 = 1
  hk(k,
    nx(inout k))
}
pub fn change_first() -> U32 {
  var k: U32 = 1
  hk(nx(inout k),
    k)
}
pub fn derived() -> U32 uses {Alloc} {
  var o = mko()
  match o {
    Some(b) => bn(b,
      gn(inout o, 1)),
    None => 0,
  }
}
pub fn copied() -> U32 {
  var n: U32 = 1
  mm(n,
    nx(inout n))
}
pub fn moved_first() -> U32 uses {Alloc} {
  var x = mk()
  tk2(move x,
    iol(inout x))
}
";
    let found = overlapping(src);
    let expected = [
        (Code::E0702, 10, vec![9]),
        (Code::E0702, 15, vec![14]),
        (Code::E0702, 21, vec![20, 20]),
        (Code::E0702, 28, vec![27, 27]),
        (Code::E0702, 33, vec![32]),
    ];
    assert_eq!(found, expected);
    let messages = writes(&format!("{OVERLAPS}{src}"));
    let says = |i: usize, s: &str| assert!(messages[i].2.contains(s), "{}", messages[i].2);
    says(0, "`k` is changed in another argument while `k` is passed borrowed in the same call");
    says(2, "`o` is changed in another argument while `b` is passed borrowed in the same call");
    says(4, "`x` is changed in another argument while `x` is passed as `move` in the same call");
    assert!(messages.iter().all(|m| m.3.is_empty()), "no candidate: {messages:?}");
}

/// R-24, S-798 (§5.4, W4-09 memo 2.1): a change of a place a borrowed
/// `for` holds is one E0715, noted at the head of each `for` it overlaps
/// (not at another), and it changes no state: a `move` of it is no move,
/// so a later one is no E0704 and the local is not among the moved.
#[test]
fn a_change_of_what_a_for_holds() {
    let src = "pub fn nested() uses {Alloc} {
  var xs = make_array()
  var ys = make_array()
  for _ in xs {
    for _ in ys {
      for _ in xs {
        xs[0] = mk()
      }
    }
  }
}
pub fn moved() -> U32 uses {Alloc} {
  var xs = make_array()
  var n: U32 = 0
  for b in xs {
    take_all(move xs)
    n = len_of(b)
  }
  n + xs[0].len()
}
";
    let found = said(src);
    let codes: Vec<_> = found.iter().map(|d| (d.0, d.1, d.2.as_str())).collect();
    assert_eq!(codes, [(Code::E0715, 7, "xs[0]"), (Code::E0715, 16, "xs")]);
    let notes = |i: usize| found[i].4.iter().filter_map(|n| n.0.clone()).collect::<Vec<_>>();
    assert_eq!(notes(0), ["xs", "xs"]);
    assert_eq!(notes(1), ["xs"]);
    assert!(seen(src).1.is_empty(), "{:?}", seen(src).1);
}

/// R-161's condition 5 (W4-09 memo 7.4): the head of a borrowed `match`
/// with a guard holds its places (W4-10's E0715), so a `let` it reads has
/// no candidate `var`, whatever its patterns bind.
#[test]
fn no_candidate_for_a_let_a_guard_holds() {
    let src = "pub fn guarded() -> U32 {
  let p: (U32, U32) = (1 + 1, 2)
  match p {
    (a, _) if bump(inout p) > a => a,
    _ => 0,
  }
}
pub fn bump(inout p: (U32, U32)) -> U32 { p.0 }
";
    let found: Vec<_> = writes(src).into_iter().map(|(c, l, _, f)| (c, l, f.len())).collect();
    assert_eq!(found, [(Code::E0701, 4, 0)]);
}

/// Memo 3 (rules 3.4): a write in 120 nested borrowed `for` loops over the
/// place is one E0715 with a note at each head, on a large stack (a `for`
/// is two levels of §2.5's 256).
#[test]
fn a_write_in_deeply_nested_for_loops() {
    const DEPTH: usize = 120;
    let run = || {
        let mut src = String::from("pub fn deep() uses {Alloc} {\n  var xs = make_array()\n");
        src.push_str(&"for _ in xs {\n".repeat(DEPTH));
        src.push_str("xs[0] = mk()\n");
        src.push_str(&"}\n".repeat(DEPTH));
        src.push_str("}\n");
        said(&src).into_iter().map(|d| (d.0, d.4.len())).collect::<Vec<_>>()
    };
    let found = onsa_diag::stack::spawn("t", run).unwrap().join().unwrap();
    assert_eq!(found, [(Code::E0715, DEPTH + 1)]);
}

/// The analysis of `body` after [`PRELUDE`], reporting nothing in it, and
/// each function of `body` by its name.
fn clean(body: &str) -> (String, crate::Analysis, impl Fn(&crate::Analysis, &str) -> crate::DefId) {
    let src = format!("{PRELUDE}{body}");
    let (_, a) = analyzed(&src);
    let said: Vec<_> = a.diagnostics.iter().filter(|d| d.span.file == FileId(0)).collect();
    assert!(said.is_empty(), "{said:?}");
    let named = |a: &crate::Analysis, n: &str| (0..a.defs.len() as u32).map(crate::DefId).find(|&d| a.def(d).name == n);
    (src, a, move |a: &crate::Analysis, n: &str| named(a, n).expect("the function"))
}

/// S-85 (§5.2): a field taken out is kept once (a loop's summary walks it
/// too, and keeps it not), with its root and path, for the stages after.
#[test]
fn a_field_taken_out_is_kept_once() {
    use crate::body::Step::{Elem, Field};
    let (src, a, def) = clean(
        "pub struct Out { h: Holder, t: (Buf[F32], U32) }
pub fn t(n: U32) uses {Alloc} {
  for i in 0 ..< n {
    let o = Out { h: Holder { buf: mk(), n: i }, t: (mk(), 1) }
    take(move o.h.buf)
  }
  let p = Out { h: Holder { buf: mk(), n: 1 }, t: (mk(), 1) }
  let x = move p.t.0
  take(move x)
}
",
    );
    let info = &a.bodies[&def(&a, "t")];
    let taken: Vec<_> = (info.taken.iter())
        .map(|t| (&src[t.at.start as usize..t.at.end as usize], info.locals[t.root.0 as usize].name.as_str(), &t.path))
        .collect();
    let (h, buf, tf) = (Field("h".into()), Field("buf".into()), Field("t".into()));
    assert_eq!(taken, [("o.h.buf", "o", &vec![h, buf]), ("p.t.0", "p", &vec![tf, Elem(0)])]);
}

/// S-85 (§5.2): the E0704 of a value after a field was taken out of it
/// says so, notes where, and how to read the others (in a loop too); after
/// a whole move, as before.
#[test]
fn the_note_of_a_use_after_a_field_was_taken_out() {
    let src = format!(
        "{PRELUDE}pub fn after(move h: Holder) -> U32 uses {{Alloc}} {{
  take(move h.buf)
  h.n
}}
pub fn looped(n: U32) uses {{Alloc}} {{
  let h = Holder {{ buf: mk(), n: 1 }}
  for i in 0 ..< n {{ take(move h.buf) }}
}}
pub fn whole(move h: Holder) -> U32 uses {{Alloc}} {{
  let g = move h
  h.n
}}
"
    );
    let (_, a) = analyzed(&src);
    let said: Vec<_> = (a.diagnostics.iter().filter(|d| d.span.file == FileId(0) && d.code == Code::E0704))
        .map(|d| {
            (d.message.as_str(), d.notes.iter().map(|n| (n.span.is_some(), n.message.as_str())).collect::<Vec<_>>())
        })
        .collect();
    let rule = (false, "read the other fields before, or take them out together with a destructuring `let` (§5.2)");
    let taken = vec![(true, "taken out here"), rule];
    assert_eq!(
        said,
        [
            ("`h` was moved when `h.buf` was taken out and cannot be used again (§5.2)", taken.clone()),
            ("`h` is moved here in a previous iteration of the loop when `h.buf` was taken out (§5.2)", taken),
            ("`h` was moved and cannot be used again (§5.2)", vec![(true, "moved here")]),
        ]
    );
}

/// S-85 (§12.2): the rest of a value a field is taken out of is dropped,
/// and needs `Alloc` when a part beside a step of the path does: a `Buf`
/// beside the field or beside a field on the way, of a generic struct by
/// its argument, a tuple's; not a Copy rest, nor a `T` (as its whole drop,
/// W6-02).
#[test]
fn the_rest_of_a_value_a_field_is_taken_out_of() {
    let (src, a, def) = clean(
        "pub struct Pair { a: Buf[F32], b: Buf[F32] }
pub struct G[T: ?Dup] { a: Buf[F32], b: T }
pub struct Out { h: Holder, k: F32 }
pub struct Out2 { h: Holder, s: Str }
pub fn copy_rest(move h: Holder) -> Buf[F32] uses {Alloc} { h.buf }
pub fn buf_rest(move p: Pair) -> Buf[F32] uses {Alloc} { p.a }
pub fn nested_copy(move o: Out) -> Buf[F32] uses {Alloc} { o.h.buf }
pub fn nested_outer(move o: Out2) -> Buf[F32] uses {Alloc} { o.h.buf }
pub fn tuple(move t: (Buf[F32], Str, U32)) -> Buf[F32] uses {Alloc} { t.0 }
pub fn of_buf(move g: G[Buf[F32]]) -> Buf[F32] uses {Alloc} { g.a }
pub fn of_u32(move g: G[U32]) -> Buf[F32] uses {Alloc} { g.a }
pub fn of_t[T: ?Dup](move g: G[T]) -> Buf[F32] uses {Alloc} { g.a }
",
    );
    let rest = |n: &str| {
        let found: Vec<_> =
            crate::rt::rest_drops(&a, &a.bodies[&def(&a, n)]).map(|(at, root)| (at, root.to_string())).collect();
        assert!(found.iter().all(|(at, _)| src[..at.start as usize].ends_with("{ ")), "{found:?}");
        found.into_iter().map(|(_, root)| root).collect::<Vec<_>>()
    };
    let none: [&str; 0] = [];
    for (n, roots) in [
        ("copy_rest", &none[..]),
        ("buf_rest", &["p"]),
        ("nested_copy", &none),
        ("nested_outer", &["o"]),
        ("tuple", &["t"]),
        ("of_buf", &["g"]),
        ("of_u32", &none),
        ("of_t", &none),
    ] {
        assert_eq!(rest(n), roots, "{n}");
    }
}
