//! The unit tests of the new modes stage (W4-07 U1): the flow of the moves
//! (§5.2, §5.4, §7), from sources parsed in memory. Each runs the whole
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
        let mut w = Walker::new(&a, ast, &a.names[&id], &a.bodies[&id], Vec::new());
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
