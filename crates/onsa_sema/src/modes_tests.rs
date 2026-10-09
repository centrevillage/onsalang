//! Unit tests for argument modes / exclusivity / moves (T2-8) and `rt` (T2-9).

use onsa_diag::{Code, FileId};

use crate::{Analysis, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        path: "main".into(),
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package { name: "t".into(), modules, deps: Vec::new(), is_std: false })
}

fn codes(src: &str) -> Vec<Code> {
    let a = check(src);
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

fn ok(src: &str) {
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "unexpected diagnostics: {:?}", a.diagnostics);
}

/// The diagnostic's range after its first candidate.
fn first_fix(src: &str) -> String {
    let a = check(src);
    match a.diagnostics.first() {
        Some(d) if !d.fixes.is_empty() => crate::fixed_region(src, d, 0),
        _ => panic!("no fix: {:?}", a.diagnostics),
    }
}

const POLY: &str = "pub struct V { g: F32 }\npub struct Poly { voices: [V; 4], params: [F32; 4] }\npub rt fn step(inout v: V, p: F32) { v.g = p }\n";

#[test]
fn different_fields_of_self_do_not_overlap() {
    // §17.6: `self.voices[i]` inout and `self.params[i]` borrowed in one call.
    ok(&format!(
        "{POLY}impl Poly {{\n  pub rt fn process(inout self) {{\n    for i in 0..<4 {{ step(inout self.voices[i], self.params[i]) }}\n  }}\n}}\n"
    ));
}

#[test]
fn same_place_inout_twice_is_e0702() {
    assert_eq!(
        codes("pub fn f(inout a: U32, inout b: U32) {}\npub fn g() { var a = 1\n f(inout a, inout a) }\n"),
        vec![Code::E0702]
    );
    assert_eq!(
        codes(
            "pub fn f(inout a: U32, inout b: U32) {}\npub fn g(inout xs: [U32; 4], i: U32, j: U32) { f(inout xs[i], inout xs[j]) }\n"
        ),
        vec![Code::E0702]
    );
    assert_eq!(
        codes("pub fn f(inout a: U32, b: U32) {}\npub fn g() { var a = 1\n f(inout a, a) }\n"),
        vec![Code::E0702]
    );
    ok(
        "pub struct P { x: U32, y: U32 }\npub fn f(inout a: U32, b: U32) {}\npub fn g() { var p = P { x: 1, y: 2 }\n f(inout p.x, p.y) }\n",
    );
}

#[test]
fn bang_marks_inout_self_calls() {
    assert_eq!(codes("pub fn g(inout out: Span[F32]) { out.fill(0.0) }\n"), vec![Code::E0713]);
    assert_eq!(first_fix("pub fn g(inout out: Span[F32]) { out.fill(0.0) }\n"), "out.fill!(0.0)");
    assert_eq!(codes("pub fn g(xs: Span[F32]) -> U32 { xs.len!() }\n"), vec![Code::E0714]);
    assert_eq!(first_fix("pub fn g(xs: Span[F32]) -> U32 { xs.len!() }\n"), "xs.len()");
    let p = "pub struct P { x: F32 }\nimpl P {\n  pub fn norm(self) -> F32 { self.x }\n  pub fn scale(inout self, k: F32) { self.x = self.x * k }\n}\n";
    assert_eq!(codes(&format!("{p}pub fn g(p: P) -> F32 {{ p.norm!() }}\n")), vec![Code::E0714]);
    assert_eq!(
        codes(&format!("{p}pub fn g() -> F32 {{ var p = P {{ x: 1.0 }}\n p.scale(2.0)\n p.norm() }}\n")),
        vec![Code::E0713]
    );
    ok(&format!("{p}pub fn g() -> F32 {{ var p = P {{ x: 1.0 }}\n p.scale!(2.0)\n p.norm() }}\n"));
    // The receiver of an `inout self` method must be mutable.
    assert_eq!(codes(&format!("{p}pub fn g(p: P) {{ p.scale!(2.0) }}\n")), vec![Code::E0701]);
    assert_eq!(codes("pub fn g(out: Span[F32]) { out.fill!(0.0) }\n"), vec![Code::E0701]);
}

#[test]
fn argument_modes_must_match() {
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g() { var a = 1\n f(a) }\n"), vec![Code::E0703]);
    assert_eq!(first_fix("pub fn f(inout a: U32) {}\npub fn g() { var a = 1\n f(a) }\n"), "inout a");
    assert_eq!(codes("pub fn f(a: U32) {}\npub fn g() { var a = 1\n f(inout a) }\n"), vec![Code::E0703]);
    assert_eq!(
        codes("pub fn f(move a: Buf[F32]) uses {Alloc} {}\npub fn g(move b: Buf[F32]) uses {Alloc} { f(b) }\n"),
        vec![Code::E0703]
    );
    // `inout` needs a place rooted at a mutable binding.
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g() { let a = 1\n f(inout a) }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g(a: U32) { f(inout a) }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g() { f(inout 1) }\n"), vec![Code::E0701]);
    assert_eq!(
        codes("pub fn f(inout a: U32) {}\npub fn g(xs: [U32; 2]) { for x in xs { f(inout x) } }\n"),
        vec![Code::E0701]
    );
    ok("pub fn f(inout a: U32) {}\npub fn g(inout a: U32) { f(inout a) }\n");
}

#[test]
fn second_class_values_stay_in_argument_position() {
    assert_eq!(codes("pub fn g(xs: Span[F32]) { let s = xs }\n"), vec![Code::E0710]);
    assert_eq!(codes("pub fn g(xs: Span[F32]) -> Span[F32] { xs }\n").first().copied(), Some(Code::E0710));
    assert_eq!(codes("pub fn g(xs: Span[F32]) { let s = xs.slice(0, 2) }\n"), vec![Code::E0710]);
    ok(
        "pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(xs: Span[F32]) -> U32 { total(xs.slice(0, 2)) + xs[0].trunc_u32() }\n",
    );
    ok(
        "pub fn mix(ch: [Span[F32]; 2]) -> U32 { ch[0].len() + ch[1].len() }\npub fn g(a: [F32; 4], b: [F32; 4]) -> U32 { mix([a, b]) }\n",
    );
    // A capturing closure is second-class too.
    assert_eq!(codes("pub fn g(k: F32) { let f: fn(F32) -> F32 = fn(x: F32) -> F32 { x * k } }\n"), vec![Code::E0710]);
    ok("pub fn g(k: F32) { let f: fn(F32) -> F32 = fn(x: F32) -> F32 { x * 2.0 } }\n");
}

#[test]
fn closures_capture_copies_only() {
    assert_eq!(
        codes(
            "pub fn apply(f: fn(F32) -> F32) -> F32 { f(1.0) }\npub fn g(inout k: F32) -> F32 { apply(fn(x) { x * k }) }\n"
        ),
        vec![Code::E0712]
    );
    assert_eq!(
        codes(
            "pub fn apply(f: fn(U32) -> U32) -> U32 { f(1) }\npub fn g(move b: Buf[F32]) -> U32 uses {Alloc} { apply(fn(x) { x + b.len() }) }\n"
        ),
        vec![Code::E0712]
    );
    ok(
        "pub fn apply(f: fn(F32) -> F32) -> F32 { f(1.0) }\npub fn g(k: F32) -> F32 { var m = k\n apply(fn(x) { x * m }) }\n",
    );
}

#[test]
fn borrowed_affine_cannot_move() {
    assert_eq!(
        codes("pub fn take(move b: Buf[F32]) uses {Alloc} {}\npub fn g(b: Buf[F32]) uses {Alloc} { take(move b) }\n"),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(
            "pub fn take(move b: Buf[F32]) uses {Alloc} {}\npub fn g(bs: [Buf[F32]; 2]) uses {Alloc} { for b in bs { take(move b) } }\n"
        ),
        vec![Code::E0711]
    );
    // Partial moves are not allowed; Dup fields are copied.
    assert_eq!(
        codes(
            "pub struct S { b: Buf[F32], n: U32 }\npub fn take(move b: Buf[F32]) uses {Alloc} {}\npub fn g(move s: S) uses {Alloc} { take(move s.b) }\n"
        ),
        vec![Code::E0711]
    );
    ok(
        "pub struct S { b: Buf[F32], n: U32 }\npub fn take(move n: U32) {}\npub fn g(move s: S) uses {Alloc} { take(move s.n) }\n",
    );
    ok("pub fn take(move b: Buf[F32]) uses {Alloc} {}\npub fn g(move b: Buf[F32]) uses {Alloc} { take(move b) }\n");
    // Dup values are copied when passed as `move`, even when borrowed.
    ok("pub fn take(move n: U32) {}\npub fn g(n: U32) { take(move n) }\n");
    // `[e; N]` needs a Dup element: a kind constraint of sema (E0416, §2.4, S-235), not a move.
    assert_eq!(codes("pub fn g(move b: Buf[F32]) uses {Alloc} { let xs = [b; 2] }\n"), vec![Code::E0416]);
}

#[test]
fn use_after_move() {
    let take = "pub fn take(move b: Buf[F32]) uses {Alloc} {}\npub fn len(b: Buf[F32]) -> U32 { b.len() }\n";
    assert_eq!(
        codes(&format!("{take}pub fn g(move b: Buf[F32]) -> U32 uses {{Alloc}} {{ take(move b)\n len(b) }}\n")),
        vec![Code::E0704]
    );
    assert_eq!(
        codes(&format!("{take}pub fn g(move b: Buf[F32]) uses {{Alloc}} {{ take(move b)\n take(move b) }}\n")),
        vec![Code::E0704]
    );
    // Moved in one branch: unusable after the `if`.
    assert_eq!(
        codes(&format!(
            "{take}pub fn g(move b: Buf[F32], c: Bool) -> U32 uses {{Alloc}} {{ if c {{ take(move b) }}\n len(b) }}\n"
        )),
        vec![Code::E0704]
    );
    // Moved in a branch that returns: fine afterwards.
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32], c: Bool) -> U32 uses {{Alloc}} {{ if c {{ take(move b)\n return 0 }}\n len(b) }}\n"
    ));
    // Reassigned `var`: usable again.
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32]) -> U32 uses {{Alloc}} {{ var v = move b\n take(move v)\n v = Buf.zeroed(4)\n len(v) }}\n"
    ));
    // Moved inside a loop.
    assert_eq!(
        codes(&format!(
            "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ for i in 0..<n {{ take(move b) }} }}\n"
        )),
        vec![Code::E0704]
    );
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ for i in 0..<n {{ take(move b)\n break }} }}\n"
    ));
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ var v = move b\n for i in 0..<n {{ take(move v)\n v = Buf.zeroed(4) }} }}\n"
    ));
    // `match` arms are branches.
    assert_eq!(
        codes(&format!(
            "{take}pub fn g(move b: Buf[F32], o: Option[U32]) -> U32 uses {{Alloc}} {{ match o {{ Some(_) => take(move b), None => {{}} }}\n len(b) }}\n"
        )),
        vec![Code::E0704]
    );
}

#[test]
fn assignment_needs_a_mutable_place() {
    assert_eq!(codes("pub fn g() { let a: U32 = 1\n a = 2 }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub struct P { x: U32 }\npub fn g(p: P) { p.x = 2 }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub fn g(xs: [U32; 2]) { for x in xs { x = 1 } }\n"), vec![Code::E0701]);
    ok("pub struct P { x: U32 }\npub fn g(inout p: P) { p.x = 2 }\n");
}

#[test]
fn rt_calls_only_rt() {
    assert_eq!(codes("pub fn slow(x: F32) -> F32 { x }\npub rt fn f(x: F32) -> F32 { slow(x) }\n"), vec![Code::E0901]);
    assert_eq!(codes("pub rt fn f(g: fn(F32) -> F32) -> F32 { g(1.0) }\n"), vec![Code::E0901]);
    ok("pub rt fn f(g: rt fn(F32) -> F32) -> F32 { g(1.0) }\n");
    ok("pub rt fn fast(x: F32) -> F32 { x }\npub rt fn f(x: F32) -> F32 { fast(x) }\n");
    assert_eq!(codes("pub rt fn f() -> U32 { let b: Buf[F32] = Buf.zeroed(4)\n b.len() }\n"), vec![Code::E0901]);
    // Owning a `Buf` drops it, which needs `Alloc`; borrowing is fine.
    assert_eq!(codes("pub rt fn f(move b: Buf[F32]) -> U32 { b.len() }\n"), vec![Code::E0901]);
    ok("pub rt fn f(b: Buf[F32]) -> U32 { b.len() }\n");
    // Moving the `Buf` on (as an argument or the return value) is not a drop.
    ok(
        "pub rt fn f(move b: Buf[F32]) -> Buf[F32] { pass(move b) }\npub rt fn pass(move b: Buf[F32]) -> Buf[F32] { b }\n",
    );
}

#[test]
fn rt_recursion_is_e0903() {
    assert_eq!(codes("pub rt fn f(n: U32) -> U32 { if n == 0 { 0 } else { f(n - 1) } }\n"), vec![Code::E0903]);
    assert_eq!(
        codes(
            "pub rt fn f(n: U32) -> U32 { g(n) }\npub rt fn g(n: U32) -> U32 { if n == 0 { 0 } else { f(n - 1) } }\n"
        ),
        vec![Code::E0903]
    );
    // Non-rt recursion is allowed.
    ok("pub fn f(n: U32) -> U32 { if n == 0 { 0 } else { f(n - 1) } }\n");
}

#[test]
fn holes_report_the_resolved_type() {
    let a = check("pub fn f(x: F32, y: I32) -> F32 { x + _ }\n");
    assert_eq!(a.diagnostics.len(), 1);
    assert_eq!(a.diagnostics[0].code, Code::E0421);
    assert_eq!(a.diagnostics[0].message, "hole of type `F32`; candidates: x");
}

// ---------------------------------------------------------------- S-21: explicit `move`

const TAKE: &str = "pub fn take(move b: Buf[F32]) uses {Alloc} {}\npub struct Box { b: Buf[F32] }\n";

#[test]
fn consuming_an_affine_value_needs_move() {
    // `let y = x` on an owned Affine value: E0711 with the `move ` insertion (§5.2).
    let src = format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let y = b\n}}\n");
    let a = check(&src);
    assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0711]);
    assert_eq!(crate::fixed_region(&src, &a.diagnostics[0], 0), "move b");
    assert_eq!(a.diagnostics[0].found.as_deref(), Some("b"));
    // The same in every consuming position: assignment, literal element, struct field, constructor.
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(move b: Buf[F32], move c: Buf[F32]) uses {{Alloc}} {{\n  var v = move b\n  v = c\n}}\n"
        )),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let t = (b, 1)\n}}\n")),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let x = Box {{ b: b }}\n}}\n")),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let o = Some(b)\n}}\n")),
        vec![Code::E0711]
    );
    // With `move`: fine, and the value is then moved (use after → E0704).
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let y = move b\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let x = Box {{ b: move b }}\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let o = Some(move b)\n}}\n"));
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let y = move b\n  take(move b)\n}}\n")),
        vec![Code::E0704]
    );
    // Dup values may be written with `move` (a copy).
    ok("pub fn f(n: U32) -> U32 {\n  let m = move n\n  m + n\n}\n");
}

#[test]
fn return_and_tail_move_implicitly() {
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) -> Buf[F32] {{\n  b\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32], c: Bool) -> Buf[F32] {{\n  if c {{\n    return b\n  }}\n  b\n}}\n"));
    // Returning a borrowed Affine parameter is still E0711.
    assert_eq!(codes(&format!("{TAKE}pub fn f(b: Buf[F32]) -> Buf[F32] {{\n  b\n}}\n")), vec![Code::E0711]);
}

#[test]
fn match_borrows_unless_moved() {
    // `match x` binds borrows and leaves `x` usable (§7, S-21).
    ok(&format!(
        "{TAKE}pub fn f(move o: Option[Buf[F32]]) uses {{Alloc}} {{\n  match o {{\n    Some(_) => 1,\n    None => 0,\n  }}\n  take_opt(move o)\n}}\npub fn take_opt(move o: Option[Buf[F32]]) uses {{Alloc}} {{}}\n"
    ));
    // `match move x` consumes it.
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(move o: Option[Buf[F32]]) uses {{Alloc}} {{\n  match move o {{\n    Some(_) => 1,\n    None => 0,\n  }}\n  take_opt(move o)\n}}\npub fn take_opt(move o: Option[Buf[F32]]) uses {{Alloc}} {{}}\n"
        )),
        vec![Code::E0704]
    );
    // Arm bindings of `match x` are borrows: they cannot be passed as `move`.
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(move o: Option[Buf[F32]]) uses {{Alloc}} {{\n  match o {{\n    Some(b) => take(move b),\n    None => {{}},\n  }}\n}}\n"
        )),
        vec![Code::E0711]
    );
    // Arm bindings of `match move x` own the value.
    ok(&format!(
        "{TAKE}pub fn f(move o: Option[Buf[F32]]) uses {{Alloc}} {{\n  match move o {{\n    Some(b) => take(move b),\n    None => {{}},\n  }}\n}}\n"
    ));
}

#[test]
fn move_needs_a_place() {
    assert_eq!(codes("pub fn g() -> U32 { 1 }\npub fn f() -> U32 {\n  let y = move g()\n  y\n}\n"), vec![Code::E0711]);
}

#[test]
fn a_move_on_the_last_expression_follows_the_position_of_its_block() {
    // S-100 (§5.2): where the block consumes or returns, the arm's `move` moves.
    ok(&format!(
        "{TAKE}pub fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] {{\n  let y = if c {{ move a }} else {{ move b }}\n  y\n}}\n"
    ));
    ok(&format!("{TAKE}pub fn f(move a: Buf[F32]) -> Buf[F32] {{\n  return move a\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move a: Buf[F32]) -> Buf[F32] {{\n  move a\n}}\n"));
    // The other arm still needs its `move` (E0711).
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) -> Buf[F32] uses {{Alloc}} {{\n  let y = if c {{ move a }} else {{ b }}\n  y\n}}\n"
        )),
        vec![Code::E0711]
    );
    // S-343: where no value is consumed (a statement, a borrowed argument), the `move` is stopped
    // (E0200), not read as a move.
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(c: Bool, move a: Buf[F32], move b: Buf[F32]) uses {{Alloc}} {{\n  if c {{ move a }} else {{ move b }}\n  take(move a)\n}}\n"
        )),
        vec![Code::E0200]
    );
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn see(b: Buf[F32]) -> U32 {{\n  1\n}}\npub fn f(move a: Buf[F32]) -> U32 uses {{Alloc}} {{\n  see({{ move a }})\n}}\n"
        )),
        vec![Code::E0200]
    );
}

/// R-194: the ends of a `for` range are read once, before the first
/// iteration (§3.5): a move in them and a use of a moved value are checked
/// as anywhere else.
#[test]
fn range_ends_are_read() {
    let take = "pub fn take(move b: Buf[F32]) -> U32 uses {Alloc} { 3 }\n";
    let f = |body: &str| {
        codes(&format!(
            "{take}pub fn g(move b: Buf[F32], n: U32) -> U32 uses {{Alloc}} {{\n  var s: U32 = 0\n{body}\n  s\n}}\n"
        ))
    };
    // A use of a moved value in an end.
    assert_eq!(f("  take(move b)\n  for i in 0..<b.len() { s = s + i }"), vec![Code::E0704]);
    assert_eq!(f("  take(move b)\n  for i in b.len()..<n { s = s + i }"), vec![Code::E0704]);
    // A move in the ends of two loops: the second is a use after the move.
    assert_eq!(
        f("  for i in 0..<take(move b) { s = s + 1 }\n  for j in 0..<take(move b) { s = s + 1 }"),
        vec![Code::E0704]
    );
    // The ends of an inner `for` are read once per iteration of the outer one.
    assert_eq!(f("  for k in 0..<n {\n    for i in 0..<take(move b) { s = s + 1 }\n  }"), vec![Code::E0704]);
    // A move in the body, then a use in the ends of a nested `for`.
    assert_eq!(
        f("  for k in 0..<n {\n    take(move b)\n    for i in 0..<b.len() { s = s + 1 }\n  }"),
        vec![Code::E0704]
    );
    // Read once: a move in the ends is not a move in each iteration.
    assert_eq!(f("  for i in 0..<take(move b) { s = s + 1 }"), vec![]);
    // A borrow in the ends, then the move after the loop.
    assert_eq!(f("  for i in 0..<b.len() { s = s + 1 }\n  s = s + take(move b)"), vec![]);
}
