//! Unit tests for argument modes / exclusivity / moves (T2-8) and `rt` (T2-9).

use onsa_diag::{Code, FileId};

use crate::{Analysis, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package::new("t", modules, vec![crate::flow_tests::std_package()]))
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
    // A value that is no place is the E0415 of the types (§5.1, S-178).
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g() { f(inout 1) }\n"), vec![Code::E0415]);
    // By the mode of the declaration, with no mark too (the types stage is before the E0703 / E0713).
    assert_eq!(codes("pub fn f(inout a: U32) {}\npub fn g() { f(1) }\n"), vec![Code::E0415]);
    let p = "pub struct P { v: F32 }\nimpl P {\n  pub fn bump(inout self) { self.v = 1.0 }\n}\npub fn mk() -> P { P { v: 0.0 } }\n";
    assert_eq!(codes(&format!("{p}pub fn g() {{ mk().bump() }}\n")), vec![Code::E0415]);
    assert_eq!(
        codes("pub fn f(inout a: U32) {}\npub fn g(xs: [U32; 2]) { for x in xs { f(inout x) } }\n"),
        vec![Code::E0701]
    );
    ok("pub fn f(inout a: U32) {}\npub fn g(inout a: U32) { f(inout a) }\n");
}

#[test]
fn second_class_values_stay_in_argument_position() {
    // A `Span` of a borrowed parameter is a borrow binding of a `let` (S-217, §5.4); of an `inout` one it is not.
    ok("pub fn g(xs: Span[F32]) { let _ = xs }\n");
    assert_eq!(codes("pub fn g(inout xs: Span[F32]) { let _ = xs }\n"), vec![Code::E0710]);
    assert_eq!(codes("pub fn g(xs: Span[F32]) -> Span[F32] { xs }\n").first().copied(), Some(Code::E0710));
    // A part of the view is too (W4-16 U1b).
    ok("pub fn g(xs: Span[F32]) { let _ = xs.slice(0, 2) }\n");
    assert_eq!(codes("pub fn g(inout xs: Span[F32]) { let _ = xs.slice(0, 2) }\n"), vec![Code::E0710]);
    ok(
        "pub fn total(xs: Span[F32]) -> U32 { xs.len() }\npub fn g(xs: Span[F32]) -> U32 { total(xs.slice(0, 2)) + xs[0].trunc_u32() }\n",
    );
    ok(
        "pub fn mix(ch: [Span[F32]; 2]) -> U32 { ch[0].len() + ch[1].len() }\npub fn g(a: [F32; 4], b: [F32; 4]) -> U32 { mix([a, b]) }\n",
    );
    // A capturing closure is second-class too.
    assert_eq!(codes("pub fn g(k: F32) { let _: fn(F32) -> F32 = fn(x: F32) -> F32 { x * k } }\n"), vec![Code::E0710]);
    ok("pub fn g(k: F32) { let _: fn(F32) -> F32 = fn(x: F32) -> F32 { x * 2.0 } }\n");
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
    assert_eq!(codes("pub fn g(move b: Buf[F32]) uses {Alloc} { let _ = [b; 2] }\n"), vec![Code::E0416]);
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
            "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ for _ in 0..<n {{ take(move b) }} }}\n"
        )),
        vec![Code::E0704]
    );
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ for _ in 0..<n {{ take(move b)\n break }} }}\n"
    ));
    ok(&format!(
        "{take}pub fn g(move b: Buf[F32], n: U32) uses {{Alloc}} {{ var v = move b\n for _ in 0..<n {{ take(move v)\n v = Buf.zeroed(4) }} }}\n"
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
    assert_eq!(codes("pub fn g() { let a: U32 = 1\n a = 2\n let _ = a }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub struct P { x: U32 }\npub fn g(p: P) { p.x = 2 }\n"), vec![Code::E0701]);
    assert_eq!(codes("pub fn g(xs: [U32; 2]) { for x in xs { x = 1\n let _ = x } }\n"), vec![Code::E0701]);
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
    let src = format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let y = b\n  take(move y)\n}}\n");
    let a = check(&src);
    assert_eq!(a.diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(), vec![Code::E0711]);
    assert_eq!(crate::fixed_region(&src, &a.diagnostics[0], 0), "move b");
    assert_eq!(a.diagnostics[0].found.as_deref(), Some("b"));
    // The same in every consuming position: assignment, literal element, struct field, constructor.
    assert_eq!(
        codes(&format!(
            "{TAKE}pub fn f(move b: Buf[F32], move c: Buf[F32]) uses {{Alloc}} {{\n  var v = move b\n  v = c\n  take(move v)\n}}\n"
        )),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = (b, 1)\n}}\n")),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = Box {{ b: b }}\n}}\n")),
        vec![Code::E0711]
    );
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = Some(b)\n}}\n")),
        vec![Code::E0711]
    );
    // With `move`: fine, and the value is then moved (use after → E0704).
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = move b\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = Box {{ b: move b }}\n}}\n"));
    ok(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = Some(move b)\n}}\n"));
    assert_eq!(
        codes(&format!("{TAKE}pub fn f(move b: Buf[F32]) uses {{Alloc}} {{\n  let _ = move b\n  take(move b)\n}}\n")),
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
        f("  for _ in 0..<take(move b) { s = s + 1 }\n  for _ in 0..<take(move b) { s = s + 1 }"),
        vec![Code::E0704]
    );
    // The ends of an inner `for` are read once per iteration of the outer one.
    assert_eq!(f("  for _ in 0..<n {\n    for _ in 0..<take(move b) { s = s + 1 }\n  }"), vec![Code::E0704]);
    // A move in the body, then a use in the ends of a nested `for`.
    assert_eq!(
        f("  for _ in 0..<n {\n    take(move b)\n    for _ in 0..<b.len() { s = s + 1 }\n  }"),
        vec![Code::E0704]
    );
    // Read once: a move in the ends is not a move in each iteration.
    assert_eq!(f("  for _ in 0..<take(move b) { s = s + 1 }"), vec![]);
    // A borrow in the ends, then the move after the loop.
    assert_eq!(f("  for _ in 0..<b.len() { s = s + 1 }\n  s = s + take(move b)"), vec![]);
}

/// The states of the bindings over their heads (§5.4) and their uses
/// (§5.2), a table of the sweep of W4-16 U1a/b (`rules/leader.md` 4.9; the
/// whole sweep stays with the breaking side). A binding `b` of the Affine
/// `Buf[F32]` from each head is used as it is or through `let c = b`. The
/// codes are from the spec: a borrow (an origin, or a `let` from one) is
/// moved nowhere, with its mark or not (E0711, §5.2), and is read-only
/// (E0701, §5.4); an `inout` parameter, a `move` parameter and a `var` are
/// written (§5.2); a `let` from a binding that is no origin is owned, so its
/// value is an Affine place consumed with no `move` (E0711, §5.2); an owned
/// Affine value passed to a `move` parameter with no mark is E0703 (§5.2).
#[test]
fn binding_states_over_heads_and_uses() {
    let pre = "pub fn take(move b: Buf[F32]) -> U32 uses {Alloc} { b.len() }\n\
        pub fn fill(inout b: Buf[F32]) uses {Alloc} { b.fill!(1.0) }\n\
        pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(2) }\n\
        pub fn len(b: Buf[F32]) -> U32 { b.len() }\n";
    let uses = [
        "let _ = take(move X)",
        "let _ = take(X)",
        "var z = X\n let _ = z.len()",
        "X.fill!(1.0)",
        "fill(inout X)",
        "let _ = len(X)",
    ];
    // (head, parameters, body around `BODY`).
    let heads = [
        ("param", "b: Buf[F32]", "BODY"),
        ("inout", "inout b: Buf[F32]", "BODY"),
        ("move", "move b: Buf[F32]", "BODY"),
        ("var", "", "var b = mk()\n BODY"),
        ("let", "", "let b = mk()\n BODY"),
        ("for", "xs: [Buf[F32]; 2]", "for b in xs {\n BODY\n }"),
        ("match", "o: Option[Buf[F32]]", "match o { Some(b) => {\n BODY\n }, None => {} }"),
        ("closure", "", "let g = fn(b: Buf[F32]) -> U32 uses {Alloc} {\n BODY\n 1 }\n let _ = g.(mk())"),
    ];
    // (head, through `let c = b`, the code of each use: `.` none, `1` E0701,
    // `3` E0703, `m` E0711, `-` not in this table).
    // The two `-` of `inout`: §5.2 makes them E0711 with no fix, which waits for R-117 (W4-07).
    let rows = [
        ("param", false, "mmm11."),
        ("param", true, "mmm11."),
        ("inout", false, "--m..."),
        ("inout", true, "-----m"),
        ("move", false, "-3m..."),
        ("move", true, "-----m"),
        ("var", false, "-3-..."),
        ("var", true, "---m--"),
        ("let", false, "-3-11."),
        ("let", true, "-----m"),
        ("for", true, "m--11."),
        ("match", true, "m--11."),
        ("closure", true, "m--11."),
    ];
    let mut n = 0;
    for (head, derived, codes_of_uses) in rows {
        let &(_, params, around) = heads.iter().find(|h| h.0 == head).unwrap();
        for (u, c) in uses.iter().zip(codes_of_uses.chars()) {
            let want = match c {
                '.' => vec![],
                '1' => vec![Code::E0701],
                '3' => vec![Code::E0703],
                'm' => vec![Code::E0711],
                _ => continue,
            };
            let body = if derived { format!("let c = b\n {}", u.replace('X', "c")) } else { u.replace('X', "b") };
            let src = format!("{pre}pub fn f({params}) uses {{Alloc}} {{\n {}\n}}\n", around.replace("BODY", &body));
            assert_eq!(codes(&src), want, "{head}, derived {derived}, `{u}`:\n{src}");
            n += 1;
        }
    }
    assert_eq!(n, 45);
}

/// A value an anonymous function captures is read-only (§5.3): assigning
/// to it, passing it as `inout` and calling a `!` method on it are E0701,
/// whatever its binding (a `move` parameter, `move self` and a `var` are
/// written outside the function). Its own parameters and bindings are not
/// captured, nor the bindings of an outer anonymous function in its own body.
#[test]
fn captured_values_are_read_only() {
    let pre = "pub fn apply(f: fn(I32) -> I32) -> I32 { f.(1) }\n\
        pub fn bump(inout z: I32) { z = z + 1 }\n\
        pub struct C { n: I32 }\n\
        impl C {\n  pub fn inc(inout self) { self.n = self.n + 1 }\n}\n";
    let f = |params: &str, body: &str| codes(&format!("{pre}pub fn h({params}) -> I32 {{\n {body}\n}}\n"));
    let read_only = vec![Code::E0701];
    assert_eq!(f("move x: I32", "apply(fn(n) { x = 3\n n + x })"), read_only);
    assert_eq!(f("move x: I32", "apply(fn(n) { bump(inout x)\n n })"), read_only);
    assert_eq!(f("x: I32", "var y = x\n apply(fn(n) { y = 3\n n + y })"), read_only);
    assert_eq!(f("", "let y = 2\n apply(fn(n) { y = 3\n n + y })"), read_only);
    assert_eq!(f("", "var c = C { n: 1 }\n apply(fn(n) { c.inc!()\n n + c.n })"), read_only);
    let move_self = "impl C {\n  pub fn a(move self) -> I32 { apply(fn(k) { self.n = 3\n k }) }\n}\n";
    assert_eq!(codes(&format!("{pre}{move_self}")), read_only);
    // A binding of an outer anonymous function, captured by an inner one.
    assert_eq!(f("", "apply(fn(n) { var k = n\n apply(fn(m) { k = m\n m }) + k })"), read_only);
    // Read only; written outside; the function's own bindings.
    let ok = |params: &str, body: &str| assert_eq!(f(params, body), vec![], "{body}");
    ok("x: I32", "var y = x\n y = 2\n apply(fn(n) { n + y })");
    ok("", "apply(fn(n) { var k = n\n k = k + 1\n apply(fn(m) { m + k }) + k })");
    ok("", "apply(fn(n) { var k = n\n bump(inout k)\n k })");
}
