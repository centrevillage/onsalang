//! The intervals of the indexes (`bounds.rs`, §9.2, S-1264 P2): each rule of
//! the list of `Env::interval` at its edge, in a Core made by hand, both by
//! the stage (does it make the index `Known`) and by the verifier (does it
//! take the index `Known`, V-25): the two read the same functions (D-15), so
//! each case asks both and they must agree. V-28: the variable of a `for` is
//! not written in its body. And the stage on Core lowered from a source.

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::walk::{
    ChildMut, PartMut, Role, block_children_mut, expr_children_mut, place_children_mut, stmt_children_mut,
};
use crate::{Rule, verify};

const U8_: CTy = Types::int(IntKind::U8);
const U16_: CTy = Types::int(IntKind::U16);

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn int(ty: CTy, n: i128) -> Expr {
    Expr::new(ty, sp(), ExprKind::Lit(Lit::Int(n)))
}

fn u32_(n: i128) -> Expr {
    int(Types::U32, n)
}

fn local(ty: CTy, l: u32) -> Expr {
    Expr::new(ty, sp(), ExprKind::Local(LocalId(l)))
}

fn bin(op: BinOp, overflow: Overflow, a: Expr, b: Expr) -> Expr {
    Expr::new(a.ty, sp(), ExprKind::Binary { op, overflow, lhs: Box::new(a), rhs: Box::new(b) })
}

fn cast(e: Expr) -> Expr {
    Expr::new(Types::U32, sp(), ExprKind::Cast(Box::new(e)))
}

fn stmt(kind: StmtKind) -> Stmt {
    Stmt { span: sp(), kind }
}

/// `for l in lo..<hi` (`..=` when `inclusive`) of the body `stmts`.
fn for_(l: u32, lo: Expr, hi: Expr, inclusive: bool, stmts: Vec<Stmt>) -> Stmt {
    let body = Block { stmts, value: None };
    stmt(StmtKind::ForRange { local: LocalId(l), lo, hi, body, inclusive })
}

/// The statement that reads `xs[index]`, of the parameter `xs` (local 0),
/// checked: `if xs[index] == 0 {}`, which the stage does not drop (R-533).
fn read(base: CTy, index: Expr) -> Stmt {
    let xs = Box::new(local(base, 0));
    let x = Expr::new(Types::U32, sp(), ExprKind::Index { base: xs, index: Box::new(index), bounds: Bounds::Checked });
    let zero = Expr::new(Types::BOOL, sp(), ExprKind::Cmp { op: CmpOp::Eq, lhs: Box::new(x), rhs: Box::new(u32_(0)) });
    stmt(StmtKind::If(zero, Block::default(), Block::default()))
}

/// A module of the function `g(xs: base)`, of the other locals `tys` (from
/// local 1) and the statements `stmts`, made by `make` given the type of `xs`.
fn module(base: TyKind, tys: &[CTy], make: impl FnOnce(CTy) -> Vec<Stmt>) -> Module {
    let mut m = Module::default();
    let base = m.tys.intern(base);
    let ty = |t: &CTy| Local { name: "l".into(), ty: *t };
    let locals = std::iter::once(Local { name: "xs".into(), ty: base }).chain(tys.iter().map(ty)).collect();
    m.fns.push(FnDef {
        name: "g".into(),
        params: vec![Param { local: LocalId(0), mode: Mode::Borrow, ty: base }],
        ret: Types::UNIT,
        sret: false,
        rt: false,
        locals,
        body: Some(Block { stmts: make(base), value: None }),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    });
    m.fill_all_facts();
    m
}

/// The bounds of every index of the bodies of `m`, each changed by `f`.
fn each_index(m: &mut Module, f: &mut dyn FnMut(&mut Bounds)) {
    fn child(c: ChildMut<'_>, f: &mut dyn FnMut(&mut Bounds)) {
        match c {
            ChildMut::Expr(x, ..) => {
                expr_children_mut(x, &mut |c| child(c, f));
                if let ExprKind::Index { bounds, .. } = &mut x.kind {
                    f(bounds);
                }
            }
            ChildMut::Block(b, ..) => block_children_mut(b, Role::Read, &mut |p| match p {
                PartMut::Stmt(s) => stmt_children_mut(s, &mut |c| child(c, f)),
                PartMut::Value(v, _) => child(ChildMut::Expr(v, crate::walk::Eval::Always, Role::Read), f),
            }),
            ChildMut::Place(p, role) => {
                place_children_mut(p, role, &mut |c| child(c, f));
                if let Place::Index(_, _, _, bounds) = p {
                    f(bounds);
                }
            }
        }
    }
    for def in &mut m.fns {
        if let Some(b) = &mut def.body {
            child(ChildMut::Block(b, crate::walk::Scope::Opens, crate::walk::Eval::Always), f);
        }
    }
}

/// Whether the index of `m` is proved in range: the stage makes it `Known`
/// exactly when the verifier takes it `Known` (else it rejects it by V-25).
fn proved(m: &Module) -> bool {
    let mut marked = m.clone();
    crate::bounds::module(&mut marked);
    let mut known = 0;
    each_index(&mut marked, &mut |b| known += usize::from(*b == Bounds::Known));
    verify(&marked).unwrap_or_else(|e| panic!("{e}"));
    let mut all = m.clone();
    each_index(&mut all, &mut |b| *b = Bounds::Known);
    let taken = verify(&all);
    if let Err(e) = &taken {
        assert_eq!(e.rule, Rule::V25, "{e}");
    }
    assert!(known <= 1, "one index");
    assert_eq!(known == 1, taken.is_ok(), "the stage and the verifier: {taken:?}");
    known == 1
}

/// `for i in lo..<hi` (`..=` when `inclusive`) of `[U32; n]` reading `xs[index(i)]`.
fn looped(n: u32, lo: i128, hi: i128, inclusive: bool, index: impl FnOnce(Expr) -> Expr) -> bool {
    let i = local(Types::U32, 1);
    proved(&module(TyKind::Array(Types::U32, n), &[Types::U32], |xs| {
        vec![for_(1, u32_(lo), u32_(hi), inclusive, vec![read(xs, index(i))])]
    }))
}

#[test]
fn the_variable_of_a_for_is_below_its_end() {
    assert!(looped(4, 0, 4, false, |i| i));
    // A loop as long as the array and one more.
    assert!(!looped(3, 0, 4, false, |i| i));
    // `..=` reaches its end.
    assert!(looped(3, 0, 2, true, |i| i));
    assert!(!looped(3, 0, 3, true, |i| i));
    // A loop that never runs gives its variable no interval: `5..<3`, `i - 3`.
    assert!(!looped(4, 5, 3, false, |i| bin(BinOp::Sub, Overflow::Checked, i, u32_(3))));
    assert!(!looped(4, 5, 3, false, |i| i));
    assert!(!looped(4, 0, 0, false, |i| i));
}

#[test]
fn a_difference_is_proved_when_it_is_not_below_zero() {
    let minus_one = |i| bin(BinOp::Sub, Overflow::Checked, i, u32_(1));
    assert!(looped(4, 1, 5, false, minus_one));
    assert!(!looped(4, 0, 4, false, minus_one));
    // Wrapping below zero gives no interval either.
    assert!(!looped(4, 0, 4, false, |i| bin(BinOp::Sub, Overflow::Wrap, i, u32_(1))));
}

#[test]
fn the_rules_of_and_or_shift_and_remainder() {
    let op = |op, k| move |i| bin(op, Overflow::Checked, i, u32_(k));
    assert!(looped(8, 0, 100, false, op(BinOp::BitAnd, 7)));
    assert!(!looped(7, 0, 100, false, op(BinOp::BitAnd, 7)));
    assert!(looped(5, 0, 7, false, op(BinOp::Rem, 5)));
    assert!(!looped(4, 0, 7, false, op(BinOp::Rem, 5)));
    // Below the divisor, the remainder is the value.
    assert!(looped(3, 0, 3, false, op(BinOp::Rem, 5)));
    assert!(looped(4, 0, 16, false, op(BinOp::Shr, 2)));
    assert!(!looped(3, 0, 16, false, op(BinOp::Shr, 2)));
    // `i | 1` of `i` below 5 has at most the bits of 4: below 8.
    assert!(looped(8, 0, 5, false, op(BinOp::BitOr, 1)));
    assert!(!looped(7, 0, 5, false, op(BinOp::BitOr, 1)));
    assert!(!looped(64, 0, 4, false, op(BinOp::Mul, 2)));
}

/// `for a in 0..=last` of `ty` reading `xs[(f(a)) as U32]` of `[U32; n]`.
fn small(ty: CTy, n: u32, last: i128, f: impl FnOnce(Expr) -> Expr) -> bool {
    let a = local(ty, 1);
    proved(&module(TyKind::Array(Types::U32, n), &[ty], |xs| {
        vec![for_(1, int(ty, 0), int(ty, last), true, vec![read(xs, cast(f(a)))])]
    }))
}

fn bytes(n: u32, last: i128, f: impl FnOnce(Expr) -> Expr) -> bool {
    small(U8_, n, last, f)
}

#[test]
fn a_value_that_may_overflow_its_type_has_no_interval() {
    let shl = |a| bin(BinOp::Shl, Overflow::Checked, a, u32_(4));
    // `a << 4` of `a` up to 15 is at most 240; of `a` up to 31 it drops a bit.
    assert!(bytes(241, 15, shl));
    assert!(!bytes(497, 31, shl));
    let wrap = |a| bin(BinOp::Add, Overflow::Wrap, a, int(U8_, 1));
    assert!(bytes(256, 254, wrap));
    assert!(!bytes(257, 255, wrap));
    let sat = |a| bin(BinOp::Add, Overflow::Sat, a, int(U8_, 1));
    assert!(!bytes(257, 255, sat));
    // A shift by the width panics: no interval.
    assert!(!bytes(256, 0, |a| bin(BinOp::Shl, Overflow::Checked, a, u32_(8))));
}

#[test]
fn a_value_of_u16_has_an_interval() {
    assert!(small(U16_, 300, 299, |a| a));
    assert!(!small(U16_, 299, 299, |a| a));
}

/// `for i in a..<b { for j in c..<d { xs[index(i, j)] } }` of `[U32; n]`.
fn twice(n: u32, (a, b): (i128, i128), (c, d): (i128, i128), index: impl FnOnce(Expr, Expr) -> Expr) -> bool {
    let (i, j) = (local(Types::U32, 1), local(Types::U32, 2));
    proved(&module(TyKind::Array(Types::U32, n), &[Types::U32, Types::U32], |xs| {
        let inner = for_(2, u32_(c), u32_(d), false, vec![read(xs, index(i, j))]);
        vec![for_(1, u32_(a), u32_(b), false, vec![inner])]
    }))
}

fn wrap_sub(a: Expr, b: Expr) -> Expr {
    bin(BinOp::Sub, Overflow::Wrap, a, b)
}

/// `a - b` is not below 0 when the least `a` is the greatest `b` or more,
/// and is at most the greatest `a` less the least `b`; below 0 it wraps
/// (`-%`) or panics, of any operation before it of a least value too small.
#[test]
fn the_least_value_of_each_operation_bounds_a_difference() {
    assert!(!twice(8, (0, 4), (0, 4), wrap_sub));
    // `i` from 3 to 6, `j` from 0 to 3: 0 to 6.
    assert!(twice(7, (3, 7), (0, 4), wrap_sub));
    assert!(!twice(6, (3, 7), (0, 4), wrap_sub));
    let five = |j| wrap_sub(u32_(5), j);
    assert!(looped(6, 0, 4, false, five));
    assert!(!looped(3, 0, 4, false, five));
    let op = |op, i, k| bin(op, Overflow::Checked, i, u32_(k));
    // `i | 1` is at least 1, `i | 4` at least 4.
    assert!(!looped(8, 0, 4, false, |i| wrap_sub(op(BinOp::BitOr, i, 1), u32_(3))));
    assert!(looped(8, 0, 4, false, |i| wrap_sub(op(BinOp::BitOr, i, 4), u32_(4))));
    assert!(!looped(8, 0, 8, false, |i| wrap_sub(op(BinOp::Shr, i, 1), u32_(2))));
    assert!(looped(8, 4, 8, false, |i| wrap_sub(op(BinOp::Shr, i, 1), u32_(2))));
    assert!(!looped(8, 0, 4, false, |i| wrap_sub(op(BinOp::Shl, i, 1), u32_(4))));
    assert!(looped(8, 2, 6, false, |i| wrap_sub(op(BinOp::Shl, i, 1), u32_(4))));
    let sum = |i, j| wrap_sub(bin(BinOp::Add, Overflow::Checked, i, j), u32_(3));
    assert!(!twice(8, (0, 4), (0, 4), sum));
    assert!(twice(8, (1, 4), (2, 4), sum));
    // Of a value not known, `% 4` and `& 3` are at least 0.
    assert!(!unknown(8, |xs, a| vec![read(xs, wrap_sub(op(BinOp::Rem, a, 4), u32_(2)))]));
    assert!(!unknown(8, |xs, a| vec![read(xs, wrap_sub(op(BinOp::BitAnd, a, 3), u32_(1)))]));
    // `for i in (a & 3) ..< 8` is from 0.
    let from_and = |index: fn(Expr) -> Expr| {
        move |xs, a| vec![for_(2, op(BinOp::BitAnd, a, 3), u32_(8), false, vec![read(xs, index(local(Types::U32, 2)))])]
    };
    assert!(!unknown(8, from_and(|i| wrap_sub(i, u32_(3)))));
    assert!(unknown(8, from_and(|i| i)));
}

/// `let a` (local 1) of a value not known, then `stmts(xs, a)`, of `[U32; n]`
/// and a local 2 of `U32`.
fn unknown(n: u32, stmts: impl FnOnce(CTy, Expr) -> Vec<Stmt>) -> bool {
    proved(&module(TyKind::Array(Types::U32, n), &[Types::U32, Types::U32], |xs| {
        let mut body = vec![stmt(StmtKind::Let(LocalId(1), Expr::new(Types::U32, sp(), ExprKind::Zeroed)))];
        body.extend(stmts(xs, local(Types::U32, 1)));
        body
    }))
}

/// The variable of a `for` of a `U32` from a value not known is at least 0.
#[test]
fn a_for_from_a_value_not_known_is_from_zero() {
    let from =
        |end, inclusive| move |xs, a| vec![for_(2, a, u32_(end), inclusive, vec![read(xs, local(Types::U32, 2))])];
    assert!(unknown(4, from(4, false)));
    assert!(!unknown(4, from(5, false)));
    assert!(unknown(4, from(3, true)));
    assert!(!unknown(4, from(4, true)));
    // At least 0, not 1.
    let minus_one = |xs, a| {
        let i = local(Types::U32, 2);
        vec![for_(2, a, u32_(4), false, vec![read(xs, wrap_sub(i, u32_(1)))])]
    };
    assert!(!unknown(4, minus_one));
}

/// `7 & i` is at most 7, whatever `i`; the place `t.0[i]` of a tuple has the
/// type of its field.
#[test]
fn the_forms_a_bound_reads_through() {
    assert!(looped(8, 0, 100, false, |i| bin(BinOp::BitAnd, Overflow::Checked, u32_(7), i)));
    assert!(!looped(7, 0, 100, false, |i| bin(BinOp::BitAnd, Overflow::Checked, u32_(7), i)));
    let written = |n| {
        let mut m = module(TyKind::Array(Types::U32, 4), &[Types::U32], |_| Vec::new());
        let t = m.tys.intern(TyKind::Tuple([m.fns[0].params[0].ty, Types::U32].into()));
        m.fill_all_facts();
        let f = &mut m.fns[0];
        f.locals.push(Local { name: "t".into(), ty: t });
        let field = Place::Field(Box::new(Place::Local(LocalId(2))), 0);
        let write = Place::Index(Box::new(field), Box::new(local(Types::U32, 1)), sp(), Bounds::Checked);
        let zero = stmt(StmtKind::Let(LocalId(2), Expr::new(t, sp(), ExprKind::Zeroed)));
        let body = vec![zero, for_(1, u32_(0), u32_(n), false, vec![stmt(StmtKind::Assign(write, u32_(0)))])];
        f.body = Some(Block { stmts: body, value: None });
        proved(&m)
    };
    assert!(written(4));
    assert!(!written(5));
}

/// `let a = 2` (local 1), `stmts` of `a`, then `xs[a]` of `[U32; 3]`.
fn let_two(stmts: impl FnOnce() -> Vec<Stmt>) -> bool {
    proved(&module(TyKind::Array(Types::U32, 3), &[Types::U32], |xs| {
        let mut body = vec![stmt(StmtKind::Let(LocalId(1), u32_(2)))];
        body.extend(stmts());
        body.push(read(xs, local(Types::U32, 1)));
        body
    }))
}

#[test]
fn a_local_of_one_let_that_nothing_writes_has_the_interval_of_its_value() {
    assert!(let_two(Vec::new));
    let assign = || vec![stmt(StmtKind::Assign(Place::Local(LocalId(1)), u32_(5)))];
    assert!(!let_two(assign));
    // A second `let` of it.
    assert!(!let_two(|| vec![stmt(StmtKind::Let(LocalId(1), u32_(5)))]));
}

#[test]
fn the_base_of_a_span_is_not_proved() {
    let span = TyKind::Span(Types::U32);
    assert!(!proved(&module(span, &[], |xs| vec![read(xs, u32_(0))])));
}

/// `const K = k` and `const L = K - 1`, and `xs[L]` (`xs[K]` when `of_k`) of `[U32; 3]`.
fn constants(k: i128, of_k: bool) -> bool {
    let mut m = module(TyKind::Array(Types::U32, 3), &[], |xs| {
        let c = Expr::new(Types::U32, sp(), ExprKind::Const(ConstId(u32::from(!of_k))));
        vec![read(xs, c)]
    });
    let konst = |init| ConstDef { name: "K".into(), ty: Types::U32, init };
    let k_ = Expr::new(Types::U32, sp(), ExprKind::Const(ConstId(0)));
    m.consts = vec![konst(u32_(k)), konst(bin(BinOp::Sub, Overflow::Checked, k_, u32_(1)))];
    proved(&m)
}

#[test]
fn a_constant_has_the_interval_of_its_initializer() {
    assert!(constants(2, true));
    assert!(!constants(3, true));
    assert!(constants(3, false));
    assert!(!constants(4, false));
}

/// V-28: the variable of a `for` is not written in its body, by `write`.
fn writes_its_variable(write: Stmt) {
    let mut m = module(TyKind::Array(Types::U32, 3), &[Types::U32], |xs| {
        vec![for_(1, u32_(0), u32_(3), false, vec![write, read(xs, local(Types::U32, 1))])]
    });
    let err = verify(&m).expect_err("V-28");
    assert_eq!(err.rule, Rule::V28, "{err}");
    // Not proved by the stage: it is no fixed local, and the verifier rejects the loop itself.
    crate::bounds::module(&mut m);
    let mut known = 0;
    each_index(&mut m, &mut |b| known += usize::from(*b == Bounds::Known));
    assert_eq!(known, 1, "the stage proves what V-28 makes true");
}

#[test]
fn the_variable_of_a_for_is_not_written_in_its_body() {
    writes_its_variable(stmt(StmtKind::Assign(Place::Local(LocalId(1)), u32_(0))));
    writes_its_variable(stmt(StmtKind::Let(LocalId(1), u32_(0))));
    writes_its_variable(for_(1, u32_(0), u32_(1), false, Vec::new()));
}

/// The stage on a source: the indexes it proves are dumped `[known `.
#[test]
fn the_stage_proves_the_indexes_of_a_source() {
    let src = "const K: U32 = 4\nconst L: U32 = K - 1\n\
               pub fn f(xs: [U32; 4]) -> U32 {\n  var s: U32 = 0\n  for i in 0 ..< K {\n    s = s + xs[i]\n  }\n  \
               for i in 0 ..= 3 {\n    s = s + xs[i]\n  }\n  for i in 0 ..= 4 {\n    s = s + xs[i % 4] + xs[i & 3] + xs[i]\n  }\n  \
               let j = s & 1\n  s + xs[K - 1] + xs[L] + xs[j] + xs[s]\n}\n";
    let d = crate::dump::dump_item(&crate::tests::core(src), "t.f");
    let known = ["xs[known i@2]", "xs[known i@3]", "xs[known (i@4 % 4:U32)]", "xs[known (i@4 & 3:U32)]"];
    for k in known.into_iter().chain(["xs[known (const t.K - 1:U32)]", "xs[known const t.L]", "xs[known j]"]) {
        assert!(d.contains(k), "{k}: {d}");
    }
    // `i` up to 4 of `0 ..= 4`, and a local written.
    assert!(d.contains("+ xs[i@4])") && d.contains("+ xs[s])"), "{d}");
    assert_eq!(d.matches("[known ").count(), 7, "{d}");
}

/// R-319: a chain of constants is read once each, on no deep recursion:
/// `C{k} = C{k-1} & C{k-1}`, which a walk without the table reads 2^k times.
#[test]
fn a_chain_of_constants_is_read_once_each() {
    let mut src = String::from("const C0: U32 = 1\n");
    for k in 1..300 {
        src.push_str(&format!("const C{k}: U32 = C{} & C{}\n", k - 1, k - 1));
    }
    src.push_str("pub fn f(xs: [U32; 2]) -> U32 {\n  xs[C299]\n}\n");
    let d = onsa_diag::stack::spawn("consts", move || crate::dump::dump_item(&crate::tests::core(&src), "t.f"));
    let d = d.unwrap().join().unwrap();
    assert!(d.contains("xs[known const t.C299]"), "{d}");
}

/// A flow of a `prev~` of `U32` (field 0) and a delay of 5 (its ring field
/// 1, its write position field 2), lowered.
fn ring() -> Module {
    crate::tests::core("pub flow f(x: U32 at sample) -> U32 at sample {\n  prev~(x) + delay~(x, 5)\n}\n")
}

/// The state of the flow of `m`, its type and the expression `s` of the parameter of `tick`.
fn state(m: &Module) -> (TypeId, CTy, Expr) {
    let (id, tick) = (m.flows[0].fns.state, m.fns.iter().find(|f| f.name == "t.f.tick").expect("tick"));
    let p = &tick.params[0];
    (id, p.ty, Expr::new(p.ty, sp(), ExprKind::Local(p.local)))
}

fn field(s: &Expr, i: u32) -> Expr {
    Expr::new(Types::U32, sp(), ExprKind::Field { base: Box::new(s.clone()), index: i })
}

/// The module `m` with `stmts` (given `s`) at the end of the statements of `tick`, verified.
fn tick_with(mut m: Module, stmts: impl FnOnce(&Expr) -> Vec<Stmt>) -> Result<(), crate::VerifyError> {
    let s = state(&m).2;
    let tick = m.fns.iter_mut().find(|f| f.name == "t.f.tick").expect("tick");
    tick.body.as_mut().expect("a body").stmts.extend(stmts(&s));
    verify(&m)
}

fn v26(r: Result<(), crate::VerifyError>) {
    assert_eq!(r.expect_err("V-26").rule, Rule::V26);
}

/// The write position of a delay is below the length of its ring, and the
/// field of a `prev~` of `U32` has no interval: the index `s.1[s.2]` of the
/// lowering is proved (V-25), into a ring of 5 and not of 4.
#[test]
fn the_write_position_of_a_delay_is_below_the_length_of_its_ring() {
    let mut m = ring();
    let (id, ty, s) = state(&m);
    let (five, four) = (m.tys.intern(TyKind::Array(Types::U32, 5)), m.tys.intern(TyKind::Array(Types::U32, 4)));
    let (consts, below) = (crate::bounds::consts(&m), crate::bounds::below(&m));
    assert_eq!(below.iter().collect::<Vec<_>>(), [(&(id, 2), &5)]);
    let env = crate::bounds::Env::new(Parts { tys: &m.tys, types: &m.types }, (&consts, &below), None);
    assert_eq!(env.interval(&field(&s, 2)), Some(crate::bounds::Iv { lo: 0, hi: 4 }));
    assert_eq!((env.interval(&field(&s, 0)), env.below(ty, 2)), (None, Some(5)));
    assert!(env.proved(&field(&s, 2), five) && !env.proved(&field(&s, 2), four));
    // The stage proved the read and the write of the ring: the dump of `tick`.
    let d = crate::dump::dump_item(&m, "t.f.tick");
    assert_eq!(d.matches("s.1[known s.2]").count(), 2, "{d}");
}

/// V-26: a value written to the write position is proved below 5.
#[test]
fn a_write_of_the_write_position_is_proved_below_its_length() {
    let assign =
        |v: fn(&Expr) -> Expr| move |s: &Expr| vec![stmt(StmtKind::Assign(field(s, 2).as_place().unwrap(), v(s)))];
    v26(tick_with(ring(), assign(|_| u32_(5))));
    assert!(tick_with(ring(), assign(|_| u32_(4))).is_ok());
    // `w + 1` with no `% 5`; with it, below 5.
    fn next(s: &Expr) -> Expr {
        bin(BinOp::Add, Overflow::Checked, field(s, 2), u32_(1))
    }
    v26(tick_with(ring(), assign(next)));
    assert!(tick_with(ring(), assign(|s| bin(BinOp::Rem, Overflow::Checked, next(s), u32_(5)))).is_ok());
    // Until W8-07, `Zeroed` is 0; a value not known is not below 5.
    assert!(tick_with(ring(), assign(|_| Expr::new(Types::U32, sp(), ExprKind::Zeroed))).is_ok());
    v26(tick_with(ring(), assign(|s| field(s, 0))));
    // The field of the `prev~` is below no length.
    let prev = |s: &Expr| vec![stmt(StmtKind::Assign(field(s, 0).as_place().unwrap(), u32_(9)))];
    assert!(tick_with(ring(), prev).is_ok());
}

/// V-26: a struct literal of the state has its write position below 5;
/// an `inout` argument is not the write position itself.
#[test]
fn a_struct_literal_and_an_inout_argument_of_the_write_position() {
    let literal = |w: i128| {
        let m = ring();
        let (id, ty, _) = state(&m);
        let TypeDefKind::Struct { fields } = &m.types[id.0 as usize].kind else { panic!("a struct") };
        let value = |(i, &(_, t)): (u32, &(String, CTy))| {
            (i, if i == 2 { u32_(w) } else { Expr::new(t, sp(), ExprKind::Zeroed) })
        };
        let lit = Expr::new(ty, sp(), ExprKind::Struct { ty: id, fields: (0..).zip(fields).map(value).collect() });
        tick_with(m, |s| vec![stmt(StmtKind::Assign(s.as_place().unwrap(), lit))])
    };
    v26(literal(5));
    assert!(literal(4).is_ok());
    // `h(inout s.2)` gives the callee the field to write any value to; `h(inout s.0)` and `h(inout s)` do not.
    let call = |arg: fn(&Expr) -> Expr| {
        let mut m = ring();
        let (h, ty) = (FnId(m.fns.len() as u32), arg(&state(&m).2).ty);
        m.fns.push(FnDef {
            name: "h".into(),
            params: vec![Param { local: LocalId(0), mode: Mode::Inout, ty }],
            ret: Types::UNIT,
            sret: false,
            rt: true,
            locals: vec![Local { name: "a".into(), ty }],
            body: Some(Block::default()),
            span: sp(),
            fp_relaxed: false,
            test: None,
            decl: None,
            hoisted: Vec::new(),
        });
        tick_with(m, |s| {
            let args = vec![Arg { mode: Mode::Inout, expr: arg(s) }];
            vec![stmt(StmtKind::Expr(Expr::new(Types::UNIT, sp(), ExprKind::Call { fn_: h, args })))]
        })
    };
    v26(call(|s| field(s, 2)));
    assert!(call(|s| field(s, 0)).is_ok());
    assert!(call(|s| s.clone()).is_ok());
}

/// R-533: the statement of the iterable of a `for` over a row of length 0
/// that the stage proves in range is dropped; one of an index not proved stays.
#[test]
fn the_statement_of_an_iterable_proved_in_range_is_dropped() {
    let src = "pub fn g(gs: [[U32; 0]; 2], i: U32) -> U32 {\n  var s: U32 = 0\n  for x in gs[1] {\n    s = s + x\n  }\n  \
               for x in gs[i] {\n    s = s + x\n  }\n  s\n}\n";
    let d = crate::dump::dump_item(&crate::tests::core(src), "t.g");
    assert!(!d.contains("gs[known") && d.contains("\n  gs[i]\n"), "{d}");
}

/// The index of a replica of a `par~` from 2 is `i -% 2` in a loop of `i`
/// over 2..<5 (§11.5), proved below 3; and an index by `i` itself in its
/// body has the interval of the variable of the `for`: `T[i + (x % 3)]` is
/// at most 4 + 2, below 8.
#[test]
fn the_variable_of_the_replicas_of_a_par_is_that_of_a_for() {
    let src = "const T: [U32; 8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
               pub flow f(x: U32 at sample) -> [U32; 3] at sample {\n  par~ i in 2 ..< 5 { delay~(T[i + (x % 3)], 3) }\n}\n";
    let m = crate::tests::core(src);
    let d = crate::dump::dump_item(&m, "t.f.tick");
    assert!(d.contains("for i in 2:U32..5:U32 {") && !d.contains("let i"), "{d}");
    assert!(d.contains("const t.T[known (i + (x % 3:U32))]") && d.contains("s.0[known (i -% 2:U32)].1 ="), "{d}");
    // The index of the replicas is of no check.
    assert!(!d.contains("(i - 2:U32)") && !d.contains("[(i -% 2:U32)]"), "{d}");
}
