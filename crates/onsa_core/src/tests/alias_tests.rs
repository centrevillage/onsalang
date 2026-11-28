//! W8-03 U6a: the statement `Alias` (a local that names a place) and the
//! first part of V-21, in a Core made by hand: an alias is defined by its
//! one `Alias` alone, one not written through is the root of no write, and
//! a write through one writes the place it names (`alias::resolve`, V-05).
//! U6a2: its second part, no use of an alias once a place that may overlap
//! the one it names is written not through it.

use onsa_diag::{FileId, Span};

use crate::alias::{resolve, table};
use crate::ir::*;
use crate::{Rule, VerifyError, verify};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// The position of the node that breaks a rule.
fn at() -> Span {
    Span::new(FileId(0), 7, 9)
}

/// The parameter `xs: [[U32; 2]; 2]` of `g`.
const XS: LocalId = LocalId(0);
/// `i: U32`, a value.
const I: LocalId = LocalId(1);
/// `r: [U32; 2]`, an alias written through.
const R: LocalId = LocalId(2);
/// `q: [U32; 2]`, an alias not written through.
const Q: LocalId = LocalId(3);
/// `s: U32`, an alias written through.
const S: LocalId = LocalId(4);
/// `p: U32`, an alias not written through.
const P: LocalId = LocalId(5);
/// `t: (U32, U32)`, a value.
const T: LocalId = LocalId(6);

fn row(m: &mut Module) -> CTy {
    m.tys.intern(TyKind::Array(Types::U32, 2))
}

fn n(v: i128) -> Expr {
    Expr::new(Types::U32, sp(), ExprKind::Lit(Lit::Int(v)))
}

fn unit() -> Expr {
    Expr::new(Types::UNIT, sp(), ExprKind::Lit(Lit::Unit))
}

fn st(span: Span, kind: StmtKind) -> Stmt {
    Stmt { span, kind }
}

/// `base[k]`.
fn at_index(base: Place, k: i128) -> Place {
    Place::Index(Box::new(base), Box::new(n(k)), sp(), Bounds::Checked)
}

fn alias(l: LocalId, p: Place) -> Stmt {
    st(at(), StmtKind::Alias(l, p))
}

/// `callee(inout x)`, of `callee(inout y: U32)`.
fn pass(x: Expr) -> Stmt {
    let call = ExprKind::Call { fn_: FnId(0), args: vec![Arg { mode: Mode::Inout, expr: x }] };
    st(at(), StmtKind::Expr(Expr::new(Types::UNIT, at(), call)))
}

/// `l[k]` of the alias `l: [U32; 2]`, an expression.
fn elem(m: &mut Module, l: LocalId, k: i128) -> Expr {
    let base = Box::new(Expr::new(row(m), sp(), ExprKind::Local(l)));
    Expr::new(Types::U32, sp(), ExprKind::Index { base, index: Box::new(n(k)), bounds: Bounds::Checked })
}

/// `callee(inout y: U32)`, `g(<mode> xs: [[U32; 2]; 2])` of the locals
/// above and the statements `stmts`, made of the module `m` gives, and
/// `both(inout y: U32, z: U32)`.
fn module(mode: Mode, stmts: impl FnOnce(&mut Module) -> Vec<Stmt>) -> Module {
    let mut m = Module::default();
    let r = row(&mut m);
    let grid = m.tys.intern(TyKind::Array(r, 2));
    let pair = m.tys.intern(TyKind::Tuple(vec![Types::U32, Types::U32].into_boxed_slice()));
    let stmts = stmts(&mut m);
    let fn_of = |name: &str, params: Vec<Param>, locals: Vec<Local>, stmts: Vec<Stmt>| FnDef {
        name: name.into(),
        params,
        ret: Types::UNIT,
        sret: false,
        rt: false,
        locals,
        body: Some(Block { stmts, value: Some(Box::new(unit())) }),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    };
    let y = Param { local: LocalId(0), mode: Mode::Inout, ty: Types::U32 };
    m.fns.push(fn_of("callee", vec![y], vec![Local::value("y", Types::U32)], vec![]));
    let of = |name: &str, ty, write| Local { name: name.into(), ty, kind: LocalKind::Alias { write } };
    let locals = vec![
        Local::value("xs", grid),
        Local::value("i", Types::U32),
        of("r", r, true),
        of("q", r, false),
        of("s", Types::U32, true),
        of("p", Types::U32, false),
        Local::value("t", pair),
    ];
    m.fns.push(fn_of("g", vec![Param { local: XS, mode, ty: grid }], locals, stmts));
    let z = Param { local: LocalId(1), mode: Mode::Borrow, ty: Types::U32 };
    let yz = vec![Local::value("y", Types::U32), Local::value("z", Types::U32)];
    let y = Param { local: LocalId(0), mode: Mode::Inout, ty: Types::U32 };
    m.fns.push(fn_of("both", vec![y, z], yz, vec![]));
    m.fill_all_facts();
    m
}

fn rejected(m: &Module, rule: Rule, message: &str) -> VerifyError {
    let err = verify(m).expect_err(message);
    assert!(err.message.contains(message) && err.rule == rule && err.span == Some(at()), "{rule}: {err}");
    err
}

/// V-21: a local of `LocalKind::Alias` is defined by an `Alias` alone, and
/// by one only (in sibling arms too); an `Alias` defines no value.
#[test]
fn an_alias_is_defined_by_its_one_alias_statement_alone() {
    let differ = "of an alias and its definition differ";
    let m = module(Mode::Inout, |m| vec![st(at(), StmtKind::Let(R, Expr::new(row(m), sp(), ExprKind::Zeroed)))]);
    rejected(&m, Rule::V21, &format!("local 2 {differ}"));
    let m = module(Mode::Inout, |_| vec![alias(I, at_index(at_index(Place::Local(XS), 0), 1))]);
    rejected(&m, Rule::V21, &format!("local 1 {differ}"));
    let empty = || Block { stmts: vec![], value: Some(Box::new(unit())) };
    let m = module(Mode::Inout, |_| vec![st(at(), StmtKind::for_excluded(S, n(0), n(2), empty()))]);
    rejected(&m, Rule::V21, &format!("local 4 {differ}"));
    let second = "a second `Alias` of the alias 2";
    let m =
        module(Mode::Inout, |_| vec![alias(R, at_index(Place::Local(XS), 0)), alias(R, at_index(Place::Local(XS), 1))]);
    rejected(&m, Rule::V21, second);
    let arm = |k| Block { stmts: vec![alias(R, at_index(Place::Local(XS), k))], value: Some(Box::new(unit())) };
    let yes = Expr::new(Types::BOOL, sp(), ExprKind::Lit(Lit::Bool(true)));
    let m = module(Mode::Inout, |_| vec![st(sp(), StmtKind::If(yes, arm(0), arm(1)))]);
    rejected(&m, Rule::V21, second);
    // Accepted: a write through `r`, a read of `q`.
    let m = module(Mode::Inout, |m| {
        let read = st(sp(), StmtKind::Expr(elem(m, Q, 0)));
        let write = st(sp(), StmtKind::Assign(at_index(Place::Local(R), 1), n(3)));
        vec![
            alias(R, at_index(Place::Local(XS), 0)),
            write,
            pass(elem(m, R, 0)),
            alias(Q, at_index(Place::Local(XS), 1)),
            read,
        ]
    });
    verify(&m).expect("aliases");
}

/// V-21: an alias not written through is the root of no assignment, no
/// `inout` argument (inside the block of an argument too, `walk::written_places`)
/// and no place of an alias written through; it may name a place of a
/// borrowed parameter.
#[test]
fn an_alias_not_written_through_is_the_root_of_no_write() {
    let msg = "a write through the alias 3 not written through";
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let m = module(Mode::Inout, |_| vec![q0(), st(at(), StmtKind::Assign(at_index(Place::Local(Q), 1), n(3)))]);
    rejected(&m, Rule::V21, msg);
    let m = module(Mode::Inout, |m| vec![q0(), pass(elem(m, Q, 1))]);
    rejected(&m, Rule::V21, msg);
    let m = module(Mode::Inout, |_| vec![q0(), alias(R, Place::Local(Q))]);
    rejected(&m, Rule::V21, msg);
    // `callee(inout { alias p = xs[0][0]; p })`, as lowering makes one of a planar `inout` argument.
    let named = |l| {
        let block = Block {
            stmts: vec![alias(l, at_index(at_index(Place::Local(XS), 0), 0))],
            value: Some(Box::new(Expr::new(Types::U32, sp(), ExprKind::Local(l)))),
        };
        pass(Expr::new(Types::U32, sp(), ExprKind::Block(block)))
    };
    rejected(&module(Mode::Inout, |_| vec![named(P)]), Rule::V21, "a write through the alias 5 not written through");
    verify(&module(Mode::Inout, |_| vec![named(S)])).expect("an `inout` block through `s`");
    let m = module(Mode::Borrow, |m| vec![q0(), st(sp(), StmtKind::Expr(elem(m, Q, 1)))]);
    verify(&m).expect("a borrowed place read through `q`");
}

/// V-05 and V-28 of the place an alias written through names: of a
/// borrowed parameter, or of the variable of a `for` in its body, it is
/// rejected at the `Alias`, as a write of that place.
#[test]
fn an_alias_written_through_writes_the_place_it_names() {
    let m = module(Mode::Borrow, |_| vec![alias(R, at_index(Place::Local(XS), 0))]);
    rejected(&m, Rule::V05, "write to the borrowed parameter `xs`");
    let m = module(Mode::Borrow, |_| vec![alias(S, at_index(at_index(Place::Local(XS), 1), 0))]);
    rejected(&m, Rule::V05, "write to the borrowed parameter `xs`");
    let body = Block { stmts: vec![alias(S, Place::Local(I))], value: Some(Box::new(unit())) };
    let m = module(Mode::Inout, |_| vec![st(sp(), StmtKind::for_excluded(I, n(0), n(2), body))]);
    rejected(&m, Rule::V28, "the variable 1 of a `for` written in its body");
}

/// `alias::resolve`: the root of a place that is an alias is replaced by
/// the place it names, of an alias inside a block expression and of an
/// alias of an alias too; another root is itself. Of a function with no
/// local of `LocalKind::Alias`, the table is empty (it is not walked).
#[test]
fn resolve_replaces_an_alias_by_the_place_it_names() {
    let xs_i = || {
        let i = Box::new(Expr::new(Types::U32, sp(), ExprKind::Local(I)));
        Place::Index(Box::new(Place::Local(XS)), i, sp(), Bounds::Checked)
    };
    let m = module(Mode::Inout, |_| {
        let inner = Block { stmts: vec![alias(S, at_index(Place::Local(R), 1))], value: Some(Box::new(unit())) };
        let inner = Expr::new(Types::UNIT, sp(), ExprKind::Block(inner));
        vec![st(sp(), StmtKind::Let(I, n(1))), alias(R, xs_i()), st(sp(), StmtKind::Expr(inner))]
    });
    verify(&m).expect("aliases");
    let t = table(&m.fns[1]);
    let same = |p: &Place, want: Place| assert_eq!(format!("{:?}", resolve(&t, p)), format!("{want:?}"));
    same(&Place::Local(R), xs_i());
    same(&at_index(Place::Local(R), 0), at_index(xs_i(), 0));
    same(&Place::Local(S), at_index(xs_i(), 1));
    same(&Place::Field(Box::new(Place::Local(S)), 2), Place::Field(Box::new(at_index(xs_i(), 1)), 2));
    same(&Place::Local(I), Place::Local(I));
    same(&at_index(Place::Local(XS), 1), at_index(Place::Local(XS), 1));
    let mut values = m.fns[1].clone();
    values.locals.iter_mut().for_each(|l| l.kind = LocalKind::Value);
    assert_eq!(format!("{:?}", resolve(&table(&values), &Place::Local(S))), format!("{:?}", Place::Local(S)));
}

/// The first user (R-433, §3.5): a planar `inout` argument whose index is
/// not repeatable is named by an alias written through, its index
/// evaluated once there; one of a repeatable index stays the place, with
/// no alias and no temporary (`build::stays`).
#[test]
fn a_planar_inout_argument_of_an_index_with_an_effect_is_an_alias() {
    let src = "fn next(inout n: U32) -> U32 {\n  n = n + 1\n  n - 1\n}\n\nfn zero(inout xs: [Span[U8]; 2]) {\n  xs[0].fill!(0)\n}\n\npub fn f(inout ws: [[[U8; 2]; 2]; 2]) {\n  var i: U32 = 0\n  zero(inout ws[next(inout i)])\n  zero(inout ws[i])\n}\n";
    let d = crate::dump(&super::core(src));
    let at = d.find("fn t.f(").expect("t.f");
    let f = &d[at..];
    assert_eq!(f.matches("alias inout __planar").count(), 1, "{f}");
    assert!(f.contains("= ws[t.next(inout i)]") && !f.contains("let __"), "{f}");
}

/// V-05 of an `inout` block (`walk::written_places`): its value is a place,
/// of no root a `Let` of the block declares (`callee(inout { let i = 0; i })`
/// would write a temporary); a root outside the block is the place written.
#[test]
fn an_inout_block_writes_no_local_of_its_own() {
    let block = |stmts, value| pass(Expr::new(Types::U32, sp(), ExprKind::Block(Block { stmts, value })));
    let own = || vec![st(sp(), StmtKind::Let(I, n(0)))];
    let i = || Some(Box::new(Expr::new(Types::U32, sp(), ExprKind::Local(I))));
    rejected(&module(Mode::Inout, |_| vec![block(own(), i())]), Rule::V05, "inout argument is not a place");
    rejected(&module(Mode::Inout, |_| vec![block(vec![], Some(Box::new(n(3))))]), Rule::V05, "not a place");
    // `callee(inout { alias p = xs[0][0]; xs[1][1] })`: the place of `xs` is written.
    let m = module(Mode::Inout, |m| {
        let (r, ix) = (row(m), |base, k| ExprKind::Index {
            base: Box::new(base),
            index: Box::new(n(k)),
            bounds: Bounds::Checked,
        });
        let xs = Expr::new(m.tys.intern(TyKind::Array(r, 2)), sp(), ExprKind::Local(XS));
        let v = Expr::new(Types::U32, sp(), ix(Expr::new(r, sp(), ix(xs, 1)), 1));
        vec![block(vec![alias(P, at_index(at_index(Place::Local(XS), 0), 0))], Some(Box::new(v)))]
    });
    verify(&m).expect("an `inout` block of a place outside it");
}

/// V-01 and V-04 of an `Alias`: the place it names is of the type of the
/// alias, and its root is seen there (not the alias itself).
#[test]
fn an_alias_names_a_seen_place_of_its_type() {
    rejected(&module(Mode::Inout, |_| vec![alias(R, Place::Local(XS))]), Rule::V01, "alias");
    rejected(&module(Mode::Inout, |_| vec![alias(R, Place::Local(R))]), Rule::V04, "");
}

/// V-28 through an alias: `let i = 0; alias inout s = i; for i in 0 ..< 2 { s = 5 }`
/// writes the variable of the `for` in its body (`alias::resolve` of the root).
#[test]
fn a_write_through_an_alias_of_the_variable_of_a_for_is_rejected() {
    let body = Block { stmts: vec![st(at(), StmtKind::Assign(Place::Local(S), n(5)))], value: Some(Box::new(unit())) };
    let m = module(Mode::Inout, |_| {
        vec![
            st(sp(), StmtKind::Let(I, n(0))),
            alias(S, Place::Local(I)),
            st(sp(), StmtKind::for_excluded(I, n(0), n(2), body)),
        ]
    });
    rejected(&m, Rule::V28, "the variable 1 of a `for` written in its body");
}

/// `xs[a][b]`.
fn xs(a: i128, b: i128) -> Place {
    at_index(at_index(Place::Local(XS), a), b)
}

/// `p = v`.
fn set(p: Place, v: i128) -> Stmt {
    st(sp(), StmtKind::Assign(p, n(v)))
}

/// A read of `l[k]`, of the alias `l: [U32; 2]`, its local at the position
/// of an error.
fn read(m: &mut Module, l: LocalId, k: i128) -> Stmt {
    let base = Box::new(Expr::new(row(m), at(), ExprKind::Local(l)));
    let e = ExprKind::Index { base, index: Box::new(n(k)), bounds: Bounds::Checked };
    st(sp(), StmtKind::Expr(Expr::new(Types::U32, sp(), e)))
}

/// A read of the alias `l: U32`, at the position of an error.
fn read_one(l: LocalId) -> Stmt {
    st(sp(), StmtKind::Expr(Expr::new(Types::U32, at(), ExprKind::Local(l))))
}

fn block(stmts: Vec<Stmt>) -> Block {
    Block { stmts, value: Some(Box::new(unit())) }
}

fn yes() -> Expr {
    Expr::new(Types::BOOL, sp(), ExprKind::Lit(Lit::Bool(true)))
}

const LOST: &str = "used after a place it names was written not through it";

/// V-21, the second part: once a place that may overlap the place of an
/// alias is written not through it, the alias is neither read nor the root
/// of a write; an index is the same place whatever its value
/// (`paths::disjoint`); a write of another root or through the alias
/// itself loses nothing.
#[test]
fn an_alias_is_not_used_once_its_place_is_written_not_through_it() {
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let m = module(Mode::Inout, |m| vec![q0(), set(xs(0, 1), 3), read(m, Q, 0)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    // At another index, of any value: the indices are not compared.
    let m = module(Mode::Inout, |m| vec![q0(), set(xs(1, 0), 3), read(m, Q, 0)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    // The whole of its root, a place its place is in.
    let whole = |m: &mut Module| {
        let r = row(m);
        let grid = m.tys.intern(TyKind::Array(r, 2));
        st(sp(), StmtKind::Assign(Place::Local(XS), Expr::new(grid, sp(), ExprKind::Zeroed)))
    };
    let m = module(Mode::Inout, |m| vec![q0(), whole(m), read(m, Q, 1)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    // A write through the alias lost: its root, at the assignment.
    let r0 = || alias(R, at_index(Place::Local(XS), 0));
    let m = module(Mode::Inout, |_| {
        vec![r0(), set(xs(1, 0), 3), st(at(), StmtKind::Assign(at_index(Place::Local(R), 1), n(4)))]
    });
    rejected(&m, Rule::V21, &format!("the alias 2 {LOST}"));
    // Accepted: a write of another root, and through the alias itself.
    let m = module(Mode::Inout, |m| {
        vec![
            st(sp(), StmtKind::Let(I, n(0))),
            r0(),
            set(Place::Local(I), 1),
            set(at_index(Place::Local(R), 1), 2),
            read(m, R, 0),
        ]
    });
    verify(&m).expect("writes of another root and through the alias");
}

/// `paths::disjoint`: a write of another field of the root is no write of
/// the place of an alias, a write of the same field is.
#[test]
fn a_write_of_another_field_keeps_an_alias() {
    let pair = |m: &mut Module| {
        let t = m.tys.intern(TyKind::Tuple(vec![Types::U32, Types::U32].into_boxed_slice()));
        st(sp(), StmtKind::Let(T, Expr::new(t, sp(), ExprKind::Zeroed)))
    };
    let field = |i| Place::Field(Box::new(Place::Local(T)), i);
    let m = module(Mode::Inout, |m| vec![pair(m), alias(P, field(0)), set(field(1), 3), read_one(P)]);
    verify(&m).expect("another field");
    let m = module(Mode::Inout, |m| vec![pair(m), alias(P, field(0)), set(field(0), 3), read_one(P)]);
    rejected(&m, Rule::V21, &format!("the alias 5 {LOST}"));
}

/// The places an `inout` argument writes are written once the call has
/// evaluated all its arguments: an alias read by a later argument of the
/// call is read before, and lost after it.
#[test]
fn an_inout_argument_writes_after_all_the_arguments() {
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let xs00 = |m: &mut Module| {
        let (r, ix) = (row(m), |base, k| ExprKind::Index {
            base: Box::new(base),
            index: Box::new(n(k)),
            bounds: Bounds::Checked,
        });
        let xs = Expr::new(m.tys.intern(TyKind::Array(r, 2)), sp(), ExprKind::Local(XS));
        Expr::new(Types::U32, sp(), ix(Expr::new(r, sp(), ix(xs, 0)), 0))
    };
    let m = module(Mode::Inout, |m| vec![q0(), pass(xs00(m)), read(m, Q, 1)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    let both = |m: &mut Module| {
        let StmtKind::Expr(q) = read(m, Q, 1).kind else { unreachable!() };
        let args = vec![Arg { mode: Mode::Inout, expr: xs00(m) }, Arg { mode: Mode::Borrow, expr: q }];
        st(sp(), StmtKind::Expr(Expr::new(Types::UNIT, sp(), ExprKind::Call { fn_: FnId(2), args })))
    };
    verify(&module(Mode::Inout, |m| vec![q0(), both(m)])).expect("read by a later argument");
    let m = module(Mode::Inout, |m| vec![q0(), both(m), read(m, Q, 0)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
}

/// The arms of an `If` begin with the state before them; past them an
/// alias lost in either is lost.
#[test]
fn an_alias_lost_in_an_arm_is_lost_past_the_arms() {
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let arms =
        |m: &mut Module| st(sp(), StmtKind::If(yes(), block(vec![set(xs(0, 0), 1)]), block(vec![read(m, Q, 0)])));
    verify(&module(Mode::Inout, |m| vec![q0(), arms(m)])).expect("read in the other arm");
    let m = module(Mode::Inout, |m| vec![q0(), arms(m), read(m, Q, 1)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    let other =
        |m: &mut Module| st(sp(), StmtKind::If(yes(), block(vec![read(m, Q, 0)]), block(vec![set(xs(1, 0), 1)])));
    let m = module(Mode::Inout, |m| vec![q0(), other(m), read(m, Q, 1)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
}

/// An alias of before a loop, used in it and then lost in it, would be used
/// lost in its next turn; one written after the loop, or defined in its
/// body (again in each turn), is not.
#[test]
fn an_alias_used_in_a_loop_that_then_writes_its_place_is_rejected() {
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let looped = "the alias 3 used in a loop that then writes a place it names not through it";
    let write = || st(at(), StmtKind::Assign(xs(1, 1), n(2)));
    let m = module(Mode::Inout, |m| vec![q0(), st(sp(), StmtKind::While(yes(), block(vec![read(m, Q, 0), write()])))]);
    rejected(&m, Rule::V21, looped);
    // In an inner loop, and of a `for`.
    let m = module(Mode::Inout, |m| {
        let inner = st(sp(), StmtKind::While(yes(), block(vec![read(m, Q, 0)])));
        vec![q0(), st(sp(), StmtKind::for_excluded(I, n(0), n(2), block(vec![inner, write()])))]
    });
    rejected(&m, Rule::V21, looped);
    let m = module(Mode::Inout, |m| {
        vec![q0(), st(sp(), StmtKind::for_excluded(I, n(0), n(2), block(vec![read(m, Q, 0)]))), set(xs(0, 0), 1)]
    });
    verify(&m).expect("written after the loop");
    let m = module(Mode::Inout, |m| {
        vec![st(sp(), StmtKind::While(yes(), block(vec![q0(), read(m, Q, 0), set(xs(0, 0), 1)])))]
    });
    verify(&m).expect("defined in the body");
}

/// The walk does not tell code no path reaches: a read after a `Return`
/// and after a write is rejected, as is one past an arm that writes and
/// returns.
#[test]
fn a_read_no_path_reaches_after_a_write_is_rejected() {
    let q0 = || alias(Q, at_index(Place::Local(XS), 0));
    let ret = || st(sp(), StmtKind::Return(None));
    let m = module(Mode::Inout, |m| vec![q0(), set(xs(0, 0), 1), ret(), read(m, Q, 0)]);
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
    let m = module(Mode::Inout, |m| {
        vec![q0(), st(sp(), StmtKind::If(yes(), block(vec![set(xs(0, 0), 1), ret()]), block(vec![]))), read(m, Q, 0)]
    });
    rejected(&m, Rule::V21, &format!("the alias 3 {LOST}"));
}

/// An alias at the root of the place of another (`alias s = r[1]`): a write
/// through `s` is through `r` too, and loses neither; one through `r` not
/// through `s` loses `s`, and a write of the root loses both.
#[test]
fn a_write_through_a_nested_alias_is_through_the_alias_at_its_root() {
    let nested = || vec![alias(R, at_index(Place::Local(XS), 0)), alias(S, at_index(Place::Local(R), 1))];
    let m = module(Mode::Inout, |m| [nested(), vec![set(Place::Local(S), 3), read(m, R, 0), read_one(S)]].concat());
    verify(&m).expect("through `s` and `r`");
    let m = module(Mode::Inout, |m| {
        [nested(), vec![set(at_index(Place::Local(R), 0), 3), read(m, R, 1), read_one(S)]].concat()
    });
    rejected(&m, Rule::V21, &format!("the alias 4 {LOST}"));
    let m = module(Mode::Inout, |m| [nested(), vec![set(xs(0, 1), 3), read(m, R, 1)]].concat());
    rejected(&m, Rule::V21, &format!("the alias 2 {LOST}"));
}
