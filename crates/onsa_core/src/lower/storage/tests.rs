//! `hoisted` (R-481, R-484, S-1118 (2)): which locals a view out of a scope
//! reads, on lowered sources and on Core made by hand (the forms U2c2b makes).

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::tests::core;
use crate::verify;

const COMMON: &str = "rt fn take(s: Span[F32]) -> F32 {\n  s[0]\n}\nrt fn mk(v: F32) -> [F32; 4] {\n  [v; 4]\n}\n\
pub struct Stereo { l: F32, r: F32 }\nflow pair(l: F32 at sample, r: F32 at sample) -> Stereo at sample {\n  Stereo { l: l, r: r }\n}\n\
rt fn take_in(i: pair.In) -> F32 {\n  i.l[0] - i.r[0]\n}\nstruct G[T] { xs: [F32; 4], t: T }\n";

/// The names of the hoisted locals of the function `t.<f>`.
fn hoisted_in(m: &Module, f: &str) -> Vec<String> {
    let def = m.fns.iter().find(|d| d.name == format!("t.{f}")).unwrap_or_else(|| panic!("no `{f}`"));
    def.hoisted.iter().map(|l| def.locals[l.0 as usize].name.clone()).collect()
}

/// A view out of an arm of what the arm declares: a temporary, a binding with
/// nothing to drop, the heads of `let` and `for`, the base of an index, a
/// chain of views, an element read through a view local (the root `s` and
/// what it views, `m`), a Copy binding at a field of a generated literal, and
/// the copies of borrowed bindings (R-484).
#[test]
fn a_view_out_of_an_arm_hoists_what_the_arm_declares() {
    let src = format!(
        "{COMMON}\
rt fn temp(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  take(if c {{ mk(v).slice(0, 2) }} else {{ y.slice(0, 2) }})\n}}\n\
rt fn nodrop(c: Bool, y: [F32; 4]) -> F32 {{\n  take(if c {{\n    let t = [1.0, 2.0, 3.0, 4.0]\n    t.slice(0, 2)\n  }} else {{ y.slice(0, 2) }})\n}}\n\
rt fn let_head(c: Bool, y: [F32; 4]) -> F32 {{\n  let s = if c {{\n    let t = [1.0, 2.0, 3.0, 4.0]\n    t.slice(0, 2)\n  }} else {{ y.slice(0, 2) }}\n  s[1]\n}}\n\
rt fn for_head(c: Bool, y: [F32; 4]) -> F32 {{\n  var acc = 0.0\n  for w in if c {{\n    let t = [1.0, 2.0, 3.0, 4.0]\n    t.slice(0, 2)\n  }} else {{ y.slice(0, 2) }} {{\n    acc = acc + w\n  }}\n  acc\n}}\n\
rt fn index_base(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  (if c {{ mk(v).slice(0, 2) }} else {{ y.slice(0, 2) }})[1]\n}}\n\
rt fn chain(c: Bool, d: Bool, y: [F32; 4]) -> F32 {{\n  take(if c {{\n    let s = if d {{ [1.0, 2.0, 3.0, 4.0].slice(0, 2) }} else {{ y.slice(0, 2) }}\n    s\n  }} else {{ y.slice(2, 4) }})\n}}\n\
rt fn view_local(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  take_in(if c {{\n    let m = [mk(v), mk(v)]\n    let s = m.slice(0, 1)\n    pair.In {{ l: s[0], r: y }}\n  }} else {{ pair.In {{ l: y, r: y }} }})\n}}\n\
rt fn gen_copy(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  take_in(if c {{\n    var t: [F32; 4] = [v; 4]\n    t[1] = 2.0\n    pair.In {{ l: t, r: y }}\n  }} else {{ pair.In {{ l: y, r: y }} }})\n}}\n\
rt fn match_arm[T](o: Option[G[T]], y: [F32; 4]) -> F32 {{\n  take(match o {{ Some(h) => h.xs.slice(0, 2), None => y.slice(0, 2) }})\n}}\n\
rt fn let_copy[T](c: Bool, g: G[T], y: [F32; 4]) -> F32 {{\n  take(if c {{\n    let h2 = g\n    h2.xs.slice(0, 2)\n  }} else {{ y.slice(0, 2) }})\n}}\n\
rt fn run(v: F32, c: Bool, y: [F32; 4]) -> F32 {{\n  match_arm(if c {{ Some(G {{ xs: mk(v), t: v }}) }} else {{ None }}, y) + let_copy(c, G {{ xs: mk(v), t: v }}, y)\n}}\n"
    );
    let m = core(&src);
    for (f, want) in [
        ("temp", &["__arr"][..]),
        ("nodrop", &["t"]),
        ("let_head", &["t"]),
        ("for_head", &["t"]),
        ("index_base", &["__arr"]),
        ("chain", &["__arr"]),
        ("view_local", &["m", "s"]),
        ("gen_copy", &["t"]),
        ("match_arm__F32", &["h"]),
        ("let_copy__F32", &["h2"]),
    ] {
        assert_eq!(hoisted_in(&m, f), want, "{f}\n{}", crate::dump(&m));
    }
}

/// What does not leave a scope stays where it is: a view used up in its arm,
/// a view of an outer local, a local of the function's level, the tail of a
/// bare block (a block expression closes no scope), a local of a loop body
/// passed to a call, the NRVO local, and a loop the fold drops with its `let`s.
#[test]
fn what_no_view_takes_out_of_its_scope_stays() {
    let src = format!(
        "{COMMON}\
rt fn used_in_arm(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  if c {{\n    let a = mk(v)\n    take(a.slice(0, 2))\n  }} else {{\n    take(y.slice(0, 2))\n  }}\n}}\n\
rt fn outer_local(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  let t = mk(v)\n  take(if c {{ t.slice(0, 2) }} else {{ y.slice(0, 2) }})\n}}\n\
rt fn top_level(v: F32) -> F32 {{\n  let t = mk(v)\n  take(t.slice(0, 2))\n}}\n\
rt fn bare_block(v: F32) -> F32 {{\n  take({{\n    let t = [1.0, 2.0, 3.0, 4.0]\n    t.slice(1, 3)\n  }}) + v\n}}\n\
rt fn loop_body(v: F32) -> F32 {{\n  var acc = 0.0\n  for i in 0 ..< 4 {{\n    let a = mk(v + F32.round_from(i))\n    acc = acc + take(a.slice(0, 2))\n  }}\n  acc\n}}\n\
rt fn nrvo(c: Bool, v: F32, y: [F32; 4]) -> [F32; 4] {{\n  var r = mk(v)\n  r[0] = take(if c {{ mk(v).slice(0, 2) }} else {{ y.slice(0, 2) }})\n  r\n}}\n\
const Z: U32 = 0\n\
rt fn dropped_loop(c: Bool, v: F32, y: [F32; 4]) -> F32 {{\n  var acc = 0.0\n  for _ in 0 ..< Z {{\n    acc = acc + take(if c {{ mk(v).slice(0, 2) }} else {{ y.slice(0, 2) }})\n  }}\n  acc\n}}\n"
    );
    let m = core(&src);
    for f in ["used_in_arm", "outer_local", "top_level", "bare_block", "loop_body", "dropped_loop"] {
        assert!(hoisted_in(&m, f).is_empty(), "{f}\n{}", crate::dump(&m));
    }
    assert_eq!(hoisted_in(&m, "nrvo"), ["__arr"], "only the temporary of the arm\n{}", crate::dump(&m));
}

/// S-1116: tails of other kinds at a view, each converted on its own: a planar value that is no
/// place (a call, a `const`, a repetition) is bound to a temporary `__planar` first, which an arm
/// declares and the views leave, so hoisted; written at the argument itself, it is not.
#[test]
fn a_planar_temporary_of_an_arm_is_hoisted() {
    let src = format!(
        "{COMMON}\
rt fn two(xs: [Span[F32]; 2]) -> F32 {{\n  xs[0][0] + xs[1][0]\n}}\nconst PS: [[F32; 4]; 2] = [[1.0; 4]; 2]\n\
rt fn arms(k: U32, v: F32, x: [F32; 4], y: [F32; 8], ps: [[F32; 4]; 2]) -> F32 {{\n  two(if k == 0 {{ [mk(v), y.slice(0, 2)] }} \
else if k == 1 {{ ps }} else if k == 2 {{ PS }} else if k == 3 {{ [x; 2] }} else {{ [mk(v), mk(v)] }})\n}}\n\
rt fn direct(v: F32) -> F32 {{\n  two([mk(v), mk(v)]) + two(PS)\n}}\n\
rt fn span_arms(c: Bool, v: F32, x: [F32; 4], y: [F32; 8]) -> F32 {{\n  take(if c {{ mk(v) }} else if !c {{ x }} else {{ y.slice(1, 3) }})\n}}\n"
    );
    let m = core(&src);
    let d = crate::dump(&m);
    assert_eq!(hoisted_in(&m, "arms"), ["__arr", "__planar", "__planar", "__arr", "__arr"], "{d}");
    assert!(hoisted_in(&m, "direct").is_empty(), "{d}");
    assert_eq!(hoisted_in(&m, "span_arms"), ["__arr"], "{d}");
}

// ---------------------------------------------------------------- Core by hand

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn x(ty: CTy, kind: ExprKind) -> Expr {
    Expr::new(ty, sp(), kind)
}

fn f32t() -> CTy {
    Types::float(FloatKind::F32)
}

/// The types of these modules, in one table each of them starts from:
/// `[F32; 4]`, `Span[F32]`, `[Span[F32]; 2]`, `E`.
fn tys() -> (Types, [CTy; 4]) {
    let mut t = Types::default();
    let arr = t.intern(TyKind::Array(f32t(), 4));
    let span = t.intern(TyKind::Span(f32t()));
    let planar = t.intern(TyKind::Array(span, 2));
    let e = t.intern(TyKind::Enum(TypeId(0)));
    (t, [arr, span, planar, e])
}

fn arr() -> CTy {
    tys().1[0]
}

fn span_ty() -> CTy {
    tys().1[1]
}

fn local(l: u32, ty: CTy) -> Expr {
    x(ty, ExprKind::Local(LocalId(l)))
}

fn span_of(l: u32) -> Expr {
    x(span_ty(), ExprKind::SpanOf(Box::new(local(l, arr()))))
}

fn st(kind: StmtKind) -> Stmt {
    Stmt { span: sp(), kind }
}

fn ones() -> Expr {
    x(arr(), ExprKind::Repeat { elem: Box::new(x(f32t(), ExprKind::Lit(Lit::F32(1.0)))), n: 4 })
}

fn block(stmts: Vec<Stmt>, value: Option<Expr>) -> Block {
    Block { stmts, value: value.map(Box::new) }
}

/// `fn f(c: Bool, y: [F32; 4], o: E)` with the extra `locals` (from 3 on)
/// and `body`; `E` is `enum E { A, B([F32; 4]) }`.
fn module(locals: &[(&str, CTy)], body: Block) -> Module {
    let e = TypeDef {
        name: "E".into(),
        kind: TypeDefKind::Enum { variants: vec![("A".into(), Vec::new()), ("B".into(), vec![arr()])] },
    };
    let params = [("c", Types::BOOL), ("y", arr()), ("o", tys().1[3])];
    let all: Vec<Local> = params.iter().chain(locals).map(|&(n, ty)| Local::value(n, ty)).collect();
    let f = FnDef {
        name: "f".into(),
        params: (0..3).map(|i| Param { local: LocalId(i), mode: Mode::Borrow, ty: all[i as usize].ty }).collect(),
        ret: Types::UNIT,
        sret: false,
        rt: true,
        locals: all,
        body: Some(body),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    };
    Module { tys: tys().0, types: vec![e], fns: vec![f], ..Module::default() }
}

/// The hoisted names of the module's function, which then verifies.
fn hoisted_by_hand(mut m: Module) -> Vec<String> {
    m.fill_all_facts();
    m.fns[0].hoisted = super::hoisted(&m, &m.fns[0]);
    verify(&m).unwrap_or_else(|e| panic!("{e}\n{}", crate::dump(&m)));
    m.fns[0].hoisted.iter().map(|l| m.fns[0].locals[l.0 as usize].name.clone()).collect()
}

/// The forms only U2c2b lowers from a source: the tail `span(t)` of a Copy
/// binding of an arm, of a Copy binding of a `match` arm, the elements of a
/// planar literal at the tail; and a view assigned to an outer place.
#[test]
fn the_forms_of_the_tails_by_hand_hoist_the_binding() {
    let use_ = |e: Expr| st(StmtKind::Let(LocalId(4), e));
    // let s = if c { let t = [1.0; 4]; span(t) } else { span(y) }
    let arm_copy = x(
        span_ty(),
        ExprKind::IfExpr {
            cond: Box::new(local(0, Types::BOOL)),
            then: block(vec![st(StmtKind::Let(LocalId(3), ones()))], Some(span_of(3))),
            else_: block(Vec::new(), Some(span_of(1))),
        },
    );
    let m = module(&[("t", arr()), ("s", span_ty())], block(vec![use_(arm_copy)], None));
    assert_eq!(hoisted_by_hand(m), ["t"]);
    // let s = match o { B(h) => span(h), _ => span(y) }
    let payload = x(arr(), ExprKind::Payload { base: Box::new(local(2, tys().1[3])), tag: 1, index: 0 });
    let switch = x(
        span_ty(),
        ExprKind::Switch {
            scrutinee: Box::new(local(2, tys().1[3])),
            arms: vec![(1, block(vec![st(StmtKind::Let(LocalId(3), payload))], Some(span_of(3))))],
            default: Some(block(Vec::new(), Some(span_of(1)))),
        },
    );
    let m = module(&[("h", arr()), ("s", span_ty())], block(vec![use_(switch)], None));
    assert_eq!(hoisted_by_hand(m), ["h"]);
    // let p = if c { let t = [1.0; 4]; [span(t), span(y)] } else { [span(y), span(y)] }
    let planar = tys().1[2];
    let tail = x(
        planar,
        ExprKind::IfExpr {
            cond: Box::new(local(0, Types::BOOL)),
            then: block(
                vec![st(StmtKind::Let(LocalId(3), ones()))],
                Some(x(planar, ExprKind::Array(vec![span_of(3), span_of(1)]))),
            ),
            else_: block(Vec::new(), Some(x(planar, ExprKind::Array(vec![span_of(1), span_of(1)])))),
        },
    );
    let m = module(&[("t", arr()), ("p", planar)], block(vec![use_(tail)], None));
    assert_eq!(hoisted_by_hand(m), ["t"]);
    // let p = [span(y), span(y)]; if c { let t = [1.0; 4]; p[0] = span(t) }
    let first = Place::Index(
        Box::new(Place::Local(LocalId(4))),
        Box::new(x(Types::U32, ExprKind::Lit(Lit::Int(0)))),
        sp(),
        Bounds::Checked,
    );
    let body = block(
        vec![
            use_(x(planar, ExprKind::Array(vec![span_of(1), span_of(1)]))),
            st(StmtKind::If(
                local(0, Types::BOOL),
                block(vec![st(StmtKind::Let(LocalId(3), ones())), st(StmtKind::Assign(first, span_of(3)))], None),
                Block::default(),
            )),
        ],
        None,
    );
    assert_eq!(hoisted_by_hand(module(&[("t", arr()), ("p", planar)], body)), ["t"]);
}

/// A view assigned to a place of the scope of its target holds no local of a
/// deeper scope: `if c { let p2 = [span(y), span(y)]; let t = [1.0; 4];
/// p2[0] = span(t) }` hoists nothing (`t` and `p2` are of one scope).
#[test]
fn a_view_assigned_at_the_level_of_its_target_hoists_nothing() {
    let planar = tys().1[2];
    let first = Place::Index(
        Box::new(Place::Local(LocalId(4))),
        Box::new(x(Types::U32, ExprKind::Lit(Lit::Int(0)))),
        sp(),
        Bounds::Checked,
    );
    let arm = vec![
        st(StmtKind::Let(LocalId(4), x(planar, ExprKind::Array(vec![span_of(1), span_of(1)])))),
        st(StmtKind::Let(LocalId(3), ones())),
        st(StmtKind::Assign(first, span_of(3))),
    ];
    let body = block(vec![st(StmtKind::If(local(0, Types::BOOL), block(arm, None), Block::default()))], None);
    assert!(hoisted_by_hand(module(&[("t", arr()), ("p2", planar)], body)).is_empty());
}

/// The verifier holds `hoisted` to locals with a `let` below the top of the
/// body: not a parameter, not a local of the top (the NRVO local is one).
#[test]
fn the_verifier_rejects_a_hoisted_local_without_a_let_in_a_scope() {
    let top = block(vec![st(StmtKind::Let(LocalId(3), ones()))], None);
    for (h, body) in [(0, Block::default()), (3, top)] {
        let mut m = module(&[("t", arr())], body);
        m.fns[0].hoisted = vec![LocalId(h)];
        m.fill_all_facts();
        let err = verify(&m).unwrap_err();
        assert!(err.message.contains("has no `let` below the top of the body"), "{err}");
        assert_eq!(err.rule, crate::Rule::V18, "{err}");
    }
}

/// A view of an alias out of an arm hoists the root of the place the alias
/// names (`let s = if c { let t = [1.0; 4]; alias r = t; span(r) } else { span(y) }`
/// hoists `t`, not the alias).
#[test]
fn a_view_of_an_alias_hoists_the_root_of_its_place() {
    let arm = x(
        span_ty(),
        ExprKind::IfExpr {
            cond: Box::new(local(0, Types::BOOL)),
            then: block(
                vec![st(StmtKind::Let(LocalId(3), ones())), st(StmtKind::Alias(LocalId(5), Place::Local(LocalId(3))))],
                Some(span_of(5)),
            ),
            else_: block(Vec::new(), Some(span_of(1))),
        },
    );
    let locals = [("t", arr()), ("s", span_ty()), ("r", arr())];
    let mut m = module(&locals, block(vec![st(StmtKind::Let(LocalId(4), arm))], None));
    m.fns[0].locals[5].kind = LocalKind::Alias { write: false };
    assert_eq!(hoisted_by_hand(m), ["t"]);
}
