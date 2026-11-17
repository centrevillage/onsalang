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

// ---------------------------------------------------------------- Core by hand

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn x(ty: Ty, kind: ExprKind) -> Expr {
    Expr::new(ty, sp(), kind)
}

fn f32t() -> Ty {
    Ty::Float(FloatKind::F32)
}

fn arr() -> Ty {
    Ty::Array(Box::new(f32t()), 4)
}

fn span_ty() -> Ty {
    Ty::Span(Box::new(f32t()))
}

fn local(l: u32, ty: Ty) -> Expr {
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
fn module(locals: &[(&str, Ty)], body: Block) -> Module {
    let e = TypeDef {
        name: "E".into(),
        kind: TypeDefKind::Enum { variants: vec![("A".into(), Vec::new()), ("B".into(), vec![arr()])] },
    };
    let params = [("c", Ty::Bool), ("y", arr()), ("o", Ty::Enum(TypeId(0)))];
    let all: Vec<Local> =
        params.iter().chain(locals).map(|(n, t)| Local { name: n.to_string(), ty: t.clone() }).collect();
    let f = FnDef {
        name: "f".into(),
        params: (0..3)
            .map(|i| Param { local: LocalId(i), mode: Mode::Borrow, ty: all[i as usize].ty.clone() })
            .collect(),
        ret: Ty::Unit,
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
    Module { types: vec![e], fns: vec![f], ..Module::default() }
}

/// The hoisted names of the module's function, which then verifies.
fn hoisted_by_hand(mut m: Module) -> Vec<String> {
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
            cond: Box::new(local(0, Ty::Bool)),
            then: block(vec![st(StmtKind::Let(LocalId(3), ones()))], Some(span_of(3))),
            else_: block(Vec::new(), Some(span_of(1))),
        },
    );
    let m = module(&[("t", arr()), ("s", span_ty())], block(vec![use_(arm_copy)], None));
    assert_eq!(hoisted_by_hand(m), ["t"]);
    // let s = match o { B(h) => span(h), _ => span(y) }
    let payload = x(arr(), ExprKind::Payload { base: Box::new(local(2, Ty::Enum(TypeId(0)))), tag: 1, index: 0 });
    let switch = x(
        span_ty(),
        ExprKind::Switch {
            scrutinee: Box::new(local(2, Ty::Enum(TypeId(0)))),
            arms: vec![(1, block(vec![st(StmtKind::Let(LocalId(3), payload))], Some(span_of(3))))],
            default: Some(block(Vec::new(), Some(span_of(1)))),
        },
    );
    let m = module(&[("h", arr()), ("s", span_ty())], block(vec![use_(switch)], None));
    assert_eq!(hoisted_by_hand(m), ["h"]);
    // let p = if c { let t = [1.0; 4]; [span(t), span(y)] } else { [span(y), span(y)] }
    let planar = Ty::Array(Box::new(span_ty()), 2);
    let tail = x(
        planar.clone(),
        ExprKind::IfExpr {
            cond: Box::new(local(0, Ty::Bool)),
            then: block(
                vec![st(StmtKind::Let(LocalId(3), ones()))],
                Some(x(planar.clone(), ExprKind::Array(vec![span_of(3), span_of(1)]))),
            ),
            else_: block(Vec::new(), Some(x(planar.clone(), ExprKind::Array(vec![span_of(1), span_of(1)])))),
        },
    );
    let m = module(&[("t", arr()), ("p", planar.clone())], block(vec![use_(tail)], None));
    assert_eq!(hoisted_by_hand(m), ["t"]);
    // let p = [span(y), span(y)]; if c { let t = [1.0; 4]; p[0] = span(t) }
    let first =
        Place::Index(Box::new(Place::Local(LocalId(4))), Box::new(x(Ty::u32(), ExprKind::Lit(Lit::Int(0)))), sp());
    let body = block(
        vec![
            use_(x(planar.clone(), ExprKind::Array(vec![span_of(1), span_of(1)]))),
            st(StmtKind::If(
                local(0, Ty::Bool),
                block(vec![st(StmtKind::Let(LocalId(3), ones())), st(StmtKind::Assign(first, span_of(3)))], None),
                Block::default(),
            )),
        ],
        None,
    );
    assert_eq!(hoisted_by_hand(module(&[("t", arr()), ("p", planar)], body)), ["t"]);
}

/// The verifier holds `hoisted` to locals with a `let` below the top of the
/// body: not a parameter, not a local of the top (the NRVO local is one).
#[test]
fn the_verifier_rejects_a_hoisted_local_without_a_let_in_a_scope() {
    let top = block(vec![st(StmtKind::Let(LocalId(3), ones()))], None);
    for (h, body) in [(0, Block::default()), (3, top)] {
        let mut m = module(&[("t", arr())], body);
        m.fns[0].hoisted = vec![LocalId(h)];
        let err = verify(&m).unwrap_err();
        assert!(err.message.contains("has no `let` below the top of the body"), "{err}");
    }
}
