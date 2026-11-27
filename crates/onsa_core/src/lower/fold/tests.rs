//! The Core the fold writes (S-288), looked at directly: what folds, what is
//! kept as statements, and what never folds.

use onsa_diag::{FileId, Span};

use super::fold_module;
use crate::ir::*;
use crate::prim::Prim;

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn e(ty: CTy, kind: ExprKind) -> Expr {
    Expr::new(ty, sp(), kind)
}

fn local(i: u32, ty: CTy) -> Expr {
    e(ty, ExprKind::Local(LocalId(i)))
}

fn int(k: IntKind, v: i128) -> Expr {
    e(Types::int(k), ExprKind::Lit(Lit::Int(v)))
}

fn cmp(op: CmpOp, lhs: Expr, rhs: Expr) -> Expr {
    e(Types::BOOL, ExprKind::Cmp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

/// A module of one function `f(x0: T0, x1: T1, …) -> ret { stmts; value }`, folded.
fn folded(locals: &[CTy], consts: Vec<ConstDef>, stmts: Vec<Stmt>, value: Expr) -> FnDef {
    folded_in(Types::default(), locals, consts, stmts, value)
}

/// [`folded`] in a module of the types `tys`.
fn folded_in(tys: Types, locals: &[CTy], consts: Vec<ConstDef>, stmts: Vec<Stmt>, value: Expr) -> FnDef {
    let mut m = Module {
        tys,
        consts,
        fns: vec![FnDef {
            name: "m.f".into(),
            params: Vec::new(),
            ret: value.ty,
            sret: false,
            rt: true,
            locals: locals.iter().enumerate().map(|(i, &t)| Local { name: format!("x{i}"), ty: t }).collect(),
            body: Some(Block { stmts, value: Some(Box::new(value)) }),
            span: sp(),
            fp_relaxed: false,
            test: None,
            decl: None,
            hoisted: Vec::new(),
        }],
        ..Module::default()
    };
    fold_module(&mut m);
    m.fns.pop().expect("the function")
}

fn value(f: &FnDef) -> &Expr {
    f.body.as_ref().and_then(|b| b.value.as_deref()).expect("a value")
}

/// The constant a comparison folded to, and the statements kept before it.
fn folded_to(x: &Expr) -> Option<(bool, &[Stmt])> {
    match &x.kind {
        ExprKind::Lit(Lit::Bool(b)) => Some((*b, &[])),
        ExprKind::Block(b) => match b.value.as_deref().map(|v| &v.kind) {
            Some(ExprKind::Lit(Lit::Bool(v))) => Some((*v, &b.stmts)),
            _ => None,
        },
        _ => None,
    }
}

fn is_local_stmt(s: &Stmt, i: u32) -> bool {
    matches!(&s.kind, StmtKind::Expr(x) if matches!(x.kind, ExprKind::Local(LocalId(n)) if n == i))
}

#[test]
fn a_self_comparison_of_an_exact_type_folds_and_keeps_one_read() {
    for ty in [Types::int(IntKind::I32), Types::int(IntKind::U8), Types::BOOL, Types::CHAR] {
        for (op, want) in [
            (CmpOp::Eq, true),
            (CmpOp::Ne, false),
            (CmpOp::Le, true),
            (CmpOp::Lt, false),
            (CmpOp::Ge, true),
            (CmpOp::Gt, false),
        ] {
            let f = folded(std::slice::from_ref(&ty), Vec::new(), Vec::new(), cmp(op, local(0, ty), local(0, ty)));
            let (v, stmts) = folded_to(value(&f)).unwrap_or_else(|| panic!("{ty:?} {op:?}: {:?}", value(&f)));
            assert_eq!(v, want, "{ty:?} {op:?}");
            assert_eq!(stmts.len(), 1, "the operand is read once: {stmts:?}");
            assert!(is_local_stmt(&stmts[0], 0), "{stmts:?}");
        }
    }
}

#[test]
fn a_float_an_element_and_two_bindings_never_fold() {
    let f32t = Types::float(FloatKind::F32);
    let f = folded(std::slice::from_ref(&f32t), Vec::new(), Vec::new(), cmp(CmpOp::Eq, local(0, f32t), local(0, f32t)));
    assert!(matches!(value(&f).kind, ExprKind::Cmp { .. }), "a NaN changes it: {:?}", value(&f));
    let i32t = Types::int(IntKind::I32);
    let mut tys = Types::default();
    let arr = tys.intern(TyKind::Array(i32t, 3));
    let elem = || {
        e(
            i32t,
            ExprKind::Index {
                base: Box::new(local(0, arr)),
                index: Box::new(local(1, Types::U32)),
                bounds: Bounds::Checked,
            },
        )
    };
    let f = folded_in(tys, &[arr, Types::U32], Vec::new(), Vec::new(), cmp(CmpOp::Eq, elem(), elem()));
    assert!(matches!(value(&f).kind, ExprKind::Cmp { .. }), "the index is checked: {:?}", value(&f));
    let f = folded(&[i32t, i32t], Vec::new(), Vec::new(), cmp(CmpOp::Eq, local(0, i32t), local(1, i32t)));
    assert!(matches!(value(&f).kind, ExprKind::Cmp { .. }), "{:?}", value(&f));
}

#[test]
fn a_comparison_the_type_decides_folds_in_both_directions() {
    let u8t = Types::int(IntKind::U8);
    let i8t = Types::int(IntKind::I8);
    let cases = [
        (cmp(CmpOp::Ge, local(0, u8t), int(IntKind::U8, 0)), Some(true)),
        (cmp(CmpOp::Lt, local(0, u8t), int(IntKind::U8, 0)), Some(false)),
        (cmp(CmpOp::Le, int(IntKind::U8, 0), local(0, u8t)), Some(true)),
        (cmp(CmpOp::Gt, int(IntKind::U8, 0), local(0, u8t)), Some(false)),
        (cmp(CmpOp::Le, local(0, u8t), int(IntKind::U8, 255)), Some(true)),
        (cmp(CmpOp::Gt, local(0, u8t), int(IntKind::U8, 255)), Some(false)),
        (cmp(CmpOp::Lt, int(IntKind::U8, 255), local(0, u8t)), Some(false)),
        // at the edge but not decided
        (cmp(CmpOp::Lt, local(0, u8t), int(IntKind::U8, 255)), None),
        (cmp(CmpOp::Le, local(0, u8t), int(IntKind::U8, 0)), None),
        (cmp(CmpOp::Eq, local(0, u8t), int(IntKind::U8, 255)), None),
        (cmp(CmpOp::Ge, local(1, i8t), int(IntKind::I8, -128)), Some(true)),
        (cmp(CmpOp::Lt, local(1, i8t), int(IntKind::I8, 0)), None),
    ];
    for (c, want) in cases {
        let shown = format!("{c:?}");
        let f = folded(&[u8t, i8t], Vec::new(), Vec::new(), c);
        match want {
            Some(w) => {
                let (v, stmts) = folded_to(value(&f)).unwrap_or_else(|| panic!("{shown}: {:?}", value(&f)));
                assert_eq!(v, w, "{shown}");
                assert_eq!(stmts.len(), 1, "the operand stays, the literal does not: {stmts:?}");
            }
            None => assert!(matches!(value(&f).kind, ExprKind::Cmp { .. }), "{shown}: {:?}", value(&f)),
        }
    }
}

#[test]
fn the_smallest_char_and_a_widened_value_fold() {
    let ch = Types::CHAR;
    let f = folded(
        std::slice::from_ref(&ch),
        Vec::new(),
        Vec::new(),
        cmp(CmpOp::Ge, local(0, ch), e(ch, ExprKind::Lit(Lit::Char('\0')))),
    );
    assert_eq!(folded_to(value(&f)).map(|x| x.0), Some(true));
    // `(x as I32) < 256` and `(x as I32) == 300` of a `U8` (§3.3: `as` keeps the value).
    let u8t = Types::int(IntKind::U8);
    let i32t = Types::int(IntKind::I32);
    let wide = || e(i32t, ExprKind::Cast(Box::new(local(0, u8t))));
    for (c, want) in [
        (cmp(CmpOp::Lt, wide(), int(IntKind::I32, 256)), true),
        (cmp(CmpOp::Eq, wide(), int(IntKind::I32, 300)), false),
        (cmp(CmpOp::Ge, wide(), int(IntKind::I32, 0)), true),
        (cmp(CmpOp::Ne, wide(), int(IntKind::I32, -1)), true),
    ] {
        let shown = format!("{c:?}");
        let f = folded(std::slice::from_ref(&u8t), Vec::new(), Vec::new(), c);
        assert_eq!(folded_to(value(&f)).map(|x| x.0), Some(want), "{shown}");
    }
    let f = folded(std::slice::from_ref(&u8t), Vec::new(), Vec::new(), cmp(CmpOp::Lt, wide(), int(IntKind::I32, 255)));
    assert!(matches!(value(&f).kind, ExprKind::Cmp { .. }), "{:?}", value(&f));
}

#[test]
fn a_const_and_the_length_of_an_array_are_constants() {
    let u32t = Types::U32;
    let consts = vec![ConstDef { name: "m.N".into(), ty: u32t, init: int(IntKind::U32, 0) }];
    let c = cmp(CmpOp::Ge, local(0, u32t), e(u32t, ExprKind::Const(ConstId(0))));
    let f = folded(std::slice::from_ref(&u32t), consts, Vec::new(), c);
    let (v, stmts) = folded_to(value(&f)).expect("folded");
    assert!(v);
    assert_eq!(stmts.len(), 1, "a const is not kept: {stmts:?}");
    // `0..xs.len()` over `[U32; 0]` never runs: the loop goes, its bounds stay as statements.
    let mut tys = Types::default();
    let arr = tys.intern(TyKind::Array(u32t, 0));
    let len = e(u32t, ExprKind::Prim { prim: Prim::Len, args: vec![Arg { mode: Mode::Borrow, expr: local(0, arr) }] });
    let body = Block { stmts: Vec::new(), value: None };
    let stmts = vec![Stmt { span: sp(), kind: StmtKind::ForRange(LocalId(1), local(2, u32t), len, body) }];
    let f = folded_in(tys, &[arr, u32t, u32t], Vec::new(), stmts, int(IntKind::U32, 1));
    let kept = &f.body.as_ref().expect("a body").stmts;
    assert_eq!(kept.len(), 2, "{kept:?}");
    assert!(is_local_stmt(&kept[0], 2), "the lower bound first: {kept:?}");
    assert!(matches!(&kept[1].kind, StmtKind::Expr(x) if matches!(x.kind, ExprKind::Prim { prim: Prim::Len, .. })));
}

#[test]
fn a_loop_up_to_a_bound_above_the_smallest_value_stays() {
    for (k, hi) in [(IntKind::U32, 1), (IntKind::I16, -32767)] {
        let t = Types::int(k);
        let body = Block { stmts: Vec::new(), value: None };
        let stmts = vec![Stmt { span: sp(), kind: StmtKind::ForRange(LocalId(0), local(1, t), int(k, hi), body) }];
        let f = folded(&[t, t], Vec::new(), stmts, int(IntKind::U32, 1));
        let kept = &f.body.as_ref().expect("a body").stmts;
        assert!(matches!(kept[..], [Stmt { kind: StmtKind::ForRange(..), .. }]), "{k:?}: {kept:?}");
    }
    // At the smallest value of a signed type, it goes.
    let t = Types::int(IntKind::I16);
    let body = Block { stmts: Vec::new(), value: None };
    let stmts =
        vec![Stmt { span: sp(), kind: StmtKind::ForRange(LocalId(0), local(1, t), int(IntKind::I16, -32768), body) }];
    let f = folded(&[t, t], Vec::new(), stmts, int(IntKind::U32, 1));
    let kept = &f.body.as_ref().expect("a body").stmts;
    assert!(matches!(kept[..], [ref s] if is_local_stmt(s, 1)), "{kept:?}");
}

#[test]
fn an_operand_with_an_effect_is_kept_in_order() {
    let u8t = Types::int(IntKind::U8);
    let call = e(u8t, ExprKind::Call { fn_: FnId(0), args: Vec::new() });
    let f = folded(&[], Vec::new(), Vec::new(), cmp(CmpOp::Ge, call, int(IntKind::U8, 0)));
    let (v, stmts) = folded_to(value(&f)).expect("folded");
    assert!(v);
    assert!(
        matches!(stmts, [Stmt { kind: StmtKind::Expr(Expr { kind: ExprKind::Call { .. }, .. }), .. }]),
        "{stmts:?}"
    );
}

#[test]
fn an_assignment_of_a_binding_to_itself_becomes_a_read() {
    let i32t = Types::int(IntKind::I32);
    let mut tys = Types::default();
    let arr = tys.intern(TyKind::Array(i32t, 2));
    let idx = || local(2, Types::U32);
    let elem =
        e(i32t, ExprKind::Index { base: Box::new(local(1, arr)), index: Box::new(idx()), bounds: Bounds::Checked });
    let stmts = vec![
        Stmt { span: sp(), kind: StmtKind::Assign(Place::Local(LocalId(0)), local(0, i32t)) },
        Stmt {
            span: sp(),
            kind: StmtKind::Assign(
                Place::Index(Box::new(Place::Local(LocalId(1))), Box::new(idx()), sp(), Bounds::Checked),
                elem,
            ),
        },
    ];
    let f = folded_in(tys, &[i32t, arr, Types::U32], Vec::new(), stmts, int(IntKind::I32, 0));
    let kept = &f.body.as_ref().expect("a body").stmts;
    assert!(is_local_stmt(&kept[0], 0), "{:?}", kept[0]);
    assert!(matches!(kept[1].kind, StmtKind::Assign(..)), "an element keeps its check: {:?}", kept[1]);
}
