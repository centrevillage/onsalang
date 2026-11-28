//! The table of `effects::own` row by row (W8-03): what a node does itself,
//! its children not counted, and `repeatable` of a tree.

use onsa_diag::{FileId, Span};

use crate::effects::{Own, own, repeatable};
use crate::ir::*;
use crate::prim::{CheckedOp, MathFn, PendingPrim, Prim};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn lit(ty: CTy, n: i128) -> Expr {
    Expr::new(ty, sp(), ExprKind::Lit(Lit::Int(n)))
}

fn local(ty: CTy) -> Expr {
    Expr::new(ty, sp(), ExprKind::Local(LocalId(0)))
}

fn bin(op: BinOp, overflow: Overflow, lhs: Expr, rhs: Expr) -> Expr {
    Expr::new(lhs.ty, sp(), ExprKind::Binary { op, overflow, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

#[test]
fn each_row_of_the_table_of_own() {
    use Own::{Effect, Panics, Pure, Writes};
    let tys = Types::default();
    let (i32_, u8_, f32_) = (Types::int(IntKind::I32), Types::int(IntKind::U8), Types::float(FloatKind::F32));
    let of = |kind| own(&Expr::new(Types::U32, sp(), kind), &tys);
    // Integer operators, by the right operand (§3.4).
    let x = || local(i32_);
    let rows = [
        (bin(BinOp::Add, Overflow::Checked, x(), x()), Panics),
        (bin(BinOp::Mul, Overflow::Wrap, x(), x()), Pure),
        (bin(BinOp::Sub, Overflow::Sat, x(), x()), Pure),
        (bin(BinOp::Div, Overflow::Checked, x(), x()), Panics),
        (bin(BinOp::Div, Overflow::Checked, x(), lit(i32_, 0)), Panics),
        (bin(BinOp::Div, Overflow::Checked, x(), lit(i32_, -1)), Panics),
        (bin(BinOp::Div, Overflow::Checked, x(), lit(i32_, 3)), Pure),
        (bin(BinOp::Div, Overflow::Checked, local(u8_), lit(u8_, 255)), Pure),
        (bin(BinOp::Rem, Overflow::Checked, x(), lit(i32_, 0)), Panics),
        // `MIN % -1` is 0 (§3.4).
        (bin(BinOp::Rem, Overflow::Checked, x(), lit(i32_, -1)), Pure),
        (bin(BinOp::Shl, Overflow::Checked, x(), local(Types::U32)), Panics),
        (bin(BinOp::Shl, Overflow::Checked, x(), lit(Types::U32, 31)), Pure),
        (bin(BinOp::Shr, Overflow::Checked, x(), lit(Types::U32, 32)), Panics),
        (bin(BinOp::Shr, Overflow::Checked, local(u8_), lit(Types::U32, 7)), Pure),
        (bin(BinOp::Shl, Overflow::Checked, local(u8_), lit(Types::U32, 8)), Panics),
        (bin(BinOp::BitXor, Overflow::Checked, x(), x()), Pure),
        (bin(BinOp::Div, Overflow::Checked, local(f32_), local(f32_)), Pure),
        (Expr::new(i32_, sp(), ExprKind::Unary(UnOp::Neg, Box::new(x()))), Panics),
        (Expr::new(f32_, sp(), ExprKind::Unary(UnOp::Neg, Box::new(local(f32_)))), Pure),
        (Expr::new(i32_, sp(), ExprKind::Unary(UnOp::Not, Box::new(x()))), Pure),
    ];
    for (e, want) in &rows {
        assert_eq!(own(e, &tys), *want, "{e:?}");
    }
    let index = |bounds| ExprKind::Index { base: Box::new(local(Types::U32)), index: Box::new(x()), bounds };
    assert_eq!(of(index(Bounds::Checked)), Panics);
    assert_eq!(of(index(Bounds::Known)), Pure);
    let arg = |mode| Arg { mode, expr: local(Types::U32) };
    assert_eq!(of(ExprKind::Call { fn_: FnId(0), args: vec![arg(Mode::Borrow), arg(Mode::Move)] }), Effect);
    assert_eq!(of(ExprKind::Call { fn_: FnId(0), args: vec![arg(Mode::Borrow), arg(Mode::Inout)] }), Writes);
    let prim = |prim: Prim, mode| ExprKind::Prim { prim, args: vec![arg(mode)] };
    assert_eq!(of(prim(Prim::IntMin(IntKind::I32), Mode::Inout)), Writes);
    // Each row of `Prim::effect`.
    let (fk, ik) = (FloatKind::F32, IntKind::I32);
    let prims = [
        (Prim::Math(MathFn::Sqrt, fk), Pure),
        (Prim::IntAbs(ik), Panics),
        (Prim::IntMin(ik), Pure),
        (Prim::IntMax(ik), Pure),
        (Prim::NarrowParts { from: ik, to: IntKind::U8 }, Pure),
        (Prim::IntToFloat { from: ik, to: fk }, Pure),
        (Prim::FloatToFloat { from: fk, to: FloatKind::F64 }, Pure),
        (Prim::TruncToInt { from: fk, to: ik, sat: true }, Pure),
        (Prim::TruncToInt { from: fk, to: ik, sat: false }, Panics),
        (Prim::ToBits(fk), Pure),
        (Prim::FromBits(fk), Pure),
        (Prim::Parts(CheckedOp::Div, ik), Pure),
        (Prim::DivEuclid(ik), Panics),
        (Prim::RemEuclid(ik), Panics),
        (Prim::IsNan(fk), Pure),
        (Prim::IsFinite(fk), Pure),
        (Prim::Len, Pure),
        (Prim::Slice, Panics),
        (Prim::StrLen, Pure),
        (Prim::Fill, Effect),
        (Prim::AddFrom, Effect),
        (Prim::CopyFrom, Effect),
        (Prim::BufZeroed, Effect),
        (Prim::AssertNear, Effect),
        (Prim::Pending(PendingPrim::GenU32), Effect),
    ];
    for (p, want) in prims {
        assert_eq!(of(prim(p.clone(), Mode::Borrow)), want, "{p:?}");
    }
    let panic = ExprKind::Panic { msg: MsgId(0), origin: PanicOrigin::Panic, shown: Vec::new() };
    assert_eq!(of(panic), Effect);
    assert_eq!(of(ExprKind::Block(Block::default())), Effect);
    assert_eq!(of(ExprKind::Cast(Box::new(local(u8_)))), Pure);
    // A tree: a panic of an operand may be repeated, a call not.
    let div = bin(BinOp::Div, Overflow::Checked, x(), x());
    assert!(repeatable(&div, &tys));
    let call = Expr::new(i32_, sp(), ExprKind::Call { fn_: FnId(0), args: Vec::new() });
    assert!(!repeatable(&bin(BinOp::Add, Overflow::Wrap, x(), call), &tys));
}
