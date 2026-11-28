//! What evaluating a node of Core does besides giving its value (D-03: the
//! classification of the operations is in this one place, W8-03): the
//! lowering asks whether an expression may be evaluated twice
//! ([`repeatable`]), and the interpreter stops with an internal error when a
//! node it classifies [`Own::Pure`] panics.

use crate::ir::{Arg, BinOp, Bounds, Expr, ExprKind, Lit, Mode, Overflow, TyKind, Types, UnOp};
use crate::prim::PrimEffect;
use crate::walk::{Child, expr_children};

/// What a node does itself, its children not counted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Own {
    /// Nothing but its value.
    Pure,
    /// It may panic, and has no other effect.
    Panics,
    /// An effect: a call, a primitive that writes or allocates, a panic; and
    /// the forms of statements (`Block`, `IfExpr`, `Switch`), which only a
    /// statement position holds once the tree is normal.
    Effect,
    /// It writes a place: a call or a primitive with an `inout` argument.
    Writes,
}

/// What `e` does itself (`tys`: the types of its module). Without a `_`, so
/// that a new form must say.
pub fn own(e: &Expr, tys: &Types) -> Own {
    match &e.kind {
        // Of a `Const`, the panics of its initializer are not counted: the
        // value of a constant is decided before lowering (the interpreter
        // that evaluates one at its first read is W9-03's).
        ExprKind::Lit(_)
        | ExprKind::Local(_)
        | ExprKind::Const(_)
        | ExprKind::Zeroed
        | ExprKind::Cast(_)
        | ExprKind::Field { .. }
        | ExprKind::Tag(_)
        | ExprKind::Payload { .. }
        | ExprKind::SpanOf(_)
        | ExprKind::Struct { .. }
        | ExprKind::Variant { .. }
        | ExprKind::Array(_)
        | ExprKind::Repeat { .. }
        | ExprKind::Tuple(_)
        | ExprKind::Logic { .. }
        | ExprKind::Cmp { .. } => Own::Pure,
        // `-MIN`; of a float, IEEE.
        ExprKind::Unary(UnOp::Neg, _) if tys.is_int(e.ty) => Own::Panics,
        ExprKind::Unary(..) => Own::Pure,
        ExprKind::Binary { op, overflow, lhs, rhs } => match tys.kind(lhs.ty) {
            TyKind::Int(k) => binary(*op, *overflow, (k.bits(), k.signed()), rhs),
            _ => Own::Pure,
        },
        ExprKind::Index { bounds, .. } => match bounds {
            Bounds::Checked => Own::Panics,
            Bounds::Known => Own::Pure,
        },
        ExprKind::Call { args, .. } => writes_or(args, Own::Effect),
        ExprKind::Prim { prim, args } => writes_or(
            args,
            match prim.effect() {
                PrimEffect::Pure => Own::Pure,
                PrimEffect::Panics => Own::Panics,
                PrimEffect::Effect => Own::Effect,
            },
        ),
        ExprKind::Panic { .. } | ExprKind::Block(_) | ExprKind::IfExpr { .. } | ExprKind::Switch { .. } => Own::Effect,
    }
}

/// An integer operator `op` on operands of `bits` bits, signed or not, of
/// the right operand `rhs` (§3.4): a `/` or `%` by a literal other than 0
/// (a `/` of a signed type, other than -1 too) and a shift by a literal
/// below the width cannot panic.
fn binary(op: BinOp, overflow: Overflow, (bits, signed): (u32, bool), rhs: &Expr) -> Own {
    let lit = match rhs.kind {
        ExprKind::Lit(Lit::Int(n)) => Some(n),
        _ => None,
    };
    let safe = match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => overflow != Overflow::Checked,
        // `MIN / -1` does not fit; `MIN % -1` is 0 (§3.4).
        BinOp::Div => lit.is_some_and(|n| n != 0 && !(signed && n == -1)),
        BinOp::Rem => lit.is_some_and(|n| n != 0),
        BinOp::Shl | BinOp::Shr => lit.is_some_and(|n| (0..i128::from(bits)).contains(&n)),
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => true,
    };
    if safe { Own::Pure } else { Own::Panics }
}

/// [`Own::Writes`] when an argument is `inout`, else `other`.
fn writes_or(args: &[Arg], other: Own) -> Own {
    if args.iter().any(|a| a.mode == Mode::Inout) { Own::Writes } else { other }
}

/// Whether evaluating `e` a second time gives the same value or the same
/// panic, in the same order (what the lowering may evaluate again, V-23): no
/// node of it has an effect, writes or is a form of statements.
pub fn repeatable(e: &Expr, tys: &Types) -> bool {
    every(e, tys, |o| matches!(o, Own::Pure | Own::Panics))
}

/// Whether evaluating `e` gives its value and does nothing else: no node of
/// it may panic, has an effect or writes.
pub fn pure(e: &Expr, tys: &Types) -> bool {
    every(e, tys, |o| o == Own::Pure)
}

/// Whether what every node of `e` does itself is `ok`.
fn every(e: &Expr, tys: &Types, ok_own: fn(Own) -> bool) -> bool {
    let mut ok = ok_own(own(e, tys));
    expr_children(e, &mut |c| {
        ok = ok
            && match c {
                Child::Expr(x, ..) => every(x, tys, ok_own),
                // Not a guard: a block is a child of the forms of statements
                // only, which are `Effect` already, and an expression has no place.
                Child::Block(..) | Child::Place(..) => false,
            }
    });
    ok
}
