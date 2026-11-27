//! The primitives (`onsa_sema::prim`): the table is sema's, so that the
//! analysis resolves a `std` `target` declaration to its row (S-69 (2)); the
//! backends read it here, as they depend on `onsa_core` alone. The types of
//! the operands and the value of each, in Core's types, are here ([`sig`],
//! V-02).

pub use onsa_sema::prim::*;

use crate::ir::{FloatKind, IntKind, Mode, TyKind};

/// The form of the type of an operand or of the value of a primitive (V-02).
/// `E` is the element: the first form of it met, the operands in order and
/// then the value, gives it, and every other is of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Int(IntKind),
    Float(FloatKind),
    Bool,
    Unit,
    /// `(Bool, Int(k))`: whether the value is defined, and the value.
    Parts(IntKind),
    /// An array, a `Span` or a `Buf` of `E` (the operand of `Len`).
    Seq,
    /// `Span[E]`; `SpanOfNum` when `E` is a number (`add_from`, `T: AnyNum`).
    SpanOf,
    SpanOfNum,
    /// `Buf[E]`.
    BufOf,
    /// `E`.
    Elem,
    /// A type the table does not read: a `Gen[T]` or a `fn` of `std.test`,
    /// and a `Str` or `Bytes`, which Core has not (W8).
    Any,
}

/// The operands of a primitive, in order, with their modes, and its value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sig {
    pub args: Vec<(Mode, Shape)>,
    pub ret: Shape,
}

/// The operands and the value of `prim`, a copy of its `std` declaration
/// (the unit tests check the number and the modes against it), without a
/// `_`, so that a new primitive must say.
pub fn sig(prim: &Prim) -> Sig {
    use Shape::*;
    let b = |s: Shape| (Mode::Borrow, s);
    let (args, ret) = match *prim {
        Prim::Math(f, k) => (vec![b(Float(k)); f.arity()], Float(k)),
        Prim::IntAbs(k) => (vec![b(Int(k))], Int(k)),
        Prim::IntMin(k) | Prim::IntMax(k) | Prim::DivEuclid(k) | Prim::RemEuclid(k) => (vec![b(Int(k)); 2], Int(k)),
        Prim::NarrowParts { from, to } => (vec![b(Int(from))], Parts(to)),
        Prim::IntToFloat { from, to } => (vec![b(Int(from))], Float(to)),
        Prim::FloatToFloat { from, to } => (vec![b(Float(from))], Float(to)),
        Prim::TruncToInt { from, to, .. } => (vec![b(Float(from))], Int(to)),
        Prim::ToBits(k) => (vec![b(Float(k))], Int(bits(k))),
        Prim::FromBits(k) => (vec![b(Int(bits(k)))], Float(k)),
        Prim::Parts(_, k) => (vec![b(Int(k)); 2], Parts(k)),
        Prim::IsNan(k) | Prim::IsFinite(k) => (vec![b(Float(k))], Bool),
        Prim::Len => (vec![b(Seq)], Int(IntKind::U32)),
        Prim::Slice => (vec![b(SpanOf), b(Int(IntKind::U32)), b(Int(IntKind::U32))], SpanOf),
        Prim::Fill => (vec![(Mode::Inout, SpanOf), b(Elem)], Unit),
        Prim::AddFrom => (vec![(Mode::Inout, SpanOfNum), b(SpanOf)], Unit),
        Prim::CopyFrom => (vec![(Mode::Inout, SpanOf), b(SpanOf)], Unit),
        Prim::BufZeroed => (vec![b(Int(IntKind::U32))], BufOf),
        Prim::StrLen => (vec![b(Any)], Int(IntKind::U32)),
        Prim::AssertNear => (vec![b(Float(FloatKind::F64)); 3], Unit),
        Prim::Pending(p) => match p {
            PendingPrim::Check => (vec![b(Int(IntKind::U32)), b(Any), b(Any)], Unit),
            PendingPrim::GenF32 => (vec![b(Float(FloatKind::F32)); 2], Any),
            PendingPrim::GenU32 => (vec![b(Int(IntKind::U32)); 2], Any),
            PendingPrim::GenPair => (vec![b(Any); 2], Any),
            PendingPrim::BytesDefault => (Vec::new(), Any),
        },
    };
    Sig { args, ret }
}

/// The integer of the bits of a float (`to_bits`, `from_bits`, §3.3).
fn bits(k: FloatKind) -> IntKind {
    match k {
        FloatKind::F32 => IntKind::U32,
        FloatKind::F64 => IntKind::U64,
    }
}

/// A type of Core as a type argument of a row reads it (as
/// [`Scalar::head`] reads sema's): by its head.
pub fn scalar(k: &TyKind) -> Scalar {
    match k {
        TyKind::Int(k) => Scalar::Int(*k),
        TyKind::Float(k) => Scalar::Float(*k),
        _ => Scalar::Other,
    }
}
