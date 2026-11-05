//! The provisional tables of the traits (§6.3, S-72, R-127): what the builtin
//! types implement, what a trait requires, and the trait of each operator.
//! In phase 2 they become the declarations of std: a row of [`IMPLS`] its
//! `impl`s, a row of [`SUPERS`] the heading of a `trait`; the table of the
//! operators stays. The judgments under the generics in scope are
//! [`crate::body::bounds`], which reads these.

use onsa_syntax::ast::BinOp;

use crate::def::Bound;
use crate::deferred::OpNeed;
use crate::ty::{BuiltinTy, Ty};

/// A row of the table of §6.3: the types that implement the same traits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Class {
    Signed,
    Unsigned,
    Float,
    Bool,
    Char,
    Str,
    Bytes,
    Unit,
    /// A tuple and `[T; N]`, when all their elements implement the trait.
    Parts,
    /// `Option[T]` and `Result[T, E]`: named types, which meet a trait by the
    /// derives of their declarations (§4.1), held equal to this row by a unit
    /// test.
    Derived,
    /// `Array[T]`, when its element implements the trait.
    Array,
    /// `Map`, `Set`, `Buf`, `Span` and the function values, with `Ptr`
    /// (§14), which §6.3 does not list.
    Bare,
}

/// The table of §6.3, row by row: a pair of a class and a trait is one `impl`
/// (R-127). It is closed, as §6.3 says; `Copy` and `Dup` are not in it, being
/// decided by the kind (§4.6).
#[rustfmt::skip]
pub(crate) const IMPLS: &[(Class, &[Bound])] = {
    use Bound::*;
    &[
        (Class::Signed, &[
            PartialEq, Eq, PartialOrd, Ord, Hash, Show, Default, AnyNum, Num, Int,
            Add, Sub, Mul, Div, Rem, Neg, BitAnd, BitOr, BitXor, Shl, Shr, Not,
            WrappingAdd, WrappingSub, WrappingMul, SaturatingAdd, SaturatingSub, SaturatingMul,
        ]),
        (Class::Unsigned, &[
            PartialEq, Eq, PartialOrd, Ord, Hash, Show, Default, AnyNum, Int, Unsigned,
            Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr, Not,
            WrappingAdd, WrappingSub, WrappingMul, SaturatingAdd, SaturatingSub, SaturatingMul,
        ]),
        (Class::Float, &[
            PartialEq, PartialOrd, Show, Default, AnyNum, Num, Float,
            Add, Sub, Mul, Div, Rem, Neg,
        ]),
        (Class::Bool, &[PartialEq, Eq, Hash, Show, Default, Not]),
        (Class::Char, &[PartialEq, Eq, PartialOrd, Ord, Hash, Show]),
        (Class::Str, &[PartialEq, Eq, PartialOrd, Ord, Hash, Show, Default]),
        (Class::Bytes, &[PartialEq, Eq, PartialOrd, Ord, Hash, Default]),
        (Class::Unit, &[PartialEq, Eq, Default]),
        (Class::Parts, &[PartialEq, Eq, PartialOrd, Ord, Hash, Show, Default]),
        (Class::Derived, &[PartialEq, Eq, Hash, Show]),
        (Class::Array, &[PartialEq, Eq]),
        (Class::Bare, &[]),
    ]
};

/// What a trait requires of the types that implement it (§6.3, the `: trait
/// + trait` of its heading). `Copy` and `Dup` are kind constraints: `Copy` ⇒
/// `Dup` is of the kinds (§4.6).
#[rustfmt::skip]
pub(crate) const SUPERS: &[(Bound, &[Bound])] = {
    use Bound::*;
    &[
        (Eq, &[PartialEq]),
        // SPEC-GAP(S-900): §6.3 and §6.4 give `PartialOrd` no requirement.
        (PartialOrd, &[PartialEq]),
        (Ord, &[PartialOrd, Eq]),
        (Copy, &[Dup]),
        (AnyNum, &[Copy, Add, Sub, Mul, Div, Rem, PartialEq, PartialOrd]),
        (Num, &[AnyNum, Neg]),
        (Float, &[Num]),
        (Int, &[
            AnyNum, Eq, Ord, Hash, BitAnd, BitOr, BitXor, Shl, Shr, Not,
            WrappingAdd, WrappingSub, WrappingMul, SaturatingAdd, SaturatingSub, SaturatingMul,
        ]),
        (Unsigned, &[Int]),
    ]
};

impl Class {
    /// The row of a type, none for a type the table does not decide: a named
    /// type, a type parameter (their judgments are of the generics in scope
    /// and of the derives), and what is not a type of a value.
    pub(crate) fn of(ty: &Ty) -> Option<Class> {
        Some(match ty {
            Ty::Int(k) if k.signed() => Class::Signed,
            Ty::Int(_) => Class::Unsigned,
            Ty::Float(_) => Class::Float,
            Ty::Bool => Class::Bool,
            Ty::Char => Class::Char,
            Ty::Unit => Class::Unit,
            Ty::Array(..) | Ty::Tuple(_) => Class::Parts,
            Ty::Builtin(b, _) => match b {
                BuiltinTy::Str => Class::Str,
                BuiltinTy::Bytes => Class::Bytes,
                BuiltinTy::Array => Class::Array,
                BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Buf | BuiltinTy::Span | BuiltinTy::Ptr => Class::Bare,
            },
            Ty::Fn(_) => Class::Bare,
            Ty::Named(..) | Ty::Param(_) | Ty::ConstVal(_) | Ty::Var(_) | Ty::Error => return None,
        })
    }

    /// Whether the row of the class has the trait `b`.
    pub(crate) fn implements(self, b: Bound) -> bool {
        IMPLS.iter().any(|(c, row)| *c == self && row.contains(&b))
    }
}

/// `have` implies `want` among the builtin bounds: it is `want`, or something
/// it requires implies `want` (§6.3: "`T: Ord` の境界からは、上位の trait…も
/// 使える"). [`SUPERS`] has no cycle (a unit test), so it stops.
pub(crate) fn implies(have: Bound, want: Bound) -> bool {
    have == want
        || SUPERS.iter().find(|(b, _)| *b == have).is_some_and(|(_, supers)| supers.iter().any(|&s| implies(s, want)))
}

/// The trait an operator needs of its operands (§3.2, §6.3), one for each.
pub(crate) fn op_bound(op: OpNeed) -> Bound {
    use BinOp::*;
    let OpNeed::Binary(b) = op else {
        return if op == OpNeed::Neg { Bound::Neg } else { Bound::Not };
    };
    match b {
        Eq | Ne => Bound::PartialEq,
        Lt | Le | Gt | Ge => Bound::PartialOrd,
        Add => Bound::Add,
        Sub => Bound::Sub,
        Mul => Bound::Mul,
        Div => Bound::Div,
        Rem => Bound::Rem,
        BitAnd => Bound::BitAnd,
        BitOr => Bound::BitOr,
        BitXor => Bound::BitXor,
        Shl => Bound::Shl,
        Shr => Bound::Shr,
        WrapAdd => Bound::WrappingAdd,
        WrapSub => Bound::WrappingSub,
        WrapMul => Bound::WrappingMul,
        SatAdd => Bound::SaturatingAdd,
        SatSub => Bound::SaturatingSub,
        SatMul => Bound::SaturatingMul,
        // `check_binary` gives them `Bool` and asks for no trait.
        And | Or => onsa_diag::internal::bug(None, "the trait of `&&` / `||` asked"),
    }
}
