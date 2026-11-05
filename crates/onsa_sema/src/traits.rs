//! The provisional tables of the traits (§6.3, S-72, R-127): what the builtin
//! types implement, what a trait requires, the names a trait gives a type
//! parameter, and the trait of each operator. In phase 2 they become the
//! declarations of std: a row of [`IMPLS`] its `impl`s, a row of [`SUPERS`]
//! the heading of a `trait`, a row of [`MEMBERS`] the items of a `trait`; the
//! table of the operators stays. The judgments under the generics in scope
//! are [`crate::body::bounds`], which reads these.

use onsa_syntax::ast::BinOp;

use crate::def::Bound;
use crate::deferred::OpNeed;
use crate::prim::{NARROW_FROM, ROUND_FROM, TRUNC_FROM, TRUNC_SAT_FROM};
use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty};
use crate::{Analysis, DefId};

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

/// The type whose declarations stand for the members of a row of [`MEMBERS`]:
/// a member of a type parameter is the member of this type, with this type
/// read as the parameter (`crate::ty::Types::replace`; [`crate::body::Target`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rep {
    I32,
    F32,
}

impl Rep {
    pub(crate) fn ty(self) -> Ty {
        match self {
            Rep::I32 => Ty::Int(IntKind::I32),
            Rep::F32 => Ty::Float(FloatKind::F32),
        }
    }
}

/// The names the number traits give a type parameter (§3.3, §6.3, §6.6): the
/// constants, the conversion functions and the methods. A row has no forms:
/// those are the declarations of std, one place (D-15), held equal for every
/// type of the row by a unit test.
#[rustfmt::skip]
pub(crate) const MEMBERS: &[(Bound, Rep, &[&str])] = &[
    (Bound::AnyNum, Rep::I32, &["ZERO"]),
    (Bound::Float, Rep::F32, &["ONE", "PI", "MAX", "EPSILON", "INFINITY", "NAN", ROUND_FROM]),
    (Bound::Int, Rep::I32, &[
        "ONE", "MIN", "MAX", "BITS", NARROW_FROM, TRUNC_FROM, TRUNC_SAT_FROM,
        "div_euclid", "rem_euclid", "checked_add", "checked_sub", "checked_mul", "checked_div",
        "checked_rem", "checked_div_euclid", "checked_rem_euclid", "checked_shl", "checked_shr",
    ]),
];

/// The representative type of the member `name` of a type parameter of the
/// bounds `bounds`: of the first row of [`MEMBERS`] with the name, of a trait
/// a bound implies.
pub(crate) fn member_rep(bounds: &[Bound], name: &str) -> Option<Rep> {
    let gives = |b| bounds.iter().any(|&have| implies(have, b));
    MEMBERS.iter().find(|(b, _, names)| names.contains(&name) && gives(*b)).map(|&(_, rep, _)| rep)
}

/// The declaration of the member `name` of a type parameter of the bounds
/// `bounds`: none with no such member, or with no std loaded.
pub(crate) fn member(a: &Analysis, bounds: &[Bound], name: &str) -> Option<DefId> {
    let key = a.types.find(&member_rep(bounds, name)?.ty())?;
    a.modules.assoc_builtin.get(&key)?.get(name).copied()
}

/// The trait of the first row of [`MEMBERS`] with the name `name`.
pub(crate) fn member_trait(name: &str) -> Option<Bound> {
    MEMBERS.iter().find(|(_, _, names)| names.contains(&name)).map(|&(b, _, _)| b)
}

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
