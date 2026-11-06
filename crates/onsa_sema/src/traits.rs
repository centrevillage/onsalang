//! The provisional tables of the traits (§6.3, S-72, R-127): what the builtin
//! types implement, what a trait requires, the names a trait gives a type
//! parameter, and the trait of each operator. In phase 2 they become the
//! declarations of std: a row of [`IMPLS`] its `impl`s, a row of [`SUPERS`]
//! the heading of a `trait`, a row of [`MEMBERS`] the items of a `trait`; the
//! table of the operators stays. The judgments under the generics in scope
//! are [`crate::body::bounds`], which reads these.

use onsa_syntax::ast::{BinOp, Mode};

use crate::def::{Bound, Derive, DerivedFn};
use crate::deferred::OpNeed;
use crate::prim::{NARROW_FROM, ROUND_FROM, TRUNC_FROM, TRUNC_SAT_FROM};
use crate::ty::{BuiltinTy, FloatKind, IntKind, Ty, TyId};
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

/// The derivable traits (§6.4, S-34), in the order of the spec: the closed
/// list, the bound of each, and whether this version derives it (`false`:
/// E0200, S-13). The one table of the two.
pub(crate) const DERIVABLE: [(Derive, Bound, bool); 8] = [
    (Derive::PartialEq, Bound::PartialEq, true),
    (Derive::Eq, Bound::Eq, true),
    (Derive::PartialOrd, Bound::PartialOrd, true),
    (Derive::Ord, Bound::Ord, true),
    (Derive::Hash, Bound::Hash, true),
    (Derive::Show, Bound::Show, false),
    (Derive::Default, Bound::Default, true),
    (Derive::Ordinal, Bound::Ordinal, true),
];

/// The trait a derive of a list makes of the bound `b`, none of a bound no
/// list holds.
pub(crate) fn derive_of(b: Bound) -> Option<Derive> {
    DERIVABLE.iter().find(|row| row.1 == b).map(|row| row.0)
}

/// What the list `written` derives: its traits and what they require
/// (§6.4, S-900), once each, in the order of the spec.
pub(crate) fn derived(written: &[Bound]) -> Vec<Derive> {
    let in_list = |b: Bound| written.iter().any(|&w| implies(w, b));
    DERIVABLE.iter().filter(|row| in_list(row.1)).map(|row| row.0).collect()
}

/// The type whose declarations stand for the members of a row of [`MEMBERS`]:
/// a member of a type parameter is the member of this type, with this type
/// read as the parameter (`crate::ty::Types::replace`; [`crate::body::Target`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rep {
    I32,
    F32,
    /// `AnyOrdinal` of std: no builtin type has `Ordinal` (§6.4).
    Ordinal,
}

impl Rep {
    /// The key of its table of members in `assoc_builtin`, or its def in
    /// `assoc`: none with no std loaded.
    pub(crate) fn table(self, a: &Analysis) -> (Option<TyId>, Option<DefId>) {
        let ty = match self {
            Rep::I32 => Ty::Int(IntKind::I32),
            Rep::F32 => Ty::Float(FloatKind::F32),
            Rep::Ordinal => return (None, a.modules.lang.any_ordinal()),
        };
        (a.types.find(&ty), None)
    }
}

/// The constants of the ends of a type: a float type has no [`MIN`], which
/// reads as two values in the languages it comes from, and writes the most
/// negative value with [`MAX`] (§6.6).
pub(crate) const MIN: &str = "MIN";
pub(crate) const MAX: &str = "MAX";

/// The members of `Default` and `Ordinal` (§6.3, §6.4).
pub(crate) const DEFAULT: &str = "default";
const ORDINAL: &str = "ordinal";
const FROM_ORDINAL: &str = "from_ordinal";

/// The names the number traits give a type parameter (§3.3, §6.3, §6.6): the
/// constants, the conversion functions and the methods. A row has no forms:
/// those are the declarations of std, one place (D-15), held equal for every
/// type of the row by a unit test.
#[rustfmt::skip]
pub(crate) const MEMBERS: &[(Bound, Rep, &[&str])] = &[
    (Bound::AnyNum, Rep::I32, &["ZERO"]),
    (Bound::Float, Rep::F32, &["ONE", "PI", MAX, "EPSILON", "INFINITY", "NAN", ROUND_FROM]),
    (Bound::Int, Rep::I32, &[
        "ONE", MIN, MAX, "BITS", NARROW_FROM, TRUNC_FROM, TRUNC_SAT_FROM,
        "div_euclid", "rem_euclid", "checked_add", "checked_sub", "checked_mul", "checked_div",
        "checked_rem", "checked_div_euclid", "checked_rem_euclid", "checked_shl", "checked_shr",
    ]),
    (Bound::Default, Rep::I32, &[DEFAULT]),
    (Bound::Ordinal, Rep::Ordinal, &[ORDINAL, FROM_ORDINAL]),
];

/// A type of the signature of a [`TraitItem`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ItemTy {
    SelfTy,
    U32,
    OptionSelf,
}

/// A member of a trait with the form every type gives it (§6.3, §6.4): `rt`,
/// with an empty effect row (S-905, S-907). In phase 2, an item of a `trait`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TraitItem {
    pub bound: Bound,
    pub name: &'static str,
    pub made: DerivedFn,
    /// The mode of `self`, none of an associated function.
    pub recv: Option<Mode>,
    pub params: &'static [(&'static str, ItemTy)],
    pub ret: ItemTy,
}

/// The members of the traits a list makes (§6.4), in the order of [`DerivedFn`]:
/// the one form of what a derive makes and of what an `impl` writes.
#[rustfmt::skip]
pub(crate) const TRAIT_ITEMS: [TraitItem; 3] = [
    TraitItem {
        bound: Bound::Default, name: DEFAULT, made: DerivedFn::Default,
        recv: None, params: &[], ret: ItemTy::SelfTy,
    },
    TraitItem {
        bound: Bound::Ordinal, name: ORDINAL, made: DerivedFn::Ordinal,
        recv: Some(Mode::Borrow), params: &[], ret: ItemTy::U32,
    },
    TraitItem {
        bound: Bound::Ordinal, name: FROM_ORDINAL, made: DerivedFn::FromOrdinal,
        recv: None, params: &[("n", ItemTy::U32)], ret: ItemTy::OptionSelf,
    },
];

impl DerivedFn {
    /// Its row of [`TRAIT_ITEMS`].
    pub(crate) fn item(self) -> &'static TraitItem {
        &TRAIT_ITEMS[self as usize]
    }

    /// The name of the member.
    pub fn name(self) -> &'static str {
        self.item().name
    }
}

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
    let table = match member_rep(bounds, name)?.table(a) {
        (_, Some(d)) => a.modules.assoc.get(&d)?,
        (key, None) => a.modules.assoc_builtin.get(&key?)?,
    };
    table.get(name).copied()
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

/// The trait a generic function narrows a bound to for the operator `op`
/// (§6.3): its own trait for a comparison, else the number trait that has it.
pub(crate) fn narrowed_bound(op: OpNeed) -> Bound {
    match op_bound(op) {
        b @ (Bound::PartialEq | Bound::PartialOrd) => b,
        b if implies(Bound::Num, b) => Bound::Num,
        _ => Bound::Int,
    }
}

/// Whether a type can meet `want` and all of `bounds`: a row of [`IMPLS`] has
/// them, or the list of §6.4 does (`Ordinal` is in no row, and an enum derives
/// it with the others). Without either, no type meets them together
/// (`Unsigned` and `Num`, §6.3). A kind constraint is in no row, and is
/// decided by the kind.
pub(crate) fn narrowable(bounds: &[Bound], want: Bound) -> bool {
    let holds = |has: &dyn Fn(Bound) -> bool| has(want) && bounds.iter().all(|&b| b.is_kind_constraint() || has(b));
    IMPLS.iter().any(|(_, row)| holds(&|b| row.contains(&b))) || holds(&|b| derive_of(b).is_some())
}

/// The number traits (§6.3), in the order a note names them.
const NUMBER_TRAITS: [Bound; 5] = [Bound::AnyNum, Bound::Num, Bound::Float, Bound::Int, Bound::Unsigned];

/// The note of the E0416 of the type `ty`, shown as `shown`, that does not
/// meet `want` (§6.3): the number traits it does, of its row of [`IMPLS`];
/// none of another trait, and of a type that meets no number trait.
pub(crate) fn number_traits_note(ty: &Ty, shown: &str, want: Bound) -> Option<String> {
    let row = Class::of(ty).filter(|_| NUMBER_TRAITS.contains(&want))?;
    let met: Vec<Bound> = NUMBER_TRAITS.into_iter().filter(|&b| row.implements(b)).collect();
    (!met.is_empty()).then(|| format!("`{shown}` satisfies the number traits {} (§6.3)", named(&met)))
}

/// The note of the E0302 of `param.name`, a name its bounds do not give
/// (§6.3): the traits that do; none of a name of no row of [`MEMBERS`].
pub(crate) fn member_note(param: &str, name: &str) -> Option<String> {
    let rows: Vec<Bound> = MEMBERS.iter().filter(|(_, _, names)| names.contains(&name)).map(|&(b, ..)| b).collect();
    let section = if rows.contains(&Bound::Ordinal) { "§6.4" } else { "§6.3" };
    (!rows.is_empty()).then(|| {
        format!("`{name}` is a member of {}, which the bounds of `{param}` do not imply ({section})", named(&rows))
    })
}

/// The bounds `bs`, for the text of a note: `` `A`, `B` and `C` ``.
fn named(bs: &[Bound]) -> String {
    let names: Vec<String> = bs.iter().map(|b| format!("`{}`", b.name())).collect();
    match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => names.concat(),
    }
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
