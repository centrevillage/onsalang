//! The names the spec gives the builtin types and this version has not
//! ([`MISSING`], E0200, §18.1, R-294), and what a receiver takes of `Span[T]`.
//! The members of the builtin types are std's declarations (`std/core/`, and
//! `std/core.onsa` for `Option` and `Result`), and `as` is `crate::cast`.

use onsa_diag::unsupported::Feature;

use crate::ty::{BuiltinTy, Ty, TyId, Types};

/// Whether a receiver of the generic builtin `b` takes the members of
/// `Span[T]` its own `impl`s have not (§5.3: "`Buf[T]` にも同じものがある",
/// D-07): `Buf`. An array does too (it has no name; the types stage's). The
/// one question of the names and the types stages (D-15).
pub(crate) fn takes_span_members(b: BuiltinTy) -> bool {
    b == BuiltinTy::Buf
}

/// What a name of [`MISSING`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// Named through the type (`Str.from_utf8(b)`), or as a value (§6.1).
    Function,
    /// Called on a value (`s.as_bytes()`); named through its type it is what
    /// any method is there (E0308, §15.1).
    Method,
}

/// A name the spec gives the types `of` and this version has not.
struct Missing {
    of: fn(&Ty) -> bool,
    name: &'static str,
    form: Form,
    feature: Feature,
}

fn str_ty(t: &Ty) -> bool {
    matches!(t, Ty::Builtin(BuiltinTy::Str, _))
}

/// What has a length (§4.2) this version does not give: `Bytes`, and `Array`,
/// `Map` and `Set`, of phase 2.
fn no_len_yet(t: &Ty) -> bool {
    matches!(t, Ty::Builtin(BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set, _))
}

/// Every name the spec gives a builtin type and this version has not: E0200
/// where it is named (§18.1, R-294), not the error of a name that does not
/// exist. The work that declares a name takes its row off (a self-test asks
/// that no row names a member of std).
const MISSING: &[Missing] = &[
    Missing { of: str_ty, name: "from_utf8", form: Form::Function, feature: Feature::BuiltinName },
    Missing { of: str_ty, name: "as_bytes", form: Form::Method, feature: Feature::BuiltinName },
    Missing { of: no_len_yet, name: "len", form: Form::Method, feature: Feature::BuiltinName },
];

/// The row of [`MISSING`] of the name `name` of the type `recv`: what the
/// name is and the feature of its E0200. Asked of what is not found.
pub(crate) fn missing(types: &Types, recv: TyId, name: &str) -> Option<(Form, Feature)> {
    let t = types.get(recv);
    MISSING.iter().find(|m| m.name == name && (m.of)(t)).map(|m| (m.form, m.feature))
}

/// The names of the builtin methods (for the gate, Q-14): none, all are
/// std's since `len` of an array is (S-862).
pub fn names() -> Vec<String> {
    Vec::new()
}
