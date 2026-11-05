//! The builtin method std does not declare yet (spec §5.3, S-09): `len` of
//! an array (W5-17). Its signature only; lowering implements it. The other
//! members of the builtin types are std's declarations (`std/core/`, and
//! `std/core.onsa` for `Option` and `Result`), and `as` is `crate::cast`.
//!
//! Every method is one row of the table here ([`methods`]); the lookups
//! read the rows, so the names are written once, and [`names`] lists them
//! for the gate's check of hard-coded builtin names (Q-14, W1-02).
//!
//! [`MISSING`] is the one list of the names the spec gives the builtin types
//! and this version has not (E0200, §18.1, R-294).

use std::sync::OnceLock;

use onsa_diag::unsupported::Feature;
use onsa_syntax::ast::Mode;

use crate::ty::{BuiltinTy, IntKind, Ty, TyId, Types};

/// A builtin method: parameter types (receiver excluded) and result.
#[derive(Debug, Clone)]
pub struct MethodSig {
    pub params: Vec<TyId>,
    pub ret: TyId,
    /// The mode of `self` (§5.2: `inout self` needs the `!` mark).
    pub self_mode: Mode,
}

/// The receivers a builtin method is defined on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Recv {
    /// `[T; N]`, its `len` of any element (§5.3, S-862). The other members
    /// of the sequences are std's (`std/core/seq.onsa`); `Array[T]` has
    /// none in this version (D5).
    Array,
}

/// A type in a method's signature, relative to the receiver.
#[derive(Debug, Clone, Copy)]
enum T {
    U32,
}

/// One builtin method.
struct Method {
    recv: Recv,
    name: String,
    params: &'static [T],
    ret: T,
    /// The mode of `self`.
    self_mode: Mode,
}

/// Every builtin method.
fn methods() -> &'static [Method] {
    static TABLE: OnceLock<Vec<Method>> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut v = Vec::new();
        let mut add = |recv, name: &str, params: &'static [T], ret| {
            v.push(Method { recv, name: name.to_string(), params, ret, self_mode: Mode::Borrow })
        };
        // The arrays (§5.3); no `is_empty` (§4.2).
        add(Recv::Array, "len", &[], T::U32);
        v
    })
}

/// The row of the method `name` of the receiver type `recv_ty`.
fn method_row(recv_ty: &Ty, name: &str) -> Option<&'static Method> {
    let family = match recv_ty {
        Ty::Array(..) => Recv::Array,
        _ => return None,
    };
    methods().iter().find(|m| m.recv == family && m.name == name)
}

/// Whether the builtin type `recv` (a scalar, or a generic one by its key)
/// has the method `name`, and whether it is called with `!`: the question
/// of the names stage, which makes no type (`Str.len(s)`, §15.1).
pub(crate) fn method_bang(types: &Types, recv: TyId, name: &str) -> Option<bool> {
    method_self(types, recv, name).map(|m| m == Mode::Inout)
}

/// The mode of `self` of the method `name` of a receiver of the type
/// `recv` (§5.2, §9.1); none of a name the table has not.
pub(crate) fn method_self(types: &Types, recv: TyId, name: &str) -> Option<Mode> {
    method_row(types.get(recv), name).map(|m| m.self_mode)
}

/// Whether a receiver of the generic builtin `b` takes the members of
/// `Span[T]` its own `impl`s have not (§5.3: "`Buf[T]` にも同じものがある",
/// D-07): `Buf`. An array does too (it has no name; the types stage's). The
/// one question of the names and the types stages (D-15).
pub(crate) fn takes_span_members(b: BuiltinTy) -> bool {
    b == BuiltinTy::Buf
}

/// Method `name` on a receiver of (resolved, non-variable) type `recv`.
pub fn method(types: &mut Types, recv: TyId, name: &str) -> Option<MethodSig> {
    let recv_ty = types.get(recv).clone();
    let m = method_row(&recv_ty, name)?;
    let params = m.params.iter().map(|t| sig_ty(types, *t)).collect();
    Some(MethodSig { params, ret: sig_ty(types, m.ret), self_mode: m.self_mode })
}

fn sig_ty(types: &mut Types, t: T) -> TyId {
    match t {
        T::U32 => types.int(IntKind::U32),
    }
}

/// What a name of [`MISSING`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// Named through the type (`I32.default()`), or as a value (§6.1).
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

/// What has `Default` with a literal for its value (§6.3).
fn literal_default(t: &Ty) -> bool {
    t.is_number() || str_ty(t) || *t == Ty::Bool
}

fn bytes(t: &Ty) -> bool {
    matches!(t, Ty::Builtin(BuiltinTy::Bytes, _))
}

/// What has a length (§4.2) this version does not give: `Bytes`, and `Array`,
/// `Map` and `Set`, of phase 2.
fn no_len_yet(t: &Ty) -> bool {
    matches!(t, Ty::Builtin(BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set, _))
}

/// Every name the spec gives a builtin type and this version has not: E0200
/// where it is named (§18.1, R-294), not the error of a name that does not
/// exist. The work that declares a name takes its row off (a self-test asks
/// that no row names a member of std): `default`, W5-06.
const MISSING: &[Missing] = &[
    Missing { of: literal_default, name: "default", form: Form::Function, feature: Feature::BuiltinValueName },
    Missing { of: bytes, name: "default", form: Form::Function, feature: Feature::BuiltinName },
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

/// The names of every builtin method, sorted and without duplicates (for
/// the gate, Q-14).
pub fn names() -> Vec<String> {
    let mut v: Vec<String> = methods().iter().map(|m| m.name.clone()).collect();
    v.sort();
    v.dedup();
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_list_every_row() {
        let n = names();
        for x in ["PI", "BITS", "from_bits", "narrow_from", "trunc_sat_from", "to_bits", "abs", "checked_add"] {
            assert!(!n.iter().any(|y| y == x), "{x} is std's (§6.6, §3.3), in {n:?}");
        }
        // The sequences' but `len` of an array are std's (`std/core/seq.onsa`, D1).
        for x in ["get", "fill", "slice", "copy_from", "add_from"] {
            assert!(!n.iter().any(|y| y == x), "{x} is std's (§5.3), in {n:?}");
        }
        // `Str`'s and `Buf.zeroed` are std's (`std/core/`, D1, R-96, R-104).
        for x in ["substr", "find", "get_substr", "is_char_boundary", "is_empty", "zeroed"] {
            assert!(!n.iter().any(|y| y == x), "{x} is std's or none, in {n:?}");
        }
        // `unwrap` is std's (`std/core.onsa`, S-785), and the others are
        // no method of `Option` or `Result` (§9.1, R-96).
        for x in ["unwrap", "is_some", "is_none", "is_ok", "is_err", "unwrap_or"] {
            assert!(!n.iter().any(|y| y == x), "{x} is std's or none, in {n:?}");
        }
        assert!(n.iter().any(|y| y == "len"), "len not in {n:?}");
        let mut sorted = n.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(n, sorted);
    }

    #[test]
    fn every_row_resolves_on_its_receiver() {
        let mut types = Types::default();
        let i32 = types.int(IntKind::I32);
        let f32 = types.float(crate::ty::FloatKind::F32);
        let buf = types.builtin(BuiltinTy::Buf, vec![f32]);
        let arr = types.intern(Ty::Array(f32, crate::ty::Len::Const(2)));
        let s = types.builtin(BuiltinTy::Str, vec![]);
        for m in methods() {
            let recv = match m.recv {
                Recv::Array => arr,
            };
            assert!(method(&mut types, recv, &m.name).is_some(), "{}", m.name);
        }
        // The scalars have no row: their members are std's.
        assert!(method(&mut types, i32, "checked_add").is_none());
        assert!(method(&mut types, f32, "to_bits").is_none());
        assert!(method(&mut types, s, "fill").is_none());
        assert!(method(&mut types, s, "len").is_none(), "std's (`std/core/str.onsa`)");
        // `Buf[T]` and `Span[T]` take std's members (§5.3), and an array its
        // `len` only, with no `is_empty` (§4.2).
        assert!(method(&mut types, buf, "len").is_none());
        assert!(method(&mut types, arr, "is_empty").is_none());
    }
}
