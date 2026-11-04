//! The builtin methods std does not declare yet (spec §4.1, §5.3, S-09):
//! of `Option` and `Result` (W5-03 makes them std's enums) and `len` of an
//! array (W5-17). Signatures only; lowering implements them. The other
//! members of the builtin types are std's declarations (`std/core/`), and
//! `as` is `crate::cast`.
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
    /// The arguments are evaluated on some paths only (`o.unwrap_or(d)`
    /// evaluates `d` when `o` is `None`; the lowering of the method): a
    /// flow takes no stateful call there (K-08, W3-10). W5-03 removes it
    /// with `unwrap_or` (no method of §4.1, R-96, E0413), and the case
    /// `tests/spec/negative/flow_map_unsupported_w5_03.onsa` with it.
    pub lazy_args: bool,
}

/// The receivers a builtin method is defined on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Recv {
    /// `[T; N]`, its `len` of any element (§5.3, S-862). The other members
    /// of the sequences are std's (`std/core/seq.onsa`); `Array[T]` has
    /// none in this version (D5).
    Array,
    Option,
    Result,
}

/// A type in a method's signature, relative to the receiver.
#[derive(Debug, Clone, Copy)]
enum T {
    /// The element of a sequence, the content of `Option` / `Result`.
    Inner,
    U32,
    Bool,
}

/// One builtin method.
struct Method {
    recv: Recv,
    name: String,
    params: &'static [T],
    ret: T,
    /// The mode of `self`.
    self_mode: Mode,
    /// [`MethodSig::lazy_args`].
    lazy_args: bool,
}

/// Every builtin method.
fn methods() -> &'static [Method] {
    static TABLE: OnceLock<Vec<Method>> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut v = Vec::new();
        let mut add = |recv, name: &str, params: &'static [T], ret| {
            v.push(Method { recv, name: name.to_string(), params, ret, self_mode: Mode::Borrow, lazy_args: false })
        };
        // The arrays (§5.3); no `is_empty` (§4.2).
        add(Recv::Array, "len", &[], T::U32);
        // Option and Result (§4.1).
        add(Recv::Option, "is_some", &[], T::Bool);
        add(Recv::Option, "is_none", &[], T::Bool);
        add(Recv::Result, "is_ok", &[], T::Bool);
        add(Recv::Result, "is_err", &[], T::Bool);
        // `move self`: it takes the content out (§9.1, S-785).
        for recv in [Recv::Option, Recv::Result] {
            let name = "unwrap".to_string();
            v.push(Method { recv, name, params: &[], ret: T::Inner, self_mode: Mode::Move, lazy_args: false });
        }
        // The default is evaluated only for `None` (the lowering's `Switch`).
        let unwrap_or = "unwrap_or".to_string();
        v.push(Method {
            recv: Recv::Option,
            name: unwrap_or,
            params: &[T::Inner],
            ret: T::Inner,
            self_mode: Mode::Borrow,
            lazy_args: true,
        });
        v
    })
}

/// The row of the method `name` of the receiver type `recv_ty`, and its
/// element type (none of the key of a generic type, `Analysis::builtin_key`).
fn method_row(recv_ty: &Ty, name: &str) -> Option<(&'static Method, Option<TyId>)> {
    let (families, inner): (&[Recv], Option<TyId>) = match recv_ty {
        Ty::Array(elem, _) => (&[Recv::Array], Some(*elem)),
        Ty::Builtin(BuiltinTy::Option, args) => (&[Recv::Option], args.first().copied()),
        Ty::Builtin(BuiltinTy::Result, args) => (&[Recv::Result], args.first().copied()),
        _ => return None,
    };
    Some((methods().iter().find(|m| families.contains(&m.recv) && m.name == name)?, inner))
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
    method_row(types.get(recv), name).map(|(m, _)| m.self_mode)
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
    let (m, inner) = method_row(&recv_ty, name)?;
    let mut ty = |t: T| sig_ty(types, t, inner);
    let params = m.params.iter().map(|t| ty(*t)).collect::<Option<Vec<_>>>()?;
    let ret = ty(m.ret)?;
    Some(MethodSig { params, ret, self_mode: m.self_mode, lazy_args: m.lazy_args })
}

fn sig_ty(types: &mut Types, t: T, inner: Option<TyId>) -> Option<TyId> {
    Some(match t {
        T::Inner => inner?,
        T::U32 => types.int(IntKind::U32),
        T::Bool => types.bool(),
    })
}

/// What a name of [`MISSING`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// Named through the type (`F32.ZERO`).
    Constant,
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
/// that no row names a member of std): `ZERO` and `ONE`, W5-05; `default`,
/// W5-06.
const MISSING: &[Missing] = &[
    Missing { of: Ty::is_number, name: "ZERO", form: Form::Constant, feature: Feature::BuiltinValueName },
    Missing { of: Ty::is_number, name: "ONE", form: Form::Constant, feature: Feature::BuiltinValueName },
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
        for x in ["len", "unwrap", "is_err", "unwrap_or"] {
            assert!(n.iter().any(|y| y == x), "{x} not in {n:?}");
        }
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
        let opt = types.builtin(BuiltinTy::Option, vec![f32]);
        let res = types.builtin(BuiltinTy::Result, vec![f32, s]);
        for m in methods() {
            let recv = match m.recv {
                Recv::Array => arr,
                Recv::Option => opt,
                Recv::Result => res,
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
