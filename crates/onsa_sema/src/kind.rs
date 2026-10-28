//! Kinds (spec §4.6): Copy / Shared / Affine, from the structure of a type.

use crate::ty::{BuiltinTy, Env, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Copy,
    Shared,
    Affine,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Copy => "Copy",
            Kind::Shared => "Shared",
            Kind::Affine => "Affine",
        }
    }
}

/// Kind of a type; `None` when it depends on a generic parameter, or for
/// second-class types (`Span`). A type that holds itself stops with `None`
/// ([`Walk`]).
pub fn kind_of(a: &Analysis, ty: TyId) -> Option<Kind> {
    kind_in(a, ty, None)
}

/// Kind of `ty` read under the arguments `env` (R-30).
pub fn kind_in(a: &Analysis, ty: TyId, env: Option<&Env>) -> Option<Kind> {
    walk(&Walk::new(a), ty, env, 0)
}

/// Kind of a user type by its def (`onsa interface`), without interning its `TyId`.
pub fn kind_of_named(a: &Analysis, d: DefId, args: &[TyId]) -> Option<Kind> {
    named(&Walk::new(a), d, args, None, 0)
}

/// `depth`: the named types entered on the way ([`Walk::enter`]).
fn walk(w: &Walk, ty: TyId, env: Option<&Env>, depth: u32) -> Option<Kind> {
    let (ty, env) = w.at(ty, env)?;
    match ty {
        Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit | Ty::Fn(_) | Ty::ConstVal(_) => Some(Kind::Copy),
        Ty::Array(t, _) => walk(w, *t, env, depth),
        Ty::Tuple(ts) => all(w, ts, env, depth),
        Ty::Builtin(b, args) => match b {
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                Some(Kind::Shared)
            }
            BuiltinTy::Buf => Some(Kind::Affine),
            BuiltinTy::Ptr => Some(Kind::Copy),
            BuiltinTy::Span => None,
            BuiltinTy::Option | BuiltinTy::Result => all(w, args, env, depth),
        },
        Ty::Named(d, args) => named(w, *d, args, env, depth),
        Ty::Param(_) | Ty::Var(_) | Ty::Error => None,
    }
}

fn all(w: &Walk, ts: &[TyId], env: Option<&Env>, depth: u32) -> Option<Kind> {
    let mut kind = Kind::Copy;
    for &t in ts {
        kind = kind.max(walk(w, t, env, depth)?);
    }
    Some(kind)
}

fn named(w: &Walk, d: DefId, args: &[TyId], env: Option<&Env>, depth: u32) -> Option<Kind> {
    let (holds, env, depth) = w.enter(d, args, env, depth)?;
    match holds {
        _ if holds.is_state() => Some(Kind::Affine), // §4.6: flow state is Affine
        Holds::Opaque(_) => Some(Kind::Copy),
        Holds::Nothing => None,
        _ => all(w, &holds.parts(), env.as_ref(), depth),
    }
}
