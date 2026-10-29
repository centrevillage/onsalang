//! Kinds (spec §4.6): Copy / Shared / Affine, from the structure of a type.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

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
        // Of the arguments it holds as values, as of an enum (§4.4).
        Ty::Builtin(b, args) if b.holds_values() => all(w, args, env, depth),
        Ty::Builtin(b, _) => match b {
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                Some(Kind::Shared)
            }
            BuiltinTy::Buf => Some(Kind::Affine),
            BuiltinTy::Ptr => Some(Kind::Copy),
            BuiltinTy::Span | BuiltinTy::Option | BuiltinTy::Result => None,
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
    w.remember(&w.a.known.kinds, (d, args, env, depth), |depth| {
        let (holds, env, depth) = w.enter(d, args, env, depth)?;
        match holds {
            _ if holds.is_state() => Some(Kind::Affine), // §4.6: flow state is Affine
            Holds::Opaque(_) => Some(Kind::Copy),
            Holds::Nothing => None,
            _ => all(w, &holds.parts(), env.as_ref(), depth),
        }
    })
}

/// Where the result of a `const` of a type can be placed (§6.6, S-610), in
/// the order of the worst part: in the static area (`Static`: Copy), there
/// from the second phase (`Later`: a Shared `Str`, `Bytes` or `Array` of
/// such parts, and a type parameter not `Copy`, W4-05 table 5), or never
/// (`Never`: `Map`, `Set`, Affine).
// S-773: a type with a Shared part and one never placed (`(Str, Buf[F32])`) is
// `Never`, the E0407: the error of every version before the E0200 of this one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Placed {
    Static,
    Later,
    Never,
}

/// Where a `const` of `ty` can be placed; `copy[i]`: whether the type
/// parameter `i` in scope is `Copy`. `None` when a part has no kind (a
/// second-class type, S-771; the error type, a field with an error too, and
/// a declaration a syntax error cut, §18.1): its own diagnostic is that
/// part's.
pub(crate) fn placed(a: &Analysis, ty: TyId, copy: &[bool]) -> Option<Placed> {
    let params: Vec<_> = copy.iter().map(|&c| Some(if c { Placed::Static } else { Placed::Later })).collect();
    let p = Place { w: Walk::new(a), seen: RefCell::default(), found: RefCell::default(), grew: Cell::new(true) };
    let mut placed = None;
    while p.grew.replace(false) {
        p.seen.borrow_mut().clear();
        placed = Some(p.of(ty, &params, 0)?);
    }
    placed
}

/// A declaration and the placements of the arguments it is read with.
type Key = (DefId, Vec<Option<Placed>>);

/// One question of [`placed`]: the worst part reached. Unlike the kinds, it
/// walks into the arguments `Array`, `Map` and `Set` hold, where a type holds
/// itself (`Tree { a: Array[Tree] }`), with ever larger arguments too
/// (`Q[T] { a: Array[Q[(T, T)]] }`). So a declaration is read with the
/// placements of its arguments, a finite key, once a round (`seen`); one
/// reached again is what it was found (`found`, at first `Static`). The
/// rounds go on while one grows, so each comes to the worst it reaches,
/// whichever is asked first (a key grows twice at most, so the rounds are at
/// most twice the keys and one).
struct Place<'a> {
    w: Walk<'a>,
    seen: RefCell<HashSet<Key>>,
    found: RefCell<HashMap<Key, Placed>>,
    grew: Cell<bool>,
}

impl Place<'_> {
    /// `params[i]`: the placement of the argument of the parameter `i` of
    /// the declaration `ty` is in; `depth` as of [`Walk::enter`].
    fn of(&self, ty: TyId, params: &[Option<Placed>], depth: u32) -> Option<Placed> {
        let all = |ts: &[TyId]| self.all(ts, params, depth);
        match self.w.at(ty, None)?.0 {
            Ty::Builtin(BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Buf, ts) => all(ts).map(|_| Placed::Never),
            Ty::Builtin(BuiltinTy::Array, ts) => Some(all(ts)?.max(Placed::Later)),
            Ty::Builtin(b, ts) if b.holds_values() => all(ts),
            Ty::Array(e, _) => self.of(*e, params, depth),
            Ty::Tuple(ts) => all(ts),
            Ty::Param(i) => params.get(*i as usize).copied().flatten(),
            // A declaration a syntax error cut: what it holds is not all read (§18.1).
            Ty::Named(d, _) if self.w.a.failed.contains_key(d) => None,
            Ty::Named(d, args) => {
                let key = (*d, args.iter().map(|&t| self.of(t, params, depth)).collect::<Vec<_>>());
                let was = self.found.borrow().get(&key).copied().unwrap_or(Placed::Static);
                if !self.seen.borrow_mut().insert(key.clone()) {
                    return Some(was);
                }
                let (holds, _, depth) = self.w.enter(*d, args, None, depth)?;
                let now = match holds {
                    _ if holds.is_state() => Placed::Never,
                    Holds::Opaque(_) => Placed::Static,
                    Holds::Nothing => return None,
                    _ => self.all(&holds.parts(), &key.1, depth)?,
                };
                if now != was {
                    self.found.borrow_mut().insert(key, now);
                    self.grew.set(true);
                }
                Some(now)
            }
            // The leaves as their kinds.
            _ => Some(match kind_in(self.w.a, ty, None)? {
                Kind::Copy => Placed::Static,
                Kind::Shared => Placed::Later,
                Kind::Affine => Placed::Never,
            }),
        }
    }

    fn all(&self, ts: &[TyId], params: &[Option<Placed>], depth: u32) -> Option<Placed> {
        ts.iter().try_fold(Placed::Static, |p, &t| Some(p.max(self.of(t, params, depth)?)))
    }
}
