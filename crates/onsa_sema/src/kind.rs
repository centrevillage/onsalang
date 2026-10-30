//! Kinds (spec §4.6): Copy / Shared / Affine, from the structure of a type.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use crate::body::bounds::Bounds;
use crate::def::{Bound, GenericDef, GenericKind};
use crate::ty::{BuiltinTy, Env, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    walk(&Walk::new(a), ty, env, (0, None))
}

/// The kind a value of `ty` in a body with the type parameters `generics` is
/// taken for by the questions of the modes (R-30): a type parameter by its
/// bounds wherever the walk meets it (`Pair[T]` too): Copy if it meets
/// `Copy`, Shared if `Dup`, else Affine (`?Dup`). A walk past its steps is
/// Affine; the other walks with no answer are none and keep quiet (§18.1:
/// the error type, a type parameter with an unknown bound, whose kind each
/// answer would claim, a declaration a syntax error cut, a type that holds
/// itself; a second-class type has no kind, §4.6).
pub(crate) fn kind_in_body(a: &Analysis, ty: TyId, generics: &[GenericDef]) -> Option<Kind> {
    let bounds = Bounds { a, generics };
    let param = |(i, g): (usize, &GenericDef)| {
        let known = matches!(g.kind, GenericKind::Type { unknown: false, .. });
        let p = a.types.find(&Ty::Param(i as u32)).filter(|_| known)?;
        let meets = |b| bounds.satisfies(p, b);
        let kinds = [(Bound::Copy, Kind::Copy), (Bound::Dup, Kind::Shared)];
        Some(kinds.into_iter().find(|&(b, _)| meets(b)).map_or(Kind::Affine, |(_, k)| k))
    };
    let params: Vec<Option<Kind>> = generics.iter().enumerate().map(param).collect();
    let w = Walk::in_body(a, &params);
    walk(&w, ty, None, (0, Some(&params))).or_else(|| w.spent().then_some(Kind::Affine))
}

/// Kind of a user type by its def (`onsa interface`), without interning its `TyId`.
pub fn kind_of_named(a: &Analysis, d: DefId, args: &[TyId]) -> Option<Kind> {
    named(&Walk::new(a), d, args, None, (0, None))
}

/// `depth`: the named types entered on the way ([`Walk::enter`]); `params[i]`:
/// in a body ([`kind_in_body`]), the kind of its type parameter `i`, met with
/// no argument around. One it does not have is of a declaration a syntax
/// error cut (§18.1): none, as one with an unknown bound.
type At<'p> = (u32, Option<&'p [Option<Kind>]>);

fn walk(w: &Walk, ty: TyId, env: Option<&Env>, at: At) -> Option<Kind> {
    let (ty, env) = w.at(ty, env)?;
    match ty {
        Ty::Param(i) if env.is_none() => at.1?.get(*i as usize).copied().flatten(),
        Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit | Ty::Fn(_) | Ty::ConstVal(_) => Some(Kind::Copy),
        Ty::Array(t, _) => walk(w, *t, env, at),
        Ty::Tuple(ts) => all(w, ts, env, at),
        // Of the arguments it holds as values, as of an enum (§4.4).
        Ty::Builtin(b, args) if b.holds_values() => all(w, args, env, at),
        Ty::Builtin(b, _) => match b {
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                Some(Kind::Shared)
            }
            BuiltinTy::Buf => Some(Kind::Affine),
            BuiltinTy::Ptr => Some(Kind::Copy),
            BuiltinTy::Span | BuiltinTy::Option | BuiltinTy::Result => None,
        },
        Ty::Named(d, args) => named(w, *d, args, env, at),
        Ty::Param(_) | Ty::Var(_) | Ty::Error => None,
    }
}

/// The kind of an aggregate of the parts `ts` (§4.6: the greatest): Affine
/// if a part is, whatever the kind of a part with none would be; else none
/// if a part has none.
fn all(w: &Walk, ts: &[TyId], env: Option<&Env>, at: At) -> Option<Kind> {
    let mut kind = Some(Kind::Copy);
    for &t in ts {
        match walk(w, t, env, at) {
            Some(Kind::Affine) => return Some(Kind::Affine),
            k => kind = kind.zip(k).map(|(a, b)| a.max(b)),
        }
    }
    kind
}

/// The answer kept of an item hangs on `params` only as its key does: its
/// arguments are closed, of the parameters of a body numbered by their
/// kinds, or read under the environment of an item being found
/// ([`Walk::remember`]).
fn named(w: &Walk, d: DefId, args: &[TyId], env: Option<&Env>, (depth, params): At) -> Option<Kind> {
    w.remember(&w.a.known.kinds, (d, args, env, depth), |depth, key| {
        let (holds, env, depth) = w.enter(d, args, env, (depth, key))?;
        match holds {
            _ if holds.is_state() => Some(Kind::Affine), // §4.6: flow state is Affine
            Holds::Opaque(_) => Some(Kind::Copy),
            Holds::Nothing => None,
            _ => all(w, &holds.parts(), env.as_ref(), (depth, params)),
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
                let (holds, _, depth) = self.w.enter(*d, args, None, (depth, None))?;
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
