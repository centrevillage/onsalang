//! Kinds (spec §4.6): Copy / Shared / Affine, from the structure of a type.

use std::cell::{Cell, RefCell};

use onsa_diag::hash::{HashMap, HashSet};
use serde::{Deserialize, Serialize};

use crate::bounds::Bounds;
use crate::def::{Bound, GenericDef, GenericKind};
use crate::summary::{Facts, Read};
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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
/// second-class types (`Span`), and for a type that holds itself ([`Facts`]).
pub fn kind_of(a: &Analysis, ty: TyId) -> Option<Kind> {
    Read::new(a, Vec::new()).of(ty).kind
}

/// The kind a value of `ty` in a body with the type parameters `generics` is
/// taken for by the questions of the modes (R-30) and by the kind constraints
/// of the types stage (R-176, [`Bounds::meets`]): a type parameter by its
/// bounds wherever `ty` holds it (`Pair[T]` too): Copy if it meets `Copy`,
/// Shared if `Dup`, else Affine (`?Dup`). With no answer it is none and
/// keeps quiet (§18.1: the error type, a type parameter with an unknown
/// bound, whose kind each answer would claim, a declaration a syntax error
/// cut, a type that holds itself; a second-class type has no kind, §4.6).
pub(crate) fn kind_in_body(a: &Analysis, ty: TyId, generics: &[GenericDef]) -> Option<Kind> {
    let bounds = Bounds { a, generics };
    let param = |(i, g): (usize, &GenericDef)| {
        let known = matches!(g.kind, GenericKind::Type { unknown: false, .. });
        let p = a.types.find(&Ty::Param(i as u32)).filter(|_| known)?;
        let meets = |b| bounds.satisfies(p, b);
        let kinds = [(Bound::Copy, Kind::Copy), (Bound::Dup, Kind::Shared)];
        Some(kinds.into_iter().find(|&(b, _)| meets(b)).map_or(Kind::Affine, |(_, k)| k))
    };
    Read::new(a, generics.iter().enumerate().map(|g| Facts::param(param(g))).collect()).of(ty).kind
}

/// Kind of a user type by its def (`onsa interface`), without interning its `TyId`.
pub fn kind_of_named(a: &Analysis, d: DefId, args: &[TyId]) -> Option<Kind> {
    Read::new(a, Vec::new()).named(d, args).kind
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
            _ => Some(match kind_of(self.w.a, ty)? {
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
