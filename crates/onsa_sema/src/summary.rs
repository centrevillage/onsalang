//! The kind (§4.6) and the drops (§12.2) of a type, from a summary of each
//! declaration (S-782). Both are the greatest of the parts of a type, so
//! those of `G[A]` hang on the kinds of `A`, not on its form: what `G` holds
//! of its own, and which parameters it holds as values, are read once from
//! the types it writes, and a question does not go into the declaration
//! with the arguments of its use. With no steps to count, neither answer
//! hangs on how many forms of arguments a chain of declarations makes.
//!
//! A question takes time in proportion to the types it reads, each once
//! ([`Read::seen`]), and each declaration is read once: a chain goes on to
//! a declaration not read, and one being read is no answer ([`Facts::cycle`]).

use std::cell::RefCell;

use onsa_diag::hash::{HashMap, HashSet};

use crate::kind::Kind;
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

/// What is known of the types as they are lowered ([`crate::walk::Known`]):
/// the summary of each declaration asked, `None` as it is read, and the
/// facts of each type asked with no parameter in it (R-449: `W[W[…[I32]]]`
/// read once for all the questions of its parts, not again for each). Both
/// go together ([`Summaries::clear`]), or those of a cycle ([`Summaries::forget_new`]).
#[derive(Debug, Default, Clone)]
pub(crate) struct Summaries {
    pub(crate) decls: HashMap<DefId, Option<Facts>>,
    closed: HashMap<TyId, Facts>,
    cycle: Option<Cycle>,
}

/// The declarations of a cycle, and what is kept that holds them: read with
/// a read of one of them or of these, as `reads` counts ([`Summaries::held`]).
#[derive(Debug, Default, Clone)]
struct Cycle {
    decls: HashSet<DefId>,
    holds: (HashSet<DefId>, HashSet<TyId>),
    reads: usize,
}

#[cfg(test)]
thread_local! {
    /// The questions of a declaration with its arguments ([`Read::named`]) of this thread.
    pub(crate) static NAMED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl Summaries {
    pub(crate) fn clear(&mut self) {
        self.decls.clear();
        self.closed.clear();
        self.cycle = None;
    }

    /// What is kept from here that holds the declarations `cycle` is what
    /// [`Self::forget_new`] forgets: none before does (`Sema::wellformed`).
    pub(crate) fn begin(&mut self, cycle: HashSet<DefId>) {
        self.cycle = (!cycle.is_empty()).then(|| Cycle { decls: cycle, ..Cycle::default() });
    }

    pub(crate) fn forget_new(&mut self) {
        let Some(Cycle { holds: (decls, types), .. }) = &mut self.cycle else { return };
        decls.drain().for_each(|d| _ = self.decls.remove(&d));
        types.drain().for_each(|t| _ = self.closed.remove(&t));
    }

    /// The count of the reads of what holds the cycle before this, one if `holds`.
    fn reads(&mut self, holds: impl FnOnce(&Cycle) -> bool) -> usize {
        let Some(c) = &mut self.cycle else { return 0 };
        let before = c.reads;
        c.reads += usize::from(holds(c));
        before
    }

    /// What holds the cycle, if one was read since `before`: so does what was read.
    fn held(&mut self, before: usize) -> Option<&mut (HashSet<DefId>, HashSet<TyId>)> {
        self.cycle.as_mut().filter(|c| c.reads != before).map(|c| &mut c.holds)
    }
}

/// What is known of a type, or of a declaration before its arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Facts {
    /// Its kind, of what is read so far: `None` for a part with no kind
    /// (a second-class type, the error type, a type parameter with no
    /// answer), which an Affine part outweighs.
    pub(crate) kind: Option<Kind>,
    /// Whether dropping it needs `Alloc`: Shared values, `Buf` and a type
    /// parameter not Copy, not flow state, Affine as it is. `None` only of a
    /// type that holds itself.
    pub(crate) drops: Option<bool>,
    /// The type parameters of the declaration held as values: not those
    /// only named by a type whose arguments no value of it holds (`Ptr[T]`,
    /// `Array[T]`, a function type).
    held: Vec<u32>,
}

impl Facts {
    fn leaf(kind: Option<Kind>, drops: bool) -> Facts {
        Facts { kind, drops: Some(drops), held: Vec::new() }
    }

    /// Of a part that is Copy: nothing to drop.
    fn copy() -> Facts {
        Facts::leaf(Some(Kind::Copy), false)
    }

    /// Of a type parameter of the kind `kind` when a question has it in
    /// scope: its drop needs `Alloc` unless it is Copy (§6.3, `?Dup` too).
    /// With no answer it keeps quiet (§18.1).
    pub(crate) fn param(kind: Option<Kind>) -> Facts {
        Facts::leaf(kind, kind.is_some_and(|k| k != Kind::Copy))
    }

    /// Of a type of which nothing is known (§18.1).
    fn none() -> Facts {
        Facts::leaf(None, false)
    }

    /// Of a declaration read again as it is read: it holds itself (E0311),
    /// and what it holds has no answer.
    fn cycle() -> Facts {
        Facts { kind: None, drops: None, held: Vec::new() }
    }

    fn builtin(b: BuiltinTy) -> Facts {
        match b {
            BuiltinTy::Str | BuiltinTy::Bytes | BuiltinTy::Array | BuiltinTy::Map | BuiltinTy::Set => {
                Facts::leaf(Some(Kind::Shared), true)
            }
            BuiltinTy::Buf => Facts::leaf(Some(Kind::Affine), true),
            // A `Ptr` (Copy, §4.1) and a `Span` (a view) own nothing to drop.
            BuiltinTy::Ptr => Facts::leaf(Some(Kind::Copy), false),
            BuiltinTy::Span => Facts::none(),
        }
    }

    /// Of an aggregate of two parts (§4.6: the greatest).
    fn join(mut self, other: Facts) -> Facts {
        self.kind = greatest(self.kind, other.kind, Kind::Affine);
        self.drops = greatest(self.drops, other.drops, true);
        for i in other.held {
            if !self.held.contains(&i) {
                self.held.push(i);
            }
        }
        self
    }
}

/// The greatest of `a` and `b`: `top` if one is, whatever one with no answer
/// would be; else none if one has none. So it does not hang on the order.
fn greatest<T: Ord + Copy>(a: Option<T>, b: Option<T>, top: T) -> Option<T> {
    if a == Some(top) || b == Some(top) {
        return Some(top);
    }
    a.zip(b).map(|(a, b)| a.max(b))
}

/// One question, over types whose parameters have the facts `params`.
pub(crate) struct Read<'a> {
    w: Walk<'a>,
    /// By number; none when reading a declaration for its summary, where
    /// each parameter is held.
    params: Option<Vec<Facts>>,
    /// The answers so far, of the types with parts: a type made by a body
    /// from one before it twice (`(t, t)`) has one `TyId` for both.
    seen: RefCell<HashMap<TyId, Facts>>,
}

impl<'a> Read<'a> {
    /// Before the declarations are all lowered (`Known::ready`), a summary
    /// holds only for one question.
    pub(crate) fn new(a: &'a Analysis, params: Vec<Facts>) -> Self {
        if !a.known.ready {
            a.known.summaries.borrow_mut().clear();
        }
        Read::of_params(a, Some(params))
    }

    fn of_params(a: &'a Analysis, params: Option<Vec<Facts>>) -> Self {
        Read { w: Walk::new(a), params, seen: RefCell::default() }
    }

    pub(crate) fn of(&self, ty: TyId) -> Facts {
        // Of no parameter, its facts are the same whatever those of the
        // parameters are, kept for every question ([`Summaries`]); a summary
        // has none, and reads each declaration once.
        let (kept, closed) = (&self.w.a.known.summaries, self.params.is_some() && !self.w.a.types.open(ty));
        let before = kept.borrow_mut().reads(|c| c.holds.1.contains(&ty));
        let found = match self.w.a.types.get(ty) {
            Ty::Param(i) => {
                return match &self.params {
                    Some(params) => params.get(*i as usize).cloned().unwrap_or_else(Facts::none),
                    None => Facts { held: vec![*i], ..Facts::copy() },
                };
            }
            Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit | Ty::Fn(_) | Ty::ConstVal(_) => {
                return Facts::copy();
            }
            Ty::Array(t, _) => return self.of(*t),
            Ty::Builtin(b, _) => return Facts::builtin(*b),
            Ty::Var(_) | Ty::Error => return Facts::none(),
            _ if self.seen.borrow().contains_key(&ty) => return self.seen.borrow()[&ty].clone(),
            _ if closed && kept.borrow().closed.contains_key(&ty) => return kept.borrow().closed[&ty].clone(),
            Ty::Tuple(ts) => self.all(ts),
            Ty::Named(d, args) => self.named(*d, args),
        };
        match closed {
            true => {
                let mut kept = kept.borrow_mut();
                kept.closed.insert(ty, found.clone());
                kept.held(before).map(|h| h.1.insert(ty));
            }
            false => _ = self.seen.borrow_mut().insert(ty, found.clone()),
        }
        found
    }

    /// Of the declaration `d` used with `args`: what it holds of its own and
    /// the arguments of the parameters it holds. An argument it does not
    /// have is of a declaration a syntax error cut (§18.1): nothing known.
    pub(crate) fn named(&self, d: DefId, args: &[TyId]) -> Facts {
        #[cfg(test)]
        NAMED.with(|n| n.set(n.get() + 1));
        let mut own = self.summary(d);
        let held = std::mem::take(&mut own.held);
        let of_arg = |i| args.get(i as usize).map_or_else(Facts::none, |&t| self.of(t));
        held.into_iter().map(of_arg).fold(own, Facts::join)
    }

    fn all(&self, ts: &[TyId]) -> Facts {
        ts.iter().map(|&t| self.of(t)).fold(Facts::copy(), Facts::join)
    }

    /// The summary of `d`, read when it is first asked ([`crate::walk::Known`]).
    fn summary(&self, d: DefId) -> Facts {
        let a = self.w.a;
        let mut kept = a.known.summaries.borrow_mut();
        let before = kept.reads(|c| c.decls.contains(&d) || c.holds.0.contains(&d));
        if let Some(found) = kept.decls.get(&d) {
            return found.clone().unwrap_or_else(Facts::cycle);
        }
        kept.decls.insert(d, None);
        drop(kept);
        let Some((holds, ..)) = self.w.enter(d, &[], None, (0, None)) else { return Facts::cycle() };
        let parts = Read::of_params(a, None).all(&holds.parts());
        let kind = match holds {
            _ if holds.is_state() => Some(Kind::Affine), // §4.6: flow state is Affine
            Holds::Opaque(_) => Some(Kind::Copy),
            Holds::Nothing => None,
            _ => parts.kind,
        };
        let found = Facts { kind, ..parts };
        let mut kept = a.known.summaries.borrow_mut();
        kept.decls.insert(d, Some(found.clone()));
        kept.held(before).map(|h| h.0.insert(d));
        found
    }
}
