//! The one walk through the declarations a type holds, read by the layouts
//! (§12.4) and the placements of a `const` (§6.6): what a declaration holds,
//! the arguments it is read under (R-30), and where the walk stops (D-15).
//! The kinds and the drops read what a declaration holds from here too, once
//! for each ([`crate::summary`]), with no steps.

use std::cell::{Cell, RefCell};

use onsa_diag::hash::HashMap;
use serde::{Deserialize, Serialize};

use crate::def::{DefKind, FieldDef, Fields, FlowTy, VariantDef};
use crate::layout::Layout;
use crate::summary::Summaries;
use crate::ty::{Env, TYPE_DEPTH_LIMIT, Ty, TyId};
use crate::{Analysis, DefId};

/// The steps one walk takes at most: a step reads a type or follows a
/// parameter to its argument, so a walk does work in proportion to them. A
/// walk reads what a declaration holds once for each place it is held in,
/// but once in all of one used with closed arguments ([`Known`]); past the
/// steps it stops with no answer, as at a type that holds itself. A
/// generic type that holds itself with ever larger arguments
/// (`R[T] { t: T, a: R[(T, T)] }`) needs steps exponential in its depth; a
/// chain of declarations deeper than the stack holds (about 70 000) is
/// fewer.
const STEPS: u32 = 1 << 20;

/// The bytes of stack a walk keeps ([`Walk::enter`]).
const STACK_RESERVE: usize = 1 << 20;

/// A declaration and the arguments it is used with ([`Known`]).
pub(crate) type Key = (DefId, Vec<TyId>, Under);

/// How the arguments of a [`Key`] are read (R-317).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum Under {
    /// None is open.
    Closed,
    /// As written, under the environment of the item being found numbered ([`Known`]).
    Item(u32),
}

/// What the walks found of a declaration used with arguments none of which
/// is open ([`crate::ty::Types::open`]), each once (R-313): so a walk through
/// a type that holds the same one in many places (`A_k { x: A_{k-1}, y:
/// A_{k-1} }`, or `G_k[T]` of two `G_{k-1}[T]`) is not exponential. Each is
/// found with steps and a depth of its own ([`Walk::remember`]), so it is
/// the same whichever walk asks first (§18.1), no answer past [`STEPS`] too:
/// a walk that holds one takes one step for it. And of one used with open
/// arguments under the environment of an item being found (R-317: `G_k[T]`
/// of two `G_{k-1}[Option[T]]`), found within that item: none but it asks
/// them, so they go when it is found (`items`), and the table keeps no more
/// than the items being found hold, whatever the items found before. Kept
/// from the end of the lowering of the declarations (`ready`), whose fields
/// are not all lowered before.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct Known {
    pub(crate) ready: bool,
    /// The keys under each item being found, at its number.
    items: RefCell<Vec<Vec<Key>>>,
    pub(crate) layouts: RefCell<HashMap<Key, Option<Layout>>>,
    /// What each declaration asked holds: before `ready`, of no use to the
    /// next question ([`crate::summary::Read::new`]). Not in the base of
    /// std: each is read again when a package asks it, once.
    #[serde(skip)]
    pub(crate) summaries: RefCell<Summaries>,
}

/// What a declaration a walk enters holds.
/// `state`: a struct a flow made for its state (§11.6).
pub(crate) enum Holds<'d> {
    Fields(&'d [FieldDef], bool),
    Variants(&'d [VariantDef]),
    /// The type of an alias, read under no arguments (§4.4).
    Alias(TyId),
    /// A type of the target or of `extern`, and flow state until M3.
    Opaque(bool),
    Nothing,
}

impl Holds<'_> {
    /// The types held, of all fields and variants.
    pub(crate) fn parts(&self) -> Vec<TyId> {
        match self {
            Holds::Fields(fs, _) => fs.iter().map(|f| f.ty).collect(),
            Holds::Variants(vs) => vs.iter().flat_map(|v| v.fields.iter().copied()).collect(),
            Holds::Alias(t) => vec![*t],
            Holds::Opaque(_) | Holds::Nothing => Vec::new(),
        }
    }

    pub(crate) fn is_state(&self) -> bool {
        matches!(self, Holds::Fields(_, true) | Holds::Opaque(true))
    }
}

/// One walk from one type. `None` from a step stops the whole walk with no
/// answer: past [`STEPS`], or at a type that holds itself ([`Walk::enter`]).
pub(crate) struct Walk<'a> {
    pub a: &'a Analysis,
    steps: Cell<u32>,
}

impl<'a> Walk<'a> {
    pub(crate) fn new(a: &'a Analysis) -> Self {
        Walk { a, steps: Cell::new(STEPS) }
    }

    fn step(&self) -> Option<()> {
        self.steps.set(self.steps.get().checked_sub(1)?);
        Some(())
    }

    /// The layout of `d` used with `args` under `env` ([`Known`]): one step,
    /// and the one kept or the one `find` finds, given the number of the
    /// item for [`Walk::enter`]. With closed arguments, from the depth 0
    /// with [`STEPS`] of its own, which the walk around does not spend; with
    /// open ones under a numbered environment, from `depth` with the steps
    /// of the walk (only the item of that number reaches it). One being
    /// found and entered again holds itself (through `Ptr`, `Span`): no
    /// answer. Else `find` from `depth`, with no number.
    pub(crate) fn remember(
        &self,
        (d, args, env, depth): (DefId, &[TyId], Option<&Env>, u32),
        find: impl FnOnce(u32, Option<u32>) -> Option<Layout>,
    ) -> Option<Layout> {
        let types = &self.a.types;
        let closed = |&t: &TyId| Some(types.resolve(t, env).0).filter(|&t| !types.open(t));
        let key = self.a.known.ready.then(|| match args.iter().map(closed).collect::<Option<Vec<TyId>>>() {
            Some(args) => Some((d, args, Under::Closed)),
            None => env.and_then(|e| e.key).map(|m| (d, args.to_vec(), Under::Item(m))),
        });
        let Some(key) = key.flatten() else { return find(depth, None) };
        self.step()?;
        let known = &self.a.known;
        if let Some(t) = known.layouts.borrow().get(&key) {
            return t.clone();
        }
        if let Under::Item(m) = key.2 {
            known.items.borrow_mut()[m as usize].push(key.clone());
        }
        let n = known.items.borrow().len() as u32;
        known.items.borrow_mut().push(Vec::new());
        known.layouts.borrow_mut().insert(key.clone(), None);
        // Read under the environment of an item: only that item reaches it.
        let found = if let Under::Item(_) = key.2 {
            find(depth, Some(n))
        } else {
            let around = self.steps.replace(STEPS);
            let found = find(0, Some(n));
            self.steps.set(around);
            found
        };
        known.layouts.borrow_mut().insert(key, found.clone());
        // The keys under it: none asks them now.
        for k in known.items.borrow_mut().pop().into_iter().flatten() {
            known.layouts.borrow_mut().remove(&k);
        }
        found
    }

    /// `ty` read under `env`: a parameter is followed to its argument, read
    /// under the environment around; one with no argument stays.
    pub(crate) fn at<'e>(&self, mut ty: TyId, mut env: Option<&'e Env<'e>>) -> Option<(&'a Ty, Option<&'e Env<'e>>)> {
        loop {
            self.step()?;
            match (self.a.types.get(ty), env) {
                (Ty::Param(i), Some(e)) if (*i as usize) < e.args.len() => (ty, env) = (e.args[*i as usize], e.outer),
                (t, _) => return Some((t, env)),
            }
        }
    }

    /// Enter `d`, used with `args` under `env` at `depth` named types in, as
    /// the item numbered `key` ([`Walk::remember`]): what it holds, the
    /// environment to read it under (none for an alias, §4.4), and the depth
    /// one deeper. A type that holds none of itself enters no more than the
    /// depth of a type (§4.4) and a chain of every declaration; past them,
    /// the type holds itself (an E0311, R-02) and the walk stops. The stack
    /// under the limit is the safety net of S-67: an internal error, not a
    /// signal.
    pub(crate) fn enter<'e>(
        &self,
        d: DefId,
        args: &'e [TyId],
        env: Option<&'e Env<'e>>,
        (depth, key): (u32, Option<u32>),
    ) -> Option<(Holds<'a>, Option<Env<'e>>, u32)> {
        let depth = depth + 1;
        if onsa_diag::stack::remaining().is_some_and(|left| left < STACK_RESERVE) {
            let msg = format!("a type holds declarations {depth} deep, deeper than the stack holds");
            onsa_diag::internal::bug(Some(self.a.def(d).name_span), msg);
        }
        if depth as usize > TYPE_DEPTH_LIMIT as usize + self.a.defs.len() {
            return None;
        }
        let inner = Some(Env { args, outer: env, key });
        let holds = match &self.a.def(d).kind {
            DefKind::Struct(s) => {
                let state = s.flow_ty == Some(FlowTy::State);
                match &s.fields {
                    Fields::Named(fs) => Holds::Fields(fs, state),
                    Fields::Opaque => Holds::Opaque(state),
                }
            }
            DefKind::Enum(e) => Holds::Variants(&e.variants),
            DefKind::Alias(t) => return Some((Holds::Alias(*t), None, depth)),
            _ => Holds::Nothing,
        };
        Some((holds, inner, depth))
    }
}
