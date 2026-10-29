//! The one walk through the declarations a type holds, read by the kinds
//! (§4.6), the layouts (§12.4) and the drops of `rt` (§12.2): what a
//! declaration holds, the arguments it is read under (R-30), and where the
//! walk stops (D-15).

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::def::{DefKind, FieldDef, Fields, FlowTy, VariantDef};
use crate::kind::Kind;
use crate::layout::Layout;
use crate::ty::{Env, TYPE_DEPTH_LIMIT, Ty, TyId};
use crate::{Analysis, DefId};

/// The steps one walk takes at most: a step reads a type or follows a
/// parameter to its argument, so a walk does work in proportion to them. A
/// walk reads what a declaration holds once for each place it is held in,
/// but once in all of one used with closed arguments ([`Known`]); past the
/// steps it stops with no answer, as at a type that holds itself. A
/// generic type that holds itself with ever larger arguments
/// (`R[T] { t: T, a: R[(T, T)] }`) needs steps exponential in its depth; a
/// chain of declarations deeper than the stack holds (about 100 000) is
/// fewer.
const STEPS: u32 = 1 << 20;

/// The bytes of stack a walk keeps ([`Walk::enter`]).
const STACK_RESERVE: usize = 1 << 20;

/// A declaration and the arguments it is used with ([`Known`]).
pub(crate) type Key = (DefId, Vec<TyId>, Under);

/// How the arguments of a [`Key`] are read (R-317).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Under {
    /// None is open.
    Closed,
    /// As written, in a body whose type parameters are of the kinds numbered ([`Walk::in_body`]).
    Body(u32),
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
/// them, so they go when it is found (`items`), and the tables keep no more
/// than the items being found hold, whatever the items found before. Kept
/// from the end of the lowering of the declarations (`ready`), whose fields
/// are not all lowered before.
#[derive(Debug, Default)]
pub(crate) struct Known {
    pub(crate) ready: bool,
    /// The keys under each item being found, at its number.
    items: RefCell<Vec<Vec<Key>>>,
    /// The kinds of the type parameters of a body, numbered ([`Walk::in_body`]).
    bodies: RefCell<HashMap<Vec<Option<Kind>>, u32>>,
    pub(crate) kinds: RefCell<HashMap<Key, Found<Kind>>>,
    pub(crate) layouts: RefCell<HashMap<Key, Found<Layout>>>,
    pub(crate) drops: RefCell<HashMap<Key, Found<bool>>>,
}

/// An answer kept, and whether it is none as its walk went past [`STEPS`]
/// ([`Walk::spent`]).
pub(crate) type Found<T> = (Option<T>, bool);

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
    spent: Cell<bool>,
    /// The number of the type parameters of the body the walk is in, the
    /// environment of the types read under none (`kind::kind_in_body`).
    body: Option<u32>,
}

impl<'a> Walk<'a> {
    pub(crate) fn new(a: &'a Analysis) -> Self {
        Walk { a, steps: Cell::new(STEPS), spent: Cell::new(false), body: None }
    }

    /// A walk in a body whose type parameters are of the kinds `params`: so
    /// one of `G_k[T]` keeps what it finds of each step (R-317), as a kind
    /// depends on the kinds of the parameters only.
    pub(crate) fn in_body(a: &'a Analysis, params: &[Option<Kind>]) -> Self {
        let mut bodies = a.known.bodies.borrow_mut();
        let next = bodies.len() as u32;
        let body = Some(*bodies.entry(params.to_vec()).or_insert(next));
        Walk { body, ..Walk::new(a) }
    }

    fn step(&self) -> Option<()> {
        let left = self.steps.get().checked_sub(1);
        self.spent.set(self.spent.get() || left.is_none());
        self.steps.set(left?);
        Some(())
    }

    /// Whether the walk went past [`STEPS`], its own or those of an item it
    /// holds ([`Walk::remember`]): its no answer is of the steps, not of an
    /// error, nor of a type that holds itself (R-30, §18.1).
    pub(crate) fn spent(&self) -> bool {
        self.spent.get()
    }

    /// The answer in `table` of `d` used with `args` under `env` ([`Known`]):
    /// one step, and the one kept or the one `find` finds, given the number
    /// of the item for [`Walk::enter`]. With closed arguments, or open ones
    /// of the parameters of the body of the walk, from the depth 0 with
    /// [`STEPS`] of its own, which the walk around does not spend; with open
    /// ones under a numbered environment, from `depth` with the steps of the
    /// walk (only the item of that number reaches it). One
    /// being found and entered again holds itself (through `Ptr`, `Span`):
    /// no answer. Else `find` from `depth`, with no number. A walk past its
    /// steps is kept with the answer, so one that holds it is too.
    pub(crate) fn remember<T: Clone>(
        &self,
        table: &RefCell<HashMap<Key, Found<T>>>,
        (d, args, env, depth): (DefId, &[TyId], Option<&Env>, u32),
        find: impl FnOnce(u32, Option<u32>) -> Option<T>,
    ) -> Option<T> {
        let types = &self.a.types;
        let closed = |&t: &TyId| Some(types.resolve(t, env).0).filter(|&t| !types.open(t));
        let under = |e: Option<&Env>| e.map_or(self.body.map(Under::Body), |e| e.key.map(Under::Item));
        let key = self.a.known.ready.then(|| match args.iter().map(closed).collect::<Option<Vec<TyId>>>() {
            Some(args) => Some((d, args, Under::Closed)),
            None => under(env).map(|u| (d, args.to_vec(), u)),
        });
        let Some(key) = key.flatten() else { return find(depth, None) };
        self.step()?;
        if let Some((t, spent)) = table.borrow().get(&key) {
            self.spent.set(self.spent.get() || *spent);
            return t.clone();
        }
        let known = &self.a.known;
        if let Under::Item(m) = key.2 {
            known.items.borrow_mut()[m as usize].push(key.clone());
        }
        let n = known.items.borrow().len() as u32;
        known.items.borrow_mut().push(Vec::new());
        table.borrow_mut().insert(key.clone(), (None, false));
        let was = self.spent.replace(false);
        // Read under the environment of an item: only that item reaches it.
        let found = if let Under::Item(_) = key.2 {
            find(depth, Some(n))
        } else {
            let around = self.steps.replace(STEPS);
            let found = find(0, Some(n));
            self.steps.set(around);
            found
        };
        let spent = self.spent.get();
        self.spent.set(was || spent);
        table.borrow_mut().insert(key, (found.clone(), spent && found.is_none()));
        // The keys under it: none asks them now.
        for k in known.items.borrow_mut().pop().into_iter().flatten() {
            known.kinds.borrow_mut().remove(&k);
            known.layouts.borrow_mut().remove(&k);
            known.drops.borrow_mut().remove(&k);
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
