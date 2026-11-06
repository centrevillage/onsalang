//! The generics: the fresh arguments of a use, the substitution, and the
//! instances.

use super::*;
use crate::deferred::{GENERIC_VIEW, LIFTED_VIEW, VIEW_OF_ARRAY};

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ generics

    /// Fresh variables for a def's generic parameters (owner's first for methods).
    pub(crate) fn fresh_args(&mut self, def: DefId) -> Vec<TyId> {
        let generics = self.all_generics(def);
        // The parameters of an `impl` whose target is the error type (a
        // heading with an error, §18.1) are not decided by a use: the error
        // type (R-324), and those of a constant of [`Self::const_unread`].
        let unread = match self.a.def(def).owner.map(|o| &self.a.def(o).kind) {
            Some(DefKind::Impl(i)) if matches!(self.ty(i.self_ty), Ty::Error) || self.const_unread(def) => {
                i.generics.len()
            }
            _ => 0,
        };
        generics
            .iter()
            .enumerate()
            .map(|(k, g)| match g.kind {
                _ if k < unread => self.a.types.error(),
                GenericKind::Const(_) => {
                    let len = self.infer.fresh_len();
                    let Len::Var(v) = len else { unreachable!() };
                    self.a.types.intern(Ty::Var(v))
                }
                _ => self.fresh(),
            })
            .collect()
    }

    /// `def` is a constant of an `impl` with an error of its heading
    /// (`impl[T] N[T]` for `N[T: Num]`), which is read as it is: the read
    /// decides nothing and reports nothing (§18.1, S-304).
    pub(super) fn const_unread(&self, def: DefId) -> bool {
        let d = self.a.def(def);
        matches!(d.kind, DefKind::Const(_)) && d.owner.is_some_and(|o| self.a.failures.failed(o))
    }

    /// The generic parameters a use of `def` decides: the ones of the `impl`
    /// first (a method's generics include them, sig.rs lowers them that way;
    /// an associated constant has only those).
    fn all_generics(&self, def: DefId) -> Vec<GenericDef> {
        match self.a.def(def).kind {
            DefKind::Const(_) => crate::body::generics_of(self.a, def),
            _ => self.a.def(def).generics().to_vec(),
        }
    }

    /// The name of the type `t` with no type argument (`W` of `W[T]`, `Buf`
    /// of `Buf[T]`): what names its members (§6.2), and no variable of the
    /// inference in a message (§18.1, R-357).
    pub(super) fn type_head(&mut self, t: TyId) -> String {
        match self.ty(t) {
            Ty::Named(d, _) => self.a.def(d).name.clone(),
            Ty::Builtin(b, _) => b.name().to_string(),
            _ => self.display(t),
        }
    }

    /// The type argument `t` a use made at `span`, named `what`: its origin
    /// (E0406 when still open at the end) and its implicit `Escape`, of the
    /// rule `rule`, judged before the other requirements made after it (§4.5,
    /// S-862). `way`: the note of the E0406; `lifted`: its parameter is
    /// `?Escape`.
    fn type_argument(
        &mut self,
        span: Span,
        t: TyId,
        what: ArgumentName,
        way: Option<String>,
        (rule, lifted): (&'static str, bool),
    ) {
        self.defer(span, t, DeferredKind::Origin { what: what.clone(), rule: way });
        self.defer(span, t, DeferredKind::Escape { what, rule, lifted });
    }

    /// How the parameters of the `impl` of the type `head` of the constant
    /// `def` are given (S-304, no candidate: which arguments is the writer's;
    /// `Self` where the body is of an `impl` of that type, the same definition
    /// and not one of the same name). `None`: `def` is no constant.
    fn way_of_const(&mut self, def: DefId, of: TyId, head: &str) -> Option<String> {
        let d = self.a.def(def);
        if !matches!(d.kind, DefKind::Const(_)) {
            return None;
        }
        let name = d.name.clone();
        // `{head}::[…].{name}` is E0200 until W5-10, and the note gives it then.
        let alias = format!("give the type its arguments by an alias: `type R = {head}[…]`, then `R.{name}`");
        let in_impl = self.self_ty.is_some_and(|s| match (self.ty(s), self.ty(of)) {
            (Ty::Named(a, _), Ty::Named(b, _)) => a == b,
            (Ty::Builtin(a, _), Ty::Builtin(b, _)) => a == b,
            _ => false,
        });
        Some(if in_impl { format!("{alias}; inside this `impl`, `Self.{name}`") } else { alias })
    }

    /// Record an instantiation made by the expression at `span`. Its arguments
    /// may be decided by a later statement (§4.5, §4.7; S-174): each one is an
    /// origin (E0406 when still open at the end) and carries the requirements of
    /// its parameter (the bounds and the implicit `Dup`, E0416, S-235).
    pub(super) fn finish_instance(&mut self, def: DefId, args: Vec<TyId>, span: Span) -> R<Option<InstId>> {
        self.instance(def, args, span, None)
    }

    /// [`Self::finish_instance`]; the requirements of the parameters of an
    /// `impl` as `element` when it is given (the element of a sequence
    /// receiver, S-853).
    pub(super) fn instance(
        &mut self,
        def: DefId,
        args: Vec<TyId>,
        span: Span,
        element: Option<Required>,
    ) -> R<Option<InstId>> {
        if args.is_empty() {
            return Ok(None);
        }
        let generics = self.all_generics(def);
        // A method's generics start with its `impl`'s (sig.rs): those belong to the `impl`.
        let name = format!("`{}`", self.a.def(def).name);
        let (impl_count, impl_name, way) = match self.a.def(def).owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) && def != o => {
                let DefKind::Impl(i) = &self.a.def(o).kind else { unreachable!() };
                let of = i.self_ty;
                let head = self.type_head(of);
                let way = self.way_of_const(def, of, &head);
                (self.a.def(o).generics().len(), format!("the `impl` of `{head}`"), way)
            }
            _ => (0, String::new(), None),
        };
        let std = self.a.modules.is_std(self.a.def(def).module);
        for (k, (g, &arg)) in generics.iter().zip(&args).enumerate() {
            let owner = if k < impl_count { impl_name.clone() } else { name.clone() };
            let what = match (&g.kind, &element) {
                (GenericKind::Const(_), _) => {
                    ArgumentName::Text(format!("the const parameter `{}` of {owner}", g.name))
                }
                (_, Some(Required::SeqElement { recv, method })) if k < impl_count => {
                    ArgumentName::SeqElement { recv: *recv, method: method.clone() }
                }
                _ => ArgumentName::Text(format!("the type parameter `{}` of {owner}", g.name)),
            };
            // A parameter with an unknown bound requires nothing of its users (§18.1, S-768).
            let GenericKind::Type { bounds, dup, unknown: false, .. } = &g.kind else {
                self.defer(span, arg, DeferredKind::Origin { what, rule: way.clone() });
                continue;
            };
            let of_seq = k < impl_count && matches!(element, Some(Required::SeqElement { .. }));
            let lifted = g.lifts_escape();
            let rule = if lifted {
                LIFTED_VIEW
            } else if of_seq {
                VIEW_OF_ARRAY
            } else {
                GENERIC_VIEW
            };
            self.type_argument(span, arg, what, way.clone(), (rule, lifted));
            let required = || match (&element, k < impl_count) {
                (Some(e), true) => e.clone(),
                _ => Required::Param { param: g.name.clone(), owner: owner.clone(), std },
            };
            if *dup {
                self.defer(span, arg, DeferredKind::Require { bound: Bound::Dup, what: required() });
            }
            for &b in bounds {
                self.defer(span, arg, DeferredKind::Require { bound: b, what: required() });
            }
        }
        let id = InstId(self.info.instances.len() as u32);
        self.info.instances.push(Instance { def, args, span });
        Ok(Some(id))
    }
}
