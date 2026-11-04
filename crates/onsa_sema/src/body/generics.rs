//! The generics: the fresh arguments of a use, the substitution, and the
//! instances.

use super::*;
use crate::deferred::{GENERIC_VIEW, VIEW_OF_ARRAY};

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ generics

    /// Fresh variables for a def's generic parameters (owner's first for methods).
    pub(crate) fn fresh_args(&mut self, def: DefId) -> Vec<TyId> {
        let generics = self.all_generics(def);
        // The parameters of an `impl` whose target is the error type (a
        // heading with an error, §18.1) are not decided by a use: the error
        // type (R-324).
        let unread = match self.a.def(def).owner.map(|o| &self.a.def(o).kind) {
            Some(DefKind::Impl(i)) if matches!(self.ty(i.self_ty), Ty::Error) => i.generics.len(),
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

    fn all_generics(&self, def: DefId) -> Vec<GenericDef> {
        let d = self.a.def(def);
        match d.owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) => {
                // Method generics already include the impl's (sig.rs lowers them that way).
                d.generics().to_vec()
            }
            _ => d.generics().to_vec(),
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
    /// (E0406 when still open at the end) and its implicit `Escape`, judged
    /// before the other requirements made after it (§4.5, S-862).
    pub(super) fn type_argument(&mut self, span: Span, t: TyId, what: String) {
        self.type_argument_with(span, t, what, GENERIC_VIEW);
    }

    /// [`Self::type_argument`], with `rule` for its E0710.
    fn type_argument_with(&mut self, span: Span, t: TyId, what: String, rule: &'static str) {
        self.defer(span, t, DeferredKind::Origin { what: what.clone() });
        self.defer(span, t, DeferredKind::Escape { what, rule });
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
        let (impl_count, impl_name) = match self.a.def(def).owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) && def != o => {
                let DefKind::Impl(i) = &self.a.def(o).kind else { unreachable!() };
                let head = self.type_head(i.self_ty);
                (self.a.def(o).generics().len(), format!("the `impl` of `{head}`"))
            }
            _ => (0, String::new()),
        };
        let std = self.a.modules.is_std(self.a.def(def).module);
        for (k, (g, &arg)) in generics.iter().zip(&args).enumerate() {
            let owner = if k < impl_count { impl_name.clone() } else { name.clone() };
            let what = match (&g.kind, &element) {
                (GenericKind::Const(_), _) => format!("the const parameter `{}` of {owner}", g.name),
                (_, Some(Required::SeqElement { recv, method })) if k < impl_count => {
                    format!("the element type of `{method}` of `{}`", self.display(*recv))
                }
                _ => format!("the type parameter `{}` of {owner}", g.name),
            };
            // A parameter with an unknown bound requires nothing of its users (§18.1, S-768).
            let GenericKind::Type { bounds, dup, unknown: false } = &g.kind else {
                self.defer(span, arg, DeferredKind::Origin { what });
                continue;
            };
            let of_seq = k < impl_count && matches!(element, Some(Required::SeqElement { .. }));
            self.type_argument_with(span, arg, what, if of_seq { VIEW_OF_ARRAY } else { GENERIC_VIEW });
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
