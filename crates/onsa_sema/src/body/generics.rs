//! The generics: the fresh arguments of a use, the substitution, and the
//! instances.

use super::*;
use crate::requirement::{Requirement, alias_way, head_of, parameter, requirements};

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ generics

    /// Fresh variables for a def's generic parameters (owner's first for methods).
    pub(crate) fn fresh_args(&mut self, def: DefId) -> Vec<TyId> {
        let generics = self.all_generics(def);
        // The parameters of an `impl` whose target is the error type (a
        // heading with an error, §18.1) are not decided by a use: the error
        // type (R-324), and those of a constant of [`crate::constarg::unread`].
        let unread = match self.a.def(def).owner.map(|o| &self.a.def(o).kind) {
            Some(DefKind::Impl(i))
                if matches!(self.ty(i.self_ty), Ty::Error) || crate::constarg::unread(self.a, def) =>
            {
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
        head_of(self.a, t).unwrap_or_else(|| self.display(t))
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
        let alias = alias_way(head, &name);
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
        self.instance(def, args, span, (None, None))
    }

    /// [`Self::finish_instance`]; the requirements of the parameters of an
    /// `impl` as `element` when it is given (the element of a sequence
    /// receiver, S-853), and `own`, the note of the E0406 of an own parameter
    /// of the function (S-303).
    pub(super) fn instance(
        &mut self,
        def: DefId,
        args: Vec<TyId>,
        span: Span,
        (element, own): (Option<Required>, Option<String>),
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
                (GenericKind::Const(_), _) => ArgumentName::Text(parameter(g, &owner)),
                (_, Some(Required::SeqElement { recv, method })) if k < impl_count => {
                    ArgumentName::SeqElement { recv: *recv, method: method.clone() }
                }
                _ => ArgumentName::Text(parameter(g, &owner)),
            };
            let of_seq = k < impl_count && matches!(element, Some(Required::SeqElement { .. }));
            // Its origin (E0406 when still open at the end, `way` its note),
            // then its requirements as items in their order.
            // An effect row variable takes no type argument (S-982): no note of them.
            let listed = !matches!(g.kind, GenericKind::Effect);
            let rule = if k < impl_count { way.clone() } else { own.clone().filter(|_| listed) };
            self.defer(span, arg, DeferredKind::Origin { what: what.clone(), rule });
            let Some(wants) = requirements(g, of_seq) else { continue };
            let required = || match (&element, k < impl_count) {
                (Some(e), true) => e.clone(),
                _ => Required::Param { param: g.name.clone(), owner: owner.clone(), std },
            };
            for q in wants {
                let kind = match q {
                    Requirement::Escape { rule, lifted } => DeferredKind::Escape { what: what.clone(), rule, lifted },
                    Requirement::Bound(bound) => DeferredKind::Require { bound, what: required() },
                };
                self.defer(span, arg, kind);
            }
        }
        let id = InstId(self.info.instances.len() as u32);
        self.info.instances.push(Instance { def, args, span });
        Ok(Some(id))
    }
}
