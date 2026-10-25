//! The generics: the fresh arguments of a use, the substitution, and the
//! instances.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ generics

    /// Fresh variables for a def's generic parameters (owner's first for methods).
    pub(crate) fn fresh_args(&mut self, def: DefId) -> Vec<TyId> {
        let generics = self.all_generics(def);
        generics
            .iter()
            .map(|g| match g.kind {
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

    /// Substitute `Ty::Param(i)` / `Len::Param(i)` with `args[i]` (variables or concrete).
    pub(crate) fn subst(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        if args.is_empty() {
            return ty;
        }
        match self.ty(ty) {
            Ty::Param(i) => args.get(i as usize).copied().unwrap_or(ty),
            Ty::Array(e, len) => {
                let e2 = self.subst(e, args);
                let len2 = match len {
                    Len::Param(i) => match args.get(i as usize).map(|&t| self.ty(t)) {
                        Some(Ty::Var(v)) => Len::Var(v),
                        Some(Ty::ConstVal(n)) => Len::Const(n),
                        _ => len,
                    },
                    other => other,
                };
                self.a.types.intern(Ty::Array(e2, len2))
            }
            Ty::Tuple(ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Tuple(ns))
            }
            Ty::Named(d, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Named(d, ns))
            }
            Ty::Builtin(b, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.a.types.intern(Ty::Builtin(b, ns))
            }
            Ty::Fn(f) => {
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|(m, t)| (*m, self.subst(*t, args))).collect();
                let ret = self.subst(f.ret, args);
                self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }))
            }
            _ => ty,
        }
    }

    /// Record an instantiation made by the expression at `span`. Its arguments
    /// may be decided by a later statement (§4.5, §4.7; S-174): each one is an
    /// origin (E0406 when still open at the end) and carries the requirements of
    /// its parameter (the bounds and the implicit `Dup`, E0416, S-235).
    pub(super) fn finish_instance(&mut self, def: DefId, args: Vec<TyId>, span: Span) -> R<Option<InstId>> {
        if args.is_empty() {
            return Ok(None);
        }
        let generics = self.all_generics(def);
        // A method's generics start with its `impl`'s (sig.rs): those belong to the `impl`.
        let name = format!("`{}`", self.a.def(def).name);
        let (impl_count, impl_name) = match self.a.def(def).owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) && def != o => {
                let DefKind::Impl(i) = &self.a.def(o).kind else { unreachable!() };
                let head = match self.ty(i.self_ty) {
                    Ty::Named(d, _) => self.a.def(d).name.clone(),
                    _ => self.display(i.self_ty),
                };
                (self.a.def(o).generics().len(), format!("the `impl` of `{head}`"))
            }
            _ => (0, String::new()),
        };
        for (k, (g, &arg)) in generics.iter().zip(&args).enumerate() {
            let owner = if k < impl_count { impl_name.clone() } else { name.clone() };
            let what = match g.kind {
                GenericKind::Const(_) => format!("the const parameter `{}` of {owner}", g.name),
                _ => format!("the type parameter `{}` of {owner}", g.name),
            };
            self.defer(span, arg, DeferredKind::Origin { what });
            if let GenericKind::Type { bounds, dup, .. } = &g.kind {
                let required = |param: &str| Required::Param { param: param.to_string(), owner: owner.clone() };
                if *dup {
                    self.defer(span, arg, DeferredKind::Require { bound: Bound::Dup, what: required(&g.name) });
                }
                for &b in bounds {
                    self.defer(span, arg, DeferredKind::Require { bound: b, what: required(&g.name) });
                }
            }
        }
        let id = InstId(self.info.instances.len() as u32);
        self.info.instances.push(Instance { def, args, span });
        Ok(Some(id))
    }
}
