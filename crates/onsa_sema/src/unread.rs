//! What the check did not read, and the defs whose check depends on it: the
//! check of those keeps quiet where it cannot know (§18.1: a use of what a
//! syntax error cut gets no diagnostic, S-260; the derive list that was not
//! read derives every trait, S-460; a type that failed to resolve,
//! [`Ty::Error`], suppresses the errors after it; a name the names stage
//! holds as an error, read by its spelling, gets no diagnostic, S-462,
//! [`Analysis::read_held`]). A fix of the cause can show an error they held
//! back, so the contract of the fix candidates of the
//! tests (`onsa_tests::fix_contract`, X-3) does not count it against the
//! candidate; the driver turns the defs into units
//! (`onsa_driver::Analyzed::unread_units`).

use std::collections::{HashMap, HashSet};

use onsa_diag::{FileId, Span};

use crate::def::{DefKind, Fields};
use crate::{Analysis, BodyInfo, DefId, Target, Ty, TyId};

impl Analysis {
    /// The spans of the defs declared in `files` whose check depends on what
    /// the check did not read: a def the unread reaches through its declared
    /// types ([`Analysis::reached`]), and a def whose body has an expression
    /// or a local of such a type, refers to such a def, or was not checked to
    /// its end (`complete == false`).
    pub fn unread_users(&self, files: &[FileId]) -> Vec<Span> {
        let reached = self.reached();
        let mut memo = self.held_alias_types();
        let mut out = Vec::new();
        for (i, def) in self.defs.iter().enumerate().filter(|(_, d)| files.contains(&d.span.file)) {
            let id = DefId(i as u32);
            let body = self.bodies.get(&id).map(|b| (b, b.complete));
            let body = body.or_else(|| self.flows.get(&id).map(|f| (&f.body, f.complete && f.body.complete)));
            let uses = reached.contains(&id)
                || body.is_some_and(|(b, complete)| !complete || self.body_reaches(b, &reached, &mut memo));
            if uses {
                out.push(def.span);
            }
        }
        out
    }

    /// The defs the unread reaches: those read in part (S-260), whose
    /// derive list is not known (S-460), that read a name held as an error
    /// (whether their check was held or not, [`Analysis::read_held`]) or rt
    /// functions whose body the check did not finish (its calls make no edges
    /// of the rt recursion), and those whose declared types hold
    /// [`Ty::Error`], the type of an alias that read a held name
    /// ([`Self::held_alias_types`]) or a def it reaches. A fixed point: each
    /// round adds a def or ends, so there are at most as many rounds as defs.
    fn reached(&self) -> HashSet<DefId> {
        let mut set: HashSet<DefId> = (0..self.defs.len() as u32)
            .map(DefId)
            .filter(|&id| {
                let derives = match &self.def(id).kind {
                    DefKind::Struct(s) => s.derives.is_none(),
                    DefKind::Enum(e) => e.derives.is_none(),
                    _ => false,
                };
                // An rt function whose written body the check did not finish:
                // its calls are no edges of the rt recursion (`rt::check_all`),
                // so an E0903 through it was held back (X-3/U1c/b, F1).
                let rt_unread = matches!(&self.def(id).kind, DefKind::Fn(f) if f.rt && f.body.is_some())
                    && !self.bodies.get(&id).is_some_and(|b| b.complete);
                derives || rt_unread || self.partly_read(id) || self.read_held.contains(&id)
            })
            .collect();
        loop {
            let mut memo = self.held_alias_types();
            let more: Vec<DefId> = (0..self.defs.len() as u32)
                .map(DefId)
                .filter(|id| !set.contains(id))
                .filter(|&id| self.declared_types(id).iter().any(|&t| self.ty_reaches(t, &set, &mut memo)))
                .collect();
            if more.is_empty() {
                return set;
            }
            set.extend(more);
        }
    }

    /// The types a def declares: of the parameters and the result, the
    /// fields, the variants, an alias, a constant, the type of an `impl`,
    /// the inputs and the output of a flow.
    fn declared_types(&self, id: DefId) -> Vec<TyId> {
        match &self.def(id).kind {
            DefKind::Fn(f) => f.params.iter().map(|p| p.ty).chain([f.ret]).collect(),
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => fs.iter().map(|f| f.ty).collect(),
                Fields::Opaque => Vec::new(),
            },
            DefKind::Enum(e) => e.variants.iter().flat_map(|v| v.fields.iter().copied()).collect(),
            DefKind::Alias(t) => vec![*t],
            DefKind::Const(c) => vec![c.ty],
            DefKind::Impl(i) => vec![i.self_ty],
            DefKind::Flow(f) => f.inputs.iter().map(|i| i.ty).chain([f.out]).collect(),
            DefKind::Test { .. } | DefKind::Unsupported => Vec::new(),
        }
    }

    /// The start of the memo of [`Self::ty_reaches`]: the type of each alias
    /// of [`Analysis::read_held`] reaches. An alias is expanded where it is
    /// written, so no def of its users names it; they write its type. The
    /// same type written without the alias reaches too (the contract of the
    /// fix candidates only gets a little looser there).
    fn held_alias_types(&self) -> HashMap<TyId, bool> {
        let alias = |d: &DefId| match &self.def(*d).kind {
            DefKind::Alias(t) => Some((*t, true)),
            _ => None,
        };
        self.read_held.iter().filter_map(alias).collect()
    }

    /// `ty` holds [`Ty::Error`] or a def of `set` (through the arguments,
    /// the elements, the parameters and the result of a function type).
    /// The interned types form no cycle, and `memo` visits each once.
    fn ty_reaches(&self, ty: TyId, set: &HashSet<DefId>, memo: &mut HashMap<TyId, bool>) -> bool {
        if let Some(&r) = memo.get(&ty) {
            return r;
        }
        let r = match self.types.get(ty) {
            Ty::Error => true,
            Ty::Named(d, args) => set.contains(d) || args.iter().any(|&a| self.ty_reaches(a, set, memo)),
            Ty::Builtin(_, args) | Ty::Tuple(args) => args.iter().any(|&a| self.ty_reaches(a, set, memo)),
            Ty::Array(t, _) => self.ty_reaches(*t, set, memo),
            Ty::Fn(f) => f.params.iter().map(|p| p.1).chain([f.ret]).any(|t| self.ty_reaches(t, set, memo)),
            _ => false,
        };
        memo.insert(ty, r);
        r
    }

    /// A body has an expression or a local of a type that reaches `set`, or
    /// refers to a def of it.
    fn body_reaches(&self, b: &BodyInfo, set: &HashSet<DefId>, memo: &mut HashMap<TyId, bool>) -> bool {
        b.expr_types.values().chain(b.locals.iter().map(|l| &l.ty)).any(|&t| self.ty_reaches(t, set, memo))
            || b.targets.values().any(|t| match t {
                Target::Fn { def, .. }
                | Target::Method { def, .. }
                | Target::Variant { def, .. }
                | Target::Const(def) => set.contains(def),
                _ => false,
            })
    }
}
