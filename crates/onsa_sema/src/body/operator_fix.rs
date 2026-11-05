//! The candidates and the note of the E0401 of an operator (§6.3, S-141,
//! S-84): a generic function narrows the bound of the type parameter to the
//! trait that has the operator, in the heading that declares it.
//!
//! Safety (§18.1): `T` keeps all it had (the bounds replaced are the ones
//! the new one contains) and gains the operator, so no error is made in the
//! unit; a caller is another unit, untouched. Each candidate adds to the
//! traits `T` implies, of a closed table, so applying them stops.

use onsa_diag::Edit;
use onsa_syntax::ast::{self, GenericParam, Ident, ItemKind};

use super::*;
use crate::traits::{implies, narrowable, narrowed_bound};

/// The note of the negation of an unsigned integer type (§3.4, §6.3).
pub(crate) const UNSIGNED_NEGATION: &str = "the two's complement negation of an unsigned integer is `0 -% u` (§3.4)";

impl<'a> Checker<'a> {
    /// The E0401 `d` of the operator `op` on the type `t`, with the candidate
    /// of a type parameter and the note of an unsigned negation: the one
    /// way of an operator judged at it or later (§4.7).
    pub(crate) fn with_bound_fix(&mut self, d: Diagnostic, op: OpNeed, t: TyId) -> Diagnostic {
        let t = self.infer.resolve(&mut self.a.types, t);
        let d = match self.bound_fix(op, t) {
            Some(fix) => d.with_fix(fix),
            None => d,
        };
        if op != OpNeed::Neg || !self.satisfies(t, Bound::Unsigned) {
            return d;
        }
        d.with_rule(match self.ty(t) {
            Ty::Param(_) => {
                format!(
                    "the two's complement negation of an unsigned integer is `{}.ZERO -% x` (§6.6)",
                    self.display(t)
                )
            }
            _ => UNSIGNED_NEGATION.to_string(),
        })
    }

    /// The candidate that narrows the bounds of the type parameter `t` to
    /// the trait of `op`: none when no type would meet the list (§6.3), when
    /// the trait requires the `Dup` that `?Dup` lifts (§4.5, an E0416), or
    /// when a bound written is not among the bounds read (`Escape`).
    fn bound_fix(&self, op: OpNeed, t: TyId) -> Option<Fix> {
        let Ty::Param(i) = self.ty(t) else { return None };
        let g = self.generics.get(i as usize)?;
        let GenericKind::Type { bounds, dup, .. } = &g.kind else { return None };
        let want = narrowed_bound(op);
        if (!dup && implies(want, Bound::Dup)) || !narrowable(bounds, want) {
            return None;
        }
        let (name, list) = self.declaration(g)?;
        let read: Vec<usize> = (0..list.len()).filter(|&k| !list[k].relaxed).collect();
        if read.len() != bounds.len() {
            return None;
        }
        let (file, name) = (name.span.file, want.name());
        let at = |k: usize| list[k].path.span;
        let contained = read.iter().zip(bounds).filter(|&(_, &b)| implies(want, b)).map(|(&k, _)| k);
        let contained: Vec<usize> = contained.collect();
        let edits = match (contained.split_first(), list.last()) {
            (None, None) => vec![Edit::insert(file, g.span.end, format!(": {name}"))],
            (None, Some(b)) => vec![Edit::insert(file, b.path.span.end, format!(" + {name}"))],
            // The first in its place; the others go with the ` + ` before them.
            (Some((&first, rest)), _) => std::iter::once(Edit::replace(at(first), name))
                .chain(rest.iter().map(|&k| Edit::delete(Span::new(file, at(k - 1).end, at(k).end))))
                .collect(),
        };
        Some(Fix::new(format!("narrow the bound of `{}` to `{name}`", g.name), edits))
    }

    /// The declaration of the type parameter `g`, of the function or of the
    /// `impl` around it: its name and the bounds written.
    fn declaration(&self, g: &GenericDef) -> Option<(&'a Ident, &'a [ast::Bound])> {
        let def = self.a.def(self.def);
        let items = [def.item, def.owner.and_then(|o| self.a.def(o).item)];
        items.into_iter().flatten().find_map(|item| {
            let generics = match crate::sig::item_kind(&self.ast.item(item).kind) {
                ItemKind::Fn(f) => &f.generics,
                ItemKind::Impl(i) => &i.generics,
                _ => return None,
            };
            generics.iter().find_map(|p| match p {
                GenericParam::Type { name, bounds } if name.span == g.span => Some((name, &bounds[..])),
                _ => None,
            })
        })
    }
}
