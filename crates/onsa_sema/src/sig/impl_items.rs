//! The items of an `impl Tr for Ty` (§6.3): the row of the `impl` of a trait
//! for a type, an `impl` that overlaps another or a derive (E0304), what it
//! lacks or has more than the trait (E0410, S-852) and the signatures of its
//! members (E0401, S-904). All read the form of the items of the trait,
//! [`TraitItem`], and no name of an item.

use super::*;
use crate::traits::{TRAIT_ITEMS, TraitItem};

/// The items of the trait `b`.
fn items_of(b: Bound) -> impl Iterator<Item = &'static TraitItem> {
    TRAIT_ITEMS.iter().filter(move |row| row.bound == b)
}

/// `d` with the note of the signatures of the items of `b` (§6.3).
fn with_items(d: Diagnostic, b: Bound) -> Diagnostic {
    items_of(b).fold(d, |d, row| d.with_rule(format!("`{}` has `{}`", b.name(), row.signature())))
}

impl<'p> Sema<'p> {
    /// The `impl`s `impls` of the traits, each with its trait and its type:
    /// the row of each, the first in the source, once the names of the
    /// members are read ([`Self::name_members`]), so that no stage waits for
    /// the signatures. What it does not write is held (§6.3, §18.1).
    pub(super) fn name_trait_impls(&mut self, mut impls: Vec<(DefId, Bound, DefId)>) {
        impls.sort_by_cached_key(|&(d, ..)| (self.file_key(self.a.def(d).module), self.a.def(d).span.start));
        for (imp, b, ty) in impls {
            self.a.modules.trait_impls.entry((b, ty)).or_insert(imp);
            if items_of(b).any(|row| !self.writes(imp, row)) {
                self.a.modules.held.insert((ty, b));
            }
        }
    }

    /// Whether the `impl` `imp` writes the item `row`.
    fn writes(&self, imp: DefId, row: &TraitItem) -> bool {
        let fns = self.a.def(imp).as_impl().map_or(&[][..], |i| &i.fns[..]);
        fns.iter().any(|&f| self.a.def(f).name == row.name)
    }

    /// The name of the trait in the heading of the `impl` `id`.
    fn trait_span(&self, id: DefId) -> Span {
        let tr = self.impl_decl(id).and_then(|(_, i)| i.trait_.as_ref());
        tr.map_or(self.a.def(id).span, |p| p.span)
    }

    /// The E0304 at the name of the trait of the `impl` `imp` of `b` for
    /// `ty`, of the overlap the names of the members do not catch (§6.3,
    /// §6.4): it is not the first of the trait, or does not write what a
    /// derive makes; a list not known makes nothing (§18.1, S-460). Whether it
    /// is one. Its name is no name where it is used (§18.1).
    fn trait_overlap(&mut self, imp: DefId, b: Bound, ty: DefId) -> bool {
        let table = self.a.modules.assoc.get(&ty);
        let members = || items_of(b).filter_map(|row| Some((row, *table?.get(row.name)?)));
        let made = |m: DefId| self.a.def(m).as_fn().is_some_and(|f| f.derived.is_some());
        let derive = members().find(|&(row, m)| !self.writes(imp, row) && made(m));
        let first = self.a.modules.trait_impls[&(b, ty)];
        let note = match (first != imp, derive) {
            (true, _) => (self.trait_span(first), "first defined here".to_string()),
            (false, Some((_, m))) => (self.a.def(m).name_span, self.first_defined(m)),
            (false, None) => return false,
        };
        let clashed: Vec<DefId> = members().map(|(_, m)| m).collect();
        self.a.modules.clashed_assoc.extend(clashed);
        let msg = format!("`{}` is implemented twice for this type", b.name());
        let d = Diagnostic::new(Stage::Names, Code::E0304, self.trait_span(imp), msg);
        self.report(imp, d.with_note(note.0, note.1));
        true
    }

    /// The `impl`s of the traits with no error in their headings, which are
    /// their units with no more (§18.1), once the types of the signatures are
    /// read: an overlap, and each member an item of the trait of its signature
    /// or one too many (in its unit), and with none too many every item
    /// written.
    pub(super) fn check_trait_impls(&mut self) {
        for id in self.a.new_defs() {
            let DefKind::Impl(ImplDef { of: Some(b), self_ty, generics, fns, consts }) = &self.a.def(id).kind else {
                continue;
            };
            let (b, self_ty, outer) = (*b, *self_ty, generics.len());
            let (fns, consts) = (fns.clone(), consts.clone());
            let ty = self.member_key(id).and_then(|key| key.0);
            if self.reported.contains_key(&id)
                || self.a.heading_failed(id)
                || ty.is_some_and(|ty| self.trait_overlap(id, b, ty))
            {
                continue;
            }
            let item = |this: &Self, f: DefId| items_of(b).find(|row| row.name == this.a.def(f).name);
            let extra: Vec<DefId> = fns.iter().copied().filter(|&f| item(self, f).is_none()).chain(consts).collect();
            for &f in &fns {
                if let Some(row) = item(self, f) {
                    self.member_signature(f, row, self_ty, outer);
                }
            }
            for &m in &extra {
                self.a.modules.clashed_assoc.insert(m);
                let (name, at) = (self.a.def(m).name.clone(), self.a.def(m).name_span);
                let msg = format!("`{name}` is no member of `{}`", b.name());
                self.report(m, with_items(Diagnostic::new(Stage::Types, Code::E0410, at, msg).with_found(name), b));
            }
            if let (true, Some(row)) = (extra.is_empty(), items_of(b).find(|row| !self.writes(id, row))) {
                let msg = format!("this `impl` of `{}` does not write `{}`", b.name(), row.name);
                self.report(id, with_items(Diagnostic::new(Stage::Types, Code::E0410, self.trait_span(id), msg), b));
            }
        }
    }

    /// The E0401 of the member `f` of an `impl` of the type `self_ty`, of
    /// `outer` generics, whose signature is not that of the item `row`: of
    /// its first difference in the order of §6.3, with the candidate that adds
    /// `rt` when that is the only one. Its uses are read as those of a
    /// member that clashes (§6.3, S-913). An error type is its own error.
    fn member_signature(&mut self, f: DefId, row: &TraitItem, self_ty: TyId, outer: usize) {
        if self.a.heading_failed(f) {
            return;
        }
        let params: Vec<TyId> = row.params.iter().map(|&(_, t)| self.item_ty(t, self_ty)).collect();
        let ret = self.item_ty(row.ret, self_ty);
        let (def, types) = (self.a.def(f), &self.a.types);
        let Some(fd) = def.as_fn() else { return };
        let same = |t: TyId, want: TyId| t == want || types.has_error(t) || types.has_error(want);
        let differs = [
            (fd.self_mode != row.recv, "its receiver"),
            (fd.params.len() != params.len(), "the number of its parameters"),
            (fd.params.iter().zip(&params).any(|(p, &t)| p.mode != Mode::Borrow || !same(p.ty, t)), "a parameter"),
            (!same(fd.ret, ret), "its result"),
            (!fd.effects.is_empty(), "its effect row"),
            (!fd.rt, "`rt`"),
            (fd.generics.len() != outer, "its type parameters"),
        ];
        let Some(&(_, first)) = differs.iter().find(|d| d.0) else { return };
        let rt_alone = !fd.rt && differs.iter().filter(|d| d.0).count() == 1;
        let (name, at, m) = (def.name.clone(), def.name_span, def.module);
        let msg = format!("`{name}` differs from the item of `{}` in {first}", row.bound.name());
        let mut d = with_items(Diagnostic::new(Stage::Types, Code::E0401, at, msg).with_found(name), row.bound);
        // `rt` goes right before the keyword before the name, whatever is
        // before that (`{fn default` has no blank).
        let before = self.module(m).map_or("", |m| m.text[..at.start as usize].trim_end());
        let word = before.trim_end_matches(|c: char| c.is_alphanumeric() || c == '_').len();
        if rt_alone && onsa_syntax::TokenKind::keyword(&before[word..]) == Some(onsa_syntax::TokenKind::KwFn) {
            d = d.with_fix(Fix::insert("add `rt`", at.file, word as u32, "rt "));
        }
        self.report(f, d);
        self.a.modules.clashed_assoc.insert(f);
    }
}
