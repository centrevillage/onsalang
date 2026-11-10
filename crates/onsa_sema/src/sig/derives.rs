//! The traits at the head of a struct or an enum (§6.4): the derivable
//! ones, what the form of the declaration and its fields require of them,
//! and the kind constraints (§4.6).

use onsa_syntax::ast::Variant;

use super::wellformed::{Slot, payloads};
use super::*;
use crate::body::bounds::Bounds;
use crate::stages::Failures;
use crate::traits::{DERIVABLE, ItemTy, TRAIT_ITEMS, TraitItem, derived};

impl<'p> Sema<'p> {
    /// The members the list `derives` of the struct or the enum `ty` makes
    /// (§6.2, §6.4, S-851), made with it in the names stage, so that the paths
    /// and the E0304 of `Sema::name_members` find them: the functions of an
    /// `impl` of no item, a member of `ty`, with no types until
    /// [`Self::fill_derived`] fills them. Seen as far as the type is (§15.1,
    /// S-905). A list not known makes none, and what it would make is held
    /// (§18.1, S-460).
    pub(crate) fn derived_defs(&mut self, ty: DefId, derives: &Derives) {
        let paths = match derives {
            Derives::Listed(paths) if list_known(paths) => paths,
            _ => return self.a.modules.held.extend(TRAIT_ITEMS.iter().map(|row| (ty, row.bound))),
        };
        let names = |p: &Path, b: Bound| matches!(p.segments.as_slice(), [n] if n.name == b.name());
        let in_list = |row: &'static TraitItem| Some((row, paths.iter().find(|p| names(p, row.bound))?.span));
        let rows: Vec<(&TraitItem, Span)> = TRAIT_ITEMS.iter().filter_map(in_list).collect();
        let Some((_, first)) = rows.first().copied() else { return };
        let (module, span) = (self.a.def(ty).module, self.a.def(ty).span);
        let (error, unit) = (self.a.types.error(), self.a.types.unit());
        let def = |name: &str, name_span, kind, owner| Def {
            name: name.to_string(),
            module,
            vis: Vis::Pub,
            span,
            name_span,
            kind,
            item: None,
            owner: Some(owner),
            export: None,
        };
        let imp = ImplDef { generics: Vec::new(), self_ty: error, of: None, fns: Vec::new(), consts: Vec::new() };
        let imp = self.add_def(def("<impl>", first, DefKind::Impl(imp), ty));
        let fns = rows.into_iter().map(|(row, at)| {
            let f = FnDef {
                generics: Vec::new(),
                self_mode: row.recv,
                params: Vec::new(),
                ret: unit,
                rt: true,
                effects: EffectSet::default(),
                body: None,
                target: false,
                flow_fn: None,
                derived: Some(row.made),
                fp_relaxed: false,
            };
            self.add_def(def(row.name, at, DefKind::Fn(f), imp))
        });
        let fns = fns.collect();
        if let DefKind::Impl(i) = &mut self.a.defs[imp.0 as usize].kind {
            i.fns = fns;
        }
    }

    /// The signatures of what [`Self::derived_defs`] made, of the traits of
    /// [`TRAIT_ITEMS`], once the generics of every type are lowered: the
    /// `impl` is of the type at its own parameters, each with the traits the
    /// `impl` is of, so that a use meets them (§6.4: "型引数が満たすときだけ").
    pub(super) fn fill_derived(&mut self) {
        for id in self.a.new_defs() {
            let def = self.a.def(id);
            let (DefKind::Impl(imp), Some(ty)) = (&def.kind, def.derived_impl_of()) else { continue };
            let fns = imp.fns.clone();
            let mut generics = self.a.def(ty).generics().to_vec();
            let made = |&f: &DefId| self.a.def(f).as_fn()?.derived;
            let items: Vec<&TraitItem> = fns.iter().filter_map(made).map(|m| m.item()).collect();
            for g in &mut generics {
                let GenericKind::Type { bounds, .. } = &mut g.kind else { continue };
                for row in &items {
                    if !bounds.contains(&row.bound) {
                        bounds.push(row.bound);
                    }
                }
            }
            let args = (0..generics.len() as u32).map(|k| self.a.types.intern(Ty::Param(k))).collect();
            let self_ty = self.a.types.intern(Ty::Named(ty, args));
            for (&f, row) in fns.iter().zip(items) {
                let params = row.params.iter().map(|&(name, t)| ParamSig {
                    name: name.to_string(),
                    mode: Mode::Borrow,
                    ty: self.item_ty(t, self_ty),
                    span: self.a.def(f).name_span,
                });
                let params = params.collect();
                let ret = self.item_ty(row.ret, self_ty);
                if let DefKind::Fn(d) = &mut self.a.defs[f.0 as usize].kind {
                    (d.generics, d.params, d.ret) = (generics.clone(), params, ret);
                }
            }
            if let DefKind::Impl(i) = &mut self.a.defs[id.0 as usize].kind {
                (i.generics, i.self_ty) = (generics, self_ty);
            }
        }
    }

    /// The type `t` of a [`TraitItem`] of the type `self_ty`. With no std
    /// (unit tests) there is no `Option`, and it is the error type.
    pub(super) fn item_ty(&mut self, t: ItemTy, self_ty: TyId) -> TyId {
        match (t, self.a.modules.lang.option()) {
            (ItemTy::SelfTy, _) => self_ty,
            (ItemTy::U32, _) => self.a.types.int(IntKind::U32),
            (ItemTy::OptionSelf, Some(d)) => self.a.types.intern(Ty::Named(d, vec![self_ty])),
            (ItemTy::OptionSelf, None) => self.a.types.error(),
        }
    }

    /// The traits a struct or an enum (of the variants `variants`) derives
    /// by its head (§6.4), with what they require (S-900): the closed list
    /// of the derivable ones ([`DERIVABLE`]); `Show` is E0200 in this version
    /// (S-13), a kind constraint is `copy_bound` (§4.6) and any other name,
    /// or a path of more than one name (S-488), E0416, as is a trait the form
    /// of the declaration does not take ([`unfit`]), whose trait stays in the
    /// list (§18.1). The diagnostics of the names stage go before the E0416
    /// of the types stage (§18.1), whatever the order of the list. `None`
    /// when the list is not known (§18.1, S-460): it holds a name out of the
    /// closed list (S-774), or one the names stage holds as an error.
    pub(super) fn lower_derives(
        &mut self,
        cx: &Cx<'p>,
        derives: &Derives,
        variants: Option<&[Variant]>,
    ) -> Option<Vec<Derive>> {
        let Derives::Listed(paths) = derives else { return None };
        let mut written = Vec::new();
        let mut underivable = Vec::new();
        for (k, p) in paths.iter().enumerate() {
            let [n] = p.segments.as_slice() else {
                underivable.push(p);
                continue;
            };
            match (DERIVABLE.iter().find(|(_, b, _)| b.name() == n.name), kind_constraint(p)) {
                (Some(&(_, b, now)), _) => {
                    // std's `Option` and `Result` head as §4.1 writes them:
                    // no code is made of these, which read as bounds alone.
                    if !now && !self.a.modules.is_std(cx.m) {
                        self.unsupported(cx.def, n.span, Feature::Derive, &[&n.name]);
                    }
                    if let Some((msg, rule)) = unfit(b, variants) {
                        let d = Diagnostic::new(Stage::Types, Code::E0416, n.span, msg);
                        self.report(cx.def, d.with_found(n.name.clone()).with_rule(rule));
                    }
                    written.push((b, n.span));
                }
                (None, Some(dup)) => {
                    let spans: Vec<Span> = paths.iter().map(|p| p.span).collect();
                    let d = foreign::report(
                        RowId::CopyBound,
                        cx.text,
                        p.span,
                        vec![drop_element(cx, &spans, k, &n.name, None)],
                    );
                    if let Some(at) = self.keep(cx.def, d) {
                        self.kind_heads.push((at, cx.def, dup));
                    }
                }
                (None, None) => underivable.push(p),
            }
        }
        // A name held as an error: the list is not known (§18.1).
        underivable.retain(|p| !self.a.record_if_held(cx.def, cx.m, p));
        for span in underivable.into_iter().map(|p| p.span) {
            let name = src(cx, span);
            let list: Vec<String> = DERIVABLE.iter().map(|(_, b, _)| format!("`{}`", b.name())).collect();
            self.report(
                cx.def,
                Diagnostic::new(Stage::Types, Code::E0416, span, format!("`{name}` cannot be derived"))
                    .with_found(name)
                    .with_rule(foreign::DERIVE_RULE)
                    .with_rule(format!("the traits a type derives are {}", list.join(", "))),
            );
        }
        // The same trait twice (§6.4, S-750): a trait read, with the other
        // E0416 of the types stage; a name not read is not compared.
        if let Some((before, k)) = onsa_diag::first_repeat(written.iter().map(|w| w.0)) {
            let what = format!("the trait `{}`", written[k].0.name());
            let d = onsa_diag::repeated(Stage::Types, Code::E0416, written[k].1, written[before].1, &what);
            self.report(cx.def, d.with_found(written[k].0.name()));
        }
        let written: Vec<Bound> = written.into_iter().map(|w| w.0).collect();
        list_known(paths).then(|| derived(&written))
    }

    /// Whether the fields of the declarations meet the traits they derive
    /// (§6.4, R-35), once the lists of all are lowered: a field may name a
    /// type declared after it. A unit with an error is not judged, which
    /// has its one diagnostic (§18.1).
    pub(super) fn derived_fields(&mut self, pkg: &Package) {
        let failures = Failures::of(pkg, self.a);
        for id in self.a.new_defs().filter(|&id| !failures.failed(id)) {
            self.fields_of_derives(id);
        }
    }

    /// The E0416 of the first field of `id`, in the order of the declaration,
    /// that does not meet a trait of its list ([`unmet_trait`]).
    fn fields_of_derives(&mut self, id: DefId) {
        let def = self.a.def(id);
        let (Some(derives), Some(item)) = (def.derives().filter(|ds| !ds.is_empty()), def.item) else { return };
        // A type parameter meets what is derived: the uses judge it (§6.4, R-355).
        let mut params = def.generics().to_vec();
        for g in &mut params {
            if let GenericKind::Type { unknown, .. } = &mut g.kind {
                *unknown = true;
            }
        }
        let Some(cx) = self.cx_for(id, params, None) else { return };
        let under = Bounds { a: self.a, generics: &cx.generics };
        let roots = payloads(decls::item_kind(&cx.ast.item(item).kind), &def.kind);
        // A field with a default does not need the `Default` of its type (§6.4).
        let declared: Vec<Derive> = derives.iter().copied().filter(|&d| d != Derive::Default).collect();
        let asked = |slot| if has_default(&def.kind, slot) { &declared[..] } else { derives };
        let found = roots.iter().find_map(|&(t, ty, slot)| Some((t, ty, slot, unmet_trait(&under, ty, asked(slot))?)));
        let Some((t, ty, slot, b)) = found else { return };
        let span = cx.ast.ty(t).span;
        let (owner, part) = (self.a.shown_name(id), part_name(&self.a.def(id).kind, slot));
        let msg = format!(
            "`{owner}` implements `{}` by its derive, so {part} must too; `{}` does not (§6.4)",
            b.name(),
            self.shown(&cx, ty),
        );
        self.report(id, Diagnostic::new(Stage::Types, Code::E0416, span, msg).with_found(src(&cx, span)));
    }
}

/// Whether the list `paths` is known (§18.1, S-774): all its names are in the
/// closed list of §6.4 or kind constraints, by their spelling alone, so that
/// the names stage asks it too.
fn list_known(paths: &[Path]) -> bool {
    let in_list = |p: &Path| matches!(p.segments.as_slice(), [n] if DERIVABLE.iter().any(|row| row.1.name() == n.name));
    paths.iter().all(|p| in_list(p) || kind_constraint(p).is_some())
}

/// The first trait of the list `derives`, in the order of §6.4, that a field
/// of the type `ty` does not meet.
fn unmet_trait(under: &Bounds<'_>, ty: TyId, derives: &[Derive]) -> Option<Bound> {
    DERIVABLE.iter().filter(|row| derives.contains(&row.0)).map(|row| row.1).find(|&b| !under.satisfies(ty, b))
}

/// Whether `slot` is a field of a struct with a default of its own (§4.4).
fn has_default(def: &DefKind, slot: Slot) -> bool {
    let (DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }), Slot::Field(k)) = (def, slot) else {
        return false;
    };
    fs[k].default.is_some()
}

/// What a message calls the field or the payload at `slot` of `def`.
fn part_name(def: &DefKind, slot: Slot) -> String {
    match (def, slot) {
        (DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }), Slot::Field(k)) => {
            format!("its field `{}`", fs[k].name)
        }
        (DefKind::Enum(e), Slot::Variant(n, _)) => format!("the payload of its variant `{}`", e.variants[n].name),
        _ => onsa_diag::internal::bug(None, "a derive of no field"),
    }
}

/// Why the form of a struct, or of an enum of `variants`, does not take the
/// trait `b` of its list (§6.4): the message and the rule of its E0416.
fn unfit(b: Bound, variants: Option<&[Variant]>) -> Option<(&'static str, &'static str)> {
    const NO_DEFAULT: (&str, &str) = (
        "an enum cannot derive `Default`",
        "which variant is the default is not left to the order of the declaration: write `impl Default for Mode { rt fn default() -> Mode { Mode.Off } }` (§6.4)",
    );
    const NO_ORDINAL: (&str, &str) = (
        "only an enum can derive `Ordinal`, with no payload in its variants",
        "`Ordinal` numbers the variants of an enum that hold nothing (§6.4)",
    );
    match (b, variants) {
        (Bound::Default, Some(_)) => Some(NO_DEFAULT),
        (Bound::Ordinal, Some(vs)) if vs.iter().all(|v| v.fields.is_empty()) => None,
        (Bound::Ordinal, _) => Some(NO_ORDINAL),
        _ => None,
    }
}

/// The candidate that takes the element `k` of a `+` list of the spans
/// `list` out (a trait of a head, §4.6, `copy_bound`; a bound of a type
/// parameter, §4.5, `implicit_bound`), titled by its name `shown`: with the
/// `+` before it, or after it when it is the first, or with the `:` when it
/// is the only one, found after `head`, the end of the name before the `:`,
/// when known. A comment between the element and the symbol goes; one on
/// the other side of the symbol stays (§18.1, R-384).
pub(super) fn drop_element(cx: &Cx<'_>, list: &[Span], k: usize, shown: &str, head: Option<u32>) -> Fix {
    let p = list[k];
    let (text, file) = (cx.text, p.file);
    // The symbol `kind` in the text from `from` to `to` (blanks, comments and
    // it): from the blanks before it on its line to the blanks after it there.
    let symbol = |from: u32, to: u32, kind: onsa_syntax::TokenKind| {
        let t = *onsa_syntax::lex(file, &text[from as usize..to as usize]).tokens.iter().find(|t| t.kind == kind)?;
        let (s, e) = ((from + t.span.start) as usize, (from + t.span.end) as usize);
        let after = text.len() - text[e..].trim_start_matches([' ', '\t']).len();
        Some((text[..s].trim_end_matches([' ', '\t']).len() as u32, after as u32))
    };
    use onsa_syntax::TokenKind::{Colon, Plus};
    let span = if k > 0 {
        let start = symbol(list[k - 1].end, p.start, Plus).map_or(list[k - 1].end, |s| s.0);
        Span::new(file, start, p.end)
    } else if list.len() > 1 {
        Span::new(file, p.start, symbol(p.end, list[1].start, Plus).map_or(list[1].start, |s| s.1))
    } else {
        // The `:` before the only trait (blanks may be between them).
        let before = || text[..p.start as usize].trim_end().strip_suffix(':').map_or(p.start, |b| b.len() as u32);
        let colon = head.map_or_else(before, |h| symbol(h, p.start, Colon).map_or(h, |s| s.0));
        Span::new(file, colon, p.end)
    };
    Fix::delete(format!("remove `{shown}`"), span)
}

/// The kind constraint `p` names (§4.6), by its spelling: whether it is
/// `Dup` (else `Copy`); none for another name or a path of more names. The
/// one judgment of `copy_bound` and `copy_impl` (`impl Copy for X` is no
/// trait implementation, S-140).
pub(crate) fn kind_constraint(p: &Path) -> Option<bool> {
    let [n] = p.segments.as_slice() else { return None };
    foreign::KIND_CONSTRAINTS.contains(&n.name.as_str()).then(|| n.name == foreign::DUP)
}
