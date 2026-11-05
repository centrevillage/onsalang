//! The traits at the head of a struct or an enum (§6.4): the derivable
//! ones, what the form of the declaration and its fields require of them,
//! and the kind constraints (§4.6).

use onsa_syntax::ast::Variant;

use super::wellformed::{Slot, payloads};
use super::*;
use crate::body::bounds::Bounds;
use crate::stages::Failures;
use crate::traits::{DERIVABLE, derived};

impl<'p> Sema<'p> {
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
                    written.push(b);
                }
                (None, Some(dup)) => {
                    let d = foreign::report(RowId::CopyBound, cx.text, p.span, vec![drop_derive(cx, paths, k)]);
                    if let Some(at) = self.keep(cx.def, d) {
                        self.kind_heads.push((at, cx.def, dup));
                    }
                }
                (None, None) => underivable.push(p),
            }
        }
        // A name held as an error: the list is not known (§18.1).
        let (held, underivable): (Vec<&Path>, Vec<&Path>) =
            underivable.into_iter().partition(|p| self.a.record_if_held(cx.def, cx.m, p));
        let known = held.is_empty() && underivable.is_empty();
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
        known.then(|| derived(&written))
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
        let found = roots.iter().find_map(|&(t, ty, slot)| Some((t, ty, slot, unmet_trait(&under, ty, derives)?)));
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

/// The first trait of the list `derives`, in the order of §6.4, that a field
/// of the type `ty` does not meet.
fn unmet_trait(under: &Bounds<'_>, ty: TyId, derives: &[Derive]) -> Option<Bound> {
    DERIVABLE.iter().filter(|row| derives.contains(&row.0)).map(|row| row.1).find(|&b| !under.satisfies(ty, b))
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

/// The candidate that takes the trait `k` of the head `paths` out (§4.6,
/// `copy_bound`): with the `+` before it, or after it when it is the first,
/// or with the `:` when it is the only one.
fn drop_derive(cx: &Cx<'_>, paths: &[onsa_syntax::ast::Path], k: usize) -> Fix {
    let p = paths[k].span;
    let span = if k > 0 {
        Span::new(p.file, paths[k - 1].span.end, p.end)
    } else if paths.len() > 1 {
        Span::new(p.file, p.start, paths[1].span.start)
    } else {
        // The `:` before the only trait (blanks may be between them).
        let before = cx.text[..p.start as usize].trim_end();
        let colon = before.strip_suffix(':').map_or(p.start, |b| b.len() as u32);
        Span::new(p.file, colon, p.end)
    };
    Fix::delete(format!("remove `{}`", &cx.text[p.start as usize..p.end as usize]), span)
}

/// The kind constraint `p` names (§4.6), by its spelling: whether it is
/// `Dup` (else `Copy`); none for another name or a path of more names. The
/// one judgment of `copy_bound` and `copy_impl` (`impl Copy for X` is no
/// trait implementation, S-140).
pub(crate) fn kind_constraint(p: &Path) -> Option<bool> {
    let [n] = p.segments.as_slice() else { return None };
    foreign::KIND_CONSTRAINTS.contains(&n.name.as_str()).then(|| n.name == foreign::DUP)
}
