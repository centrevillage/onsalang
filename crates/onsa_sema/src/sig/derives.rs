//! The traits at the head of a struct or an enum (§6.4): the derivable
//! ones, and the kind constraints (§4.6).

use super::*;

impl<'p> Sema<'p> {
    /// The traits at the head of a struct or an enum (§6.4): the closed list
    /// of the derivable ones ([`DERIVABLE`]); `Hash`, `Show` and `Ordinal` are
    /// E0200 in this version (S-13, W5-06), a kind constraint is `copy_bound`
    /// (§4.6) and any other name, or a path of more than one name (S-488),
    /// E0416. The diagnostics of the names stage go before the E0416 of the
    /// types stage (§18.1), whatever the order of the list. `None` when the
    /// list is not known (§18.1, S-460), or holds a name the names stage
    /// holds as an error.
    pub(super) fn lower_derives(&mut self, cx: &Cx<'p>, derives: &Derives) -> Option<Vec<Derive>> {
        let Derives::Listed(paths) = derives else { return None };
        let mut out = Vec::new();
        let mut underivable = Vec::new();
        for (k, p) in paths.iter().enumerate() {
            let [n] = p.segments.as_slice() else {
                underivable.push(p);
                continue;
            };
            match (DERIVABLE.iter().find(|(name, ..)| *name == n.name), kind_constraint(p)) {
                (Some(&(_, d, now)), _) => {
                    // std's `Option` and `Result` head as §4.1 writes them:
                    // no code is made of these, which read as bounds alone.
                    if !now && !self.a.modules.is_std(cx.m) {
                        self.unsupported(cx.def, n.span, Feature::Derive, &[&n.name]);
                    }
                    out.push(d);
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
        let (held, underivable): (Vec<&Path>, _) =
            underivable.into_iter().partition(|p| self.a.record_if_held(cx.def, cx.m, p));
        for span in underivable.into_iter().map(|p| p.span) {
            let name = src(cx, span);
            let list: Vec<String> = DERIVABLE.iter().map(|(name, ..)| format!("`{name}`")).collect();
            self.report(
                cx.def,
                Diagnostic::new(Stage::Types, Code::E0416, span, format!("`{name}` cannot be derived"))
                    .with_found(name)
                    .with_rule(foreign::DERIVE_RULE)
                    .with_rule(format!("the traits a type derives are {}", list.join(", "))),
            );
        }
        held.is_empty().then_some(out)
    }
}

/// The derivable traits (§6.4, S-34), in the order of the spec: the closed
/// list, and whether this version derives each (`false`: E0200, S-13,
/// S-145). The one list of their names.
const DERIVABLE: [(&str, Derive, bool); 8] = [
    ("PartialEq", Derive::PartialEq, true),
    ("Eq", Derive::Eq, true),
    ("PartialOrd", Derive::PartialOrd, true),
    ("Ord", Derive::Ord, true),
    ("Hash", Derive::Hash, false),
    ("Show", Derive::Show, false),
    ("Default", Derive::Default, true),
    ("Ordinal", Derive::Ordinal, false),
];

/// Whether `name` is the name of the derivable trait `d`.
pub(super) fn names(name: &str, d: Derive) -> bool {
    DERIVABLE.iter().any(|&(n, derive, _)| n == name && derive == d)
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
