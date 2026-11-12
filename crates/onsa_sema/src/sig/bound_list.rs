//! The list of the bounds of a type parameter (§4.5): `?` on a bound that
//! is neither `Dup` nor `Escape` (S-711), the same bound twice, `?Dup` with
//! a bound that requires `Dup` and `?Escape` with `Escape` (S-747, S-926).
//! Each an E0416 of the types stage, after the names of the list are read
//! (an error of a name, or a trait this version does not take as a bound,
//! is not compared). In a list with none of these, `Dup` or `Escape` with no
//! `?` is the E0020 of the implicit requirement written (S-751).

use onsa_syntax::ast::Bound as Written;

use super::derives::drop_element;
use super::*;
use crate::traits::implies;

/// The rule a `?` keeps to (§4.5).
const RELAXED_RULE: &str = "`?` lifts an implicit requirement of a type parameter, `Dup` or `Escape`, and only those: to take Affine types too, write `?Dup`";

/// The E0416 of `?` on the bound named `n`, neither `Dup` nor `Escape`
/// (S-711, S-862): it has nothing to lift. No candidate: `?Copy` may mean
/// `?Dup` or no bound.
pub(super) fn relaxed(n: &Ident) -> Diagnostic {
    let msg = format!("`?{}` lifts nothing: only `Dup` and `Escape` are implicit on a type parameter (§4.5)", n.name);
    Diagnostic::new(Stage::Types, Code::E0416, n.span, msg).with_found(n.name.clone()).with_rule(RELAXED_RULE)
}

/// The span of the element `b` of a list, with its `?`.
fn element_span(cx: &Cx<'_>, b: &Written) -> Span {
    let p = b.path.span;
    let before = cx.text[..p.start as usize].trim_end();
    match before.strip_suffix('?').filter(|_| b.relaxed) {
        Some(head) => Span::new(p.file, head.len() as u32, p.end),
        None => p,
    }
}

/// How a bound is written: `?Dup` or the name.
fn shown(b: (Bound, bool)) -> String {
    format!("{}{}", if b.1 { "?" } else { "" }, b.0.name())
}

impl<'p> Sema<'p> {
    /// The E0416 of the list `list` of `def` (the bounds read, with their `?`
    /// and the span of the name), at its first element the same as one
    /// before it or in a contradiction with one (`?Dup` with a bound that
    /// requires `Dup`, `?Escape` with `Escape`), that one in a note (S-747,
    /// S-926). A bound implied by another (`Float + Num`) is no error. Whether
    /// the list has a contradiction, reported or after the one reported (A5):
    /// then the users of the parameter read its bounds as unknown (§18.1).
    /// A list with none of these has the E0020 of [`Self::implicit_bound`],
    /// but one with an error of its own (`unknown`). `head` is the end of
    /// the parameter's name.
    pub(super) fn bound_list(
        &mut self,
        cx: &Cx<'p>,
        (head, bounds): (u32, &[Written]),
        list: &[(Bound, bool, Span)],
        unknown: bool,
    ) -> bool {
        let clash = |a: (Bound, bool), b: (Bound, bool)| match (a.1, b.1) {
            (true, false) => implies(b.0, a.0),
            (false, true) => implies(a.0, b.0),
            _ => false,
        };
        let any = list.iter().any(|x| list.iter().any(|y| clash((x.0, x.1), (y.0, y.1))));
        let repeat = onsa_diag::first_repeat(list.iter().map(|x| (x.0, x.1)));
        // A contradiction after the first repeat is not the first of the two: it is not looked for.
        let upto = repeat.map_or(list.len(), |(_, k)| k + 1);
        let contradiction = list[..upto]
            .iter()
            .enumerate()
            .find_map(|(k, x)| Some((list[..k].iter().position(|y| clash((y.0, y.1), (x.0, x.1)))?, k)));
        // The first element of either, with the first one before it.
        let first = repeat.into_iter().chain(contradiction).min_by_key(|&(before, k)| (k, before));
        if let Some((before, k)) = first {
            let ((b, r, at), (pb, pr, pat)) = (list[k], list[before]);
            let (this, prev) = (shown((b, r)), shown((pb, pr)));
            let d = if (pb, pr) != (b, r) {
                let lifted = if r { b } else { pb }.name();
                let msg = format!(
                    "`{this}` and `{prev}` contradict: `?{lifted}` lifts the implicit `{lifted}`, and the other requires it (§4.5)"
                );
                Diagnostic::new(Stage::Types, Code::E0416, at, msg)
                    .with_note(pat, format!("`{prev}` is written here"))
                    .with_rule(if b == Bound::Escape || pb == Bound::Escape {
                        "to take second-class types too, take out `Escape`; if first-class types are enough, take out `?Escape`"
                    } else {
                        "to take Affine types too, take out the bounds that require `Dup`; if Copy types are enough, \
                         take out `?Dup`"
                    })
            } else {
                onsa_diag::repeated(Stage::Types, Code::E0416, at, pat, &format!("the bound `{this}`"))
            };
            self.report(cx.def, d.with_found(b.name()));
            return any;
        }
        if !unknown {
            self.implicit_bound(cx, head, bounds, list);
        }
        false
    }

    /// The E0020 of the first `Dup` or `Escape` with no `?` of the list
    /// `list` read of `bounds` (§4.5, S-751): the requirement every type
    /// parameter has, written. The candidate takes the element out.
    fn implicit_bound(&mut self, cx: &Cx<'p>, head: u32, bounds: &[Written], list: &[(Bound, bool, Span)]) {
        let Some(&(_, _, at)) = list.iter().find(|x| !x.1 && matches!(x.0, Bound::Dup | Bound::Escape)) else { return };
        let Some(k) = bounds.iter().position(|b| b.path.segments.last().unwrap().span == at) else { return };
        self.drop_bound(cx, RowId::ImplicitBound, head, bounds, k);
    }

    /// The E0020 of the Rust `Sized` or `?Sized`, the bound `b` of `bounds`
    /// (§4.5, S-746): every type has a size. The candidate takes it out.
    pub(super) fn sized_bound(&mut self, cx: &Cx<'p>, head: u32, bounds: &[Written], b: &Written) {
        let k = bounds.iter().position(|x| std::ptr::eq(x, b)).unwrap();
        self.drop_bound(cx, RowId::SizedBound, head, bounds, k);
    }

    /// The diagnostic of `row` at the element `k` of `bounds`, the list of
    /// the parameter whose name ends at `head`, which the candidate takes out.
    fn drop_bound(&mut self, cx: &Cx<'p>, row: RowId, head: u32, bounds: &[Written], k: usize) {
        let spans: Vec<Span> = bounds.iter().map(|b| element_span(cx, b)).collect();
        let shown = format!("{}{}", if bounds[k].relaxed { "?" } else { "" }, bounds[k].path.dotted());
        let fix = drop_element(cx, &spans, k, &shown, Some(head));
        self.report(cx.def, foreign::report(row, cx.text, spans[k], vec![fix]));
    }
}
