//! The list of the bounds of a type parameter (§4.5): `?` on a bound that
//! is not `Dup` (S-711), the same bound twice and `?Dup` with a bound that
//! requires `Dup` (S-747). Each an E0416 of the types stage, after the names
//! of the list are read (an error of a name, or a trait this version does
//! not take as a bound, is not compared).

use super::*;
use crate::body::bounds::implies;

/// The rule a `?` keeps to (§4.5).
const RELAXED_RULE: &str =
    "`?` lifts the implicit `Dup` of a type parameter, and only it: to take Affine types too, write `?Dup`";

/// The E0416 of `?` on the bound named `n`, not `Dup` (S-711): it has
/// nothing to lift. No candidate: `?Copy` may mean `?Dup` or no bound.
pub(super) fn relaxed(n: &Ident) -> Diagnostic {
    let msg = format!("`?{}` lifts nothing: only `Dup` is implicit on a type parameter (§4.5)", n.name);
    Diagnostic::new(Stage::Types, Code::E0416, n.span, msg).with_found(n.name.clone()).with_rule(RELAXED_RULE)
}

/// How a bound is written: `?Dup` or the name.
fn shown(b: (Bound, bool)) -> String {
    format!("{}{}", if b.1 { "?" } else { "" }, b.0.name())
}

impl<'p> Sema<'p> {
    /// The E0416 of the list `list` of `def` (the bounds read, with their `?`
    /// and the span of the name), at its first element the same as one
    /// before it or in a contradiction with one (`?Dup` with a bound that
    /// requires `Dup`), that one in a note (S-747). A bound implied by
    /// another (`Float + Num`) is no error. Whether the list has a
    /// contradiction, reported or after the one reported (A5): then the users
    /// of the parameter read its bounds as unknown (§18.1).
    pub(super) fn bound_list(&mut self, def: DefId, list: &[(Bound, bool, Span)]) -> bool {
        let clash = |a: (Bound, bool), b: (Bound, bool)| match (a.1, b.1) {
            (true, false) => implies(b.0, Bound::Dup),
            (false, true) => implies(a.0, Bound::Dup),
            _ => false,
        };
        let any = list.iter().any(|x| list.iter().any(|y| clash((x.0, x.1), (y.0, y.1))));
        for (k, &(b, r, at)) in list.iter().enumerate() {
            let before = list[..k].iter().find(|x| (x.0, x.1) == (b, r) || clash((x.0, x.1), (b, r)));
            let Some(&(pb, pr, pat)) = before else { continue };
            let (this, prev) = (shown((b, r)), shown((pb, pr)));
            let contradiction = (pb, pr) != (b, r);
            let d = if contradiction {
                let msg = format!(
                    "`{this}` and `{prev}` contradict: `?Dup` lifts the implicit `Dup`, and the other requires it (§4.5)"
                );
                Diagnostic::new(Stage::Types, Code::E0416, at, msg)
                    .with_note(pat, format!("`{prev}` is written here"))
                    .with_rule(
                        "to take Affine types too, take out the bounds that require `Dup`; if Copy types are enough, \
                         take out `?Dup`",
                    )
            } else {
                Diagnostic::new(Stage::Types, Code::E0416, at, format!("the bound `{this}` is written twice (§4.5)"))
                    .with_note(pat, format!("`{prev}` is first written here"))
            };
            self.report(def, d.with_found(b.name()));
            return any;
        }
        false
    }
}
