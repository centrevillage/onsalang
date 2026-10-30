//! The writes (W4-07 memo 2.4; §5.1, §5.2, §7): the target of an
//! assignment, an `inout` argument and the receiver of an `inout self`
//! method. A place that cannot be changed is E0701 (with R-161's candidate
//! when `var` is the one fix); a write to a place that can changes the state
//! (§7, S-789). An erroneous write changes nothing (review 2).

use std::collections::BTreeMap;

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{ExprId, PatKind, StmtKind};

use super::check::Walker;
use super::flow::Run;
use super::place::{Place, place_of};
use super::state::Status;
use super::walk::Pos;
use crate::Kind;
use crate::binding::{Bind, Head, HeadRow};
use crate::body::{LocalId, LocalKind};
use crate::names::body::{BindingKind, Origin};

/// What writes a place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum How {
    Assign,
    Inout,
    /// The receiver of an `inout self` method (`x.fill!(0.0)`).
    Bang,
}

impl How {
    /// The words of an E0701 of the write.
    pub(super) fn verb(self) -> &'static str {
        match self {
            How::Assign => "cannot assign to this place",
            How::Inout => "cannot pass as `inout` this place",
            How::Bang => "cannot call an `inout self` method on this place",
        }
    }
}

impl Walker<'_> {
    /// The write `how` of `target`, walked after what is evaluated before
    /// it (§3.5). A whole local assigned is live again, and not read; any
    /// other write reads its place first (an E0704 of a moved or stale root,
    /// S-789). A value captured is not written (R-25). An `inout` argument
    /// and a receiver change their place after the call (§7, S-796). W4-09
    /// and W4-10 put the E0715 of a place a borrowed `for` or a guard holds
    /// here, first.
    pub(super) fn write_place(&mut self, r: &mut Run, target: ExprId, how: How) {
        let at = self.ast.expr(target).span;
        let Some(place) = place_of(self.ast, self.names, target) else {
            let message = match how {
                How::Assign => bug(Some(at), "an assignment to no place (the types stage's E0415)"),
                How::Inout => {
                    "an `inout` argument must be a place (a `var`, an `inout` parameter, or a field / element of one), not a temporary (§5.2)"
                }
                How::Bang => "the receiver of an `inout self` method must be a place, not a temporary (§5.2)",
            };
            self.report(Diagnostic::new(Stage::Modes, Code::E0701, at, message));
            return self.expr(r, target, Pos::Read);
        };
        let (l, whole) = (place.root, how == How::Assign && place.proj.is_empty());
        let live = self.live(r, &place);
        if !whole {
            self.expr(r, target, Pos::Read);
        }
        if self.captured(l) {
            return self.captured_write(l, at, how);
        }
        if !self.writable(l) {
            return self.read_only(l, at, how);
        }
        if whole {
            r.cur.revive(l);
        } else if !live {
            // Its E0704 above; overlapping another argument, the E0702 at it, first (S-799).
            return self.record(&place, at);
        }
        self.change(r, place, at, how != How::Assign);
    }

    /// The place `w` changes at `at`, now or (of a `direct` argument) after
    /// the call (§7, S-796: `g(inout o, len_of(b))` reads `b` before it).
    pub(super) fn change(&mut self, r: &mut Run, w: Place, at: Span, direct: bool) {
        self.record(&w, at);
        match direct {
            true => self.inside.after_call.push((w, at)),
            false => self.changed(r, &w, at),
        }
    }

    /// The change of `w` at `at`, in the arguments of a call, to compare
    /// with the places of the calls it is in (S-799).
    pub(super) fn record(&mut self, w: &Place, at: Span) {
        if self.reports && self.inside.calls > 0 {
            self.inside.changes.push((w.clone(), at));
        }
    }

    /// The place `w` changed at `at`: the bindings in scope a place of
    /// which overlaps it are unusable there (§7, S-803: kept once for each
    /// place).
    pub(super) fn changed(&mut self, r: &mut Run, w: &Place, at: Span) {
        let (deps, places) = (&self.deps, &mut self.m.places);
        let k = *self.m.ids.entry(w.clone()).or_insert_with(|| {
            places.push((w.clone(), deps.change(w)));
            places.len() as u32 - 1
        });
        for &l in places[k as usize].1.along.keys().filter(|&&l| deps.in_scope(l, at)) {
            r.cur.set(l, Status::Stale { changes: BTreeMap::from([(k, at)]) });
        }
    }

    /// The E0701 of the write `how` at `at` to a place of `l`, which cannot
    /// be changed (§5.1, §5.2, §5.4): by what `l` is (memo 2.4's table).
    fn read_only(&mut self, l: LocalId, at: Span, how: How) {
        let local = &self.info.locals[l.0 as usize];
        let n = &local.name;
        let why = match (local.kind, local.state) {
            (LocalKind::SelfParam(_), _) => "`self` is borrowed; declare the method with `inout self`".to_string(),
            (LocalKind::Param(_) | LocalKind::ClosureParam(_), _) => {
                format!("`{n}` is a borrowed parameter; declare it `inout {n}`")
            }
            (LocalKind::Let, Bind::Owned | Bind::Borrow { no_drop: true }) => {
                format!("`{n}` is immutable (`let`); declare it with `var`")
            }
            (_, Bind::Borrow { .. }) => format!("`{n}` is a borrow binding (§5.4), read-only"),
            (LocalKind::For { .. }, _) => format!("`{n}` is a `for` variable, read-only"),
            (LocalKind::MatchBind, _) => format!("`{n}` is a `match` binding, read-only"),
            (LocalKind::Let | LocalKind::Var, _) => {
                bug(Some(at), "a `let` or `var` that is neither owned nor borrowed")
            }
        };
        let d = Diagnostic::new(Stage::Modes, Code::E0701, at, format!("{}: {why} (§5.2)", how.verb()))
            .with_note(local.span, "declared here");
        let fix = self.var_fix(l);
        self.report(fix.into_iter().fold(d, Diagnostic::with_fix));
    }

    /// R-161: the candidate that writes `var` for the `let` of `l`, only
    /// when it is the one fix and leaves no error of this stage (§18.1,
    /// memo 2.4): (1) the `let` binds the name alone; (2) the write is not
    /// in an anonymous function that captures `l` (R-25's E0701 there, before
    /// this one); (3) `var`'s value is
    /// consumed, so not a second-class one and not a borrowed Affine one;
    /// (4) the `let` has no attribute; (5) no binding derives from `l`,
    /// which a write after `var` would leave unusable (§7).
    fn var_fix(&mut self, l: LocalId) -> Option<Fix> {
        let b = &self.names.bindings[l.0 as usize];
        let (Origin::Let(s), BindingKind::Let) = (b.origin, b.kind) else { return None };
        let StmtKind::Let { attrs, pat, .. } = &self.ast.stmt(s).kind else {
            bug(Some(self.ast.stmt(s).span), "the head of a `let` binding is no `let`")
        };
        let alone = b.sites == [*pat] && matches!(self.ast.pat(*pat).kind, PatKind::Bind(_));
        if !alone || !attrs.is_empty() || self.deps.derives_from(l) {
            return None;
        }
        let owned = matches!(self.info.heads.get(&Head::Let(s)), Some(HeadRow::Owned));
        match self.kind_of(self.info.locals[l.0 as usize].ty) {
            Some(Kind::Copy | Kind::Shared) => {}
            Some(_) if owned => {}
            _ => return None,
        }
        let span = self.ast.stmt(s).span;
        let word = Span::new(span.file, span.start, span.start + 3);
        self.text[span.start as usize..].starts_with("let").then(|| Fix::replace("change `let` to `var`", word, "var"))
    }
}
