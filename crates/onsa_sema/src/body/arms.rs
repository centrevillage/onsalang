//! The E0503 of an arm of a `match` and its candidates (§7, §18.1): one that
//! takes away the arms no value chooses, and one that moves the arm of a `_`
//! or a binding to the end (S-934). The body stops at the error: the patterns
//! read here for a candidate leave the state as they like, and what the
//! candidates give the rest of the body is read in [`super::reread`].

use onsa_diag::Edit;
use onsa_syntax::ast::MatchArm;

use super::reread::Try;
use super::*;

/// A `match` being read: the node, the arms, the type of its value and the
/// type it is expected to have.
pub(super) struct Arms<'x> {
    pub(super) expr: ExprId,
    pub(super) arms: &'x [MatchArm],
    pub(super) st: TyId,
    pub(super) expected: Option<TyId>,
}

impl<'a> Checker<'a> {
    /// The arms of `m` in turn: the first that gets no value stops the body
    /// with an E0503 (§7, one in a body, §18.1).
    pub(super) fn read_arms(&mut self, m: &Arms<'_>, seen: &mut Seen, result: &mut Option<TyId>) -> R<()> {
        let Some(k) = self.check_arms(m, seen, result)? else { return Ok(()) };
        let d = self.unreachable_arm(m.arms[k].pat, seen.whole);
        let tries = if self.makes_candidates() { self.arm_tries(m, k, seen) } else { Vec::new() };
        Err(self.stop_with(d, tries))
    }

    /// The candidates of the E0503 of the arm `k` of `m`.
    fn arm_tries(&mut self, m: &Arms<'_>, k: usize, seen: &mut Seen) -> Vec<Try> {
        let deleted = self.deleted_arms(m, k, seen);
        let whole = m.arms.iter().position(|a| self.takes_every_value(a));
        let moved = whole.filter(|c| c + 1 == k).and_then(|c| self.moved_arm(m, c));
        deleted.into_iter().chain(moved).collect()
    }

    /// Whether the pattern of `arm` is a `_` or a binding itself and it has
    /// no guard (§7, S-934): `(_, _)` covers as much and is not one.
    fn takes_every_value(&self, arm: &MatchArm) -> bool {
        arm.guard.is_none() && matches!(self.ast.pat(arm.pat).kind, PatKind::Wild | PatKind::Bind(_))
    }

    /// The E0503 of the arm of the pattern `pat`, which the arms before it
    /// cover (§7). `whole` is the arm of a `_` or a binding among them.
    fn unreachable_arm(&self, pat: PatId, whole: Option<Span>) -> Diagnostic {
        let span = self.ast.pat(pat).span;
        let msg = "no value chooses this arm: the arms before it cover what it takes (§7)";
        let d = Diagnostic::new(Stage::Types, Code::E0503, span, msg).with_found(self.src(span));
        match whole {
            Some(at) => d.with_note(at, "this arm takes every value"),
            None => d,
        }
    }

    /// The candidate that takes away the arm `k` of `m`, which gets no value,
    /// and all the others that get none (as the statements after a diverging
    /// one, §7): what `k` leaves in the same stage is not left for a next run
    /// (§18.1). A binding only they read is the E0309 of a later stage (S-292).
    fn deleted_arms(&mut self, m: &Arms<'_>, k: usize, seen: &mut Seen) -> Option<Try> {
        let never = self.arms_never_chosen(m, k, seen)?;
        let leaves_loop =
            |a: &MatchArm| a.guard.is_some_and(|g| self.ast.leaves_loop(g)) || self.ast.leaves_loop(a.body);
        if never.iter().any(|&i| leaves_loop(&m.arms[i])) {
            return None;
        }
        let rest = (0..m.arms.len()).filter(|i| never.binary_search(i).is_err());
        let rest: Vec<MatchArm> = rest.map(|i| m.arms[i].clone()).collect();
        if rest.iter().all(|a| self.info.diverging.expr(a.body)) && !self.stays_reached(m.expr) {
            return None;
        }
        let edits = never.iter().map(|&i| Edit::delete(self.arm_with_comma(&m.arms[i]))).collect();
        let fix = Fix::new("remove the arms that no value chooses", edits);
        Some(Try { fix, patch: Patch::Arms(m.expr, rest) })
    }

    /// The arms from `k` on that the arms before them leave no value, `k`
    /// first: the patterns after it are read here and nowhere else. None
    /// when one of them cannot be read.
    fn arms_never_chosen(&mut self, m: &Arms<'_>, k: usize, seen: &mut Seen) -> Option<Vec<usize>> {
        let mut never = vec![k];
        for (i, arm) in m.arms.iter().enumerate().skip(k + 1) {
            let p = self.quietly(|ck| ck.bind_pat(arm.pat, m.st, false));
            self.bad_consts.clear();
            let p = p?;
            if !self.reachable(seen, &p, m.st) {
                never.push(i);
            } else if arm.guard.is_none() {
                seen.add(p, self.ast.pat(arm.pat).span);
            }
        }
        Some(never)
    }

    /// The end of the `,` after `arm`, past blanks and line comments. The
    /// last arm of a `match` may have none.
    fn comma_after(&self, arm: &MatchArm) -> Option<u32> {
        let mut at = arm.span.end as usize;
        loop {
            let rest = self.text[at..].trim_start();
            at = self.text.len() - rest.len();
            if rest.starts_with(',') {
                return Some(at as u32 + 1);
            }
            if !rest.starts_with("//") {
                return None;
            }
            at += rest.find('\n').unwrap_or(rest.len());
        }
    }

    /// `arm` with its `,`: a comment at the end of the line stays (§18.1).
    fn arm_with_comma(&self, arm: &MatchArm) -> Span {
        Span::new(arm.span.file, arm.span.start, self.comma_after(arm).unwrap_or(arm.span.end))
    }

    /// The candidate that moves the arm `c` of `m` to the end (§7, S-934): it
    /// may make an arm a body or a value that was not checked, and what is
    /// covered in it stays so.
    fn moved_arm(&mut self, m: &Arms<'_>, c: usize) -> Option<Try> {
        let (arm, last) = (&m.arms[c], m.arms.last()?);
        let (end, lead) = match self.comma_after(last) {
            Some(end) => (end, ""),
            None => (last.span.end, ","),
        };
        // At the end of the last arm: its line may end in a comment (§18.1).
        let text = self.src(arm.span);
        let moved = if self.text[arm.span.end as usize..last.span.start as usize].contains('\n') {
            let line = self.text[..arm.span.start as usize].rfind('\n').map_or(0, |n| n + 1);
            let indent = &self.text[line..];
            let indent = &indent[..indent.len() - indent.trim_start_matches([' ', '\t']).len()];
            format!("{lead}\n{indent}{text},")
        } else {
            format!("{lead} {text}")
        };
        let edits = vec![Edit::delete(self.arm_with_comma(arm)), Edit::insert(arm.span.file, end, moved)];
        let fix = Fix::new("move the arm that takes every value to the end", edits);
        let order = m.arms[..c].iter().chain(&m.arms[c + 1..]).chain([arm]).cloned().collect();
        Some(Try { fix, patch: Patch::Arms(m.expr, order) })
    }
}
