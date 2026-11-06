//! The E0503 of an arm of a `match` and its candidates (§7, §18.1): one that
//! takes away the arms no value chooses, and one that moves the arm of a `_`
//! or a binding to the end (S-934). The body stops at the error, so what the
//! candidates try leaves the state as it likes, for the error to be reported.

use onsa_diag::Edit;
use onsa_syntax::ast::MatchArm;

use super::reach::Kept;
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
    /// with an E0503 (§7, one in a body, §18.1). An arm that takes every
    /// value with arms after it always ends there, so the state is kept
    /// before it for a trial of the other order, and a program with no error
    /// pays nothing. A trial or a look at another form makes no candidate.
    pub(super) fn read_arms(&mut self, m: &Arms<'_>, seen: &mut Seen, result: &mut Option<TyId>) -> R<()> {
        let plain = self.failed || self.trying_arms;
        // A pattern decides nothing of a value that is known: of one that
        // is open, the arm taken away may be what decided it (S-876).
        let known = !self.infer.has_undefaulted_vars(&self.a.types, m.st);
        let whole = m.arms.iter().position(|a| self.takes_every_value(a));
        let moved = whole.filter(|&c| !plain && c + 1 < m.arms.len() && self.judges_arms(m.st));
        let (before, from) = m.arms.split_at(moved.unwrap_or(m.arms.len()));
        let mut stopped = self.check_arms(before.iter(), m.st, seen, result, m.expected)?;
        let start = moved.filter(|_| stopped.is_none()).map(|_| (self.keep(), seen.clone(), *result));
        if stopped.is_none() {
            stopped = self.check_arms(from.iter(), m.st, seen, result, m.expected)?;
        }
        let Some(arm) = stopped else { return Ok(()) };
        let mut d = self.unreachable_arm(arm.pat, seen.whole);
        if let Some(k) = m.arms.iter().position(|a| a.pat == arm.pat).filter(|_| !plain) {
            let deleted = if known { self.deleted_arms(m, k, seen, *result) } else { None };
            let second = moved.zip(start).filter(|(c, _)| c + 1 == k).and_then(|(c, s)| self.moved_arm(m, c, s));
            for fix in deleted.into_iter().chain(second) {
                d = d.with_fix(fix);
            }
        }
        Err(self.diag(d))
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
    /// (§18.1). None when the rest does not stand without them (S-876); a
    /// binding only they read is the E0309 of a later stage (S-292). `result`
    /// is the type the arms have by `k`, whose pattern is read already.
    fn deleted_arms(&mut self, m: &Arms<'_>, k: usize, seen: &mut Seen, result: Option<TyId>) -> Option<Fix> {
        let kept = self.keep();
        let never = self.arms_never_chosen(m, k, seen);
        self.put_back(kept);
        let never = never?;
        let leaves_loop =
            |a: &MatchArm| a.guard.is_some_and(|g| self.ast.leaves_loop(g)) || self.ast.leaves_loop(a.body);
        if never.iter().any(|&i| leaves_loop(&m.arms[i])) {
            return None;
        }
        let rest = (0..m.arms.len()).filter(|i| never.binary_search(i).is_err());
        let diverges = rest.map(|i| &m.arms[i]).all(|a| self.info.diverging.expr(a.body));
        if (diverges && !self.stays_reached(m.expr)) || !self.end_is_clean(None) {
            return None;
        }
        let decides = self.parts_decide(never.iter().copied(), |ck, i| {
            let arm = &m.arms[i];
            if i != k {
                let p = ck.bind_pat(arm.pat, m.st, false);
                ck.bad_consts.clear();
                p?;
            }
            if let Some(g) = arm.guard {
                let bool_ = ck.bool_();
                ck.check_expr(g, Some(bool_))?;
            }
            ck.check_expr(arm.body, result).map(drop)
        });
        if decides {
            return None;
        }
        let edits = never.iter().map(|&i| Edit::delete(self.arm_with_comma(&m.arms[i]))).collect();
        Some(Fix::new("remove the arms that no value chooses", edits))
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

    /// The candidate that moves the arm `c` of `m` to the end (§7, S-934),
    /// if the order `c + 1 ..`, `c` reads with no error (§18.1): it may make
    /// an arm a body or a value that was not checked, and what is covered in
    /// it stays so. `start` is the state before `c`.
    fn moved_arm(&mut self, m: &Arms<'_>, c: usize, start: (Kept, Seen, Option<TyId>)) -> Option<Fix> {
        let (kept, mut seen, mut result) = start;
        self.put_back(kept);
        let order = m.arms[c + 1..].iter().chain(&m.arms[c..=c]);
        let mark = self.a.diagnostics.len();
        self.trying_arms = true;
        let clean = self.quietly(|ck| {
            ck.failed = false;
            let stopped = ck.check_arms(order, m.st, &mut seen, &mut result, m.expected)?;
            if stopped.is_some() || ck.failed { Err(Stop) } else { Ok(()) }
        });
        self.trying_arms = false;
        self.a.diagnostics.truncate(mark);
        if clean.is_none() || !self.end_is_clean(None) {
            return None;
        }
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
        Some(Fix::new("move the arm that takes every value to the end", edits))
    }
}
