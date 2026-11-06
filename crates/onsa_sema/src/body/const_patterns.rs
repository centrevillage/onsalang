//! The constants a pattern cannot compare (§7, S-252): one E0020 of the types
//! stage for all those of an arm, with the guard form as its candidate
//! (S-253, S-319; [`onsa_syntax::foreign::guard::constants_in_guard`]).

use onsa_syntax::foreign::{self, RowId, guard};

use super::*;

/// Why the guard form leaves an error (§7, §18.1): it compares with `==`.
const NO_EQUALITY: &str = "no candidate: a guard compares with `==`, which the type of this constant does not have \
     (it needs `PartialEq`; §3.2); compare its fields, or write the test by hand";

impl Checker<'_> {
    /// The E0020 of the constants `bad` of the pattern of `arm`, from the
    /// first to the last (S-316), with no candidate when the guard form
    /// would leave an error or cannot be made (§7).
    pub(super) fn reject_constants(&mut self, arm: &MatchArm, mut bad: Vec<(Span, TyId)>) -> Stop {
        bad.sort_by_key(|(at, _)| at.start);
        let (first, last) = (bad[0].0, bad[bad.len() - 1].0);
        let span = Span { end: last.end, ..first };
        let compared = |ck: &mut Self, t| matches!(ck.operator_verdict(OpNeed::Binary(BinOp::Eq), t), Verdict::Met);
        let guarded = if bad.iter().all(|&(_, t)| compared(self, t)) {
            let starts: Vec<u32> = bad.iter().map(|(at, _)| at.start).collect();
            let block_guard = arm.guard.is_some_and(|g| self.expr(g).kind.block_like());
            guard::constants_in_guard(span.file, self.text, arm.span.start, &starts, block_guard)
        } else {
            Err(Some(NO_EQUALITY))
        };
        let (fixes, note) = match guarded {
            Ok(fix) => (vec![fix], None),
            Err(note) => (Vec::new(), note),
        };
        let d = foreign::report(RowId::FloatConstantPattern, self.text, span, fixes);
        self.diag(match note {
            Some(note) => d.with_rule(note),
            None => d,
        })
    }
}
