//! The candidates of an E0503, and the one of `return` of an E0401 (§7, §18.1,
//! S-876): the first read makes them at the error, where it has not read what
//! follows, so each is judged by reading the body again with it applied, from
//! a new state, with the table of what diverges of that form. A candidate
//! stays when that read has no error of the types stage or of one before it.
//!
//! Each read goes once over a finite tree and none asks for another, for only
//! [`How::First`] makes candidates: a body is read at most three times, and
//! the cost of a file is linear in its bodies.

use super::removed::Marks;
use super::*;

/// A candidate of the error a read stopped at, and the form of the body with
/// it applied.
pub(super) struct Try {
    pub(super) fix: Fix,
    pub(super) patch: Patch,
}

/// The candidates to read of the diagnostic at `at` of the analysis.
pub(super) struct Tries {
    at: usize,
    tries: Vec<Try>,
}

impl<'a> Checker<'a> {
    /// Whether an error found now makes candidates: not in a read of a
    /// candidate, nor in a trial, where it is not reported.
    pub(super) fn makes_candidates(&self) -> bool {
        matches!(self.how, How::First) && !self.failed
    }

    /// Stop the body at `d`, with `tries`, which a read that
    /// [`Checker::makes_candidates`] makes, left to read.
    pub(super) fn stop_with(&mut self, d: Diagnostic, tries: Vec<Try>) -> Stop {
        if !tries.is_empty() {
            self.tries = Some(Tries { at: self.a.diagnostics.len(), tries });
        }
        self.diag(d)
    }

    fn patch(&self) -> Option<&'a Patch> {
        match self.how {
            How::Applied(patch) => Some(patch),
            How::First => None,
        }
    }

    /// The block `b` of the node `e`, in the form this read has of it.
    pub(super) fn block_of(&self, e: ExprId, b: &'a Block) -> &'a Block {
        Patch::block(self.patch(), e, b)
    }

    /// The arms `arms` of the `match` `e`, in the form this read has of them.
    pub(super) fn arms_of(&self, e: ExprId, arms: &'a [MatchArm]) -> &'a [MatchArm] {
        Patch::arms(self.patch(), e, arms)
    }

    /// The value this read has of the `return` statement `s`, which has none.
    pub(super) fn joined_value(&self, s: StmtId) -> Option<ExprId> {
        Patch::joined(self.patch(), s)
    }
}

/// Give the diagnostic of `tries` the candidates that read clean, in their
/// order. `diverging` is the table of the first read.
pub(super) fn read_again(
    a: &mut Analysis,
    bound: &mut HashMap<ModId, HashSet<String>>,
    job: &Job<'_>,
    names: &mut BodyNames,
    diverging: &Diverging,
    tries: Tries,
) {
    let mut fixes = Vec::new();
    for t in tries.tries {
        if reads_clean(a, bound, job, names, diverging, &t.patch) {
            fixes.push(t.fix);
        }
    }
    a.diagnostics[tries.at].fixes.extend(fixes);
}

/// Whether the body reads with `patch` applied and no error up to the types
/// stage. A read that stops with no error, or that reads what the check does
/// not (§18.1, S-692), says nothing of the code after that: it is no clean
/// one. Nothing of the read stays in the analysis.
fn reads_clean(
    a: &mut Analysis,
    bound: &mut HashMap<ModId, HashSet<String>>,
    job: &Job<'_>,
    names: &mut BodyNames,
    diverging: &Diverging,
    patch: &Patch,
) -> bool {
    let (mark, marks) = (a.diagnostics.len(), Marks::of(a, job.id));
    let table = diverging.patched(&job.module.parsed.ast, job.body, patch);
    let mut ck = read_body(a, bound, job, std::mem::take(names), table, How::Applied(patch));
    ck.end_checks();
    let stopped = ck.failed;
    *names = std::mem::take(&mut ck.names);
    let found = a.diagnostics.split_off(mark);
    let unread = marks.undo(a, job.id);
    let later = |d: &Diagnostic| d.stage.check_rank() > Stage::Types.check_rank();
    !unread && (!stopped || found.first().is_some_and(later))
}
