//! The near "same place" of S-236, for the fuzzing.

use onsa_diag::{Diagnostic, FileId, Span};
use onsa_driver::Analyzed;

use super::reading::reading_difference;
use super::text::{TextCheck, Unapplied, apply_alone, check_text};
use super::units::moved;

// ------------------------------------------------------------ the fuzzing

/// One violation of the near "same place" ([`same_place`]).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Violation {
    /// The original diagnostic.
    pub code: String,
    pub line: u32,
    pub col: u32,
    /// The title of its first candidate.
    pub title: String,
    /// The code of the diagnostic at the same place after it, or `internal`
    /// when the check after it ends in an internal error.
    pub left: String,
    pub left_line: Option<u32>,
    pub left_col: Option<u32>,
    pub message: String,
}

/// What [`same_place`] found in one file.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize)]
pub struct SamePlace {
    /// The candidates checked again.
    pub candidates: usize,
    pub violations: Vec<Violation>,
    /// The check of the file itself ended in an internal error (the fuzzing's
    /// own run of `onsa check` reports it).
    pub internal: Option<String>,
}

/// The near "same place" of S-236 for the fuzzing, which cannot know how many
/// errors an input holds (and the reading outside the edits, S-302, with the
/// kind `reading`): the file `text` checked as a single-file package
/// (as `onsa check` checks it); for each diagnostic, its first candidate
/// alone applied and the file checked again. A violation is a diagnostic of
/// the check after it, of the original's stage or an earlier one, whose
/// start lies in the same place: the original diagnostic's range or a
/// replacement, both moved to the text after it
/// ([`onsa_diag::Applied::map_span`]). An error the input held there before
/// is not one (the input has two errors there, as a stray `1.` at the top
/// level, an E0020 and an E0002): a diagnostic of the same code and message
/// among every diagnostic the stages found before the choice of one per
/// unit, but the original, whose start moves into the same place. One of the
/// original's own code inside the original's range is no other error, though:
/// it is a part of the same form, which the candidate must fix whole (S-248;
/// the inner `--x` of `---x`), and stays a violation. Nor is the outer form of
/// the original, which the syntax stage did not read past it (the next link
/// of the chain of calls `g(1)(2)(3)`, S-326): one of the same code and
/// message that starts where the moved original starts and ends after it, so
/// the original was not the only error of its unit (the premise of S-314;
/// [`outer_form`]). The diagnostics are
/// compared by code, range and message (`found` is filled in only after the
/// choice per unit). The units are not used: this is a net for new kinds,
/// not the contract.
pub fn same_place(text: &str) -> SamePlace {
    let TextCheck { loaded, analyzed } = match check_text(text) {
        Ok(run) => run,
        Err(e) => return SamePlace { internal: Some(e), ..SamePlace::default() },
    };
    let mut out = SamePlace::default();
    for d in &analyzed.diagnostics {
        let Some(fix) = d.fixes.first() else { continue };
        let lc = loaded.sources.file(d.span.file).line_col(d.span.start);
        let violation = |left: String, at: Option<(u32, u32)>, message: String| Violation {
            code: d.code.as_str().to_string(),
            line: lc.line,
            col: lc.col,
            title: fix.title().to_string(),
            left,
            left_line: at.map(|a| a.0),
            left_col: at.map(|a| a.1),
            message,
        };
        out.candidates += 1;
        // What cannot be checked is a violation of its own kind, never skipped.
        let Some(rank) = d.stage.check_rank() else {
            out.violations.push(violation("unchecked-stage".into(), None, format!("the {} stage", d.stage.name())));
            continue;
        };
        let (new_text, applied) = match apply_alone(&loaded.sources, fix) {
            Ok(a) => a,
            Err(e) => {
                let kind = match e {
                    Unapplied::CannotApply(_) => "cannot-apply",
                    Unapplied::OtherFile => "other-file",
                };
                out.violations.push(violation(kind.into(), None, e.to_string()));
                continue;
            }
        };
        // The reading outside its edits stays (S-302), as in the contract.
        if let Some(diff) = reading_difference(text, &new_text, FileId(0), &moved(fix, &applied)) {
            out.violations.push(violation("reading".into(), None, diff));
        }
        let TextCheck { loaded: again, analyzed: after } = match check_text(&new_text) {
            Ok(a) => a,
            Err(e) => {
                out.violations.push(violation("internal".into(), None, e));
                continue;
            }
        };
        let mut places: Vec<Span> = applied.ranges.clone();
        let moved_original = applied.map_span(d.span);
        places.push(moved_original);
        let in_place = |s: Span| in_same_place(&places, s);
        for d2 in &after.diagnostics {
            if d2.stage.check_rank().is_none_or(|r| r > rank) || !in_place(d2.span) {
                continue;
            }
            let same = |a: &Diagnostic, b: &Diagnostic| a.code == b.code && a.span == b.span && a.message == b.message;
            let held_before = found_before(&analyzed).any(|o| {
                let part_of_the_form = o.code == d.code
                    && o.span.file == d.span.file
                    && d.span.start <= o.span.start
                    && o.span.end <= d.span.end;
                // The same error moved by the edits: its code and its place,
                // not its message, which may quote the source the candidate
                // changed (E0010 quotes its chain).
                let moved = applied.map_span(o.span);
                !same(o, d)
                    && !part_of_the_form
                    && o.code == d2.code
                    && moved.file == d2.span.file
                    && moved.start <= d2.span.end
                    && d2.span.start <= moved.end
                    && in_place(moved)
            });
            if held_before || outer_form(d, d2, moved_original) {
                continue;
            }
            let lc2 = again.sources.file(d2.span.file).line_col(d2.span.start);
            out.violations.push(violation(d2.code.as_str().to_string(), Some((lc2.line, lc2.col)), d2.message.clone()));
        }
    }
    out
}

/// Whether `left`, found after the candidate of `original` (whose range,
/// moved to the text after it, is `moved`), is the outer form of the
/// original that the syntax stage did not read past it ([`same_place`]): the
/// same code and message, the same start, and an end strictly after the
/// moved end. One that ends where the original ends (a candidate that fixed
/// nothing) or inside it (a part of the same form, S-248) is not.
pub(super) fn outer_form(original: &Diagnostic, left: &Diagnostic, moved: Span) -> bool {
    left.code == original.code
        && left.message == original.message
        && left.span.file == moved.file
        && left.span.start == moved.start
        && left.span.end > moved.end
}

/// Whether the diagnostic at `s` starts in the same place as one of
/// `places` (the near "same place" of [`same_place`]): inside a range that is
/// not empty, half open (`start <= s.start < end`), or at the point of an
/// empty one (what a deletion or an insertion of nothing leaves). An error
/// that starts right at the end of a replacement is not in it: the input held
/// another error there, which the candidate let the check reach (the premise
/// of S-236 does not hold), as an insertion at an end of a token is not
/// inside it (S-302); a change of reading at that border is what the
/// `reading` check finds.
pub(super) fn in_same_place(places: &[Span], s: Span) -> bool {
    places.iter().any(|p| {
        p.file == s.file && if p.is_empty() { s.start == p.start } else { p.start <= s.start && s.start < p.end }
    })
}

/// Every diagnostic the stages found, before the choice of one per unit.
fn found_before(a: &Analyzed) -> impl Iterator<Item = &Diagnostic> {
    a.pkg.modules.iter().flat_map(|m| m.parsed.diagnostics.iter()).chain(a.analysis.diagnostics.iter())
}
