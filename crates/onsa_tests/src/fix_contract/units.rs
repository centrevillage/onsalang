//! The units a candidate touches (S-302) and the edits moved to the text after it.

use std::collections::BTreeSet;

use onsa_diag::{Applied, FileId, Fix, Span};
use onsa_driver::Analyzed;
use onsa_driver::reduce::Unit;

/// Whether `[a, b]` and `[c, d]` meet, both ends included.
pub(super) fn meet(a: Span, b: Span) -> bool {
    a.file == b.file && a.start <= b.end && b.start <= a.end
}

/// One edit of a candidate: its range before it, and the length of its
/// replacement after it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Moved {
    pub(super) before: Span,
    /// The range of its replacement after the candidate.
    pub(super) after: Span,
}

/// The edits of `fix` as `applied` placed them.
pub(crate) fn moved(fix: &Fix, applied: &Applied) -> Vec<Moved> {
    fix.edits().iter().zip(&applied.ranges).map(|(e, r)| Moved { before: e.span, after: *r }).collect()
}

/// Where the offset `at` of `file` lies after the edits: moved by the length
/// differences of the edits before it. An insertion at `at` is before a
/// `start` and after an end (an insertion at an end of a range is not inside
/// it; [`Applied::map_span`] puts it inside, so it is not used here, S-302).
/// The one rule of moving a place by a candidate's edits here (also
/// [`crate::fix_loop`]).
pub(crate) fn shift(edits: &[Moved], file: FileId, at: u32, start: bool) -> u32 {
    let mut delta: i64 = 0;
    for e in edits.iter().filter(|e| e.before.file == file) {
        let b = e.before;
        let before = if b.is_empty() { b.start < at || (start && b.start == at) } else { b.end <= at };
        if before {
            delta += e.after.len() as i64 - b.len() as i64;
        }
    }
    (at as i64 + delta) as u32
}

/// Whether the edit range `edit` falls in `range`: it replaces a character of
/// it, or it is an insertion strictly inside it.
pub(super) fn falls_in(edit: Span, range: Span) -> bool {
    edit.file == range.file
        && if edit.is_empty() {
            range.start < edit.start && edit.start < range.end
        } else {
            edit.start < range.end && range.start < edit.end
        }
}

/// The units of the check before the candidates and which of them are not
/// clean (the module's documentation, 3): computed once for a check.
pub(super) struct Before<'a> {
    pub(super) units: &'a [Unit],
    /// For each unit: it or its item has a diagnostic, or its check read
    /// what the check did not.
    pub(super) dirty: Vec<bool>,
}

impl<'a> Before<'a> {
    pub(super) fn of(analyzed: &'a Analyzed) -> Before<'a> {
        let units = &analyzed.units[..];
        let mut own = vec![false; units.len()];
        for u in analyzed.diagnostic_units.iter().flatten().chain(&analyzed.unread_units()) {
            own[*u] = true;
        }
        let dirty = units.iter().enumerate().map(|(u, unit)| own[u] || unit.parent.is_some_and(|p| own[p])).collect();
        Before { units, dirty }
    }
}

/// The units after a candidate and those before it ([`correspond`]).
pub(super) struct Correspondence {
    /// The units after it that it touches (the module's documentation, 2).
    pub(super) touched: BTreeSet<usize>,
    /// For each unit after it, the units before it that it comes from: the
    /// untouched unit whose moved range it is, else every unit of its level
    /// (top or member) whose moved range meets it; none for a new one.
    pub(super) origins: Vec<Vec<usize>>,
}

/// How the units `after` a candidate whose edits are `edits` come from the
/// units `before` it. (before × after; no recursion.)
pub(super) fn correspond(before: &[Unit], after: &[Unit], edits: &[Moved]) -> Correspondence {
    let mut untouched = BTreeSet::new();
    let mut origins = vec![Vec::new(); after.len()];
    for (u, unit) in before.iter().enumerate() {
        let members: Vec<Span> = before.iter().filter(|m| m.parent == Some(u)).map(|m| m.span).collect();
        // An edit inside a member touches the member, not the item.
        let in_member = |e: Span| {
            members.iter().any(|m| {
                m.file == e.file
                    && if e.is_empty() {
                        m.start < e.start && e.start < m.end
                    } else {
                        m.start <= e.start && e.end <= m.end
                    }
            })
        };
        let s = unit.span;
        let moved = Span::new(s.file, shift(edits, s.file, s.start, true), shift(edits, s.file, s.end, false));
        if !edits.iter().any(|e| falls_in(e.before, unit.span) && !in_member(e.before))
            && let Some(a) = after.iter().position(|x| x.span == moved)
        {
            untouched.insert(a);
            origins[a].push(u);
            continue;
        }
        for (a, x) in after.iter().enumerate() {
            if x.parent.is_none() == unit.parent.is_none() && meet(x.span, moved) {
                origins[a].push(u);
            }
        }
    }
    Correspondence { touched: (0..after.len()).filter(|a| !untouched.contains(a)).collect(), origins }
}
