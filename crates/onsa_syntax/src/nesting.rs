//! The check that a candidate stays in the nesting limit (§2.5; §18.1: no
//! candidate goes over it), for the candidates of the syntax stage.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span};

use crate::units::{Units, Within};

/// `d` with the candidate `edits` that write parentheses round parts of the
/// form at `span` (E0011, E0012), when it does not take the unit over the
/// nesting limit; else with the note that names the way out (§18.1: no
/// candidate goes over the limit, §2.5).
pub(crate) fn parenthesized(d: Diagnostic, limit: Limit, span: Span, title: &str, edits: Vec<Edit>) -> Diagnostic {
    let fix = Fix::new(title, edits);
    if too_deep(limit, span, std::slice::from_ref(&fix), 0) {
        return d.with_rule(TOO_DEEP_RULE);
    }
    d.with_fix(fix)
}

/// Whether one of the candidates `fixes` of the form at `span` takes the
/// unit over the nesting limit (§2.5; §18.1: then none is made, and the
/// diagnostic has [`TOO_DEEP_RULE`]). A candidate adds a level for each `(`
/// it writes, and `more` (the levels it adds otherwise). The one judgment
/// of it, for [`parenthesized`] and the clocks (`foreign::clocks`).
pub(crate) fn too_deep(limit: Limit, span: Span, fixes: &[Fix], more: u32) -> bool {
    fixes.iter().any(|f| {
        let added = f.edits().iter().map(|e| e.replace.matches('(').count() as u32).sum::<u32>() + more;
        limit.exceeded(span, f.edits(), added)
    })
}

pub(crate) const TOO_DEEP_RULE: &str =
    "bind a part of it with `let`: parenthesizing it nests deeper than the limit (§2.5)";

/// What the check that a candidate stays in the nesting limit reads (§2.5):
/// the file and its units.
#[derive(Clone, Copy)]
pub(crate) struct Limit<'a> {
    pub text: &'a str,
    pub units: &'a Units,
}

impl Limit<'_> {
    /// [`nests_too_deep`] for the candidate `edits` of the form at `span`,
    /// on the unit of the form (the whole file for a form in no unit).
    pub(crate) fn exceeded(&self, span: Span, edits: &[Edit], added: u32) -> bool {
        let spans: Vec<Span> = edits.iter().map(|e| e.span).chain([span]).collect();
        let within = self.units.reading(&spans).unwrap_or_else(|| {
            Within::file(span.file, self.text, self.units.list.iter().map(|u| u.height).max().unwrap_or(0))
        });
        nests_too_deep(self.text, within, span, edits, added)
    }
}

/// Whether the candidate `edits` of the form at `span` (in the file `text`;
/// both in `within`), which add up to `added` levels, take the text `within`
/// over the nesting limit (§2.5; §18.1: no such candidate is made). The
/// parser counts it, on that text with the candidate, when its height (a
/// level it reaches at least) and `added` are over the limit: only a unit
/// near the limit is read again, and only that unit. The one judgment of
/// it, for the candidates of the syntax stage and the parentheses they take
/// (`crate::operands`).
pub(crate) fn nests_too_deep(text: &str, within: Within, span: Span, edits: &[Edit], added: u32) -> bool {
    if within.height + added <= crate::parser::NESTING_LIMIT {
        return false;
    }
    let Some(_counting) = Counting::start() else { return false };
    let own = within.of(text);
    let local: Vec<Edit> = edits.iter().map(|e| within.local(e)).collect();
    let Ok(after) = onsa_diag::apply_text(own, &local.iter().collect::<Vec<_>>()) else { return true };
    #[cfg(test)]
    READ.set(READ.get() + after.len());
    let longer = after.len().saturating_sub(own.len()) as u32;
    let (start, end) = (span.start - within.span.start, span.end - within.span.start + longer);
    let file = span.file;
    let out = crate::parser::Parser::new(file, &after, crate::lex(file, &after)).parse_units(within.ctx);
    out.diagnostics.iter().any(|d| d.code == Code::E0006 && start <= d.span.start && d.span.start < end)
}

thread_local! {
    /// Whether a parse of [`nests_too_deep`] is running ([`Counting`]).
    static COUNTING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// How many parses [`nests_too_deep`] made on this thread: the tests
    /// see that a file of many units parses again only where a unit is deep.
    #[cfg(test)]
    pub(crate) static PARSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// The bytes those parses read: the tests bound them with what the
    /// completion of the candidates reads ([`crate::CandidateReads`]).
    #[cfg(test)]
    pub(crate) static READ: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A parse of [`nests_too_deep`] running on this thread: it only counts the
/// levels, so its own failures need no candidates and make none of the check
/// (else each candidate of each unit parses the file again inside the parse
/// of the one before, exponential in the units). The mark goes when the
/// guard does, also when an internal error unwinds through it.
struct Counting;

impl Counting {
    /// The guard, or `None` when a parse of the check is running already.
    fn start() -> Option<Counting> {
        let running = COUNTING.replace(true);
        #[cfg(test)]
        PARSES.set(PARSES.get() + usize::from(!running));
        // `then`, not `then_some`: a guard made while a parse runs would drop
        // at once and take the mark of the running one with it.
        (!running).then(|| Counting)
    }
}

impl Drop for Counting {
    fn drop(&mut self) {
        COUNTING.set(false);
    }
}
