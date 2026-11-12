//! The parentheses that the candidates of the syntax stage take round a
//! block-like expression they leave as an operand (§3.1, §18.1, S-537 J-2):
//! the line joined after `if … }` (`(if … }) +`), the `.(` after it, a
//! blank taken out before a postfix symbol, and every other candidate that
//! puts one beside an operator. No maker of a candidate knows it: each
//! candidate of a diagnostic that is reported ([`Units::choose`]) is applied,
//! the units it touches read again with the parser's own grammar in the
//! context of their list ([`Units::reading`], [`crate::read`]), and the
//! block-like operands of the expressions its edits share text with
//! ([`groups::block_like_operands`], the judgment of E0013) are
//! parenthesized in it. The candidate so completed is read once more, and it
//! is dropped when a reading nests over the limit ([`nesting::over_limit`]) or
//! leaves more than the candidate alone did, less the E0013 of those
//! expressions (§18.1: a candidate that cannot keep the promise is not made;
//! another error of the unit stays as it was). The same reading judges every
//! candidate, whatever makes it, on the error it leaves ([`leaves`]).
//!
//! [`crate::read`] completes no candidate, so the reading goes one level
//! deep; each reading is of the units a candidate touches, and one
//! diagnostic of a unit is reported, so the cost is the size of the file
//! times the candidates of a diagnostic ([`CandidateReads`]).

use std::collections::BTreeMap;
use std::ops::Range;

use onsa_diag::{Code, Diagnostic, Edit, Fix, Note, Span, Stage};

use crate::cst::Cst;
use crate::groups;
use crate::nesting;
use crate::units::{Units, Within};

/// What the completion read again in a file: the text of the units (bytes,
/// one count per reading), the text lexed in the file to judge whether two
/// tokens join (`crate::edits::lexed`: for the rows that take blanks out
/// and for the candidates reported, [`crate::edits::apart`]), the
/// candidates dropped (a
/// completed one that left more diagnostics of the syntax stage than the
/// candidate alone did, less the E0013 it takes away), those dropped for an
/// error they leave ([`Failed`]), and those kept as they are without a
/// reading (no run of the units of one list, [`Units::reading`]). The tests
/// see them.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CandidateReads {
    pub bytes: usize,
    pub lexed: usize,
    pub dropped: usize,
    pub left: usize,
    pub unread: usize,
    /// Of `dropped`, those that nest over the limit (§2.5), and the rule
    /// note of the last of them.
    pub deep: usize,
    pub deep_rule: &'static str,
}

/// The candidates of the diagnostics of the syntax stage that a check
/// reports among `diagnostics` (of the file `text` whose CST and units are
/// those), with the parentheses they need and apart from the tokens around
/// what they take out, or dropped when they join them
/// ([`crate::edits::apart`]). E0013's own candidate is
/// those parentheses. A diagnostic left without a candidate takes the code
/// of [`Code::without_fixes`]; E0002 orders before the other codes at its
/// place, so it stays the one reported.
pub(crate) fn complete(
    text: &str,
    cst: &Cst,
    units: &Units,
    apart: &crate::edits::Insertions,
    diagnostics: &mut [Diagnostic],
) -> CandidateReads {
    let reported: Vec<bool> =
        units.choose(&diagnostics.iter().collect::<Vec<_>>()).into_iter().map(|(_, c)| c).collect();
    let failed = Failed::of(units, diagnostics);
    let mut reads = CandidateReads::default();
    for (d, _) in diagnostics.iter_mut().zip(reported).filter(|(_, r)| *r) {
        if d.stage != Stage::Syntax || d.fixes.is_empty() {
            continue;
        }
        let file = d.span.file;
        let fixes: Vec<Fix> = (std::mem::take(&mut d.fixes).into_iter())
            .filter_map(|f| crate::edits::apart(file, text, cst.tokens(), f, apart))
            .collect();
        let deep = reads.deep;
        d.fixes = match d.code {
            Code::E0013 => fixes,
            _ => fixes.into_iter().filter_map(|f| completed(text, units, &failed, d.span, f, &mut reads)).collect(),
        };
        if d.fixes.is_empty() {
            d.code = d.code.without_fixes(d.stage);
            if reads.deep > deep {
                d.notes.push(Note::rule(reads.deep_rule));
            }
        }
    }
    reads
}

/// `fix`, a candidate of a later stage at `span`, whose unit has no
/// diagnostic of the syntax stage, with the parentheses it needs
/// ([`completed`]).
pub(crate) fn completed_later(text: &str, units: &Units, span: Span, fix: Fix) -> Option<Fix> {
    completed(text, units, &Failed(Vec::new()), span, fix, &mut CandidateReads::default())
}

/// The starts of the units of the diagnostics of the syntax stage of a file,
/// one for each diagnostic, in order.
struct Failed(Vec<u32>);

impl Failed {
    fn of(units: &Units, diagnostics: &[Diagnostic]) -> Failed {
        let syntax = diagnostics.iter().filter(|d| d.stage == Stage::Syntax);
        let mut starts: Vec<u32> = syntax.filter_map(|d| units.of(d.span)).map(|u| units.list[u].span.start).collect();
        starts.sort_unstable();
        Failed(starts)
    }

    /// Whether the units of `within` hold one diagnostic of the syntax stage.
    fn one_in(&self, within: &Within) -> bool {
        let (a, b) = (within.span.start, within.span.end);
        self.0.partition_point(|&s| s <= b) - self.0.partition_point(|&s| s < a) == 1
    }
}

/// Whether `read`, of a text of `len` bytes, only wants the item that
/// follows it: no item, and no error but a doc comment that documents nothing
/// or a declaration wanted at the end. A unit of no item (a comment, an
/// attribute) is read without the item after it in the file, so that is what
/// the reading says, not what a check says (S-247, S-432).
fn wants_the_next_item(read: &crate::Read, len: usize) -> bool {
    let at_the_end = |d: &Diagnostic| d.span.is_empty() && d.span.start as usize == len;
    let syntax = || read.diagnostics.iter().filter(|d| d.stage == Stage::Syntax);
    read.ast.items.is_empty() && syntax().all(|d| d.code == Code::E0004 || at_the_end(d))
}

/// Whether `read` holds an error that the candidate leaves (§18.1): a
/// diagnostic of the syntax stage that starts in `place`, from the first edit
/// of the candidate, or the diagnostic if that is before it, to the end of the
/// diagnostic's place. The reading goes forward, so one before the edit was
/// there before it, an error the check did not report (a `{` never closed, a
/// doc comment after an attribute). One from the end on cannot be told from
/// another error of the unit, past which the parser did not read (`with h()else`):
/// the number of errors of a unit is not known. One with a candidate of its own
/// is mended by the next one (`e0002_arm_comma_before_leading`), but for an
/// E0004: its candidate gives up the doc comment the candidate stranded (R-380).
/// One that starts in what the candidate writes (in a replacement of
/// `regions`) is the candidate's too, where it is (the `.` of `fn t::` moved
/// to the next line, S-963); not one right after what it takes out. One in
/// the writer's text it copies or moves, unchecked there (`writers`,
/// [`Edit::writers`]), is the input's, left to the check after it (§18.1:
/// "候補が写すか動かす部分", S-475).
fn leaves(read: &crate::Read, place: Range<u32>, regions: &[(u32, u32)], writers: &[(u32, u32)]) -> bool {
    let mended = |d: &Diagnostic| !d.fixes.is_empty() && d.code != Code::E0004;
    let at = |s: u32| place.contains(&s) || regions.iter().any(|&(a, b)| (a..b).contains(&s));
    let inside = |d: &Diagnostic| writers.iter().any(|&(a, b)| a <= d.span.start && d.span.end <= b);
    read.diagnostics.iter().any(|d| d.stage == Stage::Syntax && !mended(d) && !inside(d) && at(d.span.start))
}

/// `fix`, a candidate of the diagnostic at `span`, with the parentheses it
/// needs; `None` when it leaves more with them than [`keeps`] allows, or
/// when the diagnostic is the one of its units and it leaves an error
/// ([`leaves`]). A candidate whose edits touch no run of the units of one
/// list ([`Units::reading`]) is kept as it is.
fn completed(
    text: &str,
    units: &Units,
    failed: &Failed,
    span: Span,
    fix: Fix,
    reads: &mut CandidateReads,
) -> Option<Fix> {
    let spans: Vec<Span> = fix.edits().iter().map(|e| e.span).collect();
    let Some(within) = units.reading(&spans) else {
        reads.unread += 1;
        return Some(fix);
    };
    let (file, own) = (within.span.file, within.of(text));
    let local: Vec<Edit> = fix.edits().iter().map(|e| within.local(e)).collect();
    // The place of the diagnostic: a character at least (§18.1's near "same
    // place", `fix_contract::same_place`).
    let last = span.end.saturating_sub(within.span.start);
    let start = span.start.saturating_sub(within.span.start);
    let reach = u32::from(span.is_empty());
    let place = |regions: &[(u32, u32)], end: u32| regions.first().map_or(start, |r| r.0.min(start))..end + reach;
    let Ok(Applied { text: after, regions, writers, end }) = applied(own, &local, last) else { return Some(fix) };
    reads.bytes += after.len();
    let alone = crate::read(file, &after, within.ctx);
    let judge = within.span.start <= span.start && failed.one_in(&within) && !wants_the_next_item(&alone, after.len());
    if deep(&alone, reads, nesting::WRITTEN_TOO_DEEP) {
        return None;
    }
    let touched = touched_operands(&alone, &regions);
    if touched.is_empty() {
        let left = judge && leaves(&alone, place(&regions, end), &regions, &writers);
        reads.left += usize::from(left);
        return (!left).then_some(fix);
    }
    let operands: Vec<Span> = touched.iter().flat_map(|(_, o)| o.iter().copied()).collect();
    let local = composed(local, &regions, groups::parenthesizing(&operands).collect());
    let edits: Vec<Edit> = local.iter().map(|e| within.global(e)).collect();
    let Ok(Applied { text: again, regions, writers, end }) = applied(own, &local, last) else {
        reads.dropped += 1;
        return None;
    };
    reads.bytes += again.len();
    let with = crate::read(file, &again, within.ctx);
    if deep(&with, reads, nesting::TOO_DEEP_RULE) {
        return None;
    }
    if !keeps(&alone, touched.len(), &with, &regions) {
        reads.dropped += 1;
        return None;
    }
    if judge && leaves(&with, place(&regions, end), &regions, &writers) {
        reads.left += 1;
        return None;
    }
    Some(Fix::new(fix.title(), edits))
}

/// Whether `read`, of the units a candidate touches with it, goes over the
/// nesting limit (§2.5; §18.1: then no candidate), counted in `reads`. The
/// units are read whole, also where the parser did not read them before (a
/// guard after the failure, R-397), so their height does not bound it.
/// `rule` says why, for the note.
fn deep(read: &crate::Read, reads: &mut CandidateReads, rule: &'static str) -> bool {
    let over = nesting::over_limit(&read.diagnostics, 0..u32::MAX);
    reads.dropped += usize::from(over);
    reads.deep += usize::from(over);
    if over {
        reads.deep_rule = rule;
    }
    over
}

/// The expressions of `read` with block-like operands that share text with
/// one of `regions` (the ranges of the replacements of a candidate in its
/// text: one character at least, or inside for a replacement with nothing),
/// with those operands. An expression that only meets one at an end is not
/// touched (S-537, D-2: `[1{ 2 } + 3]` and `[1 { 2 } + 3]` alike).
fn touched_operands(read: &crate::Read, regions: &[(u32, u32)]) -> Vec<(Span, Vec<Span>)> {
    groups::block_like_operands(&read.ast, &|e| read.map.expr_kind(&read.cst, e))
        .into_iter()
        .filter(|(root, _)| regions.iter().any(|&(a, b)| root.start < b && a < root.end))
        .collect()
}

/// Whether the candidate with the parentheses (`with`, the ranges of its
/// replacements `regions`) keeps what the candidate `alone` promised: no
/// expression it touches is left with a block-like operand, and its
/// diagnostics of the syntax stage are among those of `alone` less the
/// E0013 of the `touched` expressions (one each). Another error of the unit
/// stays, and the code reported does not change for it.
fn keeps(alone: &crate::Read, touched: usize, with: &crate::Read, regions: &[(u32, u32)]) -> bool {
    if !touched_operands(with, regions).is_empty() {
        return false;
    }
    let mut left: BTreeMap<Code, usize> = BTreeMap::new();
    for d in alone.diagnostics.iter().filter(|d| d.stage == Stage::Syntax) {
        *left.entry(d.code).or_default() += 1;
    }
    let Some(e0013) = left.get_mut(&Code::E0013).and_then(|n| n.checked_sub(touched)) else { return false };
    left.insert(Code::E0013, e0013);
    with.diagnostics.iter().filter(|d| d.stage == Stage::Syntax).all(|d| {
        let n = left.entry(d.code).or_default();
        n.checked_sub(1).map(|m| *n = m).is_some()
    })
}

/// A text with the edits of a candidate ([`applied`]).
struct Applied {
    text: String,
    /// The range each replacement takes in `text`.
    regions: Vec<(u32, u32)>,
    /// The ranges of the writer's text in them ([`Edit::writers`]).
    writers: Vec<(u32, u32)>,
    /// Where the offset `last` of the text before goes: the end of the
    /// replacement of an edit that holds it.
    end: u32,
}

/// `text` with `edits` (sorted, apart): where each goes and where `last`
/// goes are [`onsa_diag::Applied`]'s.
fn applied(text: &str, edits: &[Edit], last: u32) -> Result<Applied, String> {
    let mut edits: Vec<&Edit> = edits.iter().collect();
    onsa_diag::sort_edits(&mut edits);
    let file = edits.first().map_or(onsa_diag::FileId(0), |e| e.span.file);
    let mut moved = onsa_diag::apply_text_moved(file, text, &edits)?;
    let regions: Vec<(u32, u32)> = moved.ranges.iter().map(|r| (r.start, r.end)).collect();
    let writers = (edits.iter().zip(&regions))
        .flat_map(|(e, &(a, _))| e.writers().iter().map(move |&(x, y)| (a + x, a + y)))
        .collect();
    let end = moved.map_span(Span::new(file, last, last)).end;
    let after = moved.texts.remove(&file).unwrap_or_else(|| text.to_string());
    Ok(Applied { text: after, regions, writers, end })
}

/// The edits `local` (sorted; `regions` the ranges of their replacements in
/// the text after them) and the insertions `parens` made in that text, as
/// one set of edits of the text before. An insertion at or inside the range
/// of a replacement goes into it (`" +"` is `") +"`, a blank taken out gives
/// way to a `(`); any other is an insertion of its own. The edits stay the
/// least that changes the tokens (§18.1).
fn composed(mut local: Vec<Edit>, regions: &[(u32, u32)], mut parens: Vec<Edit>) -> Vec<Edit> {
    local.sort_by_key(|e| (e.span.start, e.span.end));
    // From the back, so that the offsets inside a replacement stay right.
    parens.sort_by_key(|p| std::cmp::Reverse(p.span.start));
    let mut own: Vec<Edit> = Vec::new();
    for p in parens {
        let at = p.span.start;
        if let Some(i) = regions.iter().position(|&(a, b)| a <= at && at <= b) {
            local[i].put((at - regions[i].0) as usize, &p.replace);
            continue;
        }
        // Before the edits that end before it, the text is as it was.
        let delta: i64 = local
            .iter()
            .zip(regions)
            .filter(|(_, r)| r.1 < at)
            .map(|(e, _)| e.replace.len() as i64 - e.span.len() as i64)
            .sum();
        let before = (at as i64 - delta) as u32;
        match own.last_mut().filter(|e| e.span.start == before) {
            Some(e) => e.replace.insert_str(0, &p.replace),
            None => own.push(Edit::insert(p.span.file, before, p.replace)),
        }
    }
    local.extend(own);
    local
}
