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
//! is dropped when it nests over the limit ([`groups::nests_too_deep`]) or
//! leaves more than the candidate alone did, less the E0013 of those
//! expressions (§18.1: a candidate that cannot keep the promise is not made;
//! another error of the unit stays as it was).
//!
//! [`crate::read`] completes no candidate, so the reading goes one level
//! deep; each reading is of the units a candidate touches, and one
//! diagnostic of a unit is reported, so the cost is the size of the file
//! times the candidates of a diagnostic ([`CandidateReads`]).

use std::collections::BTreeMap;

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::cst::Cst;
use crate::groups;
use crate::units::Units;

/// What the completion read again in a file: the text of the units (bytes,
/// one count per reading), the text lexed in the file to judge whether two
/// tokens join (`crate::foreign::lexed`: for the rows that take blanks out
/// and for the candidates reported, [`crate::foreign::apart`]), the
/// candidates dropped (a
/// completed one that left more diagnostics of the syntax stage than the
/// candidate alone did, less the E0013 it takes away) and those kept as they
/// are without a reading (no run of the units of one list,
/// [`Units::reading`]). The tests see them.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CandidateReads {
    pub bytes: usize,
    pub lexed: usize,
    pub dropped: usize,
    pub unread: usize,
}

/// The candidates of the diagnostics of the syntax stage that a check
/// reports among `diagnostics` (of the file `text` whose CST and units are
/// those), with the parentheses they need and apart from the tokens around
/// what they take out ([`crate::foreign::apart`]). E0013's own candidate is
/// those parentheses. A diagnostic left without a candidate takes the code
/// of [`Code::without_fixes`]; E0002 orders before the other codes at its
/// place, so it stays the one reported.
pub(crate) fn complete(
    text: &str,
    cst: &Cst,
    units: &Units,
    apart: &crate::foreign::Insertions,
    diagnostics: &mut [Diagnostic],
) -> CandidateReads {
    let reported: Vec<bool> =
        units.choose(&diagnostics.iter().collect::<Vec<_>>()).into_iter().map(|(_, c)| c).collect();
    let mut reads = CandidateReads::default();
    for (d, _) in diagnostics.iter_mut().zip(reported).filter(|(_, r)| *r) {
        if d.stage != Stage::Syntax || d.fixes.is_empty() {
            continue;
        }
        let file = d.span.file;
        let fixes: Vec<Fix> = (std::mem::take(&mut d.fixes).into_iter())
            .map(|f| crate::foreign::apart(file, text, cst.tokens(), f, apart))
            .collect();
        d.fixes = match d.code {
            Code::E0013 => fixes,
            _ => fixes.into_iter().filter_map(|f| completed(text, units, f, &mut reads)).collect(),
        };
        if d.fixes.is_empty() {
            d.code = d.code.without_fixes();
        }
    }
    reads
}

/// `fix` with the parentheses it needs, `None` when it leaves more with them
/// than [`keeps`] allows. A candidate whose edits touch no run of the units
/// of one list ([`Units::reading`]) is kept as it is.
fn completed(text: &str, units: &Units, fix: Fix, reads: &mut CandidateReads) -> Option<Fix> {
    let spans: Vec<Span> = fix.edits().iter().map(|e| e.span).collect();
    let Some(within) = units.reading(&spans) else {
        reads.unread += 1;
        return Some(fix);
    };
    let (file, own) = (within.span.file, within.of(text));
    let local: Vec<Edit> = fix.edits().iter().map(|e| within.local(e)).collect();
    let Ok((after, regions)) = applied(own, &local) else { return Some(fix) };
    reads.bytes += after.len();
    let alone = crate::read(file, &after, within.ctx);
    let touched = touched_operands(&alone, &regions);
    if touched.is_empty() {
        return Some(fix);
    }
    let operands: Vec<Span> = touched.iter().flat_map(|(_, o)| o.iter().copied()).collect();
    let local = composed(local, &regions, groups::parenthesizing(&operands).collect());
    let edits: Vec<Edit> = local.iter().map(|e| within.global(e)).collect();
    let deep = groups::nests_too_deep(text, within, within.span, &edits, operands.len() as u32);
    let Some((again, regions)) = applied(own, &local).ok().filter(|_| !deep) else {
        reads.dropped += 1;
        return None;
    };
    reads.bytes += again.len();
    if !keeps(&alone, touched.len(), &crate::read(file, &again, within.ctx), &regions) {
        reads.dropped += 1;
        return None;
    }
    Some(Fix::new(fix.title(), edits))
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

/// `text` with `edits` (sorted, apart), and the range each replacement
/// takes in the new text.
fn applied(text: &str, edits: &[Edit]) -> Result<(String, Vec<(u32, u32)>), String> {
    let mut edits: Vec<&Edit> = edits.iter().collect();
    onsa_diag::sort_edits(&mut edits);
    let after = onsa_diag::apply_text(text, &edits)?;
    let mut delta: i64 = 0;
    let regions = edits
        .iter()
        .map(|e| {
            let a = (e.span.start as i64 + delta) as u32;
            delta += e.replace.len() as i64 - e.span.len() as i64;
            (a, a + e.replace.len() as u32)
        })
        .collect();
    Ok((after, regions))
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
            local[i].replace.insert_str((at - regions[i].0) as usize, &p.replace);
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
