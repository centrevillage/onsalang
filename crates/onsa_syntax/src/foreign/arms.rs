//! The patterns of one arm written with `,` or the word `or` between them
//! (§7, S-402): `0, 1 =>` of Swift, Kotlin and Python, `0 or 1 =>` of C#.

use super::*;

/// The rows [`arm_patterns`] names ([`super::Matcher::many`]).
pub(super) const ARM_PATTERNS_ROWS: &[RowId] = &[RowId::ArmCommaPatterns, RowId::PatternOrWord];

/// The patterns of an arm with `,` or `or` between them, where the arm
/// wants its `=>` (§7, S-402). The arm is read from its first token to its
/// `if` or `=>` outside brackets, and every separator of the kind of the
/// first (all the `,` of the arm are one form) has a pattern starting after
/// it on its line; a line that ends elsewhere, a closing bracket of none of
/// its own or the end of the file stop the reading (the general E0002, as
/// the `,` before a line break, which may be the end of a forgotten body).
/// The candidates, when every pattern reads alone with no form of its own
/// and no error of the lexer: the choice (`0 | 1 =>`) and, after `,`, the
/// tuple (`(0, 1) =>`); else E0002 with the note.
pub(super) fn arm_patterns(c: &Cursor) -> Option<(RowId, Hit)> {
    let sep = |i: usize| match c.kind(c.at) {
        TokenKind::Comma => c.kind(i) == TokenKind::Comma,
        _ => c.is_ident(i, "or"),
    };
    let row = match c.kind(c.at) {
        TokenKind::Comma => RowId::ArmCommaPatterns,
        _ if c.is_ident(c.at, "or") => RowId::PatternOrWord,
        _ => return None,
    };
    let &(NodeKind::MatchArm, start) = c.open.last()? else { return None };
    let first = c.index_at(start);
    if first >= c.at || (first..c.at).any(|i| c.kind(i) == TokenKind::KwIf) {
        return None;
    }
    let mut seps = Vec::new();
    let mut depth = 0u32;
    let mut end = None;
    for i in c.at..c.brackets().scan_end(c.at) {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth == 0 => return None,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
            TokenKind::FatArrow | TokenKind::KwIf if depth == 0 => {
                end = Some(i);
                break;
            }
            TokenKind::Newline if depth == 0 && !c.lines.goes_on(i) => return None,
            TokenKind::Eof | TokenKind::Semi => return None,
            _ if depth == 0 && sep(i) => {
                let next = c.sig_after(i);
                let on_line = !(i + 1..next).any(|j| c.kind(j) == TokenKind::Newline);
                if !on_line || !crate::starts::starts_element(NodeKind::TuplePat, c.kind(next)) {
                    return None;
                }
                seps.push(i);
            }
            _ => {}
        }
    }
    let last = c.sig_before(end?)?;
    let span = c.file_span(c.span(first).start, c.span(last).end);
    let fixes =
        if read_alone(c, first, &seps, last) { choice_and_tuple(c, row, first, &seps, last, span) } else { Vec::new() };
    found(row, span, fixes)
}

/// Whether each pattern of the arm (`first..=last`, the separators `seps`)
/// reads alone ([`reads_alone`]), with no block comment in the arm.
fn read_alone(c: &Cursor, first: usize, seps: &[usize], last: usize) -> bool {
    let bounds = std::iter::once(first).chain(seps.iter().map(|&s| c.sig_after(s)));
    let ends = seps.iter().filter_map(|&s| c.sig_before(s)).chain([last]);
    (first..=last).all(|i| c.kind(i) != TokenKind::BlockComment)
        && seps.iter().all(|&s| c.sig_before(s).is_some_and(|b| b >= first))
        && bounds.zip(ends).all(|(a, b)| a <= b && reads_alone(c, a, b))
}

/// Whether the tokens `a..=b` (code) read alone as one pattern with no
/// guard form in it, and hold no error of the lexer and no integer that
/// fits no type (§18.1: a candidate that keeps them leaves no error of the
/// syntax stage). The one test of a pattern a candidate keeps (S-402, S-512).
pub(super) fn reads_alone(c: &Cursor, a: usize, b: usize) -> bool {
    let fine = |i: usize| match c.kind(i) {
        TokenKind::Int => crate::literal::int_value(c.src(i)).is_some(),
        _ => c.literal_ok(i),
    };
    let run = c.all[c.full[a] as usize..=c.full[b] as usize].to_vec();
    (a..=b).all(fine)
        && crate::parser::reads_as_pattern(c.file, c.text, run, c.literals, true).is_some_and(|(_, f)| f.is_empty())
}

/// The candidates of the patterns `first..=last` with the separators
/// `seps`: each separator a `|`, then, after `,`, the parentheses of one
/// tuple (dropped when they nest over the limit, §2.5).
fn choice_and_tuple(c: &Cursor, row: RowId, first: usize, seps: &[usize], last: usize, span: Span) -> Vec<Fix> {
    let bar = |s: usize| {
        let before = if c.space_before(s).is_none() { " " } else { "" };
        let after = if c.space_after(s).is_none() { " " } else { "" };
        Edit::replace(c.span(s), format!("{before}|{after}"))
    };
    let mut fixes = vec![Fix::new("write the patterns as a choice with `|`", seps.iter().map(|&s| bar(s)).collect())];
    if row == RowId::ArmCommaPatterns {
        let edits = vec![Edit::insert(c.file, c.span(first).start, "("), Edit::insert(c.file, c.span(last).end, ")")];
        let within = crate::units::Within::file(c.file, c.text, c.reach);
        if !crate::nesting::nests_too_deep(c.text, within, span, &edits, 1) {
            fixes.push(Fix::new("write the patterns as one tuple pattern", edits));
        }
    }
    fixes
}
