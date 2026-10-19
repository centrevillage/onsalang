//! The reading outside the edits, the minimal edits (the checks 4 and 5) and `same_code`.

use onsa_diag::{FileId, Span};
use onsa_syntax::Token;
use onsa_syntax::TokenKind;

use super::units::{Moved, falls_in, shift};

/// The lexical readings of one file before and after a candidate, read once
/// for the checks 4 and 5.
pub(crate) struct Readings<'a> {
    before: &'a str,
    after: &'a str,
    old: Vec<Token>,
    new: Vec<Token>,
}

impl<'a> Readings<'a> {
    pub(crate) fn of(file: FileId, before: &'a str, after: &'a str) -> Readings<'a> {
        let old = onsa_syntax::lex(file, before).tokens;
        let new = onsa_syntax::lex(file, after).tokens;
        Readings { before, after, old, new }
    }
}

/// Whitespace, newlines and the end: what the checks 4 and 5 do not compare.
fn blank(t: &Token) -> bool {
    matches!(t.kind, TokenKind::Whitespace | TokenKind::Newline | TokenKind::Eof)
}

/// The tokens of `tokens` (in the order of the text) that the range `r`
/// falls in, but blanks: by kind and text.
fn falling_in<'t>(tokens: &[Token], text: &'t str, r: Span) -> Vec<(TokenKind, &'t str)> {
    // The tokens that end before the range cannot hold it.
    let first = tokens.partition_point(|t| t.span.end < r.start);
    tokens[first..]
        .iter()
        .take_while(|t| t.span.start <= r.end)
        .filter(|t| !blank(t) && falls_in(r, t.span))
        .map(|t| {
            let s = &text[t.span.start as usize..t.span.end as usize];
            // The blanks at the end of a comment are not compared.
            (t.kind, if t.kind.is_comment() { s.trim_end() } else { s })
        })
        .collect()
}

/// The checks 4 and 5 of one file (the module's documentation): their
/// messages, each after `place` (`"in m.onsa, "` or none), and how many
/// edits the check 5 compared.
pub(super) fn edit_problems(read: &Readings, file: FileId, edits: &[Moved], place: &str) -> (Vec<String>, usize) {
    let mut out: Vec<String> = reading_difference_in(read, file, edits)
        .map(|diff| format!("the reading outside its edits changed: {place}{diff}"))
        .into_iter()
        .collect();
    let (shapes, compared) = not_minimal(read, file, edits);
    out.extend(shapes.into_iter().map(|m| format!("{place}{m}")));
    (out, compared)
}

/// The edits of `file` that are not minimal (the module's documentation, 5;
/// S-251), one message per edit (the first reason that holds), and how many
/// edits it compared (both sides not empty).
pub(crate) fn not_minimal(read: &Readings, file: FileId, edits: &[Moved]) -> (Vec<String>, usize) {
    let mut out = Vec::new();
    let mut compared = 0;
    for (i, e) in edits.iter().enumerate().filter(|(_, e)| e.before.file == file) {
        let old = falling_in(&read.old, read.before, e.before);
        let new = falling_in(&read.new, read.after, e.after);
        if old.is_empty() || new.is_empty() {
            continue;
        }
        compared += 1;
        let written: std::collections::HashSet<&(TokenKind, &str)> = new.iter().collect();
        let why = if let Some(c) = old.iter().find(|o| o.0.is_comment() && written.contains(o)) {
            format!("it holds the comment `{}` and writes it again (leave the comment outside the edit)", c.1)
        } else if old[0] == new[0] {
            format!("its first token `{}` stays (shrink the edit)", old[0].1)
        } else if old.last() == new.last() {
            format!("its last token `{}` stays (shrink the edit)", old[old.len() - 1].1)
        } else if let Some(c) = old.iter().find(|o| written.contains(o)) {
            format!("the token `{}` stays inside it (split it into two edits)", c.1)
        } else {
            continue;
        };
        let show = |v: &[(TokenKind, &str)]| v.iter().map(|t| t.1).collect::<Vec<_>>().join(" ");
        out.push(format!(
            "edit {} is not minimal (§18.1, S-251): {why}: it replaces `{}` with `{}`",
            i + 1,
            show(&old),
            show(&new)
        ));
    }
    (out, compared)
}

/// Where the lexical reading of the text outside the edits differs before
/// and after a candidate (the module's documentation, 4; S-302): the tokens
/// and comments no edit falls in, but blanks, with their kinds and ranges
/// (those before moved by the edits before them), in the order of the text.
pub(super) fn reading_difference(before: &str, after: &str, file: FileId, edits: &[Moved]) -> Option<String> {
    reading_difference_in(&Readings::of(file, before, after), file, edits)
}

/// [`reading_difference`] on the readings read already.
fn reading_difference_in(read: &Readings, file: FileId, edits: &[Moved]) -> Option<String> {
    let mine: Vec<Moved> = edits.iter().copied().filter(|e| e.before.file == file).collect();
    let old: Vec<(TokenKind, u32, u32)> = read
        .old
        .iter()
        .filter(|t| !blank(t) && !mine.iter().any(|e| falls_in(e.before, t.span)))
        .map(|t| (t.kind, shift(&mine, file, t.span.start, true), shift(&mine, file, t.span.end, false)))
        .collect();
    // The ranges of the replacements after the candidate.
    let new_ranges: Vec<Span> = mine.iter().map(|e| e.after).collect();
    let new: Vec<(TokenKind, u32, u32)> = read
        .new
        .iter()
        .filter(|t| !blank(t) && !new_ranges.iter().any(|r| falls_in(*r, t.span)))
        .map(|t| (t.kind, t.span.start, t.span.end))
        .collect();
    let i = (0..old.len().max(new.len())).find(|&i| old.get(i) != new.get(i))?;
    let after = read.after;
    let show = |text: &str, t: Option<&(TokenKind, u32, u32)>| {
        t.map_or("nothing".to_string(), |&(k, s, e)| format!("{k:?} `{}` at {s}..{e}", &text[s as usize..e as usize]))
    };
    Some(format!("token {} outside the edits: {} after, {} expected", i + 1, show(after, new.get(i)), {
        let t = old.get(i);
        t.map_or("nothing".to_string(), |&(k, s, e)| format!("{k:?} at {s}..{e}"))
    }))
}

/// The code of a text for `same_code`: every token but whitespace, newlines
/// and comments (block comments too: they are what a candidate of S-247
/// rewrites), with whether a line break lies between it and the token
/// before it (not before the first one: a comment may move above the first
/// line).
fn code_shape(text: &str) -> Vec<(TokenKind, &str, bool)> {
    let mut out = Vec::new();
    let mut line_break = false;
    for t in onsa_syntax::lex(FileId(0), text).tokens {
        match t.kind {
            TokenKind::Newline => line_break = true,
            k if k.is_comment() => {}
            TokenKind::Whitespace | TokenKind::Eof => {}
            kind => {
                let first = out.is_empty();
                out.push((kind, &text[t.span.start as usize..t.span.end as usize], line_break && !first));
                line_break = false;
            }
        }
    }
    out
}

/// Where the code of `after` first differs from that of `before` (`same_code`, S-247).
pub(super) fn code_difference(before: &str, after: &str) -> Option<String> {
    let (b, a) = (code_shape(before), code_shape(after));
    let i = (0..b.len().max(a.len())).find(|&i| b.get(i) != a.get(i))?;
    let token = |t: Option<&(TokenKind, &str, bool)>| t.map_or("the end".to_string(), |t| format!("`{}`", t.1));
    let (x, y) = (b.get(i), a.get(i));
    if x.map(|t| (t.0, t.1)) == y.map(|t| (t.0, t.1)) {
        let lb = |t: Option<&(TokenKind, &str, bool)>| if t.is_some_and(|t| t.2) { "a line break" } else { "none" };
        return Some(format!(
            "before {} (token {}): the line break changed: {} before, {} after",
            token(x),
            i + 1,
            lb(x),
            lb(y)
        ));
    }
    Some(format!("token {}: {} before, {} after (the code but comments changed)", i + 1, token(x), token(y)))
}
