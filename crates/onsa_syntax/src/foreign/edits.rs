//! The edits of the candidates that move code up to the line before it
//! ([`move_up`], S-216: the parser's E0003 and the rows), that move a symbol
//! to the line of its partner (S-216, S-369, S-353, S-385), that write a
//! word next to code (R-205) and that take code out between two tokens
//! ([`apart`]), and whether such an edit joins two tokens ([`joining`]): the
//! one place of each.

use onsa_diag::{Edit, FileId, Fix, Span};

use super::Cursor;
use crate::token::{Token, TokenKind};

/// The candidate that moves `next` up to the line that ends at `end`, with
/// `sep` between them (S-216: the E0003 of `else`, the line break before a
/// postfix opener). With only blanks and line breaks between, they become
/// `sep`. Comments between and after it are kept and keep their order: the code of
/// `next`'s line (up to a comment or the end of the line) moves to `end`,
/// before the comment of that line, and the line of `next` is removed when
/// nothing else is left on it (W3-02/b 4).
pub(crate) fn move_up(file: FileId, text: &str, all: &[Token], title: &str, end: u32, next: Token, sep: &str) -> Fix {
    let at = all.partition_point(|t| t.span.start < next.span.start);
    let comment = |t: &Token| t.kind.is_line_comment();
    let between = all[..at].iter().rev().take_while(|t| t.span.start >= end);
    let rest = &all[at..];
    let after = rest.iter().take_while(|t| !matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
    if !between.clone().any(comment) && !after.clone().any(comment) {
        return Fix::replace(title, Span::new(file, end, next.span.start), sep);
    }
    // The code of `next`'s line: up to a comment, a newline or the end.
    let code_len = rest
        .iter()
        .position(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof) || t.kind.is_line_comment())
        .unwrap_or(rest.len());
    let code_end =
        rest[..code_len].iter().rev().find(|t| t.kind != TokenKind::Whitespace).map_or(next.span.end, |t| t.span.end);
    let moved = &text[next.span.start as usize..code_end as usize];
    let after = rest[code_len..].first().copied();
    let removed = match after.map(|t| t.kind) {
        // Nothing else on the line: remove the line, its indentation and its newline.
        Some(TokenKind::Newline) | Some(TokenKind::Eof) | None => {
            let line_start = match all[at.saturating_sub(1)] {
                t if at > 0 && t.kind == TokenKind::Whitespace => t.span.start,
                _ => next.span.start,
            };
            Span::new(file, line_start, after.map_or(code_end, |t| t.span.end))
        }
        // A comment stays on the line, after the indentation.
        Some(_) => Span::new(file, next.span.start, after.map_or(code_end, |t| t.span.start)),
    };
    Fix::new(title, vec![Edit::insert(file, end, format!("{sep}{moved}")), Edit::delete(removed)])
}

/// The candidate that takes out the blanks `blanks` on the line of a postfix
/// symbol after its operand (a `(` or `[` that opens a list, a `?`, a member
/// `.`; §2.5, S-89, S-203): only the blanks change (§18.1, R-214). The one
/// place of those candidates.
pub(super) fn take_out_blanks(title: &str, blanks: Vec<Span>) -> Fix {
    Fix::new(title, blanks.into_iter().map(Edit::delete).collect())
}

/// The insertions of the candidates that write a word next to code
/// ([`insert_apart`]), by place and text: [`apart`] puts the blanks they
/// need in a candidate that a check reports.
#[derive(Debug, Default)]
pub(crate) struct Insertions(std::collections::BTreeSet<(u32, String)>);

impl Insertions {
    fn holds(&self, e: &Edit) -> bool {
        e.span.is_empty() && self.0.contains(&(e.span.start, e.replace.clone()))
    }
}

/// The edit that inserts `s` at `offset` apart from the tokens around it,
/// marked in `marks`: a blank goes between `s` and a token it would join
/// ([`apart`]; R-205: ` at a` before `e` would read as ` at ae`). The one
/// insertion of the candidates that write a word next to code. The judgment
/// waits for the candidates a check reports: a line may hold many
/// diagnostics, of which one is reported.
pub(super) fn insert_apart(file: FileId, offset: u32, s: &str, marks: &mut Insertions) -> Edit {
    marks.0.insert((offset, s.to_string()));
    Edit::insert(file, offset, s)
}

/// The candidate `fix` with each edit that takes text out and joins the
/// tokens round it ([`joining`]) replaced with a blank (`impl[]S` is
/// `impl S`, not `implS`; `Some()if` is `Some if`; `0 /& //` is `0 / //`,
/// not the doc comment `///`), and each insertion of [`insert_apart`]
/// (`marks`) with a blank on the side where it joins: the reading outside the
/// edits stays (§18.1). `tokens` are those of the file `text`. The one place
/// of it, for every candidate of the syntax stage that a check reports
/// (`crate::operands::complete`); `joining` reads the candidate once.
pub(crate) fn apart(file: FileId, text: &str, tokens: &[Token], fix: Fix, marks: &Insertions) -> Fix {
    let taken = |e: &Edit| e.replace.is_empty() && !e.span.is_empty() && e.span.file == file;
    let asked = |e: &Edit| {
        let (l, r) = around(tokens, e);
        (taken(e) && (l.is_some() || r.is_some())) || (e.span.file == file && marks.holds(e))
    };
    if !fix.edits().iter().any(asked) {
        return fix;
    }
    let joins = joining(file, text, tokens, fix.edits());
    let edits = (fix.edits().iter().zip(joins))
        .map(|(e, j)| match () {
            _ if taken(e) && j.any() => Edit::replace(e.span, " "),
            _ if e.span.file == file && marks.holds(e) && j.any() => {
                let (before, after) = (if j.before { " " } else { "" }, if j.after { " " } else { "" });
                Edit::insert(file, e.span.start, format!("{before}{}{after}", e.replace))
            }
            _ => e.clone(),
        })
        .collect();
    Fix::new(fix.title(), edits)
}

/// Which of the tokens right at an edit a candidate joins to the text round
/// them ([`joining`]).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Joins {
    /// The token that ends where the edit starts.
    pub before: bool,
    /// The token that starts where the edit ends.
    pub after: bool,
}

impl Joins {
    pub(crate) fn any(self) -> bool {
        self.before || self.after
    }
}

/// The tokens of code (no blank, line break or line comment) of `tokens`
/// that end where `e` starts and that start where it ends.
fn around(tokens: &[Token], e: &Edit) -> (Option<Token>, Option<Token>) {
    let code = |t: &&Token| !t.kind.is_trivia() && t.kind != TokenKind::Eof;
    let l = tokens.get(tokens.partition_point(|t| t.span.end < e.span.start));
    let r = tokens.get(tokens.partition_point(|t| t.span.start < e.span.end));
    (
        l.filter(|t| t.span.end == e.span.start).filter(code).copied(),
        r.filter(|t| t.span.start == e.span.end).filter(code).copied(),
    )
}

/// For each of `edits` (a candidate's, of the file `text` whose tokens of
/// all kinds are `all`), whether the token of code that ends where it starts
/// and the one that starts where it ends ([`around`]) are no longer read as
/// they were, alone and of their kind, after all the edits: whether they
/// join. The one judgment of whether two tokens join (D-15), for the
/// candidates that take text out ([`apart`], the blanks round a member `.`)
/// and that write a word ([`insert_apart`]).
///
/// The lexer itself reads the text after the edits, in its own context (a
/// tuple index after a `.` too): from the first token of the line of an edit
/// ([`crate::lexer::line_of`]) to the line break that ends the line of the
/// last edit of a run of edits whose lines meet, each run once. A token that
/// another edit changes is not asked about. [`lexed`] counts the bytes of
/// those lines or of the text lexed, the longer: the cost is linear in them
/// and in the edits.
pub(crate) fn joining(file: FileId, text: &str, all: &[Token], edits: &[Edit]) -> Vec<Joins> {
    let mut out = vec![Joins::default(); edits.len()];
    let mut order: Vec<usize> = (0..edits.len()).filter(|&i| edits[i].span.file == file).collect();
    order.sort_by_key(|&i| (edits[i].span.start, edits[i].span.end));
    // The end of the line break after `at` (or of the text).
    let line_end = |at: u32| {
        let k = all.partition_point(|t| t.span.start < at);
        all[k..]
            .iter()
            .find(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof))
            .map_or(text.len() as u32, |t| t.span.end)
    };
    let mut i = 0;
    while i < order.len() {
        // A run of edits whose lines meet: the lines of the first to the end of the last.
        let first = &edits[order[i]];
        let start = all[crate::lexer::line_of(all, all.partition_point(|t| t.span.end < first.span.start))].span.start;
        let mut end = start;
        let mut j = i;
        while j < order.len() && (j == i || edits[order[j]].span.start < end) {
            let e = &edits[order[j]];
            let reach = around(all, e).1.map_or(e.span.end, |r| r.span.end);
            if reach >= end {
                end = line_end(reach);
            }
            j += 1;
        }
        let run = &order[i..j];
        i = j;
        let local: Vec<Edit> = run
            .iter()
            .map(|&k| {
                Edit::replace(
                    Span::new(file, edits[k].span.start - start, edits[k].span.end - start),
                    &edits[k].replace,
                )
            })
            .collect();
        // Edits that overlap: the check of the candidates reports them.
        let Ok(after) = onsa_diag::apply_text(&text[start as usize..end as usize], &local.iter().collect::<Vec<_>>())
        else {
            continue;
        };
        LEXED.set(LEXED.get() + after.len().max((end - start) as usize));
        let read: Vec<(u32, u32, TokenKind)> =
            crate::lex(file, &after).tokens.iter().map(|t| (t.span.start, t.span.end, t.kind)).collect();
        let kept = |t: Token, at: u32| {
            let len = t.span.len();
            read.binary_search_by_key(&at, |&(a, _, _)| a).is_ok_and(|k| read[k] == (at, at + len, t.kind))
        };
        // The shift of the text from the start of the run, before each edit.
        let mut shift: i64 = -(start as i64);
        for (n, &k) in run.iter().enumerate() {
            let e = &edits[k];
            let (l, r) = around(all, e);
            let prev_end = n.checked_sub(1).map(|p| edits[run[p]].span.end);
            let next_start = run.get(n + 1).map(|&q| edits[q].span.start);
            let moved = |at: u32, by: i64| (at as i64 + by) as u32;
            let after_e = shift + e.replace.len() as i64 - e.span.len() as i64;
            out[k] = Joins {
                before: l.is_some_and(|l| {
                    prev_end.is_none_or(|p| p <= l.span.start) && !kept(l, moved(l.span.start, shift))
                }),
                after: r.is_some_and(|r| {
                    next_start.is_none_or(|q| r.span.end <= q) && !kept(r, moved(r.span.start, after_e))
                }),
            };
            shift = after_e;
        }
    }
    out
}

thread_local! {
    /// The bytes [`joining`] read on this thread ([`lexed`]).
    static LEXED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The bytes [`joining`] has read on this thread, the lines and the text
/// lexed: [`crate::parse`] puts those of a file in
/// [`crate::CandidateReads::lexed`], the rows' (a blank round a `.`) and
/// those of the candidates reported alike.
pub(crate) fn lexed() -> usize {
    LEXED.get()
}

/// The full-list index of the parser's token `i`, and the line of it: its
/// line holds nothing but it (blanks aside).
fn alone_on_its_line(c: &Cursor, i: usize) -> Option<Span> {
    let k = c.full[i] as usize;
    let mut a = k;
    if a > 0 && c.all[a - 1].kind == TokenKind::Whitespace {
        a -= 1;
    }
    let starts = a == 0 || c.all[a - 1].kind == TokenKind::Newline;
    let mut b = k + 1;
    if c.all.get(b).is_some_and(|t| t.kind == TokenKind::Whitespace) {
        b += 1;
    }
    let ends = c.all.get(b).is_none_or(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
    // The line and its newline (the line of the end of the file has none).
    let end = c.all.get(b).filter(|t| t.kind == TokenKind::Newline).map_or(c.span(i).end, |t| t.span.end);
    (starts && ends).then(|| Span::new(c.file, c.all[a].span.start, end))
}

/// The candidate that moves the symbol `i` (`?`, the `~` of `if~`) up to the
/// end of the code before it, written against it, before the comment of
/// that line (S-216, S-369, S-385). What follows the symbol on its line stays
/// there; a line left empty goes.
pub(super) fn move_token_up(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let s = c.span(i);
    move_token_up_as(c, title, i, &c.text[s.start as usize..s.end as usize])
}

/// [`move_token_up`], the symbol written as `symbol` where it goes (` +`
/// after a blank for a binary operator, ` ..<` for `..`, S-124, S-335).
pub(super) fn move_token_up_as(c: &Cursor, title: &str, i: usize, symbol: &str) -> Option<Fix> {
    let prev = c.sig_before(i)?;
    let removed = alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize + 1;
        let end = c.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map_or(c.span(i).end, |t| t.span.end);
        Span::new(c.file, c.span(i).start, end)
    });
    Some(Fix::new(title, vec![Edit::insert(c.file, c.span(prev).end, symbol), Edit::delete(removed)]))
}

/// The candidate that moves the symbol `i` at the end of its line (a member
/// `.`, a prefix `-` / `!` / `^`) down to the token after it, written
/// against it (S-353, S-369). The comments and blank lines between stay; the
/// blanks before the symbol go with it, and a line left empty goes.
pub(super) fn move_token_down(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let next = c.sig_after(i);
    if next == i || c.kind(next) == TokenKind::Eof {
        return None;
    }
    let removed = alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize;
        let start = k.checked_sub(1).map(|p| c.all[p]).filter(|t| t.kind == TokenKind::Whitespace);
        Span::new(c.file, start.map_or(c.span(i).start, |t| t.span.start), c.span(i).end)
    });
    let s = c.span(i);
    let symbol = &c.text[s.start as usize..s.end as usize];
    Some(Fix::new(title, vec![Edit::delete(removed), Edit::insert(c.file, c.span(next).start, symbol)]))
}
