//! The scans of a run of tokens that read no node (S-384, S-419): where a
//! bracket closes and what is directly in it, whether an arm goes on to its
//! `=>`, where an alternative of a pattern ends. The parser and the table of
//! the forms of other languages ([`crate::foreign`]) read a run of tokens
//! through them alike (D-15); what one token starts is [`crate::starts`].

use crate::token::{Token, TokenKind};

/// Where each bracket of a run of tokens closes, read once for the run
/// (R-401, R-403): what a scan from an opener to its closer would say, for
/// every opener, so that the failures of a file do not each scan on to its
/// end. Made at the first that wants it ([`Brackets::of`]).
pub(crate) struct Brackets {
    /// [`Brackets::contents`], by the position of the opener.
    contents: Vec<Option<(usize, bool, bool)>>,
    /// [`Brackets::closing`], by the position of the opener.
    closing: Vec<Option<usize>>,
    /// The openers no closer closes, whatever the kinds, in order: those
    /// left open at the end of the file ([`Brackets::scan_end`]).
    unclosed: Vec<usize>,
}

impl Brackets {
    /// The table of `tokens` in `cell`, made at the first that wants it.
    pub(crate) fn of<'a>(cell: &'a std::cell::OnceCell<Brackets>, tokens: &[Token]) -> &'a Brackets {
        cell.get_or_init(|| Brackets::new(tokens))
    }

    /// One pass: a stack of the openers of any kind gives the contents, and
    /// one paired by kind ([`pair`]) the closing; a closer that closes
    /// another than the innermost there closes none of those open.
    pub(crate) fn new(tokens: &[Token]) -> Brackets {
        #[cfg(test)]
        MADE.set(MADE.get() + 1);
        let mut b =
            Brackets { contents: vec![None; tokens.len()], closing: vec![None; tokens.len()], unclosed: Vec::new() };
        let (mut any, mut kinds) = (Vec::<(usize, bool, bool)>::new(), OpenBrackets::default());
        for (i, t) in tokens.iter().enumerate() {
            #[cfg(test)]
            WALKED.set(WALKED.get() + 1);
            match t.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                    any.push((i, false, false));
                    pair(&mut kinds, tokens, i, 0);
                }
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    if let Some((o, comma, semi)) = any.pop() {
                        b.contents[o] = (t.kind == TokenKind::RBracket).then_some((i, comma, semi));
                    }
                    let innermost = kinds.last().copied();
                    match pair(&mut kinds, tokens, i, 0) {
                        Some(o) if Some(o) == innermost => b.closing[o] = Some(i),
                        _ => kinds.truncate(0),
                    }
                }
                TokenKind::Comma | TokenKind::Semi => {
                    if let Some(top) = any.last_mut() {
                        *(if t.kind == TokenKind::Comma { &mut top.1 } else { &mut top.2 }) = true;
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
        }
        b.unclosed = any.into_iter().map(|(o, ..)| o).collect();
        b
    }

    /// Where a scan by the depth from `from` ends (R-410): after the first
    /// opener from there that no closer closes, whatever the kinds (every
    /// token after it is inside it, so the scan reaches its depth again
    /// nowhere after it), else at the end of the file. The one judgment of
    /// where such a scan may stop, for the parser and the table.
    pub(crate) fn scan_end(&self, from: usize) -> usize {
        let k = self.unclosed.partition_point(|&o| o < from);
        self.unclosed.get(k).map_or(self.closing.len(), |o| o + 1)
    }

    /// The `]` that closes the `[` at `open`, the brackets in it closing one
    /// another whatever their kinds, and whether a `,` and a `;` are directly
    /// in it. None when another closer closes it, at the end of the file, and
    /// at any token that opens nothing.
    pub(crate) fn contents(&self, open: usize) -> Option<(usize, bool, bool)> {
        self.contents.get(open).copied().flatten()
    }

    /// The bracket that closes the one at `open`: the closer of its kind, the
    /// brackets in it paired by kind too (§2.5). None when `open` is no
    /// opening bracket, when a closer of another kind comes first
    /// (`pub(crate]` closes nothing), and at the end of the file. The one
    /// reading of where a bracket closes by kind, for the parser and the table
    /// of the forms of other languages ([`closing_on_line`] on a line).
    pub(crate) fn closing(&self, open: usize) -> Option<usize> {
        self.closing.get(open).copied().flatten()
    }
}

#[cfg(test)]
thread_local! {
    /// The tables [`Brackets::new`] made on this thread.
    pub(crate) static MADE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// The tokens the tables, [`closing_on_line`] and the scans of the
    /// patterns ([`pattern_alternative`], [`arm_ahead`], the guard forms' reading of an arm)
    /// went through on this thread: the tests see that the failures of a
    /// file do not each scan it.
    pub(crate) static WALKED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The bracket that closes the `(`, `[` or `{` at `open` when nothing but
/// line breaks and comments is between them (the code tokens): the empty
/// brackets of §2.5 (S-513) and the empty list of a `use` (§15.1, S-515).
/// The one judgment of an empty list, for the parser ([`crate::parser`]'s
/// `refuse_empty` and `parse_use`) and the table of the forms of other
/// languages (`Detached::joins`).
pub(crate) fn empty_brackets(tokens: &[Token], open: usize) -> Option<usize> {
    let close = match tokens.get(open)?.kind {
        TokenKind::LParen => TokenKind::RParen,
        TokenKind::LBracket => TokenKind::RBracket,
        TokenKind::LBrace => TokenKind::RBrace,
        _ => return None,
    };
    (open + 1..tokens.len())
        .find(|&k| tokens[k].kind != TokenKind::Newline && !tokens[k].kind.is_comment())
        .filter(|&k| tokens[k].kind == close)
}

/// [`Brackets::closing`] on the line of `open` (the code tokens, in which a line break
/// is a token in brackets too; none when a line break comes first): a form
/// of one line (§18.1, S-435).
pub(crate) fn closing_on_line(tokens: &[Token], open: usize) -> Option<usize> {
    scan_closing(tokens, open, true)
}

/// The scan from `open` to its closer (on its line when `on_line`): the
/// reading [`Brackets::closing`] makes for every opener at once.
fn scan_closing(tokens: &[Token], open: usize, on_line: bool) -> Option<usize> {
    closer(tokens.get(open)?.kind)?;
    let mut brackets = OpenBrackets::default();
    for (i, t) in tokens.iter().enumerate().skip(open) {
        #[cfg(test)]
        WALKED.set(WALKED.get() + 1);
        let innermost = brackets.last().copied();
        let closed = pair(&mut brackets, tokens, i, 0);
        match t.kind {
            // A closer of another kind first: it closes none, or one around the innermost.
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if closed != innermost => return None,
            _ if closed == Some(open) => return Some(i),
            TokenKind::Newline if on_line => return None,
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The brackets left open, innermost last (their positions in the tokens),
/// with where in them the openers of each kind are (R-409): a closer finds
/// the innermost opener of its kind without walking those open, so that a
/// line of closers that close nothing is read in linear time. It reads as
/// the slice of the positions; [`pair`] and [`OpenBrackets::truncate`]
/// change it.
#[derive(Clone, Default)]
pub(crate) struct OpenBrackets {
    at: Vec<usize>,
    /// For each kind (as in [`OPENERS`]), the indices in `at` of its openers, ascending.
    of: [Vec<usize>; 3],
}

impl std::ops::Deref for OpenBrackets {
    type Target = [usize];
    fn deref(&self) -> &[usize] {
        &self.at
    }
}

impl OpenBrackets {
    /// Keep the `k` outermost brackets open.
    pub(crate) fn truncate(&mut self, k: usize) {
        self.at.truncate(k);
        for of in &mut self.of {
            while of.last().is_some_and(|&j| j >= k) {
                of.pop();
            }
        }
    }
}

/// Read the token at `i` on the brackets left open, `open` (their positions;
/// those above `base` are of the run read): an opener is opened, and a
/// closer closes the innermost opener of its kind above `base`, with the
/// brackets opened inside it and left open (`f(a }` closes the `{` and the
/// `(`). The opener a closer closed; none for one that matches none (it
/// closes nothing) and for any other token. The one judgment of which
/// bracket a closer closes, for the parser and [`Brackets::closing`].
pub(crate) fn pair(open: &mut OpenBrackets, tokens: &[Token], i: usize, base: usize) -> Option<usize> {
    // A token that closes nothing, without looking at those open (R-403).
    let kind = tokens[i].kind;
    let c = OPENERS.iter().position(|&o| o == kind || closer(o) == Some(kind))?;
    if OPENERS[c] == kind {
        open.of[c].push(open.at.len());
        open.at.push(i);
        return None;
    }
    let k = *open.of[c].last().filter(|&&k| k >= base)?;
    let opener = open.at[k];
    open.truncate(k);
    Some(opener)
}

/// Whether the brackets of `tokens` close among themselves, in order.
pub(crate) fn balanced(tokens: &[Token]) -> bool {
    let mut open = Vec::new();
    let closes = |k| OPENERS.iter().any(|&o| closer(o) == Some(k));
    tokens.iter().all(|t| match closer(t.kind) {
        Some(c) => {
            open.push(c);
            true
        }
        None => !closes(t.kind) || open.pop() == Some(t.kind),
    }) && open.is_empty()
}

/// The opening brackets.
const OPENERS: [TokenKind; 3] = [TokenKind::LParen, TokenKind::LBracket, TokenKind::LBrace];

/// The closer of an opening bracket.
fn closer(kind: TokenKind) -> Option<TokenKind> {
    match kind {
        TokenKind::LParen => Some(TokenKind::RParen),
        TokenKind::LBracket => Some(TokenKind::RBracket),
        TokenKind::LBrace => Some(TokenKind::RBrace),
        _ => None,
    }
}

/// Whether an arm goes on from token `i` to its `=>`: a `=>` at the depth of
/// `i` comes before the next `,` or `}` there (S-386, S-419). The scan of the
/// tokens, which reads no element on (S-384): a symbol at the head of the
/// line that starts it is no binary operator of the arm before, and the
/// line break before an opener there is no gap inside a postfix. It stops
/// where the table says no `=>` comes at that depth ([`Brackets::scan_end`]).
pub(crate) fn arm_ahead(tokens: &[Token], brackets: &Brackets, i: usize) -> bool {
    let mut depth = 0u32;
    for t in &tokens[i..brackets.scan_end(i)] {
        #[cfg(test)]
        WALKED.set(WALKED.get() + 1);
        match t.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth == 0 => return false,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
            TokenKind::Comma if depth == 0 => return false,
            TokenKind::FatArrow if depth == 0 => return true,
            TokenKind::Eof => return false,
            _ => {}
        }
    }
    false
}

/// The alternative of a pattern whose tokens (no comment; newlines kept)
/// are `kinds`: where it ends (the first `|`, `if`, `=>`, `,`, `@`, `:`,
/// `=`, `in` or newline outside brackets, a closing bracket of none of its
/// own, or the end of the file) and the first range symbol outside brackets
/// before that, as positions among the tokens that are no newline (spec §7,
/// S-341: the ends of a range pattern are read as the ends of a range in a
/// header, and end there). The newlines before the alternative do not end
/// it, nor one after a binary operator (§2.5, as in an expression). The one
/// reading of a range in a pattern: the parser fails at it, and the table
/// of the forms reads its ends ([`crate::foreign`]).
pub(crate) fn pattern_alternative(kinds: impl Iterator<Item = TokenKind>) -> (usize, Option<usize>) {
    use TokenKind::*;
    let mut depth = 0u32;
    let mut range = None;
    let mut n = 0;
    let mut last = Eof;
    for k in kinds {
        #[cfg(test)]
        WALKED.set(WALKED.get() + 1);
        match k {
            Newline if n == 0 || depth > 0 || last.binop().is_some() => continue,
            Eof | Newline => break,
            LParen | LBracket | LBrace => depth += 1,
            RParen | RBracket | RBrace if depth == 0 => break,
            RParen | RBracket | RBrace => depth -= 1,
            Pipe | KwIf | FatArrow | Comma | At | Colon | Eq | KwIn if depth == 0 => break,
            _ if depth == 0 && range.is_none() && !k.range_readings().is_empty() => range = Some(n),
            _ => {}
        }
        last = k;
        n += 1;
    }
    (n, range)
}
