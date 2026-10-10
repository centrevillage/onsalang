//! The lines and blanks of §2.5 that the parser and the table of the forms
//! of other languages ([`crate::foreign`]) judge alike (D-15): the postfix
//! openers that a blank or a line break keeps apart from the token before
//! them ([`Detached`], S-89), the missing `,` between two elements of a list
//! ([`list_fixes`], S-384, S-387), and the candidate that moves code up to
//! the end of the line before it ([`move_up`], S-216).

use onsa_diag::{Edit, FileId, Fix, Span};

use crate::cst::NodeKind;
use crate::foreign::Cursor;
use crate::token::{Gap, Token, TokenKind};

/// A postfix opener (`(`, `[`, or the mark `!` / `~` before a `(`) that the
/// parser did not read on, because a blank or a line break is before it
/// (§2.5, S-89): the grammar fails where it fails, and the table reads this
/// at that failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Detached {
    /// The opener, an index of the parser's tokens.
    pub at: usize,
    /// The token before it ends a path of names (§6.1: what a callee is,
    /// [`crate::foreign::callee_by_name`]; a name of a declaration, a type,
    /// a pattern or an attribute is one), S-399.
    pub by_name: bool,
    /// The opener follows an expression (else a declaration, a type, a
    /// pattern or an attribute).
    pub expr: bool,
    /// The list is required there (`Parser::opens`): a line break before
    /// the opener is no next element either.
    pub required: bool,
}

impl Detached {
    /// Whether the code with the gap taken out reads as the postfix it would
    /// be (S-373, S-399, read from the tokens): a `(` or a mark after a path
    /// of names; a `[` whose list closes, is not empty and holds no `;` (an
    /// array, `[T; N]`), and, after an expression, holds no `,` either
    /// (`xs[0, 1]` is no index).
    pub(crate) fn joins(self, tokens: &[Token]) -> bool {
        match tokens[self.at].kind {
            TokenKind::LParen | TokenKind::Bang | TokenKind::Tilde => self.by_name,
            TokenKind::LBracket => {
                let Some((close, comma, semi)) = bracket_contents(tokens, self.at) else { return false };
                close > self.at + 1 && !semi && !(self.expr && comma)
            }
            _ => false,
        }
    }
}

/// The `]` that closes the `[` at `open`, and whether a `,` and a `;` are
/// directly in it.
pub(crate) fn bracket_contents(tokens: &[Token], open: usize) -> Option<(usize, bool, bool)> {
    let (mut depth, mut comma, mut semi) = (0u32, false, false);
    for (i, t) in tokens.iter().enumerate().skip(open) {
        match t.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (t.kind == TokenKind::RBracket).then_some((i, comma, semi));
                }
            }
            TokenKind::Comma if depth == 1 => comma = true,
            TokenKind::Semi if depth == 1 => semi = true,
            TokenKind::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The candidate that takes out the blank or the line break before the
/// opener at `c.at` (S-89, S-399): its line moves up to the token before it
/// ([`move_up`], S-216). The one place of that candidate.
pub(crate) fn join_fix(c: &Cursor) -> Option<Fix> {
    let prev = c.sig_before(c.at)?;
    let title = if c.gap(c.at) == Gap::Newline { "remove the line break" } else { "remove the space" };
    Some(move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[c.at], ""))
}

/// Whether a token of `kind` may start an element of a list of `list`: the
/// lexical condition of the missing `,` (S-384: the next element is not read
/// on to see whether it is one). A `~` starts no element.
pub(crate) fn starts_element(list: NodeKind, kind: TokenKind) -> bool {
    use TokenKind::*;
    let ty = matches!(kind, Ident | KwSelfType | LParen | LBracket | KwFn | KwRt);
    let pattern =
        matches!(kind, Underscore | Minus | Int | Float | Char | Str | KwTrue | KwFalse | LParen | Ident | KwSelfType);
    let expr = crate::parser::starts_operand(kind);
    match list {
        NodeKind::ArgList => expr || matches!(kind, KwMove | KwInout),
        NodeKind::TupleExpr | NodeKind::ArrayExpr => expr || kind == KwMove,
        NodeKind::StructLitFields | NodeKind::VariantList | NodeKind::UseNames | NodeKind::EffectRow => kind == Ident,
        NodeKind::FieldList => matches!(kind, Ident | KwPub),
        NodeKind::ParamList => matches!(kind, Ident | KwSelf | Underscore | At | KwInout | KwMove),
        NodeKind::GenericParams => matches!(kind, Ident | KwConst),
        NodeKind::TypeArgs => ty || expr,
        NodeKind::TupleType | NodeKind::VariantFields => ty,
        NodeKind::FnTypeParams => ty || matches!(kind, KwInout | KwMove),
        NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::MatchArms => pattern,
        NodeKind::StructPat => matches!(kind, Ident | DotDot),
        NodeKind::AttrArgs => matches!(kind, Ident | Str),
        _ => false,
    }
}

/// The candidates of the general E0002 at the token after an element of a
/// list of `list`, where a `,` or the closing bracket goes (§2.5), in the
/// order of the decisions (out of a list, `None`: only the opener after a
/// line break has its candidate, S-89):
///
/// - two string literals next to each other (S-388): the `,`, and the one
///   literal they make;
/// - an opener after a line break (S-89, S-373), or after a blank when the
///   token before is no path of names (S-399): the `,` when the opener
///   starts an element, and the gap taken out when that reads;
/// - else the `,` when the token starts an element (S-384, S-387), whatever
///   is between the elements.
///
/// The `,` goes right after the last token of the element, before the
/// comment of its line.
pub(crate) fn list_fixes(c: &Cursor, list: Option<NodeKind>) -> Vec<Fix> {
    let Some(prev) = c.sig_before(c.at) else { return Vec::new() };
    let mut fixes = Vec::new();
    let declaration = crate::parser::declares_a_function(c.kind(c.at), c.kind(c.sig_after(c.at)));
    if list.is_some_and(|l| starts_element(l, c.kind(c.at))) && !declaration {
        fixes.push(Fix::new("write the `,` between the elements", vec![Edit::insert(c.file, c.span(prev).end, ",")]));
    }
    let strings = c.kind(c.at) == TokenKind::Str && c.kind(prev) == TokenKind::Str;
    if strings && list.is_some() {
        fixes.extend(merge_strings(c, prev));
    } else if c.detached.is_some_and(|d| d.at == c.at && d.joins(c.tokens)) {
        fixes.extend(join_fix(c));
    }
    fixes
}

/// The two string literals `prev` and `c.at` as one (S-388): the text of the
/// second goes before the closing `"` of the first, and the token of the
/// second goes; the other tokens and the comments stay on their lines (as
/// S-216 moves code). Only two literals that the lexer read whole (closed,
/// with no error in them, [`Cursor::literal_ok`]): a literal that does not
/// close is the lexer's E0001.
fn merge_strings(c: &Cursor, prev: usize) -> Option<Fix> {
    if !(c.literal_ok(prev) && c.literal_ok(c.at)) {
        return None;
    }
    let (first, second) = (c.span(prev), c.span(c.at));
    let text = |s: Span| &c.text[s.start as usize..s.end as usize];
    // A closed literal starts and ends with the one-byte `"`.
    let one = format!("{}{}", &text(first)[..text(first).len() - 1], &text(second)[1..]);
    Some(Fix::new("make the two literals one", vec![Edit::replace(first, one), Edit::delete(second)]))
}

/// The candidate that moves `next` up to the line that ends at `end`, with
/// `sep` between them (S-216: the E0003 of `else`, the line break before a
/// postfix opener). With only blanks and line breaks between, they become
/// `sep`. Comments between are kept and keep their order: the code of
/// `next`'s line (up to a comment or the end of the line) moves to `end`,
/// before the comment of that line, and the line of `next` is removed when
/// nothing else is left on it (W3-02/b 4).
pub(crate) fn move_up(file: FileId, text: &str, all: &[Token], title: &str, end: u32, next: Token, sep: &str) -> Fix {
    let at = all.partition_point(|t| t.span.start < next.span.start);
    let between = all[..at].iter().rev().take_while(|t| t.span.start >= end);
    if !between.clone().any(|t| matches!(t.kind, TokenKind::Comment | TokenKind::DocComment)) {
        return Fix::replace(title, Span::new(file, end, next.span.start), sep);
    }
    // The code of `next`'s line: up to a comment, a newline or the end.
    let rest = &all[at..];
    let code_len = rest
        .iter()
        .position(|t| {
            matches!(t.kind, TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment | TokenKind::Eof)
        })
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

/// Whether a token of `kind` ends an operand: what a postfix `?` or a binary
/// operator follows (a name, a literal, a closing bracket, `?`).
pub(crate) fn ends_operand(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Ident
            | KwSelf
            | KwSelfType
            | Int
            | Float
            | Char
            | Str
            | KwTrue
            | KwFalse
            | RParen
            | RBracket
            | RBrace
            | Question
    )
}

/// The edit that inserts `s` at `offset` of `text` apart from the tokens
/// around it: a blank goes between `s` and a name or a number it would
/// touch (R-205: ` at a` before `e` would read as ` at ae`). The one
/// insertion of the candidates that write a word next to code.
pub(crate) fn insert_apart(file: FileId, text: &str, offset: u32, s: &str) -> Edit {
    let word = |c: Option<char>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
    let before = word(text[..offset as usize].chars().next_back()) && word(s.chars().next());
    let after = word(text[offset as usize..].chars().next()) && word(s.chars().next_back());
    let s = format!("{}{s}{}", if before { " " } else { "" }, if after { " " } else { "" });
    Edit::insert(file, offset, s)
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
pub(crate) fn move_token_up(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
    let prev = c.sig_before(i)?;
    let removed = alone_on_its_line(c, i).unwrap_or_else(|| {
        let k = c.full[i] as usize + 1;
        let end = c.all.get(k).filter(|t| t.kind == TokenKind::Whitespace).map_or(c.span(i).end, |t| t.span.end);
        Span::new(c.file, c.span(i).start, end)
    });
    let s = c.span(i);
    let symbol = &c.text[s.start as usize..s.end as usize];
    Some(Fix::new(title, vec![Edit::insert(c.file, c.span(prev).end, symbol), Edit::delete(removed)]))
}

/// The candidate that moves the symbol `i` at the end of its line (a member
/// `.`, a prefix `-` / `!` / `^`) down to the token after it, written
/// against it (S-353, S-369). The comments and blank lines between stay; the
/// blanks before the symbol go with it, and a line left empty goes.
pub(crate) fn move_token_down(c: &Cursor, title: &str, i: usize) -> Option<Fix> {
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
