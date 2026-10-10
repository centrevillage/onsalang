//! The lines and blanks of §2.5 that the parser and the table of the forms
//! of other languages ([`crate::foreign`]) judge alike (D-15): the postfix
//! openers that a blank or a line break keeps apart from the token before
//! them ([`Detached`], S-89), the missing `,` between two elements of a list
//! ([`list_fixes`], S-384, S-387), and the candidate that moves code up to
//! the end of the line before it ([`move_up`], S-216).

use onsa_diag::{Edit, FileId, Fix, Span};

use crate::cst::NodeKind;
use crate::foreign::{Cursor, Want};
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
///   is between the elements;
/// - in the arms of a `match`, a `-`, `|` or `+` that a `=>` follows starts
///   the next arm (S-386): the `,`, which takes a `+` out (S-405); a `- 1`
///   has none, as its blank is an error of its own.
///
/// The two candidates of an opener after a line break are only those that
/// the scan of the tokens reads (S-419): in the arms, the `,` when a `=>`
/// follows ([`arm_ahead`]) and the line break taken out when none does; in
/// a list of types only, a `[` starts an element when a `;` is in it.
///
/// The `,` goes right after the last token of the element, before the
/// comment of its line.
pub(crate) fn list_fixes(c: &Cursor, list: Option<NodeKind>) -> Vec<Fix> {
    let Some(prev) = c.sig_before(c.at) else { return Vec::new() };
    let kind = c.kind(c.at);
    let arms = list == Some(NodeKind::MatchArms);
    if arms && matches!(kind, TokenKind::Minus | TokenKind::Pipe | TokenKind::Plus) && arm_ahead(c, c.at) {
        let spaced = kind == TokenKind::Minus && c.gap_after(c.at).is_some();
        return if spaced { Vec::new() } else { vec![comma_before_sign(c, prev, c.at)] };
    }
    let mut fixes = Vec::new();
    let declaration = crate::parser::declares_a_function(kind, c.kind(c.sig_after(c.at)));
    let joins = c.detached.is_some_and(|d| d.at == c.at && d.joins(c.tokens));
    let types = matches!(list, Some(NodeKind::VariantFields | NodeKind::TupleType | NodeKind::FnTypeParams));
    let array =
        (kind != TokenKind::LBracket || !types || bracket_contents(c.tokens, c.at).is_some_and(|(_, _, semi)| semi))
            && !(list == Some(NodeKind::ArrayExpr) && array_repeats(c));
    let comma = !(arms && joins && !arm_ahead(c, c.at));
    if list.is_some_and(|l| starts_element(l, kind)) && !declaration && array && comma {
        fixes.push(Fix::new("write the `,` between the elements", vec![Edit::insert(c.file, c.span(prev).end, ",")]));
    }
    let strings = kind == TokenKind::Str && c.kind(prev) == TokenKind::Str;
    if strings && list.is_some() {
        fixes.extend(merge_strings(c, prev));
    } else if joins && !(arms && arm_ahead(c, c.at)) {
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
/// `sep`. Comments between and after it are kept and keep their order: the code of
/// `next`'s line (up to a comment or the end of the line) moves to `end`,
/// before the comment of that line, and the line of `next` is removed when
/// nothing else is left on it (W3-02/b 4).
pub(crate) fn move_up(file: FileId, text: &str, all: &[Token], title: &str, end: u32, next: Token, sep: &str) -> Fix {
    let at = all.partition_point(|t| t.span.start < next.span.start);
    let comment = |t: &Token| matches!(t.kind, TokenKind::Comment | TokenKind::DocComment);
    let between = all[..at].iter().rev().take_while(|t| t.span.start >= end);
    let rest = &all[at..];
    let after = rest.iter().take_while(|t| !matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
    if !between.clone().any(comment) && !after.clone().any(comment) {
        return Fix::replace(title, Span::new(file, end, next.span.start), sep);
    }
    // The code of `next`'s line: up to a comment, a newline or the end.
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

/// Whether a line break goes on with the line (§2.5, S-47, R-58, S-124,
/// S-335, S-374): `prev` is the last code token of the line (`before` the one
/// before it) and `next` the first of the next line, the lines of comments
/// and the blank lines passed. The line goes on after a binary operator (a
/// `-` / `^` only after an operand: a prefix one at the end of a line is the
/// error of S-369), `..<` / `..=`, `=` or `->`, and before a `.` or `uses`. A
/// line of attributes goes on too, which the tokens do not show
/// (`Parser::parse_attrs`, S-121). The one judgement of the parser
/// (`Parser::peek_index`), of its recovery (S-47) and of the table.
pub(crate) fn continues(before: Option<TokenKind>, prev: TokenKind, next: TokenKind) -> bool {
    use TokenKind::*;
    let binary = match prev {
        Minus | Caret => before.is_some_and(ends_operand),
        k => crate::lower::binop(k).is_some(),
    };
    binary || prev.range_end().is_some() || matches!(prev, Eq | Arrow) || matches!(next, Dot | KwUses)
}

/// For each token of a list without whitespace (the parser's), whether it is
/// a newline that goes on with the line ([`continues`]): one pass each way,
/// so the judgement is linear in the file however long a run of comment
/// lines and blank lines is.
pub(crate) fn line_breaks_going_on(tokens: &[Token]) -> Vec<bool> {
    let code = |k: TokenKind| !k.is_trivia();
    let mut next = vec![TokenKind::Eof; tokens.len()];
    let mut after = TokenKind::Eof;
    for (k, t) in tokens.iter().enumerate().rev() {
        if code(t.kind) {
            after = t.kind;
        }
        next[k] = after;
    }
    let (mut before, mut prev) = (None, None);
    let mut out = vec![false; tokens.len()];
    for (k, t) in tokens.iter().enumerate() {
        if t.kind == TokenKind::Newline {
            out[k] = prev.is_some_and(|p| continues(before, p, next[k]));
        } else if code(t.kind) {
            before = prev;
            prev = Some(t.kind);
        }
    }
    out
}

/// Whether an arm goes on from token `i` to its `=>`: a `=>` at the depth of
/// `i` comes before the next `,` or `}` there (S-386, S-419). The scan of the
/// tokens, which reads no element on (S-384): a symbol at the head of the
/// line that starts it is no binary operator of the arm before, and the
/// line break before an opener there is no gap inside a postfix.
pub(crate) fn arm_ahead(c: &Cursor, i: usize) -> bool {
    let mut depth = 0u32;
    for k in i..c.tokens.len() {
        match c.kind(k) {
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

/// The candidate that makes the sign `sign` the start of the element after
/// `prev` in a list: the `,` after `prev`, before the comment of its line,
/// and for a `+`, which is no prefix (§3.1), the `+` and the blanks after it
/// taken out with it (S-370, S-386, S-398, S-405). The one candidate of the
/// `,` before a `-`, `^`, `|` or `+`.
pub(crate) fn comma_before_sign(c: &Cursor, prev: usize, sign: usize) -> Fix {
    let comma = Edit::insert(c.file, c.span(prev).end, ",");
    if c.kind(sign) != TokenKind::Plus {
        return Fix::new("write the `,` between the elements", vec![comma]);
    }
    let s = c.span(sign);
    let end = c.space_after(sign).map_or(s.end, |w| w.end);
    Fix::new("write the `,` and take the `+` out", vec![comma, Edit::delete(Span::new(c.file, s.start, end))])
}

/// Whether the list of the failure is one whose elements are expressions
/// (arguments, a tuple, an array; S-370, S-398), where a sign may start the
/// next element: not the repetition `[v; n]` of an array, which a `,` does
/// not make a list (a `;` in its brackets, the scan of S-419).
pub(crate) fn expression_list(c: &Cursor) -> bool {
    match c.want {
        Want::Separator(NodeKind::ArgList | NodeKind::TupleExpr) => true,
        Want::Separator(NodeKind::ArrayExpr) => !array_repeats(c),
        _ => false,
    }
}

/// Whether the innermost array open at the failure is a repetition (a `;`
/// at its depth): its brackets close, and a `;` is in them.
fn array_repeats(c: &Cursor) -> bool {
    let Some(&(_, start)) = c.open.iter().rev().find(|o| o.0 == NodeKind::ArrayExpr) else { return false };
    bracket_contents(c.tokens, c.index_at(start)).is_some_and(|(_, _, semi)| semi)
}

/// The symbol at the head of the line where the parser failed: the token of
/// the failure, or, when the parser failed at a line break (a head waiting
/// for its `{`, a `let` for its `=`), the first token of the next line; and
/// the code before it, when that is an operand the symbol may go on with
/// (S-124, S-374, S-380): no statement or declaration that ends no operand
/// (`for`, `while`, a declaration, S-236, [`Cursor::ends`], [`End`]), but
/// for a `->` or a `=`, which go on with the head of a declaration (the
/// caller judges whose head).
pub(crate) fn line_head(c: &Cursor) -> Option<(usize, usize)> {
    use TokenKind::*;
    let s = if c.kind(c.at) == Newline { c.sig_after(c.at) } else { c.at };
    if c.gap(s) != Gap::Newline {
        return None;
    }
    let prev = c.sig_before(s)?;
    let kind = c.kind(s);
    let operand = ends_operand(c.kind(prev)) || (matches!(kind, Pipe | Eq) && c.kind(prev) == Underscore);
    let head = matches!(kind, Arrow | Eq);
    (operand && (head || end_at(c, prev) != Some(End::NoOperand))).then_some((s, prev))
}

/// What the statement or declaration whose last token is `i` ends with,
/// when the parser read one to its end there ([`End`]).
pub(crate) fn end_at(c: &Cursor, i: usize) -> Option<End> {
    c.ends.binary_search_by_key(&i, |e| e.0).ok().map(|k| c.ends[k].1)
}

/// What a statement or a declaration that the parser read to its end ends
/// with, for a symbol at the head of the next line (`Parser::ends`, S-236).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum End {
    /// No operand: a `for`, a `while`, a declaration but `const` and `type`.
    /// No symbol goes on with it.
    NoOperand,
    /// The value of a `let`, a `var`, an assignment, a `return` or an
    /// `assert`: an operator goes on with it, a `=` does not.
    Bound,
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
    let s = c.span(i);
    move_token_up_as(c, title, i, &c.text[s.start as usize..s.end as usize])
}

/// [`move_token_up`], the symbol written as `symbol` where it goes (` +`
/// after a blank for a binary operator, ` ..<` for `..`, S-124, S-335).
pub(crate) fn move_token_up_as(c: &Cursor, title: &str, i: usize, symbol: &str) -> Option<Fix> {
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
