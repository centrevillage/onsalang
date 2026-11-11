//! The rows of paths and type arguments: the type names of other languages
//! (`i32`), the `::` of a path, the `<T>` of type arguments and parameters,
//! the type arguments of other languages before a call, and `::[` where it
//! does not go (§4.5, S-239, S-250, S-256).

use super::calls::value_call;
use super::spaces::partner;
use super::*;
use crate::callee::Link;

/// The type names of other languages (`i32`: `I32`, `usize`: `U32`, S-250).
/// `String`, `Vec`, `i128` and `u128` are not here: they are names that
/// are not declared (E0302).
pub const TYPE_NAMES: &[(&str, &str)] = &[
    ("i8", "I8"),
    ("i16", "I16"),
    ("i32", "I32"),
    ("i64", "I64"),
    ("u8", "U8"),
    ("u16", "U16"),
    ("u32", "U32"),
    ("u64", "U64"),
    ("f32", "F32"),
    ("f64", "F64"),
    ("bool", "Bool"),
    ("usize", "U32"),
    ("isize", "I32"),
    ("char", "Char"),
    ("str", "Str"),
];

/// A type written as one name `t`: the E0020 of a built-in type name of
/// another language (`i32`). The parser fails the unit on it.
pub(crate) fn type_name(text: &str, t: Token) -> Option<Diagnostic> {
    let name = &text[t.span.start as usize..t.span.end as usize];
    let (_, fix) = TYPE_NAMES.iter().find(|(from, _)| *from == name)?;
    let fix = Fix::replace("write the built-in type name", t.span, *fix);
    Some(diagnostic(text, RowId::LowercaseType, Hit::new(t.span, vec![fix])))
}

pub(super) fn is_segment(kind: TokenKind) -> bool {
    crate::starts::names_a_member(kind)
}

/// `::` between the names of a path (`F32::PI`, `std::math::sqrt`, `use
/// a::{b}`): one path is one form, and the candidate writes every `::` of it
/// as `.` (S-248). The path goes on across a `::[…]` of type arguments
/// (`m::Buf::[F32]::zeroed`, S-239), whose `::` is no separator; it ends at a
/// `::<` (`Buf::<F32>::zeroed` is two forms, S-326), its gaps too ([`dot_for`]).
pub(super) fn path_separator(c: &Cursor) -> Option<Hit> {
    if !path_head(c) {
        return None;
    }
    let in_use = c.open.iter().chain(c.closed).any(|o| o.0 == NodeKind::Use);
    let follows = |i: usize| {
        let n = if c.gap_after(i) == Gap::None { i + 1 } else { partner(c, i)? };
        (is_segment(c.kind(n)) || (in_use && c.kind(n) == TokenKind::LBrace)).then_some(n)
    };
    // The path: names separated with `.` or `::`, on and after the failure.
    let mut seps = vec![c.at];
    let mut i = follows(c.at)?;
    loop {
        if is_type_args_mark(c, i + 1) {
            match closing(c, i + 2) {
                Some(close) => i = close,
                None => break,
            }
        }
        match c.kind(i + 1) {
            TokenKind::Dot if is_segment(c.kind(i + 2)) => i += 2,
            TokenKind::ColonColon if follows(i + 1).is_some() => {
                seps.push(i + 1);
                i = follows(i + 1)?;
            }
            _ => break,
        }
    }
    let edits = seps.iter().map(|&s| dot_for(c, s)).collect::<Option<Vec<_>>>()?.concat();
    let title = if seps.len() > 1 { "write each `::` as `.`" } else { "write `.`" };
    // The range of the form (S-316): from its first `::` to its last.
    let last = *seps.last().unwrap_or(&c.at);
    hit(c.file_span(c.span(c.at).start, c.span(last).end), vec![Fix::new(title, edits)])
}

/// Whether the `::` at the cursor goes on a path ([`path_separator`], and
/// `::[`): after a name ([`path_colons`]) or the `]` of type arguments, but
/// in a clock, one name (§11.3, S-359: E0002, which `.` does not fix).
pub(super) fn path_head(c: &Cursor) -> bool {
    let after_list =
        c.kind(c.at.saturating_sub(1)) == TokenKind::RBracket && c.closed.iter().any(|o| o.0 == NodeKind::TypeArgsExpr);
    (path_colons(c.tokens, c.at) || (c.kind(c.at) == TokenKind::ColonColon && after_list))
        && !c.closed.first().is_some_and(|n| n.0 == NodeKind::Clock)
}

/// Whether the token `i` is a `::` right after a name or `Self` (S-248).
pub(crate) fn path_colons(tokens: &[Token], i: usize) -> bool {
    let before = |b: usize| is_segment(tokens[b].kind) || tokens[b].kind == TokenKind::KwSelfType;
    tokens[i].kind == TokenKind::ColonColon && i.checked_sub(1).is_some_and(before)
}

/// The edits that write the `::` at `s` of a path as `.` (S-963): the blanks
/// on its line go with it, and after a line break the `.` goes to the head of
/// the next line ([`move_token_down_as`]).
fn dot_for(c: &Cursor, s: usize) -> Option<Vec<Edit>> {
    if c.gap_after(s) == Gap::Newline {
        return Some(super::edits::move_token_down_as(c, "", s, ".")?.edits().to_vec());
    }
    let start = c.space_before(s).map_or(c.span(s).start, |b| b.start);
    Some(vec![Edit::replace(c.file_span(start, c.space_after(s).map_or(c.span(s).end, |b| b.end)), ".")])
}

/// The mark `::[` of type arguments in an expression at token `i`.
fn is_type_args_mark(c: &Cursor, i: usize) -> bool {
    c.lines.type_args_mark(c.tokens, i)
}

/// `<` ... `>` of type parameters (`fn f<T>`) or type arguments
/// (`Vec<T>`): written in `[ ]` (§4.5). The candidate replaces each bracket
/// token (S-251; `>>` closing two is `]]`), the nested ones too (S-248).
pub(super) fn angle_brackets(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Lt {
        return None;
    }
    let after_type = c.closed.iter().any(|n| n.0 == NodeKind::PathType);
    // The name of a declaration with type parameters (its list of
    // parameters, fields or members may be open already).
    let after_name = c.closed.first().is_some_and(|n| n.0 == NodeKind::Name)
        && c.open.iter().rev().take(2).any(|o| {
            matches!(o.0, NodeKind::Fn | NodeKind::Struct | NodeKind::Enum | NodeKind::Trait | NodeKind::TypeAlias)
        });
    let after_impl = c.before(c.at).is_some_and(|b| c.kind(b) == TokenKind::KwImpl);
    if !(after_type || after_name || after_impl) {
        return None;
    }
    // A `<` that no `>` closes is no list of type parameters (the general
    // E0002), and neither is one that does not read as one in `[ ]` (R-193).
    let (close_at, edits) = angle_list(c, c.at, "[")?;
    if !reads_square(c, c.at, after_name || after_impl) {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(close_at).end);
    // What follows the brackets is what follows a type or a list of type
    // parameters; else the brackets are not read so (no candidate).
    let follows = follows_type(c.kind(close_at + 1)) || c.kind(close_at + 1) == TokenKind::Dot;
    let fixes = if follows { vec![Fix::new("write the brackets `[ ]`", edits)] } else { Vec::new() };
    hit(span, fixes)
}

/// A token that may follow a type or a list of type parameters (`;` after
/// the element type of an array type).
fn follows_type(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Comma
            | Semi
            | RParen
            | RBracket
            | RBrace
            | Eq
            | LBrace
            | LParen
            | Newline
            | Eof
            | Comment
            | DocComment
            | ModuleDoc
            | KwFor
            | KwUses
            | KwAt
            | Ident
            | KwSelfType
    )
}

/// Whether the list in angle brackets that opens at the `<` `open` reads as
/// a list of type parameters (`params`) or of type arguments when its
/// brackets are written `[ ]` (R-193: `fn b<T q>` and `d<U)>(x)` do not, and
/// a candidate there would leave an error of the syntax stage, S-236): the
/// parser reads it ([`crate::parser::reads_as_type_list`]).
fn reads_square(c: &Cursor, open: usize, params: bool) -> bool {
    let Some((close, brackets)) = angle_tokens(c.tokens, open) else { return false };
    let swaps: Vec<(usize, &str)> = brackets.into_iter().map(|(i, to)| (c.full[i] as usize, to)).collect();
    let run = (c.full[open] as usize, c.full[close] as usize);
    crate::parser::reads_as_type_list(c.file, c.text, c.all, c.literals, run, &swaps, params)
}

/// The list in angle brackets that opens at the `<` `open`: the token that
/// closes it, and the edits that write its brackets as `[ ]`, the first `<`
/// as `first` (S-251; `>>` closing two is `]]`, the nested lists too, S-248).
/// None when a token no list of types holds comes before its `>`.
fn angle_list(c: &Cursor, open: usize, first: &str) -> Option<(usize, Vec<Edit>)> {
    let (close, brackets) = angle_tokens(c.tokens, open)?;
    let edits =
        brackets.into_iter().map(|(i, to)| Edit::replace(c.span(i), if i == open { first } else { to })).collect();
    Some((close, edits))
}

/// The tokens of [`angle_list`]: the closing token, and each bracket with
/// what it becomes.
fn angle_tokens(tokens: &[Token], open: usize) -> Option<(usize, Vec<(usize, &'static str)>)> {
    let mut depth = 0i32;
    let mut brackets = Vec::new();
    // An element starts as a type, a type parameter or a constant does, and a
    // `>` closes what can end one (`<->`, `<A,>`, `<U->8>` are no lists).
    let starts = |k: TokenKind| {
        use TokenKind::*;
        matches!(k, Ident | KwSelfType | KwConst | KwFn | KwRt | LParen | LBracket | Int | Minus | Underscore)
    };
    let ends = |k: TokenKind| {
        use TokenKind::*;
        matches!(k, Ident | KwSelfType | RParen | RBracket | Int | Gt | Shr)
    };
    // The last token before `i` that is no comment or newline.
    let mut prev = TokenKind::Lt;
    for (i, t) in tokens.iter().enumerate().skip(open) {
        let blank = t.kind.is_comment() || t.kind == TokenKind::Newline;
        if i > open && !blank {
            if matches!(prev, TokenKind::Lt | TokenKind::Comma) && !starts(t.kind) {
                return None;
            }
            if matches!(t.kind, TokenKind::Gt | TokenKind::GtEq | TokenKind::Shr) && !ends(prev) {
                return None;
            }
            // `->` is the result of a function type, after its `)`.
            if t.kind == TokenKind::Arrow && prev != TokenKind::RParen {
                return None;
            }
            prev = t.kind;
        }
        match t.kind {
            TokenKind::Lt => {
                depth += 1;
                brackets.push((i, "["));
            }
            TokenKind::Gt => {
                depth -= 1;
                brackets.push((i, "]"));
            }
            TokenKind::GtEq => {
                depth -= 1;
                brackets.push((i, "]="));
            }
            TokenKind::Shr if depth >= 2 => {
                depth -= 2;
                brackets.push((i, "]]"));
            }
            TokenKind::Ident
            | TokenKind::KwSelfType
            | TokenKind::KwConst
            | TokenKind::KwFn
            | TokenKind::KwRt
            | TokenKind::Arrow
            | TokenKind::Underscore
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Plus
            | TokenKind::Question
            | TokenKind::Dot
            | TokenKind::Int
            | TokenKind::Minus
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::Semi => {}
            _ if blank => {}
            _ => return None,
        }
        if depth == 0 {
            return Some((i, brackets));
        }
    }
    None
}

/// Whether the `<` or `[` at `tokens[i]` opens type arguments of another
/// language before a call (`f<T>(x)`, `f[A, B](x)`, §4.5, S-256), after an
/// expression of `callee`'s kind: it touches the callee, its list closes,
/// and a `(` touches the list (for a `[` after a path, any token may follow:
/// `Rg[F32, 4].CAP`); a `[` holds a `,` (an index holds one expression). The
/// parser asks it before it reads `<` as a comparison or `[` as an index: it
/// reads a `[` after a path as a list of type arguments (`super::square`
/// reports it), and the table builds the diagnostic where it fails at the
/// others ([`type_args_call`]).
pub(crate) fn type_list_ahead(
    tokens: &[Token],
    lines: &crate::layout::Lines,
    brackets: &std::cell::OnceCell<crate::scan::Brackets>,
    i: usize,
    callee: NodeKind,
) -> bool {
    let link = Link::of(callee);
    let name = link.names_a_path();
    if !(name || link.is_value()) || lines.before(i) != Gap::None {
        return false;
    }
    let close = match tokens[i].kind {
        TokenKind::Lt => angle_tokens(tokens, i).map(|(close, _)| close),
        TokenKind::LBracket => bracket_with_comma(crate::scan::Brackets::of(brackets, tokens), i),
        _ => None,
    };
    let Some(close) = close else { return false };
    let called =
        tokens.get(close + 1).is_some_and(|t| t.kind == TokenKind::LParen) && lines.before(close + 1) == Gap::None;
    called || (name && tokens[i].kind == TokenKind::LBracket)
}

/// The `]` that closes the `[` at `open` when a `,` is directly in it.
fn bracket_with_comma(brackets: &crate::scan::Brackets, open: usize) -> Option<usize> {
    brackets.contents(open).filter(|b| b.1).map(|b| b.0)
}

/// The rows [`type_args_call`] names ([`super::Matcher::many`]).
pub(super) const TYPE_ARGS_CALL_ROWS: &[RowId] =
    &[RowId::TypeArgsTurbofish, RowId::TypeArgsAngle, RowId::TypeArgsOnExpression];

/// Type arguments of another language before a call (§4.5, S-239, S-256,
/// S-277): `f::<T>(x)` (Rust; the parser fails at the `::`), and `f<T>(x)`
/// and `(e)[A, B](x)`, at which the parser fails when [`type_list_ahead`] says
/// so (after a path of names, `f[A, B]` is read whole: `super::square`).
/// After a path of names or a method, the candidate is the Onsa form:
/// `::<` keeps the `::` and writes `[ ]`, `<` becomes `::[` (S-251; `>>` is
/// `]]`, S-248); `f<T>(x)` with one name, literal
/// or path of names in the list has the reading of the languages that read
/// it as comparisons too (`f < T && T > (x)`, §18.1). After a value
/// (`g(x)`, `(e)`), no `::[` can be written: the one candidate drops the list
/// and calls the value with `.(` (§6.1). After anything else, and for an
/// empty list, the form is not this table's (the general E0002).
pub(super) fn type_args_call(c: &Cursor) -> Option<(RowId, Hit)> {
    if !matches!(c.kind(c.at), TokenKind::ColonColon | TokenKind::Lt | TokenKind::LBracket) {
        return None;
    }
    let callee = closed_expr(c)?;
    let (row, open) = match c.kind(c.at) {
        TokenKind::ColonColon if c.kind(c.at + 1) == TokenKind::Lt => (RowId::TypeArgsTurbofish, c.at + 1),
        TokenKind::Lt if type_list_ahead(c.tokens, c.lines, c.brackets, c.at, callee.0) => (RowId::TypeArgsAngle, c.at),
        TokenKind::LBracket
            if Link::of(callee.0).is_value() && type_list_ahead(c.tokens, c.lines, c.brackets, c.at, callee.0) =>
        {
            (RowId::TypeArgsOnExpression, c.at)
        }
        _ => return None,
    };
    let (close, edits) = if row == RowId::TypeArgsOnExpression {
        (bracket_with_comma(c.brackets(), open)?, Vec::new())
    } else {
        let first = if row == RowId::TypeArgsAngle { "::[" } else { "[" };
        // A list that does not read as type arguments in `[ ]` (R-193): the general E0002.
        if !reads_square(c, open, false) {
            return None;
        }
        angle_list(c, open, first)?
    };
    if close == open + 1 {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(close).end);
    if Link::of(callee.0).is_value() {
        return found(RowId::TypeArgsOnExpression, span, value_call(c, callee, c.at, close).into_iter().collect());
    }
    if !Link::of(callee.0).names_a_path() {
        return None;
    }
    let mut fixes = vec![Fix::new(TYPE_ARGS_WITH_COLONS, edits)];
    let single = is_place(c, open + 1, close - 1)
        || (open + 2 == close
            && matches!(
                c.kind(open + 1),
                TokenKind::Int
                    | TokenKind::Float
                    | TokenKind::Str
                    | TokenKind::Char
                    | TokenKind::KwTrue
                    | TokenKind::KwFalse
            ));
    if row == RowId::TypeArgsAngle && single && c.kind(close) == TokenKind::Gt {
        let m = &c.text[c.span(open + 1).start as usize..c.span(close - 1).end as usize];
        fixes.push(Fix::new(
            "compare: both comparisons, joined with `&&`",
            // The `<` and the `>` stay (S-251): blanks around them, the second operand before `>`.
            {
                let (o, e) = (c.span(open), c.span(close));
                vec![
                    Edit::insert(o.file, o.start, " "),
                    Edit::insert(o.file, o.end, " "),
                    Edit::insert(e.file, e.start, format!(" && {m} ")),
                    Edit::insert(e.file, e.end, " "),
                ]
            },
        ));
    }
    found(row, span, fixes)
}

/// `::[` written in a type position (`b: Buf::[F32]`, §4.5): the mark is
/// needed only in an expression, where a `[` alone is an index; in a type
/// it misleads about that rule (P2). The candidate removes the `::` (and a
/// blank around it). A list that is empty or that something no type is
/// followed by follows (`Buf::[F32].Inner`) has none (the general E0002).
pub(super) fn type_position_path(c: &Cursor) -> Option<Hit> {
    let open = type_args_bracket(c)?;
    if !c.closed.iter().any(|n| n.0 == NodeKind::PathType) {
        return None;
    }
    let close = closing(c, open)?;
    if close == open + 1 || !follows_type(c.kind(close + 1)) {
        return None;
    }
    let name = c.before(c.at)?;
    hit(c.span(c.at), vec![Fix::new("remove the `::`", bracket_up(c, c.span(name).end, open)?)])
}

/// A space on either side of the `::` of `name::[…]` in an expression
/// (`id ::[U8]`, `id:: [U8]`, §2.5, §4.5) and a line break after it
/// (S-327): the candidate removes them ([`bracket_up`]).
pub(super) fn space_in_type_args_mark(c: &Cursor) -> Option<Hit> {
    let open = type_args_bracket(c)?;
    if c.gap(c.at) == Gap::Newline || !closed_expr(c).is_some_and(|n| Link::of(n.0).names_a_path()) {
        return None;
    }
    let mut edits: Vec<Edit> = c.space_before(c.at).into_iter().map(Edit::delete).collect();
    edits.extend(bracket_up(c, c.span(c.at).end, open)?);
    (!edits.is_empty()).then(|| Hit::new(c.span(c.at), vec![Fix::new("remove the space", edits)]))
}

/// The `[` after the `::` at the cursor, touching it or after a gap with no
/// block comment in it ([`partner`]).
fn type_args_bracket(c: &Cursor) -> Option<usize> {
    let open = if c.gap_after(c.at) == Gap::None { c.at + 1 } else { partner(c, c.at)? };
    (c.kind(c.at) == TokenKind::ColonColon && c.kind(open) == TokenKind::LBracket).then_some(open)
}

/// The edits that take out what is between `end` (of the `::` at the cursor or
/// of the name before it) and the `[` at `open`: after a line break (S-327),
/// the line of the `[` goes up as a mark's `(` does ([`crate::edits::move_up`]).
fn bracket_up(c: &Cursor, end: u32, open: usize) -> Option<Vec<Edit>> {
    let (colons, gap) = (c.span(c.at).end, c.file_span(end, c.span(open).start));
    if c.gap_after(c.at) != Gap::Newline {
        return Some((!gap.is_empty()).then(|| Edit::delete(gap)).into_iter().collect());
    }
    let mut edits = crate::edits::move_up(c.file, c.text, c.all, "", colons, c.tokens[open], "")?.edits().to_vec();
    if end < colons {
        edits.push(Edit::delete(c.file_span(end, colons)));
    }
    Some(edits)
}
