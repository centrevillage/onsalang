//! The rows of paths and type arguments: the type names of other languages
//! (`i32`), the `::` of a path, the `<T>` of type arguments and parameters,
//! the type arguments of other languages before a call, and `::[` where it
//! does not go (§4.5, S-239, S-250, S-256).

use super::calls::{is_value_callee, names_a_path, value_call};
use super::*;

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
    Some(diagnostic(text, RowId::LowercaseType, Hit { span: t.span, fixes: vec![fix], misplaced: false }))
}

pub(super) fn is_segment(kind: TokenKind) -> bool {
    kind == TokenKind::Ident || kind.is_keyword()
}

/// `::` between the names of a path (`F32::PI`, `std::math::sqrt`, `use
/// a::{b}`): one path is one form, and the candidate writes every `::` of it
/// as `.` (S-248). The path goes on across a `::[…]` of type arguments
/// (`m::Buf::[F32]::zeroed`, S-239), whose `::` is no separator; it ends at a
/// `::<` (`Buf::<F32>::zeroed` is two forms, S-326).
pub(super) fn path_separator(c: &Cursor) -> Option<Hit> {
    // A clock is one name (§11.3, S-359): a path after `at` is E0002, which
    // `.` for `::` does not fix.
    if c.kind(c.at) != TokenKind::ColonColon || c.closed.first().is_some_and(|n| n.0 == NodeKind::Clock) {
        return None;
    }
    let in_use = c.open.iter().chain(c.closed).any(|o| o.0 == NodeKind::Use);
    let follows = |i: usize| {
        let n = c.kind(i + 1);
        is_segment(n) || (in_use && n == TokenKind::LBrace)
    };
    let before = c.before(c.at)?;
    let after_list = c.kind(before) == TokenKind::RBracket && c.closed.iter().any(|o| o.0 == NodeKind::TypeArgsExpr);
    if !(is_segment(c.kind(before)) || c.kind(before) == TokenKind::KwSelfType || after_list) || !follows(c.at) {
        return None;
    }
    // The path: names separated with `.` or `::`, on and after the failure.
    let mut seps = vec![c.at];
    let mut i = c.at + 1;
    loop {
        if is_type_args_mark(c, i + 1) {
            match closing(c, i + 2) {
                Some(close) => i = close,
                None => break,
            }
        }
        match c.kind(i + 1) {
            TokenKind::Dot if is_segment(c.kind(i + 2)) => i += 2,
            TokenKind::ColonColon if follows(i + 1) => {
                seps.push(i + 1);
                i += 2;
            }
            _ => break,
        }
    }
    let edits = seps.iter().map(|&s| Edit::replace(c.span(s), ".")).collect();
    let title = if seps.len() > 1 { "write each `::` as `.`" } else { "write `.`" };
    // The range of the form (S-316): from its first `::` to its last.
    let last = *seps.last().unwrap_or(&c.at);
    hit(c.file_span(c.span(c.at).start, c.span(last).end), vec![Fix::new(title, edits)])
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
    // A `<` that no `>` closes is no list of type parameters (the general E0002).
    let (close_at, edits) = angle_list(c, c.at, "[")?;
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
            | KwFor
            | KwUses
            | Ident
            | KwSelfType
    )
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
        let blank =
            matches!(t.kind, TokenKind::Comment | TokenKind::DocComment | TokenKind::BlockComment | TokenKind::Newline);
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
            | TokenKind::Newline
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Plus
            | TokenKind::Question
            | TokenKind::Dot
            | TokenKind::Int
            | TokenKind::Minus
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::Semi
            | TokenKind::Comment
            | TokenKind::DocComment
            | TokenKind::BlockComment => {}
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
/// parser asks it before it reads `<` as a comparison or `[` as an index, and
/// reads a `[` on as a list of type arguments to be sure; the table builds
/// the diagnostic where the parser then fails ([`type_args_call`]).
pub(crate) fn type_list_ahead(tokens: &[Token], lines: &crate::layout::Lines, i: usize, callee: NodeKind) -> bool {
    let name = names_a_path(callee);
    if !(name || is_value_callee(callee)) || lines.before(i) != Gap::None {
        return false;
    }
    let close = match tokens[i].kind {
        TokenKind::Lt => angle_tokens(tokens, i).map(|(close, _)| close),
        TokenKind::LBracket => bracket_with_comma(tokens, i),
        _ => None,
    };
    let Some(close) = close else { return false };
    let called =
        tokens.get(close + 1).is_some_and(|t| t.kind == TokenKind::LParen) && lines.before(close + 1) == Gap::None;
    called || (name && tokens[i].kind == TokenKind::LBracket)
}

/// The `]` that closes the `[` at `open` when a `,` is directly in it.
fn bracket_with_comma(tokens: &[Token], open: usize) -> Option<usize> {
    crate::scan::bracket_contents(tokens, open).filter(|b| b.1).map(|b| b.0)
}

/// Type arguments of another language before a call (§4.5, S-239, S-256,
/// S-277): `f::<T>(x)` (Rust; the parser fails at the `::`), and `f<T>(x)`
/// and `f[A, B](x)`, at which the parser fails when [`type_list_ahead`] says
/// so. After a path of names or a method, the candidate is the Onsa form:
/// `::<` keeps the `::` and writes `[ ]`, `<` becomes `::[`, `[` gets `::`
/// before it (S-251; `>>` is `]]`, S-248); `f<T>(x)` with one name, literal
/// or path of names in the list has the reading of the languages that read
/// it as comparisons too (`f < T && T > (x)`, §18.1). After a value
/// (`g(x)`, `(e)`), no `::[` can be written: the one candidate drops the list
/// and calls the value with `.(` (§6.1). After anything else, and for an
/// empty list, the form is not this table's (the general E0002).
pub(super) fn type_args_call(c: &Cursor) -> Option<Hit> {
    let callee = closed_expr(c)?;
    let (row, open) = match c.kind(c.at) {
        TokenKind::ColonColon if c.kind(c.at + 1) == TokenKind::Lt => (RowId::TypeArgsTurbofish, c.at + 1),
        TokenKind::Lt | TokenKind::LBracket if type_list_ahead(c.tokens, c.lines, c.at, callee.0) => {
            let row = if c.kind(c.at) == TokenKind::Lt { RowId::TypeArgsAngle } else { RowId::TypeArgsSquareComma };
            (row, c.at)
        }
        _ => return None,
    };
    let (close, edits) = if row == RowId::TypeArgsSquareComma {
        let close = bracket_with_comma(c.tokens, open)?;
        (close, vec![Edit::insert(c.file, c.span(open).start, "::")])
    } else {
        let first = if row == RowId::TypeArgsAngle { "::[" } else { "[" };
        angle_list(c, open, first)?
    };
    if close == open + 1 {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(close).end);
    if is_value_callee(callee.0) {
        c.say(RowId::TypeArgsOnExpression);
        return hit(span, value_call(c, callee, c.at, close).into_iter().collect());
    }
    if !names_a_path(callee.0) {
        return None;
    }
    c.say(row);
    let mut fixes = vec![Fix::new("write the type arguments as `::[…]`", edits)];
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
            vec![Edit::replace(c.span(open), " < "), Edit::replace(c.span(close), format!(" && {m} > "))],
        ));
    }
    hit(span, fixes)
}

/// `::[` written in a type position (`b: Buf::[F32]`, §4.5): the mark is
/// needed only in an expression, where a `[` alone is an index; in a type
/// it misleads about that rule (P2). The candidate removes the `::` (and a
/// blank around it). A list that is empty or that something no type is
/// followed by follows (`Buf::[F32].Inner`) has none (the general E0002).
pub(super) fn type_position_path(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ColonColon || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    if !c.closed.iter().any(|n| n.0 == NodeKind::PathType) || c.gap_after(c.at) == Gap::Newline {
        return None;
    }
    let close = closing(c, c.at + 1)?;
    if close == c.at + 2 || !follows_type(c.kind(close + 1)) {
        return None;
    }
    let name = c.before(c.at)?;
    let gap = c.file_span(c.span(name).end, c.span(c.at + 1).start);
    hit(c.span(c.at), vec![Fix::delete("remove the `::`", gap)])
}

/// A space on either side of the `::` of `name::[…]` in an expression
/// (`id ::[U8]`, `id:: [U8]`, §2.5, §4.5): the candidate removes it.
pub(super) fn space_in_type_args_mark(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::ColonColon || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    if !closed_expr(c).is_some_and(|n| names_a_path(n.0)) {
        return None;
    }
    let (before, after) = (c.gap(c.at), c.gap_after(c.at));
    if before == Gap::Newline || after == Gap::Newline {
        return None;
    }
    let edits: Vec<Edit> =
        [c.space_before(c.at), c.space_after(c.at)].into_iter().flatten().map(Edit::delete).collect();
    if edits.is_empty() {
        return None;
    }
    hit(c.span(c.at), vec![Fix::new("remove the space", edits)])
}
