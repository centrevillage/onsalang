//! What a token starts or ends (§2.5, §3.1, §6.1): the facts of the grammar
//! that the parser, the line facts ([`crate::layout`]) and the table of the
//! forms of other languages ([`crate::foreign`]) read alike, so that none of
//! them asks another for them (D-15). Each is a fact of one token kind (or
//! of two kinds in a row); the scans of a run of tokens are
//! [`crate::scan`].

use crate::cst::NodeKind;
use crate::token::TokenKind;

/// Whether a token starts an operand (§3.1): a prefix operator, a literal,
/// a name or the reference `^name` (§2.6), `_`, a bracket, a block, or an expression keyword. `move` and
/// `rt` before an operand are errors of their own and start none.
#[inline]
pub(crate) fn starts_operand(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Minus
            | Bang
            | Caret
            | Int
            | Float
            | Char
            | Str
            | KwTrue
            | KwFalse
            | Underscore
            | Ident
            | KwSelf
            | KwSelfType
            | LParen
            | LBracket
            | LBrace
            | KwIf
            | KwMatch
            | KwFn
            | KwHandle
            | KwUnsafe
            | KwPar
    )
}

/// Whether a token of `kind` ends an operand: what a postfix `?` or a binary
/// operator follows (a name, a literal, a closing bracket, `?`).
#[inline]
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

/// Whether a token of `kind` after a member `.` is a member (§2.5): a name,
/// a tuple index or the `(` of `.(`. The parser's postfix `.` reads it
/// (`parser::expressions`, a keyword being a field name there), and so do the
/// rows of a blank or a line break around the `.` (`foreign::spaces`,
/// `foreign::lines`); the lexer
/// reads the same at the bytes after a number's `.` (a name or a `(`, a digit
/// being the fraction: `literal::point_after_int`).
pub(crate) fn starts_member(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::Ident | TokenKind::Int | TokenKind::LParen)
}

/// Whether the tokens `first` and `second` declare a function (`fn name`),
/// which no expression is (§6.1): the one test, for the parser and the
/// missing `,` of a list (`foreign::lists::list_fixes`).
pub(crate) fn declares_a_function(first: TokenKind, second: TokenKind) -> bool {
    first == TokenKind::KwFn && second == TokenKind::Ident
}

/// What starts an element of a list whose elements are separated with `,`
/// (§2.5), for each such list: the one table of those lists (none for a
/// node of another kind).
fn element_starts(list: NodeKind) -> Option<fn(TokenKind) -> bool> {
    use TokenKind::*;
    Some(match list {
        NodeKind::ArgList => |k| starts_operand(k) || matches!(k, KwMove | KwInout),
        NodeKind::TupleExpr | NodeKind::ArrayExpr => |k| starts_operand(k) || k == KwMove,
        NodeKind::StructLitFields | NodeKind::VariantList | NodeKind::UseNames | NodeKind::EffectRow => |k| k == Ident,
        NodeKind::FieldList => |k| matches!(k, Ident | KwPub | KwPriv),
        NodeKind::ParamList => |k| matches!(k, Ident | KwSelf | Underscore | At | KwInout | KwMove),
        NodeKind::GenericParams => |k| matches!(k, Ident | KwConst),
        NodeKind::TypeArgs => |k| starts_type(k) || starts_operand(k),
        NodeKind::TupleType | NodeKind::VariantFields => starts_type,
        NodeKind::FnTypeParams => |k| starts_type(k) || matches!(k, KwInout | KwMove),
        NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::MatchArms => starts_pattern,
        NodeKind::StructPat => |k| matches!(k, Ident | DotDot),
        NodeKind::AttrArgs => |k| matches!(k, Ident | Str),
        _ => return None,
    })
}

/// Whether a token of `kind` may start a type in a list.
fn starts_type(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Ident | KwSelfType | LParen | LBracket | KwFn | KwRt)
}

/// Whether a token of `kind` may start a pattern in a list.
fn starts_pattern(kind: TokenKind) -> bool {
    use TokenKind::*;
    literal_pattern(kind) || matches!(kind, Underscore | Minus | Int | Float | LParen | Ident | KwSelfType)
}

/// Whether a token of `kind` is a literal that is a pattern alone (§7): a
/// character, a string (one with no interpolation, S-225), `true` or
/// `false`. An integer is read with its `-` (`-1`), and a float is the guard
/// form (S-248). The one set for the parser (`Parser::parse_pattern_alt`) and
/// the reader of the guard forms (`foreign::guard`).
pub(crate) fn literal_pattern(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Char | Str | KwTrue | KwFalse)
}

/// Whether a token of `kind` may start an element of a list of `list`: the
/// lexical condition of the missing `,` (S-384: the next element is not read
/// on to see whether it is one). A `~` starts no element.
pub(crate) fn starts_element(list: NodeKind, kind: TokenKind) -> bool {
    element_starts(list).is_some_and(|starts| starts(kind))
}

/// Whether a node of `kind` is a list whose elements are separated with `,`
/// (§2.5), where a `;` is the `;` of other languages between them (S-248):
/// a list of the table above, but an array, whose `;` is its repetition
/// (`[v; n]`).
pub(crate) fn comma_list(kind: NodeKind) -> bool {
    element_starts(kind).is_some() && kind != NodeKind::ArrayExpr
}
