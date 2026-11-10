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

/// Whether a keyword of `kind` starts a statement that is no expression
/// (§6.1): what `Parser::parse_stmt` reads by its first token (an attribute
/// `@` before a `let` too).
pub(crate) fn starts_statement(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, KwLet | KwVar | KwFor | KwWhile | KwBreak | KwContinue | KwReturn | KwMove | KwAssert)
}

/// Whether a token of `kind` after an operand is a binary operator, `as` or
/// `at` (§3.1, §3.3).
pub(crate) fn operator_after(kind: TokenKind) -> bool {
    kind.binop().is_some() || matches!(kind, TokenKind::KwAs | TokenKind::KwAt)
}

/// Whether the keyword `kind` that the parser failed at is written as a name
/// (§2.3, S-654): a keyword that is no reserved word (its E0200, §2.2) and no
/// word of a value (`self`, `Self`, `true`, `false`, which end an operand);
/// where an operand is (`operand`), one that starts no expression and no
/// statement either (`match`, `fn`, `return`). The one test, for the names
/// and the operands the parser fails at (`Parser::fail_at`).
pub(crate) fn keyword_as_name(kind: TokenKind, operand: bool) -> bool {
    kind.is_keyword()
        && kind.reserved().is_none()
        && !ends_operand(kind)
        && !(operand && (starts_operand(kind) || starts_statement(kind)))
}

/// Whether the token after a keyword written as a name, of `kind` (`None`:
/// the end of the line), goes on after a name there (S-654, §18.1: else the
/// candidate would leave an error of its stage): a binary operator, a `,`, a
/// closing bracket, a postfix `.`, `[`, `(` or `?`, `=`, `=>` and a range
/// symbol; after a declared name (`declared`) its `:` and the `in` of `for`
/// and `par~`; after an operand `as`, `at` and in a header (`header`, S-338)
/// the `{` of the body. A name, a literal or another word after it is a form
/// of its own (`at sample`, `fn f(in x: I32)`, `let const x`), and the
/// keyword before it is no name.
pub(crate) fn follows_a_name(kind: Option<TokenKind>, declared: bool, header: bool) -> bool {
    use TokenKind::*;
    kind.is_none_or(|k| {
        let any =
            [Comma, RParen, RBracket, RBrace, Eof, Dot, LBracket, LParen, Question, Eq, FatArrow, DotDotLt, DotDotEq];
        k.binop().is_some()
            || any.contains(&k)
            || if declared { matches!(k, Colon | KwIn) } else { operator_after(k) || (header && k == LBrace) }
    })
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

/// Whether a token of `kind` is a name where a keyword is an ordinary name
/// (§2.2): after a member `.` (`x.type`, `std.test`) and among the names of
/// a `use` (`use a.{test}`, R-272); a name or a keyword. The one test, for
/// the parser, the lowering and the rows ([`starts_member`] adds the other
/// members, `.0` and `.(`).
pub(crate) fn names_a_member(kind: TokenKind) -> bool {
    kind == TokenKind::Ident || kind.is_keyword()
}

/// Whether the tokens `first` and `second` declare a function (`fn name`),
/// which no expression is (§6.1): the one test, for the parser and the
/// missing `,` of a list (`foreign::lists::list_fixes`).
pub(crate) fn declares_a_function(first: TokenKind, second: TokenKind) -> bool {
    first == TokenKind::KwFn && second == TokenKind::Ident
}

/// Whether the token `first` and the token after it on its line (`next`,
/// `None` at its end; blanks and comments passed) open a function type or an
/// anonymous function (`fn(`): no declaration, which has a name, so no item
/// starts there, nor at an `rt` before it (§18.1, S-947). The one test of a
/// form that starts with the keyword of an item and is no item, next to that
/// of a declaration ([`declares_a_function`]), which the readings of an
/// expression and of a type tell apart: such a new type or expression (an
/// `extern "C" fn(…)` type) is added to both.
pub(crate) fn opens_a_function_value(first: TokenKind, next: Option<TokenKind>) -> bool {
    first == TokenKind::KwFn && next == Some(TokenKind::LParen)
}

/// What starts an element of a list whose elements are separated with `,`
/// (§2.5), for each such list: the one table of those lists (none for a
/// node of another kind).
fn element_starts(list: NodeKind) -> Option<fn(TokenKind) -> bool> {
    use TokenKind::*;
    Some(match list {
        NodeKind::ArgList => |k| starts_operand(k) || matches!(k, KwMove | KwInout),
        NodeKind::TupleExpr | NodeKind::ArrayExpr => |k| starts_operand(k) || k == KwMove,
        NodeKind::StructLitFields => |k| matches!(k, Ident | DotDotDot),
        NodeKind::VariantList | NodeKind::UseNames | NodeKind::EffectRow => |k| k == Ident,
        NodeKind::FieldList => |k| matches!(k, Ident | KwPub | KwPriv),
        NodeKind::ParamList => |k| matches!(k, Ident | KwSelf | Underscore | At | KwInout | KwMove),
        NodeKind::GenericParams => |k| matches!(k, Ident | KwConst),
        NodeKind::TypeArgs => |k| starts_type(k) || starts_operand(k),
        NodeKind::TupleType | NodeKind::VariantFields => starts_type,
        NodeKind::FnTypeParams => |k| starts_type(k) || matches!(k, KwInout | KwMove),
        NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::MatchArms => starts_pattern,
        NodeKind::StructPat => |k| matches!(k, Ident | Underscore | DotDot),
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

#[cfg(test)]
mod tests {
    use crate::token::{KEYWORDS, TokenKind};

    /// The kinds that name a member are `Ident` and the keywords (§2.2), and
    /// no other: a new keyword is a name after `.` without a change here.
    #[test]
    fn a_member_is_named_by_a_name_or_a_keyword() {
        let mut named: Vec<usize> =
            TokenKind::ALL.iter().filter(|&&k| super::names_a_member(k)).map(|&k| k as usize).collect();
        let mut want: Vec<usize> = KEYWORDS.iter().map(|k| k.kind as usize).collect();
        want.push(TokenKind::Ident as usize);
        named.sort_unstable();
        want.sort_unstable();
        assert_eq!(named, want);
        assert!(!super::names_a_member(TokenKind::Int) && super::starts_member(TokenKind::Int));
    }

    /// The parser reads a statement past its first token exactly when that
    /// token starts an expression or a statement ([`super::starts_statement`],
    /// the arms of `Parser::parse_stmt`): every other keyword is the failure
    /// at it, where S-654 judges whether it is written as a name.
    #[test]
    fn the_keywords_that_start_a_statement_are_those_the_parser_reads() {
        for k in KEYWORDS.iter().filter(|k| k.reserved.is_none()) {
            let src = format!("fn f() {{\n  {}\n}}\n", k.text);
            let parsed = crate::parse(onsa_diag::FileId(0), &src);
            let at = src.find(&format!("  {}\n", k.text)).unwrap() as u32 + 2;
            let fails_at = parsed.diagnostics.iter().any(|d| d.span.start == at);
            let starts = super::starts_operand(k.kind) || super::starts_statement(k.kind);
            assert_eq!(fails_at, !starts, "`{}`: {:?}", k.text, parsed.diagnostics);
        }
    }

    /// S-654 (§2.3, §18.1): a keyword that starts no expression and no
    /// statement, where an operand is, takes the candidate `in_` only when
    /// the token after it surely goes on after a name; and a keyword where a
    /// name is declared takes it where the name is `snake_case`, not on an
    /// item with `@export`. The words of a value and `return` take none.
    #[test]
    fn a_keyword_written_as_a_name_takes_a_tail_where_it_would_be_a_name() {
        let candidates = |body: &str| -> Vec<String> {
            let parsed = crate::parse(onsa_diag::FileId(0), body);
            let fixes = parsed.diagnostics.iter().flat_map(|d| d.fixes.iter());
            fixes.map(|f| f.edits()[0].replace.clone()).collect()
        };
        let body = |e: &str| format!("fn f(x: I32) -> I32 {{\n  let y = {e}\n  y\n}}\n");
        for (e, want) in [("in + 1", "in_"), ("(as)", "as_"), ("x * uses", "uses_"), ("in.x", "in_"), ("in(x)", "in_")]
        {
            assert_eq!(candidates(&body(e)), [want], "{e}");
        }
        // A type is no operand: `as` takes one after it.
        for e in ["at sample", "in x", "in 1", "return", "self + 1", "true + 1", "match", "x as uses"] {
            assert_eq!(candidates(&body(e)), Vec::<String>::new(), "{e}");
        }
        assert_eq!(candidates("fn type() {}\n"), ["type_"]);
        assert_eq!(candidates("fn f() { for in in 0..<3 {} }\n"), ["in_"]);
        // A name or a literal after a declared name: the `_` would leave an E0002.
        for src in ["struct type {}\n", "@export\npub fn type() {}\n", "fn true() {}\n", "fn type f() {}\n"] {
            assert_eq!(candidates(src), Vec::<String>::new(), "{src}");
        }
        for src in ["fn f(in x: I32) {}\n", "fn f() { for in xs {} }\n", "extern \"C\" lib \"m\" {\n  fn type()\n}\n"] {
            assert_eq!(candidates(src), Vec::<String>::new(), "{src}");
        }
    }
}
