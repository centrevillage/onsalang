//! Tokens of Onsa (spec §2).

use onsa_diag::Span;

/// Kind of a token. Whitespace, comments and newlines are tokens too
/// (trivia), so the tokens cover every byte of the source and the CST holds
/// all of them (R-86). The parser skips whitespace and comments and treats
/// newlines by context (§2.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Trivia
    /// A run of spaces, tabs and carriage returns.
    Whitespace,
    /// A line break (one token per physical newline).
    Newline,
    /// `// ...`
    Comment,
    /// `/// ...` (attaches to the next declaration).
    DocComment,

    // Identifiers and literals
    /// Identifier of any shape (`snake_case`, `UpperCamel`, `UPPER_SNAKE`). The
    /// naming rule (§2.3) is checked per declaration kind by the parser.
    Ident,
    /// `_` alone.
    Underscore,
    Int,
    Float,
    Char,
    Str,

    // Keywords (§2.2)
    KwFn,
    KwRt,
    KwFlow,
    KwPar,
    KwStruct,
    KwEnum,
    KwTrait,
    KwImpl,
    KwEffect,
    KwBlocking,
    KwHandler,
    KwHandle,
    KwWith,
    KwUses,
    KwLet,
    KwVar,
    KwIf,
    KwElse,
    KwMatch,
    KwFor,
    KwIn,
    KwWhile,
    KwBreak,
    KwContinue,
    KwReturn,
    KwPub,
    KwUse,
    KwExtern,
    KwUnsafe,
    KwTarget,
    KwTest,
    KwAssert,
    KwConst,
    KwType,
    KwAs,
    KwInout,
    KwMove,
    KwSelf,
    KwSelfType,
    KwTrue,
    KwFalse,

    // Operators (§3.1)
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusPercent,
    MinusPercent,
    StarPercent,
    PlusPipe,
    MinusPipe,
    StarPipe,
    EqEq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    AndAnd,
    OrOr,
    Amp,
    Pipe,
    Caret,
    Shl,
    Shr,
    /// `!`: prefix negation, or the receiver-changing call mark `f!(` (§2.6).
    Bang,
    /// `~`: the flow-call mark `f~(` (§2.6). Never an operator.
    Tilde,

    // Punctuation
    Eq,
    Arrow,
    FatArrow,
    Dot,
    DotDot,
    Comma,
    Colon,
    Question,
    At,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    // Tokens of the forms of other languages: the parser accepts none of them
    // where they are written, and the table of those forms
    // ([`crate::foreign`]) says what the failure is (E0020 with the Onsa form,
    // or E0002 with a note).
    /// `::`
    ColonColon,
    /// `;`
    Semi,
    /// `#`
    Hash,
    /// `..=`
    DotDotEq,
    /// `++`
    PlusPlus,
    /// `--` (`- -x` with a space is two `-`)
    MinusMinus,
    /// `/* ... */`, over lines; nested ones and one never closed reach their
    /// end or the end of the file (§2.1).
    BlockComment,
    /// A number written as in other languages: `1.` (no digit after the
    /// point) and a number with a type suffix (`1u8`, `1.0f32`, §2.4).
    ForeignLit,

    /// An invalid character (E0001 was reported).
    Error,
    /// End of file.
    Eof,
}

impl TokenKind {
    pub fn is_trivia(self) -> bool {
        matches!(self, TokenKind::Whitespace | TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment)
    }

    /// A keyword (§2.2): one of [`KEYWORDS`], not an order of the declarations (R-87).
    pub fn is_keyword(self) -> bool {
        KEYWORDS.iter().any(|&(_, k)| k == self)
    }

    /// Binary operators (§3.1), excluding `as`.
    pub fn is_binary_op(self) -> bool {
        use TokenKind::*;
        matches!(
            self,
            Plus | Minus
                | Star
                | Slash
                | Percent
                | PlusPercent
                | MinusPercent
                | StarPercent
                | PlusPipe
                | MinusPipe
                | StarPipe
                | EqEq
                | NotEq
                | Lt
                | LtEq
                | Gt
                | GtEq
                | AndAnd
                | OrOr
                | Amp
                | Pipe
                | Caret
                | Shl
                | Shr
        )
    }

    /// Keyword for an identifier text, if it is one ([`KEYWORDS`]).
    pub fn keyword(text: &str) -> Option<TokenKind> {
        KEYWORDS.iter().find(|&&(t, _)| t == text).map(|&(_, k)| k)
    }

    /// How the token is written, for messages (`expected `)``).
    pub fn describe(self) -> &'static str {
        use TokenKind::*;
        match self {
            Whitespace => "whitespace",
            Newline => "newline",
            Comment | DocComment => "comment",
            Ident => "identifier",
            Underscore => "`_`",
            Int => "integer literal",
            Float => "float literal",
            Char => "char literal",
            Str => "string literal",
            KwFn => "`fn`",
            KwRt => "`rt`",
            KwFlow => "`flow`",
            KwPar => "`par`",
            KwStruct => "`struct`",
            KwEnum => "`enum`",
            KwTrait => "`trait`",
            KwImpl => "`impl`",
            KwEffect => "`effect`",
            KwBlocking => "`blocking`",
            KwHandler => "`handler`",
            KwHandle => "`handle`",
            KwWith => "`with`",
            KwUses => "`uses`",
            KwLet => "`let`",
            KwVar => "`var`",
            KwIf => "`if`",
            KwElse => "`else`",
            KwMatch => "`match`",
            KwFor => "`for`",
            KwIn => "`in`",
            KwWhile => "`while`",
            KwBreak => "`break`",
            KwContinue => "`continue`",
            KwReturn => "`return`",
            KwPub => "`pub`",
            KwUse => "`use`",
            KwExtern => "`extern`",
            KwUnsafe => "`unsafe`",
            KwTarget => "`target`",
            KwTest => "`test`",
            KwAssert => "`assert`",
            KwConst => "`const`",
            KwType => "`type`",
            KwAs => "`as`",
            KwInout => "`inout`",
            KwMove => "`move`",
            KwSelf => "`self`",
            KwSelfType => "`Self`",
            KwTrue => "`true`",
            KwFalse => "`false`",
            Plus => "`+`",
            Minus => "`-`",
            Star => "`*`",
            Slash => "`/`",
            Percent => "`%`",
            PlusPercent => "`+%`",
            MinusPercent => "`-%`",
            StarPercent => "`*%`",
            PlusPipe => "`+|`",
            MinusPipe => "`-|`",
            StarPipe => "`*|`",
            EqEq => "`==`",
            NotEq => "`!=`",
            Lt => "`<`",
            LtEq => "`<=`",
            Gt => "`>`",
            GtEq => "`>=`",
            AndAnd => "`&&`",
            OrOr => "`||`",
            Amp => "`&`",
            Pipe => "`|`",
            Caret => "`^`",
            Shl => "`<<`",
            Shr => "`>>`",
            Bang => "`!`",
            Tilde => "`~`",
            Eq => "`=`",
            Arrow => "`->`",
            FatArrow => "`=>`",
            Dot => "`.`",
            DotDot => "`..`",
            Comma => "`,`",
            Colon => "`:`",
            Question => "`?`",
            At => "`@`",
            LParen => "`(`",
            RParen => "`)`",
            LBracket => "`[`",
            RBracket => "`]`",
            LBrace => "`{`",
            RBrace => "`}`",
            ColonColon => "`::`",
            Semi => "`;`",
            Hash => "`#`",
            DotDotEq => "`..=`",
            PlusPlus => "`++`",
            MinusMinus => "`--`",
            BlockComment => "block comment",
            ForeignLit => "number literal",
            Error => "invalid token",
            Eof => "end of file",
        }
    }
}

/// The keywords of the language (§2.2) and their tokens: the one list that
/// [`TokenKind::keyword`] and [`TokenKind::is_keyword`] read (R-87).
pub const KEYWORDS: &[(&str, TokenKind)] = &[
    ("fn", TokenKind::KwFn),
    ("rt", TokenKind::KwRt),
    ("flow", TokenKind::KwFlow),
    ("par", TokenKind::KwPar),
    ("struct", TokenKind::KwStruct),
    ("enum", TokenKind::KwEnum),
    ("trait", TokenKind::KwTrait),
    ("impl", TokenKind::KwImpl),
    ("effect", TokenKind::KwEffect),
    ("blocking", TokenKind::KwBlocking),
    ("handler", TokenKind::KwHandler),
    ("handle", TokenKind::KwHandle),
    ("with", TokenKind::KwWith),
    ("uses", TokenKind::KwUses),
    ("let", TokenKind::KwLet),
    ("var", TokenKind::KwVar),
    ("if", TokenKind::KwIf),
    ("else", TokenKind::KwElse),
    ("match", TokenKind::KwMatch),
    ("for", TokenKind::KwFor),
    ("in", TokenKind::KwIn),
    ("while", TokenKind::KwWhile),
    ("break", TokenKind::KwBreak),
    ("continue", TokenKind::KwContinue),
    ("return", TokenKind::KwReturn),
    ("pub", TokenKind::KwPub),
    ("use", TokenKind::KwUse),
    ("extern", TokenKind::KwExtern),
    ("unsafe", TokenKind::KwUnsafe),
    ("target", TokenKind::KwTarget),
    ("test", TokenKind::KwTest),
    ("assert", TokenKind::KwAssert),
    ("const", TokenKind::KwConst),
    ("type", TokenKind::KwType),
    ("as", TokenKind::KwAs),
    ("inout", TokenKind::KwInout),
    ("move", TokenKind::KwMove),
    ("self", TokenKind::KwSelf),
    ("Self", TokenKind::KwSelfType),
    ("true", TokenKind::KwTrue),
    ("false", TokenKind::KwFalse),
];

/// A token. What precedes it (a space, a newline or nothing) is read from the
/// token list with [`gap_before`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// What separates a token from the token before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gap {
    /// Nothing: the token touches the one before (or starts the file).
    None,
    /// Spaces or tabs, without a newline.
    Space,
    /// A newline (with or without spaces around it).
    Newline,
}

impl Gap {
    /// Whitespace or a newline separates the tokens.
    pub fn is_some(self) -> bool {
        self != Gap::None
    }
}

/// The mark `::[` of type arguments in an expression at `tokens[i]` (§2.5,
/// §4.5): `::` and `[` with no space or newline before either. `all` is the
/// full token list and `full[k]` the index in it of `tokens[k]`. The one
/// test of the mark, for the parser and the table of the forms.
pub(crate) fn is_type_args_mark(all: &[Token], full: &[u32], tokens: &[Token], i: usize) -> bool {
    tokens.get(i).is_some_and(|t| t.kind == TokenKind::ColonColon)
        && tokens.get(i + 1).is_some_and(|t| t.kind == TokenKind::LBracket)
        && gap_before(all, full[i] as usize) == Gap::None
        && gap_before(all, full[i + 1] as usize) == Gap::None
}

/// What precedes `tokens[i]` in the full token list of the lexer: a newline
/// when the last token before it that is not whitespace is a newline, a space
/// when whitespace comes right before it, nothing otherwise. A comment right
/// before a token is not a gap (`/* */a`); a line comment is always followed
/// by a newline.
pub fn gap_before(tokens: &[Token], i: usize) -> Gap {
    let mut j = i;
    let mut space = false;
    while j > 0 {
        j -= 1;
        match tokens[j].kind {
            TokenKind::Whitespace => space = true,
            TokenKind::Newline => return Gap::Newline,
            _ => break,
        }
    }
    if space { Gap::Space } else { Gap::None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_keyword_list_is_one_to_one() {
        for (i, &(text, kind)) in KEYWORDS.iter().enumerate() {
            assert_eq!(TokenKind::keyword(text), Some(kind), "{text}");
            assert!(kind.is_keyword(), "{text}");
            assert_eq!(kind.describe(), format!("`{text}`"));
            assert!(KEYWORDS[..i].iter().all(|&(t, k)| t != text && k != kind), "{text} twice");
        }
        for not in [TokenKind::Ident, TokenKind::Underscore, TokenKind::Plus, TokenKind::Eof, TokenKind::Semi] {
            assert!(!not.is_keyword(), "{not:?}");
        }
        assert_eq!(TokenKind::keyword("loop"), None);
    }
}
