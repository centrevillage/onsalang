//! Tokens of Onsa (spec §2).

use onsa_diag::Span;

use crate::ast::{BinOp, RangeEnd};

/// Declares [`TokenKind`] and [`TokenKind::ALL`] from one list, so that the
/// list of every kind cannot miss one.
macro_rules! token_kinds {
    ($(#[$meta:meta])* pub enum TokenKind { $($(#[$vmeta:meta])* $variant:ident,)* }) => {
        $(#[$meta])*
        pub enum TokenKind {
            $($(#[$vmeta])* $variant,)*
        }

        impl TokenKind {
            /// Every kind, in the order of its declaration.
            pub const ALL: &'static [TokenKind] = &[$(TokenKind::$variant),*];
        }
    };
}

token_kinds! {
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
    /// `at`: the clock of an input, an output or an expression (§11.3).
    KwAt,
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
    /// `..<`: a range without its end (§7).
    DotDotLt,
    /// `..=`: a range with its end (§7).
    DotDotEq,
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
    /// `..`: a range of other languages (S-257), and the rest of a struct
    /// pattern of Rust (S-109).
    DotDot,
    /// `...`: a range of other languages (S-257).
    DotDotDot,
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
}

impl TokenKind {
    /// The readings of a range symbol (S-257), in the order of the
    /// candidates: one for `..<` and `..=`, both for `..` and `...` of other
    /// languages; none for another token. The one place that classifies the
    /// range symbols (the parser, the table of the forms, the lowering).
    pub fn range_readings(self) -> &'static [RangeEnd] {
        match self {
            TokenKind::DotDotLt => &[RangeEnd::Excluded],
            TokenKind::DotDotEq => &[RangeEnd::Included],
            TokenKind::DotDot | TokenKind::DotDotDot => &[RangeEnd::Excluded, RangeEnd::Included],
            _ => &[],
        }
    }

    /// The end of an Onsa range symbol (`..<`, `..=`); none for another
    /// token, the symbols of other languages too.
    pub fn range_end(self) -> Option<RangeEnd> {
        match self.range_readings() {
            [end] => Some(*end),
            _ => None,
        }
    }

    /// A range symbol of other languages (`..`, `...`).
    pub fn is_foreign_range(self) -> bool {
        self.range_readings().len() > 1
    }

    pub fn is_trivia(self) -> bool {
        matches!(self, TokenKind::Whitespace | TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment)
    }

    /// A comment of any kind: `//`, `///` and the block comment of other
    /// languages (a token of its own, which its row reports): the one test
    /// of a comment where code is looked for (the line facts, the table).
    #[inline]
    pub fn is_comment(self) -> bool {
        matches!(self, TokenKind::Comment | TokenKind::DocComment | TokenKind::BlockComment)
    }

    /// Code: no whitespace, line break or comment ([`TokenKind::is_comment`]).
    /// A line goes on or not by its code (§2.5).
    #[inline]
    pub fn is_code(self) -> bool {
        !matches!(self, TokenKind::Whitespace | TokenKind::Newline) && !self.is_comment()
    }

    /// A keyword (§2.2): one of [`KEYWORDS`], not an order of the declarations (R-87).
    pub fn is_keyword(self) -> bool {
        KEYWORDS.iter().any(|&(_, k)| k == self)
    }

    /// The binary operator of the token (§3.1), if it is one (`as` is none):
    /// the one map, for the parser, the line facts, the table and the lowering.
    #[inline]
    pub fn binop(self) -> Option<BinOp> {
        use TokenKind::*;
        Some(match self {
            Plus => BinOp::Add,
            Minus => BinOp::Sub,
            Star => BinOp::Mul,
            Slash => BinOp::Div,
            Percent => BinOp::Rem,
            PlusPercent => BinOp::WrapAdd,
            MinusPercent => BinOp::WrapSub,
            StarPercent => BinOp::WrapMul,
            PlusPipe => BinOp::SatAdd,
            MinusPipe => BinOp::SatSub,
            StarPipe => BinOp::SatMul,
            EqEq => BinOp::Eq,
            NotEq => BinOp::Ne,
            Lt => BinOp::Lt,
            LtEq => BinOp::Le,
            Gt => BinOp::Gt,
            GtEq => BinOp::Ge,
            AndAnd => BinOp::And,
            OrOr => BinOp::Or,
            Amp => BinOp::BitAnd,
            Pipe => BinOp::BitOr,
            Caret => BinOp::BitXor,
            Shl => BinOp::Shl,
            Shr => BinOp::Shr,
            _ => return None,
        })
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
            KwAt => "`at`",
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
            DotDotLt => "`..<`",
            DotDotEq => "`..=`",
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
            DotDot => "`..`",
            DotDotDot => "`...`",
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
    ("at", TokenKind::KwAt),
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

impl Gap {
    /// The gap before the token after a token of `kind`, when `self` is the
    /// gap before that token: a newline after a newline (with or without
    /// blanks after it), a blank after whitespace, and nothing after any
    /// other token (a comment right before a token is not a gap, `/* */a`; a
    /// line comment is always followed by a newline). The one rule of the
    /// gaps: [`gap_before`] and the line facts ([`crate::layout::Lines`],
    /// which keep it for every token the parser reads) fold it over the full
    /// token list.
    #[inline]
    pub fn then(self, kind: TokenKind) -> Gap {
        match kind {
            TokenKind::Whitespace if self == Gap::None => Gap::Space,
            TokenKind::Whitespace => self,
            TokenKind::Newline => Gap::Newline,
            _ => Gap::None,
        }
    }
}

/// What precedes the token `tokens[i]` of the full token list of the lexer
/// ([`Gap::then`] from the last token before it that is no whitespace).
pub fn gap_before(tokens: &[Token], i: usize) -> Gap {
    let from = tokens[..i].iter().rposition(|t| t.kind != TokenKind::Whitespace).unwrap_or(0);
    tokens[from..i].iter().fold(Gap::None, |gap, t| gap.then(t.kind))
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
