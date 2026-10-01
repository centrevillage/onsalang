//! Tokens of Onsa (spec §2).

use onsa_diag::Span;

/// Kind of a token. Comments and newlines are tokens too (trivia); the parser
/// skips comments and treats newlines by context (§2.5), `fmt` reads them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Trivia
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

    // Tokens from other languages, kept so the parser can suggest the Onsa form (E0020)
    /// `::`
    ColonColon,
    /// `;`
    Semi,
    /// `#`
    Hash,
    /// `..=`
    DotDotEq,

    /// An invalid character (E0001 was reported).
    Error,
    /// End of file.
    Eof,
}

impl TokenKind {
    pub fn is_trivia(self) -> bool {
        matches!(self, TokenKind::Newline | TokenKind::Comment | TokenKind::DocComment)
    }

    pub fn is_keyword(self) -> bool {
        (self as u8) >= (TokenKind::KwFn as u8) && (self as u8) <= (TokenKind::KwFalse as u8)
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

    /// Keyword for an identifier text, if it is one.
    pub fn keyword(text: &str) -> Option<TokenKind> {
        use TokenKind::*;
        Some(match text {
            "fn" => KwFn,
            "rt" => KwRt,
            "flow" => KwFlow,
            "par" => KwPar,
            "struct" => KwStruct,
            "enum" => KwEnum,
            "trait" => KwTrait,
            "impl" => KwImpl,
            "effect" => KwEffect,
            "blocking" => KwBlocking,
            "handler" => KwHandler,
            "handle" => KwHandle,
            "with" => KwWith,
            "uses" => KwUses,
            "let" => KwLet,
            "var" => KwVar,
            "if" => KwIf,
            "else" => KwElse,
            "match" => KwMatch,
            "for" => KwFor,
            "in" => KwIn,
            "while" => KwWhile,
            "break" => KwBreak,
            "continue" => KwContinue,
            "return" => KwReturn,
            "pub" => KwPub,
            "use" => KwUse,
            "extern" => KwExtern,
            "unsafe" => KwUnsafe,
            "target" => KwTarget,
            "test" => KwTest,
            "assert" => KwAssert,
            "const" => KwConst,
            "type" => KwType,
            "as" => KwAs,
            "inout" => KwInout,
            "move" => KwMove,
            "self" => KwSelf,
            "Self" => KwSelfType,
            "true" => KwTrue,
            "false" => KwFalse,
            _ => return None,
        })
    }

    /// How the token is written, for messages (`expected `)``).
    pub fn describe(self) -> &'static str {
        use TokenKind::*;
        match self {
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
            Error => "invalid token",
            Eof => "end of file",
        }
    }
}

/// A token. `space_before` is true when whitespace or a newline precedes it
/// (used for `f~(` / `f!(` and for `fmt`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub space_before: bool,
}
