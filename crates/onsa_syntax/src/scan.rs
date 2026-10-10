//! The scans of a run of tokens that read no node (S-384, S-419): where a
//! bracket closes and what is directly in it, whether an arm goes on to its
//! `=>`, where an alternative of a pattern ends. The parser and the table of
//! the forms of other languages ([`crate::foreign`]) read a run of tokens
//! through them alike (D-15); what one token starts is [`crate::starts`].

use crate::token::{Token, TokenKind};

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

/// Whether an arm goes on from token `i` to its `=>`: a `=>` at the depth of
/// `i` comes before the next `,` or `}` there (S-386, S-419). The scan of the
/// tokens, which reads no element on (S-384): a symbol at the head of the
/// line that starts it is no binary operator of the arm before, and the
/// line break before an opener there is no gap inside a postfix.
pub(crate) fn arm_ahead(tokens: &[Token], i: usize) -> bool {
    let mut depth = 0u32;
    for t in &tokens[i..] {
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
