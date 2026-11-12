//! The rows of the binary operators of other languages (§3.1, S-450): the
//! strict comparisons `===` / `!==` and the power `**` (`**=` too) of
//! Python and JavaScript, one token each (the lexer's), after an operand on
//! its line.

use super::*;
use crate::ast::OpGroup;

/// The expression that closed right before the token at the failure, on
/// its line: the token is in the place of a binary operator of an
/// expression (not after a type, a pattern or a path of a `use`).
fn after_operand(c: &Cursor) -> Option<(NodeKind, u32)> {
    super::lines::after_operand(c, c.at).then(|| closed_expr(c)).flatten()
}

/// `a === b`, `a !== b` (S-450): the candidate is `==` / `!=` (Onsa
/// converts no type in a comparison), when it reads in the chain around it
/// ([`compares`]); else E0002 with the note.
pub(super) fn strict_equality(c: &Cursor) -> Option<Hit> {
    let symbol = match c.kind(c.at) {
        TokenKind::EqEqEq => "==",
        TokenKind::NotEqEq => "!=",
        _ => return None,
    };
    let left = after_operand(c)?;
    let span = c.span(c.at);
    let fixes = match compares(c, c.index_at(left.1)) {
        true => vec![Fix::replace(format!("compare with `{symbol}`"), span, symbol)],
        false => Vec::new(),
    };
    hit(span, fixes)
}

/// `a ** b`, `a **= b` (S-450): no operator of Onsa has its reading (C and
/// Rust read `a * (*b)`), so E0002 with the note.
pub(super) fn power_operator(c: &Cursor) -> Option<Hit> {
    (c.kind(c.at) == TokenKind::StarStar && after_operand(c).is_some()).then(|| Hit::new(c.span(c.at), Vec::new()))
}

/// Whether a comparison in place of the token at the failure reads in the
/// chain around it (§3.1; S-236): from `first` (the operand that closed
/// before it) to the end of the operand after it, every other operator
/// has a strength against the comparisons (no other comparison and no
/// bitwise operator, E0010), and there is no `as` / `at` (E0011) and no
/// operand that is a block or a keyword's form (E0013). Read once forward,
/// the brackets passed over ([`closing`]); the operand after it ends at a
/// line break, a closer, a `,`, a `;`, a `=>` or the body of a head, and
/// any other token (a struct literal, S-450) is `false`, where it cannot tell.
fn compares(c: &Cursor, first: usize) -> bool {
    use TokenKind::*;
    let (mut i, mut expect) = (first, true);
    loop {
        let k = c.kind(i);
        if i == c.at {
            (i, expect) = (c.sig_after(i), true);
            continue;
        }
        let ahead = i > c.at;
        match k {
            _ if c.comment(i) => {}
            Newline if !ahead || c.lines.goes_on(i) => {}
            Newline => return true,
            LParen | LBracket => {
                let Some(close) = closing(c, i) else { return false };
                (i, expect) = (close, false);
            }
            Minus | Bang | Caret if expect => {}
            Ident | Int | Float | Char | Str | KwTrue | KwFalse | KwSelf | KwSelfType if expect => expect = false,
            _ if expect => return false,
            _ if k.binop().is_some() => {
                let g = k.binop().map(|op| op.group());
                if !g.is_some_and(|g| g.stronger(OpGroup::Comparison) || OpGroup::Comparison.stronger(g)) {
                    return false;
                }
                expect = true;
            }
            Dot | ColonColon | Bang | Tilde => expect = true,
            Question => {}
            Comma | Semi | RParen | RBracket | RBrace | FatArrow | Eof => return ahead,
            LBrace => return ahead && in_head(c),
            _ => return false,
        }
        i += 1;
    }
}

/// Whether a `{` after the operand after the failure opens the body of the
/// head the failure is in (`if`, `while`, `for`, `match`, `par~`, where no
/// struct literal is read, S-08).
pub(super) fn in_head(c: &Cursor) -> bool {
    use NodeKind::*;
    matches!(c.context(), Some((_, IfExpr | WhileStmt | ForStmt | MatchExpr | ParExpr)))
}
