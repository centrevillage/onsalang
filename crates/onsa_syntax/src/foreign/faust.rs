//! The row of the prefix `~` of C, the bitwise negation (§2.6, §18.1), which
//! the rows of `if~` / `match~` read too.

use super::*;

/// A prefix `~` of the C languages (the bitwise negation): `!x` (§2.6,
/// §18.1). `~` after a name is the flow-call mark, and `~ _` is the feedback
/// of FAUST (another row).
/// The row reads a prefix `~` that touches its operand and follows no name
/// (S-123) and is not the `~` of an `if` / `match` with a blank before it
/// (S-354, S-355: [`Cursor::branch`]; the `if` of a guard is none).
pub(super) fn faust_bit_not(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Tilde
        || c.want != Want::Expr
        || c.sig_before(c.at).is_some_and(|p| c.branch(p).is_some())
    {
        return None;
    }
    hit(c.span(c.at), bit_not(c)?)
}

/// The prefix `~` at the cursor read as the bitwise negation of C: its
/// candidates (none: E0002 with the note), or `None` when it does not touch
/// an operand. `space_after_branch_keyword` and `else_if_tilde` give the
/// same reading as their second candidate (S-354).
pub(super) fn bit_not(c: &Cursor) -> Option<Vec<Fix>> {
    // It touches its operand only on its line with no blank (S-385).
    if c.kind(c.at) != TokenKind::Tilde
        || c.gap_after(c.at).is_some()
        || matches!(c.kind(c.at + 1), TokenKind::Underscore | TokenKind::LParen)
    {
        return None;
    }
    // `!` beside another prefix operator would be a stack of them (E0012):
    // no candidate then.
    let prefix =
        |k: TokenKind| matches!(k, TokenKind::Minus | TokenKind::Bang | TokenKind::Tilde | TokenKind::MinusMinus);
    if c.top() == Some(NodeKind::PrefixExpr) || matches!(c.kind(c.at + 1), TokenKind::Tilde | TokenKind::MinusMinus) {
        return Some(Vec::new());
    }
    // The operand of `!` is no `move x` or `inout x` (§5.2): no candidate.
    if matches!(c.kind(c.at + 1), TokenKind::KwMove | TokenKind::KwInout) {
        return Some(Vec::new());
    }
    // The operand of `move` and `inout` is a postfix expression (§5.2, R-42):
    // `move !x` is no form either, so there is no candidate (the E0002).
    if c.sig_before(c.at).is_some_and(|p| matches!(c.kind(p), TokenKind::KwMove | TokenKind::KwInout)) {
        return Some(Vec::new());
    }
    if prefix(c.kind(c.at + 1)) {
        // `~-x`: `!(-x)`, the operand in parentheses (no stack of prefix
        // operators, §3.1); only when the operand is plain.
        let Some(end) = operand_end(c, c.at + 2) else { return Some(Vec::new()) };
        let fix =
            Fix::new("write `!`", vec![Edit::replace(c.span(c.at), "!("), Edit::insert(c.file, c.span(end).end, ")")]);
        return Some(vec![fix]);
    }
    Some(vec![Fix::replace("write `!`", c.span(c.at), "!")])
}

/// The last token of a plain operand that starts at token `i`: a name or a
/// literal, with fields, calls and indexes after it (touching it).
fn operand_end(c: &Cursor, i: usize) -> Option<usize> {
    use TokenKind::*;
    if !matches!(c.kind(i), Ident | KwSelf | Int | Float | KwTrue | KwFalse) || c.gap(i).is_some() {
        return None;
    }
    let mut end = i;
    loop {
        let n = end + 1;
        if c.gap(n).is_some() {
            return Some(end);
        }
        match c.kind(n) {
            Dot if matches!(c.kind(n + 1), Ident | Int) => end = n + 1,
            LParen | LBracket => {
                let mut depth = 0;
                let mut k = n;
                loop {
                    match c.kind(k) {
                        LParen | LBracket => depth += 1,
                        RParen | RBracket => depth -= 1,
                        Eof | Newline | LBrace | RBrace => return None,
                        _ => {}
                    }
                    if depth == 0 {
                        break;
                    }
                    k += 1;
                }
                end = k;
            }
            _ => return Some(end),
        }
    }
}
