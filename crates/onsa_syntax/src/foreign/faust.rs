//! The rows of the forms of FAUST (§2.6, §11.2, §11.4, §18.1; S-48, R-59):
//! the feedback `~ _`, the delay `x@N` and the operators that compose
//! signals, which the parser fails at; and the prefix `~` of C, the bitwise
//! negation, which the rows of `if~` / `match~` read too. The FAUST `x'` is a
//! literal right against a name (the row `string_prefix`, S-466), whose note
//! [`prime_note`] gives.
//!
//! Out of support (`rules/criteria.md` 7.32): the forms of
//! FAUST are not diagnosed by rows of their own any more. The rows here stay
//! while they are no trouble; one that conflicts with a new decision, fails
//! the gate or needs a fix is removed with its cases, not fixed. The prefix
//! `~` of C ([`bit_not`]) stays in support.

use super::*;
use crate::literal::int_value;
use crate::naming::is_constant_name;
use crate::starts::starts_operand;

/// The rows [`faust_feedback`] names ([`super::Matcher::many`]).
pub(super) const FAUST_FEEDBACK_ROWS: &[RowId] = &[RowId::FaustFeedback, RowId::FaustFeedbackUnnamed];

/// The feedback `~ _` of FAUST where an operand stands (S-48): `prev~(^y)`,
/// for the name `y` of the `let` it is the value of ([`feedback_name`]); with
/// no such name, no candidate (the row `faust_feedback_unnamed`, the E0002
/// with the note). The range is the `~` and the `_`.
pub(super) fn faust_feedback(c: &Cursor) -> Option<(RowId, Hit)> {
    use TokenKind::*;
    let wild = c.at + 1;
    if c.kind(c.at) != Tilde
        || c.want != Want::Expr
        || c.kind(wild) != Underscore
        || c.gap(wild) == Gap::Newline
        || (c.gap_after(wild) == Gap::None
            && matches!(c.kind(wild + 1), LParen | LBracket | Dot | Tilde | Bang | Question))
        || c.sig_before(c.at).is_some_and(|p| c.branch(p).is_some())
    {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(wild).end);
    let Some(name) = feedback_name(c) else { return found(RowId::FaustFeedbackUnnamed, span, Vec::new()) };
    // The `~` stays (S-251): the text is written around it, the `_` replaced.
    let written = format!("prev~(^{name})");
    let (before, after) = written.split_once('~').unwrap_or((&written, ""));
    let edits = vec![
        Edit::insert(span.file, span.start, before),
        Edit::replace(c.file_span(c.span(c.at).end, c.span(wild).end), after),
    ];
    let fix = Fix::new(format!("write `{written}`"), edits);
    found(RowId::FaustFeedback, span, vec![fix])
}

/// The name the feedback at the cursor feeds back (S-48): the `~ _` is the
/// right operand of a binary operator, in the value of the innermost `let`
/// of one name in the body of a flow, with no `par` or anonymous function
/// between them.
fn feedback_name<'c>(c: &Cursor<'c>) -> Option<&'c str> {
    // Out of support (S-479, FAUST): where the `let` name is not plain (`let y = ~ _`,
    // `let _`, a tuple, a `fn`, a `par`), no name: no candidate.
    let op = c.sig_before(c.at)?;
    let left = c.sig_before(op)?;
    if c.kind(op).binop().is_none() || !ends_operand(c.kind(left)) || !in_flow(c) {
        return None;
    }
    let k = c.open.iter().rposition(|o| o.0 == NodeKind::LetStmt)?;
    // `in_flow`: no anonymous function is open in the flow.
    if c.open[k + 1..].iter().any(|o| o.0 == NodeKind::ParExpr) {
        return None;
    }
    let kw = c.index_at(c.open[k].1);
    let name = c.sig_after(kw);
    let plain = c.kind(kw) == TokenKind::KwLet
        && c.kind(name) == TokenKind::Ident
        && matches!(c.kind(c.sig_after(name)), TokenKind::Eq | TokenKind::Colon);
    plain.then(|| {
        let s = c.span(name);
        &c.text[s.start as usize..s.end as usize]
    })
}

/// The innermost function around the failure is a flow (not a `fn` or an
/// anonymous function): the forms of FAUST are read in the body of a flow
/// only (S-479, S-478, S-485: elsewhere a candidate would leave the error of
/// a flow call in a function). The other questions of a flow in the table
/// are of its inputs (`decls::hash_attribute`, the clocks of `flow`).
fn in_flow(c: &Cursor) -> bool {
    let function = |k: NodeKind| matches!(k, NodeKind::Fn | NodeKind::Flow | NodeKind::ClosureExpr);
    c.open.iter().rev().find(|o| function(o.0)).is_some_and(|o| o.0 == NodeKind::Flow)
}

/// The rows [`faust_delay`] names ([`super::Matcher::many`]).
pub(super) const FAUST_DELAY_ROWS: &[RowId] = &[RowId::FaustDelay, RowId::FaustDelayVariable];

/// The delay `x@N` of FAUST in a flow (S-48): `prev~(x)` for 1,
/// `delay~(x, N)` for an integer literal of 2 or more and for a constant's
/// name (`UPPER_SNAKE`; its value is the later check's, E0807); no candidate
/// for another name (the row `faust_delay_variable`). The operand is one
/// name, and the `@` touches it and the length, which ends the operand. The
/// range is the `@` and the length.
pub(super) fn faust_delay(c: &Cursor) -> Option<(RowId, Hit)> {
    use TokenKind::*;
    // Out of support (S-478, FAUST): the other forms (`x@0`, `x@1.5`, `x @ 2`, `p.x@2`,
    // `x@N+1`, in a `fn`) are none of the list: the general E0002.
    let (at, len) = (c.at, c.at + 1);
    if c.kind(at) != At
        || !matches!(c.kind(len), Int | Ident)
        || c.gap(at).is_some()
        || c.gap_after(at).is_some()
        || !in_flow(c)
        || c.open.iter().any(|o| o.0.class() == Class::Type)
    {
        return None;
    }
    let name = at.checked_sub(1)?;
    let operand = c.closed.iter().find(|o| o.0.class() == Class::Expr)?;
    if c.kind(name) != Ident
        || operand.0 != NodeKind::PathExpr
        || operand.1 != c.span(name).start
        || (c.gap(name) == Gap::None && c.before(name).is_some_and(|b| c.kind(b) == Caret))
    {
        return None;
    }
    let next = len + 1;
    if c.gap(next) == Gap::None
        && !c.comment(next)
        && !matches!(c.kind(next), RParen | RBracket | RBrace | Comma | Newline | Eof)
    {
        return None;
    }
    let span = c.file_span(c.span(at).start, c.span(len).end);
    let one = match c.kind(len) {
        Int if c.literal_ok(len) => match int_value(c.src(len))? {
            0 => return None,
            n => n == 1,
        },
        Ident if is_constant_name(c.src(len)) => false,
        Ident => return found(RowId::FaustDelayVariable, span, Vec::new()),
        _ => return None,
    };
    let x = c.src(name);
    let fix = if one {
        Fix::new(
            format!("write `prev~({x})`"),
            vec![Edit::insert(c.file, c.span(name).start, "prev~("), Edit::replace(span, ")")],
        )
    } else {
        Fix::new(
            format!("write `delay~({x}, {})`", c.src(len)),
            vec![
                Edit::insert(c.file, c.span(name).start, "delay~("),
                Edit::replace(c.span(at), ", "),
                Edit::insert(c.file, c.span(len).end, ")"),
            ],
        )
    };
    found(RowId::FaustDelay, span, vec![fix])
}

/// The operators of FAUST that compose signals, after an operand in a flow
/// (S-48): `x : x`, `x <: x`, `x :> x` and `x, x` where no list is. No
/// candidate (E0002 with the note). The range is the operator.
pub(super) fn faust_compose(c: &Cursor) -> Option<Hit> {
    use TokenKind::*;
    // Out of support (S-485, FAUST): read only in the value of a `let` and an expression
    // that stands as a statement (the last one too) of the body of a flow or
    // of a branch, out of brackets and heads ([`stands_as_statement`]); a
    // blank before the `:` forms and an operand after them on the line; a
    // `,` where no list is. Elsewhere the general E0002.
    let at = c.at;
    let (first, last) = match c.kind(at) {
        // `<:`: the parser read the `<` as the binary operator.
        Colon if c.want == Want::Expr => (c.before(at).filter(|&b| c.kind(b) == Lt && c.gap(at) == Gap::None)?, at),
        Colon if c.gap_after(at) == Gap::None && c.kind(at + 1) == Gt => (at, at + 1),
        Colon => (at, at),
        Comma if c.want == Want::Other => (at, at),
        _ => return None,
    };
    if (c.kind(at) == Colon && c.gap(first) != Gap::Space)
        || (c.want != Want::Expr && closed_expr(c).is_none())
        || c.gap(last + 1) == Gap::Newline
        || !starts_operand(c.kind(last + 1))
        || !in_flow(c)
        || !stands_as_statement(c)
    {
        return None;
    }
    hit(c.file_span(c.span(first).start, c.span(last).end), Vec::new())
}

/// The failure is in the value of a `let` or in an expression that stands
/// as a statement, of a block that is the body of a flow, a branch or a
/// `par` (S-485): out of the open nodes that started before the failing
/// token, the innermost that is no binary, prefix or `as` expression is the
/// statement, and the block around it is such a body. Brackets and heads
/// (`if c : x`, `[0; 3, 4]`, `f~(x, a : 1)`) and a block of its own
/// (`{ a : 1 }`) are none.
fn stands_as_statement(c: &Cursor) -> bool {
    use NodeKind::*;
    let at = c.span(c.at).start;
    let mut outward = c.open.iter().rev().filter(|o| o.1 < at).map(|o| o.0);
    let mut node = outward.next();
    while matches!(node, Some(BinaryExpr | PrefixExpr | CastExpr)) {
        node = outward.next();
    }
    if matches!(node, Some(LetStmt | ExprStmt)) {
        node = outward.next();
    }
    node == Some(Block) && matches!(outward.next(), Some(Flow | IfExpr | ParExpr))
}

/// The note of the row `string_prefix` for a literal whose delimiter is `'`
/// right after a name (S-466): the FAUST `x'`, a delay of one sample.
/// Out of support (FAUST, see the module).
pub(super) fn prime_note(text: &str, range: Span) -> Option<&'static str> {
    let form = &text[range.start as usize..range.end as usize];
    let name = form.find(['\'', '"'])?;
    (name > 0 && form[name..].starts_with('\''))
        .then_some("a delay of one sample (the `x'` of FAUST) is written `prev~(x)`")
}

/// A prefix `~` of the C languages (the bitwise negation): `!x`, `!(x)`
/// (§2.6, §18.1, R-202). `~` after a name is the flow-call mark, and `~ _`
/// is the feedback of FAUST ([`faust_feedback`]).
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
    if c.kind(c.at) != TokenKind::Tilde || c.gap_after(c.at).is_some() || c.kind(c.at + 1) == TokenKind::Underscore {
        return None;
    }
    // Out of support (S-486, FAUST): a `_` in the parentheses of `~(…)` (out of nested
    // brackets) is the feedback of FAUST (`x + ~(_ * 0.5)`), which `!` would
    // leave a typed hole: no reading of the row (the general E0002).
    if c.kind(c.at + 1) == TokenKind::LParen && holds_wild(c, c.at + 1) {
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

/// The last token of a plain operand that starts at token `i`: a name, a
/// literal or a group in parentheses, with fields, calls and indexes after
/// it (touching it).
fn operand_end(c: &Cursor, i: usize) -> Option<usize> {
    use TokenKind::*;
    if c.gap(i).is_some() {
        return None;
    }
    let mut end = match c.kind(i) {
        Ident | KwSelf | Int | Float | KwTrue | KwFalse => i,
        LParen => group_end(c, i)?,
        _ => return None,
    };
    loop {
        let n = end + 1;
        if c.gap(n).is_some() {
            return Some(end);
        }
        match c.kind(n) {
            Dot if matches!(c.kind(n + 1), Ident | Int) => end = n + 1,
            LParen | LBracket => end = group_end(c, n)?,
            _ => return Some(end),
        }
    }
}

/// The `)` or `]` that closes the `(` or `[` at `open` on its line.
fn group_end(c: &Cursor, open: usize) -> Option<usize> {
    use TokenKind::*;
    let mut depth = 0;
    for k in open.. {
        match c.kind(k) {
            LParen | LBracket => depth += 1,
            RParen | RBracket => depth -= 1,
            Eof | Newline | LBrace | RBrace => return None,
            _ => {}
        }
        if depth == 0 {
            return Some(k);
        }
    }
    None
}

/// Whether a `_` is right inside the brackets that open at `open` (out of
/// nested brackets), up to their close or the end of the file.
fn holds_wild(c: &Cursor, open: usize) -> bool {
    use TokenKind::*;
    let mut depth = 0;
    for k in open..c.tokens.len() {
        match c.kind(k) {
            LParen | LBracket | LBrace => depth += 1,
            RParen | RBracket | RBrace => depth -= 1,
            Underscore if depth == 1 => return true,
            Eof => return false,
            _ => {}
        }
        if depth == 0 {
            return false;
        }
    }
    false
}
