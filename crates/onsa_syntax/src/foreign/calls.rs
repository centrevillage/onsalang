//! The callee of a call (§6.1, S-191, S-256): what is a path of names, and
//! the row of a callee that is no path of names (`.(`).

use super::*;

/// The nodes of an expression that name a path (a path of names, a method,
/// a tuple index): what a `::[…]`, a `!` or a `~` may follow, and the callees
/// whose type arguments of another language become `::[…]`. The one test,
/// for the parser and this table.
pub(crate) fn names_a_path(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::PathExpr | NodeKind::FieldExpr | NodeKind::TupleIndexExpr)
}

/// How a postfix chain has been read so far, for [`callee_by_name`]: a path
/// of names (§2.4: names and the fields, tuple indexes and `::[…]` after
/// them), that path with `[…]`s after it, a field of anything else (a
/// method, `g(x).m`), one `[…]` after such a field (`g(x).m[I32]`), or
/// anything else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CalleeChain {
    Names,
    Indexed,
    Member,
    MemberIndexed,
    Value,
}

impl CalleeChain {
    /// The chain that starts with an operand of `kind`.
    pub(crate) fn start(kind: NodeKind) -> CalleeChain {
        if kind == NodeKind::PathExpr { CalleeChain::Names } else { CalleeChain::Value }
    }

    /// The chain after its next link, a node of `kind`, closed. A field keeps
    /// a path of names (`ops[i].m[T](x)` is a method's, of the type stage,
    /// S-256); after anything else it is a member, and one `[…]` after it is
    /// a method's type arguments or an index of a field, which the type stage
    /// tells apart (`g(x).m[I32](y)`, §4.5); a tuple index ends a path of
    /// names only after names.
    pub(crate) fn then(self, kind: NodeKind) -> CalleeChain {
        use CalleeChain::*;
        match (self, kind) {
            (c @ (Names | Indexed), NodeKind::FieldExpr | NodeKind::TypeArgsExpr) => c,
            (_, NodeKind::FieldExpr) => Member,
            (Names, NodeKind::TupleIndexExpr) => Names,
            (Names | Indexed, NodeKind::IndexExpr) => Indexed,
            (Member, NodeKind::IndexExpr) => MemberIndexed,
            _ => Value,
        }
    }
}

/// Whether the callee of a call `callee(…)`, the last link (`kind`) of the
/// chain `chain`, is written by name, so that a later stage decides the
/// call (§6.1, S-191, S-256): a path of names (`f`, `s.f`; `t.0`, S-342),
/// a method (`x.f`, `g(x).f`), `::[…]` after one (`f::[T]`), a path of
/// names with `[…]` after it (`ops[i]`), or a field of anything else with
/// one `[…]` after it (`g(x).m[I32]`, §4.5). Any other callee (`(s.f)`,
/// `pick(true)`, `ts[0].0`, `mk2().0`) is no item: the parser fails at the
/// `(` with [`Want::Callee`], and the row `callee_expression` gives `.(`.
/// The one test, for the parser and that row.
pub(crate) fn callee_by_name(kind: NodeKind, chain: CalleeChain) -> bool {
    match kind {
        NodeKind::PathExpr | NodeKind::FieldExpr | NodeKind::TypeArgsExpr => true,
        NodeKind::TupleIndexExpr => chain == CalleeChain::Names,
        NodeKind::IndexExpr => matches!(chain, CalleeChain::Indexed | CalleeChain::MemberIndexed),
        _ => false,
    }
}

/// A callee that is a value and no path (`(e)`, `g(x)`, `xs[i]`, `x?`): no
/// `::[` can be written after it, and it is called with `.(` (§6.1).
pub(super) fn is_value_callee(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::ParenExpr | NodeKind::CallExpr | NodeKind::IndexExpr | NodeKind::TryExpr)
}

/// The candidate that calls the value `callee` with `.(` in place of the
/// type arguments in `first..=last` (the call's `(` follows `last`): the
/// list and the blanks before it become `.`, and the parentheses around a
/// postfix expression go (`(s.f)` is `s.f.(x)`, §4.5).
pub(super) fn value_call(c: &Cursor, callee: (NodeKind, u32), first: usize, last: usize) -> Option<Fix> {
    if c.kind(last + 1) != TokenKind::LParen || c.gap(last + 1) != Gap::None {
        return None;
    }
    let before = first.checked_sub(1)?;
    let mut edits = vec![Edit::replace(c.file_span(c.span(before).end, c.span(last).end), ".")];
    if let Some(open) = removable_parens(c, callee, before) {
        edits.push(Edit::delete(c.span(open)));
        edits.push(Edit::delete(c.span(before)));
    }
    Some(Fix::new("call the function value with `.(`", edits))
}

/// The `(` of the callee `callee` that closes at `close`, when the
/// parentheses can go before `.(`: the callee is a parenthesis around a
/// postfix expression (a path of names and the fields, tuple indexes,
/// indexes, calls and `?` after it), which `.(` follows with the same
/// reading (S-236). `(a + b)` keeps them, and so does a `(` that touches a
/// word before it (`return(s.f)`: the word would join the name, S-302).
fn removable_parens(c: &Cursor, callee: (NodeKind, u32), close: usize) -> Option<usize> {
    if callee.0 != NodeKind::ParenExpr || c.kind(close) != TokenKind::RParen {
        return None;
    }
    let open = c.index_at(callee.1);
    let word = |k: TokenKind| matches!(k, TokenKind::Ident | TokenKind::Int | TokenKind::Float) || k.is_keyword();
    if c.gap(open) == Gap::None && open.checked_sub(1).is_some_and(|b| word(c.kind(b))) {
        return None;
    }
    is_postfix_chain(c, open + 1, close.checked_sub(1)?).then_some(open)
}

/// The tokens `first..=last` are a postfix expression on one line: a name,
/// `self` or `Self` and, after it, only `.name`, `.0`, `.(…)`, `(…)`,
/// `[…]`, `::[…]`, `~(…)`, `!(…)` and `?`.
fn is_postfix_chain(c: &Cursor, first: usize, last: usize) -> bool {
    if first > last || !matches!(c.kind(first), TokenKind::Ident | TokenKind::KwSelf | TokenKind::KwSelfType) {
        return false;
    }
    let after_group = |open: usize| closing(c, open).map(|close| close + 1);
    let mut i = first + 1;
    while i <= last {
        let next = match (c.kind(i), c.kind(i + 1)) {
            (TokenKind::Dot, TokenKind::LParen) => after_group(i + 1),
            (TokenKind::Dot, k) if k == TokenKind::Ident || k == TokenKind::Int || k.is_keyword() => Some(i + 2),
            (TokenKind::LParen | TokenKind::LBracket, _) => after_group(i),
            (TokenKind::ColonColon, TokenKind::LBracket)
            | (TokenKind::Tilde, TokenKind::LParen)
            | (TokenKind::Bang, TokenKind::LParen) => after_group(i + 1),
            (TokenKind::Question, _) => Some(i + 1),
            _ => None,
        };
        let Some(next) = next else { return false };
        i = next;
    }
    i == last + 1
}

/// A call whose callee is neither a path of names nor a path of names with
/// `[…]` (`(s.f)(x)`, `pick(true)(5)`, `h.(1)(2)`, §6.1, S-191): no item is
/// such a callee, so the parser fails at its `(`. The one candidate calls the
/// value with `.(`: the parentheses around a postfix expression go and the
/// `)` becomes the `.` (`s.f.(x)`); else a `.` goes before the `(`
/// (`pick(true).(5)`, `(a + b).(1)`). An integer literal as the callee has
/// none (`1.(2)` reads as the literal `1.`, §2.4).
pub(super) fn callee_expression(c: &Cursor) -> Option<Hit> {
    // The parser has judged the callee ([`callee_by_name`]).
    if c.want != Want::Callee {
        return None;
    }
    let callee = closed_expr(c)?;
    let before = c.at.checked_sub(1)?;
    // From the callee to the `(` the parser failed at: the arguments, not
    // read yet, may hold errors of their own.
    let span = c.file_span(callee.1, c.span(c.at).end);
    let edits = match removable_parens(c, callee, before) {
        Some(open) => vec![Edit::delete(c.span(open)), Edit::replace(c.span(before), ".")],
        // Not a tuple index (`ts[0].0.(x)` reads as written).
        None if callee.0 == NodeKind::Literal && c.kind(before) == TokenKind::Int => return hit(span, Vec::new()),
        None => vec![Edit::insert(c.file, c.span(c.at).start, ".")],
    };
    // The call takes the callee one level down (§2.5): no candidate that
    // takes the unit over the limit, where the check after it would report
    // the E0006 of the same stage (S-236, R-200).
    let added = u32::from(edits.len() == 1);
    if crate::groups::nests_too_deep(c.text, span, &edits, added, crate::parser::NESTING_LIMIT) {
        return hit(span, Vec::new());
    }
    hit(span, vec![Fix::new("call the function value with `.(`", edits)])
}
