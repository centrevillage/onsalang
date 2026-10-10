//! The rows of the compound assignments and the increments (`+=`, `++`,
//! `a--b`; S-250, S-297, S-320).

use super::*;

/// The operators of the compound assignments (S-250).
fn compound_operator(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Plus | Minus | Star | Slash | Percent | Amp | Pipe | Caret | Shl | Shr)
}

/// The top of the expression of `kinds` (its tokens, comments and all) as
/// an operand ([`Operand`]): read by the brackets and the operators outside
/// them (a `-`, a `!` or a `^` where an operand starts is a prefix, or the
/// mark of a name). The one reading of the written text for the candidates
/// that parenthesize (the guards, `needs_parens`, the clock moved to a value);
/// [`crate::ast::BinOp::bare`] decides with it. A chain whose
/// operators have no weakest group (an error E0010 of its own) is taken as
/// needing parentheses.
pub(super) fn operand(kinds: &[TokenKind]) -> Operand {
    let mut depth = 0u32;
    let mut expect = true;
    let mut ops: Vec<BinOp> = Vec::new();
    let mut cast = false;
    for &k in kinds.iter().filter(|k| !k.is_trivia()) {
        match k {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1);
                expect = false;
            }
            _ if depth > 0 => {}
            // A prefix operator, and the mark `^` of a name (§2.6), where an
            // operand starts.
            TokenKind::Minus | TokenKind::Bang | TokenKind::Caret if expect => {}
            TokenKind::KwAs | TokenKind::KwAt => {
                cast = true;
                expect = true;
            }
            _ => match k.binop() {
                Some(op) => {
                    ops.push(op);
                    expect = true;
                }
                None => expect = false,
            },
        }
    }
    let weakest = |r: &&BinOp| ops.iter().all(|o| o.group() == r.group() || o.group().stronger(r.group()));
    match ops.iter().rev().find(weakest) {
        Some(&root) => Operand::Binary(root),
        None if !ops.is_empty() || cast => Operand::AsAt,
        None => Operand::Plain,
    }
}

/// Whether the expression `first..=last` needs parentheses as the right
/// operand of the binary operator `op` ([`crate::ast::BinOp::bare`]). An
/// operand that starts with a prefix operator is parenthesized too, so that
/// the written-out assignment reads as the compound one (`x = x - (-y)`).
fn needs_parens(c: &Cursor, op: TokenKind, first: usize, last: usize) -> bool {
    if matches!(c.kind(first), TokenKind::Minus | TokenKind::Bang) {
        return true;
    }
    let operand = operand(&(first..=last).map(|i| c.kind(i)).collect::<Vec<_>>());
    op.binop().is_none_or(|op| !op.bare(crate::ast::Side::Right, operand))
}

/// `x += 1` (and the other operators): `x = x + 1` when it is a statement
/// whose left side is a name or a path of fields (S-250). A left side that
/// would be read twice (`a[i] += 1`) and an expression (`let y = x += 1`) are
/// E0002 with the note.
pub(super) fn compound_assignment(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr || c.kind(c.at) != TokenKind::Eq || c.gap(c.at).is_some() {
        return None;
    }
    let op = c.at.checked_sub(1).filter(|&o| compound_operator(c.kind(o)))?;
    let span = c.file_span(c.span(op).start, c.span(c.at).end);
    let unfixable = || {
        c.say(RowId::CompoundAssignUnfixable);
        hit(span, Vec::new())
    };
    let statement = c.top() == Some(NodeKind::BinaryExpr) && c.open_at(1).is_some_and(|o| o.0 == NodeKind::Block);
    if !statement {
        return unfixable();
    }
    let lhs_first = c.index_at(c.open_at(0)?.1);
    let rhs_first = c.sig_after(c.at);
    let rhs_last = statement_end(c, rhs_first);
    let (Some(rhs_last), true) = (rhs_last, is_place(c, lhs_first, op - 1)) else { return unfixable() };
    if rhs_last < rhs_first {
        return unfixable();
    }
    let lhs = &c.text[c.span(lhs_first).start as usize..c.span(op - 1).end as usize];
    let parens = needs_parens(c, c.kind(op), rhs_first, rhs_last);
    let mut edits = vec![
        Edit::delete(c.span(op)),
        Edit::replace(
            c.file_span(c.span(c.at).end, c.span(rhs_first).start),
            format!(" {lhs} {} {}", c.src(op), if parens { "(" } else { "" }),
        ),
    ];
    if parens {
        edits.push(Edit::insert(c.file, c.span(rhs_last).end, ")"));
    }
    hit(span, vec![Fix::new("write the assignment out", edits)])
}

/// `a--b`, `5--3` (S-320): a binary `-` and a prefix one written without a
/// blank between them are the `--` of other languages, which read it apart
/// (C: `a-- b`, an error; Rust: `a - (-b)`). The candidate is `a - -b`. The
/// `--` follows an operand on its line and an operand that is not a prefix
/// one follows it at once; else it is an increment ([`increment`]).
pub(super) fn binary_minus_prefix_minus(c: &Cursor) -> Option<Hit> {
    if !binary_minus_minus(c) {
        return None;
    }
    let span = c.span(c.at);
    let text = if c.gap(c.at) == Gap::None { " - -" } else { "- -" };
    hit(span, vec![Fix::replace("write the two `-` apart", span, text)])
}

fn binary_minus_minus(c: &Cursor) -> bool {
    if c.kind(c.at) != TokenKind::MinusMinus {
        return false;
    }
    // A `--` is not the last token (an `Eof` follows it).
    let next = c.kind(c.at + 1);
    // SPEC-GAP(S-349): a blank before the `--` (`a --b`) is the form too.
    c.before(c.at).is_some()
        && !c.at_line_head(c.at)
        && closed_expr(c).is_some()
        && c.gap_after(c.at) == Gap::None
        && !matches!(next, TokenKind::Minus | TokenKind::Bang)
        && crate::starts::starts_operand(next)
}

/// `++x`, `x++`, `--x`, `x--` (S-250, S-297): `x = x + 1` as a statement
/// whose operand is a name or a path of fields; else E0002 with the note.
pub(super) fn increment(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    if !matches!(kind, TokenKind::PlusPlus | TokenKind::MinusMinus) || binary_minus_minus(c) {
        return None;
    }
    let op = if kind == TokenKind::PlusPlus { "+" } else { "-" };
    let span = c.span(c.at);
    let none = || {
        c.say(RowId::IncrementUnfixable);
        hit(span, Vec::new())
    };
    // `++x` as a statement: nothing of it was read yet.
    if c.want == Want::Expr && c.top() == Some(NodeKind::Block) {
        let first = c.at + 1;
        let Some(last) = statement_end(c, first) else { return none() };
        if !is_place(c, first, last) || !ends_statement(c, last) {
            return none();
        }
        let place = &c.text[c.span(first).start as usize..c.span(last).end as usize];
        let fix = Fix::new(
            "write the assignment out",
            vec![
                Edit::delete(c.file_span(span.start, c.span(first).start)),
                Edit::insert(c.file, c.span(last).end, format!(" = {place} {op} 1")),
            ],
        );
        return hit(span, vec![fix]);
    }
    // `x++` as a statement: the statement `x` closed before it.
    if let [(NodeKind::PathExpr | NodeKind::FieldExpr | NodeKind::TupleIndexExpr, start), .., (NodeKind::ExprStmt, _)] =
        c.closed
        && c.top() == Some(NodeKind::Block)
        && ends_statement(c, c.at)
    {
        let first = c.index_at(*start);
        if is_place(c, first, c.at - 1) && c.gap(c.at) == Gap::None {
            let place = &c.text[c.span(first).start as usize..c.span(c.at - 1).end as usize];
            return hit(span, vec![Fix::replace("write the assignment out", span, format!(" = {place} {op} 1"))]);
        }
    }
    none()
}
