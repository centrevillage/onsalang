//! The rows of `;` (§2.5, S-248).

use super::*;

/// The nodes that hold statements or declarations, one per line.
fn holds_lines(kind: Option<NodeKind>) -> bool {
    matches!(kind, Some(NodeKind::Block | NodeKind::SourceFile | NodeKind::ItemList))
}

/// The run of `;` at `c.at` on one line (S-248: `;;` is one form).
fn semicolon_run(c: &Cursor) -> Option<usize> {
    if c.kind(c.at) != TokenKind::Semi {
        return None;
    }
    let mut last = c.at;
    while c.kind(last + 1) == TokenKind::Semi {
        last += 1;
    }
    Some(last)
}

/// The edits that remove the run `first..=last` of `;` (each token: the
/// spaces between stay).
fn remove_run(c: &Cursor, first: usize, last: usize) -> Vec<Edit> {
    (first..=last).map(|i| Edit::delete(c.span(i))).collect()
}

/// `;` at the end of a statement or a declaration (§2.5). The candidate
/// removes it; with code after it on its line (`let a = 1; let b = 2`), it
/// puts that code on a line of its own, at the indentation of the line.
pub(super) fn semicolon(c: &Cursor) -> Option<Hit> {
    let last = semicolon_run(c)?;
    let context = c.context().map(|o| o.1);
    // `return;`: the statement `return` ends at the `;`.
    let after_return =
        context == Some(NodeKind::ReturnStmt) && c.sig_before(c.at).is_some_and(|p| c.kind(p) == TokenKind::KwReturn);
    if !holds_lines(context) && !after_return {
        return None;
    }
    // What comes before can end a statement (not `let x = ;`).
    if let Some(p) = c.sig_before(c.at)
        && (c.kind(p).binop().is_some()
            || matches!(
                c.kind(p),
                TokenKind::Eq
                    | TokenKind::Comma
                    | TokenKind::Colon
                    | TokenKind::Dot
                    | TokenKind::Arrow
                    | TokenKind::FatArrow
                    | TokenKind::LParen
                    | TokenKind::LBracket
                    | TokenKind::Bang
                    | TokenKind::Tilde
                    | TokenKind::At
                    | TokenKind::KwLet
                    | TokenKind::KwVar
                    | TokenKind::KwAs
                    | TokenKind::KwAt
            ))
    {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(last).end);
    let next = c.after(last);
    let fix = if matches!(c.kind(next), TokenKind::Newline | TokenKind::Eof | TokenKind::RBrace)
        || matches!(c.kind(last + 1), TokenKind::Comment | TokenKind::DocComment)
    {
        Fix::new(if last > c.at { "remove the `;`s" } else { "remove the `;`" }, remove_run(c, c.at, last))
    } else {
        // The next statement goes to a line of its own.
        let indent = c.indent(c.span(c.at).start).to_string();
        let gap = c.file_span(c.span(c.at).start, c.span(next).start);
        Fix::replace("end the line at the `;`", gap, format!("\n{indent}"))
    };
    hit(span, vec![fix])
}

/// `;` between the elements of a list (a struct's fields, the arguments):
/// the separator is `,` (S-250). Before the closing bracket, it is removed.
pub(super) fn semicolon_in_list(c: &Cursor) -> Option<Hit> {
    let last = semicolon_run(c)?;
    if !c.context().is_some_and(|o| crate::starts::comma_list(o.1)) {
        return None;
    }
    // After an element (not `(;` or `,;`).
    if c.sig_before(c.at).is_none_or(|p| {
        matches!(c.kind(p), TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace | TokenKind::Comma)
    }) {
        return None;
    }
    let span = c.file_span(c.span(c.at).start, c.span(last).end);
    let next = c.sig_after(last);
    let fix = if matches!(c.kind(next), TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
        Fix::new("remove the `;`", remove_run(c, c.at, last))
    } else {
        let mut edits = vec![Edit::replace(c.span(c.at), ",")];
        edits.extend(remove_run(c, c.at + 1, last).into_iter().filter(|_| last > c.at));
        Fix::new("separate with `,`", edits)
    };
    hit(span, vec![fix])
}
