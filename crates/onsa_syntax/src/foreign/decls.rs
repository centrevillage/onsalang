//! The rows of the declarations, statements and attributes of other languages
//! (`let mut`, `loop`, `proc`, `#[…]` and `#[derive]`, `pub(crate)`).

use super::*;

/// `let mut x` of Rust: `var x` (§5.1).
pub(super) fn let_mut(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Ident || c.top() != Some(NodeKind::LetStmt) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.is_ident(m, "mut"))?;
    let l = c.before(m).filter(|&l| c.kind(l) == TokenKind::KwLet)?;
    let span = c.file_span(c.span(l).start, c.span(m).end);
    let fix = Fix::new(
        "write `var`",
        vec![Edit::replace(c.span(l), "var"), Edit::delete(c.file_span(c.span(m).start, c.span(c.at).start))],
    );
    hit(span, vec![fix])
}

/// `loop { }` of Rust: `while true { }` (§7). `loop` alone is a statement,
/// and the parser fails at its `{`.
pub(super) fn endless_loop(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::LBrace
        || c.top() != Some(NodeKind::Block)
        || !matches!(c.closed, [(NodeKind::PathExpr, _), (NodeKind::ExprStmt, _)])
    {
        return None;
    }
    let l = c.before(c.at).filter(|&l| c.is_ident(l, "loop"))?;
    hit(c.span(l), vec![Fix::replace("write `while true`", c.span(l), "while true")])
}

/// `proc name` (the older keyword) among the items of a module: `flow name`
/// (§11). In a list of members a flow is not a member (the general E0002).
pub(super) fn proc(c: &Cursor) -> Option<Hit> {
    if !c.is_ident(c.at, "proc")
        || c.top() != Some(NodeKind::Item)
        || c.open_at(1).is_none_or(|o| o.0 != NodeKind::SourceFile)
        || c.kind(c.at + 1) != TokenKind::Ident
    {
        return None;
    }
    hit(c.span(c.at), vec![Fix::replace("write `flow`", c.span(c.at), "flow")])
}

/// `#[name(...)]` of Rust: `@name(...)` (§6.5).
pub(super) fn hash_attribute(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Hash || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    let mut depth = 0;
    let mut close = None;
    for i in c.at + 1..c.tokens.len() {
        match c.kind(i) {
            TokenKind::LBracket | TokenKind::LParen => depth += 1,
            TokenKind::RBracket | TokenKind::RParen => {
                depth -= 1;
                if depth == 0 {
                    close = (c.kind(i) == TokenKind::RBracket).then_some(i);
                    break;
                }
            }
            TokenKind::Newline | TokenKind::Eof | TokenKind::LBrace | TokenKind::RBrace => break,
            _ => {}
        }
    }
    let end = close.map_or(c.span(c.at + 1).end, |e| c.span(e).end);
    let span = c.file_span(c.span(c.at).start, end);
    // Where an attribute goes (§6.5): the head of an item (opened at the
    // `#`), an input of a flow. A `let` takes `@mem` too, but the parser
    // reads no attribute there yet (W3-10): no candidate before it, which
    // would leave an E0002.
    let unread = c.open_at(0).is_some_and(|o| o.1 == c.span(c.at).start);
    let item = c.top() == Some(NodeKind::Item) && unread;
    let flow_input = c.top() == Some(NodeKind::Param)
        && unread
        && c.open_at(1).is_some_and(|o| o.0 == NodeKind::ParamList)
        && c.open_at(2).is_some_and(|o| o.0 == NodeKind::Flow);
    if !(item || flow_input) {
        return hit(span, Vec::new());
    }
    let fixes = match close {
        Some(e) if c.is_ident(c.at + 2, "derive") => derive(c, e).into_iter().collect(),
        Some(e) if c.kind(c.at + 2) == TokenKind::Ident => vec![Fix::new(
            "write the attribute with `@`",
            vec![Edit::replace(c.file_span(c.span(c.at).start, c.span(c.at + 1).end), "@"), Edit::delete(c.span(e))],
        )],
        _ => Vec::new(),
    };
    hit(span, fixes)
}

/// `#[derive(A, B)]` before a `struct` or an `enum` (its `]` is token
/// `close`): the traits are written at the head of the declaration, `struct
/// S: A + B` (§8.1, S-250). The attribute and the line break after it go.
fn derive(c: &Cursor, close: usize) -> Option<Fix> {
    // The traits: names separated with `,` in the parentheses.
    let mut traits = Vec::new();
    let mut i = c.at + 3;
    if c.kind(i) != TokenKind::LParen {
        return None;
    }
    loop {
        i += 1;
        if c.kind(i) != TokenKind::Ident {
            return None;
        }
        traits.push(c.src(i).to_string());
        i += 1;
        match c.kind(i) {
            TokenKind::Comma => {}
            TokenKind::RParen if i + 1 == close => break,
            _ => return None,
        }
    }
    let mut decl = c.sig_after(close);
    if c.kind(decl) == TokenKind::KwPub {
        decl = c.sig_after(decl);
    }
    if !matches!(c.kind(decl), TokenKind::KwStruct | TokenKind::KwEnum) || c.kind(decl + 1) != TokenKind::Ident {
        return None;
    }
    // After the name, or after its type parameters (`struct S[T]: A`, §6.4).
    let mut head = decl + 1;
    if c.kind(head + 1) == TokenKind::LBracket {
        let mut depth = 0;
        for i in head + 1..c.tokens.len() {
            match c.kind(i) {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        head = i;
                        break;
                    }
                }
                TokenKind::LBrace | TokenKind::Eof => return None,
                _ => {}
            }
        }
        if c.kind(head) != TokenKind::RBracket {
            return None;
        }
    }
    if c.kind(head + 1) == TokenKind::Colon {
        return None;
    }
    let first = c.sig_after(close);
    Some(Fix::new(
        "write the traits at the head of the declaration",
        vec![
            Edit::delete(c.file_span(c.span(c.at).start, c.span(first).start)),
            Edit::insert(c.file, c.span(head).end, format!(": {}", traits.join(" + "))),
        ],
    ))
}

/// `pub(crate)` of Rust: visibility within the package is the default
/// (§15.1). The candidate removes it with the blanks after it.
pub(super) fn pub_crate(c: &Cursor) -> Option<Hit> {
    if !c.is_ident(c.at, "crate") || c.top() != Some(NodeKind::Vis) {
        return None;
    }
    let open = c.before(c.at).filter(|&o| c.kind(o) == TokenKind::LParen)?;
    let public = c.before(open).filter(|&p| c.kind(p) == TokenKind::KwPub)?;
    let close = c.at + 1;
    if c.kind(close) != TokenKind::RParen {
        return hit(c.file_span(c.span(public).start, c.span(c.at).end), Vec::new());
    }
    let span = c.file_span(c.span(public).start, c.span(close).end);
    let end = c.space_after(close).map_or(span.end, |s| s.end);
    hit(span, vec![Fix::delete("remove the visibility", c.file_span(span.start, end))])
}

/// `return`, `break` or `continue` as the whole body of an arm of `match`
/// (`None => return 0,`; S-89): they are statements, so the one candidate puts
/// the block around the statement, up to the `,` or the `}` that ends the arm.
pub(super) fn arm_return(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr
        || !matches!(c.kind(c.at), TokenKind::KwReturn | TokenKind::KwBreak | TokenKind::KwContinue)
        || c.top() != Some(NodeKind::MatchArm)
        || c.sig_before(c.at).is_none_or(|p| c.kind(p) != TokenKind::FatArrow)
    {
        return None;
    }
    // The last token of the statement: before the `,` or the `}` of the arms.
    let mut depth = 0u32;
    let mut last = c.at;
    let mut i = c.at;
    loop {
        i = c.sig_after(i);
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth > 0 => depth -= 1,
            TokenKind::Comma | TokenKind::RBrace if depth == 0 => break,
            TokenKind::Eof | TokenKind::RParen | TokenKind::RBracket => return hit(c.span(c.at), Vec::new()),
            _ => {}
        }
        last = i;
    }
    let edits = vec![Edit::insert(c.file, c.span(c.at).start, "{ "), Edit::insert(c.file, c.span(last).end, " }")];
    hit(c.span(c.at), vec![Fix::new("put the statement in a block", edits)])
}
