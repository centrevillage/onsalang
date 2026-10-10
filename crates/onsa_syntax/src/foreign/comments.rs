//! The rows of the block comments (§2.1, S-247, R-174).

use super::*;

/// Whether the block comment `text` is closed, and whether it holds another.
fn block_shape(text: &str) -> (bool, bool) {
    let b = text.as_bytes();
    let (mut depth, mut nested, mut i) = (1, false, 2);
    while i < b.len() {
        if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return (i == b.len(), nested);
            }
        } else if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
            depth += 1;
            nested = true;
            i += 2;
        } else {
            i += 1;
        }
    }
    (false, nested)
}

/// A token that may start a declaration a `///` documents: an item but `use`
/// and `test`, or its attribute or visibility (§2.1).
fn documented(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        KwFn | KwRt
            | KwFlow
            | KwStruct
            | KwEnum
            | KwType
            | KwTrait
            | KwImpl
            | KwEffect
            | KwBlocking
            | KwHandler
            | KwConst
            | KwExtern
            | KwTarget
    )
}

/// What a `///` in place of the block comment at `c.at` would document
/// (§2.1): a declaration that takes one (past `pub` and attributes; not
/// `use` or `test`, whose `///` is E0004), a field, a variant, a flow input.
fn documents(c: &Cursor) -> bool {
    let mut i = c.sig_after(c.at);
    // Past `pub` (`pub(pkg)`) and the attributes (`@name(..)`).
    while matches!(c.kind(i), TokenKind::KwPub | TokenKind::At) {
        if c.kind(i) == TokenKind::At {
            i = c.sig_after(i);
        }
        i = c.sig_after(i);
        if c.kind(i) == TokenKind::LParen {
            let mut depth = 0;
            loop {
                match c.kind(i) {
                    TokenKind::LParen => depth += 1,
                    TokenKind::RParen => depth -= 1,
                    TokenKind::Eof => return false,
                    _ => {}
                }
                i = c.sig_after(i);
                if depth == 0 {
                    break;
                }
            }
        }
    }
    let ctx = c.context();
    let member = |k: usize, kind: NodeKind| c.open.get(k).is_some_and(|o| o.0 == kind);
    match ctx {
        Some((_, NodeKind::FieldList | NodeKind::VariantList)) => c.kind(i) == TokenKind::Ident,
        Some((k, NodeKind::ParamList)) => k > 0 && member(k - 1, NodeKind::Flow) && c.kind(i) == TokenKind::Ident,
        _ => documented(c.kind(i)),
    }
}

/// A block comment (§2.1, S-247, S-302, R-174). A closed one is E0020: the
/// candidate keeps its words in line comments and changes neither the
/// tokens outside it nor the line breaks between them. When nothing but
/// blanks follows it on its last line, the line comments take its place;
/// else (it is at the start or in the middle of a line) they go on lines of
/// their own above the line it starts on, at the indentation of that line,
/// and the comment is removed from the code (with a blank, so the tokens
/// around it stay apart). Several on one line are fixed one by one (one per
/// unit), each adding its lines above. `/** */` that starts its line, before
/// a declaration it may document, is `///` (else `//`, so that a `///` moved
/// above documents no other declaration), and `/*! */` at the head of the
/// file is `//!` (or `///`, a second candidate). One over lines with code
/// after its `*/` on that line has no candidate (the line break between the
/// code around it is only inside it, so no candidate keeps the line breaks
/// without another reading: E0002). One never closed and one that holds
/// another are E0002.
pub(super) fn block_comment(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::BlockComment {
        return None;
    }
    let span = c.span(c.at);
    let text = c.src(c.at);
    let (closed, nested) = block_shape(text);
    if !closed {
        c.say(RowId::BlockCommentUnclosed);
        return hit(span, Vec::new());
    }
    if nested {
        c.say(RowId::BlockCommentNested);
        return hit(span, Vec::new());
    }
    let inner = &text[2..text.len() - 2];
    let (doc, inner) = match inner.as_bytes().first() {
        Some(b'*') if !inner.is_empty() => (Some('*'), &inner[1..]),
        Some(b'!') => (Some('!'), &inner[1..]),
        _ => (None, inner),
    };
    let mut lines: Vec<&str> = inner
        .split('\n')
        .enumerate()
        .map(|(k, l)| if k == 0 { l.trim() } else { l.trim_start_matches([' ', '\t']).trim_end() })
        .map(|l| l.trim_end_matches('\r'))
        .collect();
    if lines.len() > 1 && lines[0].is_empty() {
        lines.remove(0);
    }
    if lines.len() > 1 && lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let line_start = c.line_start(span.start);
    let pre = c.text[line_start as usize..span.start as usize].trim().is_empty();
    let rest_start = span.end as usize;
    let rest_end = c.text[rest_start..].find('\n').map_or(c.text.len(), |n| rest_start + n);
    let post = !c.text[rest_start..rest_end].trim().is_empty();
    if post && text.contains('\n') {
        c.say(RowId::BlockCommentMultilineCodeAfter);
        return hit(span, Vec::new());
    }
    // What may come after the comment: a declaration a `///` documents.
    let documents = pre && documents(c);
    let head = pre && c.sig_before(c.at).is_none();
    let mut prefixes: Vec<(&str, &str)> = Vec::new();
    match doc {
        Some('!') if head => {
            prefixes.push(("//!", "write a module doc comment `//!`"));
            if documents {
                prefixes.push(("///", "write a doc comment `///`"));
            }
        }
        Some(_) if documents => prefixes.push(("///", "write a doc comment `///`")),
        _ => prefixes.push(("//", "write a line comment")),
    }
    let indent = c.indent(span.start).to_string();
    let fixes = prefixes
        .into_iter()
        .map(|(prefix, title)| {
            let rendered: Vec<String> =
                lines.iter().map(|l| if l.is_empty() { prefix.to_string() } else { format!("{prefix} {l}") }).collect();
            if !post {
                // In place: the comment ends its line.
                return Fix::replace(title, span, rendered.join(&format!("\n{indent}")));
            }
            let above: String = rendered.iter().map(|l| format!("{l}\n{indent}")).collect();
            let ws_before = c.space_before(c.at);
            let ws_after = c.space_after(c.at);
            if pre {
                // The comment starts its line: the words take its place, and
                // the code after it goes to the next line.
                let end = ws_after.map_or(span.end, |s| s.end);
                return Fix::replace(title, c.file_span(span.start, end), above);
            }
            let removal = match (ws_before, ws_after) {
                (Some(_), Some(after)) => Edit::delete(c.file_span(span.start, after.end)),
                (None, None) => Edit::replace(span, " "),
                _ => Edit::delete(span),
            };
            let above: String = rendered.iter().map(|l| format!("{indent}{l}\n")).collect();
            Fix::new(title, vec![Edit::insert(c.file, line_start, above), removal])
        })
        .collect();
    hit(span, fixes)
}
