//! The rows of the declarations, statements and attributes of other languages
//! (`let mut`, `loop`, `proc`, `#[…]` and `#[derive]`, `pub(crate)`).

use super::*;

/// `let mut x` of Rust: `var x` (§5.1).
pub(super) fn let_mut(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Ident || c.top() != Some(NodeKind::LetStmt) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.mut_word(m))?;
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

/// The name of the attribute of Rust and of the old version that derives
/// traits (`#[derive(…)]`, `@derive(…)`), whose form is the head of a struct
/// or an enum ([`derive`]).
const DERIVE: &str = "derive";

/// `#[name(...)]` of Rust: `@name(...)` (§6.5), when the attribute of Onsa
/// that it spells goes in its place (the table of the attributes,
/// [`crate::attrs::accepts`]; `#[repr(C)]` is `@repr(c)`, the same value
/// spelled otherwise, S-463); `#[derive(…)]` is the head of a struct or an
/// enum ([`derive`]). Any other is the row with no candidate (`#[inline]`,
/// `#[repr(rust)]`, a derive on a fn, S-483), and one whose candidate cannot
/// be made as it is written is the row of its own (a derive whose names or
/// head do not read, one not closed on its line). In the head of a
/// declaration, one that closes on its line is read on after (§18.1, S-435)
/// and the parser asks about it when it has read the head, at the place of
/// the declaration (`c.place`, `c.declaration`; [`super::at_heading_hash`]).
/// At an input of a flow (the node opened at the `#`), the parser fails at
/// it.
pub(super) fn hash_attribute(c: &Cursor) -> Option<(RowId, Hit)> {
    use crate::attrs::Place;
    if c.kind(c.at) != TokenKind::Hash || c.kind(c.at + 1) != TokenKind::LBracket {
        return None;
    }
    let close = crate::scan::closing_on_line(c.tokens, c.at + 1);
    let end = close.map_or(c.span(c.at + 1).end, |e| c.span(e).end);
    let span = c.file_span(c.span(c.at).start, end);
    let found = |row, fixes, note| Some((row, Hit { span, fixes, misplaced: false, resume: None, note }));
    let no_form = || found(RowId::HashAttributeNoCandidate, Vec::new(), None);
    let unfixable = || found(RowId::HashAttributeUnfixable, Vec::new(), None);
    let unread = c.open_at(0).is_some_and(|o| o.1 == c.span(c.at).start);
    let opened_in =
        |outer: &[NodeKind]| unread && outer.iter().enumerate().all(|(n, &k)| c.open_at(n).is_some_and(|o| o.0 == k));
    let place = c
        .place
        .or_else(|| opened_in(&[NodeKind::Param, NodeKind::ParamList, NodeKind::Flow]).then_some(Place::FlowInput));
    let Some(e) = close else {
        // Not closed on its line: in the head of a declaration, the head
        // is not read on (§18.1, S-435), so its place is not known.
        let attribute_place = place.is_some() || opened_in(&[NodeKind::Attr, NodeKind::Item]);
        return if attribute_place { unfixable() } else { no_form() };
    };
    let Some(place) = place else { return no_form() };
    if c.kind(c.at + 2) != TokenKind::Ident {
        return no_form();
    }
    let name = c.src(c.at + 2);
    if name == DERIVE {
        let Some(decl) = c.declaration.filter(|&d| derives(c, d)) else { return no_form() };
        return match derive(c, decl, c.at + 3, e - 1, e) {
            Some((fix, note)) => found(RowId::HashAttribute, vec![fix], note),
            None => unfixable(),
        };
    }
    // The sole value, as the table reads it of an attribute of Onsa
    // ([`crate::attrs::sole_value`]), in the parentheses right before the `]`.
    let args = c.kind(c.at + 3) == TokenKind::LParen;
    let value = args
        .then(|| closing(c, c.at + 3))
        .flatten()
        .filter(|&shut| c.sig_after(shut) == e)
        .and_then(|shut| crate::attrs::sole_value(c.tokens, c.at + 3, shut));
    let mut edits =
        vec![Edit::replace(c.file_span(c.span(c.at).start, c.span(c.at + 1).end), "@"), Edit::delete(c.span(e))];
    if args && value.is_none() && crate::attrs::attribute(name).is_some_and(|a| a.values.is_some()) {
        return no_form();
    }
    if !crate::attrs::accepts(name, value.map(|v| c.src(v)), place) {
        // A value spelled otherwise (`C` for `c`): the same value, written as Onsa does.
        let lower = value.map(|v| c.src(v).to_lowercase());
        match (value, lower) {
            (Some(v), Some(l)) if crate::attrs::accepts(name, Some(&l), place) => {
                edits.push(Edit::replace(c.span(v), l));
            }
            _ => return no_form(),
        }
    }
    found(RowId::HashAttribute, vec![Fix::new("write the attribute with `@`", edits)], None)
}

/// Whether the declaration whose keyword is token `decl` derives traits at
/// its head, `: A + B` (a struct or an enum, §6.4).
fn derives(c: &Cursor, decl: usize) -> bool {
    matches!(c.kind(decl), TokenKind::KwStruct | TokenKind::KwEnum)
}

/// The edit that takes the attribute of tokens `first..=last` out: with the
/// blanks and the line break after it up to the next code, unless a comment
/// is between them (the comment would take the next line in, §18.1), and
/// then the attribute's tokens only.
fn remove_attribute(c: &Cursor, first: usize, last: usize) -> Edit {
    let next = c.sig_after(last);
    let end = if (last + 1..next).any(|i| c.comment(i)) { c.span(last).end } else { c.span(next).start };
    Edit::delete(c.file_span(c.span(first).start, end))
}

/// The derive of the attribute whose first token is `c.at` and last `last`
/// (`#[derive(A, B)]`, `@derive(A, B)`; `open` and `shut` its parentheses)
/// before the struct or the enum whose keyword is token `decl`: the traits
/// are written at the head of the declaration, `struct S: A + B` (§6.4,
/// S-463). The names are written as they are, but the kind constraints
/// `Copy` and `Dup` ([`KIND_CONSTRAINTS`], §4.6), which go; when none is
/// left, the attribute goes alone. A head with a `:` already takes the names
/// after its last trait, but the names it has. With the candidate, the note
/// on the kinds left out, if any (the rule of `copy_bound`, S-463). None when
/// the names or the head do not read.
fn derive(c: &Cursor, decl: usize, open: usize, shut: usize, last: usize) -> Option<(Fix, Option<&'static str>)> {
    if c.kind(open) != TokenKind::LParen || c.kind(shut) != TokenKind::RParen {
        return None;
    }
    // The traits: names separated with `,` in the parentheses.
    let mut traits = Vec::new();
    let mut i = open;
    loop {
        i += 1;
        if c.kind(i) != TokenKind::Ident {
            return None;
        }
        traits.push(c.src(i));
        i += 1;
        match c.kind(i) {
            TokenKind::Comma => {}
            TokenKind::RParen if i == shut => break,
            _ => return None,
        }
    }
    if c.kind(decl + 1) != TokenKind::Ident {
        return None;
    }
    // After the name, or after its type parameters (`struct S[T]: A`, §6.4).
    let mut head = decl + 1;
    if c.kind(head + 1) == TokenKind::LBracket {
        head = closing(c, head + 1)?;
    }
    // The traits the head has, and the token after which more go: the list
    // after the `:` (names and paths joined by `+`, a line break after a
    // `+`, §6.4) ends at any other token (the `{` of the body, a line break).
    let mut written: Vec<&str> = Vec::new();
    let mut after = head;
    if c.kind(c.after(head)) == TokenKind::Colon {
        after = c.after(head);
        loop {
            let next = if c.kind(after) == TokenKind::Plus { c.sig_after(after) } else { c.after(after) };
            match c.kind(next) {
                TokenKind::Ident => written.push(c.src(next)),
                TokenKind::Plus | TokenKind::Dot => {}
                _ => break,
            }
            after = next;
        }
        if c.kind(after) != TokenKind::Ident {
            return None;
        }
    }
    let left_out = traits.iter().any(|t| KIND_CONSTRAINTS.contains(t));
    let mut add: Vec<&str> = Vec::new();
    for t in traits {
        if !KIND_CONSTRAINTS.contains(&t) && !written.contains(&t) && !add.contains(&t) {
            add.push(t);
        }
    }
    let mut edits = vec![remove_attribute(c, c.at, last)];
    if !add.is_empty() {
        let text =
            if written.is_empty() { format!(": {}", add.join(" + ")) } else { format!(" + {}", add.join(" + ")) };
        edits.push(Edit::insert(c.file, c.span(after).end, text));
    }
    let fix = Fix::new("write the traits at the head of the declaration", edits);
    Some((fix, left_out.then_some(row(RowId::CopyBound).rule)))
}

/// The old attributes (§6.5, S-34, S-43, S-57), asked where the parser read
/// one (`c.at` its `@`, `c.place` its place): `@derive(…)` before a struct
/// or an enum is the head of the declaration ([`derive`]), `@relaxed` on a fn
/// or a flow is `@fp(relaxed)`, `@bulk` on a `let` is `@mem(bulk)`, and
/// `@mem(fast)` on a `let` goes (redundant). In a place that does not take
/// the Onsa form, the row with no candidate.
pub(super) fn old_attribute(c: &Cursor) -> Option<(RowId, Hit)> {
    use crate::attrs::{FAST, FP, MEM, Place, RELAXED};
    if c.kind(c.at) != TokenKind::At || c.kind(c.at + 1) != TokenKind::Ident {
        return None;
    }
    let place = c.place?;
    let name = c.src(c.at + 1);
    let args = c.kind(c.at + 2) == TokenKind::LParen && c.gap(c.at + 2) == Gap::None;
    let last = if args { closing(c, c.at + 2)? } else { c.at + 1 };
    let span = c.file_span(c.span(c.at).start, c.span(last).end);
    let no_candidate = || found(RowId::OldAttributeNoCandidate, span, Vec::new());
    match name {
        DERIVE if args => {
            match c.declaration.filter(|&d| derives(c, d)).and_then(|d| derive(c, d, c.at + 2, last, last)) {
                Some((fix, note)) => {
                    Some((RowId::DeriveAttribute, Hit { span, fixes: vec![fix], misplaced: false, resume: None, note }))
                }
                None => no_candidate(),
            }
        }
        "relaxed" | "bulk" if !args => {
            let (row, outer, places): (_, _, &[Place]) = if name == RELAXED {
                (RowId::RelaxedAttribute, FP, &[Place::Fn, Place::Flow])
            } else {
                (RowId::BulkAttribute, MEM, &[Place::Let])
            };
            if !places.contains(&place) {
                return no_candidate();
            }
            // The name stays; the attribute is written around it (S-251).
            let s = c.span(c.at + 1);
            let edits = vec![Edit::insert(s.file, s.start, format!("{outer}(")), Edit::insert(s.file, s.end, ")")];
            let fix = Fix::new(format!("write `@{outer}({name})`"), edits);
            found(row, span, vec![fix])
        }
        _ if name == MEM && place == Place::Let && last == c.at + 4 && c.is_ident(c.at + 3, FAST) => {
            found(RowId::MemFast, span, vec![Fix::new("remove `@mem(fast)`", vec![remove_attribute(c, c.at, last)])])
        }
        _ => None,
    }
}

/// A visibility of another language, `pub(…)`, the `(` on the line of the
/// `pub` with blanks or none between (§15.1, S-36, S-412, S-417, S-420): the
/// parser fails at its `(` (`Parser::parse_vis`). The form is `pub` to the
/// `)` that closes it on its line (one not closed is the general E0002).
/// `pub(crate)` and `pub(pkg)` go (the default visibility of the place),
/// but on a field of a `pub struct`, where taking them out would let the
/// field out of the package; any other form has no candidate. The head is
/// read on after the `)` (§18.1, S-435, [`Hit::resume`]).
pub(super) fn visibility_form(c: &Cursor) -> Option<(RowId, Hit)> {
    if c.kind(c.at) != TokenKind::LParen || c.top() != Some(NodeKind::Vis) {
        return None;
    }
    let public = c.sig_before(c.at).filter(|&p| c.kind(p) == TokenKind::KwPub)?;
    let close = crate::scan::closing_on_line(c.tokens, c.at)?;
    let span = c.file_span(c.span(public).start, c.span(close).end);
    let inner: Vec<usize> = (c.at + 1..close).filter(|&i| !c.comment(i)).collect();
    let word = match inner.as_slice() {
        [w] if c.kind(*w) == TokenKind::Ident => Some(c.src(*w)),
        _ => None,
    };
    let field_of_pub_struct =
        c.open_at(1).is_some_and(|o| o.0 == NodeKind::Field) && struct_visibility(c) == Some(TokenKind::KwPub);
    let row = match word {
        Some("crate" | "pkg") if field_of_pub_struct => {
            return found_reading_on(RowId::FieldPubCrate, span, Vec::new(), close + 1);
        }
        Some("crate") => RowId::PubCrate,
        Some("pkg") => RowId::PubPkg,
        _ => return found_reading_on(RowId::PubRestricted, span, Vec::new(), close + 1),
    };
    let end = c.space_after(close).map_or(span.end, |s| s.end);
    found_reading_on(row, span, vec![Fix::delete("remove the visibility", c.file_span(span.start, end))], close + 1)
}

/// The visibility word of the struct whose field is read (`pub`, `priv`).
fn struct_visibility(c: &Cursor) -> Option<TokenKind> {
    let (_, start) = c.open.iter().rev().find(|o| o.0 == NodeKind::Struct)?;
    let k = c.kind(c.sig_before(c.index_at(*start))?);
    matches!(k, TokenKind::KwPub | TokenKind::KwPriv).then_some(k)
}

/// The word `i` and the blanks after it go.
fn remove_word(c: &Cursor, i: usize, title: &str) -> Fix {
    let end = c.space_after(i).map_or(c.span(i).end, |s| s.end);
    Fix::delete(title, c.file_span(c.span(i).start, end))
}

/// The visibility word of a field, read at `c.at` (§15.1): a field inherits
/// the visibility of its struct, so `pub` on it, and `priv` on a field of a
/// `priv struct`, are redundant and go.
pub(super) fn field_visibility(c: &Cursor) -> Option<(RowId, Hit)> {
    if c.top() != Some(NodeKind::Field) {
        return None;
    }
    let row = match c.kind(c.at) {
        TokenKind::KwPub => RowId::FieldPub,
        TokenKind::KwPriv if struct_visibility(c) == Some(TokenKind::KwPriv) => RowId::FieldPrivInPrivStruct,
        _ => return None,
    };
    found(row, c.span(c.at), vec![remove_word(c, c.at, "remove the visibility")])
}

/// `priv use`, read at its `priv` (§15.1): the names a `use` brings in are
/// within its module, so `priv` is redundant and goes.
pub(super) fn priv_use(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::KwPriv || c.kind(c.sig_after(c.at)) != TokenKind::KwUse {
        return None;
    }
    hit(c.span(c.at), vec![remove_word(c, c.at, "remove `priv`")])
}

/// `const fn h` of Rust (§6.6, S-464): the parser fails at the keyword of
/// the function after `const` (`Parser::keyword_before_keyword`); a function
/// that a constant calls has no mark, and `const` goes.
pub(super) fn const_fn(c: &Cursor) -> Option<Hit> {
    if !matches!(c.kind(c.at), TokenKind::KwFn | TokenKind::KwRt) || c.top() != Some(NodeKind::Const) {
        return None;
    }
    let k = c.before(c.at).filter(|&k| c.kind(k) == TokenKind::KwConst)?;
    hit(c.span(k), vec![remove_word(c, k, "remove `const`")])
}

/// `extern "C" fn h` and `extern fn h` of Rust and C (§14.1, §14.2, S-464):
/// the parser fails at the keyword of the function after `extern` and its
/// string. What C calls is chosen by the manifest, which the writer does not
/// edit, so there is no candidate.
pub(super) fn extern_fn(c: &Cursor) -> Option<Hit> {
    if !matches!(c.kind(c.at), TokenKind::KwFn | TokenKind::KwRt) || c.top() != Some(NodeKind::Extern) {
        return None;
    }
    let last = c.before(c.at)?;
    let first = if c.kind(last) == TokenKind::Str { c.before(last)? } else { last };
    if c.kind(first) != TokenKind::KwExtern {
        return None;
    }
    hit(c.file_span(c.span(first).start, c.span(last).end), Vec::new())
}

/// `export "C" fn h` of the old version (§14.2, S-464): the parser fails at
/// `export`, a word before the head (`Parser::words_before_head`); there is
/// no candidate, as for [`extern_fn`].
pub(super) fn export_c(c: &Cursor) -> Option<Hit> {
    if !c.is_ident(c.at, "export") || c.top() != Some(NodeKind::Item) {
        return None;
    }
    let s = Some(c.after(c.at)).filter(|&s| c.kind(s) == TokenKind::Str)?;
    if !matches!(c.kind(c.after(s)), TokenKind::KwFn | TokenKind::KwRt) {
        return None;
    }
    hit(c.file_span(c.span(c.at).start, c.span(s).end), Vec::new())
}

/// A tuple struct, `struct Hz(F32)` (S-39, R-51): the parser fails at its
/// `(` (the `FieldList` opened there). One element is a struct with the
/// field `value` (§4.4): the brackets are the field's, when the element
/// reads as a type (else the candidate would leave an error, S-236); with
/// more, the names of the fields are the writer's, and there is no candidate.
/// The field is `priv`, as an element of a tuple struct is of its module
/// (§4.1 `pub struct Q { priv value: F32 }`; S-494), but in a `priv struct`,
/// where `priv` is redundant (§15.1).
pub(super) fn tuple_struct(c: &Cursor) -> Option<(RowId, Hit)> {
    if c.kind(c.at) != TokenKind::LParen
        || c.top() != Some(NodeKind::FieldList)
        || c.open_at(0).is_none_or(|o| o.1 != c.span(c.at).start)
    {
        return None;
    }
    let close = crate::scan::closing_on_line(c.tokens, c.at)?;
    let (_, start) = c.open_at(1).filter(|o| o.0 == NodeKind::Struct)?;
    let span = c.file_span(c.span(c.at).start, c.span(close).end);
    let mut depth = 0u32;
    let mut commas = 0;
    for i in c.at + 1..close {
        match c.kind(i) {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
            TokenKind::Comma if depth == 0 => commas += 1,
            _ => {}
        }
    }
    let empty = (c.at + 1..close).all(|i| c.comment(i));
    let trailing = c.sig_before(close).is_some_and(|p| c.kind(p) == TokenKind::Comma);
    if empty || commas > usize::from(trailing) {
        return found(RowId::TupleStructMany, span, Vec::new());
    }
    let last = c.sig_before(close).map(|p| if trailing { c.sig_before(p).unwrap_or(p) } else { p })?;
    let run = (c.full[c.sig_after(c.at)] as usize, c.full[last] as usize);
    if !crate::parser::reads_as_type(c.file, c.text, c.all, c.literals, run) {
        return found(RowId::TupleStructMany, span, Vec::new());
    }
    let indent = c.indent(start).to_string();
    let eol = c.line_break(start);
    let field = if struct_visibility(c) == Some(TokenKind::KwPriv) { "value" } else { "priv value" };
    // The `{` one blank after the head, the field on its own line; the
    // `,` after it once, whether the element has one or not (comments
    // after the element stay, the `)` alone is replaced).
    let open = c.file_span(
        c.space_before(c.at).map_or(c.span(c.at).start, |s| s.start),
        c.space_after(c.at).map_or(c.span(c.at).end, |s| s.end),
    );
    let comments = (last + 1..close).any(|i| c.comment(i));
    let mut edits = vec![Edit::replace(open, format!(" {{{eol}{indent}  {field}: "))];
    match (comments, trailing, c.sig_before(close)) {
        (true, _, _) => {
            edits.push(Edit::replace(c.span(close), format!("{}{eol}{indent}}}", if trailing { "" } else { "," })))
        }
        // A `,` written stays (S-251): the blanks before it go, the edit of the `)` starts after it.
        (false, true, Some(p)) => {
            let gap = c.file_span(c.span(last).end, c.span(p).start);
            if !gap.is_empty() {
                edits.push(Edit::delete(gap));
            }
            edits.push(Edit::replace(c.file_span(c.span(p).end, c.span(close).end), format!("{eol}{indent}}}")));
        }
        (false, _, _) => {
            edits.push(Edit::replace(c.file_span(c.span(last).end, c.span(close).end), format!(",{eol}{indent}}}")))
        }
    }
    found(RowId::TupleStruct, span, vec![Fix::new("write a struct with the field `value`", edits)])
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
