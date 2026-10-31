//! The storage attribute `@mem` of a `let` (§12.4, S-43) is read by the
//! syntax stage, and its meaning (the bulk storage, E0818 to E0820) is W9-06:
//! until then, the item that holds one is E0200, once, and is not checked
//! further ([`first_mem`]; its def is failed as a cut heading), in a flow
//! too, so that no program the spec refuses is let through (plan §8.2).

use onsa_diag::Span;
use onsa_syntax::ast::ItemId;
use onsa_syntax::cst::{NodeKind, TokenIdx};
use onsa_syntax::{Parsed, TokenKind};

/// The first attribute of a `let` in `item` (not in the items of its
/// members), which the table accepted (`@mem`, §12.4): its span.
pub(crate) fn first_mem(parsed: &Parsed, item: ItemId) -> Option<Span> {
    let cst = &parsed.cst;
    let node = *parsed.map.items.get(item.index())?;
    for i in cst.token_range(node) {
        let t = cst.tokens()[i];
        if t.kind != TokenKind::At {
            continue;
        }
        let attr = cst.token_parent(TokenIdx(i as u32));
        if cst.kind(attr) != NodeKind::Attr || !cst.is_complete(attr) {
            continue;
        }
        if cst.parent(attr).is_none_or(|p| cst.kind(p) != NodeKind::LetStmt) {
            continue;
        }
        if cst.ancestors(attr).take_while(|&a| a != node).any(|a| cst.kind(a) == NodeKind::Item) {
            continue;
        }
        return Some(cst.span(attr));
    }
    None
}
