//! The gate of the flow syntax of version 0.3 (W3-09, K-02): the clocks
//! `at` (S-102), the references `^name` (S-44), the built-in delays written
//! `prev~(…)`, `delay~(…)` and `vdelay~(…)` (S-44, S-29) and `if~` / `match~`
//! (S-110). The syntax stage reads them; the checks of this version read
//! the forms of the draft (`Sig[F32]`, `prev(y, 0.0)`) and do not know them.
//! An item that holds one is E0200 here, once, and is not checked further
//! (its def is failed as a cut heading: its body is not checked and its users
//! see an error), so no new form reaches the checks, read wrongly or in an
//! internal error (plan §8.2).
//!
//! W3-10 replaces this module with the one function that writes the new
//! forms in the checks' terms, and keeps E0200 for what it cannot write.

use onsa_diag::Span;
use onsa_diag::unsupported::FlowForm;
use onsa_syntax::ast::ItemId;
use onsa_syntax::cst::{NodeKind, TokenIdx};
use onsa_syntax::{Parsed, TokenKind};

/// The first form of the flow syntax in `item` of the file `text` (not in
/// the items of its members, which are defs of their own), and its span.
pub(crate) fn first_form(parsed: &Parsed, text: &str, item: ItemId) -> Option<(Span, FlowForm)> {
    let cst = &parsed.cst;
    let node = *parsed.map.items.get(item.index())?;
    for i in cst.token_range(node) {
        let t = cst.tokens()[i];
        if !matches!(t.kind, TokenKind::KwAt | TokenKind::Caret | TokenKind::Tilde) {
            continue;
        }
        let parent = cst.token_parent(TokenIdx(i as u32));
        // A token of a member item is that item's.
        if cst.ancestors(parent).take_while(|&a| a != node).any(|a| cst.kind(a) == NodeKind::Item) {
            continue;
        }
        let form = match (t.kind, cst.kind(parent)) {
            // `at` after a `.` is a member name (`xs.at(0)`, S-357), a later stage's.
            (TokenKind::KwAt, NodeKind::Clock) => FlowForm::Clock,
            (TokenKind::Caret, NodeKind::FeedbackExpr) => FlowForm::Feedback,
            (TokenKind::Tilde, NodeKind::IfExpr) => FlowForm::IfTilde,
            (TokenKind::Tilde, NodeKind::MatchExpr) => FlowForm::MatchTilde,
            // A built-in delay: its callee is the name alone (`a.prev~(x)`
            // calls a flow of the module `a`).
            (TokenKind::Tilde, NodeKind::CallExpr) => {
                let Some(callee) = cst.child_nodes(parent).next() else { continue };
                let s = cst.span(callee);
                let name = &text[s.start as usize..s.end as usize];
                match crate::flow::DELAYS.iter().find(|&&d| d == name) {
                    Some(&d) if cst.kind(callee) == NodeKind::PathExpr => FlowForm::Delay(d),
                    _ => continue,
                }
            }
            _ => continue,
        };
        return Some((t.span, form));
    }
    None
}
