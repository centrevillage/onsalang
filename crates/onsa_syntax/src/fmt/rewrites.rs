//! The rewrites of `onsa fmt` that change the tree (`docs/onsa-tools.md`
//! §3.3): the one closed list, in [`REWRITES`].
//!
//! A rewrite says which code tokens of the CST it drops; the plan
//! (`fmt/plan.rs`) reads them. W3-11 has the one rewrite the formatter did
//! before it printed the CST: the `return` at the end of the body of a
//! function. W3-12 adds the others of §3.3 (`-> ()`, an empty `uses {}`,
//! redundant parentheses, `init`, `move` in the place of the returned value)
//! and, beside each, the same rewrite of the tree that the check before
//! writing compares (§3.5).

use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// A rewrite: it adds to the list the code tokens it drops from a node (it
/// is called on every node of the tree).
pub(super) type Rewrite = fn(&Cst, NodeId, &mut Vec<TokenIdx>);

/// The closed list of §3.3.
pub(super) const REWRITES: &[Rewrite] = &[tail_return];

/// The `return` of a `return e` that is the last statement of the body of a
/// function (spec §6.1): `e` becomes the value of the body. The `return`
/// in a branch of an `if` or a `match` at the end, in the body of a closure
/// and without a value is not dropped yet (the formatter did not drop them
/// before W3-11).
fn tail_return(cst: &Cst, n: NodeId, out: &mut Vec<TokenIdx>) {
    if cst.kind(n) != NodeKind::Fn {
        return;
    }
    let Some(body) = cst.child_nodes(n).find(|&c| cst.kind(c) == NodeKind::Block) else { return };
    let Some(last) = cst.child_nodes(body).last() else { return };
    if cst.kind(last) != NodeKind::ReturnStmt || cst.child_nodes(last).next().is_none() {
        return;
    }
    let keyword = cst.children(last).iter().find_map(|e| match *e {
        Elem::Token(t) if cst.token(t).kind == TokenKind::KwReturn => Some(t),
        _ => None,
    });
    out.extend(keyword);
}
