//! The type arguments of an expression written `name[A, B]` with no `::`
//! (§4.5, S-329): the parser reads the list whole, as the list of
//! `name::[A, B]` (a `TypeArgsExpr` with no `::`), and the row
//! `type_args_square_comma` is found on the tree after parsing.

use onsa_diag::{Diagnostic, Edit, Fix, Span};

use super::{Hit, RowId, TYPE_ARGS_WITH_COLONS, diagnostic};
use crate::cst::{Cst, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// The E0020 of each `TypeArgsExpr` with no `::`, from its `[` to its `]`,
/// read whole or not (the `[` is before any error in it, §18.1). The
/// candidate writes `::` before the `[`. A list in another reported one is
/// not reported: one diagnostic per unit, the outer first (§18.1).
pub(crate) fn square_lists(cst: &Cst, text: &str, out: &mut Vec<Diagnostic>) {
    let tokens = cst.tokens();
    let brackets = std::cell::OnceCell::new();
    let mut reported_to = 0;
    for (i, t) in tokens.iter().enumerate() {
        if t.kind != TokenKind::LBracket || i < reported_to {
            continue;
        }
        let list = cst.token_parent(TokenIdx(i as u32));
        let Some(expr) = cst.parent(list).filter(|&e| cst.kind(e) == NodeKind::TypeArgsExpr) else { continue };
        if cst.kind(list) != NodeKind::TypeArgs
            || cst.child_tokens(expr).any(|c| cst.token(c).kind == TokenKind::ColonColon)
        {
            continue;
        }
        // The parser read the list after `type_list_ahead`: a `]` closes it.
        let close = crate::scan::Brackets::of(&brackets, tokens).contents(i).map_or_else(
            || onsa_diag::internal::bug(Some(t.span), "a list of type arguments with no `::` and no `]` with `,`"),
            |c| c.0,
        );
        reported_to = close;
        let span = Span::new(t.span.file, t.span.start, tokens[close].span.end);
        let fix = Fix::new(TYPE_ARGS_WITH_COLONS, vec![Edit::insert(t.span.file, t.span.start, "::")]);
        out.push(diagnostic(text, RowId::TypeArgsSquareComma, Hit::new(span, vec![fix])));
    }
}
