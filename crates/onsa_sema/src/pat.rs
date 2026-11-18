//! The walk of a pattern: its bindings in the order written.

use onsa_syntax::ast::{Ast, Ident, PatId, PatKind};

/// Calls `f` with each `Bind` leaf of the pattern `p` and its name, in the
/// order written: in each branch of an `Or` when `into_or`, else in none of them.
pub(crate) fn each_bind(ast: &Ast, p: PatId, into_or: bool, f: &mut impl FnMut(PatId, &Ident)) {
    match &ast.pat(p).kind {
        PatKind::Bind(name) => f(p, name),
        PatKind::Or(_) if !into_or => {}
        PatKind::TupleStruct { elems: ps, .. } | PatKind::Tuple(ps) | PatKind::Or(ps) => {
            ps.iter().for_each(|&q| each_bind(ast, q, into_or, f))
        }
        PatKind::Struct { fields, .. } => fields.iter().for_each(|&(_, q)| each_bind(ast, q, into_or, f)),
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
    }
}

#[cfg(test)]
mod tests;
