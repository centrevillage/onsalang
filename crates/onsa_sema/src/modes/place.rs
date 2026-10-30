//! Places (W4-07 memo 1.2, 1.7; §5.1, §5.2): a local and the projections
//! that reach a part of it. It reads the syntax tree and the names only, not
//! the walk (W8-05 makes it public). U3b adds the projections of a pattern
//! and the index of §7; W4-08 the views.

use onsa_syntax::ast::{Ast, ExprId, ExprKind};

use crate::body::LocalId;
use crate::names::body::{BodyNames, PathRes};

/// A place (§5.1): a local and its projections, outermost last.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Place {
    pub(super) root: LocalId,
    pub(super) proj: Vec<Proj>,
}

/// One step into a value: a field, a tuple element, an element of a
/// payload (a pattern's, U3b), an element of an array at an index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Proj {
    Field(String),
    Elem(u32),
    #[allow(dead_code)] // The patterns of U3b make it.
    Payload(u32),
    Index,
}

/// The place `e` is, through parentheses: a local, and its fields, tuple
/// elements and elements (§5.2); `None` for any other value (a call, a
/// literal, a constant, a function item, a block, an `if` or a `match`).
pub(super) fn place_of(ast: &Ast, names: &BodyNames, e: ExprId) -> Option<Place> {
    let x = ast.without_parens(e);
    let (base, step) = match &ast.expr(x).kind {
        ExprKind::Path(_) => {
            let Some(PathRes::Local(b)) = names.paths.get(&x) else { return None };
            return Some(Place { root: LocalId(b.0), proj: Vec::new() });
        }
        ExprKind::Field { base, name } => (*base, Proj::Field(name.name.clone())),
        ExprKind::TupleIndex { base, index, .. } => (*base, Proj::Elem(*index)),
        ExprKind::Index { base, .. } => (*base, Proj::Index),
        _ => return None,
    };
    let mut place = place_of(ast, names, base)?;
    place.proj.push(step);
    Some(place)
}

/// Whether the places `a` and `b` may share a part (§5.2): the same local,
/// and the projections the same up to the shorter one, where two indexes
/// are taken as the same (they are not compared statically). U4 reads it
/// (E0702).
#[allow(dead_code)] // E0702 of U4 reads it.
pub(super) fn overlaps(a: &Place, b: &Place) -> bool {
    a.root == b.root && a.proj.iter().zip(&b.proj).all(|(p, q)| p == q)
}
