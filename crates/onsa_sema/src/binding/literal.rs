//! Static values (spec §5.4, S-610): the marks of [`BodyInfo::lits`]. The
//! leaves only: a string literal with no interpolation, a number, a `Bool`
//! and a `Char` literal, and the name of a `const` whose type is Dup (S-780:
//! a value that is not Dup is owned; an Affine `const` is E0407, §6.6), a
//! const parameter or an associated constant of a builtin type (`F32.PI`).
//! A name is known by what
//! the types stage resolved the node a chain of names ends at to, through
//! namespaces (`m.LIMIT`, `T.ZERO`), not by the form of the chain (`-1` is
//! an operator, §5.4).
// The aggregates of static values, the unit variants and the
// literals that need no drop (S-613) are W4-16 U2.

use onsa_syntax::ast::{Ast, ExprId, ExprKind, Lit, StrSeg};

use super::LitClass;
use crate::Analysis;
use crate::body::{BodyInfo, Target};
use crate::kind::Kind;

/// The mark of the node `e` when it is a leaf static value.
pub(super) fn leaf(a: &Analysis, ast: &Ast, info: &BodyInfo, e: ExprId) -> Option<LitClass> {
    let leaf = match &ast.expr(e).kind {
        ExprKind::Lit(Lit::Str(s)) => !s.pathless_hole && s.segments.iter().all(|x| matches!(x, StrSeg::Text(_))),
        ExprKind::Lit(Lit::Int { .. } | Lit::Float { .. } | Lit::Bool(_) | Lit::Char(_)) => true,
        ExprKind::Path(_) | ExprKind::Field { .. } => match info.targets.get(&e) {
            Some(Target::ConstParam(_) | Target::BuiltinConst { .. }) => true,
            Some(Target::Const(_)) => {
                let kind = info.expr_types.get(&e).and_then(|&t| a.kind_of(t));
                matches!(kind, Some(Kind::Copy | Kind::Shared))
            }
            _ => false,
        },
        _ => false,
    };
    leaf.then_some(LitClass::Static)
}
