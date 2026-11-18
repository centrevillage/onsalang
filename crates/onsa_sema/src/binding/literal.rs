//! Static values (spec §5.4, S-610) and literals that need no drop (S-613):
//! the marks of [`BodyInfo::lits`], given in post-order, a node after its
//! elements.
//!
//! - A leaf static value: a string literal with no interpolation, a number,
//!   a `Bool` and a `Char` literal, the name of a `const`, a const parameter
//!   or an associated constant of a builtin type (`F32.PI`), and a unit
//!   variant (`E.A`, `None`). A name is known by what the types stage
//!   resolved the node a chain of names ends at to, through namespaces
//!   (`m.LIMIT`, `T.ZERO`), not by the form of the chain (`-1` is an
//!   operator, §5.4).
//! - An aggregate ([`parts`]: an array, `[e; N]`, a tuple, a struct literal,
//!   a call of a variant with a payload) is static when all its elements
//!   are, and needs no drop when each element is static, needs no drop, is
//!   of a first-class Copy type, or is a value that needs no drop (L4,
//!   S-1065: [`no_drop`], through paths and tails); else it
//!   is owned, with the first element that is none of these. Parentheses are
//!   what they hold.
//! - A leaf or an aggregate whose own type is not Dup (Affine, or `T: ?Dup`)
//!   is none of these whatever its elements (S-780, F7): a leaf has no mark,
//!   an aggregate is owned with itself as the first.
//!
//! The kinds are those of the types after the inference of the body, its
//! type parameters by their bounds ([`kind_in_body`]); a type with no kind
//! (a second-class `Span`, a walk that keeps quiet, §18.1) is not Copy.

use onsa_syntax::ast::{Ast, ExprId, ExprKind, Lit, Mode};

use super::{LitClass, Settle, no_drop};
use crate::Analysis;
use crate::body::{BodyInfo, Target};
use crate::kind::{Kind, kind_in_body};
use crate::ty::Ty;

impl Settle<'_> {
    /// The mark of `e`, its elements marked before.
    pub(super) fn class(&mut self, e: ExprId) -> Option<LitClass> {
        let ast = self.ast;
        if let ExprKind::Paren(x) = ast.expr(e).kind {
            return self.info.lits.get(&x).copied();
        }
        let Some(parts) = parts(ast, self.info, e) else {
            return (self.leaf(e) && self.dup(e)).then_some(LitClass::Static);
        };
        if !self.dup(e) {
            return Some(LitClass::Owned { first: e });
        }
        let mut class = LitClass::Static;
        for (x, whole) in parts {
            let path = whole && no_drop(ast, self.names, self.info, x);
            match self.info.lits.get(&x).copied().filter(|_| whole) {
                Some(LitClass::Static) => {}
                Some(LitClass::NoDrop) => class = LitClass::NoDrop,
                _ if path || self.kind(x) == Some(Kind::Copy) => class = LitClass::NoDrop,
                _ => return Some(LitClass::Owned { first: x }),
            }
        }
        Some(class)
    }

    /// Whether `e` is a leaf static value (its own type aside).
    fn leaf(&self, e: ExprId) -> bool {
        match &self.ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => s.value().is_some(),
            ExprKind::Lit(Lit::Int { .. } | Lit::Float { .. } | Lit::Bool(_) | Lit::Char(_)) => true,
            ExprKind::Path(_) | ExprKind::Field { .. }
                if matches!(self.info.targets.get(&e), Some(Target::Const { .. } | Target::ConstParam(_))) =>
            {
                true
            }
            // As the name before them (`None::[Str]`, §4.5).
            ExprKind::TypeArgs { base, .. } => self.leaf(*base),
            _ => unit_variant(self.a, self.ast, self.info, e),
        }
    }

    /// Whether the value of `e` is Dup (S-780).
    fn dup(&mut self, e: ExprId) -> bool {
        matches!(self.kind(e), Some(Kind::Copy | Kind::Shared))
    }

    /// The kind of the value of `e` (§4.6, R-30), asked once for each type
    /// of the body.
    fn kind(&mut self, e: ExprId) -> Option<Kind> {
        let t = *self.info.expr_types.get(&e)?;
        if let Some(&k) = self.kinds.get(&t) {
            return k;
        }
        let k = kind_in_body(self.a, t, &self.generics);
        self.kinds.insert(t, k);
        k
    }
}

/// Whether `e` is an aggregate literal ([`parts`]).
pub(crate) fn aggregate(ast: &Ast, info: &BodyInfo, e: ExprId) -> bool {
    parts(ast, info, e).is_some()
}

/// Whether `e` names a unit variant (`E.A`, `None`; the `None` of
/// `None::[Str]`): a variant with a payload named as a value is a function.
pub(crate) fn unit_variant(a: &Analysis, ast: &Ast, info: &BodyInfo, e: ExprId) -> bool {
    matches!(ast.expr(e).kind, ExprKind::Path(_) | ExprKind::Field { .. })
        && variant(info.targets.get(&e))
        && info.expr_types.get(&e).is_some_and(|&t| !matches!(a.types.get(t), Ty::Fn(_)))
}

/// The elements of `e` when it is an aggregate literal (S-610), each with
/// whether it may count by its own mark or as a path (`false`: a `move`
/// argument of a variant, which counts by its kind alone).
fn parts(ast: &Ast, info: &BodyInfo, e: ExprId) -> Option<Vec<(ExprId, bool)>> {
    let all = |xs: &[ExprId]| xs.iter().map(|&x| (x, true)).collect();
    match &ast.expr(e).kind {
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => Some(all(xs)),
        // `N` is a constant (§4.2), no element.
        ExprKind::Repeat { elem, .. } => Some(vec![(*elem, true)]),
        ExprKind::Struct { fields, .. } => Some(fields.iter().map(|(_, x)| (*x, true)).collect()),
        // The call of a variant, which has a payload.
        ExprKind::Call { args, .. } if variant(info.targets.get(&e)) => {
            Some(args.iter().map(|a| (a.expr, a.mode == Mode::Borrow)).collect())
        }
        _ => None,
    }
}

/// Whether `t` names a variant.
fn variant(t: Option<&Target>) -> bool {
    matches!(t, Some(Target::Variant { .. }))
}
