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
//!   of a first-class Copy type, or is a binding that needs no drop or a
//!   path of one (L4); else it is owned, with the first element that is none
//!   of these. Parentheses are what they hold.
//! - A leaf or an aggregate whose own type is not Dup (Affine, or `T: ?Dup`)
//!   is none of these whatever its elements (S-780, F7): a leaf has no mark,
//!   an aggregate is owned with itself as the first.
//!
//! The kinds are those of the types after the inference of the body, its
//! type parameters by their bounds ([`kind_in_body`]); a type with no kind
//! (a second-class `Span`, a walk that keeps quiet, §18.1) is not Copy.

use onsa_syntax::ast::{Ast, ExprId, ExprKind, Lit, Mode, StrSeg};

use super::{Bind, LitClass, Settle};
use crate::body::{BodyInfo, Target};
use crate::kind::{Kind, kind_in_body};
use crate::names::body::PathRes;
use crate::resolve::NameKind;
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
            match self.info.lits.get(&x).copied().filter(|_| whole) {
                Some(LitClass::Static) => {}
                Some(LitClass::NoDrop) => class = LitClass::NoDrop,
                _ if (whole && self.no_drop_path(x)) || self.kind(x) == Some(Kind::Copy) => class = LitClass::NoDrop,
                _ => return Some(LitClass::Owned { first: x }),
            }
        }
        Some(class)
    }

    /// Whether `e` is a leaf static value (its own type aside).
    fn leaf(&self, e: ExprId) -> bool {
        match &self.ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => !s.pathless_hole && s.segments.iter().all(|x| matches!(x, StrSeg::Text(_))),
            ExprKind::Lit(Lit::Int { .. } | Lit::Float { .. } | Lit::Bool(_) | Lit::Char(_)) => true,
            ExprKind::Path(_) | ExprKind::Field { .. } => match self.info.targets.get(&e) {
                Some(Target::Const(_) | Target::ConstParam(_) | Target::BuiltinConst { .. }) => true,
                // A variant with a payload named as a value is a function.
                t if variant(t) => {
                    let ty = self.info.expr_types.get(&e).map(|&t| self.a.types.get(t));
                    ty.is_some_and(|t| !matches!(t, Ty::Fn(_)))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether `e` is the name of a binding that needs no drop or a path of
    /// one (S-613 L4): its fields, elements and tuple elements, through
    /// parentheses. A binding not settled yet is owned.
    fn no_drop_path(&self, e: ExprId) -> bool {
        let root = self.ast.place_root_node(e).and_then(|r| self.names.paths.get(&r));
        let Some(PathRes::Local(b)) = root else { return false };
        self.info.locals[b.0 as usize].state == Bind::Borrow { no_drop: true }
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

/// Whether `t` names a variant, of a user enum or of the prelude (`Some`,
/// `None`, …, [`NameKind::of_builtin`]).
fn variant(t: Option<&Target>) -> bool {
    match t {
        Some(Target::Variant { .. }) => true,
        Some(Target::Prelude(b)) => NameKind::of_builtin(*b) == NameKind::Variant,
        _ => false,
    }
}
