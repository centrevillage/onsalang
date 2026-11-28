//! The places read and written, as a root and its steps ([`Path`]), and
//! whether two may share storage ([`disjoint`]): the one test of the
//! normalization and of V-21 and V-24 (D-15). It is the rule of the
//! checks (S-796): an index is the same as any other, whatever its value,
//! so only two different fields at the same step part two places.
//! A local of `LocalKind::Alias` stands for the place it names
//! ([`alias::resolve`]).

use crate::alias::{self, Table};
use crate::ir::{Expr, ExprKind, LocalId, Place};

/// A place without its indices: the local and the steps from it, outermost
/// last. Its root is no alias of the table it was made with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path {
    pub root: LocalId,
    pub steps: Vec<Step>,
}

/// A step into a value: a field of a struct or an element of a tuple, or
/// an element of an array at any index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    Field(u32),
    Index,
}

impl Path {
    /// The path of place `p`, through the aliases of `t`.
    pub fn of_place(t: &Table, p: &Place) -> Path {
        let p = alias::resolve(t, p);
        let mut steps = Vec::new();
        push_steps(&p, &mut steps);
        Path { root: p.root(), steps }
    }

    /// The path of expression `e` if it is a place (of the forms of
    /// [`Expr::as_place`]), through the aliases of `t`; `None` otherwise.
    pub fn of_expr(t: &Table, e: &Expr) -> Option<Path> {
        let mut steps = Vec::new();
        let mut x = e;
        let root = loop {
            let (step, base) = match &x.kind {
                ExprKind::Local(l) => break *l,
                ExprKind::Field { base, index } => (Step::Field(*index), base),
                ExprKind::Index { base, .. } => (Step::Index, base),
                _ => return None,
            };
            steps.push(step);
            x = base;
        };
        let mut path = Path::of_place(t, &Place::Local(root));
        path.steps.extend(steps.into_iter().rev());
        Some(path)
    }
}

/// The steps of `p`, outermost last, after `out`'s.
fn push_steps(p: &Place, out: &mut Vec<Step>) {
    match p {
        Place::Local(_) => {}
        Place::Field(b, i) => {
            push_steps(b, out);
            out.push(Step::Field(*i));
        }
        Place::Index(b, ..) => {
            push_steps(b, out);
            out.push(Step::Index);
        }
    }
}

/// Whether places `a` and `b` share no storage: their roots differ, or at a
/// step both have they are different fields. Otherwise they may overlap:
/// one a prefix of the other, or apart only by indices.
pub fn disjoint(a: &Path, b: &Path) -> bool {
    a.root != b.root || a.steps.iter().zip(&b.steps).any(|s| matches!(s, (Step::Field(x), Step::Field(y)) if x != y))
}
