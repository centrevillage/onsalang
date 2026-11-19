//! Hoisting (§11.3, S-33, S-1157): the slow subexpressions of a flow body
//! read at a faster stage are evaluated at the stage of their clock, and
//! the state keeps their values in hidden fields (`a._hoist_0`, §11.6,
//! §12.4). The marking ([`super::reads`]) asks [`Choose::place`] of each
//! expression it walks, with the stage it is read at, and reads the parts
//! of a hoisted one at its stage: the stages the locals are read at
//! ([`FlowInfo::read_at`], [`FlowInfo::stored`]) come of the choice, made
//! once in one walk (D-15). [`table`] names and orders the fields of the
//! plan; the lowering writes and reads them by [`FlowInfo::hoist_of`].

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::Ast;

use super::plan::names;
use super::*;
use crate::flow_names::{HOIST, OUTPUT_SCOPE};

#[cfg(test)]
mod tests;

/// The conditions on the path from a root (a `let`, the output, an
/// argument of a node) to an expression (§11.3): of the condition decided
/// last. `None`: no condition. `Late`: one decided per sample, or one this
/// version takes as such: the inside of a branch of `if` / `match`, of a
/// guard and of the right of `&&` / `||` (W7-05 U2 adds the conditions
/// decided at `init` and `block`), and the body of a `par~` (W7-05 U3).
/// What is under `Late` is evaluated where it is reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Cond {
    None,
    Late,
}

/// The index of a hoisted subexpression in [`FlowInfo::hoists`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HoistId(pub u32);

/// A hoisted subexpression and its field of the state (§11.3, §11.6).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hoist {
    pub expr: ExprId,
    /// The stage it is evaluated at, `init` or `block`: before every stage
    /// that reads it.
    pub stage: ClockStage,
    /// Written only when the conditions on its path hold (S-1157); none is
    /// yet (W7-05 U2). W8-07 makes of it what `init` sets (V-17).
    pub guarded: bool,
    pub owner: Owner,
    /// `_hoist_<n>`, numbered in its owner from 0 in the order of the
    /// starts of the subexpressions (§11.6).
    pub name: String,
    /// The name after the scope of its owner (`a._hoist_0`,
    /// `_out._hoist_0`): its field.
    pub path: String,
    pub span: Span,
}

/// Where the marking evaluates an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Place {
    /// In a field written at this stage.
    Hoist(ClockStage),
    /// Where it is read.
    Here,
}

/// What the choice reads of a flow body.
pub(super) struct Choose<'a> {
    pub(super) a: &'a Analysis,
    pub(super) ast: &'a Ast,
    pub(super) body: &'a BodyInfo,
    pub(super) clocks: &'a ClockInfo,
    /// The calls of the delays and the instances.
    pub(super) nodes: &'a HashSet<ExprId>,
    pub(super) sample_rate: &'a HashSet<ExprId>,
}

impl Choose<'_> {
    /// Where `e`, read at the stage `at` under the conditions `g`, is
    /// evaluated (§11.3): in a field of the stage of its clock when that is
    /// `init` or `block` and before `at`, no condition is on its path and
    /// it may have one ([`Choose::hoistable`]); else where it is read. The
    /// marking reads the parts of a hoisted one at its stage, so the first
    /// met from the root is the largest, and a slower part in it is hoisted
    /// again (`make(a)` in `level * make(a)`).
    pub(super) fn place(&self, e: ExprId, at: ClockStage, g: Cond) -> Place {
        let s = match self.clocks.exprs.get(&e) {
            Some(Clock::Init) => ClockStage::Init,
            Some(Clock::Block) => ClockStage::Block,
            _ => return Place::Here,
        };
        if g != Cond::None || s >= at || !self.hoistable(e) {
            return Place::Here;
        }
        Place::Hoist(s)
    }

    /// Whether `e` may have a field: its type is Copy (S-1046 (a)), and it
    /// is none of a name (an input, a `let`, the index of a `par~`, a
    /// binding of an arm, `^y`), `sample_rate()` and a node (§11.3), nor
    /// parentheses or `at`, whose operand is the same value at the same
    /// stage (§11.3: `at` changes neither): the operand is chosen instead.
    /// A constant has no stage, and is not met here.
    fn hoistable(&self, e: ExprId) -> bool {
        let kind = &self.ast.expr(e).kind;
        let name = matches!(self.body.targets.get(&e), Some(Target::Local(_)));
        if name
            || matches!(kind, ExprKind::Paren(_) | ExprKind::At { .. } | ExprKind::Par { .. })
            || self.nodes.contains(&e)
            || self.sample_rate.contains(&e)
        {
            return false;
        }
        self.body.expr_types.get(&e).is_some_and(|&ty| crate::kind::facts_of(self.a, ty, &[]).not_copy().is_none())
    }
}

/// The table of the hoisted subexpressions of `info` the marking chose
/// (`marked`: each with its stage and its owner), made with the plan:
/// numbered per owner from 0 in the order of the starts of the
/// subexpressions, named `_hoist_<n>` after the scope of the owner (§11.6),
/// in the order of their fields (§12.4: the `let`s in their order, then the
/// output).
// SPEC-GAP(S-1164): two hoisted subexpressions of one owner that start at one
// place (`make(a) * level`, `level` at `block`, and its `make(a)` at
// `init`) are numbered the outer first, in the order of the walk.
pub(super) fn table(info: &mut FlowInfo, ast: &Ast, marked: Vec<(ExprId, ClockStage, Owner)>) {
    let scopes = names::scopes(info.lets.iter().map(|l| l.locals.as_slice()), &info.body);
    let rank = |o: Owner| match o {
        Owner::Let(k) => k as usize,
        Owner::Output => scopes.len(),
        Owner::Par(_) => onsa_diag::internal::bug(None, "a field hoisted in the body of a `par~` (W7-05 U3)"),
    };
    let mut marked: Vec<_> = marked.into_iter().map(|(e, s, o)| (rank(o), ast.expr(e).span, e, s, o)).collect();
    marked.sort_by_key(|&(r, span, ..)| (r, span.start));
    let mut hoists: Vec<Hoist> = Vec::with_capacity(marked.len());
    for (r, span, expr, stage, owner) in marked {
        let n = hoists.iter().rev().take_while(|h| h.owner == owner).count();
        let name = names::local(HOIST, n as u32);
        let scope = scopes.get(r).map_or(OUTPUT_SCOPE, String::as_str);
        let path = names::qualify(scope, &name);
        hoists.push(Hoist { expr, stage, guarded: false, owner, name, path, span });
    }
    info.hoisted = hoists.iter().enumerate().map(|(i, h)| (h.expr, HoistId(i as u32))).collect();
    info.hoists = hoists;
}

impl FlowInfo {
    /// The field of the hoisted subexpression `e`, if it is one.
    pub fn hoist_of(&self, e: ExprId) -> Option<HoistId> {
        self.hoisted.get(&e).copied()
    }

    pub fn hoist(&self, h: HoistId) -> &Hoist {
        &self.hoists[h.0 as usize]
    }
}
