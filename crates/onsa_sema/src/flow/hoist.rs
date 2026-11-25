//! Hoisting (§11.3, S-33, S-1157): the slow subexpressions of a flow body
//! read at a faster stage are evaluated at their stage (S-1196), and
//! the state keeps their values in hidden fields (`a._hoist_0`, §11.6,
//! §12.4). The marking ([`super::reads`]) asks [`Choose::place`] of each
//! expression it walks, with the stage it is read at, and reads the parts
//! of a hoisted one at its stage: the stages the locals are read at
//! ([`FlowInfo::read_at`], [`FlowInfo::stored`]) come of the choice, made
//! once in one walk (D-15). [`table`] names and orders the fields of the
//! plan; the lowering writes and reads them by [`FlowInfo::hoist_of`].

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, Block};

use super::plan::names;
use super::*;
use crate::flow_names::{HOIST, OUTPUT_SCOPE};

#[cfg(test)]
mod tests;

/// The conditions on the path from a root (a `let`, the output, an
/// argument of a node) to an expression (§11.3, S-1157): the stage at which
/// the one decided last is decided, joined. `None`: no condition. `Const`:
/// constants only (W9-03 decides them at compile time). `Init`, `Block`:
/// decided at that stage, where what they guard is written under them.
/// `Tick`: an event is the one tick that decides them. `Late`: one decided
/// per sample, by a value that is not Copy at a sample, or two by stages with
/// none in common (two events, an event and `block`): what is under it is
/// evaluated where it is reached. The body of a `par~` is no conditional
/// position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Cond {
    None,
    Const,
    Init,
    Block,
    Tick(ClockStage),
    Late,
}

impl Cond {
    fn of(s: ClockStage) -> Cond {
        match s {
            ClockStage::Init => Cond::Init,
            ClockStage::Block => Cond::Block,
            ClockStage::Event(_) => Cond::Tick(s),
            // A part of a periodic tick stands in the conditional positions of an expression
            // of a faster clock, whose conditions are at that clock (`at`).
            ClockStage::Tick(_) => Cond::Late,
        }
    }

    /// Both conditions on one path.
    pub(super) fn join(self, o: Cond) -> Cond {
        match (self, o) {
            (Cond::Tick(a), Cond::Tick(b)) if a != b => Cond::Late,
            (Cond::Tick(_), Cond::Block) | (Cond::Block, Cond::Tick(_)) => Cond::Late,
            (a, b) => a.max(b),
        }
    }

    fn stage(self) -> Option<ClockStage> {
        match self {
            Cond::Init => Some(ClockStage::Init),
            Cond::Block => Some(ClockStage::Block),
            Cond::Tick(s) => Some(s),
            Cond::None | Cond::Const | Cond::Late => None,
        }
    }

    /// The stage the conditions are decided at, of an expression read at
    /// `at`: of those decided where it is reached, `at`.
    pub(super) fn decided(self, at: ClockStage) -> ClockStage {
        self.stage().unwrap_or(at)
    }

    /// Whether a part of the tick `s` may stand under the conditions (§11.3,
    /// S-1158 (c)): of constants, `init` and that tick only.
    pub(super) fn admits(self, s: ClockStage) -> bool {
        match self {
            Cond::None | Cond::Const | Cond::Init => true,
            Cond::Tick(t) => t == s,
            Cond::Block | Cond::Late => false,
        }
    }
}

/// The index of a hoisted subexpression in [`FlowInfo::hoists`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HoistId(pub u32);

/// A hoisted subexpression and its field of the state (§11.3, §11.6).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hoist {
    pub expr: ExprId,
    /// The stage it is evaluated at, `init`, `block` ([`ClockInfo::stage`]
    /// and its conditions) or a tick ([`FlowInfo::starts_default`]): before
    /// every stage that reads it.
    pub stage: ClockStage,
    /// Written only when the conditions on its path hold (S-1157): under
    /// a conditional position, but of [`Place::Field`]. W8-07 makes of it
    /// what `init` sets (V-17).
    pub guarded: bool,
    pub owner: Owner,
    /// `_hoist_<n>`, numbered in its owner from 0 in the order of the
    /// starts of the subexpressions (§11.6).
    pub name: String,
    /// The name after the scope of its owner (`a._hoist_0`,
    /// `_out._hoist_0`, `saws._hoist_0` of the body of the `par~` `saws`):
    /// its field in the `State`; in the replica of a `par~`, its `name`.
    pub path: String,
    pub span: Span,
    /// Of a part of a tick of [`FlowInfo::late`], what it reads of events
    /// where it is written (`plan`'s `events::saved`, S-1249).
    pub saved: Vec<ExprId>,
}

/// Where the marking evaluates an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Place {
    /// In a field written at this stage.
    Hoist(ClockStage),
    /// In a field written at each tick of this stage whatever the conditions
    /// on its path: a field read of a name ([`Choose::of_name`], S-1197).
    Field(ClockStage),
    /// A computed constant expression in a conditional position whose
    /// conditions are decided at this stage, before the stage that reads
    /// it: evaluated there too when they hold, for its panic (S-888 (c′)),
    /// with no field.
    Check(ClockStage),
    /// A computed constant expression in a conditional position, evaluated
    /// where it is read (W9-03 at compile time when its conditions are).
    Const,
    /// Where it is read.
    Here,
    /// A computed part or a node of the tick `stage`, slower than the stage
    /// that reads it, in a conditional position a condition decided at
    /// another stage selects (§11.3, S-1158 (c)): E0815, with no field.
    Refuse(ClockStage),
    /// Such a part of a type that is not Copy (S-1195): E0200, with no
    /// field.
    NotCopy(ClockStage),
}

/// What the choice reads of a flow body.
pub(super) struct Choose<'a> {
    pub(super) a: &'a Analysis,
    pub(super) ast: &'a Ast,
    pub(super) body: &'a BodyInfo,
    pub(super) clocks: &'a ClockInfo,
    /// The calls of the delays and the instances, and of the modifiers of
    /// their chains with their receivers ([`FlowCx::node_exprs`]).
    pub(super) nodes: &'a HashMap<ExprId, Option<ExprId>>,
    pub(super) sample_rate: &'a HashSet<ExprId>,
    pub(super) sample_tick: &'a HashSet<ExprId>,
}

impl Choose<'_> {
    /// Where `e`, read at the stage `at` under the conditions `g`, is
    /// evaluated (§11.3, S-1157): at its stage ([`ClockInfo::stage`],
    /// S-1196) and that of `g`, the later, in a field when that is `init` or
    /// `block` and before `at`, `g` is not `Late` and it may have one
    /// ([`Choose::hoistable`]); else where it is read. The marking reads the
    /// parts of a hoisted one at its stage, so the first met from the root
    /// is the largest, and a slower part in it is hoisted again (`make(a)`
    /// in `level * make(a)`). A computed part or a node of a tick slower
    /// than `at` ([`Choose::tick_field`]) is in a field written at the tick,
    /// guarded under conditions of constants, `init` and that tick; under one
    /// decided at another stage it is refused (S-1158 (c)), but for a field
    /// read of a name, which does not panic (S-1197).
    pub(super) fn place(&self, e: ExprId, at: ClockStage, g: Cond) -> Place {
        let d = match self.clocks.stage(e) {
            Some(Clock::Init) => ClockStage::Init,
            Some(Clock::Block) => ClockStage::Block,
            Some(Clock::Const) if g != Cond::None && self.computed(e) => {
                return g.stage().filter(|&s| s < at).map_or(Place::Const, Place::Check);
            }
            Some(c @ (Clock::Tick(_) | Clock::Event(_))) => {
                let slow = c.stage().filter(|&d| d.stored_slower_than(at) && self.tick_field(e));
                let Some(d) = slow else { return Place::Here };
                // SPEC-GAP(S-1195): of a type that is not Copy, E0200
                // (provisional).
                return match g.admits(d) {
                    _ if !self.nodes.contains_key(&e) && !self.copy(e) => Place::NotCopy(d),
                    _ if self.of_name(e).is_some() => Place::Field(d),
                    true => Place::Hoist(d),
                    false => Place::Refuse(d),
                };
            }
            _ => return Place::Here,
        };
        let s = match g {
            // SPEC-GAP(S-1184): under a condition decided at a tick, where
            // it is reached (provisional).
            Cond::Late | Cond::Tick(_) => return Place::Here,
            g => g.stage().map_or(d, |c| c.max(d)),
        };
        if s >= at || !self.hoistable(e) {
            return Place::Here;
        }
        Place::Hoist(s)
    }

    /// The stage at which the condition `c` (an `if`, the left of `&&` /
    /// `||`, a guard, the scrutinee of a `match`), read at `at`, is decided
    /// (§11.3, S-1166): the faster of its stage and that of its clock, `at`
    /// counted, which is its clock (a stage is never faster than its
    /// clock); of a value that is not Copy, which is not hoisted (S-1046
    /// (a)), `at`.
    pub(super) fn cond_stage(&self, c: ExprId, at: ClockStage) -> Cond {
        if !self.copy(c) {
            return Cond::of(at);
        }
        match self.clocks.exprs.get(&c) {
            Some(Clock::Const) => Cond::Const,
            Some(k) => k.stage().map_or(Cond::Late, Cond::of),
            None => Cond::Late,
        }
    }

    /// Whether `e` may have a field: a [`Choose::part`] whose type is Copy
    /// (S-1046 (a)).
    fn hoistable(&self, e: ExprId) -> bool {
        self.part(e) && self.copy(e)
    }

    /// Whether `e`, of a tick slower than the stage that reads it, has a
    /// field written at the tick: a [`Choose::part`], a node, or
    /// `sample_tick()` under the `at` of the tick or an event value with it,
    /// which keeps the value at the tick as a `let` of it would (S-1210,
    /// §11.11), whose value is kept there with no name (§11.3, §11.6).
    // SPEC-GAP(S-1231): an event value with the `at` of a slower tick stands
    // in a conditional position as `sample_tick()` with it does (provisional).
    fn tick_field(&self, e: ExprId) -> bool {
        let event = |x: ExprId| matches!(self.clocks.stage(x), Some(Clock::Event(_)));
        match &self.ast.expr(e).kind {
            ExprKind::At { expr, .. } => event(*expr),
            _ => self.part(e) || self.nodes.contains_key(&e) || self.sample_tick.contains(&e),
        }
    }

    /// The name `e` is or reads a field or an element of (of a field of it,
    /// and so on), past parentheses.
    pub(super) fn of_name(&self, e: ExprId) -> Option<ExprId> {
        match &self.ast.expr(e).kind {
            ExprKind::Field { base: x, .. } | ExprKind::TupleIndex { base: x, .. } if !self.local(e) => {
                self.of_name(*x)
            }
            ExprKind::Paren(x) => self.of_name(*x),
            _ => self.local(e).then_some(e),
        }
    }

    fn local(&self, e: ExprId) -> bool {
        matches!(self.body.targets.get(&e), Some(Target::Local(_)))
    }

    /// Whether `e` is a computed part: none of a name (an input, a `let`,
    /// the index of a `par~`, a binding of an arm, `^y`), `sample_rate()`,
    /// `sample_tick()` (of a slower tick, [`Choose::tick_field`]) and a
    /// node (§11.3), nor parentheses or `at`, whose operand is the
    /// same value (§11.3: `at` changes no value), nor a
    /// block of a value only, whose value the lowering makes of its tail in
    /// place: the operand or the tail is chosen instead.
    fn part(&self, e: ExprId) -> bool {
        let kind = &self.ast.expr(e).kind;
        !(self.local(e)
            || matches!(kind, ExprKind::At { .. } | ExprKind::Par { .. })
            || value_of(kind).is_some()
            || self.nodes.contains_key(&e)
            || self.sample_rate.contains(&e)
            || self.sample_tick.contains(&e))
    }

    /// A constant expression that is computed: one [`Choose::hoistable`]
    /// would take, not a literal or the name of a constant, nor a field of
    /// one, past parentheses and a block of a value only (`{ (PAIR.1) }`,
    /// `{ None }`): what may panic (S-888 (c′)).
    fn computed(&self, e: ExprId) -> bool {
        let mut x = e;
        loop {
            match &self.ast.expr(x).kind {
                ExprKind::Field { base: y, .. } | ExprKind::TupleIndex { base: y, .. } => x = *y,
                ExprKind::Lit(_) | ExprKind::Path(_) => return false,
                k => match value_of(k) {
                    Some(y) => x = y,
                    None => return self.hoistable(e),
                },
            }
        }
    }

    fn copy(&self, e: ExprId) -> bool {
        self.body.expr_types.get(&e).is_some_and(|&ty| crate::signal::not_copy(self.a, ty).is_none())
    }
}

/// What parentheses or a block of a value only (`{ b * 2.0 }`) hold: the
/// same value, made in place.
fn value_of(kind: &ExprKind) -> Option<ExprId> {
    match kind {
        ExprKind::Paren(y) => Some(*y),
        ExprKind::Block(Block { stmts, tail: Some(y) }) if stmts.is_empty() => Some(*y),
        _ => None,
    }
}

/// The table of the hoisted subexpressions of `info` the marking chose
/// (`marked`: each with its stage, its owner and whether it is guarded),
/// made with the plan:
/// numbered per owner from 0 in the order of the starts of the
/// subexpressions, named `_hoist_<n>` after the scope of the owner (§11.6),
/// in the order of their fields (§12.4: the `let`s in their order, then the
/// output, then the body of each `par~`, whose replica holds them).
// SPEC-GAP(S-1164): two hoisted subexpressions of one owner that start at one
// place (`make(a) * level`, `level` at `block`, and its `make(a)` at
// `init`) are numbered the outer first, in the order of the walk.
// SPEC-GAP(S-1140): those of the body of a `par~` are of each replica,
// numbered in that body by themselves, after the scope of the `par~`
// (`saws._hoist_0`).
pub(super) fn table(info: &mut FlowInfo, ast: &Ast, marked: Vec<(ExprId, ClockStage, Owner, bool)>) {
    let scopes = info.let_scopes();
    let rank = |o: Owner| match o {
        Owner::Let(k) => k as usize,
        Owner::Output => scopes.len(),
        Owner::Par(p) => scopes.len() + 1 + p.0 as usize,
    };
    let mut marked: Vec<_> = marked.into_iter().map(|(e, s, o, g)| (rank(o), ast.expr(e).span, e, s, o, g)).collect();
    marked.sort_by_key(|&(r, span, ..)| (r, span.start));
    let mut hoists: Vec<Hoist> = Vec::with_capacity(marked.len());
    let mut n = 0;
    for (r, span, expr, stage, owner, guarded) in marked {
        // Sorted by owner: the count goes on until the owner changes.
        n = if hoists.last().is_some_and(|h: &Hoist| h.owner == owner) { n + 1 } else { 0 };
        let name = names::local(HOIST, n);
        let scope = match owner {
            Owner::Par(p) => info.node(p).path.as_str(),
            _ => scopes.get(r).map_or(OUTPUT_SCOPE, String::as_str),
        };
        let path = names::qualify(scope, &name);
        hoists.push(Hoist { expr, stage, guarded, owner, name, path, span, saved: Vec::new() });
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

    /// The stage at which the computed constant expression `e` in a
    /// conditional position is evaluated for its panic, if it is one
    /// ([`Place::Check`]).
    pub fn check_of(&self, e: ExprId) -> Option<ClockStage> {
        self.checks.get(&e).copied()
    }
}
