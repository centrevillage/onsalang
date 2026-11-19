//! The state marking (S-05): the stages at which each local is read
//! (`FlowInfo::read_at`) and the stage at which `sample_rate()` is read,
//! from the clocks of the walk ([`Walked`], the `let`s), which tell what
//! the state keeps ([`FlowInfo::stored`]); and, in the same walk, the
//! subexpressions hoisted to a slower stage, whose parts are read there
//! ([`super::hoist`], §11.3). The lowering reads these and does not walk
//! the body again (R-91 (1), D-15).

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, BinOp};

use super::clocks::Walked;
use super::hoist::{Choose, Cond, Place};
use super::*;
use crate::names::body::Binding;

#[cfg(test)]
mod tests;

/// What the marking gives.
pub(super) struct Marked {
    pub(super) read_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    pub(super) sample_rate_at: Option<ClockStage>,
    /// The first call (in the order of the file) of a function that is not
    /// `rt` evaluated at a stage after `init` (R-17): E0815 in a
    /// conditional position a condition decided after `init` selects
    /// (§11.5); else E0200, of a type that is not Copy (S-1160) or of
    /// constants only (W9-03).
    pub(super) diag: Option<Diagnostic>,
    /// The locals of the `let`s the initializer of each `let` reads (by its
    /// index; the last, the output), `^y` too: the reads what is reached
    /// goes by ([`reached`]). W7-15 makes them from the edges of the plan.
    pub(super) deps: Vec<HashSet<LocalId>>,
    /// The hoisted subexpressions in the order of the walk, with their
    /// stages, owners and whether they are guarded, of which the plan makes
    /// its table.
    pub(super) hoisted: Vec<(ExprId, ClockStage, Owner, bool)>,
    /// `FlowInfo::checks` and `FlowInfo::const_conds`.
    pub(super) checks: HashMap<ExprId, ClockStage>,
    pub(super) const_conds: HashMap<ExprId, Cond>,
}

struct Marker<'a> {
    ast: &'a Ast,
    text: &'a str,
    body: &'a BodyInfo,
    clocks: &'a Walked,
    choose: Choose<'a>,
    /// The walk had a diagnostic: it did not record the nodes it did not
    /// reach (in a branch, in `if~` / `match~`).
    partial: bool,
    non_rt: &'a HashMap<ExprId, bool>,
    let_of_local: &'a HashMap<LocalId, usize>,
    /// The `let` whose initializer is marked now (its index), or the output.
    consumer: usize,
    /// The conditions on the path to the expression marked now, each with
    /// the conditions on its own path (§11.3: of an `if`, the left of `&&` /
    /// `||`, the scrutinee and the guards before of a `match`).
    conds: Vec<(ExprId, Cond)>,
    /// The conditions read at a stage, for a guarded part there.
    cond_read: HashSet<(ExprId, ClockStage)>,
    /// The hoisted subexpressions.
    seen: HashSet<ExprId>,
    /// The parts of a constant expression are marked (their reads only).
    konst: bool,
    /// The `par~`s of the walk by their expressions, and those whose bodies
    /// hold the expression marked now, the innermost last: its owner.
    par_of: HashMap<ExprId, NodeId>,
    pars: Vec<NodeId>,
    out: Marked,
}

/// The stage a read at the clock `c` is at: a constant at `init`, the first
/// stage (as a constant `let` no one reads, defined there); none of a clock
/// in error, which comes with a diagnostic of the callee and is not lowered.
fn read_stage(c: Clock) -> Option<ClockStage> {
    match c {
        Clock::Const => Some(ClockStage::Init),
        c => c.stage(),
    }
}

/// The stages each local is read at and the stage at which `sample_rate()`
/// is read (S-05), in the module of `ast` and `text`, from the walk `walked`, also
/// one with a diagnostic. A `let` in error is not marked.
pub(super) fn mark_all(
    a: &Analysis,
    ast: &Ast,
    text: &str,
    body: &BodyInfo,
    cx: &FlowCx,
    walked: &Walked,
    lets: &[FlowLet],
) -> Marked {
    let nodes: HashSet<ExprId> = cx.calls.iter().map(|c| c.expr).collect();
    let sample_rate: HashSet<ExprId> = cx.sample_rate_calls.iter().copied().collect();
    let choose = Choose { a, ast, body, clocks: &walked.info, nodes: &nodes, sample_rate: &sample_rate };
    let recorded = walked.recorded.iter().enumerate();
    let par_of = recorded.filter(|(_, r)| matches!(r.kind, PlanKind::Par { .. }));
    let par_of = par_of.map(|(i, r)| (r.expr, NodeId(i as u32))).collect();
    let mut m = Marker {
        ast,
        text,
        body,
        clocks: walked,
        choose,
        partial: walked.diag.is_some(),
        non_rt: &walked.non_rt,
        let_of_local: &cx.let_of_local,
        consumer: lets.len(),
        conds: Vec::new(),
        cond_read: HashSet::default(),
        seen: HashSet::default(),
        konst: false,
        par_of,
        pars: Vec::new(),
        out: Marked {
            read_at: HashMap::default(),
            sample_rate_at: None,
            diag: None,
            deps: vec![HashSet::default(); lets.len() + 1],
            hoisted: Vec::new(),
            checks: HashMap::default(),
            const_conds: HashMap::default(),
        },
    };
    // The `let`s and the output are evaluated at their stages whether and
    // where they are read (§11.3, S-1093): roots under no condition.
    for (k, l) in lets.iter().enumerate().filter(|(_, l)| l.clock != Clock::Const) {
        if let Some(s) = read_stage(l.clock) {
            m.consumer = k;
            m.mark(l.init, s, Cond::None);
        }
    }
    if let Some(out) = cx.output {
        m.consumer = lets.len();
        m.mark(out, ClockStage::SAMPLE, Cond::None);
    }
    // A constant `let` is defined in each phase that reads it, and its
    // initializer read there (§11.3, R-488): from the last, so that one
    // read by a later constant `let` has the stages of that one.
    for (k, l) in lets.iter().enumerate().rev().filter(|(_, l)| l.clock == Clock::Const) {
        m.consumer = k;
        let reads = l.locals.iter().filter_map(|id| m.out.read_at.get(id));
        let mut stages: BTreeSet<ClockStage> = reads.flatten().copied().collect();
        if stages.is_empty() {
            stages.insert(ClockStage::Init);
        }
        for s in stages {
            m.mark(l.init, s, Cond::None);
        }
    }
    m.out
}

/// The locals of the `let`s reached from the output and from the `let`s
/// that bind no name (§5.1, S-727), through the reads `deps` of
/// [`Marked`]: each `let` is visited once, so the walk is linear in the
/// `let`s and their reads, and ends.
pub(super) fn reached(
    lets: &[FlowLet],
    deps: &[HashSet<LocalId>],
    let_of_local: &HashMap<LocalId, usize>,
) -> HashSet<LocalId> {
    let roots = lets.iter().enumerate().filter(|(_, l)| l.binds_none()).map(|(k, _)| k);
    let mut todo: Vec<usize> = roots.chain([lets.len()]).collect();
    let mut seen = vec![false; deps.len()];
    todo.iter().for_each(|&k| seen[k] = true);
    let mut out = HashSet::default();
    while let Some(k) = todo.pop() {
        for &id in &deps[k] {
            out.insert(id);
            let j = let_of_local[&id];
            if !std::mem::replace(&mut seen[j], true) {
                todo.push(j);
            }
        }
    }
    out
}

/// The E0309 of the bindings of the complete flow `id` that are not used
/// (§5.1, S-129, S-1146), of the names stage's record: a `let` not
/// [`reached`], whose notes show the `let`s that read it, and a binding of
/// an arm by its reads; the first, which the unit reports. Reported of the
/// last stage (S-726).
pub(super) fn unused(
    a: &Analysis,
    id: DefId,
    ast: &Ast,
    info: &FlowInfo,
    deps: &[HashSet<LocalId>],
    cx: &FlowCx,
) -> Option<Diagnostic> {
    let names = a.names.get(&id).filter(|n| n.complete)?;
    let reached = reached(&info.lets, deps, &cx.let_of_local);
    let mut readers: HashMap<LocalId, Vec<Span>> = HashMap::default();
    for (l, d) in info.lets.iter().zip(deps) {
        d.iter().for_each(|&v| readers.entry(v).or_default().push(ast.pat(l.pat).span));
    }
    let unreached = |b: &Binding| {
        let Some(&v) = b.sites.first().and_then(|p| info.body.pat_locals.get(p)) else {
            onsa_diag::internal::bug(Some(b.span), "a `let` of a flow with no local")
        };
        (!reached.contains(&v)).then(|| readers.get(&v).cloned().unwrap_or_default())
    };
    use crate::names::body::{unused, unused_binding};
    #[cfg(test)]
    tests::record(names, &unreached, ast);
    let first =
        unused(names, &unreached).reduce(|x, y| if Diagnostic::place_before(y.0.span, x.0.span) { y } else { x });
    first.map(|(b, readers)| unused_binding(b, ast, readers))
}

impl Marker<'_> {
    /// Marks `e`, read at the stage `at` under the conditions `g` on its
    /// path: hoisted ([`Choose::place`]), it is evaluated, and its parts
    /// read, at its own stage; guarded, the conditions on its path are read
    /// there too. A computed constant in a conditional position is
    /// recorded, and its parts read where it is evaluated.
    fn mark(&mut self, e: ExprId, at: ClockStage, g: Cond) {
        let place = if self.konst { Place::Here } else { self.choose.place(e, at, g) };
        let at = match place {
            Place::Hoist(s) => {
                // A part of a condition read again (`read_conds`) is in the
                // table once.
                if !self.seen.insert(e) {
                    return;
                }
                let owner = match (self.pars.last(), self.consumer) {
                    (Some(&p), _) => Owner::Par(p),
                    (None, k) if k < self.out.deps.len() - 1 => Owner::Let(k as u32),
                    (None, _) => Owner::Output,
                };
                self.out.hoisted.push((e, s, owner, g != Cond::None));
                if g != Cond::None {
                    self.read_conds(s);
                }
                s
            }
            Place::Check(_) | Place::Const => {
                self.out.const_conds.insert(e, g);
                if let Place::Check(s) = place {
                    self.out.checks.insert(e, s);
                    self.read_conds(s);
                    self.konst_parts(e, s, g);
                }
                // W9-03 evaluates it once; until then, also where it is read.
                return self.konst_parts(e, at, g);
            }
            Place::Here => at,
        };
        let ast = self.ast;
        let expr = ast.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(Target::Local(id)) = self.body.targets.get(&e) {
                    self.out.read_at.entry(*id).or_default().insert(at);
                    if self.let_of_local.contains_key(id) {
                        self.out.deps[self.consumer].insert(*id);
                    }
                }
                if let ExprKind::Field { base, .. } = &expr.kind
                    && !self.body.targets.contains_key(&e)
                {
                    self.mark(*base, at, g);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if self.choose.nodes.contains(&e) {
                    let clocks = self.clocks;
                    let Some(&k) = clocks.node_of.get(&e) else {
                        if self.partial {
                            return;
                        }
                        onsa_diag::internal::bug(Some(expr.span), "a node the walk of the clocks did not reach")
                    };
                    // A node is in no branch (K-08): its arguments are roots
                    // of their own, under the body of a `par~` around it.
                    for r in &clocks.nodes[k].args {
                        if let Some(s) = read_stage(r.at) {
                            self.mark(r.expr, s, g);
                        }
                    }
                } else if self.choose.sample_rate.contains(&e) {
                    self.out.sample_rate_at = Some(self.out.sample_rate_at.map_or(at, |s| s.max(at)));
                } else {
                    self.non_rt_here(e, *callee, at, g);
                    if let Some(base) = crate::names::body::receiver(ast, *callee)
                        && self.body.expr_types.contains_key(&base)
                    {
                        self.mark(base, at, g);
                    }
                    for x in args {
                        self.mark(x.expr, at, g);
                    }
                }
            }
            // The body of a `par~`, whose fields are of each replica
            // (S-1140). One a walk with a diagnostic did not reach has no
            // node, and a flow in error no table: its body is marked for
            // the reads and the diagnostics only.
            ExprKind::Par { body, .. } => match self.par_of.get(&e) {
                Some(&p) => {
                    self.pars.push(p);
                    self.mark(*body, at, g);
                    self.pars.pop();
                }
                None if self.partial => self.mark(*body, at, g),
                None => onsa_diag::internal::bug(Some(expr.span), "a `par~` the walk of the clocks did not reach"),
            },
            // The conditional positions (§11.3) under the conditions that
            // select them, not the arms of `if~` / `match~` (W7-06).
            ExprKind::If { cond, then, else_, tilde: None } => {
                self.mark(*cond, at, g);
                let inner = self.enter(*cond, at, g);
                for x in [Some(*then), *else_].into_iter().flatten() {
                    self.mark(x, at, inner);
                }
                self.conds.pop();
            }
            ExprKind::Match { scrutinee, arms, tilde: None } => {
                self.mark(*scrutinee, at, g);
                let (depth, mut inner) = (self.conds.len(), self.enter(*scrutinee, at, g));
                for arm in arms {
                    if let Some(x) = arm.guard {
                        self.mark(x, at, inner);
                        inner = self.enter(x, at, inner);
                    }
                    self.mark(arm.body, at, inner);
                }
                self.conds.truncate(depth);
            }
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
                self.mark(*lhs, at, g);
                let inner = self.enter(*lhs, at, g);
                self.mark(*rhs, at, inner);
                self.conds.pop();
            }
            _ => {
                for child in ast.sub_exprs(e) {
                    self.mark(child, at, g);
                }
            }
        }
    }

    /// The condition `c` read at `at` under `g`, entered: the conditions
    /// under it, of the stage it is decided at ([`Choose::cond_stage`]).
    fn enter(&mut self, c: ExprId, at: ClockStage, g: Cond) -> Cond {
        self.conds.push((c, g));
        g.max(self.choose.cond_stage(c, at))
    }

    /// The conditions on the path, read at `s` (once each) by the guards of
    /// a guarded part there: each under the conditions before it.
    fn read_conds(&mut self, s: ClockStage) {
        for k in 0..self.conds.len() {
            let (c, g) = self.conds[k];
            if self.cond_read.insert((c, s)) {
                let rest = self.conds.split_off(k);
                self.mark(c, s, g);
                self.conds.extend(rest);
            }
        }
    }

    /// The reads of the parts of the constant expression `e` at `s`.
    fn konst_parts(&mut self, e: ExprId, s: ClockStage, g: Cond) {
        let k = std::mem::replace(&mut self.konst, true);
        self.mark(e, s, g);
        self.konst = k;
    }

    /// A call at `e` of the function `callee` that is not `rt`, with values
    /// at `init` ([`Walked::non_rt`]), evaluated at a stage after `init`,
    /// under the conditions `g`: one not hoisted to `init` (R-17). With a
    /// value that is not a constant, a condition decided after `init`
    /// selects its place: E0815 (§11.5, S-1157). Else E0200: of a type that
    /// is not Copy (S-1160) or of constants only (W9-03).
    fn non_rt_here(&mut self, e: ExprId, callee: ExprId, at: ClockStage, g: Cond) {
        let Some(&varies) = self.non_rt.get(&e).filter(|_| at > ClockStage::Init) else { return };
        let span = self.ast.expr(e).span;
        let found = span.text_in(self.text).to_string();
        let d = if varies && g > Cond::Init {
            let name = self.ast.expr(callee).span.text_in(self.text);
            let msg = format!(
                "`{name}` is not `rt`, and a condition decided after `init` selects this place, so it cannot be computed at `init`; bind it with a `let` before the condition (§11.3, §11.5)"
            );
            Diagnostic::new(Stage::Flow, Code::E0815, span, msg)
        } else {
            let stage = match at {
                ClockStage::Block => ClockName::Block.name(),
                ClockStage::SAMPLE => ClockName::Sample.name(),
                s => onsa_diag::internal::bug(Some(span), format!("a read at the stage {s:?}, which W7-09 makes")),
            };
            // SPEC-GAP(S-1160): one whose result is not Copy is not hoisted,
            // and is E0200 (§11.3, §11.5).
            Feature::NonRtCallAtClock.diagnostic(Stage::Flow, span, &[stage])
        };
        Diagnostic::keep_first(&mut self.out.diag, d.with_found(found));
    }
}
