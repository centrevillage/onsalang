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
    /// `rt` evaluated at a stage after `init` (E0200, R-17): in a branch, a
    /// guard, the right of `&&` / `||` or the body of a `par~` (W7-05 U2
    /// and U3), or of a type that is not Copy (S-1160).
    pub(super) diag: Option<Diagnostic>,
    /// The locals of the `let`s the initializer of each `let` reads (by its
    /// index; the last, the output), `^y` too: the reads what is reached
    /// goes by ([`reached`]). W7-15 makes them from the edges of the plan.
    pub(super) deps: Vec<HashSet<LocalId>>,
    /// The hoisted subexpressions in the order of the walk, with their
    /// stages and owners, of which the plan makes its table.
    pub(super) hoisted: Vec<(ExprId, ClockStage, Owner)>,
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
    non_rt: &'a HashSet<ExprId>,
    let_of_local: &'a HashMap<LocalId, usize>,
    /// The `let` whose initializer is marked now (its index), or the output.
    consumer: usize,
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
        out: Marked {
            read_at: HashMap::default(),
            sample_rate_at: None,
            diag: None,
            deps: vec![HashSet::default(); lets.len() + 1],
            hoisted: Vec::new(),
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
    /// read, at its own stage.
    fn mark(&mut self, e: ExprId, at: ClockStage, g: Cond) {
        let at = match self.choose.place(e, at, g) {
            Place::Hoist(s) => {
                let owner = match self.consumer {
                    k if k < self.out.deps.len() - 1 => Owner::Let(k as u32),
                    _ => Owner::Output,
                };
                self.out.hoisted.push((e, s, owner));
                s
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
                    self.non_rt_here(e, at);
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
            // The body of a `par~` (W7-05 U3, S-1140).
            ExprKind::Par { body, .. } => self.mark(*body, at, Cond::Late),
            // The conditional positions (§11.3), not those of `if~` / `match~`
            // (W7-06): W7-05 U2 counts the stages of their conditions.
            ExprKind::If { cond, then, else_, tilde } => {
                let inner = if tilde.is_some() { g } else { Cond::Late };
                self.mark(*cond, at, g);
                for x in [Some(*then), *else_].into_iter().flatten() {
                    self.mark(x, at, inner);
                }
            }
            ExprKind::Match { scrutinee, arms, tilde } => {
                let inner = if tilde.is_some() { g } else { Cond::Late };
                self.mark(*scrutinee, at, g);
                for arm in arms {
                    for x in arm.guard.iter().chain([&arm.body]) {
                        self.mark(*x, at, inner);
                    }
                }
            }
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs, rhs, .. } => {
                self.mark(*lhs, at, g);
                self.mark(*rhs, at, Cond::Late);
            }
            _ => {
                for child in ast.sub_exprs(e) {
                    self.mark(child, at, g);
                }
            }
        }
    }

    /// A call at `e` of a function that is not `rt`, with values at `init`
    /// ([`Walked::non_rt`]), evaluated at a stage after `init`: one not
    /// hoisted to `init` (R-17), in a conditional position or the body of a
    /// `par~` (W7-05 U2, U3) or of a type that is not Copy (S-1160), is
    /// E0200.
    fn non_rt_here(&mut self, e: ExprId, at: ClockStage) {
        if at <= ClockStage::Init || !self.non_rt.contains(&e) {
            return;
        }
        let span = self.ast.expr(e).span;
        let stage = match at {
            ClockStage::Block => ClockName::Block.name(),
            ClockStage::SAMPLE => ClockName::Sample.name(),
            s => onsa_diag::internal::bug(Some(span), format!("a read at the stage {s:?}, which W7-09 makes")),
        };
        let d = Feature::NonRtCallAtClock
            .diagnostic(Stage::Flow, span, &[stage])
            .with_found(span.text_in(self.text).to_string());
        Diagnostic::keep_first(&mut self.out.diag, d);
    }
}
