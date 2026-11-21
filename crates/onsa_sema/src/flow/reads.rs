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
use crate::body::LocalKind;
use crate::names::body::Binding;
use crate::signal::SlowField;

#[cfg(test)]
mod tests;

/// What the marking gives.
pub(super) struct Marked {
    pub(super) read_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    /// `FlowInfo::bound_at`.
    pub(super) bound_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    pub(super) sample_rate_at: Option<ClockStage>,
    /// The first call (in the order of the file) of a function that is not
    /// `rt` evaluated at a stage after `init` (R-17): E0815 in a
    /// conditional position a condition decided after `init` selects
    /// (§11.5); else E0200, of a type that is not Copy (S-1160) or of
    /// constants only (W9-03).
    pub(super) diag: Option<Diagnostic>,
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
    /// The walk had a diagnostic or did not go into a chain of modifiers:
    /// it did not record the nodes it did not reach (in a branch, in
    /// `match~`, in the chain).
    partial: bool,
    non_rt: &'a HashMap<ExprId, bool>,
    /// The number of the `let`s, the `consumer` of the output.
    lets: usize,
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
    /// The bindings of the arms of the `match~`s marked, the `match~`s whose
    /// arms are chosen at a stage ([`Marker::read_select`]), and the one
    /// whose guards are marked now.
    binding_of: HashMap<LocalId, Bound>,
    selected: HashSet<(ExprId, usize, ClockStage)>,
    guard: Option<ExprId>,
    out: Marked,
}

/// The arm `arm` of the `match~` `m` marked at `at` under `g`, with `depth`
/// conditions on its path.
#[derive(Debug, Clone, Copy)]
struct Bound {
    m: ExprId,
    arm: usize,
    at: ClockStage,
    g: Cond,
    depth: usize,
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
        partial: walked.diag.is_some() || walked.skipped,
        non_rt: &walked.non_rt,
        lets: lets.len(),
        consumer: lets.len(),
        conds: Vec::new(),
        cond_read: HashSet::default(),
        seen: HashSet::default(),
        konst: false,
        par_of,
        pars: Vec::new(),
        binding_of: HashMap::default(),
        selected: HashSet::default(),
        guard: None,
        out: Marked {
            read_at: HashMap::default(),
            bound_at: HashMap::default(),
            sample_rate_at: None,
            diag: None,
            hoisted: Vec::new(),
            checks: HashMap::default(),
            const_conds: HashMap::default(),
        },
    };
    // The `let`s and the output are evaluated at their stages whether and
    // where they are read (§11.3, S-1093, S-1196): roots under no condition.
    for (k, l) in lets.iter().enumerate().filter(|(_, l)| l.stage != Clock::Const) {
        if let Some(s) = read_stage(l.stage) {
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
    for (k, l) in lets.iter().enumerate().rev().filter(|(_, l)| l.stage == Clock::Const) {
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

/// The locals of the `let`s the initializer of each `let` reads (by its
/// index; the last, the output), `^y` too, of the edges of the plan
/// ([`FlowInfo::edges`]): a read by a node is of the outermost `let` or the
/// output that holds it. One pass of the nodes (a `par~` comes before the
/// nodes of its body) and one of the edges.
pub(super) fn deps(info: &FlowInfo, let_of_local: &HashMap<LocalId, usize>) -> Vec<HashSet<LocalId>> {
    let out = info.lets.len();
    let mut outer: Vec<usize> = Vec::with_capacity(info.nodes.len());
    for n in &info.nodes {
        let k = match n.owner {
            Owner::Let(k) => k as usize,
            Owner::Output => out,
            Owner::Par(p) => outer.get(p.0 as usize).copied().unwrap_or(usize::MAX),
        };
        if k > out {
            onsa_diag::internal::bug(Some(n.span), "a node of no `let` and not of the output");
        }
        outer.push(k);
    }
    let mut deps = vec![HashSet::default(); out + 1];
    for e in &info.edges {
        let Vertex::Local(v) = e.from else { continue };
        let k = match e.to {
            _ if !let_of_local.contains_key(&v) => continue,
            Vertex::Let(k) => k as usize,
            Vertex::Output => out,
            Vertex::Node(id) => outer.get(id.0 as usize).copied().unwrap_or(usize::MAX),
            Vertex::Local(_) => usize::MAX,
        };
        let Some(d) = deps.get_mut(k) else {
            onsa_diag::internal::bug(None, format!("an edge read by no `let` and not by the output: {e:?}"))
        };
        d.insert(v);
    }
    deps
}

/// The locals of the `let`s reached from the output and from the `let`s
/// that bind no name (§5.1, S-727), through the reads `deps` ([`deps`]):
/// each `let` is visited once, so the walk is linear in the `let`s and their
/// reads, and ends.
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
pub(super) fn unused(a: &Analysis, id: DefId, ast: &Ast, info: &FlowInfo, cx: &FlowCx) -> Option<Diagnostic> {
    let names = a.names.get(&id).filter(|n| n.complete)?;
    let deps = &deps(info, &cx.let_of_local);
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
                    (None, k) if k < self.lets => Owner::Let(k as u32),
                    (None, _) => Owner::Output,
                };
                self.out.hoisted.push((e, s, owner, g != Cond::None));
                if g != Cond::None {
                    self.read_conds(s);
                }
                if s.tick_slower_than(at) {
                    self.no_default(e, s, SlowField::Part);
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
            // The condition is decided at `block` or at `at`.
            Place::Refuse(s) => return self.refuse(e, s, Some(if g == Cond::Block { ClockStage::Block } else { at })),
            Place::NotCopy(s) => return self.refuse(e, s, None),
        };
        let ast = self.ast;
        let expr = ast.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(&Target::Local(id)) = self.body.targets.get(&e) {
                    self.out.read_at.entry(id).or_default().insert(at);
                    self.read_select(id, at);
                    let own = self.clocks.info.own_stage(id).filter(|s| s.tick_slower_than(at));
                    if let Some(s) = own.filter(|_| self.body.locals[id.0 as usize].kind != LocalKind::MatchBind) {
                        let name = expr.span.text_in(self.text);
                        self.no_default(e, s, SlowField::Name(name));
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
            // `if~` (§11.3, S-1094): a later condition of its chain under
            // the ones before it, its branches under no more than it.
            ExprKind::If { tilde: Some(_), .. } => {
                let chain = super::branching::chain(ast, e);
                let (depth, mut inner) = (self.conds.len(), g);
                for l in &chain.links {
                    self.mark(l.cond, at, inner);
                    inner = self.enter(l.cond, at, inner);
                }
                self.conds.truncate(depth);
                for x in chain.links.iter().map(|l| l.then).chain(chain.last) {
                    self.mark(x, at, g);
                }
            }
            // The conditional positions (§11.3) under the conditions that
            // select them.
            ExprKind::If { cond, then, else_, tilde: None } => {
                self.mark(*cond, at, g);
                let inner = self.enter(*cond, at, g);
                for x in [Some(*then), *else_].into_iter().flatten() {
                    self.mark(x, at, inner);
                }
                self.conds.pop();
            }
            // A guard under the scrutinee and the guards before it; the arm
            // bodies of `match~` (S-1094) under no more than it.
            ExprKind::Match { scrutinee, arms, tilde } => {
                let depth = self.conds.len();
                let arms_of = self.clocks.tilde.get(&e).filter(|_| tilde.is_some());
                for (arm, bound) in arms_of.into_iter().flat_map(|t| t.arms.iter().enumerate()) {
                    let b = Bound { m: e, arm, at, g, depth };
                    self.binding_of.extend(bound.iter().map(|&l| (l, b)));
                }
                self.mark(*scrutinee, at, g);
                let mut inner = self.enter(*scrutinee, at, g);
                for arm in arms {
                    if let Some(x) = arm.guard {
                        self.mark_guard(e, x, at, inner);
                        inner = self.enter(x, at, inner);
                    }
                    if tilde.is_none() {
                        self.mark(arm.body, at, inner);
                    }
                }
                self.conds.truncate(depth);
                for arm in arms.iter().filter(|_| tilde.is_some()) {
                    self.mark(arm.body, at, g);
                }
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

    /// The guard `x` of the `match` `m`, marked at `at` under `g`: a binding
    /// of `m` read in it is of the choice (S-1131).
    fn mark_guard(&mut self, m: ExprId, x: ExprId, at: ClockStage, g: Cond) {
        let outer = self.guard.replace(m);
        self.mark(x, at, g);
        self.guard = outer;
    }

    /// The binding `b` of an arm of `match~` read at `s` (S-1131): in its
    /// guard, the value of the pattern, nothing more; in a body, that arm is
    /// chosen at `s` too (`bound_at`), so the scrutinee and the guards to it
    /// are read there, under the conditions on the path of the `match~`;
    /// once each, and not at the stage of the `match~`, which reads them.
    /// Of a binding slower than `s`, nothing: the walk reports it (E0815).
    fn read_select(&mut self, b: LocalId, s: ClockStage) {
        let Some(&Bound { m, arm, at, g, depth }) = self.binding_of.get(&b) else { return };
        if self.guard == Some(m) {
            return;
        }
        self.out.bound_at.entry(b).or_default().insert(s);
        let ready = self.clocks.info.locals.get(&b).and_then(|&c| read_stage(c)).is_some_and(|c| c <= s);
        if s == at || !ready || !self.selected.insert((m, arm, s)) {
            return;
        }
        let ExprKind::Match { scrutinee, arms, .. } = &self.ast.expr(m).kind else { return };
        let rest = self.conds.split_off(depth);
        self.mark(*scrutinee, s, g);
        let mut inner = self.enter(*scrutinee, s, g);
        for x in arms[..=arm].iter().filter_map(|a| a.guard) {
            self.mark_guard(m, x, s, inner);
            inner = self.enter(x, s, inner);
        }
        self.conds.truncate(depth);
        self.conds.extend(rest);
    }

    /// The part `e` of the tick `s` that `place` refused, at it: E0815 of
    /// [`Place::Refuse`] under a condition decided at `cond` (S-1158 (c));
    /// E0200 of [`Place::NotCopy`] (S-1195).
    fn refuse(&mut self, e: ExprId, s: ClockStage, cond: Option<ClockStage>) {
        let span = self.ast.expr(e).span;
        let d = match cond {
            None => Feature::NonCopyTickParts.diagnostic(Stage::Flow, span, &[&s.shown(span)]),
            Some(c) => {
                let msg = format!(
                    "this value of the clock `{}` is computed at its ticks, and a condition decided at `{}` selects this place; bind it with a `let` before the condition to compute it at each tick, or write `at` on the names it reads to compute it where it is reached (§11.3)",
                    s.shown(span),
                    c.shown(span)
                );
                Diagnostic::new(Stage::Flow, Code::E0815, span, msg)
            }
        };
        Diagnostic::keep_first(&mut self.out.diag, d.with_found(span.text_in(self.text)));
    }

    /// The E0816 at `e` of a value of the tick `s` a faster stage reads from
    /// its field, which starts at `T.default()` (§11.3, S-1186 #14), of a
    /// type that does not satisfy `Default`.
    fn no_default(&mut self, e: ExprId, s: ClockStage, field: SlowField) {
        let Some(&ty) = self.body.expr_types.get(&e) else { return };
        let span = self.ast.expr(e).span;
        if let Some(d) = crate::signal::slow_field_default(self.choose.a, ty, span, &s.shown(span), field) {
            Diagnostic::keep_first(&mut self.out.diag, d.with_found(span.text_in(self.text)));
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
            // SPEC-GAP(S-1160): one whose result is not Copy is not hoisted,
            // and is E0200 (§11.3, §11.5).
            Feature::NonRtCallAtClock.diagnostic(Stage::Flow, span, &[&at.shown(span)])
        };
        Diagnostic::keep_first(&mut self.out.diag, d.with_found(found));
    }
}
