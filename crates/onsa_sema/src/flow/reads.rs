//! The state marking (S-05): the stages at which each local is read
//! (`FlowInfo::read_at`), the stages it evaluates at and those of
//! `sample_tick()` (`FlowInfo::eval_at`, `FlowInfo::time_at`) and the
//! stage at which `sample_rate()` is read,
//! from the clocks of the walk ([`Walked`], the `let`s), which tell what
//! the state keeps ([`FlowInfo::stored`]); and, in the same walk, the
//! subexpressions hoisted to a slower stage, whose parts are read there
//! ([`super::hoist`], §11.3). The lowering reads these and does not walk
//! the body again (R-91 (1), D-15).

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::Ast;

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
    /// `FlowInfo::eval_at`, `FlowInfo::time_at`, `FlowInfo::work` (of the
    /// hoisted fields and the checks), `FlowInfo::late` and `FlowInfo::back`.
    pub(super) eval_at: BTreeSet<ClockStage>,
    pub(super) time_at: BTreeSet<ClockStage>,
    pub(super) work: HashSet<(u32, ClockStage)>,
    pub(super) late: HashSet<ExprId>,
    pub(super) back: HashSet<ExprId>,
    /// The first call (in the order of the file) of a function that is not
    /// `rt` evaluated at a stage after `init` (R-17): E0815 in a
    /// conditional position a condition decided after `init` selects
    /// (§11.5); else E0200, of a type that is not Copy (S-1160) or of
    /// constants only (W9-03).
    pub(super) diag: Option<Diagnostic>,
    /// The hoisted subexpressions in the order of the walk, with their
    /// stages, owners, whether they are guarded and their arms, of which the
    /// plan makes its table.
    pub(super) hoisted: Vec<super::hoist::Marked>,
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
    /// reach (in a branch, in `match~`).
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
    /// The first arguments of the delays, and the bindings a `^name`
    /// chooses (`BodyNames::past`, and of the `match`es marked with no `~`,
    /// S-1249), of [`Marker::back`].
    firsts: HashSet<ExprId>,
    past: HashSet<LocalId>,
    /// The bindings of the arms of the `match~`s marked, the `match~`s whose
    /// arms are chosen at a stage ([`Marker::read_select`]), and the one
    /// whose guards are marked now.
    binding_of: HashMap<LocalId, Bound>,
    selected: HashSet<(ExprId, usize, ClockStage)>,
    guard: Option<ExprId>,
    /// The `match` / `match~` and the arm that bind each binding of an arm
    /// marked ([`Marker::chain`]).
    arm_of: HashMap<LocalId, (ExprId, u32)>,
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

/// Why [`Choose::place`] refused a part of a tick ([`Marker::refuse`]).
enum Why {
    /// A condition decided at this stage selects it.
    Cond(ClockStage),
    NotCopy,
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
/// one with a diagnostic, of the output the body writes at `out` (§11.9: the
/// tick of an output at `sample / N`). A `let` in error is not marked.
pub(super) fn mark_all(
    (a, id): (&Analysis, DefId),
    (ast, text): (&Ast, &str),
    body: &BodyInfo,
    cx: &FlowCx,
    walked: &Walked,
    lets: &[FlowLet],
    out: Clock,
) -> Marked {
    let nodes = cx.node_exprs();
    let [sample_rate, sample_tick] =
        [&cx.sample_rate_calls, &cx.sample_tick_calls].map(|x| x.iter().copied().collect());
    let (sample_rate, sample_tick) = (&sample_rate, &sample_tick);
    let choose = Choose { a, ast, body, clocks: &walked.info, nodes: &nodes, sample_rate, sample_tick };
    let recorded = walked.recorded.iter().enumerate();
    let par_of = recorded.filter(|(_, r)| matches!(r.kind, PlanKind::Par { .. }));
    let par_of = par_of.map(|(i, r)| (r.expr, NodeId(i as u32))).collect();
    let firsts = walked.recorded.iter().filter_map(|r| r.kind.stored()).collect();
    let mut m = Marker {
        ast,
        text,
        body,
        clocks: walked,
        choose,
        partial: walked.diag.is_some(),
        non_rt: &walked.non_rt,
        lets: lets.len(),
        consumer: lets.len(),
        conds: Vec::new(),
        cond_read: HashSet::default(),
        seen: HashSet::default(),
        konst: false,
        par_of,
        pars: Vec::new(),
        firsts,
        past: a.names.get(&id).into_iter().flat_map(|n| n.past.iter().map(|b| LocalId(b.0))).collect(),
        binding_of: HashMap::default(),
        selected: HashSet::default(),
        guard: None,
        arm_of: HashMap::default(),
        out: Marked {
            read_at: HashMap::default(),
            bound_at: HashMap::default(),
            sample_rate_at: None,
            eval_at: BTreeSet::new(),
            time_at: BTreeSet::new(),
            work: HashSet::default(),
            late: HashSet::default(),
            back: HashSet::default(),
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
    if let Some(e) = cx.output {
        m.consumer = lets.len();
        m.mark(e, read_stage(out).unwrap_or(ClockStage::SAMPLE), Cond::None);
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
    let (out, outer) = (info.lets.len(), info.outer());
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
        let place = if self.konst { Place::Here } else { self.place(e, at, g) };
        let at = match place {
            Place::Hoist(s) | Place::Field(s) | Place::Arm(s) => {
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
                let guarded = g != Cond::None && matches!(place, Place::Hoist(_));
                let arms = if matches!(place, Place::Arm(_)) { self.chain(e, s) } else { Vec::new() };
                self.out.hoisted.push((e, s, owner, guarded, arms));
                self.out.work.insert((self.consumer as u32, s));
                self.mark_late(e);
                if guarded {
                    self.read_conds(s);
                }
                if s.stored_slower_than(at) {
                    self.no_default(e, s, SlowField::Part);
                }
                s
            }
            Place::Check(_) | Place::Const => {
                self.out.const_conds.insert(e, g);
                if let Place::Check(s) = place {
                    self.out.checks.insert(e, s);
                    self.out.work.insert((self.consumer as u32, s));
                    self.mark_late(e);
                    self.read_conds(s);
                    self.konst_parts(e, s, g);
                }
                // W9-03 evaluates it once; until then, also where it is read.
                return self.konst_parts(e, at, g);
            }
            Place::Here => at,
            Place::Refuse(s) => {
                // The first that refuses it: the join of two may be decided at neither's.
                let of = |&(c, _): &(ExprId, Cond)| self.choose.cond_stage(c, at);
                let c = self.conds.iter().map(of).find(|c| !c.admits(s)).unwrap_or(g);
                return self.refuse(e, s, Why::Cond(c.decided(at)));
            }
            Place::NotCopy(s) => return self.refuse(e, s, Why::NotCopy),
        };
        self.out.eval_at.insert(at);
        let ast = self.ast;
        let expr = ast.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(&Target::Local(id)) = self.body.targets.get(&e) {
                    self.out.read_at.entry(id).or_default().insert(at);
                    self.read_select(id, at);
                    let own = self.clocks.info.own_stage(id).filter(|s| s.stored_slower_than(at));
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
                // A modifier: its chain is its head's node (§11.9).
                if let Some(&Some(receiver)) = self.choose.nodes.get(&e) {
                    self.mark(receiver, at, g);
                } else if self.choose.nodes.contains_key(&e) {
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
                        // The `init` of a delay in the first argument of another.
                        if r.at == Clock::Init && self.back(r.expr) {
                            self.out.late.insert(r.expr);
                        }
                        if let Some(s) = r.stage.or_else(|| read_stage(r.at)) {
                            self.mark(r.expr, s, g);
                        }
                    }
                } else if self.choose.sample_rate.contains(&e) {
                    self.out.sample_rate_at = Some(self.out.sample_rate_at.map_or(at, |s| s.max(at)));
                } else if self.choose.sample_tick.contains(&e) {
                    self.out.time_at.insert(at);
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
            // The bindings of the arms of a `match` / `match~`, then its positions.
            ExprKind::Match { scrutinee, arms, tilde } => {
                if arms.iter().filter_map(|a| a.guard).chain([*scrutinee]).any(|x| self.back(x)) {
                    let (body, past) = (self.body, &mut self.past);
                    let mut bind = |q, _: &_| past.extend(body.pat_locals.get(&q));
                    arms.iter().for_each(|a| crate::pat::each_bind(ast, a.pat, true, &mut bind));
                }
                let arms_of = self.clocks.tilde.get(&e).filter(|_| tilde.is_some());
                if arms_of.is_some_and(|t| t.arms.iter().flatten().any(|b| self.past.contains(b))) {
                    self.out.late.insert(e);
                }
                let depth = self.conds.len();
                for (arm, bound) in arms_of.into_iter().flat_map(|t| t.arms.iter().enumerate()) {
                    let b = Bound { m: e, arm, at, g, depth };
                    self.binding_of.extend(bound.iter().map(|&l| (l, b)));
                }
                for (i, a) in arms.iter().enumerate() {
                    let (body, arm_of) = (self.body, &mut self.arm_of);
                    let mut bind = |q, _: &_| arm_of.extend(body.pat_locals.get(&q).map(|&l| (l, (e, i as u32))));
                    crate::pat::each_bind(ast, a.pat, true, &mut bind);
                }
                self.mark_positions(e, at, g);
            }
            _ => self.mark_positions(e, at, g),
        }
    }

    /// The parts of `e`, read at `at` under `g`, in their positions
    /// ([`super::positions`], §11.3): a condition marked under the ones
    /// before it (a guard of the `match` `e` by [`Self::mark_guard`]), and
    /// entered; a branch and the right of `&&` / `||` under the conditions
    /// entered; after the conditions, a branch of `if~` / `match~` (S-1094)
    /// under no more than `g`, once they are marked. A walk of the nodes:
    /// the later `if` of a chain is a branch of the one before it.
    fn mark_positions(&mut self, e: ExprId, at: ClockStage, g: Cond) {
        let (depth, mut inner, mut after) = (self.conds.len(), g, Vec::new());
        for (x, p) in super::positions(self.ast, e).of_node() {
            match p {
                Pos::Always if self.conds.len() == depth => self.mark(x, at, g),
                Pos::Always => after.push(x),
                Pos::Cond | Pos::Choose => {
                    match self.ast.expr(e).kind {
                        ExprKind::Match { .. } if p == Pos::Choose => self.mark_guard(e, x, at, inner),
                        _ => self.mark(x, at, inner),
                    }
                    inner = self.enter(x, at, inner);
                }
                Pos::Branch { .. } | Pos::Right | Pos::Link => self.mark(x, at, inner),
            }
        }
        self.conds.truncate(depth);
        for x in after {
            self.mark(x, at, g);
        }
    }

    /// [`Choose::place`], but a field read of a binding with a value only
    /// where its arm is taken (of a `match`, or of a `match~` in a guard) is
    /// [`Place::Arm`], whatever the conditions on the path (§11.3, S-1247).
    fn place(&mut self, e: ExprId, at: ClockStage, g: Cond) -> Place {
        match self.choose.place(e, at, g) {
            Place::Field(s) if self.choose.of_name(e).is_some_and(|x| self.in_arm(x)) => Place::Arm(s),
            place => place,
        }
    }

    /// The arms of the field read `e` of a binding of an arm (`Hoist::arms`),
    /// from its root up the scrutinees while they are such reads, the
    /// outermost first; each scrutinee read at `s`, the stage of its field,
    /// under no condition (its patterns alone guard it).
    fn chain(&mut self, e: ExprId, s: ClockStage) -> Vec<(ExprId, u32)> {
        let (mut arms, mut root) = (Vec::new(), self.choose.of_name(e));
        while let Some(x) = root.filter(|&x| self.in_arm(x))
            && let Some(Target::Local(b)) = self.body.targets.get(&x)
            && let Some(&(m, i)) = self.arm_of.get(b)
            && let ExprKind::Match { scrutinee, .. } = &self.ast.expr(m).kind
        {
            arms.push((m, i));
            let conds = std::mem::take(&mut self.conds);
            self.mark(*scrutinee, s, Cond::None);
            self.conds = conds;
            root = self.choose.of_name(*scrutinee);
        }
        arms.reverse();
        arms
    }

    /// Whether the name `x` is a binding that no place holds where it is read.
    fn in_arm(&self, x: ExprId) -> bool {
        let Some(&Target::Local(b)) = self.body.targets.get(&x) else { return false };
        let body = |b: &Bound| match &self.ast.expr(b.m).kind {
            ExprKind::Match { arms, .. } => self.ast.expr(arms[b.arm].body).span.contains(self.ast.expr(x).span.start),
            _ => false,
        };
        self.body.locals[b.0 as usize].kind == LocalKind::MatchBind && !self.binding_of.get(&b).is_some_and(body)
    }

    /// Whether `e` reads a `^name`, or a binding one chooses, where it is
    /// evaluated (§11.2): not in the first argument of a delay in it, read
    /// at the end of its stage.
    fn back(&self, e: ExprId) -> bool {
        let mut todo = vec![e];
        while let Some(x) = todo.pop() {
            let local = match self.body.targets.get(&x) {
                Some(Target::Local(id)) => self.past.contains(id),
                _ => false,
            };
            if local || matches!(self.ast.expr(x).kind, ExprKind::Feedback(_)) {
                return true;
            }
            todo.extend(self.ast.sub_exprs(x).into_iter().filter(|y| !self.firsts.contains(y)));
        }
        false
    }

    /// The part `e` evaluated at its stage, of the end of it
    /// ([`FlowInfo::late`]) if it ([`FlowInfo::back`]) or a condition on its
    /// path reads a `^name` or a binding one chooses.
    fn mark_late(&mut self, e: ExprId) {
        let back = self.back(e);
        self.out.back.extend(back.then_some(e));
        if back || self.conds.iter().any(|c| self.back(c.0)) {
            self.out.late.insert(e);
        }
    }

    /// The condition `c` read at `at` under `g`, entered: the conditions
    /// under it, of the stage it is decided at ([`Choose::cond_stage`]).
    fn enter(&mut self, c: ExprId, at: ClockStage, g: Cond) -> Cond {
        self.conds.push((c, g));
        g.join(self.choose.cond_stage(c, at))
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
    /// [`Place::Refuse`] (S-1158 (c)); E0200 of [`Place::NotCopy`] (S-1195).
    fn refuse(&mut self, e: ExprId, s: ClockStage, why: Why) {
        let span = self.ast.expr(e).span;
        let d = match why {
            Why::NotCopy => Feature::NonCopyTickParts.diagnostic(Stage::Flow, span, &[&s.shown(span)]),
            Why::Cond(c) => {
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
