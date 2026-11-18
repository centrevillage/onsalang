//! The state marking (S-05): the stages at which each local is read
//! (`FlowInfo::read_at`), the `let`s read at a later stage than their own,
//! and the stage at which `sample_rate()` is read, from the clocks of the
//! walk ([`Walked`], the `let`s). The lowering reads these and does not
//! walk the body again (R-91 (1), D-15).

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::Ast;

use super::clocks::Walked;
use super::*;

/// What the marking gives.
pub(super) struct Marked {
    pub(super) read_at: HashMap<LocalId, BTreeSet<ClockStage>>,
    pub(super) sample_rate_at: Option<ClockStage>,
    /// The first call (in the order of the file) of a function that is not
    /// `rt` read at a stage after `init` (E0200, R-17, W7-05).
    pub(super) diag: Option<Diagnostic>,
}

struct Marker<'a> {
    ast: &'a Ast,
    text: &'a str,
    body: &'a BodyInfo,
    clocks: &'a Walked,
    /// The walk had a diagnostic: it did not record the nodes it did not
    /// reach (in a branch, in `if~` / `match~`).
    partial: bool,
    non_rt: &'a HashSet<ExprId>,
    node_calls: HashSet<ExprId>,
    sample_rate: HashSet<ExprId>,
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

/// The stages each local is read at, the `let`s read at a later stage than
/// their own (S-05, their `state`), and the stage at which `sample_rate()`
/// is read, in the module of `ast` and `text`, from the walk `walked`, also
/// one with a diagnostic. A `let` in error is not marked.
pub(super) fn mark_all(
    ast: &Ast,
    text: &str,
    body: &BodyInfo,
    cx: &FlowCx,
    walked: &Walked,
    lets: &mut [FlowLet],
) -> Marked {
    let mut m = Marker {
        ast,
        text,
        body,
        clocks: walked,
        partial: walked.diag.is_some(),
        non_rt: &walked.non_rt,
        node_calls: cx.calls.iter().map(|c| c.expr).collect(),
        sample_rate: cx.sample_rate_calls.iter().copied().collect(),
        out: Marked { read_at: HashMap::default(), sample_rate_at: None, diag: None },
    };
    for l in lets.iter().filter(|l| l.clock != Clock::Const) {
        if let Some(s) = read_stage(l.clock) {
            m.mark(l.init, s);
        }
    }
    if let Some(out) = cx.output {
        m.mark(out, ClockStage::SAMPLE);
    }
    // A constant `let` is defined in each phase that reads it, and its
    // initializer read there (§11.3, R-488): from the last, so that one
    // read by a later constant `let` has the stages of that one.
    for l in lets.iter().rev().filter(|l| l.clock == Clock::Const) {
        let reads = l.locals.iter().filter_map(|id| m.out.read_at.get(id));
        let mut stages: BTreeSet<ClockStage> = reads.flatten().copied().collect();
        if stages.is_empty() {
            stages.insert(ClockStage::Init);
        }
        for s in stages {
            m.mark(l.init, s);
        }
    }
    let read = &m.out.read_at;
    for l in lets.iter_mut() {
        let last = |id: &LocalId| read.get(id).and_then(|s| s.last()).copied();
        l.state = l.clock.stage().is_some_and(|own| l.locals.iter().any(|id| last(id).is_some_and(|s| s > own)));
    }
    m.out
}

impl Marker<'_> {
    fn mark(&mut self, e: ExprId, at: ClockStage) {
        let ast = self.ast;
        let expr = ast.expr(e);
        match &expr.kind {
            ExprKind::Path(_) | ExprKind::Feedback(_) | ExprKind::Field { .. } => {
                if let Some(Target::Local(id)) = self.body.targets.get(&e) {
                    self.out.read_at.entry(*id).or_default().insert(at);
                }
                if let ExprKind::Field { base, .. } = &expr.kind
                    && !self.body.targets.contains_key(&e)
                {
                    self.mark(*base, at);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if self.node_calls.contains(&e) {
                    let clocks = self.clocks;
                    let Some(&k) = clocks.node_of.get(&e) else {
                        if self.partial {
                            return;
                        }
                        onsa_diag::internal::bug(Some(expr.span), "a node the walk of the clocks did not reach")
                    };
                    for r in &clocks.nodes[k].args {
                        if let Some(s) = read_stage(r.at) {
                            self.mark(r.expr, s);
                        }
                    }
                } else if self.sample_rate.contains(&e) {
                    self.out.sample_rate_at = Some(self.out.sample_rate_at.map_or(at, |s| s.max(at)));
                } else {
                    self.non_rt_here(e, at);
                    if let Some(base) = crate::names::body::receiver(ast, *callee)
                        && self.body.expr_types.contains_key(&base)
                    {
                        self.mark(base, at);
                    }
                    for x in args {
                        self.mark(x.expr, at);
                    }
                }
            }
            ExprKind::Par { body, .. } => self.mark(*body, at),
            _ => {
                for child in ast.sub_exprs(e) {
                    self.mark(child, at);
                }
            }
        }
    }

    /// A call at `e` of a function that is not `rt`, with values at `init`
    /// ([`Walked::non_rt`]), read at a stage after `init`: E0200 until
    /// hoisting computes it at `init` (R-17, W7-05).
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
        let d = Feature::NonRtCallAtClock.diagnostic(Stage::Flow, span, &[stage]).with_found(found(self.text, span));
        keep_first(&mut self.out.diag, d);
    }
}
