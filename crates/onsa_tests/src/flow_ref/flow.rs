//! One instance of a flow (§11.2, §11.3, §11.6): the clock of each `let`, and the two entries `init` and `process`.
//! The clock of a `let` says when its value is made again: a `let` of a constant or of `init` once, at `init`; of `block`
//! once for each `process` call, a call of 0 frames too; of `sample` for each frame. A `let` of a faster clock reads the
//! latest value of a slower one. The `let`s of a stage run in the order they are written (§11.2), the stages of a frame
//! in the order of the clocks, and `e at k` has the clock `k` but not another value (§11.3; the name under it is read in
//! its own stage, and a computed `e` under `at` is E0200 today). The delays (`state.rs`) are in the `sample` stage, and
//! the second phase of each frame stores what they save, after the stage and before `tick` goes up. The instances of
//! flows, `reset` and `render` come with the units after this one: they are `Unavailable` here. A panic of a value of the clock
//! of a constant is E0419 in the spec (compile time, §11.3): the evaluator makes it at `init` and gives the panic of
//! `init`; the entry of the comparison (W7-19) reads it as an error of the compile time.

use std::collections::HashMap;

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::flow_names::FlowBuiltin;
use onsa_sema::{DefId, LocalId, Target};
use onsa_syntax::ast::{CallKind, ExprId, ExprKind, PatId, StmtKind};

use super::expr::{Frame, Stop};
use super::host::FnHost;
use super::scalar::Fault;
use super::sema_view::{Body, Called, Stage, View, clock_stage, input_stage, output_stage};
use super::state::{InstState, Run};
use super::value::Value;

/// When a value is made: once for good (a constant), at `init`, for each `process` call (`block`), for each frame.
/// The order is that of §11.3 (a constant < `init` < `block` < `sample`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Clock {
    Const,
    Init,
    Block,
    Sample,
}

/// The clock of an expression of two operands: the faster, as §11.3 has it. `None` for two that do not join (the event
/// clocks of two inputs, W7-17); there is always one today.
pub fn join(a: Clock, b: Clock) -> Option<Clock> {
    Some(a.max(b))
}

impl From<Stage> for Clock {
    fn from(s: Stage) -> Clock {
        match s {
            Stage::Init => Clock::Init,
            Stage::Block => Clock::Block,
            Stage::Sample => Clock::Sample,
        }
    }
}

impl Clock {
    /// Is a value of this clock made in `stage` of a call (the one place that says which stage runs which clock)?
    pub fn runs_at(self, stage: Stage) -> bool {
        match stage {
            Stage::Init => self <= Clock::Init,
            Stage::Block => self == Clock::Block,
            Stage::Sample => self == Clock::Sample,
        }
    }
}

/// The time an instance runs in: its sample rate, and the frames it has run since `init` (the counter of §11.9, which
/// goes round at 2^32).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ctx {
    pub sample_rate: f32,
    pub tick: u32,
}

/// The clock of `e` (the stage it is made in): the fastest of the names in it. A name has the clock its local has so far
/// (`known`); one that `known` has not must be bound inside `root`, the expression being clocked (an arm of a `match`),
/// and has no clock of its own: bound anywhere else is an internal error. A constant has none, a delay or an instance
/// ticks with the `sample` of the body (§11.4: the first argument of a delay is at `sample`, or `^name`, which has no clock of
/// its own and is read as `sample`, §11.3; a constant or a `block` one is E0813; the other clocks of a delay come with W7-09
/// and W7-17), and `e at k` has the clock `k` (§11.3).
pub(super) fn clock_of(body: &Body, known: &HashMap<LocalId, Clock>, root: ExprId, e: ExprId) -> Result<Clock, Fault> {
    match &body.ast.expr(e).kind {
        ExprKind::Call { callee, kind, .. } if matches!(kind, CallKind::Flow) || body.time_call(e) => {
            Ok(match body.called(*callee)? {
                Called::Builtin(FlowBuiltin::SampleRate) => Clock::Init,
                Called::Flow(def) => output_stage(body.view.flow(def)?).into(),
                Called::Builtin(_) => Clock::Sample,
            })
        }
        ExprKind::At { expr, clock } => {
            clock_of(body, known, root, *expr)?;
            clock_stage(&clock.name.name).map(Clock::from).ok_or(Fault::Unavailable("a clock the evaluator has not"))
        }
        ExprKind::Path(_) | ExprKind::Field { .. } if body.names(e) => match body.target(e)? {
            Target::Local(l) => match known.get(l) {
                Some(c) => Ok(*c),
                None if body.bound_within(*l, root) => Ok(Clock::Const),
                None => Err(Fault::Internal("a local with no clock")),
            },
            _ => Ok(Clock::Const),
        },
        _ => body.ast.sub_exprs(e).into_iter().try_fold(Clock::Const, |c, x| {
            join(c, clock_of(body, known, root, x)?).ok_or(Fault::Internal("clocks that do not join"))
        }),
    }
}

/// A `let` of the body, or (no pattern) its last expression, the output; and when its value is made.
#[derive(Debug)]
struct Step {
    pat: Option<PatId>,
    init: ExprId,
    clock: Clock,
}

/// What an instance of a flow keeps between its entries, with no lifetime: one a flow calls is kept whole in the state of
/// its caller (`InstState::children`), the outermost in an [`Instance`]; the entry `enter` is the same.
#[derive(Debug)]
pub struct Inst {
    pub(super) def: DefId,
    steps: Vec<Step>,
    locals: HashMap<LocalId, Value>,
    pub(super) out: Value,
    pub(super) state: InstState,
}

/// One instance of a flow, the outermost: the time it runs in is its own, and the instances it calls read it.
pub struct Instance<'a> {
    body: Body<'a>,
    decl: &'a FlowDef,
    me: Inst,
    /// The time the instance runs in: `sample_tick()` reads it, and `reset` makes it 0.
    pub ctx: Ctx,
}

/// The inputs of `decl` at `stage` and the `names` given: an input left out, one added and one of another clock are
/// internal errors (§11.6 decides the number), a call of 0 frames too.
fn check<'n>(at: Span, decl: &FlowDef, stage: Stage, names: impl Iterator<Item = &'n str> + Clone) -> Result<(), Stop> {
    let wrong = |what| Stop { fault: Fault::Internal(what), at };
    let mine = decl.inputs.iter().filter(|i| input_stage(i) == stage);
    if names.clone().count() != mine.clone().count() {
        return Err(wrong("the inputs given are not the inputs of the clock"));
    }
    match mine.clone().all(|i| names.clone().any(|n| n == i.name)) {
        true => Ok(()),
        false => Err(wrong("an input that was not given")),
    }
}

/// The inputs of `decl` that are at `stage`, bound to their values in `given` by name (checked by [`check`]).
fn give<V: std::borrow::Borrow<Value>>(
    f: &mut Frame,
    decl: &FlowDef,
    stage: Stage,
    given: &[(&str, V)],
) -> Result<(), Stop> {
    let at = f.body.ast.expr(decl.body).span;
    check(at, decl, stage, given.iter().map(|(n, _)| *n))?;
    let wrong = |what| Stop { fault: Fault::Internal(what), at };
    for i in decl.inputs.iter().filter(|i| input_stage(i) == stage) {
        let (_, v) = given.iter().find(|(n, _)| *n == i.name).ok_or(wrong("an input that was not given"))?;
        f.locals.insert(f.body.input(&i.name).ok_or(wrong("an input with no local"))?, v.borrow().clone());
    }
    Ok(())
}

/// The steps the clocks of `at` run, in the order they are written (the output is a step too, the last).
// SPEC-GAP(S-1093): a `let` and the output expression of a stage are evaluated whether or not a value is read from
// them (so one that panics does, in a branch not taken too, and the output of `block` or `init` in a call of 0 frames
// too); the other reading evaluates them where they are used.
fn stage(f: &mut Frame, steps: &[Step], out: &mut Value, at: Stage) -> Result<(), Stop> {
    for s in steps.iter().filter(|s| s.clock.runs_at(at)) {
        match s.pat {
            Some(pat) => f.bind(pat, s.init)?,
            None => *out = f.eval(s.init)?,
        }
    }
    Ok(())
}

/// One entry of `inst` in its frame `f` (the time is `f.run.ctx`): the inputs of the stage `at` (`given`, by name), its
/// `let`s, then what the stage has besides: at `init` the nodes (the delays, the instances it calls), at `block` the
/// `block` stage of those instances (§11.3, a call of 0 frames too), for a frame the second phase of the delays (§11.4).
pub(super) fn enter<V: std::borrow::Borrow<Value>>(
    f: &mut Frame,
    inst: &mut Inst,
    decl: &FlowDef,
    at: Stage,
    given: &[(&str, V)],
) -> Result<(), Stop> {
    give(f, decl, at, given)?;
    stage(f, &inst.steps, &mut inst.out, at)?;
    match at {
        Stage::Init => f.make_cells(&inst.steps.iter().map(|s| s.init).collect::<Vec<_>>()),
        Stage::Block => f.block_children(),
        Stage::Sample => f.commit(f.body.ast.expr(decl.body).span),
    }
}

impl Inst {
    /// The plan of the flow `def`: the clock of each `let` and of the output (§11.2), with its body and declaration.
    pub(super) fn plan<'a>(view: View<'a>, def: DefId) -> Result<(Inst, Body<'a>, &'a FlowDef), Stop> {
        let unavailable = |fault| Stop { fault, at: view.name_span(def) };
        let (body, decl) = (view.body(def).map_err(unavailable)?, view.flow(def).map_err(unavailable)?);
        let wrong = |e, what| Stop { fault: Fault::Internal(what), at: body.ast.expr(e).span };
        let ExprKind::Block(b) = &body.ast.expr(decl.body).kind else { return Err(wrong(decl.body, "a body")) };
        let tail = b.tail.ok_or(wrong(decl.body, "a flow with no output expression"))?;
        let mut known = HashMap::new();
        for i in &decl.inputs {
            known.insert(body.input(&i.name).ok_or(wrong(decl.body, "an input with no local"))?, input_stage(i).into());
        }
        let mut steps = Vec::new();
        for s in &b.stmts {
            let StmtKind::Let { pat, init, .. } = &body.ast.stmt(*s).kind else {
                return Err(wrong(decl.body, "a statement"));
            };
            let at = |fault| Stop { fault, at: body.ast.expr(*init).span };
            let clock = clock_of(&body, &known, *init, *init).map_err(at)?;
            // SPEC-GAP(S-1119): the locals the pattern binds (a `let` taken apart) have the clock of the whole right
            // side, as the interpreter has it; the other reading gives each the clock of its own element.
            for l in body.pat_locals(*pat).map_err(at)? {
                known.insert(l, clock);
            }
            steps.push(Step { pat: Some(*pat), init: *init, clock });
        }
        let clock =
            clock_of(&body, &known, tail, tail).map_err(|fault| Stop { fault, at: body.ast.expr(tail).span })?;
        steps.push(Step { pat: None, init: tail, clock });
        Ok((Inst { def, steps, locals: HashMap::new(), out: Value::Unit, state: InstState::default() }, body, decl))
    }

    /// The frame of an evaluation, given the locals and the state (`keep` takes them back), the time and the places held.
    pub(super) fn frame<'b>(
        &mut self,
        body: Body<'b>,
        ctx: Ctx,
        used: usize,
        host: Option<&'b mut dyn FnHost>,
    ) -> Frame<'b> {
        let mut f = Frame::new(body);
        f.locals = std::mem::take(&mut self.locals);
        f.run = Some(Run::new(std::mem::take(&mut self.state), ctx, used));
        f.host = host;
        f
    }

    /// What an evaluation leaves: the latest values of the locals and the state, taken back from its frame.
    pub(super) fn keep(&mut self, f: Frame, at: Span) -> Result<(), Stop> {
        self.state = f.run.ok_or(Stop { fault: Fault::Internal("a frame with no state"), at })?.state;
        self.locals = f.locals;
        Ok(())
    }
}

impl<'a> Instance<'a> {
    /// The instance of the flow `def` as `init` makes it: `config` has the inputs of `init` (by name), and the `let`s of
    /// a constant or of that clock are made once, with the instances it calls. Call it on a thread of a large stack.
    pub fn init<'h>(
        view: View<'a>,
        def: DefId,
        sample_rate: f32,
        config: &[(&str, Value)],
        host: Option<&'h mut dyn FnHost>,
    ) -> Result<Instance<'a>, Stop>
    where
        'a: 'h,
    {
        let (mut me, body, decl) = Inst::plan(view, def)?;
        let ctx = Ctx { sample_rate, tick: 0 };
        let mut f = me.frame(body, ctx, 0, host);
        let done = enter(&mut f, &mut me, decl, Stage::Init, config);
        let kept = me.keep(f, body.ast.expr(decl.body).span);
        done.and(kept).map(|()| Instance { body, decl, me, ctx })
    }

    /// `process` over `frames` frames: the `let`s of `block` once (`params`, by name), a call of 0 frames too, and for
    /// each frame the `sample` inputs (`inputs`, a column of `frames` values for each, by name), the `let`s of `sample`
    /// and the output. The outputs, one for each frame; `tick` goes up by one for each frame that is done.
    pub fn process<'h>(
        &mut self,
        params: &[(&str, Value)],
        inputs: &[(&str, &[Value])],
        frames: usize,
        host: Option<&'h mut dyn FnHost>,
    ) -> Result<Vec<Value>, Stop>
    where
        'a: 'h,
    {
        let (decl, mut outs) = (self.decl, Vec::new());
        let at = self.body.ast.expr(decl.body).span;
        let mut f = self.me.frame(self.body, self.ctx, 0, host);
        let done = (|| {
            if inputs.iter().any(|(_, column)| column.len() != frames) {
                return Err(Stop { fault: Fault::Internal("a column that is not of the frames given"), at });
            }
            check(at, decl, Stage::Sample, inputs.iter().map(|(n, _)| *n))?;
            enter(&mut f, &mut self.me, decl, Stage::Block, params)?;
            for n in 0..frames {
                if let Some(run) = f.run.as_mut() {
                    run.ctx = self.ctx;
                }
                let given: Vec<(&str, &Value)> = inputs.iter().map(|(name, col)| (*name, &col[n])).collect();
                enter(&mut f, &mut self.me, decl, Stage::Sample, &given)?;
                outs.push(self.me.out.clone());
                self.ctx.tick = self.ctx.tick.wrapping_add(1);
            }
            Ok(())
        })();
        let kept = self.me.keep(f, at);
        done.and(kept).map(|()| outs)
    }

    /// `reset` (§11.6): every delay and every instance it calls is as `init` made it, the time is 0. The `let`s of `init`
    /// keep their values; those of a faster clock are made again by the next `process` before they are read.
    pub fn reset(&mut self) {
        self.me.state.reset();
        self.ctx.tick = 0;
    }

    /// The clock of each step: the `let`s in the order they are written, then the output.
    pub fn clocks(&self) -> Vec<Clock> {
        self.me.steps.iter().map(|s| s.clock).collect()
    }
}
