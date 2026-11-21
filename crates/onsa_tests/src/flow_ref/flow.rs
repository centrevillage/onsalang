//! One instance of a flow (§11.2, §11.3, §11.6): the clock of each `let`, and the two entries `init` and `process`.
//! The clock of a `let` says when its value is made again: a `let` of a constant or of `init` once, at `init`; of `block`
//! once for each `process` call, a call of 0 frames too; of `sample` for each frame. A `let` of a faster clock reads the
//! latest value of a slower one. The `let`s of a stage run in the order they are written (§11.2), the stages of a frame
//! in the order of the clocks, and `e at k` has the clock `k` but not another value (§11.3). S-1196: a value of the parameter kinds
//! alone is made at the stage its values decide, `at` seen through, and the clock `k` is what a condition on it is decided by (S-1166);
//! a value of a tick keeps the clock `k`. The parts of a `let` that are of a slower clock than the `let` are made by the
//! slower stage (`hoist.rs`, §11.3: "各式を、部分式も含めて、その値と評価されるかどうかが決まる最も遅い段で評価する"), whether the value is
//! read or not, so a panic of a `block` part is a panic of the `block` stage of a call of 0 frames too. The delays (`state.rs`) are in the `sample` stage, and
//! the second phase of each frame stores what they save, after the stage and before `tick` goes up. The instances of
//! flows (`Inst`), `reset` (`Instance::reset`) and `render` are here too. A panic of a value of the clock
//! of a constant is E0419 in the spec (compile time, §11.3): the evaluator makes it at `init` and gives the panic of
//! `init`; the entry of the comparison (W7-19) reads it as an error of the compile time.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::flow_names::FlowBuiltin;
use onsa_sema::{DefId, LocalId, Target};
use onsa_syntax::ast::{CallKind, ExprId, ExprKind, PatId, StmtKind};

use super::expr::{Frame, Hoisted, Stop};
use super::hoist::{pre, seen_of, stage_of};
use super::host::FnHost;
use super::rate::{chain_of, components, derived, on_tick, ring_clock, slow_ticks};
use super::scalar::{Fault, PanicKind};
use super::sema_view::{Body, Called, Stage, View, clock_stage, input_stage, inputs_at, output_stage};
use super::state::SAVED;
use super::state::{InstState, Run};
use super::value::Value;

/// When a value is made: once for good (a constant), at `init`, for each `process` call (`block`), for each tick of a ratio `2^r` of the `sample` of the
/// body (`Tick(0)` is `sample`, `Tick(-2)` is `sample / 4`, §11.9). The order is that of §11.3 (a constant < `init` < `block` < `sample / N` <
/// `sample` < `sample * N`): the order of the derive is that of the variants, and of `r`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Clock {
    Const,
    Init,
    Block,
    Tick(i32),
}

impl Clock {
    /// The `sample` of the body: a const of the type (as [`Stage::Sample`]).
    #[allow(non_upper_case_globals)]
    pub const Sample: Clock = Clock::Tick(0);
    /// The clock of `sample_tick()` (§11.4): that of the place that reads it, so it is below every tick, and a `let` of it alone is rooted at `sample`.
    const AMBIENT: Clock = Clock::Tick(i32::MIN);

    /// The clock of a `let`, or of the output, whose expression has this one (§11.4: the lower bound of a tick is the `sample` of the body).
    pub(super) fn rooted(self) -> Clock {
        if self == Clock::AMBIENT { Clock::Sample } else { self }
    }
}

/// What a name stands for in the clocks (S-1196, §11.3): the *stage* its value is made in (a value of the parameter kinds alone is made
/// at the stage its values decide, whatever clock `at` gave it) and the clock it is *read* at (the clock `at` gave it, which a condition
/// on it is decided by, S-1166). The read clock is `None` for a derived clock (`p at (sample / 4)`), which this evaluator has not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Seen {
    pub stage: Clock,
    pub read: Option<Clock>,
}

impl Seen {
    /// A name whose stage and clock are the same.
    pub(super) fn both(c: Clock) -> Seen {
        Seen { stage: c, read: Some(c) }
    }
}

pub(super) type Known = HashMap<LocalId, Seen>;

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
            Stage::Tick(r) => Clock::Tick(r),
        }
    }
}

impl Clock {
    /// Is a value of this clock made in `stage` of a call (the one place that says which stage runs which clock)? The `sample` stage makes the
    /// values of `sample * N` too: they are read there (§11.9).
    pub fn runs_at(self, stage: Stage) -> bool {
        match (stage, self) {
            (Stage::Init, _) => self <= Clock::Init,
            (Stage::Block, _) => self == Clock::Block,
            (Stage::Sample, Clock::Tick(r)) => r >= 0,
            (Stage::Tick(r), _) => self == Clock::Tick(r),
        }
    }
}

/// The time an instance runs in: its sample rate, and the frames it has run since `init` (the counter of §11.9, which
/// goes round at 2^32).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ctx {
    pub sample_rate: f32,
    pub tick: u32,
    /// The digits over the counter: how many times it has gone round (§11.4 keeps them for `.down~(N)`, whose counter is 1/N of its caller's whole one).
    pub rounds: u32,
}

impl Ctx {
    /// The time at the sample rate `sample_rate` and the counter `total`, the digits over the `U32` included.
    pub(super) fn at(sample_rate: f32, total: u64) -> Ctx {
        Ctx { sample_rate, tick: total as u32, rounds: (total >> 32) as u32 }
    }

    /// The counter with the digits over it.
    pub(super) fn total(self) -> u64 {
        u64::from(self.rounds) << 32 | u64::from(self.tick)
    }
}

/// The clock of `e` (the clock it is *read* at, §11.3: `e at k` has the clock `k`; a condition on it is decided by this clock, S-1166): the
/// fastest of the names in it. The stage it is made in is [`super::hoist::stage_of`], which sees through `at` for a value of the
/// parameter kinds alone (S-1196). A name has the clock its local has so far
/// (`known`); one that `known` has not must be bound inside `root`, the expression being clocked (an arm of a `match`),
/// and has no clock of its own: bound anywhere else is an internal error. A constant has none, a delay or an instance
/// ticks with the `sample` of the body (§11.4: the first argument of a delay is at `sample`, or `^name`, which has no clock of
/// its own and is read as `sample`, §11.3; a constant or a `block` one is E0813; the clock of the events of a delay comes
/// with W7-17), and `e at k` has the clock `k` (§11.3).
pub(super) fn clock_of(body: &Body, known: &Known, root: ExprId, e: ExprId) -> Result<Clock, Fault> {
    match &body.ast.expr(e).kind {
        ExprKind::Call { kind, args, .. } if matches!(kind, CallKind::Flow) || body.time_call(e) => {
            // A chain of `.down~` and `.up~` has the clock of its head's output rebased by the sum of its ratios (§11.9): the output's `2^m` times `2^r`.
            if let Some(chain) = chain_of(body, e)? {
                return match body.called(chain.head)? {
                    Called::Flow(def) => match output_stage(body.view.flow(def)?)? {
                        Stage::Tick(m) => Ok(Clock::Tick(m + chain.ratio)),
                        _ => Err(Fault::Unavailable("a chain whose head is not an instance with an output at a tick")),
                    },
                    _ => Err(Fault::Unavailable("a chain whose head is not an instance of a flow")),
                };
            }
            Ok(match body.called(e)? {
                Called::Builtin(FlowBuiltin::SampleRate) => Clock::Init,
                Called::Builtin(FlowBuiltin::SampleTick) => Clock::AMBIENT,
                // §11.4: the clock of a delay is that of its first argument, a tick (`^name` and a parameter kind are read as `sample`, §11.3).
                Called::Builtin(FlowBuiltin::Delay(_)) => {
                    let first = args.get(SAVED).ok_or(Fault::Internal("a delay with no argument"))?;
                    match clock_of(body, known, root, first.expr)? {
                        c @ Clock::Tick(_) => c.rooted(),
                        _ => Clock::Sample,
                    }
                }
                Called::Flow(def) => output_stage(body.view.flow(def)?)?.into(),
            })
        }
        // The index of a `par~` is a value of `init` (§11.5), not a constant: the body is clocked with it.
        ExprKind::Par { var, body: inner, .. } => {
            let mut inside = known.clone();
            inside.insert(body.par_var(var.span)?, Seen::both(Clock::Init));
            clock_of(body, &inside, root, *inner)
        }
        ExprKind::At { expr, clock } => {
            clock_of(body, known, root, *expr)?;
            match &clock.ratio {
                Some(r) => derived(body, r).map(Clock::Tick),
                None => clock_stage(&clock.name.name)
                    .map(Clock::from)
                    .ok_or(Fault::Unavailable("a clock the evaluator has not")),
            }
        }
        ExprKind::Path(_) | ExprKind::Field { .. } if body.names(e) => match body.target(e)? {
            Target::Local(l) => match known.get(l) {
                Some(seen) => seen.read.ok_or(Fault::Unavailable("a clock the evaluator has not")),
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
pub(super) struct Step {
    pub(super) pat: Option<PatId>,
    pub(super) init: ExprId,
    pub(super) clock: Clock,
    /// The clocks of the locals before this step (`hoist::pre` reads the clocks of the parts of `init` by them).
    pub(super) known: Rc<Known>,
}

/// What is the same at each call of a flow: its steps, and the ticks slower than `sample` its stages are of (`rate::slow_ticks`).
#[derive(Clone)]
pub(super) struct Plan {
    pub(super) steps: Rc<[Step]>,
    pub(super) slow: Rc<[i32]>,
}

/// The plans made so far for a tree of instances, one for each flow: the clocks of a body are the same at each call.
pub(super) type Plans = Rc<RefCell<HashMap<DefId, Plan>>>;

/// What an instance of a flow keeps between its entries, with no lifetime: one a flow calls is kept whole in the state of
/// its caller (`InstState::children`), the outermost in an [`Instance`]; the entry `enter` is the same.
#[derive(Debug)]
pub struct Inst {
    pub(super) def: DefId,
    pub(super) steps: Rc<[Step]>,
    /// The ticks slower than `sample` that its stages are of (the larger N first).
    pub(super) slow: Rc<[i32]>,
    /// The ratio of the chain of modifiers it is the head of (`.down~(2)` is -1); 0 for a call with none, which runs at the time of its caller.
    pub(super) rate: i32,
    /// The time of its caller and the stage of it that this instance last ran the stages of (`Frame::run_unit`): each stage of it runs once for each, whoever asks first.
    pub(super) done: Option<(u64, Stage)>,
    /// The elements of the outputs of the runs of the last frame of a `.up~(N)` chain, in the order of time: what its call reads as a burst (`Frame::held`).
    pub(super) runs: Vec<Value>,
    locals: HashMap<LocalId, Value>,
    /// The parts of the body that a slower stage made (`Frame::hoisted`).
    hoisted: Hoisted,
    pub(super) out: Value,
    pub(super) state: InstState,
    /// The index of each `par~` around the call that made it, which the arguments of its `block` stage and what a ring gathers of them may read (the bindings of an arm they read are made by `Frame::eval_in_arms`).
    pub(super) scope: Vec<(LocalId, Value)>,
}

/// The stage of a call a panic came from (§9.2, §11.6): its `init`, the start of a `process` (the lengths of the columns are
/// compared there, before any state moves), the `block` stage of a `process` (whatever its frames), or the frame `n` of
/// it, counted from 0 in that `process`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicAt {
    Init,
    Start,
    Block,
    Sample(usize),
}

impl PanicAt {
    /// The stage of the flow it is (`None` is the start of a `process`, before any stage of a flow runs), whichever frame.
    pub fn stage(self) -> Option<Stage> {
        match self {
            PanicAt::Init => Some(Stage::Init),
            PanicAt::Start => None,
            PanicAt::Block => Some(Stage::Block),
            PanicAt::Sample(_) => Some(Stage::Sample),
        }
    }
}

/// The stage of the code written at `at` (§11.3): that of the clock of the part of a `let` (or the output) of a flow it is
/// within that a slower stage makes (`hoist::part_clock`), else of the `let`, a constant's as `init`'s. `None` where no flow
/// has it (the call a test makes, whose panic is the start of a `process`).
pub fn stage_at(view: View, at: Span) -> Option<Stage> {
    let plans = Plans::default();
    view.flows().into_iter().find_map(|def| {
        let (me, body, _) = Inst::plan(view, def, &plans).ok()?;
        let within = |e: ExprId| {
            let s = body.ast.expr(e).span;
            s.file == at.file && s.start <= at.start && at.end <= s.end
        };
        let step = me.steps.iter().find(|s| within(s.init))?;
        let clock = super::hoist::part_clock(&body, &step.known, step.init, at).ok()?.unwrap_or(step.clock);
        Some(match clock {
            Clock::Const | Clock::Init => Stage::Init,
            Clock::Block => Stage::Block,
            Clock::Tick(_) => Stage::Sample,
        })
    })
}

/// What a call of the entries gives (§11.6, the memo's `Outcome`): the outputs, or the panic with the stage and the
/// expression it is at. An unavailable form and an internal error are not an outcome of the program: they stay `Stop`s.
#[derive(Debug)]
pub enum Outcome {
    Ok(Vec<Value>),
    Panic { at: PanicAt, stop: Stop },
}

impl Outcome {
    /// The outcome of a call that gave `r`: a panic at its stage is an outcome, any other fault is the error it is.
    fn of(r: Result<Vec<Value>, (PanicAt, Stop)>) -> Result<Outcome, Stop> {
        match r {
            Ok(outs) => Ok(Outcome::Ok(outs)),
            Err((at, stop)) if matches!(stop.fault, Fault::Panic(_)) => Ok(Outcome::Panic { at, stop }),
            Err((_, stop)) => Err(stop),
        }
    }
}

/// What a call of `render` is given (§11.6): the inputs of `init` and of `block` by name, the columns of the `sample`
/// inputs, and the frames of a flow that has none of them.
#[derive(Clone, Copy, Default)]
pub struct Call<'c> {
    pub config: &'c [(&'c str, Value)],
    pub params: &'c [(&'c str, Value)],
    pub inputs: &'c [(&'c str, &'c [Value])],
    pub frames: Option<usize>,
}

/// One instance of a flow, the outermost: the time it runs in is its own, and the instances it calls read it.
pub struct Instance<'a> {
    body: Body<'a>,
    decl: &'a FlowDef,
    pub(super) me: Inst,
    plans: Plans,
    /// The time the instance runs in: `sample_tick()` reads it, and `reset` makes it 0.
    pub ctx: Ctx,
    /// The places of the tree held so far (`Run::used`), which a call goes on from: the limit is the tree's, not a call's.
    used: usize,
}

/// The inputs of `decl` at `stage` and the `names` given: an input left out, one added and one of another clock are
/// internal errors (§11.6 decides the number), a call of 0 frames too.
fn check<'n>(at: Span, decl: &FlowDef, stage: Stage, names: impl Iterator<Item = &'n str> + Clone) -> Result<(), Stop> {
    let wrong = |what| Stop { fault: Fault::Internal(what), at };
    let mine = inputs_at(decl, stage).map_err(|fault| Stop { fault, at })?;
    if names.clone().count() != mine.len() {
        return Err(wrong("the inputs given are not the inputs of the clock"));
    }
    match mine.iter().all(|i| names.clone().any(|n| n == i.name)) {
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
    for i in inputs_at(decl, stage).map_err(|fault| Stop { fault, at })? {
        let (_, v) = given.iter().find(|(n, _)| *n == i.name).ok_or(wrong("an input that was not given"))?;
        f.locals.insert(f.body.input(&i.name).ok_or(wrong("an input with no local"))?, v.borrow().clone());
    }
    Ok(())
}

/// The steps the clocks of `at` run, in the order they are written (the output is a step too, the last). A step of a faster clock
/// is not run, but the parts of it that this stage makes are (`hoist::pre`, in the order of the steps: a `let` of `block` that the
/// part reads is made before it).
// S-1093 (1): a `let` and the output expression of a stage are evaluated whether or not a value is read from them (so one that
// panics does, in a branch not taken too, and the output of `block` or `init` in a call of 0 frames too).
fn stage(f: &mut Frame, steps: &[Step], out: &mut Value, at: Stage) -> Result<(), Stop> {
    for s in steps {
        if s.clock.runs_at(at) {
            match s.pat {
                Some(pat) => f.bind(pat, s.init)?,
                None => *out = f.eval(s.init)?,
            }
        } else if s.clock > Clock::from(at) {
            pre(f, &s.known, s.init, s.init, at)?;
        }
    }
    Ok(())
}

/// One entry of `inst` in its frame `f` (the time is `f.run.ctx`): the inputs of the stage `at` (`given`, by name), its
/// `let`s, then what the stage has besides: at `init` the nodes (the delays, the instances it calls), for any other stage the stage of the instances it calls that runs in it
/// (`run_children`, §11.9, S-1088, at `block` also the `block` stage of those, a call of 0 frames too), and for a tick the second phase of the delays (§11.4), whose saves are stored at once.
pub(super) fn enter<V: std::borrow::Borrow<Value>>(
    f: &mut Frame,
    inst: &mut Inst,
    decl: &FlowDef,
    at: Stage,
    given: &[(&str, V)],
) -> Result<(), Stop> {
    give(f, decl, at, given)?;
    f.run.as_mut().iter_mut().for_each(|run| run.stage = at);
    stage(f, &inst.steps, &mut inst.out, at)?;
    let whole = f.body.ast.expr(decl.body).span;
    match at {
        Stage::Init => f.make_cells(&inst.steps.iter().map(|s| s.init).collect::<Vec<_>>()),
        Stage::Block => f.run_children(at, whole),
        _ => {
            if at == Stage::Sample {
                f.save_gathers(whole)?;
            }
            f.run_children(at, whole)?;
            f.commit(whole)
        }
    }
}

/// A frame of the outermost instance `inst` at the time of its frame `f` (§11.9): the stages of the slower ticks that the time is on, the larger N first (S-578, S-1079), then
/// `sample` with its inputs (`given`, by name). A tick of ratio `2^-k` is on when the counter of the instance is a multiple of `2^k`, the first
/// frame included, whatever the calls of `process` are (§11.9, §13.4). The instances it calls run theirs in the stages of this one (`Frame::run_children`).
pub(super) fn run_frame<V: std::borrow::Borrow<Value>>(
    f: &mut Frame,
    inst: &mut Inst,
    decl: &FlowDef,
    given: &[(&str, V)],
) -> Result<(), Stop> {
    let time = f.run.as_ref().map(|run| run.ctx);
    for r in inst.slow.clone().iter().filter(|r| time.is_none_or(|ctx| on_tick(ctx, **r))) {
        enter(f, inst, decl, Stage::Tick(*r), &[] as &[(&str, Value)])?;
    }
    enter(f, inst, decl, Stage::Sample, given)
}

impl Inst {
    /// The plan of the flow `def` (one for each flow in `plans`, made at the first instance).
    pub(super) fn planned(view: View, def: DefId, plans: &Plans) -> Result<Plan, Stop> {
        let known = plans.borrow().get(&def).cloned();
        if let Some(plan) = known {
            return Ok(plan);
        }
        let unavailable = |fault| Stop { fault, at: view.name_span(def) };
        let (body, decl) = (view.body(def).map_err(unavailable)?, view.flow(def).map_err(unavailable)?);
        let steps = Inst::steps(&body, decl)?;
        let plan = Plan { slow: slow_ticks(view, &body, &steps, plans)?, steps };
        plans.borrow_mut().insert(def, plan.clone());
        Ok(plan)
    }

    /// The instance of the flow `def` with its body and declaration, and the plan of the flow.
    pub(super) fn plan<'a>(view: View<'a>, def: DefId, plans: &Plans) -> Result<(Inst, Body<'a>, &'a FlowDef), Stop> {
        let unavailable = |fault| Stop { fault, at: view.name_span(def) };
        let (body, decl) = (view.body(def).map_err(unavailable)?, view.flow(def).map_err(unavailable)?);
        let Plan { steps, slow } = Inst::planned(view, def, plans)?;
        Ok((
            Inst {
                def,
                steps,
                slow,
                rate: 0,
                done: None,
                runs: Vec::new(),
                locals: HashMap::new(),
                hoisted: HashMap::new(),
                out: Value::Unit,
                state: InstState::default(),
                scope: Vec::new(),
            },
            body,
            decl,
        ))
    }

    /// The clock of each `let` and of the output (§11.2), made once, the `let`s that others read before those that read them (`components`): one that no loop goes through has the clock its operands give,
    /// a loop the clock of what enters it from outside when that is a tick slower than `sample` (§11.3, `ring_clock`), the same for all its steps. The output of a tick that `sample_tick()` alone makes is made at that tick.
    fn steps(body: &Body, decl: &FlowDef) -> Result<Rc<[Step]>, Stop> {
        let wrong = |e, what| Stop { fault: Fault::Internal(what), at: body.ast.expr(e).span };
        let at = |e| move |fault| Stop { fault, at: body.ast.expr(e).span };
        let ExprKind::Block(b) = &body.ast.expr(decl.body).kind else { return Err(wrong(decl.body, "a body")) };
        let tail = b.tail.ok_or(wrong(decl.body, "a flow with no output expression"))?;
        let mut lets = Vec::new();
        for s in &b.stmts {
            let StmtKind::Let { pat, init, .. } = &body.ast.stmt(*s).kind else {
                return Err(wrong(decl.body, "a statement"));
            };
            lets.push((*pat, *init));
        }
        let mut inputs = Known::new();
        for i in &decl.inputs {
            let stage = input_stage(i).map_err(at(decl.body))?;
            inputs.insert(
                body.input(&i.name).ok_or(wrong(decl.body, "an input with no local"))?,
                Seen::both(stage.into()),
            );
        }
        let (mut known, mut seen) = (inputs.clone(), vec![None; lets.len()]);
        for (members, looped) in components(body, &lets).map_err(at(decl.body))? {
            let ring = if looped {
                ring_clock(body, &mut known, &lets, &members).map_err(at(lets[members[0]].1))?
            } else {
                None
            };
            for i in members {
                let (pat, init) = lets[i];
                let clock = match ring {
                    Some(c) => Seen::both(c),
                    None => seen_of(body, &known, init, init).map_err(at(init))?,
                };
                // SPEC-GAP(S-1119): the locals the pattern binds (a `let` taken apart) have the clock of the whole right
                // side, as the interpreter has it; the other reading gives each the clock of its own element.
                known.extend(body.pat_locals(pat).map_err(at(init))?.into_iter().map(|l| (l, clock)));
                seen[i] = Some(clock);
            }
        }
        // The steps in the order they are written, each with the clocks of the locals before it.
        let (mut known, mut steps) = (inputs, Vec::new());
        for ((pat, init), clock) in lets.iter().zip(seen) {
            let clock = clock.ok_or(wrong(*init, "a `let` with no clock"))?;
            let before = Rc::new(known.clone());
            known.extend(body.pat_locals(*pat).map_err(at(*init))?.into_iter().map(|l| (l, clock)));
            steps.push(Step { pat: Some(*pat), init: *init, clock: clock.stage, known: before });
        }
        let out = seen_of(body, &known, tail, tail).map_err(at(tail))?;
        let ambient = stage_of(body, &known, tail, tail).map_err(at(tail))? == Clock::AMBIENT;
        let clock = match output_stage(decl) {
            Ok(Stage::Tick(m)) if ambient && m < 0 => Clock::Tick(m),
            _ => out.stage,
        };
        steps.push(Step { pat: None, init: tail, clock, known: Rc::new(known) });
        Ok(steps.into())
    }

    /// The frame of an evaluation, given the locals and the state (`keep` takes them back), the time and the places held.
    pub(super) fn frame<'b>(
        &mut self,
        body: Body<'b>,
        ctx: Ctx,
        used: usize,
        plans: Plans,
        host: Option<&'b mut dyn FnHost>,
    ) -> Frame<'b> {
        let mut f = Frame::new(body);
        f.locals = std::mem::take(&mut self.locals);
        f.hoisted = std::mem::take(&mut self.hoisted);
        f.run = Some(Run::new(std::mem::take(&mut self.state), ctx, used, plans));
        f.host = host;
        f
    }

    /// What an evaluation leaves: the latest values of the locals and the state, taken back from its frame.
    pub(super) fn keep(&mut self, f: Frame, at: Span) -> Result<(), Stop> {
        self.state = f.run.ok_or(Stop { fault: Fault::Internal("a frame with no state"), at })?.state;
        self.locals = f.locals;
        self.hoisted = f.hoisted;
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
        let plans = Plans::default();
        let (mut me, body, decl) = Inst::plan(view, def, &plans)?;
        let ctx = Ctx::at(sample_rate, 0);
        let mut f = me.frame(body, ctx, 0, plans.clone(), host);
        let done = enter(&mut f, &mut me, decl, Stage::Init, config);
        let used = f.run.as_ref().map_or(0, |r| r.used);
        let kept = me.keep(f, body.ast.expr(decl.body).span);
        done.and(kept).map(|()| Instance { body, decl, me, plans, ctx, used })
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
        self.stages(params, inputs, frames, host).map_err(|(_, stop)| stop)
    }

    /// [`Self::process`] with a panic as a result (§9.2, §11.6): the stage it was at and the expression.
    pub fn process_outcome<'h>(
        &mut self,
        params: &[(&str, Value)],
        inputs: &[(&str, &[Value])],
        frames: usize,
        host: Option<&'h mut dyn FnHost>,
    ) -> Result<Outcome, Stop>
    where
        'a: 'h,
    {
        Outcome::of(self.stages(params, inputs, frames, host))
    }

    /// The one `process`, with the stage a stop is at (`block`, then each frame).
    fn stages<'h>(
        &mut self,
        params: &[(&str, Value)],
        inputs: &[(&str, &[Value])],
        frames: usize,
        host: Option<&'h mut dyn FnHost>,
    ) -> Result<Vec<Value>, (PanicAt, Stop)>
    where
        'a: 'h,
    {
        let (decl, mut outs, mut stage) = (self.decl, Vec::new(), PanicAt::Start);
        let at = self.body.ast.expr(decl.body).span;
        let mut f = self.me.frame(self.body, self.ctx, self.used, self.plans.clone(), host);
        let done = (|| {
            check(at, decl, Stage::Sample, inputs.iter().map(|(n, _)| *n))?;
            stage = PanicAt::Start;
            if inputs.iter().any(|(_, column)| column.len() != frames) {
                return Err(Stop { fault: Fault::Panic(PanicKind::Length), at });
            }
            stage = PanicAt::Block;
            enter(&mut f, &mut self.me, decl, Stage::Block, params)?;
            for n in 0..frames {
                stage = PanicAt::Sample(n);
                let run = f.run.as_mut().ok_or(Stop { fault: Fault::Internal("a frame with no run"), at })?;
                run.ctx = self.ctx;
                let given: Vec<(&str, &Value)> = inputs.iter().map(|(name, col)| (*name, &col[n])).collect();
                run_frame(&mut f, &mut self.me, decl, &given)?;
                outs.push(self.me.out.clone());
                self.ctx = Ctx::at(self.ctx.sample_rate, self.ctx.total().wrapping_add(1));
            }
            Ok(())
        })();
        self.used = f.run.as_ref().map_or(self.used, |r| r.used);
        let kept = self.me.keep(f, at);
        done.and(kept).map(|()| outs).map_err(|stop| (stage, stop))
    }

    /// `render` (§11.6): `init` and one `process` of all the frames, the call a test makes. A flow with `sample` inputs
    /// has the length of their columns (`frames` is `None`); one with none has `frames`. A panic of `init` or of
    /// `process` is the outcome, at its stage.
    pub fn render<'h>(
        view: View<'a>,
        def: DefId,
        sample_rate: f32,
        call: &Call,
        mut host: Option<&'h mut dyn FnHost>,
    ) -> Result<Outcome, Stop>
    where
        'a: 'h,
    {
        let here = |fault| Stop { fault, at: view.name_span(def) };
        let Call { config, params, inputs, frames } = *call;
        let sampled = !inputs_at(view.flow(def).map_err(here)?, Stage::Sample).map_err(here)?.is_empty();
        let n = match (sampled, frames, inputs.first()) {
            (true, None, Some((_, column))) => column.len(),
            (false, Some(n), _) => n,
            _ => {
                return Err(here(Fault::Internal(
                    "`frames` is for a flow with no `sample` input, the columns for one",
                )));
            }
        };
        let first = host.as_mut().map(|h| &mut **h as &mut dyn FnHost);
        match Instance::init(view, def, sample_rate, config, first) {
            Ok(mut me) => me.process_outcome(params, inputs, n, host),
            Err(stop) => Outcome::of(Err((PanicAt::Init, stop))),
        }
    }

    /// `reset` (§11.6): every delay and every instance it calls is as `init` made it, the time is 0. The `let`s of `init`
    /// keep their values; those of a faster clock are made again by the next `process` before they are read.
    pub fn reset(&mut self) {
        self.me.state.reset();
        self.ctx = Ctx::at(self.ctx.sample_rate, 0);
    }

    /// The clock of each step: the `let`s in the order they are written, then the output.
    pub fn clocks(&self) -> Vec<Clock> {
        self.me.steps.iter().map(|s| s.clock).collect()
    }
}
