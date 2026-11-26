//! The state of a flow instance and the delays that use it (§11.4, §11.6): a tree of cells, one for each place a
//! delay is called (the call, and the replica of each `par~` around it, U2), the three delays by their formulas, and the
//! two phases of a tick: the delays read their stored value first, and what they store is evaluated after the body and
//! all of it stored at once (`^name` is read in the second phase, when the `let` it names has its value). The instances
//! a flow calls are the `children` of the tree: each is a whole [`Inst`], run in a frame of its own (`in_child`) at the
//! time of its caller (§11.5), and counted in the limit of the tree.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::flow_names::{Delay, FlowBuiltin};
use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{DefId, LocalId, Ty};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};

use super::call::parts;
use super::chain::Gate;
use super::delay_mods::DelayMods;
use super::expr::{Eval, Frame, LOW_STACK, Stop, evaluates};
use super::flow::{Clock, Ctx, Inst, Known, Plans, enter};
use super::hoist::gather_args;
use super::hoist::{caret, has_state};
use super::rate::{Bound, Level, args_of, chain_of, child_time, counted, levels, n_of, on_tick, port_exprs};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Called, Stage, input_stage};
use super::value::{IntKind, Scalar, Shape, Value};

/// The places an instance takes in the limit of the tree (`Limits::most`): some 100 thousand instances, not 2^20.
const INSTANCE: usize = 8;

/// What a node of the state is for: the delay a call is, the instance it makes, and what the caller keeps for an instance that a chain runs at another rate (§11.9: "集めた値は呼び出し側の値"、"配った値は呼び出し側の
/// `sample` の値"): the ring of the elements that the input number `input` gathers at the boundary `bound` (1 for the innermost), and the array that the boundary `bound` deals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Role {
    Delay,
    Child,
    Gather { bound: usize, input: usize },
    Deal(usize),
}

/// Where a node of the state is: the call that makes it (the head of a chain; a node of a gather or a deal is a node of that call, never of the argument it takes), the replica of each `par~` it is in (U2), and what
/// it is for (`Role`), so that nodes of one call and of the nodes of an expression that is the argument of another never meet.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKey {
    pub call: ExprId,
    pub replicas: Vec<u32>,
    pub role: Role,
}

impl NodeKey {
    /// The node of another role of the same call and replicas.
    pub(super) fn role(&self, role: Role) -> NodeKey {
        NodeKey { role, ..self.clone() }
    }
}

/// What a delay holds: `prev~` its last value, the others a ring of values and the place `w` that is written next.
#[derive(Clone, Debug)]
pub enum Store {
    Last(Value),
    Ring { buf: Vec<Value>, w: usize },
}

/// A node of the state: the value it starts from (`init`, saved for `reset`) and the one it has now.
#[derive(Clone, Debug)]
pub struct Cell {
    pub initial: Store,
    pub current: Store,
}

impl Cell {
    /// Back to the value it started from; `soft` (`reset_if~`, which leaves the phase counters) keeps the place a ring is written next, so that the frames after it write the ring of a boundary in order (§11.9).
    pub(super) fn back(&mut self, soft: bool) {
        match (&mut self.current, &self.initial, soft) {
            (Store::Ring { buf, .. }, Store::Ring { buf: start, .. }, true) => buf.clone_from(start),
            _ => self.current = self.initial.clone(),
        }
    }
}

/// The state of one instance: its own nodes, and the instances it calls (whole, with their `let`s).
#[derive(Debug, Default)]
pub struct InstState {
    pub cells: BTreeMap<NodeKey, Cell>,
    pub children: BTreeMap<NodeKey, Inst>,
    /// What each `let` (by its initializer) holds beyond the one place of its step: part of the tree's places.
    held: BTreeMap<ExprId, usize>,
    /// What each chain of modifiers on a delay keeps, by the node of the delay (`delay_mods.rs`).
    pub(super) mods: BTreeMap<NodeKey, DelayMods>,
}

impl InstState {
    /// Every node back to what it started from (§11.6 `reset`), the instances inside too. `soft` is the `reset_if~` (§11.10, S-1186): the phase counters (the stage each instance last ran, the ring's next place) and
    /// what each `when~` remembers stay, its held output does not; the fields of the ticks are `Frame::restart`'s.
    pub fn reset(&mut self, soft: bool) {
        self.cells.values_mut().for_each(|c| c.back(soft));
        self.mods.values_mut().for_each(|m| m.reset(soft));
        self.children.values_mut().for_each(|c| {
            // `done` of a `reset_if~` stays as the counters do; clearing it too shows in no value (a mutant that does passes the gate and `heavy_`): a reset is put before or after the work of a stage, and no stage is asked a second time after it.
            if !soft {
                c.done = None;
            }
            c.whens.iter_mut().flatten().for_each(|g| g.reset(soft));
            c.state.reset(soft);
        });
    }
}

/// What a delay saves this tick: where, the expression whose value it is, and the bindings it is read under (the index
/// of each `par~` it is in and the locals an arm of a `match~` binds: they are not what they were when it is stored).
pub(super) struct Save {
    key: NodeKey,
    expr: ExprId,
    scope: Vec<(LocalId, Value)>,
    /// The call whose ring it is (a gather): its argument is read with the bindings of the arms around the call, as the call reads it at a stage (`eval_in_arms`).
    call: Option<ExprId>,
    /// The clock `q` of the stream a ring gathers (`sample * 2^q`): the value is a burst of `2^q` elements, or one of the parameter kinds that is each of them; 0 for a delay, the one value.
    q: i32,
    /// Is it stored? Not where a `when~` stops the delay: the value is evaluated all the same (§11.10, `delay_mods.rs`).
    keep: bool,
    /// A part that reads a `^name` (S-1244, `Frame::defer_part`): not stored in a cell but kept in its field (`Frame::hoisted`), as of the stage that made it.
    field: Option<Clock>,
    /// The values the reads of an event it holds had where they are written (S-1240, §11.3): a name of an event and a part of an event clock that a stage kept, by the expression that reads it (one name may be read at the end of the stage in
    /// another place, where a `^name` in a condition chooses it), read so at the end of the stage, not the last ones.
    pub(super) snap_parts: Vec<super::events::Snap>,
    /// A `reset_if~` of an event that came after the delay was read and before it is stored: the delay goes back to its `init` after the store (S-1250 (B), `Frame::reset_delay`).
    reset: bool,
    /// The delays inside what it saves (the first argument of the delay it is, read where it is saved) that a `reset_if~` of an event came for before they were read: they go back after this store (S-1250 (B)).
    resets: Vec<NodeKey>,
    /// Is the delay read already? Not while the calls in the conditions of its modifiers are done (`Frame::early_conditions`): an event they give puts it back before the read.
    placed: bool,
}

/// A delay whose `init` argument reads a `^name`: its node, the argument and the bindings it is read under.
type LateCell = (NodeKey, ExprId, Vec<(LocalId, Value)>);

/// What an evaluation of a flow body holds besides its locals: the state, what the delays save this tick, the time it is
/// at (an instance reads its caller's, one that a chain runs the time of its rate, `rate::time_of`), the places of the tree made so far and
/// the plans of its flows.
pub struct Run {
    pub state: InstState,
    saves: Vec<Save>,
    pub ctx: Ctx,
    pub(super) used: usize,
    pub(super) plans: Plans,
    /// The replica of each `par~` the evaluation is inside of, and the bindings of those (`i`, an arm of a `match~`).
    pub(super) replicas: Vec<u32>,
    pub(super) scope: Vec<(LocalId, Value)>,
    /// The event stage of a maker inside `par~`s, run in the middle of the stage of its replica: the call and the replica of each `par~` around it. A `par~` that holds the call is walked for that replica alone (§11.5, §11.11: the events of a
    /// replica are its own), the others as always (`events::fire`, `Frame::replicate`).
    pub(super) pin: Option<(ExprId, Vec<u32>)>,
    /// The stage of this instance that the evaluation is in (`enter` sets it): a call reads in it (`Frame::call`).
    pub(super) stage: Stage,
    /// The calls whose gathered arguments this stage has made (`hoist::gather_args`).
    pub(super) gathered: BTreeSet<NodeKey>,
    /// The `let` (or the output) of the stage that is being made, with the clocks of the locals before it and its value: where a call that an expression of it reads is written (`read_call` makes the arguments it gathers there, S-1233).
    pub(super) step: Option<(Rc<Known>, ExprId)>,
    /// The delays whose `init` argument reads a `^name`, with the bindings it is read under: made at the end of `init` (`Frame::finish_cells`).
    late_cells: Vec<LateCell>,
    /// The steps of the instance this evaluation runs (`enter`): an event stage of its own is run from inside another stage (`Frame::fire`).
    pub(super) steps: Option<Rc<[super::flow::Step]>>,
    /// The events the output step gave in this entry, in order (a call under `.up~(N)` in its body gives one for each run), and the value of the output an event stage run inside it made (`enter` takes them).
    pub(super) emitted: Vec<Value>,
    pub(super) set_out: Option<Value>,
    /// The number of the run of an event stage that this evaluation is in (`events::next_serial`): what a delay of an event gave in it is kept for it alone, as the time is for a delay of a tick.
    pub(super) serial: u64,
}

impl Run {
    pub(super) fn saves_len(&self) -> usize {
        self.saves.len()
    }

    pub(super) fn save_mut(&mut self, slot: usize) -> Option<&mut Save> {
        self.saves.get_mut(slot)
    }

    pub(super) fn new(state: InstState, ctx: Ctx, used: usize, plans: Plans) -> Run {
        Run {
            state,
            saves: Vec::new(),
            ctx,
            used,
            plans,
            replicas: Vec::new(),
            scope: Vec::new(),
            pin: None,
            stage: Stage::Init,
            gathered: BTreeSet::new(),
            step: None,
            late_cells: Vec::new(),
            steps: None,
            emitted: Vec::new(),
            set_out: None,
            serial: 0,
        }
    }
}

enum Node {
    Delay(Delay),
    /// The ring of the `2^k` elements that the port number `input` at `sample * 2^k` (of the expression `arg`) of the part inside the `.down~` boundary `bound` gathers (§11.9), flat, at the call.
    Gather {
        bound: usize,
        input: usize,
        k: i32,
        arg: ExprId,
    },
    /// The array of the `2^m` elements that the output at `sample * 2^m` of the part inside the `.down~` boundary `bound` deals (§11.9), at the call.
    Deal {
        bound: usize,
        m: i32,
    },
    /// The flow, and the parts of the chain of modifiers it is the head of (the head alone for none).
    Instance(DefId, Rc<[Level]>),
    /// The modifiers of a chain on a delay, innermost first, with the node of the delay (`delay_mods.rs`).
    Mods(Vec<Bound>),
}

/// What an expression makes at `init`: the node of a call, or the nodes of the body of a `par~`, each made for every replica.
enum Site<'a> {
    Node(ExprId, Node, &'a [Arg]),
    Par(ExprId, Vec<Site<'a>>),
}

/// §11.4 `vdelay` as the spec writes it, on the ring `buf` (of `MAX + 1`) whose next place is `w`. A float of 32 bits is
/// computed in an `f64` and rounded after each operation, which is the same as the `f32` operation (an `f64` has more
/// than twice the digits).
#[inline(never)]
fn interpolate(buf: &[Value], w: usize, d: &Value) -> Result<Value, Fault> {
    let num = |v: &Value| match v {
        Value::F32(x) => Ok((FloatKind::F32, f64::from(*x))),
        Value::F64(x) => Ok((FloatKind::F64, *x)),
        _ => Err(Internal("a `vdelay~` of what is not a float")),
    };
    let (kind, d) = num(d)?;
    let round = |x: f64| if kind == FloatKind::F32 { f64::from(x as f32) } else { x };
    let (l, m) = (buf.len(), (buf.len() - 1) as f64);
    let dc = if d >= 1.0 { if d <= m { d } else { m } } else { 1.0 };
    let (k, f) = (dc as usize, dc - dc.trunc());
    let (a, b) = (num(&buf[(w + l - k) % l])?.1, num(&buf[(w + l - k - 1) % l])?.1);
    Ok(Value::float(kind, round(round(round(1.0 - f) * a) + round(f * b))))
}

/// What a delay gives now: the value it stored, or the one that `d` reads of the ring of a `vdelay~`.
pub(super) fn read_store(store: &Store, d: Option<&Value>) -> Result<Value, Fault> {
    match (store, d) {
        (Store::Last(v), _) => Ok(v.clone()),
        (Store::Ring { buf, w }, None) => Ok(buf[*w].clone()),
        (Store::Ring { buf, w }, Some(d)) => interpolate(buf, *w, d),
    }
}

impl<'a> Frame<'a> {
    /// The forms of a flow body that have state or a time: the calls of a flow and `^name` (the local, read in the second
    /// phase). One door for `Frame::form`.
    #[inline(never)]
    pub(super) fn stateful(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        if let Some(chain) = chain_of(&self.body, e).map_err(here)? {
            return match self.body.called(chain.head).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => self.delay_chain(chain.head, d, at),
                _ => self.read_call(e, chain.head, at),
            };
        }
        match &self.body.ast.expr(e).kind {
            ExprKind::Feedback(_) => self.name(e, at),
            ExprKind::Call { args, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => self.delay(e, d, args, at),
                Called::Builtin(FlowBuiltin::SampleRate) => Ok(Value::F32(self.time(at)?.sample_rate)),
                // S-1127 (1), §11.4: the first tick after `init` or `reset` reads 0, and each tick adds 1.
                Called::Builtin(FlowBuiltin::SampleTick) => Ok(Value::int(IntKind::U32, self.time(at)?.tick.into())),
                Called::Flow(_) => self.read_call(e, e, at),
            },
            _ => Err(here(Internal("not a stateful form"))),
        }
    }

    /// The node of the call `call` here: in the replica of each `par~` around it (U2).
    pub(super) fn key(&self, call: ExprId, role: Role) -> NodeKey {
        NodeKey { call, replicas: self.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default(), role }
    }

    /// `go` inside the replicas `replicas` of the `par~`s (after the ones it is already in) with the bindings `binds` (the index
    /// of a `par~`, the locals of an arm of a `match~`) made and kept in the run, so that a delay called in it saves them with
    /// what it stores and the second phase reads that under them (§11.4); they are taken off the run after, the one door of both.
    pub(super) fn with_bindings<R>(
        &mut self,
        replicas: &[u32],
        binds: Vec<(LocalId, Value)>,
        go: impl FnOnce(&mut Self) -> Result<R, Stop>,
    ) -> Result<R, Stop> {
        let kept = self.run.as_ref().map(|r| (r.replicas.len(), r.scope.len()));
        self.locals.extend(binds.iter().cloned());
        if let Some(run) = self.run.as_mut() {
            run.replicas.extend_from_slice(replicas);
            run.scope.extend(binds);
        }
        let result = go(self);
        if let (Some(run), Some((r, s))) = (self.run.as_mut(), kept) {
            run.replicas.truncate(r);
            run.scope.truncate(s);
        }
        result
    }

    /// The time this evaluation is at (§11.4: `sample_rate()`, `sample_tick()`); there is none outside an instance.
    pub(super) fn time(&self, at: Span) -> Result<Ctx, Stop> {
        let run = self.run.as_ref();
        run.map(|r| r.ctx).ok_or(Stop { fault: Fault::Unavailable("a time outside an instance of a flow"), at })
    }

    /// A delay called: its output now (§11.4: the value it stored, whatever the delays inside what it will save do),
    /// and the saving of its `e` for the second phase.
    fn delay(&mut self, e: ExprId, d: Delay, args: &[Arg], at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let arg = |i: usize| args.get(i).map(|a| a.expr).ok_or(here(Internal("a delay with too few arguments")));
        // The place of what it saves is held first (S-1154: in the order the delays are written, a delay inside the argument of another after it), then the calls in the first argument come (S-1241), then `d`.
        let key = self.key(e, Role::Delay);
        let slot = self.reserve_save(key.clone(), arg(Delay::SAVED)?, at)?;
        self.early_calls(arg(Delay::SAVED)?)?;
        self.snapshot(slot, arg(Delay::SAVED)?);
        let dc = match d.d_index() {
            Some(k) => Some(self.eval(arg(k)?)?),
            None => None,
        };
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        let cell = run.state.cells.get(&key).ok_or(here(Internal("a delay with no state")))?;
        read_store(&cell.current, dc.as_ref()).map_err(here)
    }

    /// The delay at `key` saves the value of `expr` for the second phase, which stores it if it is to `keep` it: the place in the order of the saves, which is the one of the second phase, is taken now (`set_keep` says if it is kept).
    pub(super) fn reserve_save(&mut self, key: NodeKey, expr: ExprId, at: Span) -> Result<usize, Stop> {
        let run =
            self.run.as_mut().ok_or(Stop { fault: Fault::Unavailable("a delay outside an instance of a flow"), at })?;
        run.saves.push(Save {
            key,
            expr,
            scope: run.scope.clone(),
            call: None,
            q: 0,
            keep: true,
            field: None,
            snap_parts: Vec::new(),
            reset: false,
            resets: Vec::new(),
            placed: true,
        });
        Ok(run.saves.len() - 1)
    }

    /// A part that the stage `here` makes and that reads a `^name` (S-1244, §11.2, §11.3): the name is a `let` of this stage or below it, so the part is made at the end of the stage, after the `let`s and the output, in the order of the saves of the delays
    /// (the place where it is written), and kept in its field like any part made by a stage before. Once for each replica in a stage.
    pub(super) fn defer_part(&mut self, e: ExprId, here: Clock, known: &Known) -> Result<(), Stop> {
        let (key, at) = (self.key(e, Role::Delay), self.body.ast.expr(e).span);
        // The names of an event it reads are the values where they are written, a `^name` the end of the stage (S-1249).
        let snap_parts = self.event_reads_in(known, e);
        let run = self
            .run
            .as_mut()
            .ok_or(Stop { fault: Internal("a part made at the end of a stage outside an instance"), at })?;
        if !run.saves.iter().any(|s| s.field.is_some() && s.key == key) {
            let scope = run.scope.clone();
            run.saves.push(Save {
                key,
                expr: e,
                scope,
                call: None,
                q: 0,
                keep: true,
                field: Some(here),
                snap_parts,
                reset: false,
                resets: Vec::new(),
                placed: true,
            });
        }
        Ok(())
    }

    pub(super) fn set_keep(&mut self, slot: usize, keep: bool) {
        if let Some(save) = self.run.as_mut().and_then(|r| r.saves.get_mut(slot)) {
            save.keep = keep;
        }
    }

    /// What of the first argument of a delay is done where the delay is written (S-1241, §11.3): the calls of instances in it, in the order written, and the conditions and the resets of the delays with modifiers in it, at any depth (the
    /// ones in the first argument of a delay in it too); the rest of it (the operators, the names, a delay with none) is evaluated where it is saved. In an `if~` or a `match~` the side that selects goes first and then each branch or arm (an
    /// arm not taken with `T.default()` for its bindings), in a `par~` each replica, and a block holds one expression (E0806), which the rest of the walk goes into (S-1233).
    pub(super) fn early_calls(&mut self, e: ExprId) -> Result<(), Stop> {
        let body = self.body;
        if !has_state(&body, e) {
            return Ok(());
        }
        let (at, here) = (body.ast.expr(e).span, |fault| Stop { fault, at: body.ast.expr(e).span });
        match &body.ast.expr(e).kind {
            // A branch or an arm of an `if` or a `match` is no place of an instance (E0811): only what chooses.
            ExprKind::If { cond, tilde: None, .. } => return self.early_calls(*cond),
            ExprKind::Match { scrutinee, tilde: None, .. } => return self.early_calls(*scrutinee),
            // A condition that reads a `^name` has no value yet where the call is written: the branches are all evaluated whatever it is, so their calls go in the order written without it.
            ExprKind::If { .. } if self.selects_with_feedback(e) => {
                let mut link = e;
                while let ExprKind::If { then, else_, .. } = &body.ast.expr(link).kind {
                    self.early_calls(*then)?;
                    match else_ {
                        Some(rest) if matches!(body.ast.expr(*rest).kind, ExprKind::If { .. }) => link = *rest,
                        Some(rest) => return self.early_calls(*rest),
                        None => break,
                    }
                }
                return Ok(());
            }
            ExprKind::If { .. } => return self.through_branches(e, at, |f, x| f.early_calls(x)).map(drop),
            // S-1245: a `^name` in the object or a guard of a `match~` has no value here, and no call of an arm reads a binding of it (E0801). The calls of the arms are left to where the delay saves until the evaluator of W7-11 U2 (§11.3: where they are written).
            ExprKind::Match { .. } if self.selects_with_feedback(e) => return Ok(()),
            ExprKind::Match { .. } => return self.through_arms(e, at, |f, x| f.early_calls(x)).map(drop),
            ExprKind::Par { body: inner, .. } => {
                return self.replicate(e, |_: &()| 0, |f| f.early_calls(*inner)).map(drop);
            }
            ExprKind::Call { kind: CallKind::Flow, args, .. } if chain_of(&body, e).map_err(here)?.is_none() => {
                if let Called::Builtin(FlowBuiltin::Delay(_)) = body.called(e).map_err(here)? {
                    return args.get(Delay::SAVED).map_or(Ok(()), |a| self.early_calls(a.expr));
                }
                self.eval(e)?;
                return Ok(());
            }
            _ if chain_of(&body, e).map_err(here)?.is_some() => {
                // A `d` of a `vdelay~` that reads a `^name` has no value where the delay is written: only the calls in the first argument and the conditions are done here, `d` and the read where it is saved.
                let chain = chain_of(&body, e).map_err(here)?.ok_or(here(Internal("a chain")))?;
                let late_d = match body.called(chain.head).map_err(here)? {
                    Called::Builtin(FlowBuiltin::Delay(d)) => {
                        d.d_index().and_then(|i| args_of(&body, chain.head).get(i).copied())
                    }
                    _ => None,
                }
                .filter(|d| caret(&body, *d));
                if let Some(first) = late_d.and(args_of(&body, chain.head).get(Delay::SAVED).copied()) {
                    self.early_calls(first)?;
                    return chain.conds().try_for_each(|c| self.eval(c).map(drop));
                }
                self.eval(e)?;
                return Ok(());
            }
            _ => {}
        }
        body.ast.sub_exprs(e).into_iter().try_for_each(|x| self.early_calls(x))
    }

    /// Does what selects in the `if~` or `match~` `e` (the conditions of the chain, the object and the guards) read a `^name`?
    fn selects_with_feedback(&self, e: ExprId) -> bool {
        let body = self.body;
        match &body.ast.expr(e).kind {
            ExprKind::If { cond, else_, .. } => {
                caret(&body, *cond)
                    || else_.is_some_and(|r| {
                        matches!(body.ast.expr(r).kind, ExprKind::If { .. }) && self.selects_with_feedback(r)
                    })
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                caret(&body, *scrutinee) || arms.iter().any(|a| a.guard.is_some_and(|g| caret(&body, g)))
            }
            _ => false,
        }
    }

    /// The second phase of a tick: what the delays saved (and the delays inside them), then every one stored.
    // S-1126, S-1154: a panic of what a delay saves (`prev~(10 / x)`, x = 0) is raised here, in the second phase, after the `let`s of the stage, and the saves are in the order the delays are written, a delay in what another saves after it.
    pub(super) fn commit(&mut self, at: Span) -> Result<(), Stop> {
        self.commit_from(at, 0)
    }

    /// `commit` of the saves from the place `from` on: an event stage run inside another stage (`Frame::fire`) stores what it saved, not what the stage it is in has saved so far.
    pub(super) fn commit_from(&mut self, at: Span, from: usize) -> Result<(), Stop> {
        let here = |fault| Stop { fault, at };
        let (mut stores, mut once, mut back) = (Vec::new(), BTreeSet::new(), Vec::new());
        for next in from.. {
            let Some(save) = self.run.as_ref().ok_or(here(Internal("no run")))?.saves.get(next) else { break };
            let (key, expr, scope, call, q) = (save.key.clone(), save.expr, save.scope.clone(), save.call, save.q);
            let (keep, field, parts_snap, reset) = (save.keep, save.field, save.snap_parts.clone(), save.reset);
            let inner = save.resets.clone();
            // The value the part had is stale: it is made again.
            if field.is_some() {
                self.hoisted.get_mut(&expr).into_iter().for_each(|(_, kept)| drop(kept.remove(&key.replicas)));
            }
            let before = self.run.as_ref().map_or(0, |r| r.saves.len());
            let at_key = |rel: &[u32]| key.replicas.iter().chain(rel).copied().collect::<Vec<u32>>();
            let was_parts: Vec<_> = parts_snap
                .iter()
                .map(|(e, rel, _)| (*e, at_key(rel), self.hoisted.get(e).and_then(|k| k.1.get(&at_key(rel))).cloned()))
                .collect();
            let made: Vec<ExprId> =
                parts_snap.iter().map(|(e, ..)| *e).filter(|e| !self.hoisted.contains_key(e)).collect();
            for (e, rel, v) in parts_snap {
                self.hoisted.entry(e).or_insert((Clock::Const, HashMap::new())).1.insert(at_key(&rel), v);
            }
            let value = self.with_bindings(&key.replicas, scope, |f| match call {
                Some(call) => f.eval_in_arms(call, expr),
                None => f.eval(expr),
            });
            made.iter().for_each(|e| drop(self.hoisted.remove(e)));
            for (e, at, was) in was_parts {
                if let Some(k) = self.hoisted.get_mut(&e) {
                    match was {
                        Some(v) => drop(k.1.insert(at, v)),
                        None => drop(k.1.remove(&at)),
                    }
                }
            }
            let value = value?;
            if let Some(clock) = field {
                self.hoisted.entry(expr).or_insert((clock, HashMap::new())).1.insert(key.replicas.clone(), value);
                continue;
            }
            // The delays in what it saved come right after it (S-1154: a delay inside the argument of another is after it, before the ones written later).
            if let Some(run) = self.run.as_mut().filter(|r| r.saves.len() > before) {
                let added = run.saves.split_off(before);
                run.saves.splice(next + 1..next + 1, added);
            }
            // A delay is stored once for a frame: a delay in the object of an arm that `eval_in_arms` evaluates again here saved its value in the frame already, the same one.
            if reset {
                back.push(key.clone());
            }
            back.extend(inner);
            if !keep || !once.insert(key.clone()) {
                continue;
            }
            // A burst is the `2^q` elements of a stream at `sample * 2^q`; any other value is the one the parameter kinds give, each of them.
            let items = match value {
                Value::Burst(es) => counted(&es, q).map(|()| es).map_err(here)?,
                v => vec![v; n_of(q.max(0)) as usize],
            };
            stores.push((key, items));
        }
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.saves.truncate(from);
        for (key, items) in stores {
            match run.state.cells.get_mut(&key).map(|c| &mut c.current) {
                Some(Store::Last(last)) => {
                    *last = items.into_iter().next_back().ok_or(here(Internal("a store of none")))?
                }
                Some(Store::Ring { buf, w }) => {
                    for v in items {
                        buf[*w] = v;
                        *w = (*w + 1) % buf.len();
                    }
                }
                None => return Err(here(Internal("a delay with no state"))),
            }
        }
        // A `reset_if~` that came between the read of a delay and its store takes effect after the store (S-1250 (B)).
        for key in back {
            run.state.cells.get_mut(&key).into_iter().for_each(|c| c.current = c.initial.clone());
        }
        Ok(())
    }

    /// The calls in the conditions of the modifiers of the delay saved at `slot` that are events of another source (`Mod::ev`), done where the delay is written, before it is read: what they give puts it back before the read.
    pub(super) fn early_conditions(&mut self, slot: usize, conds: &[ExprId]) -> Result<(), Stop> {
        let place = |f: &mut Self, placed| {
            f.run.as_mut().and_then(|r| r.saves.get_mut(slot)).iter_mut().for_each(|s| s.placed = placed)
        };
        place(self, false);
        let done = conds.iter().try_for_each(|c| self.early_calls(*c));
        place(self, true);
        done
    }

    /// The delay at `key` goes back to its `init` for a `reset_if~` of an event that comes now (S-1250 (B), §11.3: "flow の値は、`^名前` の値だけを段の終わりのものとして、保存する値を書いた位置で評価して保存したのと同じである"): when it has been read in a stage that has
    /// not stored yet, what it gave was read before the reset and what it stores is the value of its place, so it goes back after the store (`Save::reset`, `commit_from`); else now, before the next read.
    pub(super) fn reset_delay(&mut self, key: &NodeKey, at: Span) -> Result<(), Stop> {
        let body = self.body;
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        let holds = |s: &Save| s.field.is_none() && s.placed && contains(&body, s.expr, key.call);
        if let Some(save) = run.saves.iter_mut().find(|s| s.key == *key && s.field.is_none() && s.placed) {
            save.reset = true;
        } else if let Some(save) = run.saves.iter_mut().find(|s| holds(s)) {
            save.resets.push(key.clone());
        } else {
            let cell = run.state.cells.get_mut(key).ok_or(Stop { fault: Internal("a delay with no state"), at })?;
            cell.current = cell.initial.clone();
        }
        Ok(())
    }

    /// The delays and instances in `e`, the inside first, and the body of a `par~` as a site of its own. A form the
    /// evaluator does not evaluate is `Unavailable` here, at `init`, not looked into.
    fn nodes(&self, e: ExprId, out: &mut Vec<Site<'a>>) -> Result<(), Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(e).span);
        let here = |fault| Stop { fault, at };
        if !evaluates(&self.body, e) {
            return Err(here(Fault::Unavailable("a form of a later unit")));
        }
        // A chain of modifiers is one node, the instance of its head, whose stages and time the boundaries of the chain give (`rate::levels`, S-1207): its arguments are the parts.
        if let Some(chain) = chain_of(&self.body, e).map_err(here)? {
            let ExprKind::Call { args, .. } = &ast.expr(chain.head).kind else {
                return Err(here(Internal("a chain with no head call")));
            };
            args.iter().map(|a| a.expr).chain(chain.conds()).try_for_each(|x| self.nodes(x, out))?;
            return self.sites_of(e, out);
        }
        if let ExprKind::Par { body, .. } = &ast.expr(e).kind {
            let mut inner = Vec::new();
            self.nodes(*body, &mut inner)?;
            if !inner.is_empty() {
                out.push(Site::Par(e, inner));
            }
            return Ok(());
        }
        parts(&self.body, e).into_iter().try_for_each(|x| self.nodes(x, out))?;
        self.sites_of(e, out)
    }

    /// The nodes of the call `e` itself (a chain of modifiers, a delay, an instance), not those of its arguments: what `init` makes where the call is written (S-1233, S-1242).
    fn sites_of(&self, e: ExprId, out: &mut Vec<Site<'a>>) -> Result<(), Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(e).span);
        let here = |fault| Stop { fault, at };
        if let Some(chain) = chain_of(&self.body, e).map_err(here)? {
            let ExprKind::Call { args, .. } = &ast.expr(chain.head).kind else {
                return Err(here(Internal("a chain with no head call")));
            };
            let def = match self.body.called(chain.head).map_err(here)? {
                Called::Flow(def) => def,
                Called::Builtin(FlowBuiltin::Delay(d)) => {
                    out.push(Site::Node(chain.head, Node::Delay(d), args.as_slice()));
                    out.push(Site::Node(chain.head, Node::Mods(chain.bounds), args.as_slice()));
                    return Ok(());
                }
                Called::Builtin(_) => {
                    return Err(here(Internal("a chain whose head is not a call of a flow or a delay")));
                }
            };
            let parts = self.parts_of(def, &chain.bounds, at)?;
            let ports = port_exprs(args.iter().map(|a| a.expr), &parts);
            for (b, lv) in parts.iter().enumerate().skip(1) {
                for &input in &lv.gathers {
                    let k = parts[b - 1].ins[input].ok_or(here(Internal("a gather of an input of no clock")))?;
                    let node = Node::Gather { bound: b, input, k, arg: ports[input] };
                    out.push(Site::Node(chain.head, node, args.as_slice()));
                }
                if lv.deals {
                    out.push(Site::Node(chain.head, Node::Deal { bound: b, m: parts[b - 1].out }, args.as_slice()));
                }
            }
            out.push(Site::Node(chain.head, Node::Instance(def, parts), args.as_slice()));
            return Ok(());
        }
        if let ExprKind::Call { args, kind: CallKind::Flow, .. } = &ast.expr(e).kind {
            match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => out.push(Site::Node(e, Node::Delay(d), args.as_slice())),
                Called::Builtin(_) => {}
                Called::Flow(def) => {
                    out.push(Site::Node(e, Node::Instance(def, self.parts_of(def, &[], at)?), args.as_slice()))
                }
            }
        }
        Ok(())
    }

    /// Is every form in `roots` one the evaluator evaluates (`Unavailable` where one is not, at `init`)?
    pub(super) fn check_forms(&self, roots: &[ExprId]) -> Result<(), Stop> {
        roots.iter().try_for_each(|e| self.nodes(*e, &mut Vec::new()))
    }

    /// The work the call `e` has in the stage `here` (a stage of the walk of `hoist::walk`), at the place it is written (S-1233): at `init` the nodes it makes (its arguments are made before: the init of a delay, the
    /// config of an instance, S-1242), in any other stage the stage of the instance it calls (its arguments and conditions read first, `run_unit`). A call does its work in a stage once (`Inst::done`).
    pub(super) fn work_of(&mut self, e: ExprId, here: Clock, parts: Option<(&Known, ExprId)>) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let stop = |fault| Stop { fault, at };
        let head = chain_of(&self.body, e).map_err(stop)?.map_or(e, |c| c.head);
        if !matches!(&self.body.ast.expr(head).kind, ExprKind::Call { kind: CallKind::Flow, .. }) {
            return Ok(());
        }
        let stage = match here {
            Clock::Init => {
                let mut found = Vec::new();
                self.sites_of(e, &mut found)?;
                return self.build(&found);
            }
            Clock::Block => Stage::Block,
            Clock::Tick(r) => Stage::Tick(r),
            Clock::Event(_) => {
                self.reset_on_event(e, here, parts)?;
                return self.tick_receivers(e, head, here, parts);
            }
            Clock::Const => return Ok(()),
        };
        if !matches!(self.body.called(head).map_err(stop)?, Called::Flow(_)) {
            return Ok(());
        }
        let key = self.key(head, Role::Child);
        if let Some((known, root)) = parts {
            gather_args(self, &key, &[], known, root, here)?;
        }
        let scope = self.run.as_ref().and_then(|r| r.state.children.get(&key)).map(|c| c.scope.clone());
        match scope {
            Some(scope) => self.with_bindings(&[], scope, |f| f.run_unit(&key, stage)),
            None => Err(stop(Internal("an instance with no state"))),
        }
    }

    /// The nodes of `sites`: those of a `par~` once for each replica, with its index bound.
    fn build(&mut self, sites: &[Site<'a>]) -> Result<(), Stop> {
        for site in sites {
            match site {
                Site::Node(e, Node::Delay(d), args) => self.make_cell(*e, *d, args)?,
                Site::Node(e, Node::Gather { bound, input, k, arg }, _) => {
                    self.make_gather(*e, *bound, *input, *k, *arg)?
                }
                Site::Node(e, Node::Deal { bound, m }, _) => self.make_deal(*e, *bound, *m)?,
                Site::Node(e, Node::Instance(def, parts), _) => self.make_child(*e, *def, parts.clone())?,
                Site::Node(e, Node::Mods(bounds), _) => self.make_mods(*e, bounds)?,
                Site::Par(e, inner) => drop(self.replicate(*e, |_| 0, |f| f.build(inner))?),
            }
        }
        Ok(())
    }

    /// A `let` keeps the value `v` (its previous one is given back): the places it holds beyond the one of its step count in the tree.
    pub(super) fn keep_places(&mut self, init: ExprId, v: &Value) -> Result<(), Stop> {
        let Some(run) = self.run.as_mut() else { return Ok(()) };
        let (more, old) = (v.places() - 1, run.state.held.get(&init).copied().unwrap_or(0));
        run.used = run.used.saturating_sub(old);
        let held = self.hold(Some(more), self.body.ast.expr(init).span);
        // The record of the `let` changes only when its new value is held: else the old value stays, and so does its
        // count (a call stopped at the limit leaves `held` and `used` as one).
        if let Some(run) = self.run.as_mut() {
            match held {
                Ok(()) => drop(run.state.held.insert(init, more)),
                Err(_) => run.used += old,
            }
        }
        held
    }

    /// Adds `places` (none: more than a count holds) to those of the whole tree, which `Limits::most` holds.
    pub(super) fn hold(&mut self, places: Option<usize>, at: Span) -> Result<(), Stop> {
        let more = Stop { fault: Fault::Unavailable("the delays and instances are more than the evaluator holds"), at };
        let (limits, run) = (self.limits, self.run.as_mut().ok_or(more)?);
        run.used = places.and_then(|p| p.checked_add(run.used)).filter(|u| limits.holds(*u)).ok_or(more)?;
        Ok(())
    }

    /// The node of the delay `e`; its places are held with those of the nodes before it (the whole tree) before it is made.
    #[inline(never)]
    fn make_cell(&mut self, e: ExprId, d: Delay, args: &[Arg]) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        // An `init` argument that reads a `^name` has no value where the delay is written: the cell starts from `T.default()` and the argument is made at the end of `init` (S-1244, `Frame::finish_cells`).
        let arg = args.get(d.init_index()).map(|a| a.expr);
        let late = arg.filter(|a| caret(&self.body, *a));
        let given = match arg {
            Some(a) if late.is_none() => Some(self.eval_staged(e, a, Stage::Init)?),
            _ => None,
        };
        let shape = match given {
            Some(_) => None,
            None => Some(self.shape(self.body.ty(e).map_err(here)?, at)?),
        };
        let len = match d.const_index().and_then(|i| args.get(i)).map(|a| self.eval(a.expr)).transpose()? {
            Some(Value::Int(_, n, _)) => usize::try_from(n + i128::from(d == Delay::Variable)).ok(),
            _ => Some(1),
        };
        let one = given.as_ref().map_or_else(|| shape.as_ref().map_or(1, Shape::places), Value::places);
        self.hold(len.and_then(|n| n.checked_mul(one)), at)?;
        let init = given.or_else(|| shape.and_then(|s| s.default_value()));
        let init = init.ok_or(here(Internal("a delay of a type with no default")))?;
        let n = len.ok_or(here(Internal("a length that holds")))?;
        let store = if d == Delay::Prev { Store::Last(init) } else { Store::Ring { buf: vec![init; n], w: 0 } };
        let key = self.key(e, Role::Delay);
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        run.state.cells.insert(key.clone(), Cell { initial: store.clone(), current: store });
        if let Some(a) = late {
            run.late_cells.push((key, a, run.scope.clone()));
        }
        Ok(())
    }

    /// The cells whose `init` argument reads a `^name` (S-1244): made at the end of `init`, after the `let`s, the value for each place the cell holds.
    pub(super) fn finish_cells(&mut self) -> Result<(), Stop> {
        let late = self.run.as_mut().map(|r| std::mem::take(&mut r.late_cells)).unwrap_or_default();
        for (key, arg, scope) in late {
            let v = self.with_bindings(&key.replicas, scope, |f| f.eval(arg))?;
            let cell = self.run.as_mut().and_then(|r| r.state.cells.get_mut(&key));
            let at = self.body.ast.expr(arg).span;
            let cell = cell.ok_or(Stop { fault: Internal("a delay with no state"), at })?;
            for store in [&mut cell.initial, &mut cell.current] {
                match store {
                    Store::Last(last) => *last = v.clone(),
                    Store::Ring { buf, .. } => buf.iter_mut().for_each(|x| *x = v.clone()),
                }
            }
        }
        Ok(())
    }

    /// The node of the ring of the port number `input` (at `sample * 2^k`, of the expression `arg`: an argument of the head or a condition) of the chain whose head is `e`: the `2^k` elements of its argument that came before,
    /// `T.default()` at first (§11.9: position 0 has no sample before it). It is a node of the call: what the argument is does not matter to it (it may be a delay itself).
    fn make_gather(&mut self, e: ExprId, bound: usize, input: usize, k: i32, arg: ExprId) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let shape = self.shape(self.body.ty(arg).map_err(here)?, at)?;
        let n = n_of(k) as usize;
        self.hold(n.checked_mul(shape.places()), at)?;
        let one = shape.default_value().ok_or(here(Internal("a gathered type with no default")))?;
        let store = Store::Ring { buf: vec![one; n], w: 0 };
        let key = self.key(e, Role::Gather { bound, input });
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
        Ok(())
    }

    /// The node of the array that the output (at `sample * 2^m`) of the chain whose head is `e` deals: `T.default()` until the first tick makes it.
    fn make_deal(&mut self, e: ExprId, bound: usize, m: i32) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let shape = self.shape(self.body.ty(e).map_err(here)?, at)?;
        let n = n_of(m) as usize;
        self.hold(n.checked_mul(shape.places()), at)?;
        let one = shape.default_value().ok_or(here(Internal("a dealt type with no default")))?;
        let store = Store::Last(Value::Array(vec![one; n]));
        let key = self.key(e, Role::Deal(bound));
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
        Ok(())
    }

    /// A new instance of the flow `def` for a call at `at`: its places (8 and one for each step of its body) are held first.
    #[inline(never)]
    fn new_child(&mut self, def: DefId, at: Span) -> Result<(Inst, &'a FlowDef), Stop> {
        let plans = self.run.as_ref().map(|r| r.plans.clone()).ok_or(Stop { fault: Internal("no run"), at })?;
        let (inst, _, decl) = Inst::plan(self.body.view, def, &plans)?;
        self.hold(Some(INSTANCE + inst.steps.len()), at)?;
        Ok((inst, decl))
    }

    /// The parts of the chain of the boundaries `bounds` (innermost first) of the flow `def`.
    fn parts_of(&self, def: DefId, bounds: &[Bound], at: Span) -> Result<Rc<[Level]>, Stop> {
        let plans = self.run.as_ref().map(|r| r.plans.clone()).ok_or(Stop { fault: Internal("no run"), at })?;
        let slow = Inst::planned(self.body.view, def, &plans)?.slow;
        let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
        // The clock of a condition of a modifier is that of the plan of this body (`rate::slow_ticks`).
        let clock = |c| {
            let conds = Inst::planned(self.body.view, self.body.def, &plans).map_err(|stop| stop.fault)?.conds;
            conds.get(&c).copied().ok_or(Internal("a condition of a modifier with no clock"))
        };
        levels(decl, &slow, bounds, &clock).map_err(|fault| Stop { fault, at })
    }

    /// The instance of the flow `def` that the call `e` makes: kept in the state, then its `init` (the arguments of that clock).
    fn make_child(&mut self, e: ExprId, def: DefId, parts: Rc<[Level]>) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let (mut inst, decl) = self.new_child(def, at)?;
        inst.bursts = vec![Vec::new(); parts.len()];
        inst.fed = vec![Value::Unit; parts[parts.len() - 1].ins.len()];
        inst.whens = self.gates(e, &parts, at)?;
        inst.levels = parts;
        let key = self.key(e, Role::Child);
        let config = self.param_inputs(&key, decl, Stage::Init)?;
        inst.scope = self.run.as_ref().map(|r| r.scope.clone()).unwrap_or_default();
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        run.state.children.insert(key.clone(), inst);
        self.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Init, &config))?;
        self.start_events(&key, e)
    }

    /// What each `when~` and `reset_if~` of the chain whose head is `e` keeps (§11.10): the output a `when~` holds is `T.default()` at first, a burst of them for an output at `sample * N` (S-1222), and its places are held first.
    fn gates(&mut self, e: ExprId, parts: &[Level], at: Span) -> Result<Vec<Option<Gate>>, Stop> {
        let here = |fault| Stop { fault, at };
        let mut gates = Vec::new();
        for lv in parts {
            if lv.when().is_none() {
                gates.push(lv.reset().map(|_| Gate::new(Value::Unit)));
                continue;
            }
            let shape = self.shape(self.body.ty(e).map_err(here)?, at)?;
            let n = if lv.out > 0 { n_of(lv.out) as usize } else { 1 };
            self.hold(n.checked_mul(shape.places()), at)?;
            let one = shape.default_value().ok_or(here(Internal("a held type with no default")))?;
            gates.push(Some(Gate::new(if lv.out > 0 { Value::Burst(vec![one; n]) } else { one })));
        }
        Ok(gates)
    }

    /// The fields of the instance at `key` and of those it calls that a tick slower than `sample` writes and a faster stage reads, at `T.default()` (§11.10, §11.3: its `let`s and inputs of such a tick, the parts of its
    /// body that such a stage made, and its output where its caller reads it between its ticks), for `reset_if~`. A type with no default is not read by a faster stage (E0816), so its field is left as it is.
    /// `fed` is for an instance whose caller is in the part too: what it keeps of its caller's values of a tick (`Inst::fed`, which a `when~` reads in its W, and the conditions of its chain) is that caller's field, and goes back with it.
    pub(super) fn restart(&mut self, key: &NodeKey, fed: bool) -> Result<(), Stop> {
        self.in_child(key, |f, inst, decl| {
            let at = f.body.ast.expr(decl.body).span;
            let here = |fault| Stop { fault, at };
            let slow = |c: Clock| matches!(c.rooted(), Clock::Tick(r) if r < 0) || matches!(c, Clock::Event(_));
            let levels = inst.levels.clone();
            let top = levels.last().ok_or(here(Internal("an instance with no parts")))?;
            for (g, gate) in levels.iter().map(|l| l.guard).zip(&mut inst.whens) {
                if let (true, Some(g), Some(gate)) = (fed, g.filter(|g| g.at < 0), gate) {
                    gate.cond = Value::Bool(false);
                    g.port.into_iter().for_each(|n| inst.fed[n] = Value::Bool(false));
                }
            }
            for (n, i) in decl.inputs.iter().enumerate() {
                let mine = matches!(input_stage(i).map_err(here)?, Stage::Tick(r) if r < 0)
                    || matches!(input_stage(i).map_err(here)?, Stage::Event(_));
                let theirs = fed && top.ins[n].is_some_and(|q| q < 0) && !top.gathers.contains(&n);
                let Some(d) = f.shape(f.body.view.ty(i.ty), at)?.default_value().filter(|_| mine || theirs) else {
                    continue;
                };
                if theirs {
                    inst.fed[n] = d.clone();
                }
                if mine {
                    f.locals.insert(f.body.input(&i.name).ok_or(here(Internal("an input with no local")))?, d);
                }
            }
            // The output of an instance made at a tick slower than `sample`. Without it nothing shows (a mutant passes the gate and `heavy_`): the condition of a `reset_if~` is not faster than the output (E0815), so the work that makes it comes after the reset, and one that a `when~` stops reads `held`.
            let between = inst.levels.last().is_some_and(|top| top.made < 0);
            for st in inst.steps.iter().filter(|st| !st.emits && (slow(st.clock) || (st.pat.is_none() && between))) {
                let ty = f.body.ty(st.init).map_err(here)?;
                match (st.pat, f.shape(ty, at)?.default_value()) {
                    (Some(pat), Some(d)) => f.destructure(pat, &d, ty)?,
                    (None, Some(d)) => inst.out = d,
                    _ => {}
                }
            }
            let made: Vec<ExprId> = f.hoisted.iter().filter(|(_, (c, _))| slow(*c)).map(|(e, _)| *e).collect();
            for e in made {
                let d = f.shape(f.body.ty(e).map_err(here)?, at)?.default_value();
                if let (Some(d), Some((_, vs))) = (d, f.hoisted.get_mut(&e)) {
                    vs.values_mut().for_each(|v| *v = d.clone());
                }
            }
            let calls: Vec<NodeKey> =
                f.run.as_ref().map(|r| r.state.children.keys().cloned().collect()).unwrap_or_default();
            calls.iter().try_for_each(|k| f.restart(k, true))
        })
    }

    /// The arguments of the call `call` of the flow `decl`: one for each of its inputs (the checker sees to it).
    pub(super) fn args_of_call(&self, call: ExprId, decl: &FlowDef) -> Result<&'a [Arg], Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(call).span);
        match &ast.expr(call).kind {
            ExprKind::Call { args, .. } if args.len() == decl.inputs.len() => Ok(args),
            _ => Err(Stop {
                fault: Internal("an instance that is not a call of as many arguments as it has inputs"),
                at,
            }),
        }
    }

    /// The arguments of the call at `key` that are inputs of `decl` at `stage` (`init` or `block`: the parameter kinds), by input name, evaluated here from the left (S-1131: the bindings of an arm they read are those of the stage).
    /// The inputs at a tick are read by `feed`, and what a boundary gathers is its ring (`ring`).
    pub(super) fn param_inputs(
        &mut self,
        key: &NodeKey,
        decl: &'a FlowDef,
        stage: Stage,
    ) -> Result<Vec<(&'a str, Value)>, Stop> {
        let here = |fault| Stop { fault, at: self.body.ast.expr(key.call).span };
        let args = self.args_of_call(key.call, decl)?;
        let mut mine = Vec::new();
        for (i, a) in decl.inputs.iter().zip(args) {
            if input_stage(i).map_err(here)? == stage {
                mine.push((i.name.as_str(), self.eval_staged(key.call, a.expr, stage)?));
            }
        }
        Ok(mine)
    }

    /// `go` on the instance at `key` in a frame of its own (the host, limits, time and places of this one); kept again whatever.
    pub(super) fn in_child<R>(
        &mut self,
        key: &NodeKey,
        go: impl FnOnce(&mut Frame<'a>, &mut Inst, &'a FlowDef) -> Result<R, Stop>,
    ) -> Result<R, Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        if self.low_stack() {
            return Err(here(LOW_STACK));
        }
        let view = self.body.view;
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("an instance outside an instance of a flow")))?;
        let (used, plans) = (run.used, run.plans.clone());
        let (def, parts) = run
            .state
            .children
            .get(key)
            .map(|c| (c.def, c.levels.clone()))
            .ok_or(here(Internal("an instance with no state")))?;
        // The instance reads the time of its rate (`sample_rate()` of `init` and of `block` too): its caller's for no modifier, 1/N and N times for each boundary of a chain.
        let ctx = child_time(&parts, run.ctx);
        let (body, decl) = (view.body(def).map_err(here)?, view.flow(def).map_err(here)?);
        let mut inst = run.state.children.remove(key).ok_or(here(Internal("an instance with no state")))?;
        let mut f = inst.frame(body, ctx, used, plans, self.host.take());
        f.limits = self.limits;
        let done = go(&mut f, &mut inst, decl);
        self.host = f.host.take();
        let used = f.run.as_ref().map_or(used, |r| r.used);
        let kept = inst.keep(f, at);
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.used = used;
        run.state.children.insert(key.clone(), inst);
        let value = done?;
        kept.map(|()| value)
    }

    /// The argument that an input of `sample * N` of the last `.down~` boundary of a chain gathers is stored at the end of each `sample` frame of this one, the `2^q` elements of its stream at the clock `q = k + r` (§11.9: the frame
    /// after a tick reads it, the position's own value is not in); a stream slower than `sample` gives one element at each tick of its own, `sample / 2^-q`. The rings of the boundaries inside are written by the frames of the chain (`run_level`).
    /// The value is what the second phase (`commit`) evaluates the argument to, which for a part that is kept is the value that its stage made (the delays in it are read before they are saved, at their own clocks).
    pub(super) fn save_gathers(&mut self, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a sample stage with no run"), at: whole })?;
        let (ctx, calls): (_, Vec<_>) = (
            run.ctx,
            run.state.children.iter().map(|(k, c)| (k.clone(), c.def, c.levels.clone(), c.scope.clone())).collect(),
        );
        for (key, def, parts, scope) in calls {
            let here = |fault| Stop { fault, at: self.body.ast.expr(key.call).span };
            let decl = self.body.view.flow(def).map_err(here)?;
            let args = port_exprs(self.args_of_call(key.call, decl)?.iter().map(|a| a.expr), &parts);
            let top = &parts[parts.len() - 1];
            for &n in &top.gathers {
                let q = top.ins[n].ok_or(here(Internal("a gather of an input of no clock")))?;
                if q < 0 && !on_tick(ctx, q) {
                    continue;
                }
                let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
                let role = Role::Gather { bound: parts.len() - 1, input: n };
                let save = Save {
                    key: key.role(role),
                    expr: args[n],
                    scope: scope.clone(),
                    call: Some(key.call),
                    q,
                    keep: true,
                    field: None,
                    snap_parts: Vec::new(),
                    reset: false,
                    resets: Vec::new(),
                    placed: true,
                };
                run.saves.push(save);
            }
        }
        Ok(())
    }

    /// The type as far as its default needs it (§6.4); a field a struct declares a value for has it.
    pub(super) fn shape(&mut self, ty: &Ty, at: Span) -> Result<Shape, Stop> {
        let here = |fault| Stop { fault, at };
        let view = self.body.view;
        Ok(match ty {
            Ty::Tuple(ts) => Shape::Tuple(ts.iter().map(|t| self.shape(view.ty(*t), at)).collect::<Result<_, _>>()?),
            Ty::Array(t, Len::Const(n)) if self.limits.holds(*n as usize) => {
                Shape::Array(Box::new(self.shape(view.ty(*t), at)?), *n as usize)
            }
            // A `Default` written by hand: its `default()` is called (§6.4).
            Ty::Named(def, _) if view.default_by_hand(*def) => Shape::Given(self.hand_default(*def, at)?),
            Ty::Named(def, _) => {
                let mut fields = Vec::new();
                for f in view.struct_fields(*def).map_err(here)? {
                    let declared = f.default.map(|c| self.const_def(c, view.ty(f.ty), at)).transpose()?;
                    // A field that declares a value has it, and the shape of its type is not asked for (the type may have no `Default`).
                    let shape = match &declared {
                        Some(v) => Shape::Given(v.clone()),
                        None => self.shape(view.ty(f.ty), at)?,
                    };
                    fields.push((declared, shape));
                }
                Shape::Struct(fields)
            }
            ty => Shape::Scalar(Scalar::of(ty).ok_or(here(Fault::Unavailable("a type with no default here")))?),
        })
    }
}

/// Does `root` hold the expression `target`?
fn contains(body: &super::sema_view::Body, root: ExprId, target: ExprId) -> bool {
    root == target || body.ast.sub_exprs(root).into_iter().any(|x| contains(body, x, target))
}
