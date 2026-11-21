//! The state of a flow instance and the delays that use it (§11.4, §11.6): a tree of cells, one for each place a
//! delay is called (the call, and the replica of each `par~` around it, U2), the three delays by their formulas, and the
//! two phases of a tick: the delays read their stored value first, and what they store is evaluated after the body and
//! all of it stored at once (`^name` is read in the second phase, when the `let` it names has its value). The instances
//! a flow calls are the `children` of the tree: each is a whole [`Inst`], run in a frame of its own (`in_child`) at the
//! time of its caller (§11.5), and counted in the limit of the tree.

use std::collections::BTreeMap;

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::flow_names::{Delay, FlowBuiltin};
use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{DefId, LocalId, Ty};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};

use super::call::parts;
use super::expr::{Eval, Frame, LOW_STACK, Stop, evaluates};
use super::flow::{Ctx, Inst, Plans, enter, run_frame, run_ticks};
use super::rate::{
    Chain, Feed, Out, at_callers_time, chain_of, feed, frames, on_tick, out_of, out_ratio, phase, time_of,
};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Called, Stage, input_ratio, input_stage};
use super::value::{IntKind, Scalar, Shape, Value};

/// The places an instance takes in the limit of the tree (`Limits::most`): some 100 thousand instances, not 2^20.
const INSTANCE: usize = 8;

/// The positions of the arguments of a delay that the evaluator reads by place: the value it saves (the first, whose clock is the clock of the delay, §11.4)
/// and the `d` of `vdelay~(e, d, MAX)`. The registry (`Delay`) has the positions of the constant and of `init` only.
pub(super) const SAVED: usize = 0;
const D: usize = 1;

/// Where a node of the state is: the call that makes it (for the ring of a gather, the argument it takes, which may be a delay itself: `gather` tells them apart), and the
/// replica of each `par~` it is in (U2).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKey {
    pub call: ExprId,
    pub replicas: Vec<u32>,
    pub gather: bool,
}

impl NodeKey {
    /// The ring that the argument `arg` of a chain gathers, in the replicas `replicas`.
    fn gathered(arg: ExprId, replicas: &[u32]) -> NodeKey {
        NodeKey { call: arg, replicas: replicas.to_vec(), gather: true }
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

/// The state of one instance: its own nodes, and the instances it calls (whole, with their `let`s).
#[derive(Debug, Default)]
pub struct InstState {
    pub cells: BTreeMap<NodeKey, Cell>,
    pub children: BTreeMap<NodeKey, Inst>,
    /// What each `let` (by its initializer) holds beyond the one place of its step: part of the tree's places.
    held: BTreeMap<ExprId, usize>,
}

impl InstState {
    /// Every node back to what it started from (§11.6 `reset`), the instances inside too.
    pub fn reset(&mut self) {
        self.cells.values_mut().for_each(|c| c.current = c.initial.clone());
        self.children.values_mut().for_each(|c| c.state.reset());
    }
}

/// What a delay saves this tick: where, the expression whose value it is, and the bindings it is read under (the index
/// of each `par~` it is in and the locals an arm of a `match~` binds: they are not what they were when it is stored).
struct Save {
    key: NodeKey,
    expr: ExprId,
    scope: Vec<(LocalId, Value)>,
}

/// What an evaluation of a flow body holds besides its locals: the state, what the delays save this tick, the time it is
/// at (an instance reads its caller's, one that a chain runs the time of its rate, `rate::time_of`), the places of the tree made so far and
/// the plans of its flows.
pub struct Run {
    pub state: InstState,
    saves: Vec<Save>,
    pub ctx: Ctx,
    pub(super) used: usize,
    plans: Plans,
    /// The replica of each `par~` the evaluation is inside of, and the bindings of those (`i`, an arm of a `match~`).
    pub(super) replicas: Vec<u32>,
    pub(super) scope: Vec<(LocalId, Value)>,
}

impl Run {
    pub(super) fn new(state: InstState, ctx: Ctx, used: usize, plans: Plans) -> Run {
        Run { state, saves: Vec::new(), ctx, used, plans, replicas: Vec::new(), scope: Vec::new() }
    }
}

/// What the arguments of a chain give its instance: the inputs of `sample` with how each is fed, and the inputs of the ticks, by name.
type ChainInputs<'a> = (Vec<(&'a str, Feed, Value)>, Vec<(&'a str, Value)>);

enum Node {
    Delay(Delay),
    /// The ring of the `frames` values of the argument (each of `per` elements for a `sample * per`) that an input of a `.down~` chain gathers (§11.9): at the argument.
    Gather {
        frames: usize,
        per: usize,
    },
    /// The flow, and the ratio of the chain of modifiers it is the head of (0 for none).
    Instance(DefId, i32),
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

impl<'a> Frame<'a> {
    /// The forms of a flow body that have state or a time: the calls of a flow and `^name` (the local, read in the second
    /// phase). One door for `Frame::form`.
    #[inline(never)]
    pub(super) fn stateful(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        if let Some(chain) = chain_of(&self.body, e).map_err(here)? {
            return self.chained(chain, at);
        }
        match &self.body.ast.expr(e).kind {
            ExprKind::Feedback(_) => self.name(e, at),
            ExprKind::Call { args, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => self.delay(e, d, args, at),
                Called::Builtin(FlowBuiltin::SampleRate) => Ok(Value::F32(self.time(at)?.sample_rate)),
                // S-1127 (1), §11.4: the first tick after `init` or `reset` reads 0, and each tick adds 1.
                Called::Builtin(FlowBuiltin::SampleTick) => Ok(Value::int(IntKind::U32, self.time(at)?.tick.into())),
                Called::Flow(def) => self.instance(e, def, at),
            },
            _ => Err(here(Internal("not a stateful form"))),
        }
    }

    /// The node of the call `call` here: in the replica of each `par~` around it (U2).
    pub(super) fn key(&self, call: ExprId) -> NodeKey {
        NodeKey { call, replicas: self.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default(), gather: false }
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
    fn time(&self, at: Span) -> Result<Ctx, Stop> {
        let run = self.run.as_ref();
        run.map(|r| r.ctx).ok_or(Stop { fault: Fault::Unavailable("a time outside an instance of a flow"), at })
    }

    /// A delay called: its output now (§11.4: the value it stored, whatever the delays inside what it will save do),
    /// and the saving of its `e` for the second phase.
    fn delay(&mut self, e: ExprId, d: Delay, args: &[Arg], at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let arg = |i: usize| args.get(i).map(|a| a.expr).ok_or(here(Internal("a delay with too few arguments")));
        let dc = if d == Delay::Variable { Some(self.eval(arg(D)?)?) } else { None };
        let key = self.key(e);
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        let cell = run.state.cells.get(&key).ok_or(here(Internal("a delay with no state")))?;
        let out = match (&cell.current, &dc) {
            (Store::Last(v), _) => v.clone(),
            (Store::Ring { buf, w }, None) => buf[*w].clone(),
            (Store::Ring { buf, w }, Some(dc)) => interpolate(buf, *w, dc).map_err(here)?,
        };
        run.saves.push(Save { key, expr: arg(SAVED)?, scope: run.scope.clone() });
        Ok(out)
    }

    /// The second phase of a tick: what the delays saved (and the delays inside them), then every one stored.
    // SPEC-GAP(S-1126): a panic of what a delay saves (`prev~(10 / x)`, x = 0) is raised here, in the second phase, so a panic of
    // a `let` written after the delay (`5 / x`) comes first; the other reading evaluates the saved value where it is written.
    pub(super) fn commit(&mut self, at: Span) -> Result<(), Stop> {
        let here = |fault| Stop { fault, at };
        let mut stores = Vec::new();
        while let Some(save) = self.run.as_ref().ok_or(here(Internal("no run")))?.saves.get(stores.len()) {
            let (key, expr, scope) = (save.key.clone(), save.expr, save.scope.clone());
            let value = self.with_bindings(&key.replicas, scope, |f| f.eval(expr))?;
            stores.push((key, value));
        }
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.saves.clear();
        for (key, v) in stores {
            match run.state.cells.get_mut(&key).map(|c| &mut c.current) {
                Some(Store::Last(last)) => *last = v,
                Some(Store::Ring { buf, w }) => {
                    buf[*w] = v;
                    *w = (*w + 1) % buf.len();
                }
                None => return Err(here(Internal("a delay with no state"))),
            }
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
        // A chain of modifiers is one node, the instance of its head, which the ratio of the chain says the time of: its arguments are the parts.
        if let Some(chain) = chain_of(&self.body, e).map_err(here)? {
            let ExprKind::Call { args, .. } = &ast.expr(chain.head).kind else {
                return Err(here(Internal("a chain with no head call")));
            };
            let Called::Flow(def) = self.body.called(chain.head).map_err(here)? else {
                return Err(here(Fault::Unavailable("a modifier of a delay")));
            };
            args.iter().try_for_each(|a| self.nodes(a.expr, out))?;
            let decl = self.body.view.flow(def).map_err(here)?;
            if !at_callers_time(chain.ratio) {
                out_of(out_ratio(decl).map_err(here)?, chain.ratio).map_err(here)?;
                for (i, a) in decl.inputs.iter().zip(args) {
                    let k = input_ratio(i);
                    if let Some(Feed::Gather { frames, per }) =
                        k.map(|k| feed(k, chain.ratio)).transpose().map_err(here)?
                    {
                        out.push(Site::Node(a.expr, Node::Gather { frames, per }, args.as_slice()));
                    }
                }
            }
            out.push(Site::Node(chain.head, Node::Instance(def, chain.ratio), args.as_slice()));
            return Ok(());
        }
        let node = match &ast.expr(e).kind {
            ExprKind::Par { body, .. } => {
                let mut inner = Vec::new();
                self.nodes(*body, &mut inner)?;
                if !inner.is_empty() {
                    out.push(Site::Par(e, inner));
                }
                return Ok(());
            }
            ExprKind::Call { args, kind: CallKind::Flow, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => Some(Site::Node(e, Node::Delay(d), args.as_slice())),
                Called::Builtin(_) => None,
                Called::Flow(def) => Some(Site::Node(e, Node::Instance(def, 0), args.as_slice())),
            },
            _ => None,
        };
        parts(&self.body, e).into_iter().try_for_each(|x| self.nodes(x, out))?;
        out.extend(node);
        Ok(())
    }

    /// The nodes of the delays and instances in the expressions `roots`, made as they start (§11.3: `init` is evaluated
    /// once): a delay with its value or `T.default()` (§6.4) and its ring `N` long (`MAX + 1` for `vdelay~`), an instance
    /// with its own `init`.
    pub(super) fn make_cells(&mut self, roots: &[ExprId]) -> Result<(), Stop> {
        let mut found = Vec::new();
        roots.iter().try_for_each(|e| self.nodes(*e, &mut found))?;
        self.build(&found)
    }

    /// The nodes of `sites`: those of a `par~` once for each replica, with its index bound.
    fn build(&mut self, sites: &[Site<'a>]) -> Result<(), Stop> {
        for site in sites {
            match site {
                Site::Node(e, Node::Delay(d), args) => self.make_cell(*e, *d, args)?,
                Site::Node(e, Node::Gather { frames, per }, _) => self.make_gather(*e, *frames, *per)?,
                Site::Node(e, Node::Instance(def, rate), _) => self.make_child(*e, *def, *rate)?,
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
    fn hold(&mut self, places: Option<usize>, at: Span) -> Result<(), Stop> {
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
        let given = args.get(d.init_index()).map(|a| self.eval_staged(e, a.expr, Stage::Init)).transpose()?;
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
        let key = self.key(e);
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
        Ok(())
    }

    /// The node of the argument `e` that an input of `sample * N` gathers: a ring of `frames` values of it (an array of `per` of its type for a `sample * per`), `T.default()` at first (§11.9:
    /// position 0 has no sample before it).
    fn make_gather(&mut self, e: ExprId, frames: usize, per: usize) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let shape = self.shape(self.body.ty(e).map_err(here)?, at)?;
        self.hold(frames.checked_mul(per).and_then(|n| n.checked_mul(shape.places())), at)?;
        let one = shape.default_value().ok_or(here(Internal("a gathered type with no default")))?;
        let init = if per > 1 { Value::Array(vec![one; per]) } else { one };
        let store = Store::Ring { buf: vec![init; frames], w: 0 };
        let key = NodeKey::gathered(e, &self.key(e).replicas);
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

    /// The instance of the flow `def` that the call `e` makes: kept in the state, then its `init` (the arguments of that clock).
    fn make_child(&mut self, e: ExprId, def: DefId, rate: i32) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let (mut inst, decl) = self.new_child(def, at)?;
        inst.rate = rate;
        let config = self.inputs_of(e, decl, Stage::Init)?;
        let key = self.key(e);
        inst.scope = self.run.as_ref().map(|r| r.scope.clone()).unwrap_or_default();
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        run.state.children.insert(key.clone(), inst);
        self.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Init, &config))
    }

    /// The arguments of the call `call` that are inputs of `decl` at `stage`, by input name, evaluated here from the left.
    fn inputs_of(&mut self, call: ExprId, decl: &'a FlowDef, stage: Stage) -> Result<Vec<(&'a str, Value)>, Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(call).span);
        let ExprKind::Call { args, .. } = &ast.expr(call).kind else {
            return Err(Stop { fault: Internal("an instance that is not a call"), at });
        };
        let mut mine = Vec::new();
        for (i, a) in decl.inputs.iter().zip(args) {
            if input_stage(i).map_err(|fault| Stop { fault, at })? == stage {
                mine.push((i.name.as_str(), self.eval_staged(call, a.expr, stage)?));
            }
        }
        Ok(mine)
    }

    /// `go` on the instance at `key` in a frame of its own (the host, limits, time and places of this one); kept again whatever.
    fn in_child<R>(
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
        let (def, rate) =
            run.state.children.get(key).map(|c| (c.def, c.rate)).ok_or(here(Internal("an instance with no state")))?;
        // The instance reads the time of its rate (`sample_rate()` of `init` and of `block` too): its caller's for no modifier, 1/N and N times for a chain.
        let ctx = time_of(run.ctx, rate, 0);
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

    /// A call of a flow (§11.5): its instance runs a frame on the `sample` arguments, and its output is the value. One whose output is a tick (`-> F32 at (sample / 4)`)
    /// is read at that tick: the call is evaluated there, its stage of the tick runs here with its inputs (the `sample` stage of the instance runs at each frame, `sample_nodes`).
    fn instance(&mut self, e: ExprId, def: DefId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let decl = self.body.view.flow(def).map_err(here)?;
        let m = out_ratio(decl).map_err(here)?;
        if m < 0 {
            let on = on_tick(self.time(at)?, m);
            let ticks = if on { self.inputs_of(e, decl, Stage::Tick(m))? } else { Vec::new() };
            let ticks: Vec<(&str, &Value)> = ticks.iter().map(|(n, v)| (*n, v)).collect();
            return self.in_child(&self.key(e), |f, inst, decl| {
                if on {
                    enter(f, inst, decl, Stage::Tick(m), &ticks)?;
                }
                Ok(inst.out.clone())
            });
        }
        let given = self.inputs_of(e, decl, Stage::Sample)?;
        let given: Vec<(&str, &Value)> = given.iter().map(|(n, v)| (*n, v)).collect();
        self.in_child(&self.key(e), |f, inst, decl| {
            enter(f, inst, decl, Stage::Sample, &given)?;
            Ok(inst.out.clone())
        })
    }

    /// A chain of modifiers called (§11.9): the instance of its head runs at the rate of the chain, in the time `time_of` gives it: one frame at 1/N for `.down~(N)`
    /// (when the tick is on), N frames for `.up~(N)`. The arguments are read in the frame of the call: an input of `sample * N` of a `.down~` chain takes the values its
    /// caller's frames had before this tick (the ring), one of `sample` of `.up~(N)` the j-th of the array its argument is at the j-th run. The value is the output of the
    /// run, an array of the N of them for `.up~(N)`, and for an output of `sample * N` of a `.down~` chain the elements of the array of the last tick that this frame of the caller reads.
    /// An output at a tick (`sample / N`) is read at its tick: the ticks of the instance up to it run here, and the rest of its frames at each frame of the chain (`sample_nodes`).
    fn chained(&mut self, chain: Chain, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let Called::Flow(def) = self.body.called(chain.head).map_err(here)? else {
            return Err(here(Fault::Unavailable("a modifier of a delay")));
        };
        if at_callers_time(chain.ratio) {
            return self.instance(chain.head, def, at);
        }
        let (decl, r, caller, key) =
            (self.body.view.flow(def).map_err(here)?, chain.ratio, self.time(at)?, self.key(chain.head));
        let m = out_ratio(decl).map_err(here)?;
        let out = out_of(m, r).map_err(here)?;
        if m < 0 {
            if on_tick(caller, m + r) {
                self.chain_part(&key, def, r, |x| x <= m, false)?;
            }
            return self.held(&key, out, caller, at);
        }
        if r < 0 && !on_tick(caller, r) {
            return self.held(&key, out, caller, at);
        }
        let (sample, ticks) = self.chain_inputs(&key, decl, r, |_| true, true)?;
        let mut outs = Vec::new();
        for j in 0..frames(r) {
            let given: Vec<(&str, Value)> = sample
                .iter()
                .map(|(n, how, v)| match (how, v) {
                    (Feed::Each, Value::Array(vs)) => vs.get(j as usize).map(|v| (*n, v.clone())),
                    _ => Some((*n, v.clone())),
                })
                .collect::<Option<_>>()
                .ok_or(here(Internal("an array of `sample * N` that is not N long")))?;
            outs.push(self.in_child(&key, |f, inst, decl| {
                f.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?.ctx = time_of(caller, r, j);
                run_frame(f, inst, decl, &ticks, &given)?;
                Ok(inst.out.clone())
            })?);
        }
        match out {
            Out::All => Ok(Value::Array(outs)),
            _ => self.held(&key, out, caller, at),
        }
    }

    /// The values the arguments of the chain at `key` (ratio `r`) give to the inputs of `decl`: for `sample` (when `sample`) with how each one is fed, and for the stage of each
    /// tick that `ticks` takes, by name. They are read here, in the frame of the call.
    fn chain_inputs(
        &mut self,
        key: &NodeKey,
        decl: &'a FlowDef,
        r: i32,
        ticks: impl Fn(i32) -> bool,
        sample: bool,
    ) -> Result<ChainInputs<'a>, Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(key.call).span);
        let here = |fault| Stop { fault, at };
        let ExprKind::Call { args, .. } = &ast.expr(key.call).kind else {
            return Err(here(Internal("a chain with no head call")));
        };
        let (mut given, mut slow) = (Vec::new(), Vec::new());
        for (i, a) in decl.inputs.iter().zip(args) {
            let (stage, k) = (input_stage(i).map_err(here)?, input_ratio(i));
            let how = k.map_or(Ok(Feed::Plain), |k| feed(k, r)).map_err(here)?;
            let name = i.name.as_str();
            match (stage, how) {
                (Stage::Sample, _) if !sample => {}
                (Stage::Sample, Feed::Gather { per, .. }) => given.push((name, how, self.ring(key, a.expr, per, at)?)),
                (Stage::Sample, _) => given.push((name, how, self.eval_staged(key.call, a.expr, stage)?)),
                (Stage::Tick(x), _) if ticks(x) => slow.push((name, self.eval_staged(key.call, a.expr, stage)?)),
                _ => {}
            }
        }
        Ok((given, slow))
    }

    /// The part of one frame of the instance of the chain `.down~` at `key` (ratio `r`) that the ticks `ticks` say, and its `sample` stage when `sample`, read at this time of its caller.
    fn chain_part(
        &mut self,
        key: &NodeKey,
        def: DefId,
        r: i32,
        ticks: impl Fn(i32) -> bool + Copy,
        sample: bool,
    ) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
        let (given, slow) = self.chain_inputs(key, decl, r, ticks, sample)?;
        let given: Vec<(&str, &Value)> = given.iter().map(|(n, _, v)| (*n, v)).collect();
        self.in_child(key, |f, inst, decl| {
            run_ticks(f, inst, decl, &slow, ticks)?;
            if sample {
                enter(f, inst, decl, Stage::Sample, &given)?;
            }
            Ok(())
        })
    }

    /// What the chain at `key` gives between its runs: the output of the last one, or for an output dealt to the frames after a tick, the elements of this frame (§11.9).
    fn held(&self, key: &NodeKey, out: Out, caller: Ctx, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let last = &run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?.out;
        match (out, last) {
            (Out::Dealt { r, per }, Value::Array(vs)) => {
                let from = phase(caller, r) as usize * per;
                match vs.get(from..from + per) {
                    Some([one]) => Ok(one.clone()),
                    Some(part) => Ok(Value::Array(part.to_vec())),
                    None => Err(here(Internal("a dealt array that is not `sample * N` long"))),
                }
            }
            (Out::Dealt { .. }, _) => Err(here(Internal("a dealt output that no tick has made"))),
            (_, v) => Ok(v.clone()),
        }
    }

    /// The values the gather of the argument `arg` of the chain at `key` holds, the oldest first (the last is the one of the frame before): each frame's `per` elements in a row.
    fn ring(&self, key: &NodeKey, arg: ExprId, per: usize, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let at_arg = NodeKey::gathered(arg, &key.replicas);
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let Some(Store::Ring { buf, w }) = run.state.cells.get(&at_arg).map(|c| &c.current) else {
            return Err(here(Internal("a gather with no ring")));
        };
        let mut all = Vec::with_capacity(buf.len() * per);
        for v in (0..buf.len()).map(|i| &buf[(w + i) % buf.len()]) {
            match v {
                Value::Array(vs) if per > 1 => all.extend_from_slice(vs),
                v if per == 1 => all.push(v.clone()),
                _ => return Err(here(Internal("a gathered value that is not `sample * N` long"))),
            }
        }
        Ok(Value::Array(all))
    }

    /// What the instances this one calls do at each `sample` frame of it, after its own stage (§11.9): the argument that a gather takes is stored at the end of the frame (the
    /// frame after a tick reads it, the position's own value is not in), and an instance with an output at a tick runs its `sample` stage (its tick is read where the call is).
    pub(super) fn sample_nodes(&mut self, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a sample stage with no run"), at: whole })?;
        let calls: Vec<_> =
            run.state.children.iter().map(|(k, c)| (k.clone(), c.def, c.rate, c.scope.clone())).collect();
        for (key, def, rate, scope) in calls {
            let at = self.body.ast.expr(key.call).span;
            let here = |fault| Stop { fault, at };
            let decl = self.body.view.flow(def).map_err(here)?;
            let ExprKind::Call { args, .. } = &self.body.ast.expr(key.call).kind else { continue };
            if at_callers_time(rate) {
                if out_ratio(decl).map_err(here)? < 0 {
                    self.with_bindings(&key.replicas, scope, |f| {
                        let given = f.inputs_of(key.call, decl, Stage::Sample)?;
                        let given: Vec<(&str, &Value)> = given.iter().map(|(n, v)| (*n, v)).collect();
                        f.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Sample, &given))
                    })?;
                }
                continue;
            }
            for (i, a) in decl.inputs.iter().zip(args) {
                if let Some(Feed::Gather { .. }) = input_ratio(i).map(|k| feed(k, rate)).transpose().map_err(here)? {
                    let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
                    let key = NodeKey::gathered(a.expr, &key.replicas);
                    run.saves.push(Save { key, expr: a.expr, scope: scope.clone() });
                }
            }
            // The rest of the frame of a chain whose output is a tick (read at it, `chained`): the faster ticks, and `sample`.
            let m = out_ratio(decl).map_err(here)?;
            if m < 0 && on_tick(self.time(at)?, rate) {
                self.with_bindings(&key.replicas, scope, |f| f.chain_part(&key, def, rate, |x| x > m, true))?;
            }
        }
        Ok(())
    }

    /// The stage of the slower tick `r` of the instances this one calls at its own time (a call with no modifier, or a chain of ratio 0): their ticks
    /// are in the stage of this one (S-1088: `ctl` of `lin_up32~(ctl~(avg_down32~(x)).down~(32))` reads the new average at the same position). They
    /// run after the steps of this stage, with the inputs of the tick that their arguments have (a panic is the one thing whose order shows, the place of the call
    /// being the order of the spec). The tick that is the output of an instance is run where the call is read (`instance`).
    pub(super) fn tick_children(&mut self, r: i32, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a tick stage with no run"), at: whole })?;
        let calls: Vec<_> = run
            .state
            .children
            .iter()
            .filter(|(_, c)| at_callers_time(c.rate) && c.slow.contains(&r))
            .map(|(k, c)| (k.clone(), c.def, c.scope.clone()))
            .collect();
        for (key, def, scope) in calls {
            let at = self.body.ast.expr(key.call).span;
            let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
            if out_ratio(decl).map_err(|fault| Stop { fault, at })? == r {
                continue;
            }
            self.with_bindings(&key.replicas, scope, |f| {
                let given = f.inputs_of(key.call, decl, Stage::Tick(r))?;
                let given: Vec<(&str, &Value)> = given.iter().map(|(n, v)| (*n, v)).collect();
                f.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Tick(r), &given))
            })?;
        }
        Ok(())
    }

    /// The `block` stage of the instances this one calls (§11.3, a call of 0 frames too), on the `block` arguments.
    // SPEC-GAP(S-1128): the `block` stages of the instances a flow calls run after its own `block` `let`s, in the order of
    // their places; the spec does not say the order, which only the place of a panic shows.
    pub(super) fn block_children(&mut self, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a block stage with no run"), at: whole })?;
        let calls: Vec<_> = run.state.children.iter().map(|(k, c)| (k.clone(), c.def, c.scope.clone())).collect();
        for (key, def, scope) in calls {
            let at = self.body.ast.expr(key.call).span;
            let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
            self.with_bindings(&key.replicas, scope, |f| {
                let params = f.inputs_of(key.call, decl, Stage::Block)?;
                f.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Block, &params))
            })?;
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
