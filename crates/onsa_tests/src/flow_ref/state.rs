//! The state of a flow instance and the delays that use it (§11.4, §11.6): a tree of cells, one for each place a
//! delay is called (the call, and the replica of each `par~` around it, U2), the three delays by their formulas, and the
//! two phases of a tick: the delays read their stored value first, and what they store is evaluated after the body and
//! all of it stored at once (`^name` is read in the second phase, when the `let` it names has its value). The instances
//! a flow calls are the `children` of the tree: each is a whole [`Inst`], run in a frame of its own (`in_child`) at the
//! time of its caller (§11.5), and counted in the limit of the tree.

use std::collections::{BTreeMap, BTreeSet};

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::flow_names::{Delay, FlowBuiltin};
use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{DefId, LocalId, Ty};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};

use super::call::parts;
use super::expr::{Eval, Frame, LOW_STACK, Stop, evaluates};
use super::flow::{Ctx, Inst, Plans, enter};
use super::rate::{
    MOST_RATIO, body_out_stage, caller_stage, chain_of, counted, deals, dealt, elements, frames, gathers, n_of,
    on_tick, out_ratio, out_stage, phase, take, time_of,
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

/// What a node of the state is for: the delay a call is, the instance it makes, and what the caller keeps for an instance that a chain runs at another rate (§11.9: "集めた値は呼び出し側の値"、"配った値は呼び出し側の
/// `sample` の値"): the ring of the elements that its input number `n` gathers, and the array that its output deals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Role {
    Delay,
    Child,
    Gather(usize),
    Deal,
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
    fn role(&self, role: Role) -> NodeKey {
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
        self.children.values_mut().for_each(|c| {
            c.done = None;
            c.state.reset();
        });
    }
}

/// What a delay saves this tick: where, the expression whose value it is, and the bindings it is read under (the index
/// of each `par~` it is in and the locals an arm of a `match~` binds: they are not what they were when it is stored).
struct Save {
    key: NodeKey,
    expr: ExprId,
    scope: Vec<(LocalId, Value)>,
    /// The call whose ring it is (a gather): its argument is read with the bindings of the arms around the call, as the call reads it at a stage (`eval_in_arms`).
    call: Option<ExprId>,
    /// The clock `q` of the stream a ring gathers (`sample * 2^q`): the value is a burst of `2^q` elements, or one of the parameter kinds that is each of them; 0 for a delay, the one value.
    q: i32,
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
    /// The stage of this instance that the evaluation is in (`enter` sets it): a call reads in it (`Frame::call`).
    pub(super) stage: Stage,
    /// The exponent of the product of the ratios of the chains this instance is run by, from the outermost (0 there): at most `MOST_RATIO`.
    pub(super) exp: i32,
}

impl Run {
    pub(super) fn new(state: InstState, ctx: Ctx, used: usize, plans: Plans) -> Run {
        Run {
            state,
            saves: Vec::new(),
            ctx,
            used,
            plans,
            replicas: Vec::new(),
            scope: Vec::new(),
            stage: Stage::Init,
            exp: 0,
        }
    }
}

enum Node {
    Delay(Delay),
    /// The ring of the `2^k` elements that the input number `input` at `sample * 2^k` of a `.down~` chain gathers (§11.9), flat, at the call.
    Gather {
        input: usize,
        k: i32,
    },
    /// The array of the `2^m` elements that the output at `sample * 2^m` of a `.down~` chain deals (§11.9), at the call.
    Deal(i32),
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
            return self.read_call(chain.head, chain.ratio, at);
        }
        match &self.body.ast.expr(e).kind {
            ExprKind::Feedback(_) => self.name(e, at),
            ExprKind::Call { args, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => self.delay(e, d, args, at),
                Called::Builtin(FlowBuiltin::SampleRate) => Ok(Value::F32(self.time(at)?.sample_rate)),
                // S-1127 (1), §11.4: the first tick after `init` or `reset` reads 0, and each tick adds 1.
                Called::Builtin(FlowBuiltin::SampleTick) => Ok(Value::int(IntKind::U32, self.time(at)?.tick.into())),
                Called::Flow(_) => self.read_call(e, 0, at),
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
        let key = self.key(e, Role::Delay);
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        let cell = run.state.cells.get(&key).ok_or(here(Internal("a delay with no state")))?;
        let out = match (&cell.current, &dc) {
            (Store::Last(v), _) => v.clone(),
            (Store::Ring { buf, w }, None) => buf[*w].clone(),
            (Store::Ring { buf, w }, Some(dc)) => interpolate(buf, *w, dc).map_err(here)?,
        };
        run.saves.push(Save { key, expr: arg(SAVED)?, scope: run.scope.clone(), call: None, q: 0 });
        Ok(out)
    }

    /// The second phase of a tick: what the delays saved (and the delays inside them), then every one stored.
    // SPEC-GAP(S-1126): a panic of what a delay saves (`prev~(10 / x)`, x = 0) is raised here, in the second phase, so a panic of
    // a `let` written after the delay (`5 / x`) comes first; the other reading evaluates the saved value where it is written.
    pub(super) fn commit(&mut self, at: Span) -> Result<(), Stop> {
        let here = |fault| Stop { fault, at };
        let (mut stores, mut once) = (Vec::new(), BTreeSet::new());
        for next in 0.. {
            let Some(save) = self.run.as_ref().ok_or(here(Internal("no run")))?.saves.get(next) else { break };
            let (key, expr, scope, call, q) = (save.key.clone(), save.expr, save.scope.clone(), save.call, save.q);
            let value = self.with_bindings(&key.replicas, scope, |f| match call {
                Some(call) => f.eval_in_arms(call, expr),
                None => f.eval(expr),
            })?;
            // A delay is stored once for a frame: a delay in the object of an arm that `eval_in_arms` evaluates again here saved its value in the frame already, the same one.
            if !once.insert(key.clone()) {
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
        run.saves.clear();
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
            for (input, i) in decl.inputs.iter().enumerate() {
                if let Some(k) = input_ratio(i).filter(|k| gathers(*k, chain.ratio)) {
                    out.push(Site::Node(chain.head, Node::Gather { input, k }, args.as_slice()));
                }
            }
            let m = out_ratio(decl).map_err(here)?;
            if deals(m, chain.ratio) {
                out.push(Site::Node(chain.head, Node::Deal(m), args.as_slice()));
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
                Site::Node(e, Node::Gather { input, k }, args) => self.make_gather(*e, *input, *k, args)?,
                Site::Node(e, Node::Deal(m), _) => self.make_deal(*e, *m)?,
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
        let key = self.key(e, Role::Delay);
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
        Ok(())
    }

    /// The node of the ring of the input number `input` (at `sample * 2^k`) of the chain whose head is `e`: the `2^k` elements of its argument that came before, `T.default()` at first (§11.9: position 0 has no
    /// sample before it). It is a node of the call: what the argument is does not matter to it (it may be a delay itself).
    fn make_gather(&mut self, e: ExprId, input: usize, k: i32, args: &[Arg]) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let arg = args.get(input).ok_or(here(Internal("an input with no argument")))?.expr;
        let shape = self.shape(self.body.ty(arg).map_err(here)?, at)?;
        let n = n_of(k) as usize;
        self.hold(n.checked_mul(shape.places()), at)?;
        let one = shape.default_value().ok_or(here(Internal("a gathered type with no default")))?;
        let store = Store::Ring { buf: vec![one; n], w: 0 };
        let key = self.key(e, Role::Gather(input));
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
        Ok(())
    }

    /// The node of the array that the output (at `sample * 2^m`) of the chain whose head is `e` deals: `T.default()` until the first tick makes it.
    fn make_deal(&mut self, e: ExprId, m: i32) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let shape = self.shape(self.body.ty(e).map_err(here)?, at)?;
        let n = n_of(m) as usize;
        self.hold(n.checked_mul(shape.places()), at)?;
        let one = shape.default_value().ok_or(here(Internal("a dealt type with no default")))?;
        let store = Store::Last(Value::Array(vec![one; n]));
        let key = self.key(e, Role::Deal);
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
        // SPEC-GAP(S-1089): the product of the ratios of the chains around a call is held to `MOST_RATIO` by its size, a product that is slower (`.down~(8192)` inside `.down~(8192)`) too.
        if self.run.as_ref().is_some_and(|run| (run.exp + rate).abs() > MOST_RATIO) {
            return Err(Stop { fault: Fault::Unavailable("a product of the ratios of the chains over 2^24"), at });
        }
        let (mut inst, decl) = self.new_child(def, at)?;
        inst.rate = rate;
        let key = self.key(e, Role::Child);
        let config = self.unit_inputs(&key, decl, 0, Stage::Init)?;
        let config: Vec<(&str, &Value)> = config.iter().map(|(n, _, v)| (*n, v)).collect();
        inst.scope = self.run.as_ref().map(|r| r.scope.clone()).unwrap_or_default();
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        run.state.children.insert(key.clone(), inst);
        self.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Init, &config))
    }

    /// The arguments of the call `call` of the flow `decl`: one for each of its inputs (the checker sees to it).
    fn args_of_call(&self, call: ExprId, decl: &FlowDef) -> Result<&'a [Arg], Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(call).span);
        match &ast.expr(call).kind {
            ExprKind::Call { args, .. } if args.len() == decl.inputs.len() => Ok(args),
            _ => Err(Stop {
                fault: Internal("an instance that is not a call of as many arguments as it has inputs"),
                at,
            }),
        }
    }

    /// The arguments of the call at `key` (an instance at the ratio `r` of its chain) that are inputs of `decl` at `stage`, by input name with the ratio `k` of its clock, evaluated here from the left (S-1131: the bindings
    /// of an arm they read are those of the stage). The input boundary (§11.9): an input that is gathered is the ring of the elements before this position (`ring`), another is the stream of its clock `q = k + r` of
    /// this frame: one value for `q <= 0`, and for `q > 0` the burst of its `2^q` values of the frame (a value of the parameter kinds that is not one is each of them), which `run_unit` takes apart for each run.
    fn unit_inputs(
        &mut self,
        key: &NodeKey,
        decl: &'a FlowDef,
        r: i32,
        stage: Stage,
    ) -> Result<Vec<(&'a str, i32, Value)>, Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        let args = self.args_of_call(key.call, decl)?;
        let mut mine = Vec::new();
        for (n, (i, a)) in decl.inputs.iter().zip(args).enumerate() {
            if input_stage(i).map_err(here)? != stage {
                continue;
            }
            let (k, q) = input_ratio(i).map_or((0, 0), |k| (k, k + r));
            let value = if gathers(k, r) {
                self.ring(key, n, at)?
            } else {
                match self.eval_staged(key.call, a.expr, stage)? {
                    Value::Burst(es) => counted(&es, q).map(|()| Value::Burst(es)).map_err(here)?,
                    // The elements are made after the limit has been asked: `x: F32 at (sample * 2147483648)` of a value of the parameter kinds is not 2^31 of them.
                    _ if q > 0 && !self.limits.holds(n_of(q) as usize) => {
                        return Err(here(Fault::Unavailable(
                            "an input at `sample * N` of more elements than the evaluator holds",
                        )));
                    }
                    v if q > 0 => Value::Burst(vec![v; n_of(q) as usize]),
                    v => v,
                }
            };
            mine.push((i.name.as_str(), k, value));
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
        let exp = run.exp + rate;
        let mut f = inst.frame(body, ctx, used, plans, self.host.take());
        f.limits = self.limits;
        f.run.iter_mut().for_each(|run| run.exp = exp);
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

    /// A call of a flow (§11.5), alone or the head of a chain of the ratio `r` (§11.9): the instance it makes runs the stages of its body in the stages of this one (`run_children`), and the call reads its
    /// output where it is made, the stage of this one that `out_stage` says (its arguments are read there, so the call is always evaluated there), else the output of the stage that made it, held
    /// until the next one (a tick, the elements of an array that a `.down~` chain deals to the frames after it).
    fn read_call(&mut self, head: ExprId, r: i32, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let Called::Flow(def) = self.body.called(head).map_err(here)? else {
            return Err(here(Fault::Unavailable("a modifier of a delay")));
        };
        let m = out_ratio(self.body.view.flow(def).map_err(here)?).map_err(here)?;
        let (key, caller) = (self.key(head, Role::Child), self.time(at)?);
        let made = Stage::Tick(out_stage(m, r));
        if self.run.as_ref().is_some_and(|run| run.stage == made) {
            self.run_unit(&key, made)?;
        }
        self.held(&key, m, r, caller, at)
    }

    /// The stages of the instance at `key` that are in the stage `s` of this one, for this frame of it, once (`Inst::done`): the stage `x` of its body is in the stage `caller_stage(x, r)` of this one, `r` the ratio of its chain
    /// (§11.9, S-1088: `r` = 0 is the same stage, `.down~(N)` N times slower, and for `.up~(N)` the stages that are not slower than `sample / N` are in the `sample` of this one, N runs for each frame, the ticks
    /// first and then `sample`). The inputs are read here in the frame of the call (`unit_inputs`; the run j of `.up~(N)` takes its part of what a burst is, `take`), the time the instance runs in is that of its rate (`time_of`), and
    /// the elements the body makes of its output are, for `.up~(N)`, those of the N runs in a row (what the call reads, `held`), and for a `.down~` chain that makes `sample * 2^m` what the caller deals (`Role::Deal`).
    // SPEC-GAP(S-1206): the stage of this one that an instance runs a stage of its body in is the one `caller_stage` says, and its output at `sample` is made where the call is read; the spec does not say the
    // order of the stages of the parts of a call (only a panic shows it).
    fn run_unit(&mut self, key: &NodeKey, s: Stage) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let child = run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?;
        let (def, r, caller, slow, done) = (child.def, child.rate, run.ctx, child.slow.clone(), child.done);
        let decl = self.body.view.flow(def).map_err(here)?;
        let Stage::Tick(sx) = s else {
            let params = self.unit_inputs(key, decl, 0, s)?;
            let params: Vec<(&str, &Value)> = params.iter().map(|(n, _, v)| (*n, v)).collect();
            return match s {
                Stage::Block => self.in_child(key, |f, inst, decl| enter(f, inst, decl, s, &params)),
                _ => Ok(()),
            };
        };
        let mine: Vec<i32> = slow.iter().copied().chain([0]).filter(|x| caller_stage(*x, r) == sx).collect();
        if mine.is_empty() || done == Some((caller.total(), s)) {
            return Ok(());
        }
        let m = out_ratio(decl).map_err(here)?;
        let mut given = Vec::new();
        for x in &mine {
            given.push((*x, self.unit_inputs(key, decl, r, Stage::Tick(*x))?));
        }
        let dealt = self.in_child(key, |f, inst, decl| {
            let mut outs = Vec::new();
            for j in 0..if sx == 0 { frames(r) } else { 1 } {
                let time = time_of(caller, r, j);
                f.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?.ctx = time;
                for (x, inputs) in &given {
                    if *x != 0 && !on_tick(time, *x) {
                        continue;
                    }
                    let mut now = Vec::new();
                    for (name, k, v) in inputs {
                        now.push((*name, take(*k, r, j, v).map_err(|fault| Stop { fault, at })?));
                    }
                    enter(f, inst, decl, if *x == 0 { Stage::Sample } else { Stage::Tick(*x) }, &now)?;
                    if *x == body_out_stage(m) {
                        outs.extend(elements(m, &inst.out).map_err(|fault| Stop { fault, at })?);
                    }
                }
            }
            inst.done = Some((caller.total(), s));
            let made = sx == out_stage(m, r);
            Ok(if made && deals(m, r) {
                Some(outs)
            } else {
                if made && r > 0 {
                    inst.runs = outs;
                }
                None
            })
        })?;
        match dealt {
            Some(outs) => {
                let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
                let cell =
                    run.state.cells.get_mut(&key.role(Role::Deal)).ok_or(here(Internal("a deal with no array")))?;
                cell.current = Store::Last(Value::Array(outs));
                Ok(())
            }
            None => Ok(()),
        }
    }

    /// What the call at `key` (its chain of the ratio `r`, its output declared at `m`) gives in the frame of this one, the output boundary (§11.9): `o = m + r` is the clock the caller reads it at, a burst of its `2^o`
    /// values for `o > 0` (`Value::Burst`) and one value for `o <= 0`. A `.down~` chain that makes `sample * 2^m` deals what its tick made to the frames after it, in order (the caller's `Role::Deal`: the elements
    /// from `phase * 2^o`, or the one `phase / 2^-o` that the tick of `sample / 2^-o` it is in has); a `.up~(N)` chain gives the elements of its N runs in a row; a call with no chain gives the `2^m` elements of the
    /// body for `sample * 2^m`; any other is the value the body made last, held until its next tick.
    fn held(&self, key: &NodeKey, m: i32, r: i32, caller: Ctx, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let child = run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?;
        let burst = |es: Vec<Value>| counted(&es, m + r).map(|()| Value::Burst(es)).map_err(here);
        match (r.cmp(&0), m > 0) {
            (std::cmp::Ordering::Less, true) => {
                let Some(Store::Last(Value::Array(vs))) =
                    run.state.cells.get(&key.role(Role::Deal)).map(|c| &c.current)
                else {
                    return Err(here(Internal("a deal with no array")));
                };
                let (from, n) = dealt(m, r, phase(caller, r));
                match (vs.get(from..from + n), m + r > 0) {
                    (Some(part), true) => burst(part.to_vec()),
                    (Some([one]), false) => Ok(one.clone()),
                    _ => Err(here(Internal("a dealt array that is not `sample * N` long"))),
                }
            }
            (std::cmp::Ordering::Greater, _) if m + r > 0 => burst(child.runs.clone()),
            (std::cmp::Ordering::Equal, true) => burst(elements(m, &child.out).map_err(here)?),
            _ => Ok(child.out.clone()),
        }
    }

    /// The elements the ring of the input number `input` of the chain at `key` holds, the oldest first (the last is the one of the frame before): the `2^k` the body reads at its tick. The frames between two ticks
    /// write all of the ring (`2^q` of each of the `2^-r` frames, the one of each tick of a slower stream), so at a tick it is back at its first place and the buffer is in order.
    fn ring(&self, key: &NodeKey, input: usize, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let Some(Store::Ring { buf, .. }) = run.state.cells.get(&key.role(Role::Gather(input))).map(|c| &c.current)
        else {
            return Err(here(Internal("a gather with no ring")));
        };
        Ok(Value::Array(buf.clone()))
    }

    /// The argument that an input of `sample * N` of a `.down~` chain gathers is stored at the end of each `sample` frame of this one, the `2^q` elements of its stream at the clock `q = k + r` (§11.9: the frame
    /// after a tick reads it, the position's own value is not in); a stream slower than `sample` gives one element at each tick of its own, `sample / 2^-q`.
    pub(super) fn save_gathers(&mut self, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a sample stage with no run"), at: whole })?;
        let (ctx, calls): (_, Vec<_>) =
            (run.ctx, run.state.children.iter().map(|(k, c)| (k.clone(), c.def, c.rate, c.scope.clone())).collect());
        for (key, def, rate, scope) in calls {
            let here = |fault| Stop { fault, at: self.body.ast.expr(key.call).span };
            let decl = self.body.view.flow(def).map_err(here)?;
            let args = self.args_of_call(key.call, decl)?;
            for (n, (i, a)) in decl.inputs.iter().zip(args).enumerate() {
                let Some(q) = input_ratio(i).filter(|k| gathers(*k, rate)).map(|k| k + rate) else { continue };
                if q < 0 && !on_tick(ctx, q) {
                    continue;
                }
                let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
                let save = Save {
                    key: key.role(Role::Gather(n)),
                    expr: a.expr,
                    scope: scope.clone(),
                    call: Some(key.call),
                    q,
                };
                run.saves.push(save);
            }
        }
        Ok(())
    }

    /// The stage `s` of this one (`enter`) runs the stages of the instances it calls that are in it (`run_unit`), after its own `let`s, in the order of the places of the calls (a panic is the one thing whose order
    /// shows). An output at `sample` is not run here: it is made where its call is read, after the `let`s or in the second phase, with the bindings that read has. All of them have a `block` stage (§11.3, a call of 0 frames too).
    // SPEC-GAP(S-1128): the `block` stages of the instances a flow calls run after its own `block` `let`s, in the order of
    // their places; the spec does not say the order, which only the place of a panic shows.
    pub(super) fn run_children(&mut self, s: Stage, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a stage with no run"), at: whole })?;
        let calls: Vec<_> =
            run.state.children.iter().map(|(k, c)| (k.clone(), c.def, c.rate, c.scope.clone())).collect();
        for (key, def, rate, scope) in calls {
            let here = |fault| Stop { fault, at: self.body.ast.expr(key.call).span };
            let made = out_ratio(self.body.view.flow(def).map_err(here)?).map_err(here)?;
            if s == Stage::Sample && s == Stage::Tick(out_stage(made, rate)) {
                continue;
            }
            self.with_bindings(&key.replicas, scope, |f| f.run_unit(&key, s))?;
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
