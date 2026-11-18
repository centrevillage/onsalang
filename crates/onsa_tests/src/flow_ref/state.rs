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
use onsa_sema::{DefId, Ty};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};

use super::call::parts;
use super::expr::{Eval, Frame, LOW_STACK, Stop, evaluates};
use super::flow::{Ctx, Inst, Plans, enter};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Called, Stage, input_stage};
use super::value::{IntKind, Scalar, Shape, Value};

/// The places an instance takes in the limit of the tree (`Limits::most`): some 100 thousand instances, not 2^20.
const INSTANCE: usize = 8;

/// Where a node of the state is: the call that makes it, and the replica of each `par~` it is in (U2).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKey {
    pub call: ExprId,
    pub replicas: Vec<u32>,
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
}

impl InstState {
    /// Every node back to what it started from (§11.6 `reset`), the instances inside too.
    pub fn reset(&mut self) {
        self.cells.values_mut().for_each(|c| c.current = c.initial.clone());
        self.children.values_mut().for_each(|c| c.state.reset());
    }
}

/// What a delay saves this tick: where, and the expression whose value it is.
struct Save {
    key: NodeKey,
    expr: ExprId,
}

/// What an evaluation of a flow body holds besides its locals: the state, what the delays save this tick, the time it is
/// at (an instance reads its caller's; W7-09 gives `.down~` and `.up~` another), the places of the tree made so far and
/// the plans of its flows.
pub struct Run {
    pub state: InstState,
    saves: Vec<Save>,
    pub ctx: Ctx,
    used: usize,
    plans: Plans,
}

impl Run {
    pub(super) fn new(state: InstState, ctx: Ctx, used: usize, plans: Plans) -> Run {
        Run { state, saves: Vec::new(), ctx, used, plans }
    }
}

enum Node {
    Delay(Delay),
    Instance(DefId),
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
        match &self.body.ast.expr(e).kind {
            ExprKind::Feedback(_) => self.name(e, at),
            ExprKind::Call { args, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => self.delay(e, d, args, at),
                Called::Builtin(FlowBuiltin::SampleRate) => Ok(Value::F32(self.time(at)?.sample_rate)),
                // SPEC-GAP(S-1127): the first frame after `init` or `reset` reads 0 (the time since then, §11.4); the other
                // reading is that it reads 1, the ticks counted when the frame is made.
                Called::Builtin(FlowBuiltin::SampleTick) => Ok(Value::int(IntKind::U32, self.time(at)?.tick.into())),
                Called::Flow(def) => self.instance(e, def, at),
            },
            _ => Err(here(Internal("not a stateful form"))),
        }
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
        let dc = if d == Delay::Variable { Some(self.eval(arg(1)?)?) } else { None };
        let key = NodeKey { call: e, replicas: Vec::new() };
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        let cell = run.state.cells.get(&key).ok_or(here(Internal("a delay with no state")))?;
        let out = match (&cell.current, &dc) {
            (Store::Last(v), _) => v.clone(),
            (Store::Ring { buf, w }, None) => buf[*w].clone(),
            (Store::Ring { buf, w }, Some(dc)) => interpolate(buf, *w, dc).map_err(here)?,
        };
        run.saves.push(Save { key, expr: arg(0)? });
        Ok(out)
    }

    /// The second phase of a tick: what the delays saved (and the delays inside them), then every one stored.
    // SPEC-GAP(S-1126): a panic of what a delay saves (`prev~(10 / x)`, x = 0) is raised here, in the second phase, so a panic of
    // a `let` written after the delay (`5 / x`) comes first; the other reading evaluates the saved value where it is written.
    pub(super) fn commit(&mut self, at: Span) -> Result<(), Stop> {
        let here = |fault| Stop { fault, at };
        let mut stores = Vec::new();
        while let Some(save) = self.run.as_ref().ok_or(here(Internal("no run")))?.saves.get(stores.len()) {
            let (key, expr) = (save.key.clone(), save.expr);
            stores.push((key, self.eval(expr)?));
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

    /// The delays and instances in `e` as `(call, which, arguments)`, the inside first. A form the evaluator does not
    /// evaluate (`par~`, U2) is `Unavailable` here, at `init`, not looked into.
    fn nodes(&self, e: ExprId, out: &mut Vec<(ExprId, Node, &'a [Arg])>) -> Result<(), Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(e).span);
        let here = |fault| Stop { fault, at };
        if !evaluates(&self.body, e) {
            return Err(here(Fault::Unavailable("a form of a later unit")));
        }
        let node = match &ast.expr(e).kind {
            ExprKind::Call { args, kind: CallKind::Flow, .. } => match self.body.called(e).map_err(here)? {
                Called::Builtin(FlowBuiltin::Delay(d)) => Some((e, Node::Delay(d), args.as_slice())),
                Called::Builtin(_) => None,
                Called::Flow(def) => Some((e, Node::Instance(def), args.as_slice())),
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
        found.into_iter().try_for_each(|(e, node, args)| match node {
            Node::Delay(d) => self.make_cell(e, d, args),
            Node::Instance(def) => self.make_child(e, def),
        })
    }

    /// Adds `places` (none: more than a count holds) to those of the whole tree, which `Limits::most` holds.
    fn hold(&mut self, places: Option<usize>, at: Span) -> Result<(), Stop> {
        let more = Stop { fault: Fault::Unavailable("the delays and instances are more than the evaluator holds"), at };
        let (most, run) = (self.limits.most, self.run.as_mut().ok_or(more)?);
        run.used = places.and_then(|p| p.checked_add(run.used)).filter(|u| *u <= most).ok_or(more)?;
        Ok(())
    }

    /// The node of the delay `e`; its places are held with those of the nodes before it (the whole tree) before it is made.
    #[inline(never)]
    fn make_cell(&mut self, e: ExprId, d: Delay, args: &[Arg]) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let here = |fault| Stop { fault, at };
        let given = args.get(d.init_index()).map(|a| self.eval(a.expr)).transpose()?;
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
        let key = NodeKey { call: e, replicas: Vec::new() };
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
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
    fn make_child(&mut self, e: ExprId, def: DefId) -> Result<(), Stop> {
        let at = self.body.ast.expr(e).span;
        let (inst, decl) = self.new_child(def, at)?;
        let config = self.inputs_of(e, decl, Stage::Init)?;
        let key = NodeKey { call: e, replicas: Vec::new() };
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
        let mine = decl.inputs.iter().zip(args).filter(|(i, _)| input_stage(i) == stage);
        mine.map(|(i, a)| Ok((i.name.as_str(), self.eval(a.expr)?))).collect()
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
        let (ctx, used, plans) = (run.ctx, run.used, run.plans.clone());
        let def = run.state.children.get(key).map(|c| c.def).ok_or(here(Internal("an instance with no state")))?;
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

    /// A call of a flow (§11.5): its instance runs a frame on the `sample` arguments, and its output is the value.
    fn instance(&mut self, e: ExprId, def: DefId, at: Span) -> Eval {
        let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
        let given = self.inputs_of(e, decl, Stage::Sample)?;
        let given: Vec<(&str, &Value)> = given.iter().map(|(n, v)| (*n, v)).collect();
        self.in_child(&NodeKey { call: e, replicas: Vec::new() }, |f, inst, decl| {
            enter(f, inst, decl, Stage::Sample, &given)?;
            Ok(inst.out.clone())
        })
    }

    /// The `block` stage of the instances this one calls (§11.3, a call of 0 frames too), on the `block` arguments.
    // SPEC-GAP(S-1128): the `block` stages of the instances a flow calls run after its own `block` `let`s, in the order of
    // their places; the spec does not say the order, which only the place of a panic shows.
    pub(super) fn block_children(&mut self, whole: Span) -> Result<(), Stop> {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("a block stage with no run"), at: whole })?;
        let calls: Vec<(NodeKey, DefId)> = run.state.children.iter().map(|(k, c)| (k.clone(), c.def)).collect();
        for (key, def) in calls {
            let at = self.body.ast.expr(key.call).span;
            let decl = self.body.view.flow(def).map_err(|fault| Stop { fault, at })?;
            let params = self.inputs_of(key.call, decl, Stage::Block)?;
            self.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Block, &params))?;
        }
        Ok(())
    }

    /// The type as far as its default needs it (§6.4); a field a struct declares a value for has it.
    fn shape(&mut self, ty: &Ty, at: Span) -> Result<Shape, Stop> {
        let here = |fault| Stop { fault, at };
        let view = self.body.view;
        Ok(match ty {
            Ty::Tuple(ts) => Shape::Tuple(ts.iter().map(|t| self.shape(view.ty(*t), at)).collect::<Result<_, _>>()?),
            Ty::Array(t, Len::Const(n)) if *n as usize <= self.limits.most => {
                Shape::Array(Box::new(self.shape(view.ty(*t), at)?), *n as usize)
            }
            Ty::Named(def, _) => {
                let mut fields = Vec::new();
                for f in view.struct_fields(*def).map_err(here)? {
                    let declared = f.default.map(|c| self.const_def(c, view.ty(f.ty), at)).transpose()?;
                    fields.push((declared, self.shape(view.ty(f.ty), at)?));
                }
                Shape::Struct(fields)
            }
            ty => Shape::Scalar(Scalar::of(ty).ok_or(here(Fault::Unavailable("a type with no default here")))?),
        })
    }
}
