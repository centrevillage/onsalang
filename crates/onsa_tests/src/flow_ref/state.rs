//! The state of a flow instance and the delays that use it (§11.4, §11.6): a tree of cells, one for each place a
//! delay is called (the call, and the replica of each `par~` around it, U2), the three delays by their formulas, and the
//! two phases of a tick: the delays read their stored value first, and what they store is evaluated after the body and
//! all of it stored at once (`^name` is read in the second phase, when the `let` it names has its value). The instances
//! a flow calls are the `children` of the tree (U1c).

use std::collections::BTreeMap;

use onsa_diag::Span;
use onsa_sema::Ty;
use onsa_sema::flow_names::{Delay, FlowBuiltin};
use onsa_sema::ty::{FloatKind, Len};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};

use super::call::parts;
use super::expr::{Eval, Frame, Stop, evaluates};
use super::scalar::{Fault, Fault::Internal};
use super::value::{Scalar, Shape, Value};

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

/// The state of one instance: its own nodes, and the instances it calls.
#[derive(Clone, Debug, Default)]
pub struct InstState {
    pub cells: BTreeMap<NodeKey, Cell>,
    pub children: BTreeMap<NodeKey, InstState>,
}

impl InstState {
    /// Every node back to what it started from (§11.6 `reset`), the instances inside too.
    pub fn reset(&mut self) {
        self.cells.values_mut().for_each(|c| c.current = c.initial.clone());
        self.children.values_mut().for_each(InstState::reset);
    }
}

/// What a delay saves this tick: where, and the expression whose value it is.
struct Save {
    key: NodeKey,
    expr: ExprId,
}

/// What an evaluation of a flow body holds besides its locals: the state, and what the delays save this tick.
pub struct Run {
    pub state: InstState,
    saves: Vec<Save>,
}

impl Run {
    pub fn new(state: InstState) -> Run {
        Run { state, saves: Vec::new() }
    }
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
    /// The delay a flow call names (`prev~`, `delay~`, `vdelay~`), else none (an instance of a flow, U1c).
    fn delay_of(&self, callee: ExprId) -> Option<Delay> {
        let ExprKind::Path(p) = &self.body.ast.expr(onsa_sema::named(self.body.ast, callee)).kind else { return None };
        match (p.segments.as_slice(), p.segments.first().and_then(|s| FlowBuiltin::named(&s.name))) {
            ([_], Some(FlowBuiltin::Delay(d))) => Some(d),
            _ => None,
        }
    }

    /// The forms of a flow body that have state: a delay, and `^name` (which is the local the name is, read when what
    /// a delay saves is evaluated). One door for `Frame::form`.
    #[inline(never)]
    pub(super) fn stateful(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        match &self.body.ast.expr(e).kind {
            ExprKind::Feedback(_) => self.name(e, at),
            ExprKind::Call { callee, args, kind: CallKind::Flow } => match self.delay_of(*callee) {
                Some(d) => self.delay(e, d, args, at),
                None => Err(here(Fault::Unavailable("an instance of a flow"))),
            },
            _ => Err(here(Internal("not a stateful form"))),
        }
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

    /// The delays in `e` as `(call, which, arguments)`, the inside of a delay first. A form the evaluator does not evaluate
    /// (`par~`, U2), an instance of a flow and `sample_rate()` (U1c) are `Unavailable` here, at `init`, not looked into.
    fn delays(&self, e: ExprId, out: &mut Vec<(ExprId, Delay, &'a [Arg])>) -> Result<(), Stop> {
        let (ast, at) = (self.body.ast, self.body.ast.expr(e).span);
        let stop = |what| Err(Stop { fault: Fault::Unavailable(what), at });
        if !evaluates(&self.body, e) {
            return stop("a form of a later unit");
        }
        let delay = match &ast.expr(e).kind {
            ExprKind::Call { callee, args, kind: CallKind::Flow } => match self.delay_of(*callee) {
                Some(d) => Some((e, d, args.as_slice())),
                None => return stop("an instance of a flow"),
            },
            _ => None,
        };
        parts(&self.body, e).into_iter().try_for_each(|x| self.delays(x, out))?;
        out.extend(delay);
        Ok(())
    }

    /// The nodes of the delays in the expressions `roots`, made as they start (§11.3: `init` is evaluated once, at
    /// `init`): the value of each, or `T.default()` of its type (§6.4), and the ring `N` long (`MAX + 1` for `vdelay~`).
    pub(super) fn make_cells(&mut self, roots: &[ExprId]) -> Result<(), Stop> {
        let mut found = Vec::new();
        roots.iter().try_for_each(|e| self.delays(*e, &mut found))?;
        let mut used = 0;
        found.into_iter().try_for_each(|(e, d, args)| self.make_cell(e, d, args, &mut used))
    }

    /// The node of the delay `e`; the places of all the nodes (`used` before it) are held to `Limits::most` before it is made.
    #[inline(never)]
    fn make_cell(&mut self, e: ExprId, d: Delay, args: &[Arg], used: &mut usize) -> Result<(), Stop> {
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
        let places = len.and_then(|n| n.checked_mul(one)).and_then(|p| p.checked_add(*used));
        let (Some(n), Some(places)) = (len, places.filter(|p| *p <= self.limits.most)) else {
            return Err(here(Fault::Unavailable("the delay lines are longer than the evaluator holds")));
        };
        *used = places;
        let init = given.or_else(|| shape.and_then(|s| s.default_value()));
        let init = init.ok_or(here(Internal("a delay of a type with no default")))?;
        let store = if d == Delay::Prev { Store::Last(init) } else { Store::Ring { buf: vec![init; n], w: 0 } };
        let key = NodeKey { call: e, replicas: Vec::new() };
        let run = self.run.as_mut().ok_or(here(Fault::Unavailable("a delay outside an instance of a flow")))?;
        run.state.cells.insert(key, Cell { initial: store.clone(), current: store });
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
