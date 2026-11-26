//! The `test` blocks of a case run on the evaluator (W7-19 U2a): the memo's extraction, read from the syntax tree and the
//! tables of the checker (no builtin is told by its name: a generated function is [`FlowFn`], a primitive a `PrimRow`, a
//! type a [`FlowTy`]). A `let` is evaluated by [`Frame`]; a call of `render` is made by [`Instance::render`] and kept
//! as the outputs it gave, which the paths of the asserts (`o.out[k]`, `o.l[c][k]`) read; the rest of an assert is
//! evaluated. The state of `var st = F.init(..)` is an [`Instance`] kept by its local; `F.process(inout st, ..)` reads its
//! inputs (a local, `xs.slice(a, b)` or a call) and writes what it gave back into the part of the buffer its output names;
//! `F.reset(inout st)` is the instance's `reset`. The first stop ends a test: a panic is the test's (marked
//! `TESTFAIL`/`PANIC` or not, it is checked), an `Unavailable` is counted, an `Internal` fails. A form this unit does not
//! take is a [`Skip`] with its reason, never a silent drop.

use std::collections::HashMap;
use std::ops::Range;

use onsa_diag::Span;
use onsa_diag::unsupported::is_unsupported;
use onsa_driver::{Loaded, PackageInput, analyze_loaded, lower_core};
use onsa_sema::def::{FlowDef, FlowFn, FlowInput, FlowTy};
use onsa_sema::ty::Len;
use onsa_sema::{DefId, LocalId, Target, Ty, TyId};
use onsa_syntax::ast::{Arg, ExprId, ExprKind, Mode, PatKind, StmtKind};

use super::expr::{Frame, Stop};
use super::flow::{Call, Instance, Outcome, PanicAt};
use super::host::{FnHost, HostCall};
use super::interp_host::{GENERATED, InterpHost, Wrappers};
use super::scalar::{Fault, PanicKind};
use super::sema_view::{Body, Callee, Stage, View, inputs_at};
use super::value::{Scalar, Value};
use crate::{Markers, parse_markers};
use onsa_sema::prim::PrimRow;

use super::reads::{elem, part, rendered_struct};
pub use super::walk_model::{CaseRun, Event, Named, Panic, Run, Shape, Skip, TestRun, Types, Verdict};

/// Run the tests of `input` on the evaluator, its functions through the interpreter host. Call it on a thread of a
/// large stack. `Err` is a case that is not read (no check or a diagnostic that is not of a feature this version does not
/// support: the checker found it a mistake, and the evaluator does not take a program that is not whole).
pub fn run_case(input: PackageInput, wrappers: &Wrappers) -> Result<CaseRun, String> {
    run_case_with(input, wrappers, Expect::Marks)
}

/// What decides whether a test panics, for [`run_case_with`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expect {
    /// The marks of the case (`PANIC`, `TESTFAIL`): a marked test panics, an unmarked one does not.
    Marks,
    /// What the evaluator gave, for a program made by a generator, which has no marks: a panic is kept as the test's
    /// ([`Verdict::Ok`] with `panic`), and only the asserts before it have to hold.
    Evaluator,
}

/// [`run_case`] with the panics of the tests judged by `expect`.
pub fn run_case_with(input: PackageInput, wrappers: &Wrappers, expect: Expect) -> Result<CaseRun, String> {
    let marks: Vec<Markers> = input.files.iter().map(|f| parse_markers(&f.text)).collect::<Result<_, _>>()?;
    let mut loaded = Loaded::from_input(input)?;
    let analyzed = analyze_loaded(&mut loaded).map_err(|e| e.render(&loaded.sources))?;
    let e0200 = analyzed.diagnostics.iter().any(is_unsupported);
    if let Some(d) = analyzed.diagnostics.iter().find(|d| !is_unsupported(d)) {
        return Err(format!("{:?}: {}", d.code, d.message));
    }
    let core = lower_core(&analyzed).ok();
    let mut host = InterpHost::new(core.as_ref(), wrappers);
    let view = View::new(&analyzed);
    let marked = |name: &str| {
        marks.iter().any(|m| m.testfails.iter().any(|n| n == name) || m.panics.iter().any(|p| p.name == name))
    };
    let mut tests = Vec::new();
    for (def, name, root) in view.tests() {
        let mut run = Walk {
            host: &mut host,
            rendered: HashMap::new(),
            locals: HashMap::new(),
            states: Vec::new(),
            events: Vec::new(),
            asserts: 0,
            generated: 0,
        };
        let r = view.body(def).map_err(Halt::from).and_then(|body| run.steps(body, root));
        let file = loaded.sources.file(view.name_span(def).file).name().to_string();
        tests.push(run.finish((name.clone(), file), r, (expect == Expect::Marks).then(|| marked(&name))));
    }
    Ok(CaseRun { tests, lowered: core.is_some(), e0200 })
}

/// What ends a test before its last statement.
pub(super) enum Halt {
    Skip(Skip),
    Fault(Fault),
    /// The panic of the test, and the place in the body of the flow the evaluator stopped at (`Stop::at`; none for a panic of a plain expression of the test).
    Panic(Panic, Option<Span>),
    Failed(String),
}

impl From<Fault> for Halt {
    fn from(f: Fault) -> Halt {
        if matches!(f, Fault::Panic(_)) { Halt::Panic(Panic::Eval, None) } else { Halt::Fault(f) }
    }
}

impl From<Stop> for Halt {
    fn from(s: Stop) -> Halt {
        s.fault.into()
    }
}

/// The outputs a `render` gave and the names of the fields of its `Rendered` (§11.6: `out`, or those of a struct).
pub(super) struct Rendered {
    pub(super) outs: Vec<Value>,
    pub(super) fields: Vec<String>,
    /// The channels of each field, from the type (so that `o.out.len()` is not the frames when there are none).
    pub(super) channels: Vec<Option<usize>>,
}

/// What a call of a generated function gave: the outputs of a `render`, or the state of an `init`.
enum Gave<'a> {
    Rendered(Rendered),
    State(Box<Instance<'a>>),
}

/// The arguments of a call of a generated function by what they are: the `Config` and the `Params` by field, the state
/// (`inout st`), and the rest in the order written (the inputs, then the outputs of a `process`, or those of a `render`).
struct Args<'e> {
    config: Named<Value>,
    params: Named<Value>,
    state: Option<&'e Arg>,
    rest: Vec<&'e Arg>,
}

pub(super) struct Walk<'h, 'a> {
    host: &'h mut dyn FnHost,
    pub(super) rendered: HashMap<LocalId, Rendered>,
    locals: HashMap<LocalId, Value>,
    /// The states the test made, with the local of their `var`: two of a flow are two.
    states: Vec<(LocalId, Instance<'a>)>,
    events: Vec<Event>,
    asserts: usize,
    /// The generated functions the test calls.
    generated: usize,
}

impl<'a> Walk<'_, 'a> {
    fn finish(self, (name, file): (String, String), r: Result<(), Halt>, marked: Option<bool>) -> TestRun {
        let (asserts, generated, events) = (self.asserts, self.generated, self.events);
        let mut panic_span = None;
        let (panic, verdict) = match r {
            Ok(()) => (None, Verdict::Ok),
            Err(Halt::Panic(p, span)) => {
                panic_span = span;
                (Some(p), Verdict::Ok)
            }
            Err(Halt::Skip(s)) => (None, Verdict::Skipped(s)),
            Err(Halt::Fault(Fault::Unavailable(w))) => (None, Verdict::Unavailable(w)),
            Err(Halt::Fault(f)) => (None, Verdict::Failed(format!("{f:?}"))),
            Err(Halt::Failed(m)) => (None, Verdict::Failed(m)),
        };
        // A marked test panics and an unmarked one does not (the asserts before the panic have held, or it had failed).
        let verdict = match verdict {
            Verdict::Ok if marked.is_some_and(|m| panic.is_some() != m) => {
                let marked = marked == Some(true);
                Verdict::Failed(if marked { "no panic".into() } else { format!("a panic: {panic:?}") })
            }
            Verdict::Ok if generated == 0 => Verdict::Skipped(Skip::NoCall),
            v => v,
        };
        TestRun { name, file, asserts, panic, panic_span, verdict, events }
    }

    /// `e` evaluated in the frame of the test, whose locals are kept between the calls.
    pub(super) fn eval(&mut self, body: Body, e: ExprId) -> Result<Value, Halt> {
        if views(body, e) {
            return Err(Halt::Skip(Skip::Layout));
        }
        let mut door =
            Door { host: &mut *self.host, events: &mut self.events, generated: &mut self.generated, panic: None };
        let mut frame = Frame::new(body);
        frame.locals = std::mem::take(&mut self.locals);
        frame.host = Some(&mut door);
        let got = frame.eval(e);
        self.locals = std::mem::take(&mut frame.locals);
        match (got, door.panic) {
            (Err(Stop { fault: Fault::Unavailable(GENERATED), .. }), _) => Err(Halt::Skip(Skip::NoCall)),
            (Err(_), Some((at, span))) => Err(Halt::Panic(Panic::Call(at), Some(span))),
            (got, _) => Ok(got?),
        }
    }

    fn steps(&mut self, body: Body<'a>, root: ExprId) -> Result<(), Halt> {
        let ExprKind::Block(block) = &body.ast.expr(root).kind else {
            return Err(Fault::Unavailable("a test body").into());
        };
        for s in &block.stmts {
            match &body.ast.stmt(*s).kind {
                StmtKind::Let { pat, init, .. } if matches!(body.ast.pat(*pat).kind, PatKind::Wild) => {
                    self.discard(body, *init)?
                }
                StmtKind::Let { pat, init, .. } => self.bind(body, *init, body.pat_local(*pat).map_err(Halt::from))?,
                StmtKind::Var { name, init, .. } => {
                    self.bind(body, *init, body.var_local(name.span).map_err(Halt::from))?
                }
                StmtKind::Assert(e) => {
                    self.asserts += 1;
                    match self.value(body, *e)? {
                        Value::Bool(true) => {}
                        _ => return Err(Halt::Failed(format!("assert {} does not hold", self.asserts))),
                    }
                }
                // `for i in lo ..< hi { .. }` of a test: the body runs once for each value, with the variable bound (the asserts of a column read one by one).
                StmtKind::For { pat, moved: None, iter, body: inner } => {
                    let ExprKind::Range(r) = &body.ast.expr(*iter).kind else {
                        return Err(Halt::Skip(Skip::Statement));
                    };
                    let (lo, hi) = (self.value(body, r.lo)?, self.value(body, r.hi)?);
                    let (Value::Int(kind, lo, _), Value::Int(_, hi, _)) = (lo, hi) else {
                        return Err(Halt::Skip(Skip::Statement));
                    };
                    let local = body.pat_local(*pat).map_err(Halt::from)?;
                    let end = if matches!(r.end, onsa_syntax::ast::RangeEnd::Included) { hi + 1 } else { hi };
                    for i in lo..end {
                        self.locals.insert(local, Value::int(kind, i));
                        self.steps(body, *inner)?;
                    }
                }
                // `xs[i] = v` of a local array of scalars (the columns a test builds).
                StmtKind::Assign { target, value } if self.element_assign(body, *target, *value)? => {}
                StmtKind::Assign { target, .. } if views(body, *target) => return Err(Halt::Skip(Skip::Layout)),
                StmtKind::Expr(e) => self.statement(body, *e)?,
                _ => return Err(Halt::Skip(Skip::Statement)),
            }
        }
        block.tail.map_or(Ok(()), |e| self.statement(body, e))
    }

    /// `xs[i] = v` where `xs` is a local array of scalars: stored (`true`); any other target is left to the caller.
    fn element_assign(&mut self, body: Body<'a>, target: ExprId, value: ExprId) -> Result<bool, Halt> {
        let ExprKind::Index { base, index } = &body.ast.expr(target).kind else { return Ok(false) };
        let Ok(Target::Local(l)) = body.target(*base) else { return Ok(false) };
        if !matches!(self.locals.get(l), Some(Value::Array(vs)) if !vs.iter().any(|v| matches!(v, Value::Array(_)))) {
            return Ok(false);
        }
        let (Value::Int(_, i, _), v) = (self.value(body, *index)?, self.value(body, value)?) else { return Ok(false) };
        let at = usize::try_from(i).map_err(|_| Fault::Panic(PanicKind::Bounds))?;
        match self.locals.get_mut(l) {
            Some(Value::Array(vs)) => *vs.get_mut(at).ok_or(Fault::Panic(PanicKind::Bounds))? = v,
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// An expression as a statement (or the tail of the block: the last call of a test is one): a call of a generated
    /// function is run, a view is a layout, anything else is no form of this unit.
    fn statement(&mut self, body: Body<'a>, e: ExprId) -> Result<(), Halt> {
        if self.generated_call(body, e).is_some() {
            self.call(body, e).map(drop)
        } else {
            Err(Halt::Skip(if views(body, e) { Skip::Layout } else { Skip::Statement }))
        }
    }

    /// `let _ = e`: a call of a generated function is run (its event is kept) and any other value evaluated, then dropped.
    fn discard(&mut self, body: Body<'a>, e: ExprId) -> Result<(), Halt> {
        if self.generated_call(body, e).is_some() {
            self.call(body, e).map(drop)
        } else {
            self.value(body, e).map(drop)
        }
    }

    /// The `let` of `local`: a call of `render` is kept as its outputs, one of `init` as its state, any other value is evaluated.
    fn bind(&mut self, body: Body<'a>, init: ExprId, local: Result<LocalId, Halt>) -> Result<(), Halt> {
        if self.generated_call(body, init).is_some() {
            match self.call(body, init)? {
                Some(Gave::Rendered(r)) => {
                    let local = local?;
                    self.locals.insert(local, rendered_struct(&r.outs, r.fields.len())?);
                    self.rendered.insert(local, r);
                }
                Some(Gave::State(st)) => self.states.push((local?, *st)),
                None => {}
            }
            return Ok(());
        }
        let v = self.value(body, init)?;
        self.locals.insert(local?, v);
        Ok(())
    }

    /// The generated function a call is, with its flow.
    fn generated_call<'b>(&self, body: Body<'b>, e: ExprId) -> Option<(FlowFn, onsa_sema::DefId, Callee<'b>)> {
        let callee = matches!(body.ast.expr(e).kind, ExprKind::Call { .. }).then(|| body.callee(e).ok()).flatten()?;
        let (kind, flow) = body.view.flow_fn(callee.def)?;
        Some((kind, flow, callee))
    }

    /// The call `e` of a generated function: `init` gives a state, `render` its outputs, `process` writes into the buffer
    /// of its output and `reset` gives nothing.
    fn call(&mut self, body: Body<'a>, e: ExprId) -> Result<Option<Gave<'a>>, Halt> {
        let (kind, flow, callee) = self.generated_call(body, e).ok_or(Fault::Internal("not a generated call"))?;
        self.generated += 1;
        let ExprKind::Call { args, .. } = &body.ast.expr(e).kind else { return Err(Fault::Internal("a call").into()) };
        let (view, decl) = (body.view, body.view.flow(flow)?);
        if kind == FlowFn::ProcessInplace {
            return Err(Halt::Skip(Skip::Layout));
        }
        let args = self.split(body, &callee, args)?;
        let (config, params) = (by_name(&args.config), by_name(&args.params));
        match kind {
            FlowFn::Init => {
                let (sample_rate, _) = self.rate(body, &args.rest)?;
                let (state, config_of) = (self.states.len(), args.config.clone());
                let (name, written) = (view.qualified_name(flow), written_flow(body, e));
                let at = Event::Init { state, flow: name, written, sample_rate, config: config_of };
                self.events.push(at);
                let made = Instance::init(view, flow, sample_rate, &config, Some(&mut *self.host));
                Ok(Some(Gave::State(Box::new(made.map_err(|stop| stopped(stop, PanicAt::Init))?))))
            }
            FlowFn::Reset => {
                let (state, st) = Self::state(&mut self.states, body, &args)?;
                st.reset();
                self.events.push(Event::Reset { state });
                Ok(None)
            }
            FlowFn::Process => self.process(body, decl, &args, &params).map(|()| None),
            _ => self.render(body, e, flow, &args).map(|r| Some(Gave::Rendered(r))),
        }
    }

    /// A call of `render`: its inputs are the columns of the `sample` inputs, the frames of a flow with none, the rate.
    fn render(&mut self, body: Body<'a>, e: ExprId, flow: DefId, args: &Args) -> Result<Rendered, Halt> {
        let (view, decl) = (body.view, body.view.flow(flow)?);
        let sampled = inputs_at(decl, Stage::Sample)?;
        let (sample_rate, rest) = self.rate(body, &args.rest)?;
        let (frames, rest) = match (sampled.is_empty(), rest.split_last()) {
            (true, Some((n, rest))) => match self.eval(body, n.expr)? {
                Value::Int(_, n, _) => (Some(n as usize), rest),
                _ => return Err(Fault::Internal("the frame count of a render that is no integer").into()),
            },
            _ => (None, rest),
        };
        let given = sample_exprs(body, &sampled, &rest.iter().map(|a| a.expr).collect::<Vec<_>>())?;
        let columns = given.iter().map(|e| self.column(body, *e)).collect::<Result<Vec<_>, _>>()?;
        let call = (&args.config, &args.params);
        let (outcome, mut event) = render_run(&mut *self.host, view, flow, call, (sample_rate, frames, &columns))?;
        if let Event::Render { written, .. } = &mut event {
            *written = written_flow(body, e);
        }
        let (rendered, _) = view.flow_ty(body.ty_id(e)?).ok_or(Fault::Internal("a `Rendered`"))?;
        let fields: Vec<String> = view.struct_fields(rendered)?.iter().map(|f| f.name.clone()).collect();
        self.events.push(event);
        match outcome {
            Outcome::Ok(outs) => {
                let channels = io(view, decl, &sampled).0.into_iter().map(|(_, n)| n).collect();
                Ok(Rendered { outs, fields, channels })
            }
            Outcome::Panic { at, stop } => Err(Halt::Panic(Panic::Call(at), Some(stop.at))),
        }
    }

    /// A call of `process` over the buffers it names: the frames are the length of all of them, which `outs` takes back
    /// into the part of the buffer of the output (a plain local or `xs.slice(a, b)`; the other layouts are skipped).
    fn process(&mut self, body: Body<'a>, decl: &FlowDef, args: &Args, params: &[(&str, Value)]) -> Result<(), Halt> {
        let sampled = inputs_at(decl, Stage::Sample)?;
        let (outs, ins): (Vec<&&Arg>, Vec<&&Arg>) = args.rest.iter().partition(|a| a.mode == Mode::Inout);
        let &[out] = &outs[..] else { return Err(Halt::Skip(Skip::Layout)) };
        let given = sample_exprs(body, &sampled, &ins.iter().map(|a| a.expr).collect::<Vec<_>>())?;
        if given.len() != sampled.len() {
            return Err(Halt::Skip(Skip::Layout));
        }
        let columns = given.iter().map(|e| self.column(body, *e)).collect::<Result<Vec<_>, _>>()?;
        let (whole, part) = self.slice_of(body, out.expr)?;
        let Ok(Target::Local(buf)) = body.target(whole) else { return Err(Halt::Skip(Skip::Layout)) };
        let Some(Value::Array(vs)) = self.locals.get(buf) else { return Err(Halt::Skip(Skip::Layout)) };
        // A flow of several channels: the buffer is one array of scalars for each, all of the same length (planar, §5).
        let planar = vs.first().is_some_and(|v| matches!(v, Value::Array(_)));
        let (frames, at) = match (planar, &part) {
            (false, _) => cut(vs, part)?,
            (true, None) => {
                match vs.iter().map(|v| if let Value::Array(c) = v { Some(c.len()) } else { None }).collect() {
                    Some::<Vec<usize>>(ls) if ls.iter().all(|l| *l == ls[0]) => (ls[0], 0..ls[0]),
                    _ => return Err(Halt::Skip(Skip::Layout)),
                }
            }
            (true, Some(_)) => return Err(Halt::Skip(Skip::Layout)),
        };
        let inputs = named_columns(&sampled, &columns);
        let (state, st) = Self::state(&mut self.states, body, args)?;
        let outcome = st.process_outcome(params, &inputs, frames, Some(&mut *self.host))?;
        let run = run_of((&args.config, &args.params), Some(frames), &inputs, &outcome, io(body.view, decl, &sampled));
        self.events.push(Event::Process { state, run });
        match outcome {
            Outcome::Ok(gave) => {
                if let Some(Value::Array(vs)) = self.locals.get_mut(buf) {
                    match planar {
                        false => vs[at].clone_from_slice(&gave),
                        true => {
                            for (c, ch) in vs.iter_mut().enumerate() {
                                let (Value::Array(ch), true) =
                                    (ch, gave.iter().all(|f| matches!(f, Value::Array(a) if a.len() > c)))
                                else {
                                    return Err(Halt::Skip(Skip::Layout));
                                };
                                for (slot, f) in ch.iter_mut().zip(&gave) {
                                    if let Value::Array(a) = f {
                                        slot.clone_from(&a[c]);
                                    }
                                }
                            }
                        }
                    }
                }
                Ok(())
            }
            Outcome::Panic { at, stop } => Err(Halt::Panic(Panic::Call(at), Some(stop.at))),
        }
    }

    /// The arguments of a call, the `Config` and the `Params` evaluated.
    fn split<'e>(&mut self, body: Body<'a>, callee: &Callee, args: &'e [Arg]) -> Result<Args<'e>, Halt> {
        let mut got = Args { config: Vec::new(), params: Vec::new(), state: None, rest: Vec::new() };
        for (p, a) in callee.func.params.iter().zip(args) {
            let named = |this: &mut Self, def| -> Result<Named<Value>, Halt> {
                Ok(fields_of(body.view, def, this.eval(body, a.expr)?)?)
            };
            match body.view.flow_ty(p.ty) {
                Some((def, FlowTy::Config)) => got.config = named(self, def)?,
                Some((def, FlowTy::Params)) => got.params = named(self, def)?,
                Some((_, FlowTy::State)) => got.state = Some(a),
                _ => got.rest.push(a),
            }
        }
        Ok(got)
    }

    /// The sample rate, the last of the arguments of `init` and of `render`, and the others.
    fn rate<'e>(&mut self, body: Body<'a>, rest: &'e [&'e Arg]) -> Result<(f32, &'e [&'e Arg]), Halt> {
        let (rate, rest) = rest.split_last().ok_or(Fault::Internal("no sample rate"))?;
        let Value::F32(sample_rate) = self.eval(body, rate.expr)? else { return Err(Fault::Internal("a rate").into()) };
        Ok((sample_rate, rest))
    }

    /// The state `inout st` names, made by the `var` of its local: the last one it made (a `var` in the body of a `for` makes one for each pass).
    fn state<'s>(
        states: &'s mut [(LocalId, Instance<'a>)],
        body: Body<'a>,
        args: &Args,
    ) -> Result<(usize, &'s mut Instance<'a>), Halt> {
        let arg = args.state.ok_or(Fault::Internal("no state argument"))?;
        let Ok(Target::Local(l)) = body.target(arg.expr) else {
            return Err(Fault::Unavailable("a state that is no local").into());
        };
        let at = states.iter().rposition(|(m, _)| m == l).ok_or(Fault::Internal("a state that was not made"))?;
        Ok((at, &mut states[at].1))
    }

    /// `xs.slice(a, b)` as the expression it cuts and the part it takes, any other expression as itself and no part.
    fn slice_of(&mut self, body: Body<'a>, e: ExprId) -> Result<(ExprId, Option<Range<usize>>), Halt> {
        let ExprKind::Call { callee, args, .. } = &body.ast.expr(e).kind else { return Ok((e, None)) };
        let row = body.callee(e).ok().and_then(|c| body.view.prim(c.def));
        let (Some(PrimRow::Slice), Some(base), [from, to]) = (row, onsa_sema::receiver(body.ast, *callee), &args[..])
        else {
            return Ok((e, None));
        };
        let (Value::Int(_, from, _), Value::Int(_, to, _)) = (self.eval(body, from.expr)?, self.eval(body, to.expr)?)
        else {
            return Err(Fault::Internal("a bound of a slice").into());
        };
        let at = |n: i128| usize::try_from(n).map_err(|_| Fault::Panic(PanicKind::Bounds));
        Ok((base, Some(at(from)?..at(to)?)))
    }

    /// An input of a call: an array of scalars, the column of the `sample` input (else it is a layout of views).
    fn column(&mut self, body: Body<'a>, e: ExprId) -> Result<Vec<Value>, Halt> {
        let (whole, part) = self.slice_of(body, e)?;
        match self.eval(body, whole)? {
            Value::Array(vs) if !vs.iter().any(|v| matches!(v, Value::Array(_))) => Ok(vs[cut(&vs, part)?.1].to_vec()),
            _ => Err(Halt::Skip(Skip::Layout)),
        }
    }
}

/// The expressions of the columns of the `sample` inputs `sampled` that a call of `process` or `render` is given in `rest`: the inputs of a flow of two `sample` inputs or more are the fields of `f.In { x: .., y: .. }` (§11.6), in the order of
/// the declaration; any other layout is skipped.
fn sample_exprs(body: Body, sampled: &[&FlowInput], rest: &[ExprId]) -> Result<Vec<ExprId>, Halt> {
    match (sampled.len() > 1, rest) {
        (true, [one]) => match &body.ast.expr(*one).kind {
            ExprKind::Struct { fields, .. } => sampled
                .iter()
                .map(|i| fields.iter().find(|(n, _)| n.name == i.name).map(|f| f.1))
                .collect::<Option<_>>()
                .ok_or(Halt::Skip(Skip::Layout)),
            _ => Err(Halt::Skip(Skip::Layout)),
        },
        _ => Ok(rest.to_vec()),
    }
}

/// What a call of `process` or `render` was given and gave, kept for the data.
fn run_of(
    (config, params): (&Named<Value>, &Named<Value>),
    frames: Option<usize>,
    inputs: &[(&str, &[Value])],
    outcome: &Outcome,
    (shape, types): (Shape, Types),
) -> Run {
    let outs = if let Outcome::Ok(o) = outcome { Some(o.clone()) } else { None };
    let inputs = inputs.iter().map(|(n, c)| (n.to_string(), c.to_vec())).collect();
    Run { shape, types, config: config.clone(), params: params.clone(), frames, inputs, outs }
}

/// A call of `render` on the evaluator with its `Config` and `Params` and its rate, frames and input columns: what it gave,
/// and the event it is in the data.
fn render_run<'a>(
    host: &mut dyn FnHost,
    view: View<'a>,
    flow: DefId,
    (config, params): (&Named<Value>, &Named<Value>),
    (sample_rate, frames, columns): (f32, Option<usize>, &[Vec<Value>]),
) -> Result<(Outcome, Event), Fault> {
    let decl = view.flow(flow)?;
    let sampled = inputs_at(decl, Stage::Sample)?;
    let inputs = named_columns(&sampled, columns);
    let (cfg, prm) = (by_name(config), by_name(params));
    let call = Call { config: &cfg, params: &prm, inputs: &inputs, frames };
    let outcome = Instance::render(view, flow, sample_rate, &call, Some(host)).map_err(|stop| stop.fault)?;
    let run = run_of((config, params), frames, &inputs, &outcome, io(view, decl, &sampled));
    Ok((outcome, Event::Render { flow: view.qualified_name(flow), written: None, sample_rate, run }))
}

/// The fields of the struct `v` of the struct `def` by name.
fn fields_of(view: View, def: DefId, v: Value) -> Result<Named<Value>, Fault> {
    let Value::Struct(vs) = v else { return Err(Fault::Internal("a struct")) };
    Ok(view.struct_fields(def)?.iter().map(|f| f.name.clone()).zip(vs).collect())
}

/// The host of an expression of the test: a `render` that a helper calls (`fn is_prev(d: F32) -> Bool` of §11.4's edges of
/// `d`) is run on the evaluator as a call of the test is, and any other call is the host's.
struct Door<'d> {
    host: &'d mut dyn FnHost,
    events: &'d mut Vec<Event>,
    generated: &'d mut usize,
    /// The stage of the `render` that panicked, and where the evaluator stopped.
    panic: Option<(PanicAt, Span)>,
}

impl FnHost for Door<'_> {
    fn call(&mut self, call: HostCall) -> Result<Value, Fault> {
        let Some((FlowFn::Render, flow)) = call.view.flow_fn(call.callee.def) else { return self.host.call(call) };
        let (view, sampled) = (call.view, inputs_at(call.view.flow(flow)?, Stage::Sample)?);
        let (mut config, mut params, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for (p, v) in call.callee.func.params.iter().zip(call.args) {
            match view.flow_ty(p.ty) {
                Some((def, FlowTy::Config)) => config = fields_of(view, def, v)?,
                Some((def, FlowTy::Params)) => params = fields_of(view, def, v)?,
                _ => rest.push(v),
            }
        }
        let Some((Value::F32(rate), rest)) = rest.split_last() else { return Err(Fault::Internal("a rate")) };
        let (frames, rest) = match (sampled.is_empty(), rest.split_last()) {
            (true, Some((Value::Int(_, n, _), rest))) => (Some(*n as usize), rest),
            _ => (None, rest),
        };
        let columns: Vec<Vec<Value>> =
            rest.iter().map(|v| if let Value::Array(vs) = v { vs.clone() } else { Vec::new() }).collect();
        let args = (&config, &params);
        let (outcome, event) = render_run(&mut *self.host, view, flow, args, (*rate, frames, &columns))?;
        self.events.push(event);
        *self.generated += 1;
        match outcome {
            Outcome::Ok(outs) => rendered_value(view, call.ret, &outs),
            Outcome::Panic { at, stop } => {
                self.panic = Some((at, stop.at));
                Err(Fault::Panic(PanicKind::Host))
            }
        }
    }
}

/// The value of a `Rendered` that a `render` gave: each of its fields is the frames of one output, or the channels of it
/// (the frames of each) when the output is an array (§11.6).
fn rendered_value(view: View, ret: TyId, outs: &[Value]) -> Result<Value, Fault> {
    let (def, _) = view.flow_ty(ret).ok_or(Fault::Internal("a `Rendered`"))?;
    let field = |at: usize| -> Result<Value, Fault> {
        let frames: Vec<Value> = outs.iter().map(|v| part(v, at)).collect();
        match frames.first() {
            Some(Value::Array(a)) => {
                let channel = |k| frames.iter().map(|v| elem(v, k)).collect::<Result<_, _>>().map(Value::Array);
                (0..a.len()).map(channel).collect::<Result<_, _>>().map(Value::Array)
            }
            _ => Ok(Value::Array(frames)),
        }
    };
    Ok(Value::Struct((0..view.struct_fields(def)?.len()).map(field).collect::<Result<_, _>>()?))
}

/// The path of the flow of the call `e` of a generated function as the test writes it (`b.dup` of `b.dup.render(..)`).
fn written_flow(body: Body, e: ExprId) -> Option<String> {
    fn dotted(body: Body, e: ExprId) -> Option<String> {
        match &body.ast.expr(e).kind {
            ExprKind::Path(p) => Some(p.dotted()),
            ExprKind::Field { base, name } => Some(format!("{}.{}", dotted(body, *base)?, name.name)),
            _ => None,
        }
    }
    let ExprKind::Call { callee, .. } = &body.ast.expr(e).kind else { return None };
    match &body.ast.expr(*callee).kind {
        ExprKind::Field { base, .. } => dotted(body, *base),
        ExprKind::Path(p) => Some(p.dotted().rsplit_once('.')?.0.to_string()),
        _ => None,
    }
}

/// The leaves of the output of a flow, and the types of its `sample` inputs and of those leaves (a struct output is its
/// fields; an array is its channels, and its element is the type).
fn io(view: View, decl: &FlowDef, sampled: &[&FlowInput]) -> (Shape, Types) {
    let channels = |t| match view.ty(t) {
        Ty::Array(_, Len::Const(n)) => Some(*n as usize),
        _ => None,
    };
    let element = |t| match view.ty(t) {
        Ty::Array(e, _) => *e,
        _ => t,
    };
    let leaves: Vec<(String, TyId)> = match view.ty(decl.out) {
        Ty::Named(def, _) => match view.struct_fields(*def) {
            Ok(fields) if !fields.is_empty() => fields.iter().map(|f| (format!(".{}", f.name), f.ty)).collect(),
            _ => vec![(String::new(), decl.out)],
        },
        _ => vec![(String::new(), decl.out)],
    };
    let types = Types {
        inputs: sampled.iter().map(|i| view.display_type(i.ty)).collect(),
        leaves: leaves.iter().map(|(_, t)| view.display_type(element(*t))).collect(),
        zeros: leaves.iter().map(|(_, t)| Scalar::of(view.ty(element(*t))).and_then(Scalar::default_value)).collect(),
    };
    (leaves.into_iter().map(|(p, t)| (p, channels(t))).collect(), types)
}

/// The columns of the inputs by the name of the `sample` input each is given to.
fn named_columns<'c>(sampled: &[&'c FlowInput], columns: &'c [Vec<Value>]) -> Vec<(&'c str, &'c [Value])> {
    sampled.iter().map(|i| i.name.as_str()).zip(columns.iter().map(|c| &c[..])).collect()
}

/// The part `part` of `vs` (all of it when none) as its length and range; a range that is not inside is a panic.
// S-1148: `xs.slice(from, to)` with `from > to` panics, as in the interpreter, apart from an index
// out of range.
fn cut(vs: &[Value], part: Option<Range<usize>>) -> Result<(usize, Range<usize>), Fault> {
    let at = part.unwrap_or(0..vs.len());
    Ok((vs.get(at.clone()).ok_or(Fault::Panic(PanicKind::Bounds))?.len(), at))
}

/// A stop of the call at `at`: a panic is the test's, at that stage; the others are the faults they are.
fn stopped(stop: Stop, at: PanicAt) -> Halt {
    if matches!(stop.fault, Fault::Panic(_)) { Halt::Panic(Panic::Call(at), Some(stop.at)) } else { stop.into() }
}

fn by_name(v: &[(String, Value)]) -> Vec<(&str, Value)> {
    v.iter().map(|(n, x)| (n.as_str(), x.clone())).collect()
}

/// Does `e` have, or read, a value of a view (`In`, `Out`, `Span`, `Buf`: the layout of the C API, W7-12), or an array of them?
fn views(body: Body, e: ExprId) -> bool {
    let of = body.ty_id(e).ok().is_some_and(|mut t| {
        while let Ty::Array(elem, _) = body.view.ty(t) {
            t = *elem;
        }
        body.view.flow_ty(t).is_some_and(|(_, f)| f.views()) || matches!(body.view.ty(t), Ty::Builtin(..))
    });
    of || body.ast.sub_exprs(e).into_iter().any(|x| views(body, x))
}
