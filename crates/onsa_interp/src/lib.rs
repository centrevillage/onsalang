//! Interpreter for Onsa Core; the reference semantics (M3, T3-7).
//!
//! A tree walker over [`onsa_core::Module`]. Numerics follow spec §3.4 and
//! §13.4 exactly: `F32` arithmetic stays in `f32`, integer operators are
//! checked / wrapping / saturating per instruction, every index is
//! bounds-checked, and a panic (§9.2) unwinds to the nearest call made from
//! outside the interpreter (a test, a `const` initializer, a tool).
//!
//! # Places and aliasing
//!
//! Every local lives in a [`Slot`]; an `inout` parameter is an alias of the
//! caller's place (slot + projections), so writes through it land in the
//! caller's storage. `Span` values carry their slot too (see `value.rs`).
//!
//! # Decisions recorded for the spec (S-25)
//!
//! - `round` is round-half-to-even (IEEE `roundToIntegralTiesToEven`, like
//!   the `round_f32` conversions of §3.3, WASM `nearest`, C `rint` under the
//!   default rounding mode). Half-away-from-zero is not available.
//! - `min` / `max` return NaN when either operand is NaN (WASM / JS
//!   semantics; the C backend must not use `fminf`), `min(-0.0, 0.0)` is
//!   `-0.0` and `max(-0.0, 0.0)` is `0.0`.

pub mod value;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use onsa_core::prim::{CheckedOp, MathFn, NAN_BITS_F32, NAN_BITS_F64, Prim};
use onsa_core::{
    Arg, BinOp, Block, CmpOp, ConstId, Expr, ExprKind, FloatKind, FnId, IntKind, Lit, LocalId, LogicOp, Mode, Module,
    MsgId, Overflow, Place, Stmt, StmtKind, Ty, TypeDefKind, UnOp,
};
use onsa_diag::{Diagnostic, Span};

pub use value::{ArrayData, Proj, Slot, SpanRef, Value, show, slot, zero};
use value::{clamp_int, in_range, int_value, wrap_int, zero_array};

/// A panic of the program (spec §9.2, and a call beyond the depth limit of
/// §12.5) with the position of the instruction that raised it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Panic {
    pub message: String,
    pub span: Span,
}

/// A form this version of the interpreter cannot run: E0200 (spec §18.1,
/// S-224). [`unsupported`] finds every one in a module before it runs; an
/// evaluation that reaches one stops with it. Today the one kind is a call of
/// a `std` `target fn` the interpreter does not implement ([`std_prim`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported {
    /// The qualified name of the `std` function (`std.test.gen.f32`).
    pub std_fn: String,
    pub span: Span,
}

impl Unsupported {
    /// Its E0200 (spec §18.1, S-224): the one place that words the feature
    /// and the note.
    pub fn diagnostic(&self) -> Diagnostic {
        onsa_diag::unsupported::Feature::InterpreterStdFn.diagnostic(
            onsa_diag::Stage::Build,
            self.span,
            &[&self.std_fn],
        )
    }
}

/// Why an evaluation gave no value.
///
/// A failure of the interpreter itself (a value of the wrong type, a place
/// that does not exist, control flow that escapes a function: a state the
/// Core verifier should have ruled out) is neither: it is an internal error
/// (S-67, R-92, R-137) that unwinds through [`onsa_diag::internal::bug`] to
/// the guard of the caller (`onsa_driver::guard`). Every entry runs under one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    Panic(Panic),
    Unsupported(Unsupported),
}

impl Failure {
    /// The position of the failure.
    pub fn span(&self) -> Span {
        match self {
            Failure::Panic(p) => p.span,
            Failure::Unsupported(u) => u.span,
        }
    }
}

/// Non-local control flow inside the interpreter.
#[derive(Debug)]
enum Signal {
    Fail(Failure),
    Return(Value),
    Break,
    Continue,
}

type R<T> = Result<T, Signal>;

fn panic<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(Signal::Fail(Failure::Panic(Panic { message: msg.into(), span })))
}

/// The interpreter found a state it cannot be in at `span`: an internal
/// error (S-67), never a panic of the program (R-137).
#[cold]
#[inline(never)]
#[track_caller]
fn internal(span: Span, msg: impl Into<String>) -> ! {
    onsa_diag::internal::bug(Some(span), msg)
}

/// The `std` `target fn`s the interpreter runs itself ([`Prim::Std`]). The
/// one place that decides which it runs (D-15): [`unsupported`] and the
/// evaluation both ask [`std_prim`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StdPrim {
    AssertNear,
}

fn std_prim(name: &str) -> Option<StdPrim> {
    match name {
        "std.dsp.test.assert_near" => Some(StdPrim::AssertNear),
        _ => None,
    }
}

fn std_unsupported(name: &str, span: Span) -> Unsupported {
    Unsupported { std_fn: name.to_string(), span }
}

/// Every form of `m` this version of the interpreter cannot run (E0200,
/// S-224), in the order of the module: the `std` `target fn`s it does not
/// implement, in every function body and every `const` initializer. `onsa
/// test` reports them before it runs any test, so what it reports does not
/// depend on which code the tests reach.
pub fn unsupported(m: &Module) -> Vec<Unsupported> {
    let mut out = Vec::new();
    let mut visit = |e: &Expr| {
        if let ExprKind::Prim { prim: Prim::Std(name), .. } = &e.kind
            && std_prim(name).is_none()
        {
            out.push(std_unsupported(name, e.span));
        }
    };
    for f in &m.fns {
        if let Some(b) = &f.body {
            onsa_core::walk::walk_block(b, &mut visit);
        }
    }
    for c in &m.consts {
        onsa_core::walk::walk_expr(&c.init, &mut visit);
    }
    out
}

/// A resolved memory location: a slot and the projections inside its value.
#[derive(Debug, Clone)]
struct PlaceRef {
    root: Slot,
    projs: Vec<Proj>,
}

/// What a local binding refers to.
#[derive(Debug, Clone)]
enum Loc {
    Slot(Slot),
    /// An `inout` parameter: the caller's place.
    Alias(PlaceRef),
}

struct Frame {
    locals: Vec<Option<Loc>>,
}

/// A leaf found by walking projections.
enum Leaf<'a> {
    Val(&'a Value),
    F32(f32),
}

enum LeafMut<'a> {
    Val(&'a mut Value),
    F32(&'a mut f32),
}

/// An argument after evaluation: a value, or the caller's place for `inout`.
enum ArgVal {
    Val(Value),
    Place(PlaceRef),
}

/// A sequence a prim reads or writes: the array at `root` + `projs`, from
/// `start` for `len` elements.
struct SeqRef {
    root: Slot,
    projs: Vec<Proj>,
    start: u32,
    len: u32,
}

enum ConstState {
    Unevaluated,
    InProgress,
    Done(Value),
}

/// The upper limit of the call depth (spec §12.5, S-222, R-05, R-112): the
/// calls nested in one evaluation, which starts at depth 0 (the body of a
/// `test`, a `const` initializer, any other entry from outside the
/// interpreter). Calls 1 to 128 run; the 129th is a panic of the program, at
/// that call. A tail call counts; reading a `const` is not a call, and its
/// initializer is an evaluation of its own, from 0. The same in every build.
///
/// The stack it needs (R-05: measured, `measure_the_stack_of_calls_and_levels`
/// in the unit tests prints it). The interpreter runs on a thread with
/// [`onsa_diag::stack::STACK_SIZE`] (64 MiB) of stack, and the safety net keeps
/// [`STACK_RESERVE`] (4 MiB) of it, so a call may use 60 MiB / 128 = 480 K
/// before the net comes before the limit. What a call uses is its body's
/// frames down to the next call: the expressions around that call nest up to
/// 256 levels (spec §2.5, S-183). Measured on aarch64-apple-darwin
/// (2026-10-08, again after W2-03), bytes of stack, with `onsa_interp` at
/// `opt-level = 1` in the dev profile (`Cargo.toml`):
///
/// | | debug | release |
/// |---|---|---|
/// | one call, no nesting (`1 + f(n - 1)`) | 1.0 K | 0.7 K |
/// | one level of `0 + (x)` | 0.3 K | 0.3 K |
/// | one level of `(x, 0).0` | 0.7 K | 0.7 K |
/// | one level of `match`, `[x][0]` (the most) | 0.8 K | 0.7–0.8 K |
///
/// The arms of [`Interp::eval`] take the expression, not its span: a span
/// passed by value kept `eval`'s frame under each level (W2-03 measured 0.6 K
/// a level of `0 + (x)` that way).
///
/// So 128 calls, each under 256 levels of the most expensive kind, use 27 MB
/// in debug and 27 MB in release, less than half of the 60 MiB (the unit
/// tests `the_limit_comes_before_the_net_under_256_levels` and
/// `measure_the_stack_of_calls_and_levels`). Without the `opt-level` the debug
/// build uses 4.2 K a call and up to 5.1 K a level, and the net would come
/// first under about 96 levels. The guarantee in every environment (the
/// evaluator keeps its own stack) is W9-03's.
pub const MAX_CALL_DEPTH: u32 = 128;

/// The safety net under [`MAX_CALL_DEPTH`] (R-05): every call and every entry
/// checks the stack left to the thread ([`onsa_diag::stack::remaining`]), and
/// below this many bytes it stops with an internal error (S-67), not a signal.
/// With a right limit the limit comes first and the net is never reached by
/// calls; reaching it means the limit does not fit the stack, a bug of the
/// compiler.
///
/// The reserve is also the most stack one stretch between two checks may use:
/// the body of one function down to its next call, whose expressions nest up
/// to 256 levels (S-183, W3-14): 256 × 0.9 K = 0.23 MiB here, and 256 × 5.1 K
/// = 1.3 MiB in a debug build without the `opt-level`, both below 4 MiB. When
/// the nesting limit grows, measure this again.
///
/// The nested evaluations of `const`s (a `const` read in an initializer,
/// whose initializer reads another, ...) are not calls and have no limit
/// (S-222): every one checks the net at its entry, and a chain too long for
/// the stack stops with the internal error. A stand-in until W9-03 evaluates
/// the `const`s in the order of their dependencies, with no recursion.
pub const STACK_RESERVE: usize = 4 << 20;

// The reserve is a part of the stack of a command.
const _: () = assert!(STACK_RESERVE < onsa_diag::stack::STACK_SIZE);

pub struct Interp<'m> {
    pub m: &'m Module,
    consts: Vec<RefCell<ConstState>>,
    /// The calls nested in the current evaluation (see [`MAX_CALL_DEPTH`]).
    depth: Cell<u32>,
    /// The evaluations running: more than one when a `const` is evaluated
    /// inside another evaluation (only for the message of the safety net).
    evals: Cell<u32>,
}

/// Where the safety net is checked.
#[derive(Clone, Copy)]
enum Check {
    /// A call nested in an evaluation.
    Call,
    /// The entry of an evaluation (a call from outside, a `const`).
    Entry,
}

/// Puts the depth of the evaluation that was running, and the number of
/// evaluations running, back when an entry ends, also when an internal error
/// unwinds through it (P-1: a tool may go on with the same interpreter after
/// an internal error).
struct DepthBack<'a> {
    depth: &'a Cell<u32>,
    saved: u32,
    evals: &'a Cell<u32>,
}

impl Drop for DepthBack<'_> {
    fn drop(&mut self) {
        self.depth.set(self.saved);
        self.evals.set(self.evals.get() - 1);
    }
}

/// Puts a `const` that is being evaluated back to unevaluated when its
/// evaluation does not finish with a value (a panic, or an internal error
/// that unwinds), so that a later read evaluates it again and does not see
/// it as depending on itself.
struct ConstBack<'a>(&'a RefCell<ConstState>);

impl Drop for ConstBack<'_> {
    fn drop(&mut self) {
        let mut st = self.0.borrow_mut();
        if matches!(*st, ConstState::InProgress) {
            *st = ConstState::Unevaluated;
        }
    }
}

impl<'m> Interp<'m> {
    pub fn new(m: &'m Module) -> Interp<'m> {
        Interp {
            m,
            consts: m.consts.iter().map(|_| RefCell::new(ConstState::Unevaluated)).collect(),
            depth: Cell::new(0),
            evals: Cell::new(0),
        }
    }

    pub fn fn_by_name(&self, name: &str) -> Option<FnId> {
        self.m.fns.iter().position(|f| f.name == name).map(|i| FnId(i as u32))
    }

    /// Call a function with by-value arguments (an `inout` parameter gets a
    /// fresh slot, so the caller does not see its writes; use
    /// [`Interp::call_inout`] for that).
    ///
    /// A call from outside is the entry of an evaluation: its body is at
    /// depth 0 (spec §12.5). Every entry runs on a thread with the stack of a
    /// command ([`onsa_diag::stack`]); on another thread it stops with an
    /// internal error (S-67). A host without such a thread (the browser's
    /// IDE, `onsa_web`) needs another way to bound the stack before it runs
    /// the interpreter: the evaluator with its own stack of W9-03, or a
    /// [`onsa_diag::stack::remaining`] of its own.
    pub fn call(&self, fn_: FnId, args: Vec<Value>) -> Result<Value, Failure> {
        let site = self.m.fn_(fn_).span;
        let args = args.into_iter().map(ArgVal::Val).collect();
        self.enter(site, || self.run_body(fn_, args)).map_err(|s| Self::failure_of(s, site))
    }

    /// Call with an `inout` first argument held in `state` (flows: `process(inout s, ...)`).
    pub fn call_inout(&self, fn_: FnId, state: &Slot, rest: Vec<Value>) -> Result<Value, Failure> {
        let mut args = vec![ArgVal::Place(PlaceRef { root: state.clone(), projs: Vec::new() })];
        args.extend(rest.into_iter().map(ArgVal::Val));
        let site = self.m.fn_(fn_).span;
        self.enter(site, || self.run_body(fn_, args)).map_err(|s| Self::failure_of(s, site))
    }

    /// Value of a `const` (evaluated on first use; T3-9), from wherever it is
    /// read: its initializer is an evaluation of its own (spec §12.5).
    pub fn const_value(&self, id: ConstId) -> Result<Value, Failure> {
        let at = self.m.const_(id).init.span;
        self.const_val(id).map_err(|s| Self::failure_of(s, at))
    }

    /// What an entry at `at` gives back: only a failure leaves an entry
    /// ([`Interp::run_body`] and [`Interp::eval_const`] take the rest).
    fn failure_of(s: Signal, at: Span) -> Failure {
        match s {
            Signal::Fail(f) => f,
            Signal::Return(_) | Signal::Break | Signal::Continue => internal(at, "control flow escaped an evaluation"),
        }
    }

    /// A `const`: its value when evaluated, else the evaluation of its
    /// initializer as an entry of its own, from depth 0, whatever the depth of
    /// the read (spec §12.5, S-222). So whether it succeeds does not depend on
    /// where or in which order it is read first (the order of the tests,
    /// `--filter`, `onsa test` or a build). Only a value is kept: a failed
    /// evaluation is made again at the next read, with the same result.
    fn const_val(&self, id: ConstId) -> R<Value> {
        match &*self.consts[id.0 as usize].borrow() {
            ConstState::Done(v) => return Ok(v.clone()),
            ConstState::InProgress => return self.const_cycle(id),
            ConstState::Unevaluated => {}
        }
        self.enter(self.m.const_(id).init.span, || self.eval_const(id))
    }

    #[cold]
    #[inline(never)]
    fn const_cycle(&self, id: ConstId) -> R<Value> {
        let c = self.m.const_(id);
        panic(c.init.span, format!("const `{}` depends on itself", c.name))
    }

    /// The initializer of `id`, inside its entry. Going beyond the call
    /// depth limit is a panic of the evaluation, as any other: E0419 at the
    /// initializer (spec §6.6) is W9-03's; until then `onsa test` fails the
    /// test that reads the `const`, and a build stops with the C backend's
    /// E0200 (`inline_consts`).
    #[inline(never)]
    fn eval_const(&self, id: ConstId) -> R<Value> {
        let cell = &self.consts[id.0 as usize];
        *cell.borrow_mut() = ConstState::InProgress;
        let _back = ConstBack(cell);
        let mut f = Frame { locals: Vec::new() };
        let init = &self.m.const_(id).init;
        match self.eval(&mut f, init) {
            Ok(v) => {
                *cell.borrow_mut() = ConstState::Done(v.clone());
                Ok(v)
            }
            Err(Signal::Fail(e)) => Err(Signal::Fail(e)),
            // Not out of an initializer into the evaluation that reads it.
            Err(Signal::Return(_) | Signal::Break | Signal::Continue) => {
                internal(init.span, "control flow escaped a `const` initializer")
            }
        }
    }

    // ------------------------------------------------------------ calls

    /// The entry of an evaluation at `at` (spec §12.5): `f` counts its calls
    /// from depth 0, and the depth of the evaluation that was running comes
    /// back after it, also when an internal error unwinds. The one place an
    /// evaluation starts; [`Interp::call_with`] is the one place a call is
    /// counted.
    fn enter<T>(&self, at: Span, f: impl FnOnce() -> R<T>) -> R<T> {
        self.check_stack(at, Check::Entry);
        self.evals.set(self.evals.get() + 1);
        let _back = DepthBack { depth: &self.depth, saved: self.depth.replace(0), evals: &self.evals };
        f()
    }

    /// The safety net (see [`STACK_RESERVE`]) at a call or an entry at `at`.
    #[inline(always)]
    fn check_stack(&self, at: Span, check: Check) {
        match onsa_diag::stack::remaining() {
            Some(left) if left >= STACK_RESERVE => {}
            left => self.out_of_stack(at, check, left),
        }
    }

    #[cold]
    #[inline(never)]
    fn out_of_stack(&self, at: Span, check: Check, left: Option<usize>) -> ! {
        let Some(left) = left else {
            onsa_diag::internal::bug(
                Some(at),
                "the interpreter runs on a thread without the stack of a command (`onsa_diag::stack`)",
            )
        };
        let used = onsa_diag::stack::STACK_SIZE - left;
        // The evaluations the stack holds: the running ones, and the one an
        // entry starts.
        let evals = self.evals.get() + matches!(check, Check::Entry) as u32;
        let message = if evals > 1 {
            // A `const` read inside another evaluation: not a call (S-222).
            format!(
                "the interpreter has used {used} bytes of stack in {evals} nested evaluations: the `const`s read \
                 inside other evaluations, each an evaluation of its own and not counted as calls (S-222), nest \
                 deeper than the stack holds (W9-03 evaluates the `const`s in the order of their dependencies)"
            )
        } else {
            match check {
                Check::Call => format!(
                    "the interpreter has used {used} bytes of stack at a call depth of {}, below the limit of \
                     {MAX_CALL_DEPTH}: the limit does not fit the stack",
                    self.depth.get()
                ),
                Check::Entry => format!("an evaluation starts with only {left} bytes of stack left"),
            }
        };
        onsa_diag::internal::bug(Some(at), message)
    }

    /// A call of `fn_` made at `site`, nested in an evaluation: the one place
    /// the call depth is counted (spec §12.5).
    ///
    /// Each frame on the way down a recursion (this one, [`Interp::exec_block`],
    /// [`Interp::exec`], [`Interp::eval`] and the arm of `eval` that holds the
    /// call) is kept small: an arm with more locals, or a message to format, is
    /// a function of its own, off the way down (R-05).
    fn call_with(&self, fn_: FnId, args: Vec<ArgVal>, site: Span) -> R<Value> {
        // The limit comes before the safety net, so a right limit is reached
        // first.
        if self.depth.get() >= MAX_CALL_DEPTH {
            return depth_limit(site);
        }
        self.check_stack(site, Check::Call);
        self.depth.set(self.depth.get() + 1);
        let r = self.run_body(fn_, args);
        self.depth.set(self.depth.get() - 1);
        r
    }

    /// The body of `fn_` with its parameters bound to `args`, not counted.
    #[inline(always)]
    fn run_body(&self, fn_: FnId, args: Vec<ArgVal>) -> R<Value> {
        let f = self.m.fn_(fn_);
        let Some(body) = &f.body else { return self.no_body(fn_) };
        let mut frame = self.bind_params(fn_, args)?;
        match self.exec_block(&mut frame, body) {
            Ok(v) | Err(Signal::Return(v)) => Ok(v),
            Err(Signal::Break) | Err(Signal::Continue) => internal(f.span, "loop control outside a loop"),
            Err(e) => Err(e),
        }
    }

    /// A call of a function without a body: lowering turns every call of a
    /// `target fn` into a primitive or E0200 (`lower/body.rs`), so Core never
    /// calls one (an internal error, S-67).
    #[cold]
    #[inline(never)]
    fn no_body(&self, fn_: FnId) -> R<Value> {
        let f = self.m.fn_(fn_);
        internal(f.span, format!("a call of `{}`, which has no body", f.name))
    }

    /// The frame of a call of `fn_`, with the parameters bound to `args`.
    #[inline(never)]
    fn bind_params(&self, fn_: FnId, args: Vec<ArgVal>) -> R<Frame> {
        let f = self.m.fn_(fn_);
        if args.len() != f.params.len() {
            internal(f.span, format!("`{}` called with {} arguments", f.name, args.len()));
        }
        let mut frame = Frame { locals: vec![None; f.locals.len()] };
        for (p, a) in f.params.iter().zip(args) {
            let loc = match (p.mode, a) {
                (Mode::Inout, ArgVal::Place(pr)) => Loc::Alias(pr),
                (_, ArgVal::Val(v)) => Loc::Slot(slot(v)),
                (_, ArgVal::Place(pr)) => Loc::Slot(slot(self.read(&pr, f.span)?)),
            };
            frame.locals[p.local.0 as usize] = Some(loc);
        }
        Ok(frame)
    }

    // ------------------------------------------------------------ places

    fn local_place(&self, f: &Frame, l: LocalId, span: Span) -> R<PlaceRef> {
        match &f.locals[l.0 as usize] {
            Some(Loc::Slot(s)) => Ok(PlaceRef { root: s.clone(), projs: Vec::new() }),
            Some(Loc::Alias(p)) => Ok(p.clone()),
            None => internal(span, "local read before initialization"),
        }
    }

    fn resolve_place(&self, f: &mut Frame, p: &Place, span: Span) -> R<PlaceRef> {
        match p {
            Place::Local(l) => self.local_place(f, *l, span),
            Place::Field(b, i) => {
                let r = self.resolve_place(f, b, span)?;
                self.project_field(r, *i, span)
            }
            Place::Index(b, e) => {
                let i = self.eval_u32(f, e)?;
                let r = self.resolve_place(f, b, span)?;
                self.project_index(r, i, span)
            }
        }
    }

    fn project_field(&self, mut r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        let ok = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Struct(fs)) | Leaf::Val(Value::Tuple(fs)) | Leaf::Val(Value::Enum { fields: fs, .. }) => {
                (i as usize) < fs.len()
            }
            _ => false,
        })?;
        if !ok {
            internal(span, "field projection on a non-aggregate");
        }
        r.projs.push(Proj::Field(i));
        Ok(r)
    }

    /// Index into the sequence at `r`, following `Span` / `Buf` indirection.
    fn project_index(&self, r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        enum Kind {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let kind = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => Kind::Array(a.len()),
            Leaf::Val(Value::Span(s)) => Kind::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => Kind::Buf(b.clone()),
            _ => Kind::Other,
        })?;
        match kind {
            Kind::Array(len) => {
                if i >= len {
                    return panic(span, format!("index {i} out of range for a sequence of length {len}"));
                }
                let mut r = r;
                r.projs.push(Proj::Index(i));
                Ok(r)
            }
            Kind::Span(s) => {
                if i >= s.len {
                    return panic(span, format!("index {i} out of range for a span of length {}", s.len));
                }
                let mut projs = s.projs.clone();
                projs.push(Proj::Index(s.start + i));
                Ok(PlaceRef { root: s.root, projs })
            }
            Kind::Buf(b) => {
                let len = buf_len(&b, span);
                if i >= len {
                    return panic(span, format!("index {i} out of range for a buffer of length {len}"));
                }
                Ok(PlaceRef { root: b, projs: vec![Proj::Index(i)] })
            }
            Kind::Other => internal(span, "index on a non-sequence"),
        }
    }

    fn walk<'a>(v: &'a Value, projs: &[Proj]) -> Option<Leaf<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get(*i as usize).map(|x| Leaf::F32(*x)) } else { None };
                }
                _ => return None,
            }
        }
        Some(Leaf::Val(cur))
    }

    fn walk_mut<'a>(v: &'a mut Value, projs: &[Proj]) -> Option<LeafMut<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get_mut(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get_mut(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get_mut(*i as usize).map(LeafMut::F32) } else { None };
                }
                _ => return None,
            }
        }
        Some(LeafMut::Val(cur))
    }

    fn peek<T>(&self, r: &PlaceRef, span: Span, f: impl FnOnce(Leaf<'_>) -> T) -> R<T> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(leaf) => Ok(f(leaf)),
            None => internal(span, "dangling place"),
        }
    }

    fn read(&self, r: &PlaceRef, span: Span) -> R<Value> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => internal(span, "dangling place"),
        }
    }

    fn write(&self, r: &PlaceRef, value: Value, span: Span) -> R<()> {
        let mut v = r.root.borrow_mut();
        match Self::walk_mut(&mut v, &r.projs) {
            Some(LeafMut::Val(x)) => {
                *x = value;
                Ok(())
            }
            Some(LeafMut::F32(x)) => match value {
                Value::F32(y) => {
                    *x = y;
                    Ok(())
                }
                _ => internal(span, "non-F32 written into an F32 array"),
            },
            None => internal(span, "dangling place"),
        }
    }

    /// The sequence an expression denotes (a `Span` value, a `Buf`, or an
    /// array place); temporaries are copied into a fresh slot.
    fn seq_of_arg(&self, f: &mut Frame, a: &Arg) -> R<SeqRef> {
        let span = a.expr.span;
        if a.mode == Mode::Inout
            && let Some(p) = a.expr.as_place()
        {
            let r = self.resolve_place(f, &p, span)?;
            return self.seq_of_place(r, span);
        }
        let v = self.eval(f, &a.expr)?;
        self.seq_of_value(v, span)
    }

    fn seq_of_place(&self, r: PlaceRef, span: Span) -> R<SeqRef> {
        enum K {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let k = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => K::Array(a.len()),
            Leaf::Val(Value::Span(s)) => K::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => K::Buf(b.clone()),
            _ => K::Other,
        })?;
        match k {
            K::Array(len) => Ok(SeqRef { root: r.root, projs: r.projs, start: 0, len }),
            K::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            K::Buf(b) => {
                let len = buf_len(&b, span);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            K::Other => internal(span, "sequence expected"),
        }
    }

    fn seq_of_value(&self, v: Value, span: Span) -> R<SeqRef> {
        match v {
            Value::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            Value::Buf(b) => {
                let len = buf_len(&b, span);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            Value::Array(a) => {
                let len = a.len();
                Ok(SeqRef { root: slot(Value::Array(a)), projs: Vec::new(), start: 0, len })
            }
            _ => internal(span, "sequence expected"),
        }
    }

    fn seq_get(&self, s: &SeqRef, i: u32, span: Span) -> R<Value> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        let r = PlaceRef { root: s.root.clone(), projs };
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => internal(span, "dangling sequence"),
        }
    }

    fn seq_set(&self, s: &SeqRef, i: u32, v: Value, span: Span) -> R<()> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        self.write(&PlaceRef { root: s.root.clone(), projs }, v, span)
    }

    /// Fast path: the `f32` slice of a sequence, when its storage is `F32`.
    fn with_f32_slice<T>(&self, s: &SeqRef, f: impl FnOnce(&mut [f32]) -> T) -> Option<T> {
        let mut v = s.root.borrow_mut();
        match Self::walk_mut(&mut v, &s.projs) {
            Some(LeafMut::Val(Value::Array(ArrayData::F32(xs)))) => {
                let (a, b) = (s.start as usize, (s.start + s.len) as usize);
                Some(f(&mut xs[a..b]))
            }
            _ => None,
        }
    }

    // ------------------------------------------------------------ statements

    /// Run a block; its value, or `()`.
    fn exec_block(&self, f: &mut Frame, b: &Block) -> R<Value> {
        for s in &b.stmts {
            self.exec(f, s)?;
        }
        match &b.value {
            Some(e) => self.eval(f, e),
            None => Ok(Value::Unit),
        }
    }

    /// A statement. Each kind with locals of its own is a function (R-05).
    fn exec(&self, f: &mut Frame, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => self.exec_let(f, *l, e),
            StmtKind::Assign(p, e) => self.exec_assign(f, p, e, s.span),
            StmtKind::Expr(e) => self.exec_expr(f, e),
            StmtKind::If(c, t, e) => self.exec_if(f, c, t, e),
            StmtKind::While(c, body) => self.exec_while(f, c, body),
            StmtKind::ForRange(l, lo, hi, body) => self.exec_for(f, *l, lo, hi, body, s.span),
            StmtKind::Break => Err(Signal::Break),
            StmtKind::Continue => Err(Signal::Continue),
            StmtKind::Return(e) => self.exec_return(f, e.as_ref()),
        }
    }

    #[inline(never)]
    fn exec_let(&self, f: &mut Frame, l: LocalId, e: &Expr) -> R<()> {
        let v = self.eval(f, e)?;
        f.locals[l.0 as usize] = Some(Loc::Slot(slot(v)));
        Ok(())
    }

    #[inline(never)]
    fn exec_expr(&self, f: &mut Frame, e: &Expr) -> R<()> {
        self.eval(f, e)?;
        Ok(())
    }

    #[inline(never)]
    fn exec_if(&self, f: &mut Frame, c: &Expr, t: &Block, e: &Block) -> R<()> {
        let c = self.eval_bool(f, c)?;
        self.exec_block(f, if c { t } else { e })?;
        Ok(())
    }

    #[inline(never)]
    fn exec_return(&self, f: &mut Frame, e: Option<&Expr>) -> R<()> {
        let v = match e {
            Some(e) => self.eval(f, e)?,
            None => Value::Unit,
        };
        Err(Signal::Return(v))
    }

    #[inline(never)]
    fn exec_assign(&self, f: &mut Frame, p: &Place, e: &Expr, span: Span) -> R<()> {
        let v = self.eval(f, e)?;
        let r = self.resolve_place(f, p, span)?;
        self.write(&r, v, span)
    }

    #[inline(never)]
    fn exec_while(&self, f: &mut Frame, c: &Expr, body: &Block) -> R<()> {
        while self.eval_bool(f, c)? {
            match self.exec_block(f, body) {
                Ok(_) | Err(Signal::Continue) => {}
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    #[inline(never)]
    fn exec_for(&self, f: &mut Frame, l: LocalId, lo: &Expr, hi: &Expr, body: &Block, span: Span) -> R<()> {
        let lo_v = self.eval(f, lo)?;
        let hi_v = self.eval(f, hi)?;
        let kind = int_kind_of(&lo_v, span);
        let (lo_i, hi_i) = (int_of(&lo_v, kind, span), int_of(&hi_v, kind, span));
        let var = slot(lo_v);
        f.locals[l.0 as usize] = Some(Loc::Slot(var.clone()));
        let mut i = lo_i;
        while i < hi_i {
            *var.borrow_mut() = int_value(kind, i);
            match self.exec_block(f, body) {
                Ok(_) | Err(Signal::Continue) => {}
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
            i += 1;
        }
        Ok(())
    }

    // ------------------------------------------------------------ expressions

    fn eval_bool(&self, f: &mut Frame, e: &Expr) -> R<bool> {
        let v = self.eval(f, e)?;
        Ok(bool_of(&v, e.span))
    }

    /// An index, a length, a bound of a slice: a `U32` and nothing else (R-92).
    #[inline(never)]
    fn eval_u32(&self, f: &mut Frame, e: &Expr) -> R<u32> {
        let v = self.eval(f, e)?;
        Ok(int_of(&v, IntKind::U32, e.span) as u32)
    }

    fn eval_args(&self, f: &mut Frame, args: &[Arg]) -> R<Vec<ArgVal>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            if a.mode == Mode::Inout
                && let Some(p) = a.expr.as_place()
            {
                out.push(ArgVal::Place(self.resolve_place(f, &p, a.expr.span)?));
            } else {
                out.push(ArgVal::Val(self.eval(f, &a.expr)?));
            }
        }
        Ok(out)
    }

    /// The values of `xs`, in order.
    fn eval_all(&self, f: &mut Frame, xs: &[Expr]) -> R<Vec<Value>> {
        let mut out = Vec::with_capacity(xs.len());
        for x in xs {
            out.push(self.eval(f, x)?);
        }
        Ok(out)
    }

    /// An expression. The dispatch only: every kind with locals of its own is
    /// a function, so that this frame, which is on the way down every
    /// recursion, stays small (R-05).
    fn eval(&self, f: &mut Frame, e: &Expr) -> R<Value> {
        let span = e.span;
        match &e.kind {
            ExprKind::Lit(l) => self.eval_lit(l, e),
            ExprKind::Local(l) => self.eval_local(f, *l, span),
            ExprKind::Const(c) => self.const_val(*c),
            ExprKind::Zeroed => self.eval_zeroed(&e.ty),
            ExprKind::Unary(op, x) => self.eval_unary(f, *op, x, e),
            ExprKind::Binary { op, overflow, lhs, rhs } => self.eval_binary(f, (*op, *overflow), lhs, rhs, e),
            ExprKind::Cmp { op, lhs, rhs } => self.eval_cmp(f, *op, lhs, rhs, e),
            ExprKind::Logic { op, lhs, rhs } => self.eval_logic(f, *op, lhs, rhs),
            ExprKind::Cast(x) => self.eval_cast(f, x, e),
            ExprKind::Call { fn_, args } => self.eval_call(f, *fn_, args, e),
            ExprKind::Prim { prim, args } => self.prim(f, prim, args, &e.ty, span),
            ExprKind::Field { base, index } => self.eval_field(f, base, *index, e),
            ExprKind::Index { base, index } => self.eval_index(f, base, index, e),
            ExprKind::SpanOf(inner) => self.eval_span_of(f, inner, e),
            ExprKind::Struct { fields, .. } => self.eval_struct(f, fields),
            ExprKind::Variant { tag, fields, .. } => self.eval_variant(f, *tag, fields),
            ExprKind::Array(items) => self.eval_array(f, items, e),
            ExprKind::Repeat { elem, n } => self.eval_repeat(f, elem, *n),
            ExprKind::Tuple(items) => self.eval_tuple(f, items),
            ExprKind::Tag(x) => self.eval_tag(f, x, e),
            ExprKind::Payload { base, tag, index } => self.eval_payload(f, base, *tag, *index, e),
            ExprKind::IfExpr { cond, then, else_ } => self.eval_if(f, cond, then, else_),
            ExprKind::Switch { scrutinee, arms, default } => self.eval_switch(f, scrutinee, arms, default, e),
            ExprKind::Block(b) => self.exec_block(f, b),
            ExprKind::Panic(msg) => self.eval_panic(*msg, span),
        }
    }

    #[inline(never)]
    fn eval_zeroed(&self, ty: &Ty) -> R<Value> {
        Ok(zero(self.m, ty))
    }

    #[inline(never)]
    fn eval_unary(&self, f: &mut Frame, op: UnOp, x: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let v = self.eval(f, x)?;
        self.unary(op, v, span)
    }

    #[inline(never)]
    fn eval_cast(&self, f: &mut Frame, x: &Expr, e: &Expr) -> R<Value> {
        let v = self.eval(f, x)?;
        self.cast(v, &x.ty, &e.ty, e.span)
    }

    #[inline(never)]
    fn eval_call(&self, f: &mut Frame, fn_: FnId, args: &[Arg], at: &Expr) -> R<Value> {
        let span = at.span;
        let args = self.eval_args(f, args)?;
        self.call_with(fn_, args, span)
    }

    #[inline(never)]
    fn eval_struct(&self, f: &mut Frame, fields: &[Expr]) -> R<Value> {
        Ok(Value::Struct(self.eval_all(f, fields)?))
    }

    #[inline(never)]
    fn eval_variant(&self, f: &mut Frame, tag: u32, fields: &[Expr]) -> R<Value> {
        Ok(Value::Enum { tag, fields: self.eval_all(f, fields)? })
    }

    #[inline(never)]
    fn eval_tuple(&self, f: &mut Frame, items: &[Expr]) -> R<Value> {
        Ok(Value::Tuple(self.eval_all(f, items)?))
    }

    #[inline(never)]
    fn eval_if(&self, f: &mut Frame, cond: &Expr, then: &Block, else_: &Block) -> R<Value> {
        let c = self.eval_bool(f, cond)?;
        self.exec_block(f, if c { then } else { else_ })
    }

    #[cold]
    #[inline(never)]
    fn eval_panic(&self, msg: MsgId, span: Span) -> R<Value> {
        panic(span, self.m.messages[msg.0 as usize].clone())
    }

    #[inline(never)]
    fn eval_lit(&self, l: &Lit, e: &Expr) -> R<Value> {
        Ok(match l {
            Lit::Int(n) => match &e.ty {
                Ty::Int(k) => int_value(*k, *n),
                _ => internal(e.span, "integer literal type"),
            },
            Lit::F32(x) => Value::F32(*x),
            Lit::F64(x) => Value::F64(*x),
            Lit::Bool(b) => Value::Bool(*b),
            Lit::Char(c) => Value::Char(*c),
            Lit::Unit => Value::Unit,
        })
    }

    #[inline(never)]
    fn eval_local(&self, f: &Frame, l: LocalId, span: Span) -> R<Value> {
        let r = self.local_place(f, l, span)?;
        self.read(&r, span)
    }

    #[inline(never)]
    fn eval_binary(&self, f: &mut Frame, op: (BinOp, Overflow), lhs: &Expr, rhs: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let a = self.eval(f, lhs)?;
        let b = self.eval(f, rhs)?;
        self.binary(op.0, op.1, a, b, span)
    }

    #[inline(never)]
    fn eval_cmp(&self, f: &mut Frame, op: CmpOp, lhs: &Expr, rhs: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let a = self.eval(f, lhs)?;
        let b = self.eval(f, rhs)?;
        Ok(Value::Bool(self.compare(op, &a, &b, span)?))
    }

    #[inline(never)]
    fn eval_logic(&self, f: &mut Frame, op: LogicOp, lhs: &Expr, rhs: &Expr) -> R<Value> {
        let a = self.eval_bool(f, lhs)?;
        Ok(Value::Bool(match op {
            LogicOp::And => a && self.eval_bool(f, rhs)?,
            LogicOp::Or => a || self.eval_bool(f, rhs)?,
        }))
    }

    #[inline(never)]
    fn eval_field(&self, f: &mut Frame, base: &Expr, index: u32, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_field(r, index, span)?;
            return self.read(&r, span);
        }
        match self.eval(f, base)? {
            Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. } => {
                fs.into_iter().nth(index as usize).map_or_else(|| internal(span, "field out of range"), Ok)
            }
            _ => internal(span, "field on a non-aggregate"),
        }
    }

    #[inline(never)]
    fn eval_index(&self, f: &mut Frame, base: &Expr, index: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let i = self.eval_u32(f, index)?;
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_index(r, i, span)?;
            return self.read(&r, span);
        }
        let v = self.eval(f, base)?;
        let i = self.eval_u32(f, index)?;
        self.index_value(v, i, span)
    }

    /// Element `i` of the sequence `v`, off the way down a recursion (R-05).
    #[inline(never)]
    fn index_value(&self, v: Value, i: u32, span: Span) -> R<Value> {
        let s = self.seq_of_value(v, span)?;
        if i >= s.len {
            return panic(span, format!("index {i} out of range for a sequence of length {}", s.len));
        }
        self.seq_get(&s, i, span)
    }

    #[inline(never)]
    fn eval_span_of(&self, f: &mut Frame, inner: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let s = match inner.as_place() {
            Some(p) => {
                let r = self.resolve_place(f, &p, span)?;
                self.seq_of_place(r, span)?
            }
            None => {
                let v = self.eval(f, inner)?;
                self.seq_of_value(v, span)?
            }
        };
        Ok(Value::Span(SpanRef { root: s.root, projs: s.projs, start: s.start, len: s.len }))
    }

    #[inline(never)]
    fn eval_array(&self, f: &mut Frame, items: &[Expr], e: &Expr) -> R<Value> {
        let out = self.eval_all(f, items)?;
        let elem = match &e.ty {
            Ty::Array(el, _) => (**el).clone(),
            _ => internal(e.span, "array literal type"),
        };
        Ok(Value::Array(ArrayData::from_values(&elem, out)))
    }

    #[inline(never)]
    fn eval_repeat(&self, f: &mut Frame, elem: &Expr, n: u32) -> R<Value> {
        let v = self.eval(f, elem)?;
        Ok(Value::Array(match v {
            Value::F32(x) => ArrayData::F32(vec![x; n as usize]),
            v => ArrayData::Any(vec![v; n as usize]),
        }))
    }

    #[inline(never)]
    fn eval_tag(&self, f: &mut Frame, x: &Expr, e: &Expr) -> R<Value> {
        let span = e.span;
        let tag = match x.as_place() {
            Some(p) => {
                let r = self.resolve_place(f, &p, span)?;
                self.peek(&r, span, |v| match v {
                    Leaf::Val(Value::Enum { tag, .. }) => Some(*tag),
                    _ => None,
                })?
            }
            None => match self.eval(f, x)? {
                Value::Enum { tag, .. } => Some(tag),
                _ => None,
            },
        };
        let Some(tag) = tag else { internal(span, "tag of a non-enum") };
        match &e.ty {
            Ty::Int(k) => Ok(int_value(*k, tag as i128)),
            _ => internal(span, "tag type"),
        }
    }

    #[inline(never)]
    fn eval_payload(&self, f: &mut Frame, base: &Expr, tag: u32, index: u32, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let ok = self.peek(&r, span, |v| matches!(v, Leaf::Val(Value::Enum { tag: t, .. }) if *t == tag))?;
            if !ok {
                internal(span, "payload of the wrong variant");
            }
            let r = self.project_field(r, index, span)?;
            return self.read(&r, span);
        }
        match self.eval(f, base)? {
            Value::Enum { tag: t, fields } if t == tag => {
                fields.into_iter().nth(index as usize).map_or_else(|| internal(span, "payload field out of range"), Ok)
            }
            _ => internal(span, "payload of the wrong variant"),
        }
    }

    #[inline(never)]
    fn eval_switch(
        &self,
        f: &mut Frame,
        scrutinee: &Expr,
        arms: &[(u32, Block)],
        default: &Option<Block>,
        at: &Expr,
    ) -> R<Value> {
        let span = at.span;
        let tag = match self.eval(f, scrutinee)? {
            Value::Enum { tag, .. } => tag,
            _ => internal(span, "switch on a non-enum"),
        };
        match arms.iter().find(|(t, _)| *t == tag) {
            Some((_, b)) => self.exec_block(f, b),
            None => match default {
                Some(b) => self.exec_block(f, b),
                None => internal(span, "switch without a matching arm"),
            },
        }
    }

    // ------------------------------------------------------------ numerics

    fn unary(&self, op: UnOp, v: Value, span: Span) -> R<Value> {
        Ok(match (op, v) {
            (UnOp::Neg, Value::F32(x)) => Value::F32(-x),
            (UnOp::Neg, Value::F64(x)) => Value::F64(-x),
            (UnOp::Neg, v) => {
                let k = int_kind_of(&v, span);
                let i = int_of(&v, k, span);
                let r = -i;
                if !in_range(k, r) {
                    return panic(span, format!("integer overflow in `-{i}`"));
                }
                int_value(k, r)
            }
            (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
            (UnOp::Not, v) => {
                let k = int_kind_of(&v, span);
                let i = int_of(&v, k, span);
                int_value(k, wrap_int(k, !i))
            }
        })
    }

    /// Off the way down a recursion through an operand (R-05).
    #[inline(never)]
    fn binary(&self, op: BinOp, overflow: Overflow, a: Value, b: Value, span: Span) -> R<Value> {
        match (&a, &b) {
            (Value::F32(x), Value::F32(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F32(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => internal(span, "bit operation on a float"),
                }));
            }
            (Value::F64(x), Value::F64(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F64(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => internal(span, "bit operation on a float"),
                }));
            }
            (Value::Bool(x), Value::Bool(y)) => {
                return Ok(Value::Bool(match op {
                    BinOp::BitAnd => *x & *y,
                    BinOp::BitOr => *x | *y,
                    BinOp::BitXor => *x ^ *y,
                    _ => internal(span, "arithmetic on Bool"),
                }));
            }
            _ => {}
        }
        let k = int_kind_of(&a, span);
        let x = int_of(&a, k, span);
        // The amount of a shift is a `U32` (spec §3.4); the other operators
        // take two operands of one type.
        let y = match op {
            BinOp::Shl | BinOp::Shr => int_of(&b, IntKind::U32, span),
            _ => int_of(&b, k, span),
        };
        let bits = k.bits() as i128;
        let r = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => return arith(op, overflow, k, x, y, span),
            BinOp::Div => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let q = x / y;
                if !in_range(k, q) {
                    return panic(span, format!("integer overflow in `{x} / {y}`"));
                }
                q
            }
            // `MIN % -1` is 0 (spec §3.4, R-19): only a zero divisor panics.
            BinOp::Rem => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                x % y
            }
            BinOp::BitAnd => x & y,
            BinOp::BitOr => x | y,
            BinOp::BitXor => x ^ y,
            BinOp::Shl | BinOp::Shr => {
                if y >= bits {
                    return panic(span, format!("shift amount {y} is not below the bit width {bits}"));
                }
                if op == BinOp::Shl { wrap_int(k, x << y) } else { x >> y }
            }
        };
        Ok(int_value(k, r))
    }

    fn compare(&self, op: CmpOp, a: &Value, b: &Value, span: Span) -> R<bool> {
        use std::cmp::Ordering;
        let ord: Option<Ordering> = match (a, b) {
            (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
            (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
            (Value::Bool(x), Value::Bool(y)) => Some(x.cmp(y)),
            (Value::Char(x), Value::Char(y)) => Some(x.cmp(y)),
            (Value::Unit, Value::Unit) => Some(Ordering::Equal),
            _ => {
                let k = int_kind_of(a, span);
                Some(int_of(a, k, span).cmp(&int_of(b, k, span)))
            }
        };
        Ok(match (op, ord) {
            (CmpOp::Eq, o) => o == Some(Ordering::Equal),
            (CmpOp::Ne, o) => o != Some(Ordering::Equal),
            (CmpOp::Lt, o) => o == Some(Ordering::Less),
            (CmpOp::Le, o) => matches!(o, Some(Ordering::Less | Ordering::Equal)),
            (CmpOp::Gt, o) => o == Some(Ordering::Greater),
            (CmpOp::Ge, o) => matches!(o, Some(Ordering::Greater | Ordering::Equal)),
        })
    }

    /// Lossless widening (§3.3) of `v`, of type `from`, to `to`. The value
    /// has the type the operand declares (R-92 (1)).
    fn cast(&self, v: Value, from: &Ty, to: &Ty, span: Span) -> R<Value> {
        Ok(match (from, to) {
            (Ty::Float(fk), Ty::Float(k)) => {
                // Exact: an `F32` is exact as an `f64`, and back.
                let x = float_of(&v, *fk, span);
                match (fk, k) {
                    (FloatKind::F32, FloatKind::F32) => Value::F32(x as f32),
                    (_, FloatKind::F64) => Value::F64(x),
                    (FloatKind::F64, FloatKind::F32) => {
                        internal(span, "the cast of an `F64` to `F32` loses information")
                    }
                }
            }
            (Ty::Int(fk), Ty::Float(k)) => {
                let i = int_of(&v, *fk, span);
                match k {
                    FloatKind::F32 => Value::F32(i as f32),
                    FloatKind::F64 => Value::F64(i as f64),
                }
            }
            (Ty::Int(fk), Ty::Int(k)) => match int_of(&v, *fk, span) {
                i if in_range(*k, i) => int_value(*k, i),
                i => internal(span, format!("the cast of {i} to `{}` loses information", k.name())),
            },
            _ => internal(span, "a cast that is not a widening of numbers"),
        })
    }

    // ------------------------------------------------------------ primitives

    /// A primitive: its arguments, then the operation, in a function of its
    /// own, off the way down a recursion through an argument (R-05).
    fn prim(&self, f: &mut Frame, prim: &Prim, args: &[Arg], ty: &Ty, span: Span) -> R<Value> {
        if let Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed =
            prim
        {
            return self.seq_prim(f, prim, args, ty, span);
        }
        let mut vs = Vec::with_capacity(args.len());
        for a in args {
            vs.push(self.eval(f, &a.expr)?);
        }
        self.prim_values(prim, &vs, span)
    }

    /// The primitives that take their receiver as a sequence reference.
    #[inline(never)]
    fn seq_prim(&self, f: &mut Frame, prim: &Prim, args: &[Arg], ty: &Ty, span: Span) -> R<Value> {
        match prim {
            Prim::Len => {
                let s = self.seq_of_arg(f, &args[0])?;
                Ok(Value::U32(s.len))
            }
            Prim::Slice => {
                let s = self.seq_of_arg(f, &args[0])?;
                let from = self.eval_u32(f, &args[1].expr)?;
                let to = self.eval_u32(f, &args[2].expr)?;
                if from > to || to > s.len {
                    return panic(
                        span,
                        format!("slice {from}..{to} is out of range for a sequence of length {}", s.len),
                    );
                }
                Ok(Value::Span(SpanRef { root: s.root, projs: s.projs, start: s.start + from, len: to - from }))
            }
            Prim::Get => {
                let s = self.seq_of_arg(f, &args[0])?;
                let i = self.eval_u32(f, &args[1].expr)?;
                Ok(if i < s.len { some(self.seq_get(&s, i, span)?) } else { none() })
            }
            Prim::Fill => {
                let s = self.seq_of_arg(f, &args[0])?;
                let v = self.eval(f, &args[1].expr)?;
                if let Value::F32(x) = v
                    && self.with_f32_slice(&s, |xs| xs.fill(x)).is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..s.len {
                    self.seq_set(&s, i, v.clone(), span)?;
                }
                Ok(Value::Unit)
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let dst = self.seq_of_arg(f, &args[0])?;
                let src = self.seq_of_arg(f, &args[1])?;
                if dst.len != src.len {
                    return panic(span, format!("span lengths differ: {} and {}", dst.len, src.len));
                }
                let add = *prim == Prim::AddFrom;
                let src_vals: Option<Vec<f32>> = self.with_f32_slice(&src, |xs| xs.to_vec());
                if let Some(sv) = src_vals
                    && self
                        .with_f32_slice(&dst, |xs| {
                            for (d, s) in xs.iter_mut().zip(&sv) {
                                if add {
                                    *d += *s;
                                } else {
                                    *d = *s;
                                }
                            }
                        })
                        .is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..dst.len {
                    let sv = self.seq_get(&src, i, span)?;
                    let nv = if add {
                        self.binary(BinOp::Add, Overflow::Checked, self.seq_get(&dst, i, span)?, sv, span)?
                    } else {
                        sv
                    };
                    self.seq_set(&dst, i, nv, span)?;
                }
                Ok(Value::Unit)
            }
            Prim::BufZeroed => {
                let n = self.eval_u32(f, &args[0].expr)?;
                let elem = match ty {
                    Ty::Buf(e) => (**e).clone(),
                    _ => internal(span, "Buf.zeroed type"),
                };
                Ok(Value::Buf(slot(Value::Array(zero_array(self.m, &elem, n)))))
            }
            _ => internal(span, "not a sequence primitive"),
        }
    }

    /// A primitive on the values of its arguments. Each operand has the type
    /// the primitive names, or the interpreter stops with an internal error
    /// (R-92 (1)).
    #[inline(never)]
    fn prim_values(&self, prim: &Prim, vs: &[Value], span: Span) -> R<Value> {
        match prim {
            Prim::Math(mf, k) => self.math(prim, *mf, *k, vs, span),
            Prim::IntAbs(k) => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *k, span);
                let r = x.abs();
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in `abs({x})`"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IntMin(k) | Prim::IntMax(k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                Ok(int_value(*k, if matches!(prim, Prim::IntMin(_)) { x.min(y) } else { x.max(y) }))
            }
            Prim::Narrow { from, to } => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *from, span);
                Ok(if in_range(*to, x) { some(int_value(*to, x)) } else { none() })
            }
            Prim::IntToFloat { from, to } => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *from, span);
                // Round to nearest, ties to even (§3.3): Rust's `as` from an integer.
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x as f64),
                })
            }
            Prim::FloatToFloat { from, to } => {
                let [a] = args(prim, vs, span);
                let x = float_of(a, *from, span);
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x),
                })
            }
            Prim::TruncToInt { from, to, sat } => {
                let [a] = args(prim, vs, span);
                Ok(int_value(*to, trunc_to_int(float_of(a, *from, span), *to, *sat, span)?))
            }
            Prim::ToBits(k) => {
                let [a] = args(prim, vs, span);
                // A NaN reads as the positive quiet NaN (spec §3.4, S-106).
                Ok(match (k, a) {
                    (FloatKind::F32, Value::F32(x)) => Value::U32(if x.is_nan() { NAN_BITS_F32 } else { x.to_bits() }),
                    (FloatKind::F64, Value::F64(x)) => Value::U64(if x.is_nan() { NAN_BITS_F64 } else { x.to_bits() }),
                    _ => mismatch(span, &format!("an `{}`", k.name()), a),
                })
            }
            Prim::FromBits(k) => {
                let [a] = args(prim, vs, span);
                Ok(match k {
                    FloatKind::F32 => Value::F32(f32::from_bits(int_of(a, IntKind::U32, span) as u32)),
                    FloatKind::F64 => Value::F64(f64::from_bits(int_of(a, IntKind::U64, span) as u64)),
                })
            }
            Prim::Checked(op, k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                let r = match op {
                    CheckedOp::Add => x.checked_add(y),
                    CheckedOp::Sub => x.checked_sub(y),
                    CheckedOp::Mul => x.checked_mul(y),
                    CheckedOp::Div => (y != 0).then(|| x / y),
                };
                Ok(match r {
                    Some(r) if in_range(*k, r) => some(int_value(*k, r)),
                    _ => none(),
                })
            }
            Prim::DivEuclid(k) | Prim::RemEuclid(k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                if y == 0 {
                    return panic(span, "division by zero");
                }
                // `MIN.rem_euclid(-1)` is 0; `MIN.div_euclid(-1)` does not fit (§3.4).
                let r = if matches!(prim, Prim::DivEuclid(_)) { x.div_euclid(y) } else { x.rem_euclid(y) };
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in euclidean division of {x} by {y}"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IsNan(k) => {
                let [a] = args(prim, vs, span);
                Ok(Value::Bool(float_of(a, *k, span).is_nan()))
            }
            Prim::IsFinite(k) => {
                let [a] = args(prim, vs, span);
                Ok(Value::Bool(float_of(a, *k, span).is_finite()))
            }
            Prim::Std(name) => self.std_prim(prim, name, vs, span),
            Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed => {
                internal(span, format!("the sequence primitive `{}` on values", prim.name()))
            }
        }
    }

    fn math(&self, prim: &Prim, mf: MathFn, k: FloatKind, vs: &[Value], span: Span) -> R<Value> {
        let (x, y) = if mf.arity() == 2 {
            let [a, b] = args(prim, vs, span);
            (float_of(a, k, span), float_of(b, k, span))
        } else {
            let [a] = args(prim, vs, span);
            (float_of(a, k, span), 0.0)
        };
        // An `F32` operand is exact as an `f64`, and back.
        Ok(match k {
            FloatKind::F32 => Value::F32(math_f32(mf, x as f32, y as f32)),
            FloatKind::F64 => Value::F64(math_f64(mf, x, y)),
        })
    }

    /// `std` `target fn`s the interpreter implements directly ([`std_prim`]);
    /// the others are E0200 ([`unsupported`]).
    fn std_prim(&self, prim: &Prim, name: &str, vs: &[Value], span: Span) -> R<Value> {
        match std_prim(name) {
            Some(StdPrim::AssertNear) => {
                let [a, b, tol] = args(prim, vs, span);
                let f = |v| float_of(v, FloatKind::F64, span);
                let (a, b, tol) = (f(a), f(b), f(tol));
                if (a - b).abs() <= tol {
                    Ok(Value::Unit)
                } else {
                    panic(span, format!("assert_near failed: {a:?} and {b:?} differ by more than {tol:?}"))
                }
            }
            None => Err(Signal::Fail(Failure::Unsupported(std_unsupported(name, span)))),
        }
    }
}

/// The `N` operands of `prim` (an internal error for another number).
#[track_caller]
fn args<'v, const N: usize>(prim: &Prim, vs: &'v [Value], span: Span) -> &'v [Value; N] {
    match vs.try_into() {
        Ok(a) => a,
        Err(_) => internal(span, format!("`{}` given {} operands, not {N}", prim.name(), vs.len())),
    }
}

/// `x + y`, `x - y`, `x * y` on integers of kind `k` (spec §3.4, R-04). The
/// exact result when `i128` holds it, which it does for every sum and
/// difference of 64-bit values and every product but one of two `U64`s above
/// 2^127; such a product is beyond every type, and positive.
fn arith(op: BinOp, overflow: Overflow, k: IntKind, x: i128, y: i128, span: Span) -> R<Value> {
    let (exact, wrapped, sym) = match op {
        BinOp::Add => (x.checked_add(y), x.wrapping_add(y), "+"),
        BinOp::Sub => (x.checked_sub(y), x.wrapping_sub(y), "-"),
        BinOp::Mul => (x.checked_mul(y), x.wrapping_mul(y), "*"),
        _ => internal(span, "not an arithmetic operator"),
    };
    let r = match (overflow, exact) {
        // Modulo 2^128, so modulo 2^(bit width) too.
        (Overflow::Wrap, _) => wrap_int(k, wrapped),
        (Overflow::Sat, Some(r)) => clamp_int(k, r),
        (Overflow::Sat, None) => {
            let (lo, hi) = value::int_range(k);
            if (x < 0) != (y < 0) { lo } else { hi }
        }
        (Overflow::Checked, Some(r)) if in_range(k, r) => r,
        (Overflow::Checked, _) => {
            return panic(span, format!("integer overflow in `{x} {sym} {y}` ({})", k.name()));
        }
    };
    Ok(int_value(k, r))
}

/// `trunc_<type>()` and `trunc_<type>_sat()` of `x` (spec §3.3, §3.4): toward
/// zero; out of range or NaN is a panic, or the bound and 0 for `_sat`. The
/// range is `lo <= t < above`, with `above` the power of two just past the
/// type's maximum: both exact as `f64`, where the maximum of a 64-bit type is
/// not (R-19).
fn trunc_to_int(x: f64, to: IntKind, sat: bool, span: Span) -> R<i128> {
    let (lo, hi) = value::int_range(to);
    let above = (hi + 1) as f64;
    if x.is_nan() {
        return if sat { Ok(0) } else { panic(span, "conversion of NaN to an integer") };
    }
    let t = x.trunc();
    if t < lo as f64 || t >= above {
        return if sat {
            Ok(if t < lo as f64 { lo } else { hi })
        } else {
            panic(span, format!("{x:?} is out of range for {}", to.name()))
        };
    }
    Ok(t as i128)
}

/// The panic of a call beyond [`MAX_CALL_DEPTH`] (spec §12.5), at the call.
#[cold]
#[inline(never)]
fn depth_limit(site: Span) -> R<Value> {
    panic(site, format!("the call depth reached its limit of {MAX_CALL_DEPTH}"))
}

/// The length of the `Buf` in `b`, whose slot holds an array.
#[track_caller]
fn buf_len(b: &Slot, span: Span) -> u32 {
    match &*b.borrow() {
        Value::Array(a) => a.len(),
        v => mismatch(span, "the array of a `Buf`", v),
    }
}

/// A value of the wrong type where Core's types promise another (R-92 (1)):
/// the interpreter never reads it as 0 or `false`, it is an internal error
/// (the Core verifier missed it, S-67).
#[cold]
#[inline(never)]
#[track_caller]
fn mismatch(span: Span, expected: &str, got: &Value) -> ! {
    internal(span, format!("{expected} expected, found {}", value_kind(got)))
}

/// The kind of a value, for the message of [`mismatch`].
fn value_kind(v: &Value) -> String {
    match v {
        Value::F32(_) => "an `F32`".into(),
        Value::F64(_) => "an `F64`".into(),
        Value::Bool(_) => "a `Bool`".into(),
        Value::Char(_) => "a `Char`".into(),
        Value::Unit => "`()`".into(),
        Value::Array(_) => "an array".into(),
        Value::Tuple(_) => "a tuple".into(),
        Value::Struct(_) => "a struct".into(),
        Value::Enum { .. } => "an enum".into(),
        Value::Span(_) => "a `Span`".into(),
        Value::Buf(_) => "a `Buf`".into(),
        Value::Fn(_) => "a function".into(),
        v => match v.int_kind() {
            Some(k) => format!("an integer of `{}`", k.name()),
            None => "a value".into(),
        },
    }
}

/// The checks of the types of values (R-92 (1)): the one place the
/// interpreter compares a value with the type Core gives it. Each stops with
/// [`mismatch`], at its caller (`#[track_caller]`).
///
/// The kind of the integer `v`.
#[track_caller]
fn int_kind_of(v: &Value, span: Span) -> IntKind {
    // A `match`, not a closure: `#[track_caller]` does not pass through one.
    match v.int_kind() {
        Some(k) => k,
        None => mismatch(span, "an integer", v),
    }
}

/// The `Bool` in `v`.
#[track_caller]
fn bool_of(v: &Value, span: Span) -> bool {
    match v {
        Value::Bool(b) => *b,
        _ => mismatch(span, "a `Bool`", v),
    }
}

/// The integer of kind `k` in `v` (R-92 (1)).
#[track_caller]
fn int_of(v: &Value, k: IntKind, span: Span) -> i128 {
    match (v.int_kind(), v.to_i128()) {
        (Some(vk), Some(i)) if vk == k => i,
        _ => mismatch(span, &format!("an integer of `{}`", k.name()), v),
    }
}

/// The float of kind `k` in `v`, as `f64` (exact for `F32`) (R-92 (1)).
#[track_caller]
fn float_of(v: &Value, k: FloatKind, span: Span) -> f64 {
    match (v, k) {
        (Value::F32(x), FloatKind::F32) => *x as f64,
        (Value::F64(x), FloatKind::F64) => *x,
        _ => mismatch(span, &format!("an `{}`", k.name()), v),
    }
}

fn some(v: Value) -> Value {
    Value::Enum { tag: 1, fields: vec![v] }
}

fn none() -> Value {
    Value::Enum { tag: 0, fields: Vec::new() }
}

/// Round half to even (S-25).
fn round_even_f32(x: f32) -> f32 {
    x.round_ties_even()
}

fn round_even_f64(x: f64) -> f64 {
    x.round_ties_even()
}

/// `min` / `max` with NaN propagation and signed zeros ordered (S-25).
fn min_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() || b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a < b { a } else { b }
}

fn max_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() && b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a > b { a } else { b }
}

fn math_f32(mf: MathFn, x: f32, y: f32) -> f32 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f32(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x as f64, y as f64) as f32,
        MathFn::Max => max_f64(x as f64, y as f64) as f32,
        MathFn::Fmod => x % y,
    }
}

fn math_f64(mf: MathFn, x: f64, y: f64) -> f64 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f64(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x, y),
        MathFn::Max => max_f64(x, y),
        MathFn::Fmod => x % y,
    }
}

/// Type information for tools: the variant names of an enum type.
pub fn variant_names(m: &Module, ty: &Ty) -> Vec<String> {
    match ty {
        Ty::Enum(id) => match &m.ty(*id).kind {
            TypeDefKind::Enum { variants } => variants.iter().map(|(n, _)| n.clone()).collect(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// A fresh slot holding `v` (for callers that build `inout` state).
pub fn new_slot(v: Value) -> Slot {
    Rc::new(RefCell::new(v))
}

#[cfg(test)]
mod tests;
