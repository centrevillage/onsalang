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

use onsa_core::prim::{CheckedOp, MathFn, Prim};
use onsa_core::{
    Arg, BinOp, Block, CmpOp, ConstId, Expr, ExprKind, FloatKind, FnId, Lit, LocalId, LogicOp, Mode, Module, MsgId,
    Overflow, Place, Stmt, StmtKind, Ty, TypeDefKind, UnOp,
};
use onsa_diag::Span;

pub use value::{ArrayData, Proj, Slot, SpanRef, Value, show, slot, zero};
use value::{clamp_int, in_range, int_value, wrap_int, zero_array};

/// A panic (spec §9.2) with the position of the instruction that raised it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Panic {
    pub message: String,
    pub span: Span,
}

/// Non-local control flow inside the interpreter.
#[derive(Debug)]
enum Signal {
    Panic(Panic),
    Return(Value),
    Break,
    Continue,
}

type R<T> = Result<T, Signal>;

fn panic<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(Signal::Panic(Panic { message: msg.into(), span }))
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
/// (2026-10-08), bytes of stack, with `onsa_interp` at `opt-level = 1` in the
/// dev profile (`Cargo.toml`):
///
/// | | debug | release |
/// |---|---|---|
/// | one call, no nesting (`1 + f(n - 1)`) | 0.8 K | 0.5 K |
/// | one level of `0 + (x)` | 0.3 K | 0.3 K |
/// | one level of `(x, 0).0` | 0.7 K | 0.7 K |
/// | one level of `match`, `[x][0]` (the most) | 0.8–0.9 K | 0.8 K |
///
/// So 128 calls, each under 256 levels of the most expensive kind, use 28 MB
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
    pub fn call(&self, fn_: FnId, args: Vec<Value>) -> Result<Value, Panic> {
        let site = self.m.fn_(fn_).span;
        let args = args.into_iter().map(ArgVal::Val).collect();
        self.enter(site, || self.run_body(fn_, args)).map_err(Self::into_panic)
    }

    /// Call with an `inout` first argument held in `state` (flows: `process(inout s, ...)`).
    pub fn call_inout(&self, fn_: FnId, state: &Slot, rest: Vec<Value>) -> Result<Value, Panic> {
        let mut args = vec![ArgVal::Place(PlaceRef { root: state.clone(), projs: Vec::new() })];
        args.extend(rest.into_iter().map(ArgVal::Val));
        let site = self.m.fn_(fn_).span;
        self.enter(site, || self.run_body(fn_, args)).map_err(Self::into_panic)
    }

    /// Value of a `const` (evaluated on first use; T3-9), from wherever it is
    /// read: its initializer is an evaluation of its own (spec §12.5).
    pub fn const_value(&self, id: ConstId) -> Result<Value, Panic> {
        self.const_val(id).map_err(Self::into_panic)
    }

    fn into_panic(s: Signal) -> Panic {
        match s {
            Signal::Panic(p) => p,
            Signal::Return(_) | Signal::Break | Signal::Continue => Panic {
                message: "internal: control flow escaped a function".into(),
                span: Span::new(onsa_diag::FileId(0), 0, 0),
            },
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
        let r = self.eval(&mut f, &self.m.const_(id).init);
        if let Ok(v) = &r {
            *cell.borrow_mut() = ConstState::Done(v.clone());
        }
        r
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
            Err(Signal::Break) | Err(Signal::Continue) => panic(f.span, "internal: loop control outside a loop"),
            Err(e) => Err(e),
        }
    }

    #[cold]
    #[inline(never)]
    fn no_body(&self, fn_: FnId) -> R<Value> {
        let f = self.m.fn_(fn_);
        panic(f.span, format!("`{}` has no body in this version (target function)", f.name))
    }

    /// The frame of a call of `fn_`, with the parameters bound to `args`.
    #[inline(never)]
    fn bind_params(&self, fn_: FnId, args: Vec<ArgVal>) -> R<Frame> {
        let f = self.m.fn_(fn_);
        if args.len() != f.params.len() {
            return panic(f.span, format!("internal: `{}` called with {} arguments", f.name, args.len()));
        }
        let mut frame = Frame { locals: vec![None; f.locals.len()] };
        for (p, a) in f.params.iter().zip(args) {
            let loc = match (p.mode, a) {
                (Mode::Inout, ArgVal::Place(pr)) => Loc::Alias(pr),
                (_, ArgVal::Val(v)) => Loc::Slot(slot(v)),
                (_, ArgVal::Place(pr)) => Loc::Slot(slot(self.read(&pr)?)),
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
            None => panic(span, "internal: local read before initialization"),
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
            return panic(span, "internal: field projection on a non-aggregate");
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
                let len = match &*b.borrow() {
                    Value::Array(a) => a.len(),
                    _ => 0,
                };
                if i >= len {
                    return panic(span, format!("index {i} out of range for a buffer of length {len}"));
                }
                Ok(PlaceRef { root: b, projs: vec![Proj::Index(i)] })
            }
            Kind::Other => panic(span, "internal: index on a non-sequence"),
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
            None => panic(span, "internal: dangling place"),
        }
    }

    fn read(&self, r: &PlaceRef) -> R<Value> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => panic(Span::new(onsa_diag::FileId(0), 0, 0), "internal: dangling place"),
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
                _ => panic(span, "internal: non-F32 written into an F32 array"),
            },
            None => panic(span, "internal: dangling place"),
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
                let len = buf_len(&b);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            K::Other => panic(span, "internal: sequence expected"),
        }
    }

    fn seq_of_value(&self, v: Value, span: Span) -> R<SeqRef> {
        match v {
            Value::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            Value::Buf(b) => {
                let len = buf_len(&b);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            Value::Array(a) => {
                let len = a.len();
                Ok(SeqRef { root: slot(Value::Array(a)), projs: Vec::new(), start: 0, len })
            }
            _ => panic(span, "internal: sequence expected"),
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
            None => panic(span, "internal: dangling sequence"),
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
        let kind =
            lo_v.int_kind().ok_or_else(|| Signal::Panic(Panic { message: "internal: range bound".into(), span }))?;
        let (lo_i, hi_i) = (lo_v.to_i128().unwrap(), hi_v.to_i128().unwrap_or(0));
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
        match self.eval(f, e)? {
            Value::Bool(b) => Ok(b),
            _ => panic(e.span, "internal: Bool expected"),
        }
    }

    fn eval_u32(&self, f: &mut Frame, e: &Expr) -> R<u32> {
        match self.eval(f, e)? {
            Value::U32(x) => Ok(x),
            v => match v.to_i128() {
                Some(i) if (0..=u32::MAX as i128).contains(&i) => Ok(i as u32),
                _ => panic(e.span, "internal: U32 expected"),
            },
        }
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
            ExprKind::Unary(op, x) => self.eval_unary(f, *op, x, span),
            ExprKind::Binary { op, overflow, lhs, rhs } => self.eval_binary(f, (*op, *overflow), lhs, rhs, span),
            ExprKind::Cmp { op, lhs, rhs } => self.eval_cmp(f, *op, lhs, rhs, span),
            ExprKind::Logic { op, lhs, rhs } => self.eval_logic(f, *op, lhs, rhs),
            ExprKind::Cast(x) => self.eval_cast(f, x, e),
            ExprKind::Call { fn_, args } => self.eval_call(f, *fn_, args, span),
            ExprKind::Prim { prim, args } => self.prim(f, prim, args, &e.ty, span),
            ExprKind::Field { base, index } => self.eval_field(f, base, *index, span),
            ExprKind::Index { base, index } => self.eval_index(f, base, index, span),
            ExprKind::SpanOf(inner) => self.eval_span_of(f, inner, span),
            ExprKind::Struct { fields, .. } => self.eval_struct(f, fields),
            ExprKind::Variant { tag, fields, .. } => self.eval_variant(f, *tag, fields),
            ExprKind::Array(items) => self.eval_array(f, items, e),
            ExprKind::Repeat { elem, n } => self.eval_repeat(f, elem, *n),
            ExprKind::Tuple(items) => self.eval_tuple(f, items),
            ExprKind::Tag(x) => self.eval_tag(f, x, e),
            ExprKind::Payload { base, tag, index } => self.eval_payload(f, base, *tag, *index, span),
            ExprKind::IfExpr { cond, then, else_ } => self.eval_if(f, cond, then, else_),
            ExprKind::Switch { scrutinee, arms, default } => self.eval_switch(f, scrutinee, arms, default, span),
            ExprKind::Block(b) => self.exec_block(f, b),
            ExprKind::Panic(msg) => self.eval_panic(*msg, span),
        }
    }

    #[inline(never)]
    fn eval_zeroed(&self, ty: &Ty) -> R<Value> {
        Ok(zero(self.m, ty))
    }

    #[inline(never)]
    fn eval_unary(&self, f: &mut Frame, op: UnOp, x: &Expr, span: Span) -> R<Value> {
        let v = self.eval(f, x)?;
        self.unary(op, v, span)
    }

    #[inline(never)]
    fn eval_cast(&self, f: &mut Frame, x: &Expr, e: &Expr) -> R<Value> {
        let v = self.eval(f, x)?;
        self.cast(v, &e.ty, e.span)
    }

    #[inline(never)]
    fn eval_call(&self, f: &mut Frame, fn_: FnId, args: &[Arg], span: Span) -> R<Value> {
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
                _ => return panic(e.span, "internal: integer literal type"),
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
        self.read(&r)
    }

    #[inline(never)]
    fn eval_binary(&self, f: &mut Frame, op: (BinOp, Overflow), lhs: &Expr, rhs: &Expr, span: Span) -> R<Value> {
        let a = self.eval(f, lhs)?;
        let b = self.eval(f, rhs)?;
        self.binary(op.0, op.1, a, b, span)
    }

    #[inline(never)]
    fn eval_cmp(&self, f: &mut Frame, op: CmpOp, lhs: &Expr, rhs: &Expr, span: Span) -> R<Value> {
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
    fn eval_field(&self, f: &mut Frame, base: &Expr, index: u32, span: Span) -> R<Value> {
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_field(r, index, span)?;
            return self.read(&r);
        }
        match self.eval(f, base)? {
            Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. } => fs
                .into_iter()
                .nth(index as usize)
                .ok_or_else(|| Signal::Panic(Panic { message: "internal: field".into(), span })),
            _ => panic(span, "internal: field on a non-aggregate"),
        }
    }

    #[inline(never)]
    fn eval_index(&self, f: &mut Frame, base: &Expr, index: &Expr, span: Span) -> R<Value> {
        if let Some(p) = base.as_place() {
            let i = self.eval_u32(f, index)?;
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_index(r, i, span)?;
            return self.read(&r);
        }
        let v = self.eval(f, base)?;
        let i = self.eval_u32(f, index)?;
        let s = self.seq_of_value(v, span)?;
        if i >= s.len {
            return panic(span, format!("index {i} out of range for a sequence of length {}", s.len));
        }
        self.seq_get(&s, i, span)
    }

    #[inline(never)]
    fn eval_span_of(&self, f: &mut Frame, inner: &Expr, span: Span) -> R<Value> {
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
            _ => return panic(e.span, "internal: array literal type"),
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
        let Some(tag) = tag else { return panic(span, "internal: tag of a non-enum") };
        match &e.ty {
            Ty::Int(k) => Ok(int_value(*k, tag as i128)),
            _ => panic(span, "internal: tag type"),
        }
    }

    #[inline(never)]
    fn eval_payload(&self, f: &mut Frame, base: &Expr, tag: u32, index: u32, span: Span) -> R<Value> {
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let ok = self.peek(&r, span, |v| matches!(v, Leaf::Val(Value::Enum { tag: t, .. }) if *t == tag))?;
            if !ok {
                return panic(span, "internal: payload of the wrong variant");
            }
            let r = self.project_field(r, index, span)?;
            return self.read(&r);
        }
        match self.eval(f, base)? {
            Value::Enum { tag: t, fields } if t == tag => fields
                .into_iter()
                .nth(index as usize)
                .ok_or_else(|| Signal::Panic(Panic { message: "internal: payload".into(), span })),
            _ => panic(span, "internal: payload of the wrong variant"),
        }
    }

    #[inline(never)]
    fn eval_switch(
        &self,
        f: &mut Frame,
        scrutinee: &Expr,
        arms: &[(u32, Block)],
        default: &Option<Block>,
        span: Span,
    ) -> R<Value> {
        let tag = match self.eval(f, scrutinee)? {
            Value::Enum { tag, .. } => tag,
            _ => return panic(span, "internal: switch on a non-enum"),
        };
        match arms.iter().find(|(t, _)| *t == tag) {
            Some((_, b)) => self.exec_block(f, b),
            None => match default {
                Some(b) => self.exec_block(f, b),
                None => panic(span, "internal: switch without a matching arm"),
            },
        }
    }

    // ------------------------------------------------------------ numerics

    fn unary(&self, op: UnOp, v: Value, span: Span) -> R<Value> {
        Ok(match (op, v) {
            (UnOp::Neg, Value::F32(x)) => Value::F32(-x),
            (UnOp::Neg, Value::F64(x)) => Value::F64(-x),
            (UnOp::Neg, v) => {
                let (Some(k), Some(i)) = (v.int_kind(), v.to_i128()) else { return panic(span, "internal: neg") };
                let r = -i;
                if !in_range(k, r) {
                    return panic(span, format!("integer overflow in `-{i}`"));
                }
                int_value(k, r)
            }
            (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
            (UnOp::Not, v) => {
                let (Some(k), Some(i)) = (v.int_kind(), v.to_i128()) else { return panic(span, "internal: not") };
                int_value(k, wrap_int(k, !i))
            }
        })
    }

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
                    _ => return panic(span, "internal: bit operation on a float"),
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
                    _ => return panic(span, "internal: bit operation on a float"),
                }));
            }
            (Value::Bool(x), Value::Bool(y)) => {
                return Ok(Value::Bool(match op {
                    BinOp::BitAnd => *x & *y,
                    BinOp::BitOr => *x | *y,
                    BinOp::BitXor => *x ^ *y,
                    _ => return panic(span, "internal: arithmetic on Bool"),
                }));
            }
            _ => {}
        }
        let (Some(k), Some(x)) = (a.int_kind(), a.to_i128()) else { return panic(span, "internal: binary operand") };
        let Some(y) = b.to_i128() else { return panic(span, "internal: binary operand") };
        let bits = k.bits() as i128;
        let r = match op {
            BinOp::Add => x + y,
            BinOp::Sub => x - y,
            BinOp::Mul => x * y,
            BinOp::Div | BinOp::Rem => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let q = x / y;
                if !in_range(k, q) {
                    return panic(span, format!("integer overflow in `{x} / {y}`"));
                }
                if op == BinOp::Div { q } else { x % y }
            }
            BinOp::BitAnd => x & y,
            BinOp::BitOr => x | y,
            BinOp::BitXor => x ^ y,
            BinOp::Shl | BinOp::Shr => {
                if y < 0 || y >= bits {
                    return panic(span, format!("shift amount {y} is not below the bit width {bits}"));
                }
                if op == BinOp::Shl { wrap_int(k, x << y) } else { x >> y }
            }
        };
        let r = match (op, overflow) {
            (BinOp::Add | BinOp::Sub | BinOp::Mul, Overflow::Wrap) => wrap_int(k, r),
            (BinOp::Add | BinOp::Sub | BinOp::Mul, Overflow::Sat) => clamp_int(k, r),
            _ => {
                if !in_range(k, r) {
                    let sym = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        _ => "?",
                    };
                    return panic(span, format!("integer overflow in `{x} {sym} {y}` ({})", k.name()));
                }
                r
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
            _ => match (a.to_i128(), b.to_i128()) {
                (Some(x), Some(y)) => Some(x.cmp(&y)),
                _ => return panic(span, "internal: comparison operands"),
            },
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

    /// Lossless widening (§3.3).
    fn cast(&self, v: Value, to: &Ty, span: Span) -> R<Value> {
        Ok(match (v, to) {
            (Value::F32(x), Ty::Float(FloatKind::F64)) => Value::F64(x as f64),
            (Value::F32(x), Ty::Float(FloatKind::F32)) => Value::F32(x),
            (Value::F64(x), Ty::Float(FloatKind::F64)) => Value::F64(x),
            (v, Ty::Float(FloatKind::F32)) => match v.to_i128() {
                Some(i) => Value::F32(i as f32),
                None => return panic(span, "internal: cast operand"),
            },
            (v, Ty::Float(FloatKind::F64)) => match v.to_i128() {
                Some(i) => Value::F64(i as f64),
                None => return panic(span, "internal: cast operand"),
            },
            (v, Ty::Int(k)) => match v.to_i128() {
                Some(i) if in_range(*k, i) => int_value(*k, i),
                _ => return panic(span, "internal: cast out of range"),
            },
            _ => return panic(span, "internal: cast type"),
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
                    _ => return panic(span, "internal: Buf.zeroed type"),
                };
                Ok(Value::Buf(slot(Value::Array(zero_array(self.m, &elem, n)))))
            }
            _ => panic(span, "internal: not a sequence primitive"),
        }
    }

    /// A primitive on the values of its arguments.
    #[inline(never)]
    fn prim_values(&self, prim: &Prim, vs: &[Value], span: Span) -> R<Value> {
        match prim {
            Prim::Math(mf, k) => self.math(*mf, *k, vs, span),
            Prim::IntAbs(k) => {
                let x = vs[0].to_i128().unwrap_or(0);
                let r = x.abs();
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in `abs({x})`"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IntMin(k) => Ok(int_value(*k, vs[0].to_i128().unwrap_or(0).min(vs[1].to_i128().unwrap_or(0)))),
            Prim::IntMax(k) => Ok(int_value(*k, vs[0].to_i128().unwrap_or(0).max(vs[1].to_i128().unwrap_or(0)))),
            Prim::Narrow { to, .. } => {
                let x = vs[0].to_i128().unwrap_or(0);
                Ok(if in_range(*to, x) { some(int_value(*to, x)) } else { none() })
            }
            Prim::IntToFloat { to, .. } => {
                let x = vs[0].to_i128().unwrap_or(0);
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x as f64),
                })
            }
            Prim::FloatToFloat { to, .. } => Ok(match (&vs[0], to) {
                (Value::F64(x), FloatKind::F32) => Value::F32(*x as f32),
                (Value::F32(x), FloatKind::F64) => Value::F64(*x as f64),
                (v, _) => v.clone(),
            }),
            Prim::TruncToInt { to, sat, .. } => {
                let x = match &vs[0] {
                    Value::F32(x) => *x as f64,
                    Value::F64(x) => *x,
                    _ => return panic(span, "internal: trunc operand"),
                };
                let (lo, hi) = value::int_range(*to);
                if *sat {
                    // Rust `as` semantics: saturate, NaN -> 0.
                    let r = if x.is_nan() {
                        0
                    } else {
                        let t = x.trunc();
                        if t <= lo as f64 {
                            lo
                        } else if t >= hi as f64 {
                            hi
                        } else {
                            t as i128
                        }
                    };
                    Ok(int_value(*to, r))
                } else {
                    if x.is_nan() {
                        return panic(span, "conversion of NaN to an integer");
                    }
                    let t = x.trunc();
                    if t < lo as f64 || t > hi as f64 {
                        return panic(span, format!("{x:?} is out of range for {}", to.name()));
                    }
                    Ok(int_value(*to, t as i128))
                }
            }
            Prim::ToBits(_) => Ok(match &vs[0] {
                Value::F32(x) => Value::U32(x.to_bits()),
                Value::F64(x) => Value::U64(x.to_bits()),
                _ => return panic(span, "internal: to_bits operand"),
            }),
            Prim::FromBits(k) => Ok(match (k, &vs[0]) {
                (FloatKind::F32, Value::U32(b)) => Value::F32(f32::from_bits(*b)),
                (FloatKind::F64, Value::U64(b)) => Value::F64(f64::from_bits(*b)),
                _ => return panic(span, "internal: from_bits operand"),
            }),
            Prim::Checked(op, k) => {
                let (x, y) = (vs[0].to_i128().unwrap_or(0), vs[1].to_i128().unwrap_or(0));
                let r = match op {
                    CheckedOp::Add => Some(x + y),
                    CheckedOp::Sub => Some(x - y),
                    CheckedOp::Mul => Some(x * y),
                    CheckedOp::Div => (y != 0).then(|| x / y),
                };
                Ok(match r {
                    Some(r) if in_range(*k, r) => some(int_value(*k, r)),
                    _ => none(),
                })
            }
            Prim::DivEuclid(k) | Prim::RemEuclid(k) => {
                let (x, y) = (vs[0].to_i128().unwrap_or(0), vs[1].to_i128().unwrap_or(0));
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let r = if matches!(prim, Prim::DivEuclid(_)) { x.div_euclid(y) } else { x.rem_euclid(y) };
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in euclidean division of {x} by {y}"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IsNan(_) => Ok(Value::Bool(match &vs[0] {
                Value::F32(x) => x.is_nan(),
                Value::F64(x) => x.is_nan(),
                _ => false,
            })),
            Prim::IsFinite(_) => Ok(Value::Bool(match &vs[0] {
                Value::F32(x) => x.is_finite(),
                Value::F64(x) => x.is_finite(),
                _ => false,
            })),
            Prim::Std(name) => self.std_prim(name, vs, span),
            Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed => {
                unreachable!()
            }
        }
    }

    fn math(&self, mf: MathFn, k: FloatKind, vs: &[Value], span: Span) -> R<Value> {
        match k {
            FloatKind::F32 => {
                let x = vs[0]
                    .as_f32()
                    .ok_or_else(|| Signal::Panic(Panic { message: "internal: math operand".into(), span }))?;
                let y = vs.get(1).and_then(|v| v.as_f32()).unwrap_or(0.0);
                Ok(Value::F32(math_f32(mf, x, y)))
            }
            FloatKind::F64 => {
                let x = vs[0]
                    .as_f64()
                    .ok_or_else(|| Signal::Panic(Panic { message: "internal: math operand".into(), span }))?;
                let y = vs.get(1).and_then(|v| v.as_f64()).unwrap_or(0.0);
                Ok(Value::F64(math_f64(mf, x, y)))
            }
        }
    }

    /// `std` `target fn`s the interpreter implements directly.
    fn std_prim(&self, name: &str, vs: &[Value], span: Span) -> R<Value> {
        match name {
            "std.dsp.test.assert_near" => {
                let (a, b, tol) =
                    (vs[0].as_f64().unwrap_or(0.0), vs[1].as_f64().unwrap_or(0.0), vs[2].as_f64().unwrap_or(0.0));
                if (a - b).abs() <= tol {
                    Ok(Value::Unit)
                } else {
                    panic(span, format!("assert_near failed: {a:?} and {b:?} differ by more than {tol:?}"))
                }
            }
            _ => panic(span, format!("`{name}` is not available in this version of the interpreter")),
        }
    }
}

/// The panic of a call beyond [`MAX_CALL_DEPTH`] (spec §12.5), at the call.
#[cold]
#[inline(never)]
fn depth_limit(site: Span) -> R<Value> {
    panic(site, format!("the call depth reached its limit of {MAX_CALL_DEPTH}"))
}

fn buf_len(b: &Slot) -> u32 {
    match &*b.borrow() {
        Value::Array(a) => a.len(),
        _ => 0,
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
