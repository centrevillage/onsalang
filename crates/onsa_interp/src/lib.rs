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

mod calls;
mod exec;
mod numeric;
mod place;
mod prim;
mod std_fns;
pub mod value;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use onsa_core::{ConstId, FnId, Module, PanicOrigin, Ty, TypeDefKind};
use onsa_diag::{Diagnostic, Span};

use calls::ConstState;
use place::{ArgVal, PlaceRef};
pub use std_fns::unsupported;
pub use value::{ArrayData, Proj, Slot, SpanRef, Value, show, slot, zero};

/// A panic of the program (spec §9.2, and a call beyond the depth limit of
/// §12.5) with the position of the instruction that raised it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Panic {
    pub message: String,
    pub span: Span,
    /// The calls the panic went out of, innermost first, up to the entry of
    /// the evaluation (the body of a `test`): what `onsa test --json` reports
    /// as `calls` (spec §18.1, S-233). Reading a `const` is not a call, so the
    /// calls of its initializer come before the calls around the read, and
    /// the read itself has no position: the form until W9-03 makes a panic
    /// of an initializer the E0419 of §6.6.
    pub calls: Vec<CallSite>,
    /// A failed `assert` (of Core, or of `std.dsp.test.assert_near`) or
    /// another panic: what the message cannot tell (X9-36).
    pub origin: PanicOrigin,
}

/// A call a panic went out of ([`Panic::calls`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallSite {
    /// The position of the call expression in Core (the call of the source,
    /// or the flow's own position for a call a flow's generated function
    /// makes to another of the same flow).
    pub span: Span,
    /// The function called.
    pub callee: FnId,
}

/// A form this version of the interpreter cannot run: E0200 (spec §18.1,
/// S-224). [`unsupported`] finds every one in a module before it runs; an
/// evaluation that reaches one stops with it. Today the one kind is a call of
/// a `std` `target fn` the interpreter does not implement ([`std_prim`](std_fns::std_prim)).
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
    panic_from(PanicOrigin::Panic, span, msg)
}

fn panic_from<T>(origin: PanicOrigin, span: Span, msg: impl Into<String>) -> R<T> {
    Err(Signal::Fail(Failure::Panic(Panic { message: msg.into(), span, calls: Vec::new(), origin })))
}

/// The interpreter found a state it cannot be in at `span`: an internal
/// error (S-67), never a panic of the program (R-137).
#[cold]
#[inline(never)]
#[track_caller]
fn internal(span: Span, msg: impl Into<String>) -> ! {
    onsa_diag::internal::bug(Some(span), msg)
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
