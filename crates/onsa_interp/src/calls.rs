//! Calls and the entries of an evaluation: the call depth (spec §12.5), the
//! safety net of the stack, and the evaluation of the `const`s.

use std::cell::{Cell, RefCell};

use onsa_core::{ConstId, FnId, Mode};
use onsa_diag::Span;

use crate::place::{ArgVal, Frame, Loc};
use crate::value::{Value, slot};
use crate::{CallSite, Failure, Interp, MAX_CALL_DEPTH, Panic, R, STACK_RESERVE, Signal, internal, panic};

pub(super) enum ConstState {
    Unevaluated,
    InProgress,
    Done(Value),
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
    /// What an entry at `at` gives back: only a failure leaves an entry
    /// ([`Interp::run_body`] and [`Interp::eval_const`] take the rest).
    pub(super) fn failure_of(s: Signal, at: Span) -> Failure {
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
    pub(super) fn const_val(&self, id: ConstId) -> R<Value> {
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
    pub(super) fn enter<T>(&self, at: Span, f: impl FnOnce() -> R<T>) -> R<T> {
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
    pub(super) fn call_with(&self, fn_: FnId, args: Vec<ArgVal>, site: Span) -> R<Value> {
        // The limit comes before the safety net, so a right limit is reached
        // first.
        if self.depth.get() >= MAX_CALL_DEPTH {
            return depth_limit(site);
        }
        self.check_stack(site, Check::Call);
        self.depth.set(self.depth.get() + 1);
        let r = self.run_body(fn_, args);
        self.depth.set(self.depth.get() - 1);
        match r {
            Err(Signal::Fail(Failure::Panic(p))) => Err(out_of_call(p, site, fn_)),
            r => r,
        }
    }

    /// The body of `fn_` with its parameters bound to `args`, not counted.
    #[inline(always)]
    pub(super) fn run_body(&self, fn_: FnId, args: Vec<ArgVal>) -> R<Value> {
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
}

/// A panic that goes out of the call of `callee` at `site` ([`Panic::calls`]).
#[cold]
#[inline(never)]
fn out_of_call(mut p: Panic, site: Span, callee: FnId) -> Signal {
    p.calls.push(CallSite { span: site, callee });
    Signal::Fail(Failure::Panic(p))
}

/// The panic of a call beyond [`MAX_CALL_DEPTH`] (spec §12.5), at the call.
#[cold]
#[inline(never)]
fn depth_limit(site: Span) -> R<Value> {
    panic(site, format!("the call depth reached its limit of {MAX_CALL_DEPTH}"))
}
