//! The stack of the threads a command runs on (R-05, spec §12.5).
//!
//! A command of the CLI, a case of the test runner and every run of the
//! interpreter go on a thread with [`STACK_SIZE`] bytes of stack, spawned by
//! [`spawn`] or [`spawn_scoped`] (or by [`run`], which uses the current thread
//! when it is one). Such a thread knows where its stack starts, so a stage can
//! ask how much of it is left ([`remaining`]) and stop with an internal error
//! before it runs out, instead of the process ending by a signal.
//!
//! The start is the address of a local of the first frame of the thread, so
//! the few frames of the standard library above it are not counted: a stage
//! that uses [`remaining`] keeps a reserve larger than them.

use std::cell::Cell;
use std::thread::{Builder, JoinHandle, Scope, ScopedJoinHandle};

/// The stack size of the thread a command, a test case or a run of the
/// interpreter goes on: the one place that decides it. The CLI, the test
/// runner, the tests that parse sources (`onsa_syntax`'s CST tests) and the
/// interpreter's tests all run on it, so that all reach the same depth.
///
/// The syntax is at most 256 levels deep (spec §2.5, S-183: the parser stops
/// at the limit with E0006, `onsa_syntax::parser::NESTING_LIMIT`), so the
/// stages that recurse on the written tree are bounded. What is made from it
/// is not yet: a chain of type aliases (`type A2 = Option[A1]`, ...) expands
/// to a type as deep as the chain is long, each alias one level deep in the
/// source, and a chain of pairs (`type A2 = (A1, A1)`) takes exponential
/// time; their bound is S-264 (to decide before W4-05). Measured on
/// aarch64-apple-darwin in a debug build (2026-10-08, W3-14, the stack
/// painted under the call): `check` of one function 256 levels deep uses at
/// most 3.9 MiB (256 nested calls `id(id(...))`; parentheses 2.2 MiB, of
/// which the parser takes most, about 8.5 K a level), and `build` of a package
/// of such functions to C 8.3 MiB. The interpreter bounds its call depth well
/// inside the stack (`onsa_interp::MAX_CALL_DEPTH`, measured there).
pub const STACK_SIZE: usize = 64 << 20;

thread_local! {
    /// The address the stack of this thread starts at, when it was spawned
    /// here; 0 on any other thread.
    static TOP: Cell<usize> = const { Cell::new(0) };
}

/// The address of a local of the caller's frame: where the stack is now.
#[inline(always)]
fn here() -> usize {
    let anchor = 0u8;
    std::hint::black_box(&anchor) as *const u8 as usize
}

/// Run `f` as the body of a thread with [`STACK_SIZE`]: mark where its stack
/// starts.
fn body<T>(f: impl FnOnce() -> T) -> T {
    // The address in this frame, not in the closure of `with`, which is
    // deeper than the frames of `f`.
    let top = here();
    TOP.with(|t| t.set(top));
    f()
}

/// Spawn a thread named `name` with [`STACK_SIZE`] bytes of stack.
pub fn spawn<T: Send + 'static>(name: &str, f: impl FnOnce() -> T + Send + 'static) -> std::io::Result<JoinHandle<T>> {
    Builder::new().name(name.into()).stack_size(STACK_SIZE).spawn(move || body(f))
}

/// [`spawn`] in a scope.
pub fn spawn_scoped<'scope, 'env, T: Send + 'scope>(
    scope: &'scope Scope<'scope, 'env>,
    name: &str,
    f: impl FnOnce() -> T + Send + 'scope,
) -> std::io::Result<ScopedJoinHandle<'scope, T>> {
    Builder::new().name(name.into()).stack_size(STACK_SIZE).spawn_scoped(scope, move || body(f))
}

/// Whether the current thread was spawned here (it has [`STACK_SIZE`]).
pub fn is_command_thread() -> bool {
    TOP.with(Cell::get) != 0
}

/// Run `f` on a thread with [`STACK_SIZE`]: the current one when it is one,
/// else a new one, joined before returning. A panic in `f` goes on in the
/// caller (`std::panic::resume_unwind`). A guard that turns a panic into an
/// internal error with its position (`onsa_driver::guard`) goes inside `f`
/// (`onsa_driver::guard_on_stack`): the panic hook runs on the thread of the
/// panic, so a guard outside sees no position, and the hook prints the panic
/// (P-2).
pub fn run<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    if is_command_thread() {
        return f();
    }
    std::thread::scope(|s| {
        let handle = spawn_scoped(s, "onsa-stack", f)
            .unwrap_or_else(|e| panic!("cannot start a thread with a stack of {STACK_SIZE} bytes: {e}"));
        match handle.join() {
            Ok(v) => v,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

/// The bytes of stack left to the current thread, when it was spawned here
/// (`None` on another thread: its stack is unknown).
#[inline(always)]
pub fn remaining() -> Option<usize> {
    let top = TOP.with(Cell::get);
    if top == 0 {
        return None;
    }
    // The stack grows down on every host the compiler runs on.
    Some(STACK_SIZE.saturating_sub(top.saturating_sub(here())))
}

/// For tests and measurements only; no path of the compiler calls it. Run
/// `f` on the current thread (a thread spawned here) with about `left` bytes
/// of its stack left: between `left` and `left` + 12 K. The stack above is
/// used by frames of this function, never beyond `left`, so `f` meets a stack
/// that is nearly used up without a deep input (the safety net of the
/// interpreter, `onsa_interp::STACK_RESERVE`, is tested and measured this
/// way). `f` must not need more than `left` itself.
///
/// Panics when the thread was not spawned here, or when less than `left` is
/// left already.
#[doc(hidden)]
pub fn with_stack_left<T>(left: usize, f: impl FnOnce() -> T) -> T {
    let now = remaining().expect("with_stack_left on a thread of `onsa_diag::stack`");
    assert!(left <= now, "with_stack_left({left}) with {now} bytes left");
    let mut f = Some(f);
    use_down_to(left, &mut f)
}

/// One frame of [`with_stack_left`]: [`STEP`] bytes and a little more (up to
/// 3 × [`STEP`] in a debug build), until the next could go below `left`.
#[inline(never)]
fn use_down_to<T>(left: usize, f: &mut Option<impl FnOnce() -> T>) -> T {
    let pad = std::hint::black_box([0u8; STEP]);
    let now = remaining().unwrap_or(0);
    let r = if now < left + 3 * STEP { (f.take().expect("called once"))() } else { use_down_to(left, f) };
    // The pad lives across the call.
    std::hint::black_box(&pad);
    r
}

/// The bytes one frame of [`with_stack_left`] uses, at least.
const STEP: usize = 4 << 10;

#[cfg(test)]
mod tests {
    use super::*;

    /// `n` frames of at least 1 K each, then the stack left.
    #[inline(never)]
    fn down(n: u32) -> usize {
        let pad = std::hint::black_box([n as u8; 1024]);
        if n == 0 {
            return remaining().expect("a command thread");
        }
        let left = down(n - 1);
        // The pad lives across the call.
        std::hint::black_box(&pad);
        left
    }

    #[test]
    fn a_spawned_thread_knows_its_stack() {
        assert!(!is_command_thread(), "the test's own thread is not one");
        assert_eq!(remaining(), None);
        let (top, deep) = spawn("t", || (remaining().expect("a command thread"), down(100))).unwrap().join().unwrap();
        assert!(top <= STACK_SIZE && top > STACK_SIZE - (64 << 10), "{top}");
        assert!(deep + 100 * 1024 <= top, "{top} {deep}");
    }

    #[test]
    fn run_uses_the_current_command_thread_or_a_new_one() {
        // From a thread that is not one: a new thread, which is one.
        assert!(run(is_command_thread));
        let caller = std::thread::current().id();
        assert_ne!(run(|| std::thread::current().id()), caller);
        // From a command thread: that thread.
        let same = spawn("outer", || {
            let outer = std::thread::current().id();
            run(|| std::thread::current().id()) == outer
        })
        .unwrap()
        .join()
        .unwrap();
        assert!(same);
    }

    #[test]
    fn with_stack_left_leaves_about_that_much() {
        for left in [8usize << 20, 1 << 20, 64 << 10] {
            let got = spawn("t", move || with_stack_left(left, || remaining().unwrap())).unwrap().join().unwrap();
            assert!(got >= left && got <= left + 3 * STEP, "asked {left}, got {got}");
        }
    }

    #[test]
    fn a_panic_in_run_goes_on_in_the_caller() {
        let r = std::panic::catch_unwind(|| run(|| std::panic::panic_any(7u32)));
        assert_eq!(r.unwrap_err().downcast_ref::<u32>(), Some(&7));
    }
}
