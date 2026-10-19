//! The `std` `target fn`s the interpreter runs itself ([`Prim::Std`]): which
//! it runs, and what each does.

use onsa_core::prim::Prim;
use onsa_core::{Expr, ExprKind, FloatKind, FnId, Module, PanicOrigin};
use onsa_diag::Span;

use crate::numeric::float_of;
use crate::prim::args;
use crate::value::{self, Value};
use crate::{Failure, Interp, R, Signal, Unsupported, panic_from};

/// The `std` `target fn`s the interpreter runs itself ([`Prim::Std`]). The
/// one place that decides which it runs (D-15): [`unsupported`] and the
/// evaluation both ask [`std_prim`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StdPrim {
    AssertNear,
}

pub(super) fn std_prim(name: &str) -> Option<StdPrim> {
    match name {
        "std.dsp.test.assert_near" => Some(StdPrim::AssertNear),
        _ => None,
    }
}

fn std_unsupported(name: &str, span: Span) -> Unsupported {
    Unsupported { std_fn: name.to_string(), span }
}

/// Every form this version of the interpreter cannot run (E0200, S-224) that
/// a run from the entries `roots` reaches ([`onsa_core::reach`]; spec §15.2,
/// S-242): the `std` `target fn`s it does not implement, in the bodies of the
/// reached functions, then in the initializers of the reached `const`s, each
/// in the order of the module. `onsa test` reports them before it runs any
/// test, with the tests it runs as the roots, so what it reports does not
/// depend on which code the run passes, only on what it reaches. A run
/// from the roots evaluates no other `const` (the interpreter evaluates a
/// `const` when it reads it), so it cannot step on an unreached one.
pub fn unsupported(m: &Module, roots: &[FnId]) -> Vec<Unsupported> {
    let mut out = Vec::new();
    onsa_core::reach(m, roots).walk(m, &mut |e: &Expr| {
        if let ExprKind::Prim { prim: Prim::Std(name), .. } = &e.kind
            && std_prim(name).is_none()
        {
            out.push(std_unsupported(name, e.span));
        }
    });
    out
}
impl<'m> Interp<'m> {
    /// `std` `target fn`s the interpreter implements directly ([`std_prim`]);
    /// the others are E0200 ([`unsupported`]).
    pub(super) fn std_prim(&self, prim: &Prim, name: &str, vs: &[Value], span: Span) -> R<Value> {
        match std_prim(name) {
            Some(StdPrim::AssertNear) => {
                let [a, b, tol] = args(prim, vs, span);
                let f = |v| float_of(v, FloatKind::F64, span);
                assert_near(f(a), f(b), f(tol), span)
            }
            None => Err(Signal::Fail(Failure::Unsupported(std_unsupported(name, span)))),
        }
    }
}

/// `std.dsp.test.assert_near(a, b, tol)` (spec §11.8, S-241): it passes when
/// `a == b || abs(a - b) <= tol` with the `F64` operations of §3.4; a `tol`
/// that is not finite and at least 0 (`-0.0` is 0) fails before `a` and `b`
/// are compared; a NaN fails. A failure is a panic at the call. The messages
/// are the ones the doc comment of `std/dsp/test.onsa` writes, with the values
/// in the `Show` form of §6.3 (`spec/tools.md` §4). Both failures are those of
/// an assertion ([`PanicOrigin::Assert`]), a bad `tol` too.
fn assert_near(a: f64, b: f64, tol: f64, span: Span) -> R<Value> {
    let show = |x: f64| value::show(&Value::F64(x));
    if !(tol.is_finite() && tol >= 0.0) {
        return panic_from(
            PanicOrigin::Assert,
            span,
            format!("assert_near: the tolerance {} is not a finite number at least 0", show(tol)),
        );
    }
    if a == b || (a - b).abs() <= tol {
        return Ok(Value::Unit);
    }
    panic_from(
        PanicOrigin::Assert,
        span,
        format!(
            "assert_near failed: {} and {} differ by {}, more than {}",
            show(a),
            show(b),
            show((a - b).abs()),
            show(tol)
        ),
    )
}
