//! The primitives the C backend provides (S-69 (3), spec §15.2), and the
//! check of a unit against them before it is generated.

use std::collections::BTreeSet;

use onsa_core::prim::Prim;
use onsa_core::walk::{walk_block, walk_expr};
use onsa_core::{Expr, ExprKind, FnId, Module, Reach};
use onsa_diag::Diagnostic;
use onsa_diag::unsupported::Feature;
use onsa_diag::{Span, internal};

use crate::unsupported;

/// Whether the C backend provides `prim`: the one place that decides it
/// (D-15). A unit that reaches one it does not provide is E0200 before it
/// is generated ([`check`]).
pub(crate) fn supports(p: &Prim) -> bool {
    match p {
        Prim::BufZeroed | Prim::AssertNear | Prim::Pending(_) => false,
        Prim::Math(..)
        | Prim::IntAbs(_)
        | Prim::IntMin(_)
        | Prim::IntMax(_)
        | Prim::NarrowParts { .. }
        | Prim::IntToFloat { .. }
        | Prim::FloatToFloat { .. }
        | Prim::TruncToInt { .. }
        | Prim::ToBits(_)
        | Prim::FromBits(_)
        | Prim::Parts(..)
        | Prim::DivEuclid(_)
        | Prim::RemEuclid(_)
        | Prim::IsNan(_)
        | Prim::IsFinite(_)
        | Prim::Len
        | Prim::Slice
        | Prim::Get
        | Prim::Fill
        | Prim::AddFrom
        | Prim::CopyFrom => true,
    }
}

/// E0200 at each use of a primitive C does not provide in what the unit
/// reaches (spec §15.2, S-242), in the order of the module, and the
/// functions that hold one: the unit generates none of them and fails with
/// these E0200s and the diagnostics of the rest.
pub(crate) fn check(m: &Module, reach: &Reach) -> (Vec<Diagnostic>, BTreeSet<FnId>) {
    let look = |out: &mut Vec<Diagnostic>, e: &Expr| {
        if let ExprKind::Prim { prim, .. } = &e.kind
            && !supports(prim)
        {
            out.push(lacking(prim, e.span));
        }
    };
    let (mut out, mut fns) = (Vec::new(), BTreeSet::new());
    for &id in &reach.fns {
        let before = out.len();
        if let Some(b) = &m.fn_(id).body {
            walk_block(b, &mut |e| look(&mut out, e));
        }
        if out.len() > before {
            fns.insert(id);
        }
    }
    for &c in &reach.consts {
        walk_expr(&m.const_(c).init, &mut |e| look(&mut out, e));
    }
    (out, fns)
}

/// The E0200 of `prim`: `Buf` for `Buf.zeroed`, else the `std` declaration.
fn lacking(prim: &Prim, span: Span) -> Diagnostic {
    if *prim == Prim::BufZeroed {
        return unsupported(span, Feature::Buf, &[]);
    }
    match prim.std_name() {
        Some(name) => unsupported(span, Feature::StdFn, &[&name]),
        None => internal::bug(Some(span), format!("the C backend lacks `{}`", prim.name())),
    }
}
