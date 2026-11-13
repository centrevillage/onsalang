//! Which drops of a body need `Alloc` (§12.2, R-83): the one test of a drop
//! ([`needs_alloc`]) and the list of a body ([`alloc_drops`]), from the drop
//! points the modes stage met (`BodyInfo::drops`, R-32). The rt stage
//! (E0901) and the effects stage (the note of E0601) read the same list and
//! only word it. Phase 2's drops that free nothing (`tasks/phase2.md`) are
//! conditions of [`needs_alloc`].

use std::collections::BTreeSet;

use onsa_diag::Span;
use onsa_diag::internal::bug;
use onsa_syntax::ast::ExprId;

use crate::body::{Dropped, LocalId, LocalInfo, generics_of};
use crate::kind::params_in_body;
use crate::modes::Proj;
use crate::summary::{Facts, Read, any};
use crate::ty::{Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

/// A drop of a body (§12.2), as the stages before tell it.
pub(crate) enum Drop<'b> {
    /// An owned local, at the drop points of it (one for all, W6-02: at its
    /// declaration, which the readers name).
    Local(&'b LocalInfo),
    /// What is left of `root` where the path `path` is taken out at `at` (S-85).
    Rest { at: Span, path: &'b [Proj], root: &'b LocalInfo },
    /// The value of `value`, of the type `ty`, the exit at `exit` leaves before
    /// its consumer runs (A-1).
    Value { value: ExprId, ty: TyId, exit: Span },
    /// The rest of the value `iter` of the type `ty` an owned `for` iterates,
    /// where the loop is left at `exit` (`early`) or ends (S-1037).
    IterRest { iter: ExprId, ty: TyId, exit: Span, early: bool },
}

/// Whether the drop `d` needs `Alloc` (§12.2): the one test of a drop, by
/// the facts of the body's type parameters in `body` ([`Frame::body`]). A
/// type that holds itself has no answer ([`crate::summary::Facts`]), so no use.
fn needs_alloc(a: &Analysis, body: &Frame, d: &Drop) -> bool {
    let drops = |t| body.read.of(t).drops.unwrap_or(false);
    match d {
        Drop::Local(l) => drops(l.ty),
        Drop::Rest { at, path, root } => {
            rest_drops_alloc(&Walk::new(a), (root.ty, body, 0), path, *at).unwrap_or(false)
        }
        Drop::Value { ty, .. } => drops(*ty),
        // At its end, its container: a fixed-length array has none (S-1037).
        Drop::IterRest { ty, early, .. } => (*early || !matches!(a.types.get(*ty), Ty::Array(..))) && drops(*ty),
    }
}

/// The drops of the body of `id` that need `Alloc`: the locals of its drop
/// points (at the end of a scope and at an exit alike), each once in the
/// order of the locals, then the others in the order the modes stage met
/// them. A reader takes the earliest in the source by a stable sort, so this
/// order breaks the ties.
pub(crate) fn alloc_drops(a: &Analysis, id: DefId) -> impl Iterator<Item = Drop<'_>> {
    let body = &a.bodies[&id];
    let frame = Frame::body(a, params_in_body(a, &generics_of(a, id)));
    let local = |l: &LocalId| &body.locals[l.0 as usize];
    let locals: BTreeSet<LocalId> = (body.drops.iter())
        .filter_map(|d| match d.what {
            Dropped::End(l) | Dropped::Exit(l) => Some(l),
            _ => None,
        })
        .collect();
    let ty =
        |e: &ExprId, at| *body.expr_types.get(e).unwrap_or_else(|| bug(Some(at), "a drop of a value with no type"));
    let others = body.drops.iter().filter_map(move |d| match &d.what {
        Dropped::Rest(t) => Some(Drop::Rest { at: d.at, path: &t.path, root: local(&t.root) }),
        Dropped::Value(e) => Some(Drop::Value { value: *e, ty: ty(e, d.at), exit: d.at }),
        &Dropped::IterRest { iter, early } => Some(Drop::IterRest { iter, ty: ty(&iter, d.at), exit: d.at, early }),
        Dropped::End(_) | Dropped::Exit(_) => None,
    });
    let locals = locals.into_iter().map(move |l| Drop::Local(local(&l)));
    locals.chain(others).filter(move |d| needs_alloc(a, &frame, d))
}

/// A declaration a path goes through ([`rest_drops_alloc`]): the arguments
/// of its use, written in the frame `outer`, and their facts in `read`.
/// Each is found once, so a long path through arguments that grow reads no
/// more than the types it writes (S-782).
struct Frame<'f> {
    read: Read<'f>,
    args: &'f [TyId],
    outer: Option<&'f Frame<'f>>,
}

impl<'f> Frame<'f> {
    /// Of a type written where the type parameters have the facts `params`:
    /// in a body (a local, a value), or with none (an alias).
    fn body(a: &'f Analysis, params: Vec<Facts>) -> Self {
        Frame { read: Read::new(a, params), args: &[], outer: None }
    }
}

/// `t` written in `frame`: a parameter is followed to its argument, written
/// in the frame around.
fn follow<'f>(a: &'f Analysis, mut t: TyId, mut frame: &'f Frame<'f>) -> (&'f Ty, &'f Frame<'f>) {
    loop {
        match (a.types.get(t), frame.outer) {
            (Ty::Param(i), Some(outer)) if (*i as usize) < frame.args.len() => {
                (t, frame) = (frame.args[*i as usize], outer);
            }
            (ty, _) => return (ty, frame),
        }
    }
}

/// Whether dropping what is left of a value of the type `t` (written in
/// `frame`, `depth` named types in) when `path` is taken out of it at `at`
/// needs `Alloc`: the parts beside each step ([`Read`]).
fn rest_drops_alloc(w: &Walk, (t, frame, depth): (TyId, &Frame, u32), path: &[Proj], at: Span) -> Option<bool> {
    let Some((step, more)) = path.split_first() else { return Some(false) };
    let (ty, frame) = follow(w.a, t, frame);
    let taken = |name: &str| matches!(step, Proj::Field(n) if n == name);
    let inner;
    let (parts, frame, depth): (Vec<_>, _, _) = match (ty, step) {
        (Ty::Tuple(ts), Proj::Elem(i)) => {
            (ts.iter().enumerate().map(|(k, &t)| (t, k as u32 == *i)).collect(), frame, depth)
        }
        (Ty::Named(d, args), _) => match w.enter(*d, args, None, (depth, None))? {
            (Holds::Alias(t), _, depth) => return rest_drops_alloc(w, (t, &Frame::body(w.a, vec![]), depth), path, at),
            (Holds::Fields(fs, _), _, depth) => {
                let params = args.iter().map(|&t| frame.read.of(t)).collect();
                inner = Frame { read: Read::new(w.a, params), args, outer: Some(frame) };
                (fs.iter().map(|f| (f.ty, taken(&f.name))).collect(), &inner, depth)
            }
            _ => (Vec::new(), frame, depth),
        },
        _ => (Vec::new(), frame, depth),
    };
    let (mut rest, mut on) = (Some(false), None);
    for (t, taken) in parts {
        match taken {
            true => on = Some(t),
            false => rest = any(rest, frame.read.of(t).drops),
        }
    }
    if rest == Some(true) {
        return rest;
    }
    let Some(t) = on else { onsa_diag::internal::bug(Some(at), "a field taken out that its type does not have") };
    any(rest, rest_drops_alloc(w, (t, frame, depth), more, at))
}
