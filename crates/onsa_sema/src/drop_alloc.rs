//! Which drops of a body need `Alloc` (§12.2, R-83): the one test of a drop
//! ([`needs_alloc`]) and the list of a body ([`alloc_drops`]). The rt stage
//! (E0901) and the effects stage (the note of E0601) read the same list and
//! only word it. Phase 2's drops that free nothing (`tasks/phase2.md`) are
//! conditions of [`needs_alloc`].

use onsa_diag::Span;
use onsa_diag::hash::HashSet;

use crate::Analysis;
use crate::body::{BodyInfo, LocalId, LocalInfo, Taken};
use crate::modes::Proj;
use crate::summary::{Read, any};
use crate::ty::{Ty, TyId};
use crate::walk::{Holds, Walk};

/// A drop of a body (§12.2), as the stages before tell it.
pub(crate) enum Drop<'b> {
    /// An owned local not moved on anywhere in the body (`MovedLocals`).
    Local(&'b LocalInfo),
    /// What is left of `root` where `taken` takes a field out of it (S-85).
    Rest { taken: &'b Taken, root: &'b LocalInfo },
}

/// Whether the drop `d` needs `Alloc` (§12.2): the one test of a drop.
pub(crate) fn needs_alloc(a: &Analysis, d: &Drop) -> bool {
    match d {
        Drop::Local(l) => needs_alloc_drop(a, l.ty),
        // As `needs_alloc_drop`: no answer, so no use.
        Drop::Rest { taken: t, root } => {
            rest_drops_alloc(&Walk::new(a), (root.ty, &Frame::root(a), 0), &t.path, t.at).unwrap_or(false)
        }
    }
}

/// The drops of `body` that need `Alloc`: the owned locals not in `moved`,
/// then the rests in the order the modes stage took them out. A reader
/// takes the earliest in the source by a stable sort, so this order breaks
/// the ties.
pub(crate) fn alloc_drops<'b>(
    a: &'b Analysis,
    body: &'b BodyInfo,
    moved: Option<&'b HashSet<LocalId>>,
) -> impl Iterator<Item = Drop<'b>> {
    let locals = body.locals.iter().enumerate();
    let locals =
        locals.filter(move |(i, l)| l.state.owned() && !moved.is_some_and(|m| m.contains(&LocalId(*i as u32))));
    let rests = body.taken.iter().map(|taken| Drop::Rest { taken, root: &body.locals[taken.root.0 as usize] });
    locals.map(|(_, l)| Drop::Local(l)).chain(rests).filter(move |d| needs_alloc(a, d))
}

/// Whether dropping a value of this type needs `Alloc` (§12.2): Shared values
/// and `Buf`, or anything containing them. Flow state is Affine but drops freely.
/// A type that holds itself has no answer ([`crate::summary::Facts`]), so no use.
pub(crate) fn needs_alloc_drop(a: &Analysis, t: TyId) -> bool {
    Read::new(a, Vec::new()).of(t).drops.unwrap_or(false)
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
    /// Of a type with no parameters read as arguments: a local, an alias.
    fn root(a: &'f Analysis) -> Self {
        Frame { read: Read::new(a, Vec::new()), args: &[], outer: None }
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
            (Holds::Alias(t), _, depth) => return rest_drops_alloc(w, (t, &Frame::root(w.a), depth), path, at),
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
