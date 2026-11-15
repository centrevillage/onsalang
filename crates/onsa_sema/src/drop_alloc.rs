//! Which drops of a body need `Alloc` (§12.2, R-83): the one test of a drop
//! ([`needs_alloc`]) and the list of a body ([`alloc_drops`]), from the drop
//! points the modes stage met (`BodyInfo::drops`, R-32). The record of the
//! uses (`crate::uses`) reads the list, and the effects and rt stages read
//! the record. Phase 2's drops that free nothing (`tasks/phase2.md`) are
//! conditions of [`needs_alloc`].

use onsa_diag::Span;
use onsa_diag::hash::HashMap;
use onsa_diag::internal::bug;
use onsa_syntax::ast::{Ast, ExprId};

use crate::body::{Dropped, LocalId, LocalInfo, Unbound, generics_of};
use crate::kind::{Kind, params_in_body};
use crate::modes::Proj;
use crate::summary::{Facts, Read};
use crate::ty::{Env, Ty, TyId};
use crate::walk::{Holds, Walk};
use crate::{Analysis, DefId};

/// A drop of a body (§12.2), as the stages before tell it.
pub(crate) enum Drop<'b> {
    /// An owned local, at the drop points of it (one for all, W6-02: at its
    /// declaration, which the readers name).
    Local(LocalId, &'b LocalInfo),
    /// What is left of `root`, of the type `ty`, where the path `path` is
    /// taken out at `at` (S-85).
    Rest { at: Span, path: &'b [Proj], root: Root<'b>, ty: TyId },
    /// The value of `value`, of the type `ty`, an exit (its point) leaves
    /// before its consumer runs (A-1).
    Value { value: ExprId, ty: TyId },
    /// The rest of the value `iter` of the type `ty` an owned `for` iterates,
    /// where the loop is left (`early`, as its first point tells) or ends (S-1037).
    IterRest { iter: ExprId, ty: TyId, early: bool, root: Option<LocalId> },
    /// The value of `value`, of the type `ty`, made where nothing consumes
    /// it (R-32).
    Temp { value: ExprId, ty: TyId },
    /// The value the place `target`, of the type `ty`, held before it is
    /// assigned (R-32, S-1038).
    Overwrite { target: ExprId, ty: TyId, root: Option<LocalId> },
    /// The parts of the types `tys` what is written at `at` binds to no
    /// name (§5.4, S-1036).
    Discard { at: Span, tys: &'b [TyId] },
    /// The value of `value`, of the type `ty`, of `[value; N]` whose length
    /// may be 0 (S-1045), and is (`zero`).
    Unplaced { value: ExprId, ty: TyId, zero: bool },
}

/// What a path is taken out of (S-85): an owned local, or a value no
/// binding owns (R-32).
pub(crate) enum Root<'b> {
    Local(LocalId, &'b LocalInfo),
    Value(ExprId),
}

impl Drop<'_> {
    /// Where the value is written (S-783): the declaration of a local, the
    /// expression that takes out, the pattern that binds to no name, the
    /// expression of the value or of the place.
    pub(crate) fn at(&self, ast: &Ast) -> Span {
        match self {
            Drop::Local(_, l) => l.span,
            Drop::Rest { at, .. } | Drop::Discard { at, .. } => *at,
            Drop::Value { value: e, .. }
            | Drop::Temp { value: e, .. }
            | Drop::Overwrite { target: e, .. }
            | Drop::IterRest { iter: e, .. }
            | Drop::Unplaced { value: e, .. } => ast.expr(*e).span,
        }
    }
}

/// The value a drop point drops (S-783: one value, one use): an owned
/// local, the value of an expression, what is left where a path is taken
/// out (by where), what binds to no name.
#[derive(PartialEq, Eq, Hash)]
enum Of {
    Local(LocalId),
    Expr(ExprId),
    Taken(Span),
    Unbound(Unbound),
}

impl Root<'_> {
    /// Its name, or the value as written (`src` of its span).
    pub(crate) fn name(&self, ast: &Ast, src: impl Fn(Span) -> String) -> String {
        match self {
            Root::Local(_, l) => l.name.clone(),
            Root::Value(e) => src(ast.expr(*e).span),
        }
    }
}

/// Whether the drop `d` needs `Alloc` (§12.2): the one test of a drop, by
/// the facts of the body's type parameters in `frame` ([`Frame::body`]).
pub(crate) fn needs_alloc(a: &Analysis, frame: &Frame, d: &Drop) -> bool {
    let drops = |t| frame.drops(t);
    match d {
        Drop::Local(_, l) => drops(l.ty),
        Drop::Rest { at, path, ty, .. } => rest_drops_alloc(&Walk::new(a), (*ty, frame, 0), path, *at),
        Drop::Value { ty, .. } | Drop::Temp { ty, .. } | Drop::Overwrite { ty, .. } | Drop::Unplaced { ty, .. } => {
            drops(*ty)
        }
        // At its end, its container: a fixed-length array has none (S-1037).
        Drop::IterRest { ty, early, .. } => (*early || !matches!(a.types.get(*ty), Ty::Array(..))) && drops(*ty),
        Drop::Discard { tys, .. } => tys.iter().any(|&t| drops(t)),
    }
}

/// The values the body of `id` drops where it needs `Alloc`, each once with
/// those of its drop points (`DropPoint::at`, in the order the modes stage
/// met them; each tested, as the rest of a `for` needs it on an early exit
/// alone), as the first of them tells it: the locals in the order of their
/// ids, then the others in the order of their first points. A reader that
/// takes the earliest in the source by a stable sort breaks the ties by
/// this order.
pub(crate) fn alloc_drops(a: &Analysis, id: DefId) -> Vec<(Drop<'_>, Vec<Span>)> {
    let body = &a.bodies[&id];
    let frame = Frame::body(a, params_in_body(a, &generics_of(a, id)));
    let local = |l: &LocalId| &body.locals[l.0 as usize];
    let ty =
        |e: &ExprId, at| *body.expr_types.get(e).unwrap_or_else(|| bug(Some(at), "a drop of a value with no type"));
    let (mut values, mut index) = (Vec::new(), HashMap::default());
    for d in &body.drops {
        let (of, drop) = match &d.what {
            Dropped::End(l) | Dropped::Exit(l) => (Of::Local(*l), Drop::Local(*l, local(l))),
            Dropped::Rest(t) => {
                let (l, root) = (t.root, local(&t.root));
                (Of::Taken(d.at), Drop::Rest { at: d.at, path: &t.path, root: Root::Local(l, root), ty: root.ty })
            }
            Dropped::TempRest(t) => {
                let rest = Drop::Rest { at: d.at, path: &t.path, root: Root::Value(t.root), ty: ty(&t.root, d.at) };
                (Of::Taken(d.at), rest)
            }
            Dropped::Temp(e) => (Of::Expr(*e), Drop::Temp { value: *e, ty: ty(e, d.at) }),
            &Dropped::Overwrite(e, root) => (Of::Expr(e), Drop::Overwrite { target: e, ty: ty(&e, d.at), root }),
            Dropped::Value(e) => (Of::Expr(*e), Drop::Value { value: *e, ty: ty(e, d.at) }),
            &Dropped::Unplaced { value, zero } => {
                (Of::Expr(value), Drop::Unplaced { value, ty: ty(&value, d.at), zero })
            }
            &Dropped::IterRest { iter, early, root } => {
                (Of::Expr(iter), Drop::IterRest { iter, ty: ty(&iter, d.at), early, root })
            }
            Dropped::Discard(u) => {
                let x = body.discards.get(u).unwrap_or_else(|| bug(Some(d.at), "a drop of a part with no type"));
                (Of::Unbound(*u), Drop::Discard { at: x.at, tys: &x.tys })
            }
        };
        if !needs_alloc(a, &frame, &drop) {
            continue;
        }
        let local = if let Of::Local(l) = of { Some(l) } else { None };
        let i = *index.entry(of).or_insert_with(|| {
            values.push((local, drop, Vec::new()));
            values.len() - 1
        });
        values[i].2.push(d.at);
    }
    values.sort_by_key(|(l, ..)| l.map_or((true, 0), |l| (false, l.0)));
    values.into_iter().map(|(_, d, at)| (d, at)).collect()
}

/// The type parameters of the body of `id` that, `Copy`, would free the drop
/// `d` from `Alloc` (S-1052): of those not `Copy`, each without which it
/// needs it still, the others `Copy` (`(A, B)` names both). None where it
/// needs `Alloc` whatever they are (`(T, Str)`). O(G) questions of G of them.
pub(crate) fn copy_would_free(a: &Analysis, id: DefId, d: &Drop) -> Vec<usize> {
    let params = params_in_body(a, &generics_of(a, id));
    let open: Vec<usize> = (0..params.len()).filter(|&i| params[i].drops == Some(true)).collect();
    let needs = |kept: Option<usize>| {
        let copy = |(i, f): (usize, &Facts)| match open.contains(&i) && Some(i) != kept {
            true => Facts::param(Some(Kind::Copy)),
            false => f.clone(),
        };
        needs_alloc(a, &Frame::body(a, params.iter().enumerate().map(copy).collect()), d)
    };
    if open.is_empty() || needs(None) {
        return Vec::new();
    }
    open.iter().copied().filter(|&i| needs(Some(i))).collect()
}

/// A declaration a path goes through ([`rest_drops_alloc`]): the arguments
/// of its use (`env`), written in the frame `outer` (under its `env`), and
/// their facts in `read`. Each is found once, so a long path through
/// arguments that grow reads no more than the types it writes (S-782).
pub(crate) struct Frame<'f> {
    read: Read<'f>,
    env: Env<'f>,
    outer: Option<&'f Frame<'f>>,
}

impl<'f> Frame<'f> {
    /// Of a type written where the type parameters have the facts `params`:
    /// in a body (a local, a value), or with none (an alias, a flow, which
    /// has no type parameters). The root of a chain of frames.
    pub(crate) fn body(a: &'f Analysis, params: Vec<Facts>) -> Self {
        Frame { read: Read::new(a, params), env: Env { args: &[], outer: None, key: None }, outer: None }
    }

    /// The frame of a declaration used here with the arguments `args`: the
    /// one place that makes an inner frame, so its `env` and its `outer`
    /// are of the same frame around.
    fn enter(&'f self, a: &'f Analysis, args: &'f [TyId]) -> Frame<'f> {
        let read = Read::new(a, args.iter().map(|&t| self.read.of(t)).collect());
        Frame { read, env: Env { args, outer: Some(&self.env), key: None }, outer: Some(self) }
    }

    /// Whether dropping a value of the type `ty` written here needs `Alloc`
    /// (§12.2): the one test of a type. One that holds itself has no answer
    /// ([`Facts`]): it is an E0311 of its declaration (R-02), and its drop
    /// is no use.
    pub(crate) fn drops(&self, ty: TyId) -> bool {
        self.read.of(ty).drops.unwrap_or(false)
    }

    /// `t` written here, read under the environment ([`crate::ty::Types::resolve`]):
    /// a parameter is followed to its argument, written in a frame around
    /// (the one of the environment it reaches). Only [`Frame::enter`] makes
    /// an inner frame, so the `Env` that `resolve` returns is of a frame of
    /// the chain.
    fn follow(&'f self, a: &'f Analysis, t: TyId) -> (&'f Ty, &'f Frame<'f>) {
        let (t, env) = a.types.resolve(t, Some(&self.env));
        let mut frame = self;
        while let Some(outer) = frame.outer
            && !env.is_some_and(|e| std::ptr::eq(e, &frame.env))
        {
            frame = outer;
        }
        debug_assert!(env.is_some_and(|e| std::ptr::eq(e, &frame.env)), "an environment of no frame of the chain");
        (a.types.get(t), frame)
    }
}

/// Whether dropping what is left of a value of the type `t` (written in
/// `frame`, `depth` named types in) when `path` is taken out of it at `at`
/// needs `Alloc`: the parts beside each step ([`Frame::drops`]; past a type
/// that holds itself, none).
fn rest_drops_alloc(w: &Walk, (t, frame, depth): (TyId, &Frame, u32), path: &[Proj], at: Span) -> bool {
    let Some((step, more)) = path.split_first() else { return false };
    let (ty, frame) = frame.follow(w.a, t);
    let taken = |name: &str| matches!(step, Proj::Field(n) if n == name);
    let inner;
    let (parts, frame, depth): (Vec<_>, _, _) = match (ty, step) {
        (Ty::Tuple(ts), Proj::Elem(i)) => {
            (ts.iter().enumerate().map(|(k, &t)| (t, k as u32 == *i)).collect(), frame, depth)
        }
        (Ty::Named(d, args), _) => match w.enter(*d, args, None, (depth, None)) {
            None => return false,
            Some((Holds::Alias(t), _, depth)) => {
                return rest_drops_alloc(w, (t, &Frame::body(w.a, vec![]), depth), path, at);
            }
            Some((Holds::Fields(fs, _), _, depth)) => {
                inner = frame.enter(w.a, args);
                (fs.iter().map(|f| (f.ty, taken(&f.name))).collect(), &inner, depth)
            }
            _ => (Vec::new(), frame, depth),
        },
        _ => (Vec::new(), frame, depth),
    };
    let (mut rest, mut on) = (false, None);
    for (t, taken) in parts {
        match taken {
            true => on = Some(t),
            false => rest |= frame.drops(t),
        }
    }
    if rest {
        return true;
    }
    let Some(t) = on else { bug(Some(at), "a field taken out that its type does not have") };
    rest_drops_alloc(w, (t, frame, depth), more, at)
}
