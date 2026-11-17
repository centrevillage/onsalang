//! What a value stands for at its position (§5.2 "位置を継ぐ", §5.3; S-1113,
//! S-1114, R-482): the one walk of the tails, the partial views, the paths
//! over values and the literals opened at an argument. It records nothing:
//! the binding stage (the heads), the types stage (`inout`) and the modes
//! (the exclusivity, the writes, the temporaries that wait, E0716) read it
//! (D-15). Linear in the expression's
//! spine and bases: each step goes into a part of the expression, once.

use onsa_syntax::ast::{Ast, ExprId, ExprKind};

use crate::Analysis;
use crate::body::{BodyInfo, view_base};
use crate::modes::Proj;
use crate::names::body::BodyNames;
use crate::tails::{Tail, tails};
use crate::ty::TyId;

/// What a stage reads: the types stage's `ty` resolves its variables, the
/// later stages' is the identity ([`Cx::after_types`]).
#[derive(Clone, Copy)]
pub(crate) struct Cx<'a> {
    pub ast: &'a Ast,
    pub names: &'a BodyNames,
    pub info: &'a BodyInfo,
    pub a: &'a Analysis,
    pub ty: &'a dyn Fn(TyId) -> TyId,
}

fn same(t: TyId) -> TyId {
    t
}

impl<'a> Cx<'a> {
    /// The reader of a stage after the types, whose types are resolved.
    pub(crate) fn after_types(ast: &'a Ast, names: &'a BodyNames, info: &'a BodyInfo, a: &'a Analysis) -> Self {
        Cx { ast, names, info, a, ty: &same }
    }

    /// The base of `e`, a partial view of it ([`view_base`]).
    pub(crate) fn view_base(&self, e: ExprId) -> Option<ExprId> {
        view_base((self.ast, self.info, self.a), e, |t| (self.ty)(t))
    }
}

/// Whether the literals of generated `In`/`Out` and planar arrays
/// ([`BodyInfo::planar`]) are opened: at an argument or a receiver (§5.3,
/// §11.6), not at a head (`let o = voice.Out { … }` stays a value, E0710).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Open {
    Arg,
    No,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum What {
    /// A place (the expression, without parentheses), of a local root.
    Place(ExprId),
    /// A value that is no place: a call, a literal, an operator, `move x`, a constant.
    Value(ExprId),
    /// The `()` of a block with no tail or of an `if` with no `else`.
    Unit(ExprId),
    /// The argument itself (or an element opened) diverges; a tail that
    /// exits gives no leaf.
    Exits,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Leaf {
    /// The unit of exclusivity: the argument as written, or an element of a
    /// literal opened at it (S-196, §11.6), as written.
    pub arg: ExprId,
    /// The unit `arg` is opened in (the argument, or a field of a generated
    /// literal whose tail is a planar literal), `arg` itself at the argument.
    pub up: ExprId,
    /// The tail of `arg`'s own spine (`tails`), or `arg` when it has none:
    /// the value put at the position (a head's `by`).
    pub tail: ExprId,
    /// The innermost tail that gives `what` (`tail` unless reached through
    /// the tails of a base): where a diagnostic is.
    pub at: ExprId,
    pub what: What,
    /// The steps written over a base that is no place, the innermost first
    /// (`(if c { o } else { p }).l`: `[l]`): the place is `what`'s then these (S-1114).
    pub over: Vec<Proj>,
    /// A partial view was taken off on the way; it adds no step (R-482).
    pub viewed: bool,
}

impl Leaf {
    /// Reached over a base that is no place: a step over a value, or the
    /// tails of a base (S-1114's forms); a head reads such a tail as owned (S-1117).
    pub(crate) fn through(&self) -> bool {
        !self.over.is_empty() || self.at != self.tail
    }
}

/// Where the walk is: the leaf so far, and whether it is on `arg`'s spine
/// (no path nor partial view taken off yet), where a tail is `arg`'s own.
#[derive(Clone)]
struct Cur {
    arg: ExprId,
    up: ExprId,
    tail: ExprId,
    at: ExprId,
    over: Vec<Proj>,
    viewed: bool,
    spine: bool,
}

impl Cur {
    fn new(arg: ExprId) -> Self {
        Cur { arg, up: arg, tail: arg, at: arg, over: Vec::new(), viewed: false, spine: true }
    }

    fn leaf(self, what: What) -> Leaf {
        let (arg, up, tail, at) = (self.arg, self.up, self.tail, self.at);
        Leaf { arg, up, tail, at, what, over: self.over, viewed: self.viewed }
    }

    /// One step written over the base: the walk goes on off the spine.
    fn over(mut self, step: Proj) -> Self {
        self.over.insert(0, step);
        self.spine = false;
        self
    }
}

/// The leaves of `e`, in source order.
pub(crate) fn leaves(cx: Cx<'_>, e: ExprId, open: Open) -> Vec<Leaf> {
    let mut out = Vec::new();
    walk(cx, e, Cur::new(e), open, &mut out);
    out
}

fn walk(cx: Cx<'_>, e: ExprId, cur: Cur, open: Open, out: &mut Vec<Leaf>) {
    let x = cx.ast.without_parens(e);
    // Off the spine, a base that diverges is a value, as the heads read it.
    if cur.spine && cx.info.diverging.expr(e) {
        return out.push(cur.leaf(What::Exits));
    }
    if let ExprKind::If { .. } | ExprKind::Match { .. } | ExprKind::Block(_) = cx.ast.expr(x).kind {
        let mut ts = Vec::new();
        tails(cx.ast, x, &cx.info.diverging, &mut ts);
        for t in ts {
            let (v, what) = match t {
                Tail::Exits => continue,
                Tail::Value(v) => (v, None),
                Tail::Unit(u) => (u, Some(What::Unit(u))),
            };
            let next = Cur { at: v, tail: if cur.spine { v } else { cur.tail }, ..cur.clone() };
            match what {
                Some(w) => out.push(next.leaf(w)),
                None => walk(cx, v, next, open, out),
            }
        }
        return;
    }
    if let Some(base) = cx.view_base(x) {
        return walk(cx, base, Cur { viewed: true, spine: false, ..cur }, open, out);
    }
    if cx.names.place_root(cx.ast, x).is_some() {
        return out.push(cur.leaf(What::Place(x)));
    }
    let opened = if open == Open::Arg { elements(cx.ast, cx.info, x) } else { None };
    match (&cx.ast.expr(x).kind, opened) {
        // A chain of names (`m.LIMIT`) and a method are values.
        (ExprKind::Field { base, name }, _)
            if !cx.names.paths.contains_key(&x) && !cx.info.targets.contains_key(&x) =>
        {
            walk(cx, *base, cur.over(Proj::Field(name.name.clone())), open, out)
        }
        (ExprKind::TupleIndex { base, index, .. }, _) => walk(cx, *base, cur.over(Proj::Elem(*index)), open, out),
        (ExprKind::Index { base, .. }, _) => walk(cx, *base, cur.over(Proj::Index), open, out),
        (_, Some(parts)) => match cur.over.first() {
            None => parts.into_iter().for_each(|(_, f)| walk(cx, f, Cur { up: cur.arg, ..Cur::new(f) }, open, out)),
            // S-1114: a path over a generated literal is of the field chosen.
            Some(Proj::Field(n)) => match parts.into_iter().find(|(i, _)| *i == Some(n.as_str())) {
                Some((_, f)) => {
                    let over = cur.over[1..].to_vec();
                    walk(cx, f, Cur { arg: f, up: cur.arg, at: f, over, spine: false, ..cur }, open, out)
                }
                None => out.push(cur.leaf(What::Value(x))),
            },
            Some(_) => out.push(cur.leaf(What::Value(x))),
        },
        _ => out.push(cur.leaf(What::Value(x))),
    }
}

/// The places `e` writes as an `inout` argument or receiver or an
/// assignment's target (§5.1, §5.3, S-178): `e` itself, or each element of
/// the literal `e` is ([`planar_parts`]), when it is a place, or a partial
/// view of one (it writes its base, R-482); `None` else, the types stage's
/// E0415: a tail, a step over a value, and a literal opened under one
/// (`inout { pair.Out { … } }`).
pub(crate) fn written(cx: Cx<'_>, e: ExprId) -> Option<Vec<ExprId>> {
    let parts = planar_parts(cx.ast, cx.info, e).unwrap_or_else(|| vec![e]);
    let place = |p: ExprId| match leaves(cx, p, Open::Arg).as_slice() {
        [l @ Leaf { what: What::Place(b), .. }] if l.arg == p && l.at == p && !l.through() => Some(*b),
        _ => None,
    };
    parts.into_iter().map(place).collect()
}

/// `e` without its parentheses and partial views.
pub(crate) fn bare(cx: Cx<'_>, mut e: ExprId) -> ExprId {
    loop {
        e = cx.ast.without_parens(e);
        match cx.view_base(e) {
            Some(b) => e = b,
            None => return e,
        }
    }
}

/// The elements of `x` (no parentheses), an array literal passed as a
/// planar argument (`[a, b]` at `[Span[T]; N]`, §5.3, S-196) or a literal of
/// a generated `In` or `Out` (§11.6), as the types stage records them
/// ([`BodyInfo::planar`]), with the names of the fields: each is an argument
/// of its own. The one test of what is opened, of the walk and of [`planar_parts`].
fn elements<'a>(ast: &'a Ast, info: &BodyInfo, x: ExprId) -> Option<Vec<(Option<&'a str>, ExprId)>> {
    match &ast.expr(x).kind {
        _ if !info.planar.contains(&x) => None,
        ExprKind::Array(parts) => Some(parts.iter().map(|&p| (None, p)).collect()),
        ExprKind::Struct { fields, .. } => Some(fields.iter().map(|(n, f)| (Some(n.name.as_str()), *f)).collect()),
        _ => None,
    }
}

/// The elements of the literal `e` opened ([`elements`]), through
/// parentheses and the literals opened at its elements. Read by the walk of
/// the modes and its writes.
pub(crate) fn planar_parts(ast: &Ast, info: &BodyInfo, e: ExprId) -> Option<Vec<ExprId>> {
    let parts = elements(ast, info, ast.without_parens(e))?;
    Some(parts.into_iter().flat_map(|(_, p)| planar_parts(ast, info, p).unwrap_or_else(|| vec![p])).collect())
}
