//! Places (W4-07 memo 1.2, 1.7; §5.1, §5.2): a local and the projections
//! that reach a part of it. It reads the syntax tree and the names only, not
//! the walk (W8-05 makes it public): the projections of a pattern and the
//! index of §7 too. W4-08 adds the views.

use std::collections::{BTreeSet, HashMap};

use onsa_diag::internal::bug;
use onsa_syntax::ast::{Ast, ExprId, ExprKind, PatId, PatKind, StmtKind};

use crate::binding::{Head, HeadRow};
use crate::body::{BodyInfo, LocalId};
use crate::names::body::{BodyNames, PathRes};
use crate::ty::TyId;

/// A place (§5.1): a local and its projections, outermost last.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Place {
    pub(super) root: LocalId,
    pub(super) proj: Vec<Proj>,
}

/// One step into a value: a field, a tuple element, an element of a
/// payload (a pattern's), an element of an array at an index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Proj {
    Field(String),
    Elem(u32),
    Payload(u32),
    Index,
}

/// The place `e` is, through parentheses: a local, and its fields, tuple
/// elements and elements (§5.2); `None` for any other value (a call, a
/// literal, a constant, a function item, a block, an `if` or a `match`). The
/// form is [`Ast::place_root_node`]'s, the one definition of it.
pub(super) fn place_of(ast: &Ast, names: &BodyNames, e: ExprId) -> Option<Place> {
    let root = ast.place_root_node(e)?;
    let Some(PathRes::Local(b)) = names.paths.get(&root) else { return None };
    let (mut proj, mut x) = (Vec::new(), ast.without_parens(e));
    while x != root {
        let (base, step) = match &ast.expr(x).kind {
            ExprKind::Field { base, name } => (*base, Proj::Field(name.name.clone())),
            ExprKind::TupleIndex { base, index, .. } => (*base, Proj::Elem(*index)),
            ExprKind::Index { base, .. } => (*base, Proj::Index),
            _ => bug(Some(ast.expr(x).span), "a step of a place `place_root_node` does not take"),
        };
        proj.push(step);
        x = ast.without_parens(base);
    }
    proj.reverse();
    Some(Place { root: LocalId(b.0), proj })
}

/// Whether the places `a` and `b` may share a part (§5.2): the same local,
/// and the projections the same up to the shorter one, where two indexes
/// are taken as the same (they are not compared statically). §7 reads it,
/// and E0702 (U4).
pub(super) fn overlaps(a: &Place, b: &Place) -> bool {
    a.root == b.root && a.proj.iter().zip(&b.proj).all(|(p, q)| p == q)
}

/// Each local the pattern `p` binds, with its projection from the value the
/// pattern matches (memo 2.3): a tuple's element, a struct's field, a
/// payload's element; each branch of a choice has its own.
fn pattern_places(ast: &Ast, info: &BodyInfo, p: PatId, proj: &mut Vec<Proj>, f: &mut dyn FnMut(LocalId, &[Proj])) {
    let mut each = |step: Proj, q: PatId, proj: &mut Vec<Proj>| {
        proj.push(step);
        pattern_places(ast, info, q, proj, f);
        proj.pop();
    };
    match &ast.pat(p).kind {
        PatKind::Bind(_) => match info.pat_locals.get(&p) {
            Some(&l) => f(l, proj),
            None => bug(Some(ast.pat(p).span), "a binding with no local"),
        },
        PatKind::Tuple(ps) => (ps.iter().enumerate()).for_each(|(i, &q)| each(Proj::Elem(i as u32), q, proj)),
        PatKind::TupleStruct { elems, .. } => {
            (elems.iter().enumerate()).for_each(|(i, &q)| each(Proj::Payload(i as u32), q, proj))
        }
        PatKind::Struct { fields, .. } => fields.iter().for_each(|(n, q)| each(Proj::Field(n.name.clone()), *q, proj)),
        PatKind::Or(ps) => ps.iter().for_each(|&q| pattern_places(ast, info, q, proj, f)),
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
    }
}

/// The index of §7 (memo 2.3): of each local, the bindings that derive from
/// a place of it, each with that place. Made once for a body from the heads
/// of `let` and `match` whose row is a borrow (a `for` is E0715's, W4-09,
/// review 5), of the bindings that are not Copy (one of them holds the value
/// it was bound to, §5.4). A static value is no source, so derives nothing.
#[derive(Debug, Default)]
pub(super) struct Deps(HashMap<LocalId, Vec<(LocalId, Place)>>);

impl Deps {
    /// The index of the body `root` (`copy`: whether a type is Copy).
    pub(super) fn of_body(
        (ast, names, info): (&Ast, &BodyNames, &BodyInfo),
        root: ExprId,
        mut copy: impl FnMut(TyId) -> bool,
    ) -> Deps {
        let (mut heads, mut deps) = (Vec::new(), Deps::default());
        heads_in(ast, root, &mut heads);
        for (head, pat) in heads {
            let Some(HeadRow::Borrow { sources, .. }) = info.heads.get(&head) else { continue };
            let places: Vec<Place> = (sources.iter())
                .map(|&s| place_of(ast, names, s).unwrap_or_else(|| bug(Some(ast.expr(s).span), "a source no place")))
                .collect();
            pattern_places(ast, info, pat, &mut Vec::new(), &mut |l, proj| {
                if copy(info.locals[l.0 as usize].ty) {
                    return;
                }
                for s in &places {
                    let place = Place { root: s.root, proj: [&s.proj[..], proj].concat() };
                    deps.0.entry(s.root).or_default().push((l, place));
                }
            });
        }
        deps
    }

    /// The bindings a change of the place `w` leaves unusable (§7): those
    /// that derive from a place that overlaps it, and the ones derived from
    /// them (§5.4), each once. A binding derives from earlier ones only.
    pub(super) fn stale(&self, w: Place) -> BTreeSet<LocalId> {
        let (mut out, mut work) = (BTreeSet::new(), vec![w]);
        while let Some(p) = work.pop() {
            for (l, q) in self.0.get(&p.root).into_iter().flatten() {
                if overlaps(&p, q) && out.insert(*l) {
                    work.push(Place { root: *l, proj: Vec::new() });
                }
            }
        }
        out
    }

    /// Some binding derives from a place of `l`.
    pub(super) fn derives_from(&self, l: LocalId) -> bool {
        self.0.contains_key(&l)
    }
}

/// The heads of `let` and of the arms of `match` in `e`, with their patterns.
fn heads_in(ast: &Ast, e: ExprId, out: &mut Vec<(Head, PatId)>) {
    match &ast.expr(e).kind {
        ExprKind::Block(b) => out.extend(b.stmts.iter().filter_map(|&s| match &ast.stmt(s).kind {
            StmtKind::Let { pat, .. } => Some((Head::Let(s), *pat)),
            _ => None,
        })),
        ExprKind::Match { scrutinee, arms, .. } => {
            out.extend(arms.iter().map(|a| (Head::Match { scrutinee: *scrutinee }, a.pat)))
        }
        _ => {}
    }
    ast.sub_exprs(e).into_iter().for_each(|x| heads_in(ast, x, out));
}
