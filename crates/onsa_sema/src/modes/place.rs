//! Places (W4-07 memo 1.2, 1.7; §5.1, §5.2): a local and the projections
//! that reach a part of it. It reads the syntax tree and the names only, not
//! the walk (W8-05 makes it public): the projections of a pattern and the
//! index of §7 too. W4-08 adds the views.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use onsa_diag::Span;
use onsa_diag::internal::bug;
use onsa_syntax::ast::{Ast, ExprId, ExprKind, PatId, PatKind, Path, StmtKind};
use onsa_syntax::hole_tuple_index;

use crate::binding::{Head, HeadRow};
use crate::body::{BodyInfo, LocalId};
use crate::names::body::{BodyNames, PathRes};
use crate::ty::TyId;

/// A place (§5.1): a local and its projections, outermost last.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Place {
    pub(super) root: LocalId,
    pub(super) proj: Vec<Proj>,
}

/// One step into a value: a field, a tuple element, an element of an
/// array at an index, and (a pattern's) into the payload of a variant, which
/// stands for the whole of the enum value (§5.2, S-796): no step follows it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Proj {
    Field(String),
    Elem(u32),
    Index,
    Payload,
}

impl Place {
    /// This place and then the steps `proj` (none after a payload).
    pub(super) fn then(&self, proj: &[Proj]) -> Place {
        let mut p = self.clone();
        for step in proj {
            if p.proj.last() == Some(&Proj::Payload) {
                break;
            }
            p.proj.push(step.clone());
        }
        p
    }
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

/// What [`pattern_places`] gives each element to.
pub(super) type Reads<'a> = dyn FnMut(Option<LocalId>, &[Proj], PatId) + 'a;

/// Each element the pattern `p` reads (S-803's D1, D2), with its
/// projection from the value the pattern matches (memo 2.3) and its
/// pattern: a local it binds (`Some`), a literal or constant it compares
/// and a variant whose value it reads whole at its position (`None`, a
/// variant before the locals of its payload, [`Proj::Payload`]); `_` none.
/// Each branch of a choice has its own.
pub(super) fn pattern_places(ast: &Ast, info: &BodyInfo, p: PatId, proj: &mut Vec<Proj>, f: &mut Reads<'_>) {
    let kind = &ast.pat(p).kind;
    if matches!(kind, PatKind::TupleStruct { .. } | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_)) {
        f(None, proj, p);
    }
    let mut each = |step: Proj, q: PatId, proj: &mut Vec<Proj>| {
        let n = proj.len();
        if proj.last() != Some(&Proj::Payload) {
            proj.push(step);
        }
        pattern_places(ast, info, q, proj, f);
        proj.truncate(n);
    };
    match kind {
        PatKind::Bind(_) => match info.pat_locals.get(&p) {
            Some(&l) => f(Some(l), proj, p),
            None => bug(Some(ast.pat(p).span), "a binding with no local"),
        },
        PatKind::Tuple(ps) => (ps.iter().enumerate()).for_each(|(i, &q)| each(Proj::Elem(i as u32), q, proj)),
        PatKind::TupleStruct { elems, .. } => elems.iter().for_each(|&q| each(Proj::Payload, q, proj)),
        PatKind::Struct { fields, .. } => fields.iter().for_each(|(n, q)| each(Proj::Field(n.name.clone()), *q, proj)),
        PatKind::Or(ps) => ps.iter().for_each(|&q| pattern_places(ast, info, q, proj, f)),
        PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
    }
}

/// The place a hole of a string literal names (§2.4, S-803): of its last
/// record a local, then the names after it, a tuple element by the types
/// stage's one test (`check_hole`); `None` of any other hole.
pub(super) fn hole_place(names: &BodyNames, e: ExprId, k: u32, path: &Path) -> Option<Place> {
    let (at, PathRes::Local(b)) = names.interp.get(&(e, k))?.last()? else { return None };
    let proj = (path.segments[*at as usize + 1..].iter())
        .map(|s| hole_tuple_index(&s.name).map_or_else(|| Proj::Field(s.name.clone()), Proj::Elem))
        .collect();
    Some(Place { root: LocalId(b.0), proj })
}

/// The text of the place `base` then `proj` (up to a payload): a note's.
pub(super) fn path_text(base: &str, proj: &[Proj]) -> String {
    let mut s = base.to_string();
    for step in proj.iter().take_while(|&p| p != &Proj::Payload) {
        match step {
            Proj::Field(n) => s += &format!(".{n}"),
            Proj::Elem(i) => s += &format!(".{i}"),
            _ => s += "[_]",
        }
    }
    s
}

/// A place a binding of the index derives from directly: that of a source
/// of its head with the steps of its pattern, and the source.
#[derive(Debug)]
pub(super) struct Source {
    pub(super) place: Place,
    pub(super) at: Span,
    pub(super) pat: Vec<Proj>,
}

/// The places of the sources of `head` at a borrow row (S-604: of each
/// tail; a view's base, S-217), with their text; `None` at an owned row.
pub(super) fn head_places((ast, names, info): (&Ast, &BodyNames, &BodyInfo), head: Head) -> Option<Vec<(Place, Span)>> {
    let Some(HeadRow::Borrow { sources, .. }) = info.heads.get(&head) else { return None };
    let place = |&s: &ExprId| match place_of(ast, names, s) {
        Some(p) => (p, ast.expr(s).span),
        None => bug(Some(ast.expr(s).span), "a source no place"),
    };
    Some(sources.iter().map(place).collect())
}

/// The index of §7 (memo 2.3): the bindings of the heads of `let` and
/// `match` whose row is a borrow (a `for` holds its places, E0715), but
/// the Copy ones (one of them holds the value it was bound to, §5.4), each
/// with the places it derives from directly. A static value is no source,
/// so derives nothing. The places a binding stands for (S-797: those of the
/// bindings it derives from, the steps composed) are not made: their number
/// grows as the product of the sources along a chain. A question reads them
/// along another place instead ([`along`]).
#[derive(Debug, Default)]
pub(super) struct Deps {
    /// Each binding of the index, in the order of their ids: a binding
    /// derives from earlier ones only.
    of: BTreeMap<LocalId, Vec<Source>>,
    /// The locals of the places the heads read, and those a borrowed `for`
    /// or a guard holds (R-161's condition 5).
    read: HashSet<LocalId>,
    /// Of each root (no binding of the index), the bindings that derive
    /// from it, in the order of the ids (memo 3).
    by_root: HashMap<LocalId, Vec<LocalId>>,
    /// Of each binding, the roots it derives from ([`Deps::origins`]).
    roots: HashMap<LocalId, BTreeSet<LocalId>>,
    /// The text where each binding is in scope: its block from its `let`,
    /// its arm (a change elsewhere leaves it as it is where it is used:
    /// declared again before, or never).
    scope: HashMap<LocalId, (u32, u32)>,
}

/// How far a place read from its root has gone along the ways of another
/// ([`Way`]): `At(way, steps)`, or `Over`, overlapping whatever steps follow
/// (the other ended first, or both read a payload, after which no step
/// counts, [`Place::then`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Cur {
    At(usize, usize),
    Over,
}

/// The cursors of a place along another; empty: they do not overlap.
pub(super) type Along = BTreeSet<Cur>;

/// One way to read a place from a root: from `from`, the steps, then on
/// into the binding `to` (the ways from it), or the end of the place.
#[derive(Debug)]
struct Way {
    from: LocalId,
    to: Option<LocalId>,
    steps: Vec<Proj>,
}

/// A change of a place (§7): of each binding of the index a place of
/// which overlaps it, how far it went along it. Made once for each place
/// changed (whatever binding is in scope where).
#[derive(Debug)]
pub(super) struct Change {
    ways: Vec<Way>,
    pub(super) along: HashMap<LocalId, Along>,
}

impl Change {
    /// Whether the place `p` of a binding overlaps the change: `None` if
    /// not, else whether it is a proper prefix of it (it ends before it).
    pub(super) fn reaches(&self, p: &Place) -> Option<bool> {
        let at = advance(&self.ways, self.along.get(&p.root)?.clone(), &p.proj);
        (!at.is_empty()).then(|| at.iter().any(|c| *c != Cur::Over))
    }
}

impl Deps {
    /// The index of the body `root` (`copy`: whether a type is Copy).
    pub(super) fn of_body(
        (ast, names, info): (&Ast, &BodyNames, &BodyInfo),
        root: ExprId,
        mut copy: impl FnMut(TyId) -> bool,
    ) -> Deps {
        let (mut heads, mut deps) = (Vec::new(), Deps::default());
        heads_in(ast, root, &mut heads);
        for (head, pat, scope, holds) in heads {
            let Some(places) = head_places((ast, names, info), head) else { continue };
            // R-161's condition 5: what a `for` or a guard holds (E0715) is read.
            if holds {
                deps.read.extend(places.iter().map(|(p, _)| p.root));
            }
            if let Head::For(_) = head {
                continue;
            }
            pattern_places(ast, info, pat, &mut Vec::new(), &mut |l, proj, _| {
                let Some(l) = l.filter(|l| !copy(info.locals[l.0 as usize].ty)) else { return };
                deps.scope.insert(l, scope);
                for (p, at) in &places {
                    let source = Source { place: p.then(proj), at: *at, pat: proj.to_vec() };
                    deps.of.entry(l).or_default().push(source);
                }
            });
        }
        for (&l, sources) in &deps.of {
            let mut mine = BTreeSet::new();
            for s in sources {
                if deps.of.contains_key(&s.place.root) && s.place.root >= l {
                    bug(Some(s.at), "a binding derived from a later one");
                }
                deps.read.insert(s.place.root);
                match deps.roots.get(&s.place.root) {
                    Some(r) => mine.extend(r),
                    None => drop(mine.insert(s.place.root)),
                }
            }
            mine.iter().for_each(|&r| deps.by_root.entry(r).or_default().push(l));
            deps.roots.insert(l, mine);
        }
        deps
    }

    /// The roots the places of `l` start from: of a binding of the index,
    /// those it derives from; else `l`. Two places of no common root share
    /// no part, so it is a condition [`Deps::meets`] needs (`frozen.rs`
    /// asks it first), not another judgment of the overlap.
    pub(super) fn origins(&self, l: LocalId) -> BTreeSet<LocalId> {
        self.roots.get(&l).cloned().unwrap_or_else(|| BTreeSet::from([l]))
    }

    /// Whether `l` is a binding of the index.
    pub(super) fn indexed(&self, l: LocalId) -> bool {
        self.of.contains_key(&l)
    }

    /// The places the binding `l` derives from directly.
    pub(super) fn sources(&self, l: LocalId) -> &[Source] {
        self.of.get(&l).map_or(&[], |s| s.as_slice())
    }

    /// The change of the place `w` (§7): the bindings it leaves unusable
    /// are those of `along` in scope (§5.4: the ones derived from them too,
    /// by the places they derive from, S-797), of those of its root.
    pub(super) fn change(&self, w: &Place) -> Change {
        let ways = vec![Way { from: w.root, to: None, steps: w.proj.clone() }];
        let along = self.along(&ways, self.by_root.get(&w.root).map_or(&[], Vec::as_slice));
        Change { ways, along }
    }

    /// Whether the binding `l` is in scope at `at`.
    pub(super) fn in_scope(&self, l: LocalId, at: Span) -> bool {
        self.scope.get(&l).is_some_and(|&(start, end)| start <= at.start && at.end <= end)
    }

    /// Whether the places `a` and `b` may share a part (§5.2, S-796): of a
    /// binding of the index, any place it stands for; the same local and
    /// the steps the same up to the shorter one, where two indexes are
    /// taken as the same (not compared statically). The one judgment of the
    /// overlap, E0702's and §7's.
    pub(super) fn meets(&self, a: &Place, b: &Place) -> bool {
        // The ways of `b`: those of the sources of its ancestors, then its own steps.
        let mut ways: Vec<Way> = (self.ancestors(b.root).into_iter())
            .flat_map(|u| self.sources(u).iter().map(move |s| (u, s)))
            .map(|(u, s)| Way { from: s.place.root, to: Some(u), steps: s.place.proj.clone() })
            .collect();
        ways.push(Way { from: b.root, to: None, steps: b.proj.clone() });
        let start = match self.indexed(a.root) {
            true => self.along(&ways, &self.ancestors(a.root)).remove(&a.root).unwrap_or_default(),
            false => close(&ways, starts(&ways, a.root)),
        };
        !advance(&ways, start, &a.proj).is_empty()
    }

    /// The binding `l` of the index and those it derives from, in the
    /// order of the ids.
    fn ancestors(&self, l: LocalId) -> Vec<LocalId> {
        let (mut todo, mut seen) = (vec![l], BTreeSet::new());
        while let Some(u) = todo.pop() {
            if self.indexed(u) && seen.insert(u) {
                todo.extend(self.sources(u).iter().map(|s| s.place.root));
            }
        }
        seen.into_iter().collect()
    }

    /// Of each of the bindings `bound` of the index (in the order of the
    /// ids, each after those it derives from that derive from the roots of
    /// `ways`), how far the places it stands for go along `ways`: from those
    /// of the bindings it derives from, else from the start of the ways from
    /// the root. A binding none of which overlaps is left out.
    fn along(&self, ways: &[Way], bound: &[LocalId]) -> HashMap<LocalId, Along> {
        let mut out: HashMap<LocalId, Along> = HashMap::new();
        for &l in bound {
            let mut at = Along::new();
            for s in self.sources(l) {
                let start = match self.indexed(s.place.root) {
                    true => out.get(&s.place.root).cloned().unwrap_or_default(),
                    false => close(ways, starts(ways, s.place.root)),
                };
                at.extend(advance(ways, start, &s.place.proj));
            }
            if !at.is_empty() {
                out.insert(l, at);
            }
        }
        out
    }

    /// Some head reads a place of `l`.
    pub(super) fn derives_from(&self, l: LocalId) -> bool {
        self.read.contains(&l)
    }
}

/// The starts of the ways from `l`.
fn starts(ways: &[Way], l: LocalId) -> Vec<Cur> {
    (ways.iter().enumerate()).filter(|(_, w)| w.from == l).map(|(k, _)| Cur::At(k, 0)).collect()
}

/// The cursors `todo`, each at the end of a way gone on into the next ones
/// (each once: a choice of ways does not grow them) or over.
fn close(ways: &[Way], mut todo: Vec<Cur>) -> Along {
    let (mut seen, mut out) = (BTreeSet::new(), Along::new());
    while let Some(c) = todo.pop() {
        match c {
            _ if !seen.insert(c) => {}
            Cur::At(k, i) if i == ways[k].steps.len() => match ways[k].to {
                Some(v) => todo.extend(starts(ways, v)),
                None => drop(out.insert(Cur::Over)),
            },
            c => drop(out.insert(c)),
        }
    }
    out
}

/// The cursors `at` after the steps `proj`: on where the way reads the same
/// step, over after a payload both read.
fn advance(ways: &[Way], mut at: Along, proj: &[Proj]) -> Along {
    for step in proj {
        let next = at.iter().filter_map(|&c| match c {
            Cur::At(k, i) if ways[k].steps[i] != *step => None,
            Cur::At(k, i) if *step != Proj::Payload => Some(Cur::At(k, i + 1)),
            _ => Some(Cur::Over),
        });
        at = close(ways, next.collect());
    }
    at
}

/// The heads of `let`, `for` and of the arms of `match` in `e`, with their
/// patterns, the text where their bindings are in scope, and whether they
/// hold the places of their value (a `for`, an arm with a guard: E0715).
fn heads_in(ast: &Ast, e: ExprId, out: &mut Vec<(Head, PatId, (u32, u32), bool)>) {
    let end = ast.expr(e).span.end;
    match &ast.expr(e).kind {
        ExprKind::Block(b) => out.extend(b.stmts.iter().filter_map(|&s| match &ast.stmt(s).kind {
            StmtKind::Let { pat, .. } => Some((Head::Let(s), *pat, (ast.stmt(s).span.start, end), false)),
            StmtKind::For { pat, .. } => Some((Head::For(s), *pat, (ast.stmt(s).span.start, end), true)),
            _ => None,
        })),
        ExprKind::Match { scrutinee, arms, .. } => out
            .extend((arms.iter()).map(|a| {
                (Head::Match { scrutinee: *scrutinee }, a.pat, (a.span.start, a.span.end), a.guard.is_some())
            })),
        _ => {}
    }
    ast.sub_exprs(e).into_iter().for_each(|x| heads_in(ast, x, out));
}
