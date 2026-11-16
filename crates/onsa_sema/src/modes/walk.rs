//! The walk of the expressions (§5.2, §5.3): each gives its
//! sub-expressions their positions, and a place at a consuming position goes
//! to [`Walker::consume`]. A call gives its receiver and arguments the
//! positions of the parameters of its callee (`calls.rs`).

use onsa_syntax::ast::{ExprId, ExprKind, Lit, Mode, PatId, StrSeg};

use super::check::Walker;
use super::drops::Leave;
use super::flow::Run;
use super::place::{Place, Proj, hole_place, pattern_places, place_of};
use crate::Kind;
use crate::body::{Dropped, Taken, Target};
use crate::ty::{Ty, TyId};

/// Where a value stands (§5.2, §5.3): what the walk checks at it. Passed down
/// to the tails of a block, an `if` and a `match` (§5.2) and through
/// parentheses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pos {
    /// An operand, a condition, a guard, an index, a statement's value.
    Read,
    /// A borrowed or `inout` argument, a receiver, an index base, a borrowed
    /// `for` head.
    Arg(Mode),
    /// A borrowed argument of a parameter whose declared type is not a
    /// function type (a `T`, of a method of the std too): its callee may
    /// keep a copy (S-809).
    Kept,
    /// The argument of a `move` parameter (S-609).
    MoveArg,
    /// The value of a `let` or `match` head whose row is a borrow (§5.4;
    /// S-810: a `match` head binds as a `let` does, whatever its arms).
    Bind,
    /// An owned head: of a `let`, `match` or `for`, the value of a `var`
    /// (S-795: a Dup value's `move` chooses the owned binding).
    Own,
    /// Where a value is put: an assignment's value, an element of a literal
    /// or a constructor (S-795: a Dup value's `move` is E0703).
    Value,
    /// `return e` and the tail of a function or anonymous function.
    Return,
    /// A consuming position with no mark written: the operand of `?`, a
    /// `move self` receiver (S-786, §5.2, §9.1).
    Extract,
    /// An argument of a call on a value of the error type (§18.1): no check.
    Unknown,
}

impl Pos {
    /// A value at it is consumed (§5.2): moved, copied or an error; the
    /// whole of an owned binding of a Dup value that is not Copy is
    /// released at it (S-1030, `Walker::release`).
    pub(super) fn consumes(self) -> bool {
        matches!(self, Pos::Own | Pos::Value | Pos::MoveArg | Pos::Return | Pos::Extract)
    }

    /// A value made at it is borrowed by a call or an index, and waits for
    /// it to run (R-32, D3: `Walker::waits`); at another position that does
    /// not consume, it is dropped where it is.
    pub(super) fn waits(self) -> bool {
        matches!(self, Pos::Arg(Mode::Borrow) | Pos::Kept)
    }

    /// It consumes, and an owned Affine place at it is moved with `move`
    /// written (§5.2, S-807): of the consuming positions, all but a return
    /// and the ones with no mark (`Extract`).
    pub(super) fn takes_move(self) -> bool {
        matches!(self, Pos::Own | Pos::Value | Pos::MoveArg)
    }

    /// What a second-class value at it would be (§5.3), `None` where one
    /// stands (an operand, a function-type argument).
    pub(super) fn out(self) -> Option<&'static str> {
        Some(match self {
            Pos::Read | Pos::Arg(_) | Pos::Unknown => return None,
            Pos::Bind | Pos::Own | Pos::Value => "stored",
            Pos::Return => "returned",
            Pos::MoveArg | Pos::Extract => "moved",
            Pos::Kept => "passed to a parameter whose type is not a function type",
        })
    }
}

impl<'a> Walker<'a> {
    /// Walk `e` at `pos` (in source order).
    pub(super) fn expr(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        #[cfg(test)]
        {
            self.m.visits += 1;
        }
        let ast = self.ast;
        // A place goes whole to `consume` (a candidate outside parentheses).
        if pos.consumes() && place_of(ast, self.names, e).is_some() {
            return self.consume(r, e, pos, None);
        }
        if self.control(r, e, pos) || self.out_of_place(r, e, pos) {
            return;
        }
        // A use of a place is of its path, at the whole of it (S-803).
        if let Some(place) = self.path(r, e) {
            self.used(r, &place, ast.expr(e).span, None);
            return;
        }
        // An element is where a value is put, but for a literal passed to a
        // callee that is not known, which is not checked (§18.1, R-372).
        let element = if pos == Pos::Unknown { Pos::Unknown } else { Pos::Value };
        match &ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => {
                for (i, seg) in s.segments.iter().enumerate() {
                    let StrSeg::Interp(p) = seg else { continue };
                    if let Some(place) = hole_place(self.names, e, i as u32, p) {
                        self.used(r, &place, p.span, None);
                    }
                }
            }
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => self.elements(r, xs.iter().copied(), element),
            // The fields of a generated `In` or `Out` stand at arguments (§11.6).
            ExprKind::Struct { fields, .. } => match self.planar_literal(e) {
                Some(parts) => self.elements(r, parts.into_iter(), Pos::Arg(Mode::Borrow)),
                None => self.elements(r, fields.iter().map(|&(_, x)| x), element),
            },
            // The path of an error leaves the function (§9.1).
            ExprKind::Try(x) => {
                self.expr(r, *x, Pos::Extract);
                self.drops(r, 0, ast.expr(e).span, Leave::Exit);
            }
            ExprKind::Repeat { elem, len } => {
                self.expr(r, *elem, element);
                self.expr(r, *len, Pos::Read);
                self.repeated(r, e, *elem, element);
            }
            // The base waits for the index (§3.5), then is read.
            ExprKind::Index { base, index } => {
                let values = r.items();
                self.expr(r, *base, Pos::Arg(Mode::Borrow));
                self.waits(r, *base, Pos::Arg(Mode::Borrow));
                self.expr(r, *index, Pos::Read);
                self.ran(r, values, ast.expr(e).span);
            }
            // A path of a value made here (D2): consumed, the rest of it is dropped there; else the whole, after.
            ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } => match pos.consumes() {
                true => self.take_out(r, e, pos),
                false => self.expr(r, *base, if pos.waits() { pos } else { Pos::Read }),
            },
            ExprKind::Call { callee, args, kind } => {
                self.call(r, e, *callee, args, *kind);
                // `panic`, which does not come back (§7).
                if self.info.diverging.expr(e) {
                    r.cur.stop();
                }
            }
            _ => ast.sub_exprs(e).into_iter().for_each(|x| self.expr(r, x, Pos::Read)),
        }
        // A value made where nothing consumes it is dropped there (R-32), or waits for its call or index (D3).
        if !pos.consumes() && !pos.waits() && pos != Pos::Unknown && self.made(e, false) {
            self.drop_point(r, ast.expr(e).span, Dropped::Temp(e), (true, None));
        }
    }

    /// Whether `e` makes a new value that needs a drop where nothing
    /// consumes it (R-32, §12.2): a call, a `?`, a literal, the name of a
    /// variant (§5.4: `None`, no place), owned ([`Walker::owned`]: not one
    /// that is static or needs no drop, S-610, S-613, nor Copy); with
    /// `joins` (the root of a path taken out), a block, an `if` or a
    /// `match` too, whose tails move into it (§5.2).
    pub(super) fn made(&mut self, e: ExprId, joins: bool) -> bool {
        let new = match self.ast.expr(e).kind {
            ExprKind::Call { .. }
            | ExprKind::Try(_)
            | ExprKind::Lit(_)
            | ExprKind::Tuple(_)
            | ExprKind::Array(_)
            | ExprKind::Struct { .. }
            | ExprKind::Repeat { .. } => true,
            ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::Match { .. } => joins,
            // The name before the type arguments (`None::[Buf[F32]]`, §4.5).
            ExprKind::Path(_) | ExprKind::Field { .. } | ExprKind::TypeArgs { .. } => {
                let name = match self.ast.expr(e).kind {
                    ExprKind::TypeArgs { base, .. } => base,
                    _ => e,
                };
                matches!(self.info.targets.get(&name), Some(Target::Variant { .. }))
            }
            _ => false,
        };
        new && !self.info.diverging.expr(e) && self.owned(e)
    }

    /// The value `e`, a path of fields at `pos`, which consumes it: of a
    /// value made here (D2), an Affine one is taken out and the rest of the
    /// value dropped there (S-85, R-32); another is copied, and the whole
    /// value dropped. Else (a path of a place), read.
    fn take_out(&mut self, r: &mut Run, e: ExprId, pos: Pos) {
        let mut path = Vec::new();
        let root = self.root_of_path(e, Some(&mut path));
        path.reverse();
        if !self.made(root, true) {
            return self.expr(r, root, Pos::Read);
        }
        self.expr(r, root, pos);
        let ty = self.info.expr_types.get(&e).copied();
        let at = self.ast.expr(e).span;
        let what = match ty.and_then(|t| self.kind_of(t)) {
            Some(Kind::Affine) => Dropped::TempRest(Box::new(Taken { root, path })),
            // SPEC-GAP(S-1034): a Shared field is copied (§5.2), and the whole value dropped.
            _ => Dropped::Temp(root),
        };
        self.drop_point(r, at, what, (true, None));
    }

    /// The root of `e` through its fields and tuple elements (and
    /// parentheses); its steps pushed on `path`, if given, the last first.
    pub(super) fn root_of_path(&self, e: ExprId, mut path: Option<&mut Vec<Proj>>) -> ExprId {
        let mut x = self.ast.without_parens(e);
        loop {
            let (base, step) = match &self.ast.expr(x).kind {
                ExprKind::Field { base, name } => (*base, path.is_some().then(|| Proj::Field(name.name.clone()))),
                ExprKind::TupleIndex { base, index, .. } => (*base, Some(Proj::Elem(*index))),
                _ => return x,
            };
            if let (Some(p), Some(s)) = (path.as_deref_mut(), step) {
                p.push(s);
            }
            x = self.ast.without_parens(base);
        }
    }

    /// The elements `xs` of a literal at `pos`, in the order written (§3.5):
    /// each waits for the ones after it (A-1).
    fn elements(&mut self, r: &mut Run, xs: impl Iterator<Item = ExprId>, pos: Pos) {
        let base = r.items();
        for x in xs {
            self.expr(r, x, pos);
            self.waits(r, x, pos);
        }
        r.forget(base);
    }

    /// The place `e` is, the indexes in it walked first, the inner first
    /// (§3.5: an element is read after its index is evaluated, S-803).
    fn path(&mut self, r: &mut Run, e: ExprId) -> Option<Place> {
        let place = place_of(self.ast, self.names, e)?;
        let (mut indexes, mut x) = (Vec::new(), self.ast.without_parens(e));
        loop {
            x = match &self.ast.expr(x).kind {
                ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } => *base,
                ExprKind::Index { base, index } => {
                    indexes.push(*index);
                    *base
                }
                _ => break,
            };
            x = self.ast.without_parens(x);
        }
        indexes.into_iter().rev().for_each(|i| self.expr(r, i, Pos::Read));
        Some(place)
    }

    /// The value `e` of a head at `pos` with the patterns `pats` (of each
    /// arm of a `match`): a place of a binding of the index at a borrow row
    /// is used by the paths the patterns read (S-803's D1, D2, S-804: the
    /// elements bound, the ones compared, a variant's position whole, not
    /// `_`), at `e`, each noted at the first element that reads it.
    pub(super) fn head(&mut self, r: &mut Run, e: ExprId, pos: Pos, pats: &[PatId]) {
        let place = place_of(self.ast, self.names, e).filter(|p| pos != Pos::Own && self.deps.indexed(p.root));
        let Some(place) = place else { return self.expr(r, e, pos) };
        let at = self.ast.expr(e).span;
        self.path(r, e);
        self.read_captured(place.root, at);
        let mut reads = Vec::new();
        for &p in pats {
            pattern_places(self.ast, self.info, p, &mut place.proj.clone(), &mut |_, proj, q| {
                reads.push((proj.to_vec(), q))
            });
        }
        for (proj, q) in reads {
            let by = self.ast.pat(q).span;
            if !self.used(r, &Place { root: place.root, proj }, at, Some(by)) {
                return;
            }
        }
    }

    /// The borrowed argument `e` of a parameter of the type `param`, if
    /// read: a planar literal passes its elements on as arguments (§5.3:
    /// `planes([a, b])`). An `inout` one is a write (`write.rs`).
    pub(super) fn argument(&mut self, r: &mut Run, e: ExprId, param: TyId) {
        match self.planar_literal(e) {
            Some(parts) => parts.into_iter().for_each(|y| self.expr(r, y, Pos::Arg(Mode::Borrow))),
            None => self.expr(r, e, self.borrowed_at(param)),
        }
    }

    /// The position of a borrowed argument of a parameter of the declared
    /// type `param` (S-809): `Kept` unless a function type (an alias
    /// resolved) or the error type.
    pub(super) fn borrowed_at(&self, param: TyId) -> Pos {
        match self.a.types.get(param) {
            Ty::Fn(_) | Ty::Error => Pos::Arg(Mode::Borrow),
            _ => Pos::Kept,
        }
    }

    /// The elements of `e`, an array literal passed as a planar argument
    /// (`[a, b]` at `[Span[T]; N]`, §5.3, S-196) or a literal of a generated
    /// `In` or `Out` (§11.6), through the planar literals of its fields (the
    /// types stage's [`crate::body::BodyInfo::planar`]): each is an argument
    /// of its own, whose place is checked for exclusivity. Read by the walk,
    /// the writes and the places passed.
    pub(super) fn planar_literal(&self, e: ExprId) -> Option<Vec<ExprId>> {
        let x = self.ast.without_parens(e);
        let parts: Vec<ExprId> = match &self.ast.expr(x).kind {
            _ if !self.info.planar.contains(&x) => return None,
            ExprKind::Array(parts) => parts.clone(),
            ExprKind::Struct { fields, .. } => fields.iter().map(|&(_, f)| f).collect(),
            _ => return None,
        };
        Some(parts.into_iter().flat_map(|p| self.planar_literal(p).unwrap_or_else(|| vec![p])).collect())
    }
}
