//! The intervals of the indexes of Core (§9.2, S-1264 P2): the checks of the
//! indexes of an array that a function's body proves in range are removed
//! ([`module`]: `Bounds::Checked` becomes `Known`), and the verifier proves
//! them again with the same functions (V-25, D-15). Lowering makes no
//! `Known` but those of the sample loop of `process` (S-196).
//!
//! An interval says the value of a node is at least its `lo` and at most its
//! `hi`. Only a node of `U8`, `U16` or `U32` has one, of the closed list of
//! rules of [`Env::interval`]: a node it does not list has none. What is
//! known where a node is ([`Env`]): the variable of a `for` in its body, from
//! the intervals of its ends, from 0 of a start of none (the body does not
//! write it, V-28); a local of one `let` that nothing writes, from its value
//! where it is defined; a constant, from its initializer ([`consts`]). The
//! base of an index of a `Span` or a `Buf` has its length at run time: no
//! index of one is proved.
//!
//! O(n), but for the type of the base of an index of a place, found from
//! its root ([`Parts::place`]): one walk finds the locals written
//! ([`fixed`]), one marks. An interval stops at an `Index` and at a
//! `Const`, so each node is in the interval of one index, one `let` or one
//! end of a `for`. The walks recurse: they run after V-22, on a Core of at
//! most `CORE_DEPTH_LIMIT` levels, on the stack of a command.

use crate::ir::*;
use crate::walk::{
    Child, ChildMut, Eval, Part, PartMut, PlaceRole, Role, Scope, block_children, block_children_mut, expr_children,
    expr_children_mut, place_children, place_children_mut, stmt_children, stmt_children_mut, walk_expr, written_places,
};

/// The values a node can have: from `lo` to `hi`, `lo <= hi <=` the greatest
/// of its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Iv {
    pub lo: u64,
    pub hi: u64,
}

impl Iv {
    fn point(n: u64) -> Iv {
        Iv { lo: n, hi: n }
    }

    /// The interval if its values are of a type of the greatest `max`.
    fn within(self, max: u64) -> Option<Iv> {
        (self.hi <= max).then_some(self)
    }

    /// The one value of an interval of one value.
    fn value(iv: Option<Iv>) -> Option<u64> {
        iv.filter(|iv| iv.lo == iv.hi).map(|iv| iv.lo)
    }
}

/// The variable of a `for` and its interval in the body ([`Env::variable`]).
#[derive(Debug, Clone, Copy)]
pub struct Var {
    pub local: LocalId,
    iv: Option<Iv>,
}

/// What [`Env::enter`] changed, which [`Env::leave`] puts back.
pub struct Saved(LocalId, Option<Iv>, bool);

/// What is known of the locals of a function where a node is: the walk that
/// reads it tells it where a `let` defines a local ([`Env::define`]) and
/// where the body of a `for` begins and ends ([`Env::enter`], [`Env::leave`]).
pub struct Env<'m> {
    parts: Parts<'m>,
    /// By `ConstId`: the interval of each constant ([`consts`]).
    consts: &'m [Option<Iv>],
    /// By `LocalId`: the interval of the local, where it has one.
    vars: Vec<Option<Iv>>,
    /// By `LocalId`: a local of one `let` that nothing writes ([`fixed`]).
    fixed: Vec<bool>,
    /// By `LocalId`: the variable of a `for` around the node (V-28).
    looped: Vec<bool>,
}

impl<'m> Env<'m> {
    /// The locals of the body of `f`; of none (a `const`), no local.
    pub fn new(parts: Parts<'m>, consts: &'m [Option<Iv>], f: Option<&FnDef>) -> Env<'m> {
        let n = f.map_or(0, |f| f.locals.len());
        let fixed = f.and_then(|f| f.body.as_ref()).map_or_else(Vec::new, |b| fixed(b, n));
        Env { parts, consts, vars: vec![None; n], fixed, looped: vec![false; n] }
    }

    /// Past `let l = e`: a local of one `let` that nothing writes has the interval of `e` here.
    pub fn define(&mut self, l: LocalId, e: &Expr) {
        if self.fixed.get(l.0 as usize) == Some(&true) {
            self.vars[l.0 as usize] = self.interval(e);
        }
    }

    /// Of `for l in lo..<hi` (`lo..=hi` when `inclusive`), `l` and its values
    /// in the body: from the least of `lo` (0 when not known: `hi` of an
    /// interval is unsigned) to the greatest of `hi` (one less of `..<`),
    /// none when no value is (the loop does not run).
    pub fn variable(&self, s: &StmtKind) -> Option<Var> {
        let StmtKind::ForRange { local, lo, hi, inclusive, .. } = s else { return None };
        let last = self.interval(hi).and_then(|h| if *inclusive { Some(h.hi) } else { h.hi.checked_sub(1) });
        let lo = self.interval(lo).map_or(0, |a| a.lo);
        let iv = last.filter(|&last| lo <= last).map(|hi| Iv { lo, hi });
        Some(Var { local: *local, iv })
    }

    /// The body of the `for` of `v` begins.
    pub fn enter(&mut self, v: Var) -> Option<Saved> {
        let i = v.local.0 as usize;
        let was = std::mem::replace(self.vars.get_mut(i)?, v.iv);
        Some(Saved(v.local, was, std::mem::replace(&mut self.looped[i], true)))
    }

    /// The body of the `for` [`Env::enter`] began ends.
    pub fn leave(&mut self, saved: Option<Saved>) {
        if let Some(Saved(l, iv, looped)) = saved {
            (self.vars[l.0 as usize], self.looped[l.0 as usize]) = (iv, looped);
        }
    }

    /// Whether `l` is the variable of a `for` around the node (V-28: not written there).
    pub fn looped(&self, l: LocalId) -> bool {
        self.looped.get(l.0 as usize) == Some(&true)
    }

    /// Whether the value of `index`, of an element of `base`, is below its length here.
    pub fn proved(&self, index: &Expr, base: CTy) -> bool {
        let Ok(&TyKind::Array(_, n)) = self.parts.kind(base) else { return false };
        self.interval(index).is_some_and(|iv| iv.hi < u64::from(n))
    }

    /// The values `e` can have here, of the rules of its node and of its children.
    pub fn interval(&self, e: &Expr) -> Option<Iv> {
        let max = self.max(e.ty)?;
        match &e.kind {
            ExprKind::Lit(Lit::Int(n)) => Iv::point(u64::try_from(*n).ok()?).within(max),
            ExprKind::Local(l) => self.vars.get(l.0 as usize).copied().flatten(),
            ExprKind::Const(c) => self.consts.get(c.0 as usize).copied().flatten(),
            ExprKind::Binary { op, lhs, rhs, .. } => self.binary(*op, lhs, rhs, max),
            // A widening keeps the value (§3.3); of a signed or wider type, none.
            ExprKind::Cast(x) => self.interval(x)?.within(max),
            ExprKind::Lit(_)
            | ExprKind::Zeroed
            | ExprKind::Unary(..)
            | ExprKind::Cmp { .. }
            | ExprKind::Logic { .. }
            | ExprKind::Call { .. }
            | ExprKind::Prim { .. }
            | ExprKind::Field { .. }
            | ExprKind::Index { .. }
            | ExprKind::SpanOf(_)
            | ExprKind::Struct { .. }
            | ExprKind::Variant { .. }
            | ExprKind::Array(_)
            | ExprKind::Repeat { .. }
            | ExprKind::Tuple(_)
            | ExprKind::Tag(_)
            | ExprKind::Payload { .. }
            | ExprKind::IfExpr { .. }
            | ExprKind::Switch { .. }
            | ExprKind::Block(_)
            | ExprKind::Panic { .. } => None,
        }
    }

    /// `a op b` of a type of the greatest `max`: of `&` and `%` by an
    /// operand of one value, whatever the other; of the others, from the
    /// intervals of both, and of `+` and `<<` only when the result fits. What
    /// does not overflow is the value of mathematics, whatever the
    /// `Overflow` of the node.
    fn binary(&self, op: BinOp, a: &Expr, b: &Expr, max: u64) -> Option<Iv> {
        let (x, y) = (self.interval(a), self.interval(b));
        // A shift by one value below the width, which does not panic (`max` has its bits).
        let by = || Iv::value(y).filter(|&k| k < u64::from(max.count_ones())).map(|k| k as u32);
        match op {
            BinOp::BitAnd => match (Iv::value(x), Iv::value(y)) {
                (Some(m), Some(n)) => Some(Iv::point(m & n)),
                (Some(m), None) => Some(Iv { lo: 0, hi: y.map_or(m, |y| y.hi.min(m)) }),
                (None, Some(m)) => Some(Iv { lo: 0, hi: x.map_or(m, |x| x.hi.min(m)) }),
                (None, None) => None,
            },
            // No more bits than the wider operand.
            BinOp::BitOr => {
                let (x, y) = (x?, y?);
                Some(Iv { lo: x.lo.max(y.lo), hi: (x.hi.max(y.hi) + 1).next_power_of_two() - 1 })
            }
            BinOp::Shr => {
                let (x, k) = (x?, by()?);
                Some(Iv { lo: x.lo >> k, hi: x.hi >> k })
            }
            // `<<` drops the bits it shifts out (§3.4): a value that may lose one wraps below.
            BinOp::Shl => {
                let (x, k) = (x?, by()?);
                Iv { lo: x.lo.checked_shl(k)?, hi: x.hi.checked_shl(k)? }.within(max)
            }
            BinOp::Add => {
                let (x, y) = (x?, y?);
                Iv { lo: x.lo.checked_add(y.lo)?, hi: x.hi.checked_add(y.hi)? }.within(max)
            }
            // Not below 0: the least of `a` is at least the greatest of `b`.
            BinOp::Sub => {
                let (x, y) = (x?, y?);
                Some(Iv { lo: x.lo.checked_sub(y.hi)?, hi: x.hi.checked_sub(y.lo)? })
            }
            BinOp::Rem => {
                let l = Iv::value(y).filter(|&l| l != 0)?;
                Some(x.filter(|x| x.hi < l).unwrap_or(Iv { lo: 0, hi: l - 1 }))
            }
            BinOp::Mul | BinOp::Div | BinOp::BitXor => None,
        }
    }

    /// The greatest value of `t` when it is `U8`, `U16` or `U32`.
    fn max(&self, t: CTy) -> Option<u64> {
        match self.parts.kind(t) {
            Ok(TyKind::Int(k @ (IntKind::U8 | IntKind::U16 | IntKind::U32))) => Some((1 << k.bits()) - 1),
            _ => None,
        }
    }
}

/// By `ConstId`: the interval of each constant of `m`, of its initializer
/// where no local is known. An initializer is read once, after the
/// constants it reads, in a walk on a stack of its own: a chain of
/// constants is no recursion (R-319), and the answer is the same in any
/// order it is asked. A constant of a cycle (which the analysis rejects)
/// reads none of the cycle.
pub fn consts(m: &Module) -> Vec<Option<Iv>> {
    let n = m.consts.len();
    let (mut table, mut seen) = (vec![None; n], vec![false; n]);
    for root in 0..n {
        let mut stack = vec![(root, false)];
        while let Some((c, read)) = stack.pop() {
            if read {
                table[c] = Env::new(Parts { tys: &m.tys, types: &m.types }, &table, None).interval(&m.consts[c].init);
            } else if !std::mem::replace(&mut seen[c], true) {
                stack.push((c, true));
                walk_expr(&m.consts[c].init, &mut |e| match e.kind {
                    ExprKind::Const(d) if seen.get(d.0 as usize) == Some(&false) => stack.push((d.0 as usize, false)),
                    _ => {}
                });
            }
        }
    }
    table
}

/// By `LocalId` of the `n` locals: whether the body `b` defines the local by
/// one `let`, and no assignment, `inout` argument or `for` writes it.
fn fixed(b: &Block, n: usize) -> Vec<bool> {
    struct Scan {
        lets: Vec<u8>,
        written: Vec<bool>,
    }
    impl Scan {
        fn write(&mut self, l: LocalId) {
            if let Some(w) = self.written.get_mut(l.0 as usize) {
                *w = true;
            }
        }
        fn stmt(&mut self, s: &Stmt) {
            match &s.kind {
                StmtKind::Let(l, _) => {
                    if let Some(k) = self.lets.get_mut(l.0 as usize) {
                        *k = k.saturating_add(1);
                    }
                }
                StmtKind::Assign(p, _) => self.write(p.root()),
                StmtKind::ForRange { local, .. } => self.write(*local),
                StmtKind::Expr(_)
                | StmtKind::If(..)
                | StmtKind::While(..)
                | StmtKind::Break
                | StmtKind::Continue
                | StmtKind::Return(_) => {}
            }
            stmt_children(s, &mut |c| self.child(c));
        }
        fn child(&mut self, c: Child<'_>) {
            match c {
                Child::Expr(x, _, role) => {
                    if role == Role::Inout {
                        written_places(x, &mut |p| p.place_root().into_iter().for_each(|l| self.write(l)));
                    }
                    expr_children(x, &mut |c| self.child(c));
                }
                Child::Block(b, ..) => block_children(b, Role::Read, &mut |p| match p {
                    Part::Stmt(s) => self.stmt(s),
                    Part::Value(v, role) => self.child(Child::Expr(v, Eval::Always, role)),
                }),
                Child::Place(p, role) => place_children(p, role, &mut |c| self.child(c)),
            }
        }
    }
    let mut scan = Scan { lets: vec![0; n], written: vec![false; n] };
    scan.child(Child::Block(b, Scope::Opens, Eval::Always));
    scan.lets.iter().zip(&scan.written).map(|(&k, &w)| k == 1 && !w).collect()
}

/// The checked indexes of an array that each function of `m` proves below
/// its length become `Known`.
pub fn module(m: &mut Module) {
    let consts = consts(m);
    let Module { tys, types, fns, .. } = m;
    for f in fns.iter_mut() {
        let env = Env::new(Parts { tys, types }, &consts, Some(f));
        let mut mark = Mark { env, locals: &f.locals };
        if let Some(b) = &mut f.body {
            mark.block(b);
        }
    }
}

/// The walk of [`module`] on a function, on the `&mut` lists of `walk.rs`:
/// it tells its [`Env`] what the verifier's walk tells its own, and marks an
/// index after its children.
struct Mark<'m> {
    env: Env<'m>,
    locals: &'m [Local],
}

impl Mark<'_> {
    fn block(&mut self, b: &mut Block) {
        block_children_mut(b, Role::Read, &mut |p| match p {
            PartMut::Stmt(s) => self.stmt(s),
            PartMut::Value(v, _) => self.expr(v),
        });
    }

    /// The body of a `for` has its variable; a `let` defines past it.
    fn stmt(&mut self, s: &mut Stmt) {
        let var = self.env.variable(&s.kind);
        stmt_children_mut(s, &mut |c| match c {
            ChildMut::Block(b, ..) => {
                let saved = var.and_then(|v| self.env.enter(v));
                self.block(b);
                self.env.leave(saved);
            }
            c @ (ChildMut::Expr(..) | ChildMut::Place(..)) => self.child(c),
        });
        if let StmtKind::Let(l, e) = &s.kind {
            self.env.define(*l, e);
        }
    }

    fn child(&mut self, c: ChildMut<'_>) {
        match c {
            ChildMut::Expr(x, ..) => self.expr(x),
            ChildMut::Block(b, ..) => self.block(b),
            ChildMut::Place(p, _) => self.place(p),
        }
    }

    fn expr(&mut self, e: &mut Expr) {
        expr_children_mut(e, &mut |c| self.child(c));
        if let ExprKind::Index { base, index, bounds } = &mut e.kind {
            self.mark(bounds, index, base.ty);
        }
    }

    /// The indexes of the place `p`, after its parts (of a Core the verifier rejects, none).
    fn place(&mut self, p: &mut Place) {
        place_children_mut(p, PlaceRole::Write, &mut |c| self.child(c));
        if let Place::Index(b, i, _, bounds) = p
            && let Ok(t) = self.env.parts.place(self.locals, b)
        {
            self.mark(bounds, i, t);
        }
    }

    fn mark(&self, bounds: &mut Bounds, index: &Expr, base: CTy) {
        if *bounds == Bounds::Checked && self.env.proved(index, base) {
            *bounds = Bounds::Known;
        }
    }
}
