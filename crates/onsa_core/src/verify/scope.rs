//! The walk of the verifier on the list of the children (`walk.rs`): the
//! children of a node in evaluation order, then the node where it is
//! ([`V::stmt_here`], [`V::expr_here`]; an error in a part is found before
//! one of its parent). The context a node is checked in, the locals seen
//! (V-04), a loop (V-07), the sample loop of a `process` and what is known
//! of the locals (V-25, V-28), changes in [`V::stmt`] and [`V::child`] only;
//! the state of the aliases (V-21, `aliased.rs`) in [`V::children`] too.

use super::{R, Rule, V};
use crate::bounds::Var;
use crate::ir::*;
use crate::walk::{
    Child, Eval, Part, PlaceRole, Role, Scope, block_children, expr_children, place_children, stmt_children,
    written_places,
};

impl<'a> V<'a> {
    /// The parts of `b`, in order: its statements, then its value. A block
    /// is no `inout` argument (V-05), so its value is read.
    pub(super) fn block(&mut self, b: &'a Block) -> R<()> {
        let mut r = Ok(());
        block_children(b, Role::Read, &mut |p| {
            if r.is_ok() {
                r = match p {
                    Part::Stmt(s) => self.stmt(s),
                    Part::Value(v, _) => self.expr(v),
                }
            }
        });
        r
    }

    /// A statement or an expression is the position of the errors in it
    /// but in its parts.
    pub(super) fn stmt(&mut self, s: &'a Stmt) -> R<()> {
        let outer = self.at.replace(s.span);
        let var = self.env.variable(&s.kind);
        self.children(|each| stmt_children(s, each), var)?;
        self.stmt_here(s)?;
        if let StmtKind::Alias(l, p) = &s.kind {
            self.define(*l, true)?;
            if std::mem::replace(&mut self.named[l.0 as usize], true) {
                return Err(self.err(Rule::V21, format!("a second `Alias` of the alias {}", l.0)));
            }
            self.alias_named(*l, p);
        }
        if let StmtKind::Assign(p, _) = &s.kind {
            self.alias_assigned(p)?;
        }
        if let StmtKind::Let(l, e) = &s.kind {
            self.unwritten(*l)?;
            self.define(*l, false)?;
            self.lets[l.0 as usize] = true;
            self.env.define(*l, e);
        }
        self.at = outer;
        Ok(())
    }

    /// The `inout` arguments of `e` write their places once all its
    /// children are evaluated (V-21).
    pub(super) fn expr(&mut self, e: &'a Expr) -> R<()> {
        let (outer, mark) = (self.at.replace(e.span), self.aliased.mark());
        self.children(|each| expr_children(e, each), None)?;
        self.expr_here(e)?;
        if let ExprKind::Local(l) = e.kind {
            self.alias_used(l)?;
        }
        self.alias_written(mark)?;
        self.at = outer;
        Ok(())
    }

    fn place(&mut self, p: &'a Place, role: PlaceRole) -> R<()> {
        self.children(|each| place_children(p, role, each), None)?;
        self.place_here(p, role)?;
        match p {
            Place::Local(l) => self.alias_used(*l),
            Place::Field(..) | Place::Index(..) => Ok(()),
        }
    }

    /// The children `list` gives, in order, each in its context
    /// ([`V::child`]), up to the first error. Of the aliases (V-21): each
    /// arm of a node begins with the state before the arms, and the
    /// children of a loop are in a loop of their own.
    fn children(&mut self, list: impl FnOnce(&mut dyn FnMut(Child<'a>)), var: Option<Var>) -> R<()> {
        let (mut r, mut arms, mut looped) = (Ok(()), None, false);
        list(&mut |c| {
            if r.is_err() {
                return;
            }
            let eval = match c {
                Child::Expr(_, eval, _) | Child::Block(_, _, eval) => eval,
                Child::Place(..) => Eval::Always,
            };
            self.aliased.arm(eval, &mut arms);
            if eval == Eval::Loop && !looped {
                looped = true;
                self.aliased.enter();
            }
            r = self.child(c, var);
            self.aliased.armed(eval, &mut arms);
        });
        self.aliased.arm(Eval::Always, &mut arms);
        if looped {
            self.aliased.leave();
        }
        r
    }

    /// A child in its context. The names defined in a block a backend opens
    /// or in a child not always evaluated (the right operand of a `Logic`,
    /// the condition of a `While`, a value a panic shows) are not seen past
    /// it; a block expression closes no name, as it ends no life (V-04).
    /// The body of a loop is in that loop; its condition is in the loop
    /// around it if any, as its source is for a `for` (§7, V-07). `var`, the
    /// variable of a `ForRange`, is defined in its body, with its interval,
    /// the sample loop of a `process` (V-25).
    fn child(&mut self, c: Child<'a>, var: Option<Var>) -> R<()> {
        let (mark, outer) = (self.undo.len(), (self.in_loop, self.known));
        let closes = match c {
            Child::Expr(x, eval, role) => {
                self.expr(x)?;
                if role == Role::Inout {
                    self.inout(x)?;
                    self.alias_inout(x);
                }
                eval != Eval::Always
            }
            Child::Block(b, scope, eval) => {
                self.in_loop |= eval == Eval::Loop;
                let saved = match var {
                    Some(v) => {
                        self.unwritten(v.local)?;
                        self.define(v.local, false)?;
                        self.known |= self.process;
                        self.env.enter(v)
                    }
                    None => None,
                };
                self.block(b)?;
                self.env.leave(saved);
                scope == Scope::Opens || eval != Eval::Always
            }
            Child::Place(p, role) => {
                self.place(p, role)?;
                false
            }
        };
        if closes {
            for l in self.undo.drain(mark..) {
                self.visible[l.0 as usize] = false;
            }
        }
        (self.in_loop, self.known) = outer;
        Ok(())
    }

    /// A local `how` (read, written) is seen where it is (V-04).
    pub(super) fn read_local(&self, l: LocalId, how: &str) -> R<CTy> {
        let t = self.local_ty(l)?;
        if !self.visible[l.0 as usize] {
            let name = &self.f.unwrap().locals[l.0 as usize].name;
            return Err(self.err(Rule::V04, format!("local `{name}` {how} before definition")));
        }
        Ok(t)
    }

    /// A parameter, a `let`, the variable of a `for`, or `by_alias` an
    /// `Alias`: seen from here to the end of its scope; a second definition
    /// of a local seen changes nothing. An alias is defined by an `Alias`
    /// alone, and other locals by the others (V-21).
    pub(super) fn define(&mut self, l: LocalId, by_alias: bool) -> R<()> {
        self.local_ty(l)?;
        if self.alias_kind(l).is_some() != by_alias {
            return Err(self.err(Rule::V21, format!("local {} of an alias and its definition differ", l.0)));
        }
        if !std::mem::replace(&mut self.visible[l.0 as usize], true) {
            self.undo.push(l);
        }
        Ok(())
    }

    /// V-05: the root of a place written is no borrowed parameter. A write
    /// through a view (`let v = xs.slice(…)`, then `v[0] = …`) has the view
    /// as its root: the verifier leaves it to sema. Through an alias, its
    /// place is written (`alias::resolve`): an alias written through is one
    /// of `write` (V-21).
    pub(super) fn writable(&self, root: LocalId) -> R<()> {
        if self.alias_kind(root) == Some(false) {
            return Err(self.err(Rule::V21, format!("a write through the alias {} not written through", root.0)));
        }
        let root = crate::alias::resolve(&self.aliases, &Place::Local(root)).root();
        self.unwritten(root)?;
        let Some(f) = self.f.filter(|f| f.params.iter().any(|p| p.local == root && p.mode == Mode::Borrow)) else {
            return Ok(());
        };
        let name = &f.locals[root.0 as usize].name;
        Err(self.err(Rule::V05, format!("write to the borrowed parameter `{name}`")))
    }

    /// The places an `inout` argument writes: writable (V-05), and no field
    /// below a length (V-26: the callee could write any value to it). That
    /// it is of the forms that write places is its parent's check.
    fn inout(&self, x: &Expr) -> R<()> {
        let mut r = Ok(());
        written_places(x, &mut |p| {
            if let (Ok(()), Some(l)) = (&r, p.place_root()) {
                r = self.writable(l)
            }
            if let (Ok(()), ExprKind::Field { base, index }) = (&r, &p.kind)
                && self.env.below(base.ty, *index).is_some()
            {
                r = Err(self.err(Rule::V26, format!("an `inout` argument of the field {index} below a length")));
            }
        });
        r
    }

    /// V-26: a value `v` written to the field `i` of a value of `base`
    /// below a length is proved below it; `Zeroed` is 0 (W8-07 proves that
    /// a field is written before it is read). So every value of the type
    /// has it below its length, which its reads assume (V-25): of a struct
    /// literal or a write of the field, here; of a copy of another value, of
    /// that one; of a callee given it `inout`, of the writes of the callee.
    pub(super) fn below(&self, base: CTy, i: u32, v: &Expr) -> R<()> {
        let Some(n) = self.env.below(base, i) else { return Ok(()) };
        let hi = match v.kind {
            ExprKind::Zeroed => Some(0),
            _ => self.env.interval(v).map(|iv| iv.hi),
        };
        if hi.is_some_and(|hi| hi < u64::from(n)) {
            return Ok(());
        }
        Err(self.err(Rule::V26, format!("a value not proved below {n} written to the field {i} below it")))
    }

    /// Of an alias, whether it is written through (`LocalKind::Alias`).
    pub(super) fn alias_kind(&self, l: LocalId) -> Option<bool> {
        match self.f?.locals.get(l.0 as usize)?.kind {
            LocalKind::Alias { write } => Some(write),
            LocalKind::Value => None,
        }
    }

    /// V-28: the variable of a `for` is not written in its body: no
    /// assignment, `inout` argument, `let` or `for` has it as its root.
    fn unwritten(&self, l: LocalId) -> R<()> {
        if self.env.looped(l) {
            return Err(self.err(Rule::V28, format!("the variable {} of a `for` written in its body", l.0)));
        }
        Ok(())
    }

    /// V-25 (S-196, §9.2): an index `index` of `base` known in range is in
    /// the sample loop of a `process`, or proved below its length.
    pub(super) fn known(&self, index: &Expr, base: CTy) -> R<()> {
        if !self.known && !self.env.proved(index, base) {
            let msg = "an index known in range outside the sample loop of `process` and not proved in range";
            return Err(self.err(Rule::V25, msg));
        }
        Ok(())
    }
}
