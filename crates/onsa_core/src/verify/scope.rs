//! The walk of the verifier on the list of the children (`walk.rs`): the
//! children of a node in evaluation order, then the node where it is
//! ([`V::stmt_here`], [`V::expr_here`]; an error in a part is found before
//! one of its parent). The context a node is checked in, the locals seen
//! (V-04), a loop (V-07) and the sample loop of a `process` (V-19), changes
//! in [`V::child`] only.

use super::{R, Rule, V};
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
        let var = match s.kind {
            StmtKind::ForRange(l, ..) => Some(l),
            _ => None,
        };
        let mut r = Ok(());
        stmt_children(s, &mut |c| {
            if r.is_ok() {
                r = self.child(c, var)
            }
        });
        r?;
        self.stmt_here(s)?;
        if let StmtKind::Let(l, _) = s.kind {
            self.define(l)?;
            self.lets[l.0 as usize] = true;
        }
        self.at = outer;
        Ok(())
    }

    pub(super) fn expr(&mut self, e: &'a Expr) -> R<()> {
        let outer = self.at.replace(e.span);
        let mut r = Ok(());
        expr_children(e, &mut |c| {
            if r.is_ok() {
                r = self.child(c, None)
            }
        });
        r?;
        self.expr_here(e)?;
        self.at = outer;
        Ok(())
    }

    fn place(&mut self, p: &'a Place, role: PlaceRole) -> R<()> {
        let mut r = Ok(());
        place_children(p, role, &mut |c| {
            if r.is_ok() {
                r = self.child(c, None)
            }
        });
        r?;
        self.place_here(p)
    }

    /// A child in its context. The names defined in a block a backend opens
    /// or in a child not always evaluated (the right operand of a `Logic`,
    /// the condition of a `While`, a value a panic shows) are not seen past
    /// it; a block expression closes no name, as it ends no life (V-04).
    /// The body of a loop is in that loop; its condition is in the loop
    /// around it if any, as its source is for a `for` (§7, V-07). `var`, the
    /// variable of a `ForRange`, is defined in its body, the sample loop of a
    /// `process` (V-19).
    fn child(&mut self, c: Child<'a>, var: Option<LocalId>) -> R<()> {
        let (mark, outer) = (self.undo.len(), (self.in_loop, self.known));
        let closes = match c {
            Child::Expr(x, eval, role) => {
                self.expr(x)?;
                if role == Role::Inout {
                    self.inout(x)?;
                }
                eval != Eval::Always
            }
            Child::Block(b, scope, eval) => {
                self.in_loop |= eval == Eval::Loop;
                if let Some(l) = var {
                    self.define(l)?;
                    self.known |= self.process;
                }
                self.block(b)?;
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

    /// A parameter, a `let` or the variable of a `for`: seen from here to
    /// the end of its scope; a second `let` of a local seen changes nothing.
    pub(super) fn define(&mut self, l: LocalId) -> R<()> {
        self.local_ty(l)?;
        if !std::mem::replace(&mut self.visible[l.0 as usize], true) {
            self.undo.push(l);
        }
        Ok(())
    }

    /// V-05: the root of a place written is no borrowed parameter. A write
    /// through a view (`let v = xs.slice(…)`, then `v[0] = …`) has the view
    /// as its root: the verifier leaves it to sema.
    pub(super) fn writable(&self, root: LocalId) -> R<()> {
        let Some(f) = self.f.filter(|f| f.params.iter().any(|p| p.local == root && p.mode == Mode::Borrow)) else {
            return Ok(());
        };
        let name = &f.locals[root.0 as usize].name;
        Err(self.err(Rule::V05, format!("write to the borrowed parameter `{name}`")))
    }

    /// The places an `inout` argument writes: writable (V-05). That it is of
    /// the forms that write places is its parent's check.
    fn inout(&self, x: &Expr) -> R<()> {
        let mut r = Ok(());
        written_places(x, &mut |p| {
            if let (Ok(()), Some(l)) = (&r, p.place_root()) {
                r = self.writable(l)
            }
        });
        r
    }

    /// V-19 (S-196): an index known in range is in the sample loop of a `process` only.
    pub(super) fn bounds(&self, b: Bounds) -> R<()> {
        if b == Bounds::Known && !self.known {
            return Err(self.err(Rule::V19, "an index known in range outside the sample loop of `process`"));
        }
        Ok(())
    }
}
