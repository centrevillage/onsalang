//! V-21, its second part: an alias `a` is not used (read, or the root of a
//! write through it) once a place that may overlap the place it names
//! ([`paths::disjoint`]) is written not through `a` (by an assignment or an
//! `inout` argument), as `a` names the place it evaluated before that write.
//!
//! The state is of each alias, lost or not, on the one walk of `scope.rs`:
//! the arms of a node begin with the state before them, and past them an
//! alias is lost when it is in any arm. A loop is walked once: an alias of
//! before it, used in it and then lost in it, would be used lost in its next
//! turn. The walk does not tell the code no path reaches (after a `Return`
//! or a `Break`) from the rest. O(nodes × aliases); of a function with no
//! alias, the state is empty and no path is made.

use super::{R, Rule, V};
use crate::ir::*;
use crate::paths::{Path, disjoint};
use crate::walk::{Eval, written_places};

/// The state of the aliases of a function.
#[derive(Default)]
pub(super) struct Aliased {
    /// By `LocalId`: the number of its alias, if it is one; by number, the local.
    slot: Vec<Option<usize>>,
    locals: Vec<LocalId>,
    named: Vec<Named>,
    /// By alias: lost, that is, a place it names written not through it.
    lost: Vec<bool>,
    /// The loops around the node, by number, and how many were opened.
    loops: Vec<u32>,
    opened: u32,
    /// The places the `inout` arguments of the calls being walked write,
    /// each with the root it is written through.
    pending: Vec<(LocalId, Path)>,
}

/// An alias, once its `Alias` is walked: the path of its place, the alias
/// at the root of that place, the depth of the loops at its `Alias`, and
/// the loop of that depth it was used in last.
#[derive(Clone, Default)]
struct Named {
    path: Option<Path>,
    via: Option<usize>,
    depth: usize,
    used_in: Option<u32>,
}

/// The arms of a node walked so far: the state before them, and the
/// aliases lost in any.
pub(super) type Arms = Option<(Vec<bool>, Vec<bool>)>;

impl Aliased {
    /// The state of `f`: empty when it has no local of `LocalKind::Alias`.
    pub(super) fn of(f: &FnDef) -> Aliased {
        let mut a = Aliased::default();
        if f.locals.iter().any(|l| l.kind != LocalKind::Value) {
            for (i, l) in f.locals.iter().enumerate() {
                let alias = l.kind != LocalKind::Value;
                a.slot.push(alias.then_some(a.locals.len()));
                if alias {
                    a.locals.push(LocalId(i as u32));
                }
            }
            let n = a.locals.len();
            (a.named, a.lost) = (vec![Named::default(); n], vec![false; n]);
        }
        a
    }

    fn slot(&self, l: LocalId) -> Option<usize> {
        self.slot.get(l.0 as usize).copied().flatten()
    }

    /// Before a child evaluated `eval`: the next arm begins from the state
    /// before the first; another child is past the arms, of their losses.
    pub(super) fn arm(&mut self, eval: Eval, arms: &mut Arms) {
        match (eval, &mut *arms) {
            (Eval::Conditional, Some((start, _))) => self.lost.clone_from(start),
            (Eval::Conditional, None) => *arms = Some((self.lost.clone(), self.lost.clone())),
            (Eval::Always | Eval::Loop | Eval::Observed, _) => {
                if let Some((_, all)) = arms.take() {
                    self.lost = all;
                }
            }
        }
    }

    /// After a child evaluated `eval`: an arm adds its losses.
    pub(super) fn armed(&mut self, eval: Eval, arms: &mut Arms) {
        if let (Eval::Conditional, Some((_, all))) = (eval, arms) {
            all.iter_mut().zip(&self.lost).for_each(|(a, &l)| *a |= l);
        }
    }

    /// Where the places of the call being walked begin in `pending`.
    pub(super) fn mark(&self) -> usize {
        self.pending.len()
    }

    pub(super) fn enter(&mut self) {
        self.opened += 1;
        self.loops.push(self.opened);
    }

    pub(super) fn leave(&mut self) {
        self.loops.pop();
    }

    /// Whether a write through the root `through` is through alias `k`: the
    /// alias it is, or one at the root of the place of that (`s` of
    /// `alias s = r[1]` is through `r`). An alias is at the root of the
    /// place of one defined after it (V-04), so the chain ends.
    fn through(&self, through: LocalId, k: usize) -> bool {
        let mut on = self.slot(through);
        while let Some(j) = on {
            if j == k {
                return true;
            }
            on = self.named[j].via;
        }
        false
    }
}

impl V<'_> {
    /// The `Alias` of `l`, of place `p`: not lost, and in the loops it is in.
    pub(super) fn alias_named(&mut self, l: LocalId, p: &Place) {
        let a = &mut self.aliased;
        let Some(k) = a.slot(l) else { return };
        let path = Some(Path::of_place(&self.aliases, p));
        a.named[k] = Named { path, via: a.slot(p.root()), depth: a.loops.len(), used_in: None };
        a.lost[k] = false;
    }

    /// A use of `l`: of an alias, not lost; in a loop its `Alias` is not in,
    /// that loop is the one it was used in last.
    pub(super) fn alias_used(&mut self, l: LocalId) -> R<()> {
        let Some(k) = self.aliased.slot(l) else { return Ok(()) };
        if self.aliased.lost[k] {
            let msg = format!("the alias {} used after a place it names was written not through it", l.0);
            return Err(self.err(Rule::V21, msg));
        }
        let a = &mut self.aliased;
        if let Some(&n) = a.loops.get(a.named[k].depth) {
            a.named[k].used_in = Some(n);
        }
        Ok(())
    }

    /// The write of place `p` of an assignment.
    pub(super) fn alias_assigned(&mut self, p: &Place) -> R<()> {
        if self.aliased.lost.is_empty() {
            return Ok(());
        }
        self.alias_write(p.root(), &Path::of_place(&self.aliases, p))
    }

    /// The places the `inout` argument `x` writes, written once the call
    /// has evaluated all its arguments ([`V::alias_written`]).
    pub(super) fn alias_inout(&mut self, x: &Expr) {
        if self.aliased.lost.is_empty() {
            return;
        }
        let (table, pending) = (&self.aliases, &mut self.aliased.pending);
        written_places(x, &mut |p| {
            if let (Some(root), Some(path)) = (p.place_root(), Path::of_expr(table, p)) {
                pending.push((root, path));
            }
        });
    }

    /// Of the call being walked, the places its `inout` arguments write,
    /// those after `mark`.
    pub(super) fn alias_written(&mut self, mark: usize) -> R<()> {
        for (root, path) in self.aliased.pending.split_off(mark) {
            self.alias_write(root, &path)?;
        }
        Ok(())
    }

    /// A write of `path` through the root `root`: an alias it is not
    /// through, of a place that may overlap, is lost, and one used before
    /// in a loop the write is in would be used lost in the next turn.
    fn alias_write(&mut self, root: LocalId, path: &Path) -> R<()> {
        let a = &mut self.aliased;
        for k in 0..a.named.len() {
            let Some(at) = a.named[k].path.as_ref() else { continue };
            if disjoint(at, path) || a.through(root, k) {
                continue;
            }
            a.lost[k] = true;
            let Named { depth, used_in, .. } = a.named[k];
            if used_in.is_some() && used_in == a.loops.get(depth).copied() {
                let l = a.locals[k].0;
                let msg = format!("the alias {l} used in a loop that then writes a place it names not through it");
                return Err(self.err(Rule::V21, msg));
            }
        }
        Ok(())
    }
}
