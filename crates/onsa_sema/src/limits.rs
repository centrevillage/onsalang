//! The limits of the types a body makes (spec §4.4, §4.7; S-264, S-849).
//!
//! Each expression's type is measured when it is recorded ([`Checker::record_within`]),
//! the bound variables followed ([`Infer::measure`]): over the limits, it is E0422 at
//! the expression, which made it. A type within them that holds an open variable may
//! grow when a later binding decides it, so it waits as a [`DeferredKind::Limit`] item.
//! Such an item is measured again only when a variable it reaches is bound, so that a
//! body with many open types and many unrelated bindings stays linear (W2-06/b).

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::ExprId;

use crate::body::{Checker, R};
use crate::deferred::{Deferred, DeferredKind, Look, decided_at};
use crate::infer::{Measured, Walk};
use crate::ty::{LIMIT_RULE, Ty, TyId};

/// The [`DeferredKind::Limit`] items of a body.
#[derive(Debug, Default)]
pub(crate) struct Limits {
    /// The items in the order they were made; `None` once done.
    pub(crate) items: Vec<Option<Deferred>>,
    /// The types that have an item: one item a type.
    types: HashSet<TyId>,
    /// For each open variable, the items whose type reaches it.
    waiting: HashMap<u32, Vec<usize>>,
    /// The bindings looked at ([`crate::infer::Infer::generation`]).
    seen: u32,
    /// The items measured again so far, which stays linear in the body (a test counts them).
    pub(crate) measured: u32,
}

#[cfg(test)]
thread_local! {
    /// The items measured again by the bodies checked on this thread ([`Limits::measured`]).
    pub(crate) static MEASURED: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

impl<'a> Checker<'a> {
    /// Record `t` as the type of `e`, which made it, within the limits of §4.4
    /// (S-264): over them, E0422 at `e`, which then has the error type, so
    /// that nothing walks the large type, unless a binding of this statement
    /// made an earlier type over them first (S-849). A type with the error
    /// type in it is not judged (§18.1).
    pub(crate) fn record_within(&mut self, e: ExprId, t: TyId) -> R<TyId> {
        let mut walk = Walk::default();
        let m = self.infer.measure(&self.a.types, t, &mut walk);
        if !m.measure.over_limit() {
            if m.waits && self.limits.types.insert(t) {
                let item = self.deferred_item(self.expr(e).span, t, DeferredKind::Limit);
                self.wait_on(self.limits.items.len(), &walk.vars);
                self.limits.items.push(Some(item));
            }
            return Ok(self.record(e, t));
        }
        let err = self.a.types.error();
        self.record(e, err);
        if m.error {
            return Ok(err);
        }
        let d = match self.wake_limits() {
            Some((_, d)) => d,
            None => self.limit_error(self.expr(e).span, m),
        };
        Err(self.diag(d))
    }

    fn wait_on(&mut self, item: usize, vars: &[u32]) {
        for &v in vars {
            self.limits.waiting.entry(v).or_default().push(item);
        }
    }

    fn limit_error(&self, span: Span, m: Measured) -> Diagnostic {
        Diagnostic::new(Stage::Types, Code::E0422, span, m.measure.limit_message())
            .with_found(self.src(span))
            .with_rule(LIMIT_RULE)
    }

    /// The E0422 of `item`, with the expression that decided a part of its type.
    fn limit_fail(&self, item: &Deferred, m: Measured) -> Diagnostic {
        let d = self.limit_error(item.span, m);
        match decided_at(&self.infer.decided_by(&self.a.types, item.ty)) {
            Some((span, why)) => d.with_note(span, format!("a part of the type was decided here{why}")),
            None => d,
        }
    }

    /// An item at the end of the body: the measure only grows (S-849).
    pub(crate) fn look_limit(&mut self, item: &Deferred) -> Look {
        let m = self.infer.measure(&self.a.types, item.ty, &mut Walk::default());
        if m.measure.over_limit() && !m.error { Look::Fail(self.limit_fail(item, m)) } else { Look::Done }
    }

    /// The items that reach a variable bound since the last look, measured again:
    /// the first made of those over the limits fails, with its order. Each item
    /// then waits on the open variables the bound ones reach.
    pub(crate) fn wake_limits(&mut self) -> Option<(u32, Diagnostic)> {
        let bound = self.infer.bound_since(self.limits.seen).to_vec();
        self.limits.seen = self.infer.generation();
        let mut woken = Vec::new();
        for v in bound {
            let Some(items) = self.limits.waiting.remove(&v) else { continue };
            let mut walk = Walk::default();
            if let Some(t) = self.a.types.find(&Ty::Var(v)) {
                self.infer.measure(&self.a.types, t, &mut walk);
            }
            for &i in &items {
                self.wait_on(i, &walk.vars);
            }
            woken.extend(items);
        }
        woken.sort_unstable();
        woken.dedup();
        // One walk for all: the bindings do not change while they are measured.
        let mut walk = Walk::default();
        for i in woken {
            let Some(item) = self.limits.items[i].take() else { continue };
            self.limits.measured = self.limits.measured.saturating_add(1);
            let m = self.infer.measure(&self.a.types, item.ty, &mut walk);
            if m.measure.over_limit() && !m.error {
                return Some((item.seq, self.limit_fail(&item, m)));
            }
            if m.waits && !m.measure.over_limit() {
                self.limits.items[i] = Some(item);
            }
        }
        None
    }
}
