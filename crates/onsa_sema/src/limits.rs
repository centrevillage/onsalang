//! The limits of the types a body makes (spec §4.4, §4.7; S-264, S-849).
//!
//! Each expression's type is measured when it is recorded ([`Checker::record_within`]),
//! the bound variables followed ([`Infer::measure`]): over the limits, it is E0422 at
//! the expression, which made it. A type within them that holds an open variable may
//! grow when a later binding decides it, so it waits as a [`DeferredKind::Limit`] item.
//! Such an item is measured again only when a variable it reaches is bound
//! ([`Checker::wake`], as every deferred item), so that a body with many open types
//! and many unrelated bindings stays linear (W2-06/b).

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::ExprId;

use crate::body::{Checker, R};
use crate::deferred::{Deferred, DeferredKind, Look, decided_at};
use crate::infer::{Measured, Walk};
use crate::ty::{LIMIT_RULE, TyId};

impl<'a> Checker<'a> {
    /// Record `t` as the type of `e`, which made it, within the limits of §4.4
    /// (S-264): over them, E0422 at `e`, which then has the error type, so
    /// that nothing walks the large type, unless a binding of this statement
    /// made an earlier type over them first (S-849). A type with the error
    /// type in it is not judged (§18.1).
    pub(crate) fn record_within(&mut self, e: ExprId, t: TyId) -> R<TyId> {
        let m = self.infer.measure(&self.a.types, t, &mut Walk::default());
        if !m.measure.over_limit() {
            if m.waits && self.waits.limit_types.insert(t) {
                let item = self.deferred_item(self.expr(e).span, t, DeferredKind::Limit);
                self.wait(item);
            }
            return Ok(self.record(e, t));
        }
        let err = self.a.types.error();
        self.record(e, err);
        if m.error {
            return Ok(err);
        }
        let d = match self.wake() {
            Some((_, d)) => d,
            None => self.limit_error(self.expr(e).span, m),
        };
        Err(self.diag(d))
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

    /// The item `i`, a limit that a binding woke, measured again in `walk`
    /// (the bindings do not change while the woken ones are measured): over
    /// the limits, it fails with its order; it waits on while an open
    /// variable is left in it.
    pub(crate) fn measure_again(&mut self, i: usize, walk: &mut Walk) -> Option<(u32, Diagnostic)> {
        let item = self.waits.items[i].take()?;
        self.waits.looked = self.waits.looked.saturating_add(1);
        let m = self.infer.measure(&self.a.types, item.ty, walk);
        if m.measure.over_limit() && !m.error {
            return Some((item.seq, self.limit_fail(&item, m)));
        }
        if m.waits && !m.measure.over_limit() {
            self.waits.items[i] = Some(item);
        }
        None
    }
}
