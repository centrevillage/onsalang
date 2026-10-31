//! The calls of a body (§6.1, §15.1, §2.6): the form of a call that the
//! names of its callee decide, read from the form of the callee in the AST
//! and the records of the walk (A1): (i) a chain of names (`f(x)`,
//! `inc.(1)`), (ii) a chain of names with `[…]` after it (`ops[i](x)`),
//! (iii) anything else, whose form the syntax stage or the types stage
//! decides. A wrong form is the E0020 of a row of `onsa_syntax::foreign`
//! (`value_call`, `item_dot_call`, `indexed_value_call`), which stops the
//! walk (§18.1).

use onsa_diag::{Diagnostic, Fix, Span};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind};
use onsa_syntax::foreign::{self, RowId};

use super::kinds::value_call_fix;
use super::paths::Place;
use super::{Fail, PathRes, W, Walker};
use crate::Analysis;
use crate::def::DefKind;
use crate::flow_names::FlowBuiltin;
use crate::resolve::{Builtin, Entity, NameKind};

/// What the record of a callee is, as the forms of a call read it: the one
/// table of the values and the items of a call (§15.1, §6.1; A6, D-15).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Called {
    /// A value that is no unit variant: a local, a const parameter, a
    /// constant, a constant of a builtin type.
    Value,
    /// A unit variant (`None`, `E.A`), whose `E.A()` is the E0412 of the
    /// types stage (S-514).
    UnitVariant,
    /// What is called as `f(x)`: a function, an associated function, a
    /// function of a namespace, a variant with elements, an associated
    /// function of a builtin type.
    Item,
    /// Anything else (a flow, a builtin name of a flow).
    Other,
}

impl Called {
    /// A value, a unit variant or not.
    pub(super) fn is_value(self) -> bool {
        matches!(self, Called::Value | Called::UnitVariant)
    }
}

/// Whether the entity is a variant with no elements.
fn unit_variant(a: &Analysis, e: Entity) -> bool {
    match e {
        Entity::Variant(d, i) => a.def(d).as_enum().is_some_and(|en| en.variants[i as usize].fields.is_empty()),
        Entity::Builtin(b) => b == Builtin::None,
        _ => false,
    }
}

impl Walker<'_> {
    /// The call `e` (§6.1): its callee, the form of the call that the
    /// callee decides, then its arguments.
    pub(super) fn call(&mut self, e: ExprId, callee: ExprId, kind: CallKind, args: &[Arg]) -> W {
        let ast = self.ast;
        let place = match kind {
            CallKind::Value { .. } => Place::DotCallee,
            CallKind::Flow => Place::Instance,
            _ => Place::Callee(e),
        };
        match self.indexed(callee) {
            Some((head, indices)) if place != Place::DotCallee => self.indexed_callee(callee, kind, head, &indices)?,
            _ => {
                self.name_at(callee, place)?;
                self.form(callee, kind)?;
            }
        }
        if let (CallKind::Flow, Some(&PathRes::Item { entity: Entity::Def(d) | Entity::Member(d), .. })) =
            (kind, self.out.paths.get(&callee))
            && matches!(self.a.def(d).kind, DefKind::Flow(_))
        {
            self.out.instances.push((d, ast.expr(callee).span));
        }
        // The constant of a delay (`delay~(x, N)`, §11.4).
        let constant = match self.out.paths.get(&callee) {
            Some(PathRes::FlowBuiltin(FlowBuiltin::Delay(d))) => d.const_index(),
            _ => None,
        };
        (0..).zip(args).try_for_each(|(k, a)| match Some(k) == constant {
            true => self.const_expr(a.expr),
            false => self.expr(a.expr),
        })
    }

    /// What the record of a callee is ([`Called`]).
    pub(super) fn called(&self, r: &PathRes) -> Called {
        let a = self.a;
        match r {
            PathRes::Local(_) | PathRes::ConstParam(_) => Called::Value,
            PathRes::BuiltinAssoc { ty, name, .. } if crate::builtin::has_assoc_const(&a.types, *ty, name) => {
                Called::Value
            }
            PathRes::BuiltinAssoc { .. } => Called::Item,
            PathRes::Item { entity, .. } => match NameKind::of(*entity, &a.defs) {
                Some(NameKind::Function) => Called::Item,
                Some(NameKind::Constant) => Called::Value,
                Some(NameKind::Variant) if unit_variant(a, *entity) => Called::UnitVariant,
                Some(NameKind::Variant) => Called::Item,
                _ => Called::Other,
            },
            _ => Called::Other,
        }
    }

    /// The form (i) of the call of the chain of names `callee`: a value
    /// called as `f(x)` is the E0020 of the row `value_call` (a constant is
    /// found as the chain resolves, `kinds.rs`; a unit variant is the E0412
    /// of the types stage, S-514), and an item called with `.(` the E0020 of
    /// the row `item_dot_call` (a flow is no value there, E0308, S-816). A
    /// value called with `!(` is the types stage's (E0714, E0401, S-812).
    fn form(&mut self, callee: ExprId, kind: CallKind) -> W {
        let Some(r) = self.out.paths.get(&callee) else { return Ok(()) };
        let span = self.ast.expr(callee).span;
        let d = match (kind, self.called(r)) {
            (CallKind::Plain, Called::Value) => self.call_form(RowId::ValueCall, span, value_call_fix(span)),
            (CallKind::Value { dot }, Called::Item) => {
                // Up to the end of the `.`, which may start the next line (§2.5).
                let fix = Fix::delete("call the item without `.`", Span { start: span.end, ..dot });
                self.call_form(RowId::ItemDotCall, span, fix)
            }
            _ => None,
        };
        d.map_or(Ok(()), |d| Err(self.fail(Fail::Report(d))))
    }

    /// The E0020 of the row `row` of a call at `span`, with the candidate
    /// `fix`. In a flow body the form a candidate writes is an E0806 (§11.2,
    /// S-811): a value called as `f(x)` has no candidate there, and an item
    /// called with `.(` is the E0806 of the flow stage (its candidate is
    /// W7-04's). The one place of that judgment for the rows of a call.
    pub(super) fn call_form(&self, row: RowId, span: Span, fix: Fix) -> Option<Diagnostic> {
        match (self.flow, row) {
            (false, _) => Some(foreign::report(row, self.text, span, vec![fix])),
            (true, RowId::ItemDotCall) => None,
            (true, _) => Some(foreign::report(row, self.text, span, Vec::new())),
        }
    }

    /// The head of the callee `c` of `ops[i](x)` (a chain of names: the form
    /// (ii)) and the indices after it, in the order of the text; none when
    /// `c` is no `[…]`.
    fn indexed(&self, c: ExprId) -> Option<(ExprId, Vec<ExprId>)> {
        let mut indices = Vec::new();
        let mut head = c;
        while let ExprKind::Index { base, index } = &self.ast.expr(head).kind {
            indices.push(*index);
            head = *base;
        }
        indices.reverse();
        (!indices.is_empty()).then_some((head, indices))
    }

    /// The callee `ops[i]` whose head is `head`: a value there (the form
    /// (ii), a chain of names) called as `f(x)` is the E0020 of the row
    /// `indexed_value_call`, whose candidate calls it with `.(`; an item or
    /// a type is as it was (its type arguments `inc::[I32](x)` from W5-10).
    /// One `[…]` after a field (`p.m[I32](1)`) is the type arguments of a
    /// method or an index, which the types stage tells apart (§4.5).
    fn indexed_callee(&mut self, callee: ExprId, kind: CallKind, head: ExprId, indices: &[ExprId]) -> W {
        self.name_at(head, Place::Value)?;
        let span = self.ast.expr(callee).span;
        let fix = Fix::insert("call the function value with `.(`", span.file, span.end, ".");
        if kind == CallKind::Plain
            && self.out.paths.get(&head).is_some_and(|r| self.called(r).is_value())
            && let Some(d) = self.call_form(RowId::IndexedValueCall, span, fix)
        {
            return Err(self.fail(Fail::Report(d)));
        }
        let typed = indices.len() == 1 && matches!(self.ast.expr(head).kind, ExprKind::Field { .. });
        indices.iter().try_for_each(|&i| match typed {
            true => self.name_at(i, Place::TypeOrValue),
            false => self.expr(i),
        })
    }
}
