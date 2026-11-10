//! The calls of a body (§6.1, §15.1, §2.6): the form of a call that the
//! names of its callee decide, read from the form of the callee in the AST
//! and the records of the walk (A1): (i) a chain of names (`f(x)`,
//! `inc.(1)`), (ii) a chain of names with `[…]` after it (`ops[i](x)`),
//! (iii) anything else, whose form the syntax stage or the types stage
//! decides. A wrong form is the E0020 of a row of `onsa_syntax::foreign`
//! (`value_call`, `item_dot_call`, `indexed_value_call`, and
//! `type_args_square` of a `[…]` after an item or a type, called or not),
//! which stops the walk (§18.1).

use onsa_diag::internal::bug;
use onsa_diag::{Diagnostic, Fix, Span};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind, Ident};
use onsa_syntax::foreign::{self, CALL_WITH_DOT, RowId, TYPE_ARGS_WITH_COLONS};

use super::kinds::value_call_fix;
use super::paths::{Place, path_of};
use super::type_args::Form;
use super::{Fail, PathRes, W, Walker};
use crate::Analysis;
use crate::DefId;
use crate::flow_names::FlowBuiltin;
use crate::resolve::{Callee, Entity, NameKind};

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
    /// A flow ([`Callee::Flow`]), called with `~` (§2.6).
    Flow(DefId),
    /// Anything else (a type, a module, a builtin name of a flow).
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
        _ => false,
    }
}

impl Walker<'_> {
    /// The call `e` (§6.1): its callee, the form of the call that the
    /// callee decides, then its arguments.
    pub(super) fn call(&mut self, e: ExprId, callee: ExprId, kind: CallKind, args: &[Arg]) -> W {
        if !self.flow {
            self.call_outside(e, callee, kind, false)?;
        }
        let place = match kind {
            CallKind::Value { .. } => Place::DotCallee,
            CallKind::Flow => Place::Instance(e),
            _ => Place::Callee(e),
        };
        match self.ast.indexed(callee) {
            Some((head, indices)) if place != Place::DotCallee => self.indexed_callee(callee, kind, head, &indices)?,
            _ => {
                self.name_at(callee, place)?;
                self.form(callee, kind)?;
            }
        }
        // The `~` after the names of the callee, before its arguments (R-286).
        match self.flow {
            true => self.flow_mark(e, callee, kind, args)?,
            false => self.call_outside(e, callee, kind, true)?,
        }
        // The constant of a delay (`delay~(x, N)`, §11.4).
        let constant = match self.out.paths.get(&super::named(self.ast, callee)) {
            Some(PathRes::FlowBuiltin(FlowBuiltin::Delay(d))) => d.const_index(),
            _ => None,
        };
        (0..).zip(args).try_for_each(|(k, a)| match Some(k) == constant {
            true => self.const_expr(a.expr),
            false => self.expr(a.expr),
        })
    }

    /// What the record of a callee is ([`Called`]): of the kind of its name
    /// at the callee ([`NameKind::at_callee`]); a local is a value.
    pub(super) fn called(&self, r: &PathRes) -> Called {
        let a = self.a;
        let (kind, entity) = match r {
            PathRes::Local(_) => return Called::Value,
            PathRes::ConstParam(_) => (NameKind::ConstParam, None),
            PathRes::Item { entity, .. } => match NameKind::of(*entity, &a.defs) {
                Some(k) => (k, Some(*entity)),
                None => return Called::Other,
            },
            PathRes::BoundMember { member, .. } => match NameKind::of(Entity::Member(*member), &a.defs) {
                Some(k) => (k, None),
                None => return Called::Other,
            },
            _ => return Called::Other,
        };
        match (kind.at_callee(false), entity) {
            (Callee::Flow, Some(Entity::Def(d) | Entity::Member(d))) => Called::Flow(d),
            (Callee::Value, _) => Called::Value,
            (Callee::Called, Some(e)) if kind == NameKind::Variant && unit_variant(a, e) => Called::UnitVariant,
            (Callee::Called, _) => Called::Item,
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
        let Some(r) = self.out.paths.get(&super::named(self.ast, callee)) else { return Ok(()) };
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

    /// The callee `ops[i]` whose head is `head`: after an item or a type,
    /// [`Self::square`]; a value there (the form (ii), a chain of names)
    /// called as `f(x)` is the E0020 of the row `indexed_value_call`, whose
    /// candidate calls it with `.(`, none when its indices, walked first,
    /// have an error of the names stage that the candidate would leave
    /// (`g[F32](x)`, §18.1, S-974). One `[…]` after a field (`p.m[I32](1)`)
    /// is the type arguments of a method or an index, which the types stage
    /// tells apart (§4.5).
    fn indexed_callee(&mut self, callee: ExprId, kind: CallKind, head: ExprId, indices: &[ExprId]) -> W {
        self.square(callee, (head, indices), Square::Called)?;
        let span = self.ast.expr(callee).span;
        if kind == CallKind::Plain && self.out.paths.get(&head).is_some_and(|r| self.called(r).is_value()) {
            let left = self.exprs(indices.iter().copied()).is_err() && matches!(self.failure, Some(Fail::Report(_)));
            let fix = Fix::insert(CALL_WITH_DOT, span.file, span.end, ".");
            let d = match left {
                true => Some(foreign::report(RowId::IndexedValueCall, self.text, span, Vec::new())),
                false => self.call_form(RowId::IndexedValueCall, span, fix),
            };
            if let Some(d) = d {
                return Err(self.fail(Fail::Report(d)));
            }
        }
        let typed = indices.len() == 1 && matches!(self.ast.expr(head).kind, ExprKind::Field { .. });
        indices.iter().try_for_each(|&i| match typed {
            true => self.name_at(i, Place::TypeOrValue),
            false => self.expr(i),
        })
    }

    /// The `[…]` `e` that is no callee, at `at` ([`Self::square`]), then its indices.
    pub(super) fn index(&mut self, e: ExprId, at: Square) -> W {
        let (head, indices) = self.ast.indexed(e).unwrap_or_else(|| bug(Some(self.ast.expr(e).span), "no `[…]`"));
        self.square(e, (head, &indices), at)?;
        self.exprs(indices)
    }

    /// The `[…]` `x` after `head` at `at`, and the names of `head`: after a
    /// chain of names that ends at an item called as `f(x)` or at a type,
    /// the E0020 of the row `type_args_square` (§4.5, §6.1, S-256, R-179),
    /// up to its last `]`. Its candidate puts `::` before its `[`, when there
    /// is one `[…]` ([`Self::fits_square`]) and it makes no other error of
    /// the names stage: a type only before a member (`Buf::[F32].zeroed(4)`,
    /// not called or a value), an item not called with `.(` (S-974). A type
    /// is read by its form, no value there (its E0308).
    fn square(&mut self, x: ExprId, (head, indices): (ExprId, &[ExprId]), at: Square) -> W {
        let names = self.chain(head).filter(|(_, lists)| lists.is_empty()).map(|(c, _)| c);
        let names: Vec<&Ident> = names.iter().flatten().map(|&(_, n)| n).collect();
        let Some(&last) = names.last() else { return self.name_at(head, Place::Value) };
        let (r, takes) = match self.form_of(&path_of(&names)) {
            Form::Type(Some(entity)) => (PathRes::Item { entity, owner: None }, at == Square::Member),
            Form::Type(None) => (self.heading(last).unwrap_or_else(|| bug(None, "no parameter")), at == Square::Member),
            _ => {
                self.name_at(head, Place::Value)?;
                match self.out.paths.get(&head) {
                    // Not one whose heading a syntax error cut (S-59): no diagnostic.
                    Some(r) if self.called(r) == Called::Item && !self.cut(r, last) => {
                        (r.clone(), at != Square::DotCalled)
                    }
                    _ => return Ok(()),
                }
            }
        };
        let fits = takes && indices.len() == 1 && self.fits_square(&r, last, indices[0]);
        let head = self.ast.expr(head).span;
        let fixes = fits.then(|| Fix::insert(TYPE_ARGS_WITH_COLONS, head.file, head.end, "::")).into_iter().collect();
        let span = Span { start: head.end, ..self.ast.expr(x).span };
        Err(self.fail(Fail::Report(foreign::report(RowId::TypeArgsSquare, self.text, span, fixes))))
    }
}

/// Where a `[…]` after a chain of names is ([`Walker::square`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Square {
    /// The callee of `f(x)`, `f!(x)`, `f~(x)`.
    Called,
    /// The callee of `f.(x)`.
    DotCalled,
    /// Before a member (`Buf[F32].zeroed`).
    Member,
    Value,
}
