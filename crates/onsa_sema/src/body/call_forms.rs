//! The forms of a call that the types stage tells (§6.1, §6.2, §4.5): the
//! syntax and the names cannot say what a name after a value is. A field of
//! a function type called like a method (`s.f(x)`, `s.f!(x)`), and a `[…]`
//! after a field, which is an index of the field (`q.ops[0](x)`) or the type
//! arguments of a method (`v.m[I32](x)`).

use onsa_diag::Edit;
use onsa_syntax::foreign::{self, RowId};

use super::*;
use crate::names::body::Form;
use crate::slot::{Slot, slot_of};

impl<'a> Checker<'a> {
    /// The call `e` of `callee`, `recv.name(…)`, where `recv` has no method
    /// `name`, when a field visible here (§15.1, S-922) answers it, by its
    /// type at the receiver (§6.2, S-923): the E0020 of a function type; of
    /// `!(` also the E0714, or the E0401 of no function type (§5.2, S-811);
    /// an unknown callee of the error type (§18.1). `None`: the field has
    /// nothing to say, and the method is missing.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn field_called(
        &mut self,
        e: ExprId,
        callee: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> Option<R<TyId>> {
        let Ty::Named(d, targs) = self.ty(recv) else { return None };
        let (_, field) = self.a.named_field(d, &name.name).filter(|(_, f)| self.field_visible(d, f))?;
        if let ExprKind::TypeArgs { .. } = self.expr(callee).kind {
            return Some(Err(self.args_after_field(callee)));
        }
        let t = self.a.types.subst(field.ty, &targs);
        let t = self.shallow(t);
        Some(match (self.ty(t), kind) {
            (Ty::Error, _) => self.args_of_unknown_callee(args),
            (Ty::Fn(_), CallKind::Bang) => Err(self.bang_on_value(e, callee)),
            (Ty::Fn(f), _) => {
                let span = self.expr(callee).span;
                let fixes = self.dot_candidate(e, span, &f, args, expected);
                Err(self.diag(foreign::report(RowId::FieldCall, self.text, span, fixes)))
            }
            (_, CallKind::Bang) => Err(self.not_callable(callee, t)),
            _ => return None,
        })
    }

    /// The field `….f` that heads the `[…]` of `callee`: no chain the names
    /// stage stopped at, of an item or a value (`K[0](1)`, its E0020).
    pub(super) fn member_head(&self, callee: ExprId) -> Option<ExprId> {
        let (head, _) = self.ast.indexed(callee)?;
        let member = matches!(self.expr(head).kind, ExprKind::Field { .. });
        (member && !self.names.paths.contains_key(&head)).then_some(head)
    }

    /// The call `e` of `callee`, `….f[…]`, whose head is `head`
    /// ([`Self::member_head`]). One `[…]` after what is no field is on a
    /// method (§4.5); else it reads a field, and an element is called with
    /// `.(`, whatever its type (§6.1, §15.1).
    pub(super) fn check_member_brackets(
        &mut self,
        e: ExprId,
        callee: ExprId,
        head: ExprId,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> R<TyId> {
        let ExprKind::Field { base, name } = &self.expr(head).kind else {
            onsa_diag::internal::bug(Some(self.expr(head).span), "a member that is no field")
        };
        let bt = self.field_base(head, *base)?;
        let one = matches!(self.expr(callee).kind, ExprKind::Index { base, .. } if base == head);
        if one && self.lacks_field(bt, &name.name) {
            return self.check_method_call(e, callee, bt, name, args, expected, kind);
        }
        let t = self.field_type(bt, name)?;
        // A type parameter, which the names stage took as a type there
        // (`self.conv[T](x)`), is no index (as `q.ops[I32](1)`, E0401).
        if let ExprKind::Index { index, .. } = self.expr(callee).kind
            && let Some(PathRes::TypeParam(_)) = self.names.paths.get(&index).filter(|_| one)
        {
            let span = self.expr(index).span;
            return Err(self.err(Code::E0401, span, format!("`{}` is not a value", self.src(span))));
        }
        self.record(head, t);
        let ft = self.elements(callee, head, t)?;
        let ft = self.known_shape(ft, self.expr(callee).span, "callee")?;
        match self.ty(ft) {
            Ty::Error => self.args_of_unknown_callee(args),
            t if kind == CallKind::Plain => Err(self.element_called(e, callee, t, args, expected)),
            _ => self.call_value(e, callee, ft, args, kind),
        }
    }

    /// Whether `t` is a type that surely has no field `name`: what is not
    /// known has its fields read as ever (§18.1).
    fn lacks_field(&self, t: TyId, name: &str) -> bool {
        match self.ty(t) {
            Ty::Error => false,
            Ty::Named(d, _) => match &self.a.def(d).kind {
                DefKind::Struct(_) => self.a.named_field(d, name).is_none() && !self.a.partly_read(d),
                _ => true,
            },
            _ => self.infer.lit_of(&self.a.types, t).is_none(),
        }
    }

    /// The type of `c`, a chain of `[…]` on `head` of the type `t`.
    fn elements(&mut self, c: ExprId, head: ExprId, t: TyId) -> R<TyId> {
        if c == head {
            return Ok(t);
        }
        let &ExprKind::Index { base, index } = &self.expr(c).kind else {
            onsa_diag::internal::bug(Some(self.expr(c).span), "a chain of `[…]` with no head")
        };
        let bt = self.elements(base, head, t)?;
        let el = self.element(c, base, bt, index)?;
        Ok(self.record(c, el))
    }

    /// E0020 for the element `callee` of a field, of the type `t`, called
    /// as `f(x)`, in the words of the row of the names stage (§15.1). Of no
    /// function no candidate: `.(` would leave its E0401 (S-921).
    fn element_called(&mut self, e: ExprId, callee: ExprId, t: Ty, args: &[Arg], expected: Option<TyId>) -> Stop {
        let span = self.expr(callee).span;
        let fixes = match t {
            Ty::Fn(f) => self.dot_candidate(e, span, &f, args, expected),
            _ => Vec::new(),
        };
        self.diag(foreign::report_from(Stage::Types, RowId::IndexedValueCall, self.text, span, fixes))
    }

    /// The candidate `.(` after `span`, the callee of the call `e` of the
    /// type `f`, when it leaves no error of this stage (§18.1): none in a
    /// flow body, where `.(` is an E0806 (§11.2), and none of `args` or of a
    /// place that do not fit `f`.
    fn dot_candidate(&mut self, e: ExprId, span: Span, f: &FnTy, args: &[Arg], expected: Option<TyId>) -> Vec<Fix> {
        let ret = self.shallow(f.ret);
        let dropped = matches!(slot_of(self.ast, self.root, e), Some(p) if matches!(p.outer, Slot::Discarded));
        let place = if dropped { matches!(self.ty(ret), Ty::Unit) } else { self.place_fits(e, ret).is_some() };
        let fits = self.flow.is_none()
            && place
            && expected.is_none_or(|t| self.may_fit(t, ret))
            && self.quietly(|ck| ck.check_args(args, &f.params, e)).is_some();
        fits.then(|| Fix::insert(foreign::CALL_WITH_DOT, span.file, span.end, ".")).into_iter().collect()
    }

    /// E0020 for the `[index]` of the method `md` in `callee` (§4.5).
    pub(super) fn method_brackets(&mut self, callee: ExprId, md: DefId, index: ExprId) -> Stop {
        let fixes = match crate::names::body::own_params(self.a, md)[..] {
            [k] if self.fits_parameter(&self.a.def(md).generics()[k].clone(), index) => self.colons(callee),
            _ => Vec::new(),
        };
        self.brackets_on_method(callee, fixes)
    }

    /// The candidate `::[…]` of `callee`: the `::` before its `[`, an edit
    /// of the syntax that keeps the argument (§4.5).
    fn colons(&self, callee: ExprId) -> Vec<Fix> {
        let ExprKind::Index { base, .. } = self.expr(callee).kind else { return Vec::new() };
        let at = self.expr(base).span;
        vec![Fix::new(foreign::TYPE_ARGS_WITH_COLONS, vec![Edit::insert(at.file, at.end, "::")])]
    }

    /// Whether the `[…]` written `index` reads as the argument of `g`, the
    /// method's only own parameter (a count left is an E0412 of this stage,
    /// S-924), with no other error of this stage in it (§4.5, S-995): one
    /// name or an integer literal of the kind of `g` ([`Form::fits`], the
    /// table of the names stage's `f[…]`), a type that takes no type
    /// arguments, a constant expression of `U32` (not a local, E0417).
    fn fits_parameter(&mut self, g: &GenericDef, index: ExprId) -> bool {
        // Of the type an alias or `Self` names, its arguments are known.
        let (form, known) = match (&self.expr(index).kind, self.names.paths.get(&index)) {
            (ExprKind::Lit(Lit::Int { .. }), _) => (Form::Value, false),
            (_, Some(r)) if crate::names::body::names_only(self.ast, index) => {
                (Form::of_record(self.a, r), matches!(r, PathRes::Item { owner: Some(_), .. }))
            }
            _ => return false,
        };
        let constant = match g.kind {
            GenericKind::Effect => return false,
            ref k => matches!(k, GenericKind::Const(_)),
        };
        match form {
            _ if !form.fits(Some(constant)) => false,
            Form::Type(Some(e)) => known || crate::sig::declared_params(self.a, e).is_some_and(|ps| ps.is_empty()),
            Form::Type(None) => true,
            _ => self.const_expr(index).is_ok(),
        }
    }

    /// The E0020 of a `[…]` on a method, with `fixes` (§4.5, S-924).
    pub(super) fn brackets_on_method(&mut self, callee: ExprId, fixes: Vec<Fix>) -> Stop {
        let span = self.expr(callee).span;
        self.diag(foreign::report(RowId::TypeArgsMethodSquare, self.text, span, fixes))
    }

    /// E0401 for the value `callee` of the type `t`, no function (§15.1).
    pub(super) fn not_callable(&mut self, callee: ExprId, t: TyId) -> Stop {
        let shown = self.described(t);
        self.err(Code::E0401, self.expr(callee).span, format!("{shown} is not a function and cannot be called"))
    }

    /// E0714 for the call `e` with `!(` of the function value `callee`: the
    /// `!` comes right after it (`h!(`, §2.6), and `.(` calls it (§5.2, S-812).
    pub(super) fn bang_on_value(&mut self, e: ExprId, callee: ExprId) -> Stop {
        let span = self.expr(e).span;
        let at = self.expr(callee).span.end;
        let dot = Edit::replace(Span::new(span.file, at, at + 1), ".");
        self.diag(
            Diagnostic::new(Stage::Types, Code::E0714, span, BANG_ON_NO_INOUT_SELF)
                .with_found(self.src(span))
                .with_fix(Fix::new(foreign::CALL_WITH_DOT, vec![dot])),
        )
    }
}
