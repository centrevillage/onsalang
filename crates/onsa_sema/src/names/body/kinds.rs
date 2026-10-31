//! The kinds of the names of a body (§15.1, §7, S-103, S-713, S-719,
//! S-721): the E0308 of a name the walk finds at a place that does not take
//! its kind (the error is [`ResolveError::Kind`], the one wording of it, which
//! the types of a signature give too), of a method named through its type,
//! of a `.` after a name that is no namespace, and the E0020 of a constant
//! called (the row `value_call`).

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{CallKind, ExprId, ExprKind, Ident, Lit};
use onsa_syntax::foreign::{self, RowId};

use super::paths::{Place, span_of};
use super::{Fail, Walker};
use crate::names::{BuiltinMember, PathEnd};
use crate::resolve::{Callee, Entity, NameKind, ResolveError, no_members};

/// The call whose callee a method named through its type is at `place`
/// (none at the place of a value, where it is no value, and in the `[…]`
/// of `p.m[P.get](1)`, no type and no value either); the callee of an
/// instance is the flow stage's (W4-12).
fn method_call_at(place: Place) -> Option<Option<ExprId>> {
    match place {
        Place::Callee(call) => Some(Some(call)),
        Place::Value | Place::DotCallee | Place::TypeOrValue => Some(None),
        Place::Instance => None,
    }
}

/// What a path of a pattern or a struct literal names (§7, §15.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Want {
    /// A struct literal and a struct pattern.
    Type,
    /// The path of a pattern of a variant, with fields or not.
    VariantOrConstant,
}

impl Walker<'_> {
    /// E0308 for a `.` after a name of the kind `kind`, neither a value nor
    /// a namespace (a trait, a kind constraint, a handler; §15.1, S-713 (e),
    /// S-719, S-721), with no candidate; after a trait or a kind constraint,
    /// a note shows where a method and an associated function are named.
    pub(super) fn no_namespace(&self, segs: &[&Ident], kind: NameKind) -> Diagnostic {
        let (name, member) = (segs[segs.len() - 2], segs[segs.len() - 1]);
        let span = span_of(segs);
        let d = no_members(&name.name, kind, span).with_found(self.src(span));
        if !matches!(kind, NameKind::Trait | NameKind::KindConstraint) {
            return d;
        }
        d.with_note(
            name.span,
            format!(
                "a method is called on a value (`x.{}()`), and an associated function or constant is named after \
                 a type (`F32.from_bits(b)`, §6.6)",
                member.name
            ),
        )
    }

    /// E0308 when the name `segs` of the kind `kind` is no value at the place
    /// of a value, and neither a value nor a flow at the callee of a call
    /// (the call of a flow is W4-12's, E0821); the callee of an instance is
    /// the flow stage's.
    pub(super) fn kind_fail(&self, kind: NameKind, segs: &[&Ident], place: Place) -> Option<Fail> {
        let want = match place {
            Place::Value | Place::DotCallee => "a value",
            Place::Callee(call) => match kind.at_callee() {
                Callee::Called => return None,
                // `K!(x)`: a value that is no function, the E0401 of the
                // types stage (§5.2, S-812, R-341).
                Callee::Value if self.bang(call) => return None,
                Callee::Value => return self.value_called(segs),
                Callee::NoValue => "a function",
            },
            Place::Instance | Place::TypeOrValue => return None,
        };
        (!kind.is_value()).then(|| self.kind_error(kind, segs, want))
    }

    /// E0308 for the name `segs` of the kind `kind`, at a place that takes
    /// `want` (§15.1).
    fn kind_error(&self, kind: NameKind, segs: &[&Ident], want: &'static str) -> Fail {
        let span = span_of(segs);
        Fail::Report(ResolveError::Kind { shown: self.src(span), span, kind, want }.into_diagnostic())
    }

    /// E0308 for a method `cur` named through its type (§15.1): called in
    /// the function form (`P.get(p)`, with the candidate of
    /// [`Self::method_call`]), or as a value (`let f = P.get`, S-205).
    pub(super) fn method_form(&self, cur: Entity, segs: &[&Ident], place: Place) -> Option<Fail> {
        let call = method_call_at(place)?;
        let bang = PathEnd::Entity(cur).method(self.a)?;
        Some(Fail::Report(self.method_call(call, segs, bang)))
    }

    /// The error of the last name of `segs` after the builtin type `of`, which
    /// is no associated function or constant of it there: a method of it
    /// called in the function form (`Str.len(s)`) or named as a value
    /// (`Str.len`), E0308, or an associated constant called (`F32.PI()`, a
    /// value called with `(…)`, E0020; §6.1, §15.1).
    pub(super) fn builtin_called(&self, of: Entity, segs: &[&Ident], place: Place) -> Option<Fail> {
        let call = method_call_at(place)?;
        match crate::names::builtin_member(self.a, of, &segs[segs.len() - 1].name)? {
            BuiltinMember::Method { bang } => Some(Fail::Report(self.method_call(call, segs, bang))),
            BuiltinMember::Constant if call.is_some_and(|c| !self.bang(c)) => self.value_called(segs),
            BuiltinMember::Constant | BuiltinMember::Function => None,
        }
    }

    /// E0020 for the value `segs` called as `x(...)` ([`value_called`],
    /// [`Self::call_form`]).
    pub(super) fn value_called(&self, segs: &[&Ident]) -> Option<Fail> {
        let span = span_of(segs);
        self.call_form(RowId::ValueCall, span, value_call_fix(span)).map(Fail::Report)
    }

    /// Whether the call `call` is `f!(x)`.
    pub(super) fn bang(&self, call: ExprId) -> bool {
        matches!(self.ast.expr(call).kind, ExprKind::Call { kind: CallKind::Bang, .. })
    }

    /// E0308 for the method `segs` named through its type (§15.1), at the
    /// callee of `call` or as a value (none). The candidate calls it on the
    /// first argument (`p.get()`, `b.m!(x)` for an `inout self` method, with
    /// the `!` added or taken off as the receiver is declared); none with no
    /// argument or no call.
    fn method_call(&self, call: Option<ExprId>, segs: &[&Ident], bang: bool) -> Diagnostic {
        let span = span_of(segs);
        let name = &segs[segs.len() - 1].name;
        let d = method_named(self.src(span), name, span);
        let ast = self.ast;
        let Some(call) = call else { return d };
        let ExprKind::Call { args, kind, .. } = &ast.expr(call).kind else { return d };
        let Some((first, rest)) = args.split_first() else { return d };
        let recv = self.src(ast.expr(first.expr).span);
        // What `.` follows with the same reading (a number literal does not:
        // `1.len` is no name after it).
        let postfix = matches!(
            ast.expr(first.expr).kind,
            ExprKind::Lit(Lit::Str(_) | Lit::Char(_) | Lit::Bool(_))
                | ExprKind::Path(_)
                | ExprKind::Paren(_)
                | ExprKind::Tuple(_)
                | ExprKind::Array(_)
                | ExprKind::Call { .. }
                | ExprKind::Field { .. }
                | ExprKind::TupleIndex { .. }
                | ExprKind::Index { .. }
        );
        let recv = if postfix { recv } else { format!("({recv})") };
        // The type becomes the receiver, and the first argument goes (the
        // edits change only what changes, §18.1, S-251).
        let (ty, last) = (span_of(&segs[..segs.len() - 1]), segs[segs.len() - 1].span);
        // Up to the next argument, or to the `)` past a trailing `,`.
        let end = rest.first().map_or(ast.expr(call).span.end - 1, |a| a.span.start);
        // A receiver that starts with the type (`P.new(x)` of `P.get(P.new(x))`)
        // keeps it.
        let kept =
            recv.strip_prefix(&self.src(ty)).filter(|r| !r.starts_with(|c: char| c.is_alphanumeric() || c == '_'));
        let mut edits = vec![Edit::replace(Span::new(span.file, first.span.start, end), "")];
        match kept {
            Some("") => {}
            Some(r) => edits.push(Edit::replace(Span { start: ty.end, ..ty }, r)),
            None => edits.push(Edit::replace(ty, recv)),
        }
        match (bang, *kind == CallKind::Bang) {
            (true, false) => edits.push(Edit::replace(Span::new(span.file, last.end, last.end), "!")),
            (false, true) => edits.push(Edit::replace(Span::new(span.file, last.end, last.end + 1), "")),
            _ => {}
        }
        // The title is one line: the receiver may span lines (§18.1).
        d.with_fix(Fix::new(format!("call `{name}` on the first argument"), edits))
    }

    /// E0308 when the name `segs` of the kind `kind` is not what a path of a
    /// pattern or a struct literal takes (`want`).
    pub(super) fn want(&self, kind: NameKind, segs: &[&Ident], want: Want) -> Option<Fail> {
        let (takes, noun) = match want {
            Want::Type => (kind == NameKind::Type, "a type"),
            Want::VariantOrConstant => {
                (matches!(kind, NameKind::Variant | NameKind::Constant), "a variant or a constant")
            }
        };
        (!takes).then(|| self.kind_error(kind, segs, noun))
    }
}

/// E0020 for the value at `span` of `text` called as `x(...)` (a constant,
/// §15.1, the row `value_call`); the candidate calls it with `.(` (§6.1).
/// The one form of a body and a constant expression.
pub(crate) fn value_called(text: &str, span: Span) -> Diagnostic {
    foreign::report(RowId::ValueCall, text, span, vec![value_call_fix(span)])
}

/// The candidate of the E0020 of a value at `span` called as `x(...)`: `.(`.
pub(super) fn value_call_fix(span: Span) -> Fix {
    Fix::new("call the function value with `.(`", vec![Edit::replace(Span { start: span.end, ..span }, ".")])
}

/// E0308 for the method `shown`, whose name is `name`, named through its
/// type at `span` (§15.1), with no candidate; a note says that a method is
/// only called (§6.1, S-205).
pub(crate) fn method_named(shown: String, name: &str, span: Span) -> Diagnostic {
    let msg = format!("`{shown}` is a method, which is called on a value (`value.{name}(…)`, §6.2, §15.1)");
    let rule = "a method is only called, on a value; it is no value of its own (§6.1)";
    Diagnostic::new(Stage::Names, Code::E0308, span, msg).with_found(shown).with_rule(rule)
}
