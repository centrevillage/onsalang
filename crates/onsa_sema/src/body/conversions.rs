//! The conversions that are associated functions of the number types
//! (`F32.round_from`, `I8.narrow_from`, §3.3): a pair of concrete types `as`
//! converts has none (E0413, S-231). A use is judged when its source is
//! decided, which a later statement may do (§4.7). A call rejected at once
//! has the candidate of the `as` form, or a note of it where none keeps the
//! promise of §18.1; a use rejected later or as a value has the note.

use onsa_diag::Edit;
use onsa_syntax::ast::{OperandPlace, TypeId, TypeKind};

use super::slot::{Form, Slot, opens_a_brace};
use super::*;
use crate::cast::{Instead, cast_instead};
use crate::lang;
use crate::prim::NARROW_FROM;

/// The call a candidate replaces: the expression and the type expected of it
/// (§4.7).
pub(super) struct ConversionCall {
    pub e: ExprId,
    pub expected: Option<TyId>,
}

impl<'a> Checker<'a> {
    /// The E0411 of `inner as ty` at `span`, a conversion from `from` to
    /// `to` that `as` does not write (§3.3). Only the number types have
    /// another way to convert, so only their text names one (`Char`, R-257).
    /// A candidate keeps the operand as it is written and the target as `ty`
    /// writes it. A type parameter as the target has none yet, other than the
    /// same type (`T.round_from`, W5-05 U5).
    pub(super) fn cast_error(&mut self, span: Span, inner: ExprId, ty: TypeId, from: TyId, to: TyId) -> Diagnostic {
        let (source, target) = (self.display(from), self.display(to));
        let (f, t) = (self.ty(from), self.ty(to));
        let text = if matches!(f, Ty::Param(_)) || matches!(t, Ty::Param(_)) {
            format!("a type parameter has no `as`, which no trait gives: `{source}` to `{target}` (§3.3)")
        } else if f.is_number() && t.is_number() {
            format!(
                "`as` only widens without losing information; `{source}` to `{target}` needs a conversion function (§3.3)"
            )
        } else {
            format!("`as` only converts between number types; `{source}` to `{target}` is not such a conversion (§3.3)")
        };
        let d = Diagnostic::new(Stage::Types, Code::E0411, span, text).with_found(self.src(span));
        let TypeKind::Path { path, .. } = &self.ast.ty(ty).kind else { return d };
        let written = self.src(path.span);
        // After the operand, the text the candidates replace; they go around
        // the operand (S-251).
        let rest = Span::new(span.file, self.expr(inner).span.end, span.end);
        if from == to && matches!(f, Ty::Param(_)) {
            return d.with_fix(Fix::new(format!("remove `as {written}`"), vec![Edit::delete(rest)]));
        }
        match cast_instead(&self.bounds(), from, to) {
            Instead::Calls(names) => names.iter().fold(d, |d, name| {
                let head = Edit::insert(span.file, span.start, format!("{written}.{name}("));
                d.with_fix(Fix::new(format!("call `{written}.{name}`"), vec![head, Edit::replace(rest, ")")]))
            }),
            Instead::Narrowing => d.with_rule(format!(
                "`{written}.{NARROW_FROM}(…)` gives an `Option[{target}]`, `None` out of range; it does not keep the low bits as `as` does in Rust or C (§3.3)"
            )),
            Instead::Nothing => d,
        }
    }

    /// A use at `span`, the name of the function, of the conversion to `to`
    /// from a value of `from`, with the result `ret`: an error now, or a
    /// check that waits for the source. It comes before the requirements of
    /// the use (S-883). `call`: the call, none of a function taken as a value.
    pub(super) fn conversion_use(
        &mut self,
        span: Span,
        from: TyId,
        to: TyId,
        ret: TyId,
        call: Option<ConversionCall>,
    ) -> R<()> {
        match self.conversion_verdict(from, to) {
            Verdict::Met => Ok(()),
            Verdict::Wait => {
                self.defer(span, from, DeferredKind::Conversion { to, ret, value: call.is_none() });
                Ok(())
            }
            Verdict::Unmet(why) => {
                let d = self.conversion_error(span, why);
                let from = self.infer.resolve(&mut self.a.types, from);
                let form = match call {
                    Some(call) => self.as_form(&call, from, to, ret),
                    None => Err(self.as_in_a_function(from, to, ret)),
                };
                let d = match form {
                    Ok(fix) => d.with_fix(fix),
                    Err(rule) => d.with_rule(rule),
                };
                Err(self.diag(d))
            }
        }
    }

    /// Whether a conversion from `from` to `to` exists. The one question is
    /// [`cast_allowed`](crate::cast::cast_allowed), of every kind of the
    /// source: a type parameter, which `as` does not convert, passes (§3.3),
    /// and so does a type that is no number, whose bound is its error; the
    /// same type does not, a type parameter too (`T.round_from(x)`, `x: T`). A
    /// pair `as` converts is this error also when the source breaks the bound
    /// of the function (`I64.trunc_from(n)`, `n: I32`, S-883), and an integer
    /// literal is judged at the type of its default at the end of the body
    /// (`F64.round_from(1)`, `I32` to `F64`, S-884).
    pub(crate) fn conversion_verdict(&mut self, from: TyId, to: TyId) -> Verdict {
        if self.infer.has_vars(&self.a.types, from) {
            return Verdict::Wait;
        }
        let from = self.infer.resolve(&mut self.a.types, from);
        if from != to && !crate::cast::cast_allowed(&self.a.types, from, to) {
            return Verdict::Met;
        }
        let (source, target) = (self.display(from), self.display(to));
        Verdict::Unmet(if from == to {
            format!("the value is already `{target}`; there is no conversion function to the same type (§3.3)")
        } else {
            format!("`as` converts `{source}` to `{target}`, so there is no conversion function for this pair (§3.3)")
        })
    }

    /// The E0413 of a use at `span` a verdict rejected for the reason `why`.
    pub(crate) fn conversion_error(&self, span: Span, why: String) -> Diagnostic {
        Diagnostic::new(Stage::Types, Code::E0413, span, why).with_found(self.src(span))
    }

    /// The note of a use whose source a later statement or the default
    /// decided (`as` takes the type of its operand where it is written, so
    /// the `as` form would be an E0420, §4.7, S-884): each form written out
    /// passes where the result of the call does.
    pub(crate) fn conversion_late_rule(&mut self, from: TyId, to: TyId, ret: TyId, value: bool) -> String {
        if value {
            return self.as_in_a_function(from, to, ret);
        }
        let (source, form) = (self.display(from), self.as_text("k", from, to, ret));
        let first = format!(
            "`as` takes the type of its operand where it is written (§4.7): give the operand a type first (`let k: {source} = …`, then `{form}`)"
        );
        // No literal is a value of a type parameter (§6.6).
        if matches!(self.ty(to), Ty::Param(_)) {
            return format!("{first} (§3.3)");
        }
        let literal = if matches!(self.ty(to), Ty::Float(_)) { "1.0" } else { "1" };
        let literal = if ret == to { literal.to_string() } else { format!("{}({literal})", lang::some(self.a)) };
        format!("{first}, or write the result as a literal (`{literal}`) (§3.3)")
    }

    /// The note of the function taken as a value (S-885): its parameter
    /// has its type, which `as` takes where it is written (§4.7).
    fn as_in_a_function(&mut self, from: TyId, to: TyId, ret: TyId) -> String {
        let (source, form) = (self.display(from), self.as_text("i", from, to, ret));
        format!("write an anonymous function in its place: `fn(i: {source}) {{ {form} }}` (§3.3)")
    }

    /// The text of the conversion of the variable `x` that the function
    /// from `from` to `to` with the result `ret` stands for.
    fn as_text(&mut self, x: &str, from: TyId, to: TyId, ret: TyId) -> String {
        let cast = if from == to { x.to_string() } else { format!("{x} as {}", self.display(to)) };
        if ret == to { cast } else { format!("{}({cast})", lang::some(self.a)) }
    }

    /// The note of a call with no candidate: the forms the pair has (§3.3).
    fn as_rule(&mut self, from: TyId, to: TyId, ret: TyId) -> String {
        let (target, option) = (self.display(to), self.display(ret));
        let (value, cast) = if from == to {
            ("the value".to_string(), "…".to_string())
        } else {
            (format!("`… as {target}`"), format!("… as {target}"))
        };
        if ret == to {
            return format!("write {value}, with no call (§3.3)");
        }
        let some = lang::some(self.a);
        format!("write {value} where `{target}` is expected, or `{some}({cast})` where `{option}` is (§3.3)")
    }

    /// The candidate of a call rejected at once (§3.3), else the rule of its
    /// note: `x as T`, or `x` of the same type; of a `narrow_from`, which
    /// gives `Option[T]`, that or the same in `Some`, the one that fits the
    /// expected type (S-875, S-880). `T` stays as it is written. The source
    /// is decided, so the operand of `as` is too (§4.7). None where neither
    /// or both fit, or where the form cannot be (§18.1). `Some` is a name
    /// no item takes (§15.1).
    fn as_form(&mut self, call: &ConversionCall, from: TyId, to: TyId, ret: TyId) -> Result<Fix, String> {
        let rule = self.as_rule(from, to, ret);
        let fits = |ck: &Self, c: TyId| call.expected.is_none_or(|t| ck.may_fit(t, c));
        let (bare, some) = (fits(self, to), ret != to && fits(self, ret));
        if bare == some {
            return Err(rule);
        }
        let Some(slot) = self.place_fits(call.e, if some { ret } else { to }) else { return Err(rule) };
        let ExprKind::Call { callee, args, .. } = &self.expr(call.e).kind else { return Err(rule) };
        // A `move` stands only on an argument (§5.2): none of the marked one.
        let (callee, &[Arg { mode: Mode::Borrow, expr: arg, .. }]) = (*callee, args.as_slice()) else {
            return Err(rule);
        };
        let ExprKind::Field { base, .. } = self.expr(callee).kind else { return Err(rule) };
        // The text around the argument, from the outside in. The argument
        // keeps parentheses in the place it comes to; out of `Some(…)`, also
        // where a header could end at it.
        let form = Form::of(self.ast, arg);
        let place = if some { Slot::Free } else { slot };
        let cast = from != to;
        let around = cast && place.wraps(Form::AsAt);
        let under = if cast { Slot::Operand(OperandPlace::AsAtLeft) } else { place };
        let inner = under.wraps(form) || (!some && opens_a_brace(self.ast, arg));
        let written = self.src(self.expr(base).span);
        let ctor = lang::some(self.a);
        let mut prefix = if some { format!("{ctor}(") } else { String::new() };
        prefix.push_str(&"(".repeat(around as usize + inner as usize));
        let mut suffix = ")".repeat(inner as usize);
        if cast {
            suffix.push_str(&format!(" as {written}"));
        }
        suffix.push_str(&")".repeat(around as usize + some as usize));
        let Some(edits) = self.around_arg(call.e, callee, arg, &prefix, &suffix) else { return Err(rule) };
        let title = match (cast, some) {
            (true, false) => format!("write `… as {written}`"),
            (true, true) => format!("write `{ctor}(… as {written})`"),
            (false, false) => "remove the call".to_string(),
            (false, true) => format!("write `{ctor}(…)`"),
        };
        Ok(Fix::new(title, edits))
    }

    /// The edits of the call `e` of `callee(arg)` into `prefix arg suffix`
    /// (§18.1): of what the call and the new text share, the `(` that ends
    /// `prefix` and the first `)` of `suffix` stay (S-251).
    fn around_arg(&self, e: ExprId, callee: ExprId, arg: ExprId, prefix: &str, suffix: &str) -> Option<Vec<Edit>> {
        let (call, open, arg) = (self.expr(e).span, self.expr(callee).span.end, self.expr(arg).span);
        let close = call.end.checked_sub(1)?;
        let bytes = self.text.as_bytes();
        if bytes.get(open as usize) != Some(&b'(') || bytes.get(close as usize) != Some(&b')') {
            return None;
        }
        let at = |start, end| Span::new(call.file, start, end);
        let mut edits = vec![match prefix.strip_suffix('(') {
            Some(p) => Edit::replace(at(call.start, open), p),
            None => Edit::delete(at(call.start, arg.start)),
        }];
        match suffix.split_once(')') {
            Some((before, after)) => {
                if arg.end < close || !before.is_empty() {
                    edits.push(Edit::replace(at(arg.end, close), before));
                }
                if !after.is_empty() {
                    edits.push(Edit::insert(call.file, call.end, after));
                }
            }
            None => edits.push(Edit::replace(at(arg.end, call.end), suffix)),
        }
        Some(edits)
    }
}
