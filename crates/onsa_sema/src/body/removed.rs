//! E0413 for a method a receiver has not (§3.3, §3.4, §4.2): of a method
//! the spec leaves out and gives another form of, the candidate of that
//! form, or a note of the rule where no candidate keeps the promise of
//! §18.1 (the form put there would leave an error).

use onsa_diag::Edit;
use onsa_syntax::ast::OperandPlace;

use super::slot::{Form, Slot, slot_of};
use super::*;

/// What the spec gives instead of a method it leaves out.
#[derive(Debug, Clone, Copy)]
enum Named {
    /// `is_empty` of a type with a length: `len() == 0` (§4.2).
    Length,
}

/// The methods the spec leaves out, by name.
const NAMED: &[(&str, Named)] = &[("is_empty", Named::Length)];

/// The one method of a type with a length (§4.2).
const LEN: &str = "len";

impl<'a> Checker<'a> {
    /// E0413 for the method `name` that `recv` has not, called by `e` with
    /// `args`, where the type `expected` is expected (§4.7).
    pub(super) fn removed_method(
        &mut self,
        e: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> Stop {
        let shown = self.display(recv);
        let message = format!("`{shown}` has no method `{}`", name.name);
        let d = Diagnostic::new(Stage::Types, Code::E0413, name.span, message).with_found(self.src(name.span));
        let d = match NAMED.iter().find(|(n, _)| *n == name.name) {
            Some((_, Named::Length)) if self.has_len(recv) => match self.len_test(e, name, args, expected, kind) {
                Some(fix) => d.with_fix(fix),
                None => d.with_rule("a type with a length has `len()` only, and an empty test is `len() == 0` (§4.2)"),
            },
            _ => d,
        };
        self.diag(d)
    }

    /// Whether `recv` is a builtin type with a length (§4.2), as far as this
    /// version gives it `len`; the `len` of a user type is none.
    fn has_len(&mut self, recv: TyId) -> bool {
        let (key, owner, _) = self.method_key(recv, LEN);
        if owner.is_some() {
            return false;
        }
        let table = key.and_then(|k| self.a.modules.assoc_builtin.get(&k));
        match self.a.modules.assoc_member(table, LEN) {
            Ok(Some(md)) => matches!(&self.a.def(md).kind, DefKind::Fn(f) if f.self_mode.is_some()),
            Ok(None) => builtin::method(&mut self.a.types, recv, LEN).is_some(),
            // Two declarations clash on it: no method a candidate can call.
            Err(_) => false,
        }
    }

    /// The candidate `….len() == 0` of `….is_empty()`: none of another form
    /// of the call, of an expression statement (its value is dropped), or
    /// where a `Bool` cannot be.
    fn len_test(
        &mut self,
        e: ExprId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> Option<Fix> {
        let bool_ = self.bool_();
        if kind != CallKind::Plain || !args.is_empty() || expected.is_some_and(|t| !self.may_fit(t, bool_)) {
            return None;
        }
        // A `Bool` has no member and no `as` (§6.3, §3.3): in the place of a
        // receiver or before `as` and `at`, the form leaves an error.
        let wrap = match slot_of(self.ast, self.root, e)? {
            Slot::Discarded | Slot::Operand(OperandPlace::Postfix | OperandPlace::AsAtLeft) => return None,
            slot => slot.wraps(Form::Binary(BinOp::Eq)),
        };
        let span = self.expr(e).span;
        let close = if wrap { ")" } else { "" };
        let mut edits = vec![
            Edit::replace(name.span, LEN),
            Edit::insert(span.file, span.end, format!(" {} 0{close}", BinOp::Eq.symbol())),
        ];
        if wrap {
            edits.insert(0, Edit::insert(span.file, span.start, "("));
        }
        Some(Fix::new("test `len() == 0`", edits))
    }

    /// Whether a value of the type `c` may be where the type `t` is expected
    /// (§4.7): `t` is `c`, a variable not of a literal, or the error type.
    /// `c` has no parts and is no literal's type (`Bool`).
    fn may_fit(&self, t: TyId, c: TyId) -> bool {
        let t = self.shallow(t);
        match self.ty(t) {
            Ty::Error => true,
            Ty::Var(i) => self.infer.var_lit(i).is_none(),
            _ => t == c,
        }
    }
}
