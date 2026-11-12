//! A string literal of the type `FixedStr[N]` of `std.text` (§4.2, §4.7,
//! S-614): where the expected type is one, a literal with no interpolation
//! is a value of it. The one judgment of an expression (`check_lit` and
//! the comparisons); a pattern of a `match` is to call it too (§7, U3a).

use onsa_syntax::ast::StrLit;

use super::*;

impl Checker<'_> {
    /// The type of the string literal `lit` at `span` whose expected type is
    /// `want`: `Some` of the `FixedStr[N]` it is a value of, `None` where it
    /// is a `Str` (no expected type, or another). An interpolation is an
    /// E0401 (§2.4: it makes a new `Str`); a character out of ASCII and a
    /// literal longer than `N` are E0408. An `N` not decided is the length of
    /// the literal (S-614 C1), as the length of an array literal.
    pub(super) fn fixed_literal(&mut self, span: Span, lit: &StrLit, want: Option<TyId>) -> R<Option<TyId>> {
        let Some(want) = want.map(|t| self.shallow(t)) else { return Ok(None) };
        let Ty::Named(d, args) = self.ty(want) else { return Ok(None) };
        if self.a.modules.lang.fixed_str(d).is_none() {
            return Ok(None);
        }
        // The value of a literal with no interpolation.
        let Some(text) = lit.value() else {
            let shown = self.display(want);
            let msg = format!("a string literal with an interpolation makes a new `Str`, not a `{shown}` (§2.4, §4.2)");
            return Err(self.err(Code::E0401, span, msg));
        };
        if let Some(c) = text.chars().find(|c| !c.is_ascii()) {
            let msg =
                format!("`{}` holds ASCII alone; the literal has `{}` (§4.2)", self.display(want), c.escape_unicode());
            return Err(self.err(Code::E0408, span, msg));
        }
        let length = text.len() as u32;
        let n = self.shallow(args[0]);
        match self.ty(n) {
            Ty::ConstVal(c) if length > c => {
                let shown = self.display(want);
                let msg = format!("the literal of length {length} is longer than the capacity of `{shown}` (§4.2)");
                Err(self.err(Code::E0408, span, msg))
            }
            Ty::Var(_) => {
                let t = self.a.types.intern(Ty::ConstVal(length));
                self.unify_at(span, t, n)?;
                Ok(Some(want))
            }
            // SPEC-GAP(S-1005): a capacity that is a const parameter of the
            // item is not known at the check, so the literal is not read as
            // one (as an array literal where `[U8; N]` is expected).
            Ty::Param(_) => {
                let shown = self.display(want);
                let msg = format!("a string literal cannot have type `{shown}`: its capacity is a parameter (§4.2)");
                Err(self.err(Code::E0401, span, msg))
            }
            _ => Ok(Some(want)),
        }
    }
}
