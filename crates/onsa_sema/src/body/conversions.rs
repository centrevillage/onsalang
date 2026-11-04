//! The conversions that are associated functions of the number types
//! (`F32.round_from`, `I8.narrow_from`, §3.3): a pair of concrete types `as`
//! converts has none (E0413, S-231). A use is judged when its source is
//! decided, which a later statement may do (§4.7).

use super::*;

impl<'a> Checker<'a> {
    /// A use at `span`, the name of the function, of the conversion to `to`
    /// from a value of `from`: an error now, or a check that waits for the
    /// source. It comes before the requirements of the use (S-883).
    pub(super) fn conversion_use(&mut self, span: Span, from: TyId, to: TyId) -> R<()> {
        match self.conversion_verdict(from, to) {
            Verdict::Met => Ok(()),
            Verdict::Wait => {
                self.defer(span, from, DeferredKind::Conversion { to });
                Ok(())
            }
            Verdict::Unmet(why) => {
                let d = self.conversion_error(span, why);
                Err(self.diag(d))
            }
        }
    }

    /// Whether a conversion from `from` to `to` exists. The one question is
    /// [`cast_allowed`](crate::cast::cast_allowed), of every kind of the
    /// source: a type parameter, which `as` does not convert, passes (§3.3),
    /// and so does a type that is no number, whose bound is its error. A
    /// pair `as` converts is this error also when the source breaks the bound
    /// of the function (`I64.trunc_from(n)`, `n: I32`, S-883), and an integer
    /// literal is judged at the type of its default at the end of the body
    /// (`F64.round_from(1)`, `I32` to `F64`, S-884).
    pub(crate) fn conversion_verdict(&mut self, from: TyId, to: TyId) -> Verdict {
        if self.infer.has_vars(&self.a.types, from) {
            return Verdict::Wait;
        }
        let from = self.infer.resolve(&mut self.a.types, from);
        if !crate::cast::cast_allowed(&self.a.types, from, to) {
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
}
