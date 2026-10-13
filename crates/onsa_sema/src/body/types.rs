//! The types written inside a body.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ types in bodies

    /// Lower a type written inside a body (annotations, casts, closure params).
    pub(crate) fn lower_type_expr(&mut self, t: onsa_syntax::ast::TypeId) -> R<TyId> {
        let generics = self.generics.clone();
        let (ty, diags) =
            crate::sig::lower_type_in_body(self.a, self.m, self.ast, self.text, &generics, self.self_ty, self.def, t);
        if let Some(d) = diags.into_iter().next() {
            return Err(self.diag(d));
        }
        Ok(ty)
    }
}
