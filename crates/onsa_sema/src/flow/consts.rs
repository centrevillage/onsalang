//! The constant expressions of a flow (§4.5, §11.4): the lengths and
//! bounds that fix the state size (R-195, W7-02), read by the one reader of
//! the constant expressions (`crate::constarg`) from the records of the
//! names of the body.

use super::*;
use crate::constarg::{ConstU32, Unheld};

impl<'a> Checker<'a> {
    /// A compile-time `U32` (§11.4, §4.5): the value of a constant
    /// expression. This version computes an integer literal and a `const`
    /// with a literal value (in parentheses too); the other constant
    /// expressions are E0200 until W7-02 (R-195).
    pub(super) fn flow_const_u32(&mut self, e: ExprId) -> R<u32> {
        match self.const_expr(e) {
            Ok((ConstU32::Value(v), constant)) => {
                let u32 = self.u32();
                let mut cur = e;
                while let ExprKind::Paren(inner) = self.expr(cur).kind {
                    self.record(cur, u32);
                    cur = inner;
                }
                self.record(cur, u32);
                if let Some(def) = constant {
                    self.info.targets.insert(cur, Target::Const { def, of: None, inst: None });
                }
                Ok(v)
            }
            // A flow has no const parameters.
            Ok((ConstU32::Param(_), _)) | Err(Unheld::Uncomputed(_)) => {
                Err(self.unsupported_in(Stage::Flow, self.expr(e).span, Feature::FlowConstExprs, &[]))
            }
            Err(Unheld::Report(d)) => Err(self.diag(d)),
            // A name held as an error, a constant whose unit failed (§18.1).
            Err(Unheld::Unknown) => {
                self.failed = true;
                Err(crate::body::Stop)
            }
        }
    }
}
