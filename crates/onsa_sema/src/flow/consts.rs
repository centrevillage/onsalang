//! The constant expressions of a flow (§4.5, §11.4): the lengths and
//! bounds that fix the state size (R-195, W7-02).

use super::*;

impl<'a> Checker<'a> {
    /// A compile-time `U32` (§11.4, §4.5): the value of a constant
    /// expression. This version computes an integer literal and a `const`
    /// with a literal value; the other constant expressions are E0200 until
    /// W7-02 (R-195), and what is no constant expression is E0417.
    pub(super) fn flow_const_u32(&mut self, e: ExprId, what: &str) -> R<u32> {
        let span = self.expr(e).span;
        let u32 = self.u32();
        let mut shape = ConstShape { leaves: Vec::new(), arith: true, neg: false, ops: false };
        self.const_shape(e, &mut shape);
        // Each leaf, its names read as the constants of type positions are
        // (`constarg::named`: `N`, `cfg.N`, `I32.BITS`).
        let mut leaves = Vec::new();
        for &l in &shape.leaves {
            let leaf = match &self.expr(l).kind {
                ExprKind::Lit(Lit::Int { value, .. }) => Leaf::Int(*value),
                ExprKind::Path(_) | ExprKind::Field { .. } => match crate::constarg::path_of(self.ast, l) {
                    // A local, or a field of one.
                    Some(p) if self.is_local_head(&p.segments[0].name) => Leaf::Other,
                    Some(p) => {
                        let lspan = self.expr(l).span;
                        match crate::constarg::named(self.a, self.m, self.ast, self.text, &p, lspan) {
                            Ok(Some(v)) => match self.a.resolve_path(self.m, &p) {
                                Ok(Entity::Def(d) | Entity::Member(d)) => Leaf::Value(v, Some(d)),
                                _ => Leaf::Value(v, None),
                            },
                            Ok(None) => Leaf::Other,
                            Err(crate::constarg::ConstErr::Uncomputed(_)) => Leaf::Uncomputed,
                            Err(crate::constarg::ConstErr::Report(d)) => Leaf::Error(d),
                            // A constant whose unit failed (S-59): no diagnostic.
                            Err(crate::constarg::ConstErr::Unknown) => {
                                self.failed = true;
                                return Err(crate::body::Stop);
                            }
                        }
                    }
                    None => Leaf::Other,
                },
                _ => Leaf::Other,
            };
            leaves.push((l, leaf));
        }
        // The names stage first (§18.1): a name that does not resolve.
        if let Some(i) = leaves.iter().position(|(_, l)| matches!(l, Leaf::Error(d) if d.stage == Stage::Names)) {
            let Leaf::Error(d) = leaves.swap_remove(i).1 else { unreachable!() };
            return Err(self.diag(d));
        }
        // The type: an integer (§7, §4.5), with no prefix `-` (S-228).
        if let Some(form) = self.non_integer_form(e) {
            return Err(self.err(Code::E0401, span, format!("{what} is an integer (`U32`); found {form}")));
        }
        if shape.neg {
            return Err(self.err(Code::E0401, span, format!("{what} is a `U32`, which has no prefix `-` (§4.5)")));
        }
        // A constant expression is made of literals and constants (§4.5).
        if !shape.arith || leaves.iter().any(|(_, l)| matches!(l, Leaf::Other)) {
            return Err(self.flow_not_const(span, what));
        }
        if let Some(i) = leaves.iter().position(|(_, l)| matches!(l, Leaf::Error(_))) {
            let Leaf::Error(d) = leaves.swap_remove(i).1 else { unreachable!() };
            return Err(self.diag(d));
        }
        // A literal that no `U32` holds, wherever it is (before the values
        // this version does not compute, S-224).
        if let Some(&(l, _)) = leaves.iter().find(|(_, l)| matches!(l, Leaf::Int(v) if *v > u32::MAX as u64)) {
            let lspan = self.expr(l).span;
            return Err(self.flow_err(Code::E0408, lspan, format!("{what} does not fit in `U32`")));
        }
        // The value: one literal or one constant, in parentheses or not.
        let value = match leaves.as_slice() {
            [(l, Leaf::Int(v))] if !shape.ops => {
                self.record(*l, u32);
                *v as u32
            }
            [(l, Leaf::Value(v, d))] if !shape.ops => {
                self.record(*l, u32);
                if let Some(d) = d {
                    self.info.targets.insert(*l, Target::Const(*d));
                }
                *v
            }
            // The values of the other constant expressions (W7-02, R-195).
            _ => return Err(self.unsupported_in(Stage::Flow, span, Feature::FlowConstExprs, &[])),
        };
        self.record(e, u32);
        Ok(value)
    }

    /// The leaves of `e` under parentheses, prefix `-` and binary operators,
    /// and whether those are the operators of a constant expression (§4.5:
    /// `+ - * / %`).
    fn const_shape(&self, e: ExprId, shape: &mut ConstShape) {
        match &self.expr(e).kind {
            ExprKind::Paren(x) => self.const_shape(*x, shape),
            ExprKind::Unary { op: UnOp::Neg, expr: x } => {
                shape.neg = true;
                self.const_shape(*x, shape);
            }
            ExprKind::Binary { op, lhs, rhs, .. } => {
                shape.ops = true;
                shape.arith &= matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem);
                self.const_shape(*lhs, shape);
                self.const_shape(*rhs, shape);
            }
            _ => shape.leaves.push(e),
        }
    }

    fn flow_not_const(&mut self, span: Span, what: &str) -> crate::body::Stop {
        self.err(
            Code::E0417,
            span,
            format!("{what} must be a constant expression (§4.5), so that the state size is fixed (§11.4)"),
        )
    }
}

/// The shape of a constant expression of a flow ([`Checker::const_shape`]).
struct ConstShape {
    leaves: Vec<ExprId>,
    /// Every binary operator is one of a constant expression.
    arith: bool,
    /// A prefix `-` (S-228).
    neg: bool,
    /// A binary operator.
    ops: bool,
}

/// A leaf of a constant expression of a flow.
enum Leaf {
    Int(u64),
    /// A constant with a value (and its item, for a `const`).
    Value(u32, Option<crate::DefId>),
    /// A constant whose value this version does not compute (W7-02).
    Uncomputed,
    Error(Diagnostic),
    /// No constant: a local, a function, a call, ...
    Other,
}
