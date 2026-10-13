//! Compile-time values of `const` items whose initializer is a literal, a
//! negated literal, or an aggregate of those (T2-11, spec §6.6). Initializers
//! that call functions are evaluated by the interpreter in M3.

use onsa_syntax::ast::{ExprId, ExprKind, Lit, UnOp};

use crate::body::{Checker, Target};
use crate::ty::Ty;

#[derive(Debug, Clone, PartialEq)]
pub enum ConstValue {
    Int(i128),
    /// The value rounded once to its type (`onsa_syntax::float_value`): an
    /// `F32` value is held exactly, so it is not rounded twice (R-20).
    Float(f64),
    /// A float literal (with a `-` written on it) whose type was still open
    /// when it was evaluated (the initial value of a delay whose type a later
    /// statement decides, `prev~(^y, 0.1)`): the lowering rounds it once to
    /// the decided type (`onsa_syntax::float_value`, R-20).
    FloatText(String),
    Bool(bool),
    Char(char),
    Unit,
    Array(Vec<ConstValue>),
    Tuple(Vec<ConstValue>),
    /// Struct fields in declaration order.
    Struct(Vec<ConstValue>),
}

pub(crate) fn eval(ck: &mut Checker<'_>, e: ExprId) -> Option<ConstValue> {
    let expr = ck.ast_expr(e);
    match &expr.kind {
        ExprKind::Lit(Lit::Int { value, .. }) => Some(ConstValue::Int(*value as i128)),
        ExprKind::Lit(Lit::Float { text }) => match ck.ty(ck.shallow(ck.body_type(e)?)) {
            Ty::Float(k) => onsa_syntax::float_value(text, k.width()).ok().map(ConstValue::Float),
            Ty::Var(_) => Some(ConstValue::FloatText(text.clone())),
            _ => None,
        },
        ExprKind::Lit(Lit::Bool(b)) => Some(ConstValue::Bool(*b)),
        ExprKind::Lit(Lit::Char(c)) => Some(ConstValue::Char(*c)),
        ExprKind::Paren(inner) => eval(ck, *inner),
        ExprKind::Unary { op: UnOp::Neg, expr: inner } => match eval(ck, *inner)? {
            ConstValue::Int(v) => Some(ConstValue::Int(-v)),
            ConstValue::Float(v) => Some(ConstValue::Float(-v)),
            ConstValue::FloatText(t) => {
                Some(ConstValue::FloatText(t.strip_prefix('-').map_or_else(|| format!("-{t}"), str::to_string)))
            }
            _ => None,
        },
        ExprKind::Tuple(elems) => {
            if elems.is_empty() {
                return Some(ConstValue::Unit);
            }
            elems.iter().map(|&x| eval(ck, x)).collect::<Option<Vec<_>>>().map(ConstValue::Tuple)
        }
        ExprKind::Array(elems) => elems.iter().map(|&x| eval(ck, x)).collect::<Option<Vec<_>>>().map(ConstValue::Array),
        ExprKind::Repeat { elem, len } => {
            let v = eval(ck, *elem)?;
            let n = match ck.body_type(*len).and_then(|_| match &ck.ast_expr(*len).kind {
                ExprKind::Lit(Lit::Int { value, .. }) => Some(*value as usize),
                _ => None,
            }) {
                Some(n) => n,
                None => match ck.target_of(*len) {
                    Some(Target::Const(d)) => match &ck.a.def(d).kind {
                        crate::def::DefKind::Const(c) => c.int_value? as usize,
                        _ => return None,
                    },
                    _ => return None,
                },
            };
            Some(ConstValue::Array(vec![v; n]))
        }
        ExprKind::Struct { fields, .. } => {
            // Fields in declaration order.
            let t = ck.body_type(e)?;
            let Ty::Named(d, _) = ck.a.types.get(t).clone() else { return None };
            let def = ck.a.def(d).as_struct()?.clone();
            let crate::def::Fields::Named(fs) = &def.fields else { return None };
            let mut out = Vec::new();
            for f in fs {
                let (_, v) = fields.iter().find(|(n, _)| n.name == f.name)?;
                out.push(eval(ck, *v)?);
            }
            Some(ConstValue::Struct(out))
        }
        ExprKind::Path(_) | ExprKind::Field { .. } => match ck.target_of(e) {
            Some(Target::Const(d)) => ck.a.const_values.get(&d).cloned(),
            _ => None,
        },
        _ => None,
    }
}
