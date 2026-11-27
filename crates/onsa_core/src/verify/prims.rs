//! V-02: the operands and the value of a primitive are of its row of the
//! table ([`crate::prim::sig`]): their number, their modes and the forms of
//! their types.

use super::{R, Rule, V};
use crate::ir::*;
use crate::prim::{Prim, Shape, sig};

impl<'a> V<'a> {
    pub(super) fn prim_sig(&self, prim: &Prim, args: &[Arg], ty: CTy) -> R<()> {
        let sig = sig(prim);
        let fail = |what: String| self.err(Rule::V02, format!("`{}`: {what}", prim.name()));
        if args.len() != sig.args.len() {
            return Err(fail(format!("{} operand(s), expected {}", args.len(), sig.args.len())));
        }
        let not_of = |what: String, t, shape| {
            fail(format!("{what} of `{}` is not of the form {shape:?} of its row", crate::dump::type_name(self.m, t)))
        };
        // The element `E`, given by the first form of it.
        let mut elem = None;
        for (i, (a, &(mode, shape))) in args.iter().zip(&sig.args).enumerate() {
            if a.mode != mode {
                return Err(fail(format!("the mode of operand {i} is not of its row")));
            }
            if !self.fits(shape, a.expr.ty, &mut elem)? {
                return Err(not_of(format!("operand {i}"), a.expr.ty, shape));
            }
        }
        if !self.fits(sig.ret, ty, &mut elem)? {
            return Err(not_of("the value".into(), ty, sig.ret));
        }
        Ok(())
    }

    /// Whether `t` is of the form `shape`, its element the `elem` met before
    /// (or the first). A part of `t`, which is in the table, is in it.
    fn fits(&self, shape: Shape, t: CTy, elem: &mut Option<CTy>) -> R<bool> {
        let exact = |want: CTy| Ok(t == want);
        let e = match (shape, self.kind(t)?) {
            (Shape::Int(k), _) => return exact(Types::int(k)),
            (Shape::Float(k), _) => return exact(Types::float(k)),
            (Shape::Bool, _) => return exact(Types::BOOL),
            (Shape::Unit, _) => return exact(Types::UNIT),
            (Shape::Parts(k), TyKind::Tuple(ts)) => return Ok(**ts == [Types::BOOL, Types::int(k)]),
            (Shape::Any, _) => return Ok(true),
            (Shape::Seq, TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e)) => *e,
            (Shape::SpanOf, TyKind::Span(e)) => *e,
            (Shape::SpanOfNum, TyKind::Span(e)) if self.m.tys.is_int(*e) || self.m.tys.is_float(*e) => *e,
            (Shape::BufOf, TyKind::Buf(e)) => *e,
            (Shape::Elem, _) => t,
            _ => return Ok(false),
        };
        Ok(*elem.get_or_insert(e) == e)
    }
}
