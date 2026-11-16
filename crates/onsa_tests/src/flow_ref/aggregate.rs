//! The aggregates of the evaluator (§4.4, §11.2): the literals of tuples, arrays and structs (`[e; N]` and `...`
//! included), the fields, the elements and the indexes of them. The elements are
//! evaluated from the left as written (§3.5), and an index out of the array is a panic at the index expression (§9.2).
//! Each arm is a function of its own (`#[inline(never)]`) so that the frame of `Frame::form` stays small.

use onsa_diag::Span;
use onsa_sema::Ty;
use onsa_sema::def::FieldDef;
use onsa_sema::ty::Len;
use onsa_syntax::ast::{ExprId, ExprKind, Ident};

use super::expr::{Eval, Frame, Stop};
use super::scalar::{Fault, PanicKind};
use super::value::Value;

impl Frame<'_> {
    /// The values of `xs`, from the left.
    fn all(&mut self, xs: &[ExprId]) -> Result<Vec<Value>, Stop> {
        xs.iter().map(|x| self.eval(*x)).collect()
    }

    /// The form of `e` that is an aggregate or a part of one (`F32.PI` is a field of the name `F32` to the syntax,
    /// and the table says it is a constant); one door for `Frame::form`, which keeps its frame small.
    #[inline(never)]
    pub(super) fn aggregate(&mut self, e: ExprId, at: Span) -> Eval {
        match &self.body.ast.expr(e).kind {
            ExprKind::Field { base, name } => self.field(e, *base, &name.name, at),
            ExprKind::TupleIndex { base, index, .. } => self.element(*base, *index as usize, at),
            ExprKind::Index { base, index } => self.index(*base, *index, at),
            ExprKind::Tuple(xs) => self.tuple(xs),
            ExprKind::Array(xs) => self.array(xs),
            ExprKind::Repeat { elem, .. } => self.repeat(e, *elem, at),
            ExprKind::Struct { fields, rest, .. } => self.record(e, fields, rest.is_some(), at),
            _ => Err(Stop { fault: Fault::Internal("not an aggregate"), at }),
        }
    }

    #[inline(never)]
    pub(super) fn tuple(&mut self, xs: &[ExprId]) -> Eval {
        Ok(Value::tuple(self.all(xs)?))
    }

    #[inline(never)]
    pub(super) fn array(&mut self, xs: &[ExprId]) -> Eval {
        Ok(Value::Array(self.all(xs)?))
    }

    /// `[e; N]`: `e` is evaluated once, even when `N` is 0 (§2.4); `N` is the length the table gives the array, and
    /// the places of the copies (`N` times those of `e`) are at most `Limits::most`: the spec bounds the type (§4.4),
    /// not what the evaluator holds of it.
    #[inline(never)]
    pub(super) fn repeat(&mut self, e: ExprId, elem: ExprId, at: Span) -> Eval {
        let v = self.eval(elem)?;
        match self.body.ty(e).map_err(|fault| Stop { fault, at })? {
            Ty::Array(_, Len::Const(n)) if (*n as usize).saturating_mul(v.places()) <= self.limits.most => {
                Ok(Value::Array(vec![v; *n as usize]))
            }
            _ => Err(Stop { fault: Fault::Unavailable("an array that is not of a size the evaluator builds"), at }),
        }
    }

    /// A struct literal: the fields as written, then the ones `...` fills with the default of their declaration.
    #[inline(never)]
    pub(super) fn record(&mut self, e: ExprId, written: &[(Ident, ExprId)], fill: bool, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let Ty::Named(def, _) = self.body.ty(e).map_err(here)? else {
            return Err(here(Fault::Internal("a struct literal that is not of a struct")));
        };
        let decl = self.body.view.struct_fields(*def).map_err(here)?;
        let mut vals: Vec<Option<Value>> = vec![None; decl.len()];
        for (name, x) in written {
            let place = decl.iter().position(|f| f.name == name.name);
            vals[place.ok_or(here(Fault::Internal("a field the struct has not")))?] = Some(self.eval(*x)?);
        }
        let mut out = Vec::with_capacity(decl.len());
        for (field, v) in decl.iter().zip(vals) {
            out.push(match v {
                Some(v) => v,
                None if fill => self.default_of(field, at)?,
                None => return Err(here(Fault::Internal("a field with no value"))),
            });
        }
        Ok(Value::Struct(out))
    }

    /// The default `...` gives a field (§4.4). A field with none is E0410 in the checker, not `T.default()`.
    fn default_of(&mut self, field: &FieldDef, at: Span) -> Eval {
        let Some(def) = field.default else {
            return Err(Stop { fault: Fault::Internal("`...` over a field with no default"), at });
        };
        self.const_def(def, self.body.view.ty(field.ty), at)
    }

    /// `base.name`: a field of a struct, or else a name the table knows (`F32.PI`, `Mode.Off`).
    #[inline(never)]
    pub(super) fn field(&mut self, e: ExprId, base: ExprId, name: &str, at: Span) -> Eval {
        if self.body.names(e) {
            return self.name(e, at);
        }
        let here = |fault| Stop { fault, at };
        let Ty::Named(def, _) = self.body.ty(base).map_err(here)? else {
            return Err(here(Fault::Internal("a field of what is not a struct")));
        };
        let place = self.body.view.struct_fields(*def).map_err(here)?.iter().position(|f| f.name == name);
        match (self.eval(base)?, place) {
            (Value::Struct(mut vs), Some(i)) if i < vs.len() => Ok(vs.swap_remove(i)),
            _ => Err(here(Fault::Internal("a field that is not there"))),
        }
    }

    /// `base.0`.
    #[inline(never)]
    pub(super) fn element(&mut self, base: ExprId, index: usize, at: Span) -> Eval {
        match self.eval(base)? {
            Value::Tuple(mut vs, _) if index < vs.len() => Ok(vs.swap_remove(index)),
            _ => Err(Stop { fault: Fault::Internal("an element that is not there"), at }),
        }
    }

    /// `base[index]`: `base` first, then `index` (§3.5); out of the array is a panic at this expression (§9.2).
    #[inline(never)]
    pub(super) fn index(&mut self, base: ExprId, index: ExprId, at: Span) -> Eval {
        match (self.eval(base)?, self.eval(index)?) {
            (Value::Array(mut vs), Value::Int(_, i, _)) => match usize::try_from(i) {
                Ok(i) if i < vs.len() => Ok(vs.swap_remove(i)),
                _ => Err(Stop { fault: Fault::Panic(PanicKind::Bounds), at }),
            },
            _ => Err(Stop { fault: Fault::Internal("an index of what is not an array"), at }),
        }
    }
}
