//! The C lvalues of the places: locals, fields and elements.

use super::text::dot;
use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    pub(super) fn place_ty(&self, p: &Place) -> R<CTy> {
        Ok(match p {
            Place::Local(l) => self.local_ty(*l),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                field_ty(self.cx, bt, *i)?
            }
            Place::Index(b, ..) => match self.kind(self.place_ty(b)?) {
                TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e) => *e,
                _ => return Err(internal("index of a non-sequence place")),
            },
        })
    }

    /// Render a field access on a C lvalue / rvalue of type `base_ty`.
    pub(super) fn field_access(&mut self, base: &str, base_ty: CTy, index: u32) -> R<String> {
        match self.kind(base_ty) {
            TyKind::Tuple(_) => Ok(format!("{}f{index}", dot(base))),
            TyKind::Struct(id) => {
                let (fname, _) = self.cx.fields(*id).get(index as usize).ok_or_else(|| internal("field index"))?;
                if let Some(b) = self.cx.bulk.get(id).cloned()
                    && b.fields.contains(&index)
                {
                    return Ok(format!("(*({}*){}bulk).{}", b.struct_name, dot(base), ident(fname)));
                }
                Ok(format!("{}{}", dot(base), ident(fname)))
            }
            _ => Err(internal("field of a non-record")),
        }
    }

    pub(super) fn place(&mut self, p: &Place) -> R<String> {
        match p {
            Place::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                self.field_access(&bs, bt, *i)
            }
            Place::Index(b, i, _, bounds) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                let idx = self.expr(i)?;
                self.index_access(&bs, bt, &idx, i.span, *bounds)
            }
        }
    }

    /// `base[idx]`; checked by `onsa_idx` unless known in range (S-196).
    pub(super) fn index_access(
        &mut self,
        base: &str,
        base_ty: CTy,
        idx: &str,
        span: Span,
        bounds: Bounds,
    ) -> R<String> {
        let loc = self.loc(span);
        match (self.kind(base_ty), bounds) {
            (TyKind::Array(..), Bounds::Known) => Ok(format!("{base}.a[{idx}]")),
            (TyKind::Span(_), Bounds::Known) => Ok(format!("{base}.ptr[{idx}]")),
            (TyKind::Array(_, n), Bounds::Checked) => Ok(format!("{base}.a[onsa_idx({idx}, UINT32_C({n}), {loc})]")),
            (TyKind::Span(_), Bounds::Checked) => Ok(format!("{base}.ptr[onsa_idx({idx}, {base}.len, {loc})]")),
            (TyKind::Buf(_), _) => Err(unsupported(span, Feature::Buf, &[])),
            _ => Err(internal("index of a non-sequence")),
        }
    }
}

pub(crate) fn field_ty(cx: &Cx, base: CTy, index: u32) -> R<CTy> {
    match cx.kind(base) {
        TyKind::Tuple(ts) => ts.get(index as usize).copied().ok_or_else(|| internal("tuple index")),
        TyKind::Struct(id) => {
            cx.fields(*id).get(index as usize).map(|(_, t)| *t).ok_or_else(|| internal("field index"))
        }
        _ => Err(internal("field of a non-record")),
    }
}
