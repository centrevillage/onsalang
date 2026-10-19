//! Places: locals, projections, and the sequences a primitive reads or
//! writes.

use onsa_core::{Arg, LocalId, Mode, Place};
use onsa_diag::Span;

use crate::numeric::mismatch;
use crate::value::{ArrayData, Proj, Slot, SpanRef, Value, slot};
use crate::{Interp, R, internal, panic};

/// A resolved memory location: a slot and the projections inside its value.
#[derive(Debug, Clone)]
pub(super) struct PlaceRef {
    pub(super) root: Slot,
    pub(super) projs: Vec<Proj>,
}

/// What a local binding refers to.
#[derive(Debug, Clone)]
pub(super) enum Loc {
    Slot(Slot),
    /// An `inout` parameter: the caller's place.
    Alias(PlaceRef),
}

pub(super) struct Frame {
    pub(super) locals: Vec<Option<Loc>>,
}

/// A leaf found by walking projections.
pub(super) enum Leaf<'a> {
    Val(&'a Value),
    F32(f32),
}

enum LeafMut<'a> {
    Val(&'a mut Value),
    F32(&'a mut f32),
}

/// An argument after evaluation: a value, or the caller's place for `inout`.
pub(super) enum ArgVal {
    Val(Value),
    Place(PlaceRef),
}

/// A sequence a prim reads or writes: the array at `root` + `projs`, from
/// `start` for `len` elements.
pub(super) struct SeqRef {
    pub(super) root: Slot,
    pub(super) projs: Vec<Proj>,
    pub(super) start: u32,
    pub(super) len: u32,
}
impl<'m> Interp<'m> {
    // ------------------------------------------------------------ places

    pub(super) fn local_place(&self, f: &Frame, l: LocalId, span: Span) -> R<PlaceRef> {
        match &f.locals[l.0 as usize] {
            Some(Loc::Slot(s)) => Ok(PlaceRef { root: s.clone(), projs: Vec::new() }),
            Some(Loc::Alias(p)) => Ok(p.clone()),
            None => internal(span, "local read before initialization"),
        }
    }

    pub(super) fn resolve_place(&self, f: &mut Frame, p: &Place, span: Span) -> R<PlaceRef> {
        match p {
            Place::Local(l) => self.local_place(f, *l, span),
            Place::Field(b, i) => {
                let r = self.resolve_place(f, b, span)?;
                self.project_field(r, *i, span)
            }
            // Each element has its own position (R-188): an inner `xs[i]` of
            // `xs[i][0]` that is out of range panics at `xs[i]`.
            Place::Index(b, e, at) => {
                let i = self.eval_u32(f, e)?;
                let r = self.resolve_place(f, b, span)?;
                self.project_index(r, i, *at)
            }
        }
    }

    pub(super) fn project_field(&self, mut r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        let ok = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Struct(fs)) | Leaf::Val(Value::Tuple(fs)) | Leaf::Val(Value::Enum { fields: fs, .. }) => {
                (i as usize) < fs.len()
            }
            _ => false,
        })?;
        if !ok {
            internal(span, "field projection on a non-aggregate");
        }
        r.projs.push(Proj::Field(i));
        Ok(r)
    }

    /// Index into the sequence at `r`, following `Span` / `Buf` indirection.
    pub(super) fn project_index(&self, r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        enum Kind {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let kind = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => Kind::Array(a.len()),
            Leaf::Val(Value::Span(s)) => Kind::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => Kind::Buf(b.clone()),
            _ => Kind::Other,
        })?;
        match kind {
            Kind::Array(len) => {
                if i >= len {
                    return panic(span, format!("index {i} out of range for a sequence of length {len}"));
                }
                let mut r = r;
                r.projs.push(Proj::Index(i));
                Ok(r)
            }
            Kind::Span(s) => {
                if i >= s.len {
                    return panic(span, format!("index {i} out of range for a span of length {}", s.len));
                }
                let mut projs = s.projs.clone();
                projs.push(Proj::Index(s.start + i));
                Ok(PlaceRef { root: s.root, projs })
            }
            Kind::Buf(b) => {
                let len = buf_len(&b, span);
                if i >= len {
                    return panic(span, format!("index {i} out of range for a buffer of length {len}"));
                }
                Ok(PlaceRef { root: b, projs: vec![Proj::Index(i)] })
            }
            Kind::Other => internal(span, "index on a non-sequence"),
        }
    }

    fn walk<'a>(v: &'a Value, projs: &[Proj]) -> Option<Leaf<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get(*i as usize).map(|x| Leaf::F32(*x)) } else { None };
                }
                _ => return None,
            }
        }
        Some(Leaf::Val(cur))
    }

    fn walk_mut<'a>(v: &'a mut Value, projs: &[Proj]) -> Option<LeafMut<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get_mut(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get_mut(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get_mut(*i as usize).map(LeafMut::F32) } else { None };
                }
                _ => return None,
            }
        }
        Some(LeafMut::Val(cur))
    }

    pub(super) fn peek<T>(&self, r: &PlaceRef, span: Span, f: impl FnOnce(Leaf<'_>) -> T) -> R<T> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(leaf) => Ok(f(leaf)),
            None => internal(span, "dangling place"),
        }
    }

    pub(super) fn read(&self, r: &PlaceRef, span: Span) -> R<Value> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => internal(span, "dangling place"),
        }
    }

    pub(super) fn write(&self, r: &PlaceRef, value: Value, span: Span) -> R<()> {
        let mut v = r.root.borrow_mut();
        match Self::walk_mut(&mut v, &r.projs) {
            Some(LeafMut::Val(x)) => {
                *x = value;
                Ok(())
            }
            Some(LeafMut::F32(x)) => match value {
                Value::F32(y) => {
                    *x = y;
                    Ok(())
                }
                _ => internal(span, "non-F32 written into an F32 array"),
            },
            None => internal(span, "dangling place"),
        }
    }

    /// The sequence an expression denotes (a `Span` value, a `Buf`, or an
    /// array place); temporaries are copied into a fresh slot.
    pub(super) fn seq_of_arg(&self, f: &mut Frame, a: &Arg) -> R<SeqRef> {
        let span = a.expr.span;
        if a.mode == Mode::Inout
            && let Some(p) = a.expr.as_place()
        {
            let r = self.resolve_place(f, &p, span)?;
            return self.seq_of_place(r, span);
        }
        let v = self.eval(f, &a.expr)?;
        self.seq_of_value(v, span)
    }

    pub(super) fn seq_of_place(&self, r: PlaceRef, span: Span) -> R<SeqRef> {
        enum K {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let k = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => K::Array(a.len()),
            Leaf::Val(Value::Span(s)) => K::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => K::Buf(b.clone()),
            _ => K::Other,
        })?;
        match k {
            K::Array(len) => Ok(SeqRef { root: r.root, projs: r.projs, start: 0, len }),
            K::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            K::Buf(b) => {
                let len = buf_len(&b, span);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            K::Other => internal(span, "sequence expected"),
        }
    }

    pub(super) fn seq_of_value(&self, v: Value, span: Span) -> R<SeqRef> {
        match v {
            Value::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            Value::Buf(b) => {
                let len = buf_len(&b, span);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            Value::Array(a) => {
                let len = a.len();
                Ok(SeqRef { root: slot(Value::Array(a)), projs: Vec::new(), start: 0, len })
            }
            _ => internal(span, "sequence expected"),
        }
    }

    pub(super) fn seq_get(&self, s: &SeqRef, i: u32, span: Span) -> R<Value> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        let r = PlaceRef { root: s.root.clone(), projs };
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => internal(span, "dangling sequence"),
        }
    }

    pub(super) fn seq_set(&self, s: &SeqRef, i: u32, v: Value, span: Span) -> R<()> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        self.write(&PlaceRef { root: s.root.clone(), projs }, v, span)
    }

    /// Fast path: the `f32` slice of a sequence, when its storage is `F32`.
    pub(super) fn with_f32_slice<T>(&self, s: &SeqRef, f: impl FnOnce(&mut [f32]) -> T) -> Option<T> {
        let mut v = s.root.borrow_mut();
        match Self::walk_mut(&mut v, &s.projs) {
            Some(LeafMut::Val(Value::Array(ArrayData::F32(xs)))) => {
                let (a, b) = (s.start as usize, (s.start + s.len) as usize);
                Some(f(&mut xs[a..b]))
            }
            _ => None,
        }
    }
}

/// The length of the `Buf` in `b`, whose slot holds an array.
#[track_caller]
fn buf_len(b: &Slot, span: Span) -> u32 {
    match &*b.borrow() {
        Value::Array(a) => a.len(),
        v => mismatch(span, "the array of a `Buf`", v),
    }
}
