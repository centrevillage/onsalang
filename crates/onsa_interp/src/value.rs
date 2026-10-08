//! Runtime values of the interpreter (T3-7).
//!
//! Values have value semantics: cloning an `Array` / `Struct` copies it.
//! The two reference-like kinds are `Buf` (a heap buffer, Affine, D-08) and
//! `Span` (a view over an array place or a buffer, §5.3). Both point at a
//! [`Slot`], the shared cell every local and every buffer lives in, so a
//! `Span` stays valid for as long as the interpreter keeps the slot alive.

use std::cell::RefCell;
use std::rc::Rc;

use onsa_core::{FloatKind, FnId, IntKind, Module, Ty, TypeDefKind};

/// A storage cell: one per local binding and one per `Buf`.
pub type Slot = Rc<RefCell<Value>>;

pub fn slot(v: Value) -> Slot {
    Rc::new(RefCell::new(v))
}

/// One step into an aggregate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Proj {
    /// Struct field, tuple element, or enum payload field by position.
    Field(u32),
    /// Array element (already bounds-checked and offset for spans).
    Index(u32),
}

/// A view over `len` elements of the array found at `root` + `projs`,
/// starting at `start` (spec §5.3).
#[derive(Debug, Clone)]
pub struct SpanRef {
    pub root: Slot,
    pub projs: Vec<Proj>,
    pub start: u32,
    pub len: u32,
}

/// Array storage; `F32` is the fast path for signal buffers.
#[derive(Debug, Clone)]
pub enum ArrayData {
    F32(Vec<f32>),
    Any(Vec<Value>),
}

impl ArrayData {
    pub fn len(&self) -> u32 {
        match self {
            ArrayData::F32(v) => v.len() as u32,
            ArrayData::Any(v) => v.len() as u32,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, i: u32) -> Value {
        match self {
            ArrayData::F32(v) => Value::F32(v[i as usize]),
            ArrayData::Any(v) => v[i as usize].clone(),
        }
    }

    pub fn set(&mut self, i: u32, v: Value) {
        match self {
            ArrayData::F32(xs) => xs[i as usize] = f32_element(&v),
            ArrayData::Any(xs) => xs[i as usize] = v,
        }
    }

    pub fn from_values(elem: &Ty, vs: Vec<Value>) -> ArrayData {
        if *elem == Ty::Float(FloatKind::F32) {
            ArrayData::F32(vs.iter().map(f32_element).collect())
        } else {
            ArrayData::Any(vs)
        }
    }
}

/// An element of an `F32` array: an `F32`, or an internal error (R-92 (1)).
#[track_caller]
fn f32_element(v: &Value) -> f32 {
    match v {
        Value::F32(x) => *x,
        _ => onsa_diag::internal::bug(None, format!("a value that is not an `F32` in an `F32` array: {v:?}")),
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    F32(f32),
    F64(f64),
    Bool(bool),
    Char(char),
    Unit,
    Array(ArrayData),
    Tuple(Vec<Value>),
    Struct(Vec<Value>),
    Enum {
        tag: u32,
        fields: Vec<Value>,
    },
    Span(SpanRef),
    /// The slot holds a `Value::Array`.
    Buf(Slot),
    Fn(FnId),
}

impl Value {
    pub fn as_f32(&self) -> Option<f32> {
        match self {
            Value::F32(x) => Some(*x),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::F64(x) => Some(*x),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_u32(&self) -> Option<u32> {
        match self {
            Value::U32(x) => Some(*x),
            _ => None,
        }
    }

    /// Any integer as `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        Some(match self {
            Value::I8(x) => *x as i128,
            Value::I16(x) => *x as i128,
            Value::I32(x) => *x as i128,
            Value::I64(x) => *x as i128,
            Value::U8(x) => *x as i128,
            Value::U16(x) => *x as i128,
            Value::U32(x) => *x as i128,
            Value::U64(x) => *x as i128,
            _ => return None,
        })
    }

    pub fn int_kind(&self) -> Option<IntKind> {
        Some(match self {
            Value::I8(_) => IntKind::I8,
            Value::I16(_) => IntKind::I16,
            Value::I32(_) => IntKind::I32,
            Value::I64(_) => IntKind::I64,
            Value::U8(_) => IntKind::U8,
            Value::U16(_) => IntKind::U16,
            Value::U32(_) => IntKind::U32,
            Value::U64(_) => IntKind::U64,
            _ => return None,
        })
    }

    /// The `f32` samples of a `Buf[F32]` or `[F32; N]` (tests and tools).
    pub fn f32_samples(&self) -> Option<Vec<f32>> {
        match self {
            Value::Array(ArrayData::F32(v)) => Some(v.clone()),
            Value::Array(ArrayData::Any(v)) => v.iter().map(|x| x.as_f32()).collect(),
            Value::Buf(s) => s.borrow().f32_samples(),
            _ => None,
        }
    }

    /// Fields of a struct value.
    pub fn struct_fields(&self) -> Option<&[Value]> {
        match self {
            Value::Struct(f) => Some(f),
            _ => None,
        }
    }
}

/// Range of an integer kind as `(min, max)`.
pub fn int_range(k: IntKind) -> (i128, i128) {
    match k {
        IntKind::I8 => (i8::MIN as i128, i8::MAX as i128),
        IntKind::I16 => (i16::MIN as i128, i16::MAX as i128),
        IntKind::I32 => (i32::MIN as i128, i32::MAX as i128),
        IntKind::I64 => (i64::MIN as i128, i64::MAX as i128),
        IntKind::U8 => (0, u8::MAX as i128),
        IntKind::U16 => (0, u16::MAX as i128),
        IntKind::U32 => (0, u32::MAX as i128),
        IntKind::U64 => (0, u64::MAX as i128),
    }
}

pub fn in_range(k: IntKind, v: i128) -> bool {
    let (lo, hi) = int_range(k);
    lo <= v && v <= hi
}

/// Two's complement wraparound into the kind's range.
pub fn wrap_int(k: IntKind, v: i128) -> i128 {
    let bits = k.bits();
    let m = v.rem_euclid(1i128 << bits);
    let (_, hi) = int_range(k);
    if m > hi { m - (1i128 << bits) } else { m }
}

pub fn clamp_int(k: IntKind, v: i128) -> i128 {
    let (lo, hi) = int_range(k);
    v.clamp(lo, hi)
}

/// Build a value of kind `k` from an in-range `i128`.
pub fn int_value(k: IntKind, v: i128) -> Value {
    match k {
        IntKind::I8 => Value::I8(v as i8),
        IntKind::I16 => Value::I16(v as i16),
        IntKind::I32 => Value::I32(v as i32),
        IntKind::I64 => Value::I64(v as i64),
        IntKind::U8 => Value::U8(v as u8),
        IntKind::U16 => Value::U16(v as u16),
        IntKind::U32 => Value::U32(v as u32),
        IntKind::U64 => Value::U64(v as u64),
    }
}

/// The zero value of a type (`ExprKind::Zeroed`): numbers 0, `false`,
/// `'\0'`, zeroed aggregates, enums at tag 0 with a zeroed payload, empty
/// buffers and spans.
pub fn zero(m: &Module, ty: &Ty) -> Value {
    match ty {
        Ty::Int(k) => int_value(*k, 0),
        Ty::Float(FloatKind::F32) => Value::F32(0.0),
        Ty::Float(FloatKind::F64) => Value::F64(0.0),
        Ty::Bool => Value::Bool(false),
        Ty::Char => Value::Char('\0'),
        Ty::Unit => Value::Unit,
        Ty::Array(e, n) => Value::Array(zero_array(m, e, *n)),
        Ty::Tuple(ts) => Value::Tuple(ts.iter().map(|t| zero(m, t)).collect()),
        Ty::Struct(id) => match &m.ty(*id).kind {
            TypeDefKind::Struct { fields } => Value::Struct(fields.iter().map(|(_, t)| zero(m, t)).collect()),
            _ => onsa_diag::internal::bug(None, "the zero value of a struct type whose definition is not a struct"),
        },
        Ty::Enum(id) => match &m.ty(*id).kind {
            TypeDefKind::Enum { variants } => Value::Enum {
                tag: 0,
                fields: variants.first().map(|(_, ts)| ts.iter().map(|t| zero(m, t)).collect()).unwrap_or_default(),
            },
            _ => onsa_diag::internal::bug(None, "the zero value of an enum type whose definition is not an enum"),
        },
        Ty::Span(e) => {
            Value::Span(SpanRef { root: slot(Value::Array(zero_array(m, e, 0))), projs: Vec::new(), start: 0, len: 0 })
        }
        Ty::Buf(e) => Value::Buf(slot(Value::Array(zero_array(m, e, 0)))),
        Ty::FnPtr(_) => Value::Fn(FnId(u32::MAX)),
    }
}

pub fn zero_array(m: &Module, elem: &Ty, n: u32) -> ArrayData {
    if *elem == Ty::Float(FloatKind::F32) {
        ArrayData::F32(vec![0.0; n as usize])
    } else {
        ArrayData::Any((0..n).map(|_| zero(m, elem)).collect())
    }
}

/// Human-readable form for panic messages and test reports.
pub fn show(v: &Value) -> String {
    match v {
        Value::I8(x) => x.to_string(),
        Value::I16(x) => x.to_string(),
        Value::I32(x) => x.to_string(),
        Value::I64(x) => x.to_string(),
        Value::U8(x) => x.to_string(),
        Value::U16(x) => x.to_string(),
        Value::U32(x) => x.to_string(),
        Value::U64(x) => x.to_string(),
        Value::F32(x) => format!("{x:?}"),
        Value::F64(x) => format!("{x:?}"),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => format!("{c:?}"),
        Value::Unit => "()".into(),
        Value::Array(ArrayData::F32(xs)) => format!("[F32; {}]", xs.len()),
        Value::Array(ArrayData::Any(xs)) => format!("[{}]", xs.iter().map(show).collect::<Vec<_>>().join(", ")),
        Value::Tuple(xs) => format!("({})", xs.iter().map(show).collect::<Vec<_>>().join(", ")),
        Value::Struct(xs) => format!("{{ {} }}", xs.iter().map(show).collect::<Vec<_>>().join(", ")),
        Value::Enum { tag, fields } => {
            format!("#{tag}({})", fields.iter().map(show).collect::<Vec<_>>().join(", "))
        }
        Value::Span(s) => format!("Span[{}..{}]", s.start, s.start + s.len),
        Value::Buf(b) => format!("Buf[{}]", b.borrow().f32_samples().map(|v| v.len()).unwrap_or(0)),
        Value::Fn(f) => format!("fn#{}", f.0),
    }
}
