//! The values of the evaluator. An integer is its kind and an `i128` (every kind
//! fits, and so does the exact result of `+`, `-` and a signed `*`), a float is
//! the `f32` or `f64` itself, and the others are what §4 writes.
//!
//! Two values are the same when they have the same bits (§13.4): `-0.0` and
//! `0.0` differ, and any NaN is the same as any other (their sign and payload
//! are not specified, §3.4). The comparison of the language (`==`, IEEE) is
//! [`super::scalar::binary`].

/// The integer types (§4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntKind {
    pub fn bits(self) -> u32 {
        match self {
            IntKind::I8 | IntKind::U8 => 8,
            IntKind::I16 | IntKind::U16 => 16,
            IntKind::I32 | IntKind::U32 => 32,
            IntKind::I64 | IntKind::U64 => 64,
        }
    }

    pub fn signed(self) -> bool {
        matches!(self, IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64)
    }

    pub fn min(self) -> i128 {
        if self.signed() { -(1i128 << (self.bits() - 1)) } else { 0 }
    }

    pub fn max(self) -> i128 {
        if self.signed() { (1i128 << (self.bits() - 1)) - 1 } else { (1i128 << self.bits()) - 1 }
    }
}

/// The scalar types, the ones `as` converts between and `Default` is given for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scalar {
    Int(IntKind),
    F32,
    F64,
    Bool,
    Char,
    Unit,
}

impl Scalar {
    /// `T.default()` (§6.3): 0, `+0.0`, `false`, `()`. `Char` has no `Default`.
    pub fn default_value(self) -> Option<Value> {
        Some(match self {
            Scalar::Int(k) => Value::Int(k, 0),
            Scalar::F32 => Value::F32(0.0),
            Scalar::F64 => Value::F64(0.0),
            Scalar::Bool => Value::Bool(false),
            Scalar::Unit => Value::Unit,
            Scalar::Char => return None,
        })
    }
}

/// A type as far as its default needs it (§6.4).
#[derive(Clone, Debug)]
pub enum Shape {
    Scalar(Scalar),
    Tuple(Vec<Shape>),
    Array(Box<Shape>, usize),
    /// Per field: the value its declaration gives (`y: F32 = 0.5`), and its type.
    Struct(Vec<(Option<Value>, Shape)>),
}

impl Shape {
    /// The default of the type: elementwise for tuples and arrays, and for a struct
    /// the declared value of a field or else the default of its type. `None` when a
    /// type that is needed has no `Default` (E0816 in a flow).
    pub fn default_value(&self) -> Option<Value> {
        match self {
            Shape::Scalar(s) => s.default_value(),
            Shape::Tuple(fs) => fs.iter().map(Shape::default_value).collect::<Option<_>>().map(Value::Tuple),
            Shape::Array(e, n) => Some(Value::Array(vec![e.default_value()?; *n])),
            Shape::Struct(fs) => fs
                .iter()
                .map(|(declared, ty)| declared.clone().or_else(|| ty.default_value()))
                .collect::<Option<_>>()
                .map(Value::Struct),
        }
    }
}

/// A value of the evaluator. Not `PartialEq`: use [`Value::same`].
#[derive(Clone, Debug)]
pub enum Value {
    Int(IntKind, i128),
    F32(f32),
    F64(f64),
    Bool(bool),
    Char(char),
    Unit,
    Tuple(Vec<Value>),
    Array(Vec<Value>),
    /// The fields in the order of the declaration.
    Struct(Vec<Value>),
    /// The variant by its number in the declaration, and its elements.
    Enum {
        tag: u32,
        fields: Vec<Value>,
    },
}

impl Value {
    /// Same bits (§13.4); any NaN is the same as any NaN.
    pub fn same(&self, other: &Value) -> bool {
        fn all(x: &[Value], y: &[Value]) -> bool {
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| p.same(q))
        }
        match (self, other) {
            (Value::Int(k, x), Value::Int(l, y)) => k == l && x == y,
            (Value::F32(x), Value::F32(y)) => x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()),
            (Value::F64(x), Value::F64(y)) => x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()),
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Char(x), Value::Char(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Tuple(x), Value::Tuple(y))
            | (Value::Array(x), Value::Array(y))
            | (Value::Struct(x), Value::Struct(y)) => all(x, y),
            (Value::Enum { tag: s, fields: x }, Value::Enum { tag: t, fields: y }) => s == t && all(x, y),
            _ => false,
        }
    }
}
