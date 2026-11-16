//! The values of the evaluator. An integer is its kind and an `i128` (every kind
//! fits, and so does the exact result of `+`, `-` and a signed `*`), a float is
//! the `f32` or `f64` itself, and the others are what §4 writes.
//!
//! Two values are the same when they have the same bits (§13.4): `-0.0` and
//! `0.0` differ, and any NaN is the same as any other (their sign and payload
//! are not specified, §3.4). The comparison of the language (`==`, IEEE) is
//! [`super::scalar::binary`].

use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{Ty, TyId};

use super::scalar::Fault;
use super::sema_view::View;

/// Each value against the type of its place, and as many places as values.
fn all(vs: &[Value], ts: &[TyId], view: View, env: Option<&Env>) -> Result<bool, Fault> {
    if ts.len() != vs.len() {
        return Ok(false);
    }
    for (v, t) in vs.iter().zip(ts) {
        if !v.agrees_in(view.ty(*t), view, env)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The type arguments a type is written in: the `args` of a `Named(def, args)` for the types of the fields of `def`,
/// each of them written in `outer`. The evaluator's own, as `onsa_sema`'s `Types::subst` takes `&mut self` (it interns
/// the types it makes) and the evaluator reads the tables as they are.
pub(super) struct Env<'e> {
    pub args: &'e [TyId],
    pub outer: Option<&'e Env<'e>>,
}

impl Env<'_> {
    /// `ty` read under `env`: a parameter is followed to its argument, read under the environment around.
    pub fn follow<'a, 'x>(
        view: View<'a>,
        mut ty: &'a Ty,
        mut env: Option<&'x Env<'x>>,
    ) -> (&'a Ty, Option<&'x Env<'x>>) {
        while let (Ty::Param(i), Some(e)) = (ty, env) {
            let Some(arg) = e.args.get(*i as usize) else { break };
            (ty, env) = (view.ty(*arg), e.outer);
        }
        (ty, env)
    }
}
/// The integer types (§4.1) are the table of the checker, not a second one: what the
/// evaluator has of its own is the arithmetic ([`super::scalar`]), not the kinds.
pub use onsa_sema::ty::IntKind;

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
    /// The scalar of a type of the checker; `None` for the types that are not scalars.
    pub fn of(ty: &Ty) -> Option<Scalar> {
        Some(match ty {
            Ty::Int(k) => Scalar::Int(*k),
            Ty::Float(FloatKind::F32) => Scalar::F32,
            Ty::Float(FloatKind::F64) => Scalar::F64,
            Ty::Bool => Scalar::Bool,
            Ty::Char => Scalar::Char,
            Ty::Unit => Scalar::Unit,
            _ => return None,
        })
    }

    /// `T.default()` (§6.3): 0, `+0.0`, `false`, `()`. `Char` has no `Default`.
    pub fn default_value(self) -> Option<Value> {
        Some(match self {
            Scalar::Int(k) => Value::int(k, 0),
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
            Shape::Tuple(fs) => fs.iter().map(Shape::default_value).collect::<Option<_>>().map(Value::tuple),
            Shape::Array(e, n) => Some(Value::Array(vec![e.default_value()?; *n])),
            Shape::Struct(fs) => fs
                .iter()
                .map(|(declared, ty)| declared.clone().or_else(|| ty.default_value()))
                .collect::<Option<_>>()
                .map(Value::Struct),
        }
    }
}

/// Only this file makes one: `Value::int` and `Value::tuple` are the only doors to an integer and a tuple.
#[derive(Clone, Copy, Debug)]
pub struct Seal(());

/// A value of the evaluator. Not `PartialEq`: use [`Value::same`].
#[derive(Clone, Debug)]
pub enum Value {
    Int(IntKind, i128, Seal),
    F32(f32),
    F64(f64),
    Bool(bool),
    Char(char),
    Unit,
    Tuple(Vec<Value>, Seal),
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
    /// An integer of the kind `k`, which holds the value: the checker gives every integer its type, so a value
    /// out of the range is a mistake of the evaluator (a literal, `as`, the host): it stops in release too.
    pub fn int(k: IntKind, v: i128) -> Value {
        assert!((k.range().0..=k.range().1).contains(&v), "{v} is not a value of {}", k.name());
        Value::Int(k, v, Seal(()))
    }

    /// A float of the kind `k` (`x` is already rounded to it when it is an `F32`).
    pub fn float(k: FloatKind, x: f64) -> Value {
        if k == FloatKind::F32 { Value::F32(x as f32) } else { Value::F64(x) }
    }

    /// The tuple of the values. `()` has one form: the tuple of none is `Value::Unit`.
    pub fn tuple(vs: Vec<Value>) -> Value {
        if vs.is_empty() { Value::Unit } else { Value::Tuple(vs, Seal(())) }
    }

    /// The places the value holds: a scalar is one, an aggregate the sum of its parts (one when it has none). What
    /// `[e; N]` makes is bounded by it (`Limits::most`).
    pub fn places(&self) -> usize {
        match self {
            Value::Tuple(vs, _) | Value::Array(vs) | Value::Struct(vs) | Value::Enum { fields: vs, .. } => {
                vs.iter().map(Value::places).sum::<usize>().max(1)
            }
            _ => 1,
        }
    }

    /// Does the value have the type? A scalar by its kind, an aggregate element by element: the length of an array, the
    /// fields of a struct, the number of the variant of an enum and its elements. A table that is not there is
    /// `Unavailable`, not a disagreement.
    pub fn agrees(&self, ty: &Ty, view: View) -> Result<bool, Fault> {
        self.agrees_in(ty, view, None)
    }

    /// `env` holds the type arguments `ty` is written in (the `T` of `Option[T]` is its first); a length that is a
    /// parameter is not checked (a flow has no generic type).
    fn agrees_in(&self, ty: &Ty, view: View, env: Option<&Env>) -> Result<bool, Fault> {
        let (ty, env) = Env::follow(view, ty, env);
        if let Some(s) = Scalar::of(ty) {
            return Ok(match (self, s) {
                (Value::Int(k, ..), Scalar::Int(t)) => *k == t,
                (Value::F32(_), Scalar::F32) | (Value::F64(_), Scalar::F64) | (Value::Bool(_), Scalar::Bool) => true,
                (Value::Char(_), Scalar::Char) | (Value::Unit, Scalar::Unit) => true,
                _ => false,
            });
        }
        match (self, ty) {
            (Value::Tuple(vs, _), Ty::Tuple(ts)) => all(vs, ts, view, env),
            (Value::Array(vs), Ty::Array(t, len)) => {
                if matches!(len, Len::Const(n) if *n as usize != vs.len()) {
                    return Ok(false);
                }
                all(vs, &vec![*t; vs.len()], view, env)
            }
            (Value::Struct(vs), Ty::Named(def, args)) => {
                let fs = view.struct_fields(*def)?;
                all(vs, &fs.iter().map(|f| f.ty).collect::<Vec<_>>(), view, Some(&Env { args, outer: env }))
            }
            (Value::Enum { tag, fields }, Ty::Named(def, args)) => {
                let Some(v) = view.variants(*def)?.get(*tag as usize) else { return Ok(false) };
                all(fields, &v.fields, view, Some(&Env { args, outer: env }))
            }
            _ => Ok(false),
        }
    }

    /// Same bits (§13.4); any NaN is the same as any NaN.
    pub fn same(&self, other: &Value) -> bool {
        fn all(x: &[Value], y: &[Value]) -> bool {
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| p.same(q))
        }
        match (self, other) {
            (Value::Int(k, x, _), Value::Int(l, y, _)) => k == l && x == y,
            (Value::F32(x), Value::F32(y)) => x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()),
            (Value::F64(x), Value::F64(y)) => x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()),
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Char(x), Value::Char(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Tuple(x, _), Value::Tuple(y, _))
            | (Value::Array(x), Value::Array(y))
            | (Value::Struct(x), Value::Struct(y)) => all(x, y),
            (Value::Enum { tag: s, fields: x }, Value::Enum { tag: t, fields: y }) => s == t && all(x, y),
            _ => false,
        }
    }
}
