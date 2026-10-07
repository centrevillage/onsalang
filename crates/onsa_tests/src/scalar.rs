//! The scalar types of the export boundary (spec §11.6, §14.2) as the tools
//! that drive the generated C hold them: the bytes a C program reads and
//! writes (little-endian, as C holds them), and the
//! comparison of spec §13.4. One codec for the conformance harness
//! ([`crate::conformance`]) and the host steps ([`crate::host`]).

use onsa_core::{FloatKind, IntKind, Ty};
use onsa_interp::Value;
use onsa_interp::value::int_value;

/// A scalar type of the boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    F32,
    F64,
    Int(IntKind),
    Bool,
    Char,
}

impl Scalar {
    pub fn of(ty: &Ty) -> Option<Scalar> {
        Some(match ty {
            Ty::Float(FloatKind::F32) => Scalar::F32,
            Ty::Float(FloatKind::F64) => Scalar::F64,
            Ty::Int(k) => Scalar::Int(*k),
            Ty::Bool => Scalar::Bool,
            Ty::Char => Scalar::Char,
            _ => return None,
        })
    }

    pub fn ty(self) -> Ty {
        match self {
            Scalar::F32 => Ty::Float(FloatKind::F32),
            Scalar::F64 => Ty::Float(FloatKind::F64),
            Scalar::Int(k) => Ty::Int(k),
            Scalar::Bool => Ty::Bool,
            Scalar::Char => Ty::Char,
        }
    }

    /// The Onsa name (`F32`, `U8`), for messages: as Core prints the type.
    pub fn name(self) -> String {
        onsa_core::dump::type_name(&onsa_core::Module::default(), &self.ty())
    }

    pub fn size(self) -> usize {
        match self {
            Scalar::F32 | Scalar::Char => 4,
            Scalar::F64 => 8,
            Scalar::Int(k) => k.bits() as usize / 8,
            Scalar::Bool => 1,
        }
    }

    pub fn zero(self) -> Value {
        match self {
            Scalar::F32 => Value::F32(0.0),
            Scalar::F64 => Value::F64(0.0),
            Scalar::Int(k) => int_value(k, 0),
            Scalar::Bool => Value::Bool(false),
            Scalar::Char => Value::Char('\0'),
        }
    }

    /// The little-endian bytes of `v` (of this type), as C holds it.
    pub fn bytes(self, v: &Value, out: &mut Vec<u8>) {
        match (self, v) {
            (Scalar::F32, Value::F32(x)) => out.extend(x.to_le_bytes()),
            (Scalar::F64, Value::F64(x)) => out.extend(x.to_le_bytes()),
            (Scalar::Bool, Value::Bool(b)) => out.push(*b as u8),
            (Scalar::Char, Value::Char(c)) => out.extend((*c as u32).to_le_bytes()),
            (Scalar::Int(k), v) => {
                let n = v.to_i128().expect("an integer value");
                out.extend(&n.to_le_bytes()[..k.bits() as usize / 8]);
            }
            (s, v) => panic!("a {s:?} value expected, got {v:?}"),
        }
    }

    /// The value of `b` (`self.size()` bytes, little-endian).
    pub fn read(self, b: &[u8]) -> Result<Value, String> {
        let mut w = [0u8; 16];
        w[..b.len()].copy_from_slice(b);
        Ok(match self {
            Scalar::F32 => Value::F32(f32::from_le_bytes([b[0], b[1], b[2], b[3]])),
            Scalar::F64 => Value::F64(f64::from_le_bytes(w[..8].try_into().expect("8 bytes"))),
            Scalar::Bool => match b[0] {
                0 => Value::Bool(false),
                1 => Value::Bool(true),
                x => return Err(format!("a `bool` byte {x} (neither 0 nor 1)")),
            },
            Scalar::Char => {
                let u = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
                Value::Char(char::from_u32(u).ok_or_else(|| format!("a `Char` {u:#x} that is not a scalar value"))?)
            }
            Scalar::Int(k) => {
                let raw = u128::from_le_bytes(w) as i128;
                let bits = k.bits();
                // Sign-extend from the width of the kind.
                let n = if k.signed() && raw >> (bits - 1) & 1 == 1 { raw - (1i128 << bits) } else { raw };
                int_value(k, n)
            }
        })
    }
}

/// Whether two outputs are the same sample: bit for bit, NaNs equal
/// (§13.4); the ULP distance of two floats otherwise.
pub fn distance(a: &Value, b: &Value) -> Option<u64> {
    match (a, b) {
        (Value::F32(x), Value::F32(y)) if x.is_nan() && y.is_nan() => Some(0),
        (Value::F64(x), Value::F64(y)) if x.is_nan() && y.is_nan() => Some(0),
        (Value::F32(x), Value::F32(y)) => Some((x.to_bits() as i64 - y.to_bits() as i64).unsigned_abs()),
        (Value::F64(x), Value::F64(y)) => {
            Some(u64::try_from((x.to_bits() as i128 - y.to_bits() as i128).unsigned_abs()).unwrap_or(u64::MAX))
        }
        (a, b) => {
            let same = match (a, b) {
                (Value::Bool(x), Value::Bool(y)) => x == y,
                (Value::Char(x), Value::Char(y)) => x == y,
                _ => a.to_i128().is_some() && a.to_i128() == b.to_i128() && a.int_kind() == b.int_kind(),
            };
            if same { Some(0) } else { None }
        }
    }
}

/// A value with its bits, for messages: `2.0 (0x40000000)`.
pub fn show(v: &Value) -> String {
    match v {
        Value::F32(x) => format!("{x:?} ({:#010x})", x.to_bits()),
        Value::F64(x) => format!("{x:?} ({:#018x})", x.to_bits()),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => format!("{c:?} (U+{:04X})", *c as u32),
        v => match v.to_i128() {
            Some(n) => n.to_string(),
            None => format!("{v:?}"),
        },
    }
}
