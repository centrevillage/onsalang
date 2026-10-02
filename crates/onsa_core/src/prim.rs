//! Primitives: operations the backends provide (spec §3.3, §13.4, S-09, S-12,
//! D-07). Every backend keeps a table over this enum; a missing entry is a
//! test failure there, not a silent fallback.

use crate::ir::{FloatKind, IntKind};

/// `std.math` functions (`target rt fn`, generic over `Float`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MathFn {
    Exp,
    Exp2,
    Log,
    Log2,
    Sin,
    Cos,
    Tan,
    Tanh,
    Pow,
    Sqrt,
    Floor,
    Ceil,
    Trunc,
    Round,
    Abs,
    Min,
    Max,
    Fmod,
}

impl MathFn {
    pub fn parse(name: &str) -> Option<MathFn> {
        Some(match name {
            "exp" => MathFn::Exp,
            "exp2" => MathFn::Exp2,
            "log" => MathFn::Log,
            "log2" => MathFn::Log2,
            "sin" => MathFn::Sin,
            "cos" => MathFn::Cos,
            "tan" => MathFn::Tan,
            "tanh" => MathFn::Tanh,
            "pow" => MathFn::Pow,
            "sqrt" => MathFn::Sqrt,
            "floor" => MathFn::Floor,
            "ceil" => MathFn::Ceil,
            "trunc" => MathFn::Trunc,
            "round" => MathFn::Round,
            "abs" => MathFn::Abs,
            "min" => MathFn::Min,
            "max" => MathFn::Max,
            "fmod" => MathFn::Fmod,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            MathFn::Exp => "exp",
            MathFn::Exp2 => "exp2",
            MathFn::Log => "log",
            MathFn::Log2 => "log2",
            MathFn::Sin => "sin",
            MathFn::Cos => "cos",
            MathFn::Tan => "tan",
            MathFn::Tanh => "tanh",
            MathFn::Pow => "pow",
            MathFn::Sqrt => "sqrt",
            MathFn::Floor => "floor",
            MathFn::Ceil => "ceil",
            MathFn::Trunc => "trunc",
            MathFn::Round => "round",
            MathFn::Abs => "abs",
            MathFn::Min => "min",
            MathFn::Max => "max",
            MathFn::Fmod => "fmod",
        }
    }

    pub fn arity(self) -> usize {
        match self {
            MathFn::Pow | MathFn::Min | MathFn::Max | MathFn::Fmod => 2,
            _ => 1,
        }
    }

    /// Bit-exact on every target (correctly rounded or exact, §13.4); the
    /// others are transcendental and match within the precision target.
    pub fn is_exact(self) -> bool {
        matches!(
            self,
            MathFn::Sqrt
                | MathFn::Floor
                | MathFn::Ceil
                | MathFn::Trunc
                | MathFn::Round
                | MathFn::Abs
                | MathFn::Min
                | MathFn::Max
                | MathFn::Fmod
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckedOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Prim {
    /// `std.math` on `F32` / `F64`.
    Math(MathFn, FloatKind),
    /// `abs` / `min` / `max` on integers (`abs`: signed only, checked).
    IntAbs(IntKind),
    IntMin(IntKind),
    IntMax(IntKind),
    /// `x.narrow_i32()` -> `Option[I32]`.
    Narrow {
        from: IntKind,
        to: IntKind,
    },
    /// `x.round_f32()` / `x.round_f64()` from an integer (round to nearest even).
    IntToFloat {
        from: IntKind,
        to: FloatKind,
    },
    /// `x.round_f32()` on `F64` (and the identity on the same kind).
    FloatToFloat {
        from: FloatKind,
        to: FloatKind,
    },
    /// `x.trunc_i32()` (panics out of range) / `x.trunc_i32_sat()` (saturates, NaN -> 0).
    TruncToInt {
        from: FloatKind,
        to: IntKind,
        sat: bool,
    },
    ToBits(FloatKind),
    FromBits(FloatKind),
    /// `x.checked_add(y)` -> `Option[T]`.
    Checked(CheckedOp, IntKind),
    DivEuclid(IntKind),
    RemEuclid(IntKind),
    IsNan(FloatKind),
    IsFinite(FloatKind),
    /// `xs.len()` of a `Span` / `Buf` (arrays fold to a literal).
    Len,
    /// `xs.slice(from, to)` -> `Span` (panics when out of range).
    Slice,
    /// `xs.get(i)` -> `Option[T]`.
    Get,
    /// `xs.fill!(v)` (`inout` receiver).
    Fill,
    /// `xs.add_from!(other)` (`inout` receiver, `other: Span`).
    AddFrom,
    /// `xs.copy_from!(other)`.
    CopyFrom,
    /// `Buf.zeroed(n)` -> `Buf[T]` (needs `Alloc`; interpreter only).
    BufZeroed,
    /// Any other `std` `target fn`, by qualified name (`std.dsp.test.impulse`).
    Std(String),
}

impl Prim {
    /// Name for the dump and for backend tables.
    pub fn name(&self) -> String {
        match self {
            Prim::Math(f, k) => format!("math.{}.{}", f.name(), k.name()),
            Prim::IntAbs(k) => format!("abs.{}", k.name()),
            Prim::IntMin(k) => format!("min.{}", k.name()),
            Prim::IntMax(k) => format!("max.{}", k.name()),
            Prim::Narrow { from, to } => format!("narrow.{}.{}", from.name(), to.name()),
            Prim::IntToFloat { from, to } => format!("round.{}.{}", from.name(), to.name()),
            Prim::FloatToFloat { from, to } => format!("round.{}.{}", from.name(), to.name()),
            Prim::TruncToInt { from, to, sat } => {
                format!("trunc{}.{}.{}", if *sat { "_sat" } else { "" }, from.name(), to.name())
            }
            Prim::ToBits(k) => format!("to_bits.{}", k.name()),
            Prim::FromBits(k) => format!("from_bits.{}", k.name()),
            Prim::Checked(op, k) => format!(
                "checked_{}.{}",
                match op {
                    CheckedOp::Add => "add",
                    CheckedOp::Sub => "sub",
                    CheckedOp::Mul => "mul",
                    CheckedOp::Div => "div",
                },
                k.name()
            ),
            Prim::DivEuclid(k) => format!("div_euclid.{}", k.name()),
            Prim::RemEuclid(k) => format!("rem_euclid.{}", k.name()),
            Prim::IsNan(k) => format!("is_nan.{}", k.name()),
            Prim::IsFinite(k) => format!("is_finite.{}", k.name()),
            Prim::Len => "len".into(),
            Prim::Slice => "slice".into(),
            Prim::Get => "get".into(),
            Prim::Fill => "fill".into(),
            Prim::AddFrom => "add_from".into(),
            Prim::CopyFrom => "copy_from".into(),
            Prim::BufZeroed => "buf.zeroed".into(),
            Prim::Std(name) => name.clone(),
        }
    }
}
