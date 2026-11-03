//! Primitives: operations the backends provide (spec §3.3, §13.4, S-09, S-12,
//! D-07), and the table of the `std` `target` declarations (S-69 (2)): sema
//! resolves each to its [`Row`] ([`Analysis::prims`]), lowering instantiates
//! it, and every backend says of each [`Prim`], without a `_`, whether it
//! provides it (S-69 (3)).

use std::sync::OnceLock;

use crate::Analysis;
use crate::def::{DefId, DefKind};
use crate::ty::{FloatKind, IntKind, Ty, TyId, Types};

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
    /// Every function, in the order of `std/math.onsa`.
    pub const ALL: [MathFn; 18] = [
        MathFn::Exp,
        MathFn::Exp2,
        MathFn::Log,
        MathFn::Log2,
        MathFn::Sin,
        MathFn::Cos,
        MathFn::Tan,
        MathFn::Tanh,
        MathFn::Pow,
        MathFn::Sqrt,
        MathFn::Floor,
        MathFn::Ceil,
        MathFn::Trunc,
        MathFn::Round,
        MathFn::Fmod,
        MathFn::Abs,
        MathFn::Min,
        MathFn::Max,
    ];

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

/// The bits `to_bits()` gives for every NaN of an `F32`: the positive quiet
/// NaN (spec §3.4, S-106). Every backend reads it from here (plan D-15): the
/// interpreter, and the C backend, which writes it into `onsa.h`.
pub const NAN_BITS_F32: u32 = 0x7FC0_0000;
/// The same for an `F64`.
pub const NAN_BITS_F64: u64 = 0x7FF8_0000_0000_0000;

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
    /// `std.dsp.test.assert_near(a, b, tol)` (interpreter only).
    AssertNear,
    /// A declaration of `std.test` no backend provides until M5.
    Pending(PendingPrim),
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
            Prim::AssertNear | Prim::Pending(_) => match self.std_name() {
                Some(name) => name,
                None => onsa_diag::internal::bug(None, format!("the primitive {self:?} has no row")),
            },
        }
    }

    /// The row of the `std` `target` declaration this primitive instantiates
    /// ([`PrimRow::instantiate`] the other way), without a `_`, so that a new
    /// primitive must say whether a declaration gives it. `None` for the ones
    /// no row gives yet (the members of the `impl`s of std come with their
    /// declarations, W5-02 U4–U6) and the ones Core makes itself.
    pub fn row_prim(&self) -> Option<PrimRow> {
        match self {
            Prim::Math(f, _) => Some(PrimRow::Math(*f)),
            Prim::IntAbs(_) => Some(PrimRow::Math(MathFn::Abs)),
            Prim::IntMin(_) => Some(PrimRow::Math(MathFn::Min)),
            Prim::IntMax(_) => Some(PrimRow::Math(MathFn::Max)),
            Prim::AssertNear => Some(PrimRow::AssertNear),
            Prim::Pending(p) => Some(PrimRow::Pending(*p)),
            Prim::Narrow { .. }
            | Prim::IntToFloat { .. }
            | Prim::FloatToFloat { .. }
            | Prim::TruncToInt { .. }
            | Prim::ToBits(_)
            | Prim::FromBits(_)
            | Prim::Checked(..)
            | Prim::DivEuclid(_)
            | Prim::RemEuclid(_)
            | Prim::IsNan(_)
            | Prim::IsFinite(_)
            | Prim::Len
            | Prim::Slice
            | Prim::Get
            | Prim::Fill
            | Prim::AddFrom
            | Prim::CopyFrom
            | Prim::BufZeroed => None,
        }
    }

    /// The `std` declaration whose primitive this is, by its qualified name
    /// (`std.test.gen.u32`): the E0200 of a backend that does not provide it
    /// names the declaration (spec §15.2). `None` as for [`Prim::row_prim`].
    pub fn std_name(&self) -> Option<String> {
        let prim = self.row_prim()?;
        let found = rows().iter().find(|r| r.prim == prim)?;
        Some(format!("std.{}", found.key))
    }
}

/// The declarations of `std.test` no backend provides until M5 (spec §15.2,
/// S-69, R-79): a use is E0200 wherever it runs or is built.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PendingPrim {
    Check,
    GenF32,
    GenU32,
    GenPair,
}

/// A type argument of a `target` declaration, as its row reads it: a
/// scalar of the numbers, or another type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    Int(IntKind),
    Float(FloatKind),
    Other,
}

impl Scalar {
    /// The type `t` of sema, or `None` while it is open (a type parameter of
    /// a generic body, an inference variable) or holds the error type.
    pub fn of(types: &Types, t: TyId) -> Option<Scalar> {
        if types.open(t) || types.has_error(t) {
            return None;
        }
        Some(match types.get(t) {
            Ty::Int(k) => Scalar::Int(*k),
            Ty::Float(k) => Scalar::Float(*k),
            _ => Scalar::Other,
        })
    }
}

/// The primitive of a `std` `target` declaration before its instantiation
/// (S-69 (2)): the family of [`Prim`]s it stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimRow {
    /// On a float, [`Prim::Math`]; `abs` / `min` / `max` on an integer too.
    Math(MathFn),
    AssertNear,
    /// `array.from_fn`: lowering expands it, it is no [`Prim`].
    FromFn,
    Pending(PendingPrim),
}

impl PrimRow {
    /// The primitive for the type arguments `args` of a use (those of the
    /// declaration, in order); `None` when the row has none for them, and
    /// for [`PrimRow::FromFn`].
    pub fn instantiate(self, args: &[Scalar]) -> Option<Prim> {
        match self {
            PrimRow::Math(f) => match (args, f) {
                ([Scalar::Float(k)], _) => Some(Prim::Math(f, *k)),
                ([Scalar::Int(k)], MathFn::Abs) => Some(Prim::IntAbs(*k)),
                ([Scalar::Int(k)], MathFn::Min) => Some(Prim::IntMin(*k)),
                ([Scalar::Int(k)], MathFn::Max) => Some(Prim::IntMax(*k)),
                _ => None,
            },
            PrimRow::AssertNear => Some(Prim::AssertNear),
            PrimRow::Pending(p) => Some(Prim::Pending(p)),
            PrimRow::FromFn => None,
        }
    }

    /// Whether the compiler gives the declaration at the type arguments
    /// `args`: a primitive, or the expansion of `from_fn`. A use where it
    /// does not is E0200 (spec §15.2).
    pub fn provides(self, args: &[Scalar]) -> bool {
        self == PrimRow::FromFn || self.instantiate(args).is_some()
    }
}

/// One `std` `target` declaration: its key (the module path under `std` and
/// the name, `dsp.test.assert_near`), its primitive, and the number of its
/// parameters and its `rt`, a copy of the declaration (which is the source)
/// that the unit tests check against it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    pub key: String,
    pub prim: PrimRow,
    pub arity: u8,
    pub rt: bool,
}

/// Every row, one per `target` declaration of `std`.
pub fn rows() -> &'static [Row] {
    static ROWS: OnceLock<Vec<Row>> = OnceLock::new();
    ROWS.get_or_init(|| {
        let row = |key: &str, prim, arity, rt| Row { key: key.to_string(), prim, arity, rt };
        let mut v: Vec<Row> = MathFn::ALL
            .iter()
            .map(|&f| row(&format!("math.{}", f.name()), PrimRow::Math(f), f.arity() as u8, true))
            .collect();
        v.extend([
            row("array.from_fn", PrimRow::FromFn, 1, false),
            row("dsp.test.assert_near", PrimRow::AssertNear, 3, false),
            row("test.check", PrimRow::Pending(PendingPrim::Check), 3, false),
            row("test.gen.f32", PrimRow::Pending(PendingPrim::GenF32), 2, false),
            row("test.gen.u32", PrimRow::Pending(PendingPrim::GenU32), 2, false),
            row("test.gen.pair", PrimRow::Pending(PendingPrim::GenPair), 2, false),
        ]);
        v
    })
}

/// The row of the key `key`.
pub fn row(key: &str) -> Option<&'static Row> {
    rows().iter().find(|r| r.key == key)
}

/// The key of the `std` declaration `def` (a free item; the members of the
/// `impl`s of std come with their declarations, W5-02 U4).
pub(crate) fn key_of(a: &Analysis, def: DefId) -> String {
    let d = a.def(def);
    format!("{}.{}", a.modules.get(d.module).path, d.name)
}

/// The row of every `target` declaration of `std`, once after the
/// signatures ([`Analysis::prims`]). One without a row is a disagreement of
/// the compiler and its std (the unit test of the table finds it first). A
/// `target` declaration outside std has none: it is the names stage's E0200
/// (`UserTargets`).
pub(crate) fn record(a: &mut Analysis) {
    for i in 0..a.defs.len() {
        let def = DefId(i as u32);
        let d = a.def(def);
        if !matches!(&d.kind, DefKind::Fn(f) if f.target) || !a.modules.is_std(d.module) {
            continue;
        }
        let key = key_of(a, def);
        let Some(r) = row(&key) else {
            onsa_diag::internal::bug(Some(d.span), format!("the `std` declaration `{key}` has no primitive"))
        };
        a.prims.insert(def, r.prim);
    }
}
