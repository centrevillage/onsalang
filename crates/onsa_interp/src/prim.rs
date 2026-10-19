//! The primitives of Core ([`Prim`]).

use onsa_core::prim::{CheckedOp, MathFn, NAN_BITS_F32, NAN_BITS_F64, Prim};
use onsa_core::{Arg, BinOp, FloatKind, IntKind, Overflow, Ty};
use onsa_diag::Span;

use crate::numeric::{float_of, int_of, math_f32, math_f64, mismatch, none, some, trunc_to_int};
use crate::place::Frame;
use crate::value::{SpanRef, Value, in_range, int_value, slot, zero_array};
use crate::{Interp, R, internal, panic};

impl<'m> Interp<'m> {
    // ------------------------------------------------------------ primitives

    /// A primitive: its arguments, then the operation, in a function of its
    /// own, off the way down a recursion through an argument (R-05).
    pub(super) fn prim(&self, f: &mut Frame, prim: &Prim, args: &[Arg], ty: &Ty, span: Span) -> R<Value> {
        if let Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed =
            prim
        {
            return self.seq_prim(f, prim, args, ty, span);
        }
        let mut vs = Vec::with_capacity(args.len());
        for a in args {
            vs.push(self.eval(f, &a.expr)?);
        }
        self.prim_values(prim, &vs, span)
    }

    /// The primitives that take their receiver as a sequence reference.
    #[inline(never)]
    fn seq_prim(&self, f: &mut Frame, prim: &Prim, args: &[Arg], ty: &Ty, span: Span) -> R<Value> {
        match prim {
            Prim::Len => {
                let s = self.seq_of_arg(f, &args[0])?;
                Ok(Value::U32(s.len))
            }
            Prim::Slice => {
                let s = self.seq_of_arg(f, &args[0])?;
                let from = self.eval_u32(f, &args[1].expr)?;
                let to = self.eval_u32(f, &args[2].expr)?;
                if from > to || to > s.len {
                    return panic(
                        span,
                        format!("slice {from}..{to} is out of range for a sequence of length {}", s.len),
                    );
                }
                Ok(Value::Span(SpanRef { root: s.root, projs: s.projs, start: s.start + from, len: to - from }))
            }
            Prim::Get => {
                let s = self.seq_of_arg(f, &args[0])?;
                let i = self.eval_u32(f, &args[1].expr)?;
                Ok(if i < s.len { some(self.seq_get(&s, i, span)?) } else { none() })
            }
            Prim::Fill => {
                let s = self.seq_of_arg(f, &args[0])?;
                let v = self.eval(f, &args[1].expr)?;
                if let Value::F32(x) = v
                    && self.with_f32_slice(&s, |xs| xs.fill(x)).is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..s.len {
                    self.seq_set(&s, i, v.clone(), span)?;
                }
                Ok(Value::Unit)
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let dst = self.seq_of_arg(f, &args[0])?;
                let src = self.seq_of_arg(f, &args[1])?;
                if dst.len != src.len {
                    return panic(span, format!("span lengths differ: {} and {}", dst.len, src.len));
                }
                let add = *prim == Prim::AddFrom;
                let src_vals: Option<Vec<f32>> = self.with_f32_slice(&src, |xs| xs.to_vec());
                if let Some(sv) = src_vals
                    && self
                        .with_f32_slice(&dst, |xs| {
                            for (d, s) in xs.iter_mut().zip(&sv) {
                                if add {
                                    *d += *s;
                                } else {
                                    *d = *s;
                                }
                            }
                        })
                        .is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..dst.len {
                    let sv = self.seq_get(&src, i, span)?;
                    let nv = if add {
                        self.binary(BinOp::Add, Overflow::Checked, self.seq_get(&dst, i, span)?, sv, span)?
                    } else {
                        sv
                    };
                    self.seq_set(&dst, i, nv, span)?;
                }
                Ok(Value::Unit)
            }
            Prim::BufZeroed => {
                let n = self.eval_u32(f, &args[0].expr)?;
                let elem = match ty {
                    Ty::Buf(e) => (**e).clone(),
                    _ => internal(span, "Buf.zeroed type"),
                };
                Ok(Value::Buf(slot(Value::Array(zero_array(self.m, &elem, n)))))
            }
            _ => internal(span, "not a sequence primitive"),
        }
    }

    /// A primitive on the values of its arguments. Each operand has the type
    /// the primitive names, or the interpreter stops with an internal error
    /// (R-92 (1)).
    #[inline(never)]
    fn prim_values(&self, prim: &Prim, vs: &[Value], span: Span) -> R<Value> {
        match prim {
            Prim::Math(mf, k) => self.math(prim, *mf, *k, vs, span),
            Prim::IntAbs(k) => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *k, span);
                let r = x.abs();
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in `abs({x})`"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IntMin(k) | Prim::IntMax(k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                Ok(int_value(*k, if matches!(prim, Prim::IntMin(_)) { x.min(y) } else { x.max(y) }))
            }
            Prim::Narrow { from, to } => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *from, span);
                Ok(if in_range(*to, x) { some(int_value(*to, x)) } else { none() })
            }
            Prim::IntToFloat { from, to } => {
                let [a] = args(prim, vs, span);
                let x = int_of(a, *from, span);
                // Round to nearest, ties to even (§3.3): Rust's `as` from an integer.
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x as f64),
                })
            }
            Prim::FloatToFloat { from, to } => {
                let [a] = args(prim, vs, span);
                let x = float_of(a, *from, span);
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x),
                })
            }
            Prim::TruncToInt { from, to, sat } => {
                let [a] = args(prim, vs, span);
                Ok(int_value(*to, trunc_to_int(float_of(a, *from, span), *from, *to, *sat, span)?))
            }
            Prim::ToBits(k) => {
                let [a] = args(prim, vs, span);
                // A NaN reads as the positive quiet NaN (spec §3.4, S-106).
                Ok(match (k, a) {
                    (FloatKind::F32, Value::F32(x)) => Value::U32(if x.is_nan() { NAN_BITS_F32 } else { x.to_bits() }),
                    (FloatKind::F64, Value::F64(x)) => Value::U64(if x.is_nan() { NAN_BITS_F64 } else { x.to_bits() }),
                    _ => mismatch(span, &format!("an `{}`", k.name()), a),
                })
            }
            Prim::FromBits(k) => {
                let [a] = args(prim, vs, span);
                Ok(match k {
                    FloatKind::F32 => Value::F32(f32::from_bits(int_of(a, IntKind::U32, span) as u32)),
                    FloatKind::F64 => Value::F64(f64::from_bits(int_of(a, IntKind::U64, span) as u64)),
                })
            }
            Prim::Checked(op, k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                let r = match op {
                    CheckedOp::Add => x.checked_add(y),
                    CheckedOp::Sub => x.checked_sub(y),
                    CheckedOp::Mul => x.checked_mul(y),
                    CheckedOp::Div => (y != 0).then(|| x / y),
                };
                Ok(match r {
                    Some(r) if in_range(*k, r) => some(int_value(*k, r)),
                    _ => none(),
                })
            }
            Prim::DivEuclid(k) | Prim::RemEuclid(k) => {
                let [a, b] = args(prim, vs, span);
                let (x, y) = (int_of(a, *k, span), int_of(b, *k, span));
                if y == 0 {
                    return panic(span, "division by zero");
                }
                // `MIN.rem_euclid(-1)` is 0; `MIN.div_euclid(-1)` does not fit (§3.4).
                let r = if matches!(prim, Prim::DivEuclid(_)) { x.div_euclid(y) } else { x.rem_euclid(y) };
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in euclidean division of {x} by {y}"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IsNan(k) => {
                let [a] = args(prim, vs, span);
                Ok(Value::Bool(float_of(a, *k, span).is_nan()))
            }
            Prim::IsFinite(k) => {
                let [a] = args(prim, vs, span);
                Ok(Value::Bool(float_of(a, *k, span).is_finite()))
            }
            Prim::Std(name) => self.std_prim(prim, name, vs, span),
            Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed => {
                internal(span, format!("the sequence primitive `{}` on values", prim.name()))
            }
        }
    }

    fn math(&self, prim: &Prim, mf: MathFn, k: FloatKind, vs: &[Value], span: Span) -> R<Value> {
        let (x, y) = if mf.arity() == 2 {
            let [a, b] = args(prim, vs, span);
            (float_of(a, k, span), float_of(b, k, span))
        } else {
            let [a] = args(prim, vs, span);
            (float_of(a, k, span), 0.0)
        };
        // An `F32` operand is exact as an `f64`, and back.
        Ok(match k {
            FloatKind::F32 => Value::F32(math_f32(mf, x as f32, y as f32)),
            FloatKind::F64 => Value::F64(math_f64(mf, x, y)),
        })
    }
}

/// The `N` operands of `prim` (an internal error for another number).
#[track_caller]
pub(super) fn args<'v, const N: usize>(prim: &Prim, vs: &'v [Value], span: Span) -> &'v [Value; N] {
    match vs.try_into() {
        Ok(a) => a,
        Err(_) => internal(span, format!("`{}` given {} operands, not {N}", prim.name(), vs.len())),
    }
}
