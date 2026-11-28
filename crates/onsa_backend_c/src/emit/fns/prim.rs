//! The primitives, and the spans they take.

use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    /// The `(Bool, T)` of `narrow_parts` or `add_parts` (and the others), of
    /// the type `ty`: `call` of the out-parameter is the runtime's function,
    /// which says whether the result is defined and writes it only then, so
    /// nothing undefined is computed (R-10) and the result is 0 when not.
    fn parts(&mut self, ty: CTy, k: IntKind, call: impl FnOnce(&str) -> String) -> String {
        let tn = self.cx.names.name(ty);
        let (r, rc) = self.temp(Types::int(k));
        let (ok, okc) = self.temp(Types::BOOL);
        self.line(&format!("{rc} {r} = 0;"));
        self.line(&format!("{okc} {ok} = {};", call(&r)));
        format!("(({tn}){{ .f0 = {ok}, .f1 = {r} }})")
    }

    pub(super) fn prim(&mut self, prim: &Prim, args: &[onsa_core::Arg], e: &Expr) -> R<String> {
        let loc = self.loc(e.span);
        let refs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        match prim {
            Prim::Math(f, k) => {
                let vs = self.operands(&refs)?;
                let (a, b) = (vs[0].clone(), vs.get(1).cloned().unwrap_or_default());
                let sfx = match k {
                    FloatKind::F32 => "f",
                    FloatKind::F64 => "",
                };
                let t = float_tag(*k);
                Ok(match f {
                    MathFn::Exp => format!("exp{sfx}({a})"),
                    MathFn::Exp2 => format!("exp2{sfx}({a})"),
                    MathFn::Log => format!("log{sfx}({a})"),
                    MathFn::Log2 => format!("log2{sfx}({a})"),
                    MathFn::Sin => format!("sin{sfx}({a})"),
                    MathFn::Cos => format!("cos{sfx}({a})"),
                    MathFn::Tan => format!("tan{sfx}({a})"),
                    MathFn::Tanh => format!("tanh{sfx}({a})"),
                    MathFn::Pow => format!("pow{sfx}({a}, {b})"),
                    MathFn::Sqrt => format!("sqrt{sfx}({a})"),
                    MathFn::Floor => format!("floor{sfx}({a})"),
                    MathFn::Ceil => format!("ceil{sfx}({a})"),
                    MathFn::Trunc => format!("trunc{sfx}({a})"),
                    MathFn::Round => format!("onsa_round_{t}({a})"),
                    MathFn::Abs => format!("fabs{sfx}({a})"),
                    MathFn::Min => format!("onsa_fmin_{t}({a}, {b})"),
                    MathFn::Max => format!("onsa_fmax_{t}({a}, {b})"),
                    MathFn::Fmod => format!("onsa_fmod_{t}({a}, {b})"),
                })
            }
            Prim::IntAbs(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_abs_{}({}, {loc})", int_tag(*k), vs[0]))
            }
            Prim::IntMin(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_min_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IntMax(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_max_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::NarrowParts { from, to } => {
                // The range check is the runtime's (ONSA_DEFINE_NARROW): no comparison
                // that the types decide, none of a signed and an unsigned value (R-11, R-145).
                let vs = self.operands(&refs)?;
                let (f, t) = (int_tag(*from), int_tag(*to));
                Ok(self.parts(e.ty, *to, |r| format!("onsa_narrow_{f}_{t}({}, &{r})", vs[0])))
            }
            Prim::IntToFloat { to, .. } | Prim::FloatToFloat { to, .. } => {
                let vs = self.operands(&refs)?;
                Ok(format!("(({}){})", crate::names::float_c(*to), vs[0]))
            }
            Prim::TruncToInt { from, to, sat } => {
                let vs = self.operands(&refs)?;
                let (f, t) = (float_tag(*from), int_tag(*to));
                Ok(if *sat {
                    format!("onsa_trunc_sat_{t}_{f}({})", vs[0])
                } else {
                    format!("onsa_trunc_{t}_{f}({}, {loc})", vs[0])
                })
            }
            Prim::ToBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::FromBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_from_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::Parts(op, k) => {
                let vs = self.operands(&refs)?;
                let t = int_tag(*k);
                Ok(self.parts(e.ty, *k, |r| format!("onsa_c{}_{t}({}, {}, &{r})", op.name(), vs[0], vs[1])))
            }
            Prim::DivEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_div_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::RemEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_rem_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IsNan(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isnan({}))", vs[0]))
            }
            Prim::IsFinite(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isfinite({}))", vs[0]))
            }
            Prim::Len => {
                let s = self.place_like(&args[0].expr)?;
                match self.kind(args[0].expr.ty) {
                    TyKind::Span(_) => Ok(format!("{s}.len")),
                    TyKind::Array(_, n) => Ok(format!("UINT32_C({n})")),
                    _ => Err(unsupported(e.span, Feature::Buf, &[])),
                }
            }
            Prim::Slice => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(args[0].expr.ty)?;
                Ok(format!("onsa_slice_{tag}({s}, {}, {}, {loc})", vs[0], vs[1]))
            }
            Prim::Fill => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(args[0].expr.ty)?;
                self.line(&format!("onsa_fill_{tag}({s}, {});", vs[0]));
                Ok("((onsa_unit){0})".into())
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let d = self.span_arg(&args[0].expr)?;
                let s = self.span_arg(&args[1].expr)?;
                let tag = self.span_tag(args[0].expr.ty)?;
                let f = if matches!(prim, Prim::AddFrom) { "add_from" } else { "copy_from" };
                self.line(&format!("onsa_{f}_{tag}({d}, {s}, {loc});"));
                Ok("((onsa_unit){0})".into())
            }
            // `crate::prims::check` stops the unit before it is generated.
            Prim::BufZeroed | Prim::StrLen | Prim::AssertNear | Prim::Pending(_) => {
                Err(internal(&format!("the primitive `{}` C does not provide", prim.name())))
            }
        }
    }

    /// A span-typed argument as a C value (lowering made an array argument
    /// the `SpanOf` of its place).
    fn span_arg(&mut self, e: &Expr) -> R<String> {
        match self.kind(e.ty) {
            TyKind::Span(_) => self.place_like(e),
            _ => Err(unsupported(e.span, Feature::Buf, &[])),
        }
    }

    /// The `Span` `span` of the whole of the C array `arr` of `n` elements
    /// `el`. The pointer is cast to the element's type: the array of a
    /// borrowed parameter or of a `const` is `const`, and a `Span` the types
    /// stage lets write is of none of them (R-431).
    pub(super) fn array_span(&mut self, arr: &str, span: CTy, el: CTy, n: u32) -> String {
        let (tag, et) = (self.cx.names.tag(el), self.cx.names.name(el));
        let _ = self.cx.names.name(span);
        format!("onsa_span_{tag}_of(({et}*){arr}.a, UINT32_C({n}))")
    }

    fn span_tag(&mut self, ty: CTy) -> R<String> {
        match self.kind(ty) {
            TyKind::Span(el) => Ok(self.cx.names.tag(*el)),
            _ => Err(unsupported(no_span(), Feature::Buf, &[])),
        }
    }
}
