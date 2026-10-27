//! The patterns: the names they bind and their constructors.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ patterns

    /// Bind a pattern against `ty`. Returns the lowered pattern for the
    /// exhaustiveness check. `irrefutable` is the `let` / `for` context (E0502).
    /// The names it binds are the bindings of the record (a name of a choice
    /// is one, which each branch unifies with, §7).
    pub(super) fn bind_pat(&mut self, pat: PatId, ty: TyId, irrefutable: bool, borrow: bool) -> R<P> {
        let p = self.ast.pat(pat);
        let span = p.span;
        match &p.kind {
            PatKind::Wild => Ok(P::Wild),
            PatKind::Bind(id) => {
                let lid = self.local_of_pat(pat)?;
                self.bind_local(lid, ty, borrow, id.span)?;
                self.info.pat_locals.insert(pat, lid);
                Ok(P::Wild)
            }
            PatKind::Lit(lit) | PatKind::Neg(lit) => {
                if irrefutable {
                    return Err(self.err(
                        Code::E0502,
                        span,
                        "a literal pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                    ));
                }
                match lit {
                    Lit::Int { value, .. } => {
                        // Unified with the subject's type argument like an operand of `==`,
                        // and range-checked when that is decided (§4.7, §7; S-185, S-226).
                        let v = self.infer.fresh(&mut self.a.types, Some(LitKind::Int));
                        let neg = matches!(p.kind, PatKind::Neg(_));
                        self.defer(span, v, DeferredKind::IntLit { value: *value, neg, lit: None });
                        self.unify_at(span, v, ty)?;
                        Ok(P::Lit(if neg { -(*value as i128) } else { *value as i128 }))
                    }
                    // The parser refuses a float literal in a pattern (the
                    // table of the forms of other languages, S-252).
                    Lit::Float { .. } => {
                        onsa_diag::internal::bug(Some(span), "a float literal pattern after the parse")
                    }
                    Lit::Char(c) => {
                        let t = self.a.types.intern(Ty::Char);
                        self.unify_at(span, t, ty)?;
                        Ok(P::Lit(*c as i128))
                    }
                    Lit::Bool(b) => {
                        let t = self.bool_();
                        self.unify_at(span, t, ty)?;
                        Ok(P::Ctor(*b as u32, vec![]))
                    }
                    Lit::Str(s) => {
                        let t = self.a.types.builtin(BuiltinTy::Str, vec![]);
                        self.unify_at(span, t, ty)?;
                        let text: String = s
                            .segments
                            .iter()
                            .map(|x| match x {
                                StrSeg::Text(t) => t.clone(),
                                _ => String::new(),
                            })
                            .collect();
                        Ok(P::Str(text))
                    }
                }
            }
            PatKind::Path(path) => self.bind_ctor_pat(pat, path, &[], ty, irrefutable, borrow, false),
            PatKind::TupleStruct { path, elems } => self.bind_ctor_pat(pat, path, elems, ty, irrefutable, borrow, true),
            PatKind::Tuple(elems) => {
                let s = self.known(ty, span, "matched value")?;
                let Ty::Tuple(ts) = self.ty(s) else {
                    // A value of the error type: the elements are errors too,
                    // and their names are bound (§18.1, R-271).
                    if matches!(self.ty(s), Ty::Error) {
                        for &el in elems {
                            self.bind_pat(el, s, irrefutable, borrow)?;
                        }
                        return Ok(P::Wild);
                    }
                    let shown = self.display(ty);
                    return Err(self.err(
                        Code::E0401,
                        span,
                        format!("expected a tuple pattern target, found `{shown}`"),
                    ));
                };
                if ts.len() != elems.len() {
                    return Err(self.err(
                        Code::E0401,
                        span,
                        format!("a tuple of {} element(s) cannot match this pattern of {}", ts.len(), elems.len()),
                    ));
                }
                let mut subs = Vec::new();
                for (&el, &t) in elems.iter().zip(&ts) {
                    subs.push(self.bind_pat(el, t, irrefutable, borrow)?);
                }
                Ok(P::Ctor(0, subs))
            }
            PatKind::Struct { path, fields, rest } => {
                let mut bound: Vec<(usize, P)> = Vec::new();
                let Some(count) = self.struct_pattern(
                    Stage::Types,
                    span,
                    ty,
                    Written { pat, path, fields, rest: *rest },
                    &mut |ck, fp, ft, i| {
                        let sub = ck.bind_pat(fp, ft, irrefutable, borrow)?;
                        bound.extend(i.map(|i| (i, sub)));
                        Ok(())
                    },
                )?
                else {
                    // A struct that is not known covers what it may (R-271).
                    return Ok(P::Wild);
                };
                let mut subs = vec![P::Wild; count];
                for (i, sub) in bound {
                    subs[i] = sub;
                }
                Ok(P::Ctor(0, subs))
            }
            PatKind::Or(alts) => {
                if irrefutable {
                    return Err(self.err(
                        Code::E0502,
                        span,
                        "an or-pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
                    ));
                }
                let mut lowered = Vec::new();
                for &alt in alts {
                    lowered.push(self.bind_pat(alt, ty, false, borrow)?);
                }
                Ok(P::Or(lowered))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_ctor_pat(
        &mut self,
        pat: PatId,
        path: &Path,
        elems: &[PatId],
        ty: TyId,
        irrefutable: bool,
        borrow: bool,
        with_parens: bool,
    ) -> R<P> {
        let span = self.ast.pat(pat).span;
        let entity = self.ctor_of(pat)?;
        // (constructor index, field types, number of constructors of the type)
        let (ctor, fields, nctors): (u32, Vec<TyId>, usize) = match entity {
            Entity::Builtin(Builtin::None) => {
                let t = self.fresh();
                let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                self.unify_at(span, opt, ty)?;
                (0, vec![], 2)
            }
            Entity::Builtin(Builtin::Some) => {
                let t = self.fresh();
                let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                self.unify_at(span, opt, ty)?;
                (1, vec![t], 2)
            }
            Entity::Builtin(Builtin::Ok) | Entity::Builtin(Builtin::Err) => {
                let (t, e2) = (self.fresh(), self.fresh());
                let res = self.a.types.builtin(BuiltinTy::Result, vec![t, e2]);
                self.unify_at(span, res, ty)?;
                if matches!(entity, Entity::Builtin(Builtin::Ok)) { (0, vec![t], 2) } else { (1, vec![e2], 2) }
            }
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                let en = self.a.def(d).as_enum().unwrap().clone();
                let named = self.a.types.intern(Ty::Named(d, args.clone()));
                self.unify_at(span, named, ty)?;
                let fields: Vec<TyId> = en.variants[i as usize].fields.iter().map(|&f| self.subst(f, &args)).collect();
                (i, fields, en.variants.len())
            }
            _ => {
                let shown = self.src(path.span);
                return Err(self.name_err(
                    Code::E0302,
                    path.span,
                    format!(
                        "`{shown}` is not a variant; patterns are literals, bindings, variants, tuples and structs (§7)"
                    ),
                ));
            }
        };
        if irrefutable && nctors > 1 {
            return Err(self.err(
                Code::E0502,
                span,
                "this pattern can fail to match; `let` takes only tuple and struct patterns; use `match` (§7)",
            ));
        }
        if !with_parens && !fields.is_empty() {
            return Err(self.err(
                Code::E0412,
                span,
                format!(
                    "this variant has {} field(s); write the pattern as `{}(...)`",
                    fields.len(),
                    self.src(path.span)
                ),
            ));
        }
        if with_parens && elems.len() != fields.len() {
            return Err(self.err(
                Code::E0412,
                span,
                format!("this variant has {} field(s) but the pattern gives {}", fields.len(), elems.len()),
            ));
        }
        let mut subs = Vec::new();
        for (&el, &t) in elems.iter().zip(&fields) {
            subs.push(self.bind_pat(el, t, irrefutable, borrow)?);
        }
        Ok(P::Ctor(ctor, subs))
    }
}
