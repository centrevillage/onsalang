//! The patterns: the names they bind and their constructors.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ patterns

    /// Bind a pattern against `ty`. Returns the lowered pattern for the
    /// exhaustiveness check. `irrefutable` is the `let` / `for` context (E0502).
    /// The names it binds are the bindings of the record (a name of a choice
    /// is one, which each branch unifies with, §7).
    pub(super) fn bind_pat(&mut self, pat: PatId, ty: TyId, irrefutable: bool) -> R<P> {
        let p = self.ast.pat(pat);
        let span = p.span;
        match &p.kind {
            PatKind::Wild => Ok(P::Wild),
            PatKind::Bind(id) => {
                let lid = self.local_of_pat(pat)?;
                self.bind_local(lid, ty, id.span)?;
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
                    // Of a `FixedStr[N]` subject, a value of it, compared as
                    // `==` (§7, §4.2, S-614); else a `Str`.
                    Lit::Str(s) => {
                        if self.fixed_literal(span, s, Some(ty))?.is_none() {
                            let t = self.a.types.builtin(BuiltinTy::Str, vec![]);
                            self.unify_at(span, t, ty)?;
                        }
                        // Its value, as the lowering reads it; one with an
                        // interpolation (E0020 of the syntax) covers none.
                        Ok(onsa_syntax::test_name::value(s).map_or(P::Const, P::Str))
                    }
                }
            }
            PatKind::Path(path) => self.bind_ctor_pat(pat, path, &[], ty, irrefutable, false),
            PatKind::TupleStruct { path, elems } => self.bind_ctor_pat(pat, path, elems, ty, irrefutable, true),
            PatKind::Tuple(elems) => {
                let Some(ts) = self.tuple_pattern(Stage::Types, ty, span, elems.len())? else {
                    // The names of the elements are bound (§18.1, R-271).
                    let s = self.shallow(ty);
                    for &el in elems {
                        self.bind_pat(el, s, irrefutable)?;
                    }
                    return Ok(P::Wild);
                };
                // The unit pattern `()` is the constructor of `()` (S-516).
                let mut subs = Vec::new();
                for (&el, &t) in elems.iter().zip(&ts) {
                    subs.push(self.bind_pat(el, t, irrefutable)?);
                }
                Ok(P::Ctor(0, subs))
            }
            PatKind::Struct { path, fields, rest } => {
                let mut bound: Vec<(usize, P)> = Vec::new();
                let count = self.struct_pattern(
                    Stage::Types,
                    span,
                    ty,
                    Written { pat, path, fields, rest: *rest },
                    &mut |ck, fp, ft, i| {
                        let sub = ck.bind_pat(fp, ft, irrefutable)?;
                        bound.extend(i.map(|i| (i, sub)));
                        Ok(())
                    },
                )?;
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
                    lowered.push(self.bind_pat(alt, ty, false)?);
                }
                Ok(P::Or(lowered))
            }
        }
    }

    /// The element types of a tuple pattern of `n` elements against `ty`, for
    /// the bodies and the flows (`stage`, of the diagnostic): those of a tuple
    /// of `n`, or none for the unit pattern `()` against `()` (§7, S-516). Any
    /// other type is E0401. `None` is a value of the error type, whose
    /// elements are errors too (§18.1, R-271).
    pub(crate) fn tuple_pattern(&mut self, stage: Stage, ty: TyId, span: Span, n: usize) -> R<Option<Vec<TyId>>> {
        // A literal variable is no tuple (S-860).
        let s = self.known_shape(ty, span, "matched value")?;
        let msg = match self.ty(s) {
            Ty::Tuple(ts) if ts.len() == n => return Ok(Some(ts)),
            Ty::Unit if n == 0 => return Ok(Some(Vec::new())),
            Ty::Error => return Ok(None),
            Ty::Tuple(ts) => format!("a tuple of {} element(s) cannot match this pattern of {n}", ts.len()),
            _ => format!("expected a tuple pattern target, found {}", self.described(ty)),
        };
        Err(self.diag(Diagnostic::new(stage, Code::E0401, span, msg).with_found(self.src(span))))
    }

    fn bind_ctor_pat(
        &mut self,
        pat: PatId,
        path: &Path,
        elems: &[PatId],
        ty: TyId,
        irrefutable: bool,
        with_parens: bool,
    ) -> R<P> {
        let span = self.ast.pat(pat).span;
        let (entity, owner) = self.ctor_of(pat)?;
        let (ctor, fields): (u32, Vec<TyId>) = match entity {
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                self.of_owner(d, &args, owner, span)?;
                let named = self.a.types.intern(Ty::Named(d, args.clone()));
                self.unify_at(span, named, ty)?;
                let written = self.a.def(d).as_enum().unwrap().variants[i as usize].fields.clone();
                let fields: Vec<TyId> = written.iter().map(|&f| self.a.types.subst(f, &args)).collect();
                (i, fields)
            }
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Const(_)) => {
                return self.bind_const_pat(pat, path, (d, owner), ty, irrefutable);
            }
            _ => return Err(self.not_a_pattern(path)),
        };
        self.info.pat_ctors.insert(pat, ctor);
        // Even of one variant: a variant more would break a far `let` (§7, S-177).
        if irrefutable {
            let msg = "this pattern can fail to match; `let` takes only tuple and struct patterns; use `match` (§7)";
            let d = Diagnostic::new(Stage::Types, Code::E0502, span, msg).with_found(self.src(span));
            return Err(self.diag(d.with_rule("a type that holds one value is written as a struct (§4.4)")));
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
            subs.push(self.bind_pat(el, t, irrefutable)?);
        }
        Ok(P::Ctor(ctor, subs))
    }

    /// The constant `d` as a pattern, which is compared with `==` (§7,
    /// S-185): a pattern that can fail (E0502), of the type of the value it
    /// is compared with (E0401, S-933). No value is read here.
    fn bind_const_pat(
        &mut self,
        pat: PatId,
        path: &Path,
        (d, owner): (DefId, Option<TyId>),
        ty: TyId,
        irrefutable: bool,
    ) -> R<P> {
        let span = self.ast.pat(pat).span;
        if irrefutable {
            return Err(self.err(
                Code::E0502,
                span,
                "a constant pattern can fail to match; `let` takes only tuple and struct patterns (§7)",
            ));
        }
        // A constant of no known type: the arms after it would report what
        // follows from that (§18.1).
        // SPEC-GAP(S-935): the unit stops here, as at a failed name; an
        // expression goes on with the error type.
        if self.a.heading_failed(d) {
            return Err(self.held_stop());
        }
        let (t, target) = self.const_value(d, owner, span)?;
        self.unify_at(span, t, ty)?;
        let t = self.known(t, span, "constant of a pattern")?;
        match self.ty(t) {
            Ty::Int(_) | Ty::Char | Ty::Bool | Ty::Builtin(BuiltinTy::Str, _) => {
                self.info.pat_consts.insert(pat, target);
                Ok(P::Const)
            }
            Ty::Error => Err(self.held_stop()),
            // Any other type (§7, S-252): the arm reports them as one
            // ([`Self::reject_constants`]).
            _ => {
                self.bad_consts.push((path.span, t));
                Ok(P::Const)
            }
        }
    }

    /// E0302 for the path of a pattern that names none of what a pattern
    /// takes.
    fn not_a_pattern(&mut self, path: &Path) -> Stop {
        let shown = self.src(path.span);
        self.name_err(
            Code::E0302,
            path.span,
            format!("`{shown}` is not a variant; patterns are literals, bindings, variants, tuples and structs (§7)"),
        )
    }
}
