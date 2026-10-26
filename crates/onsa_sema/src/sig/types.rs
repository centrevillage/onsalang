//! The lowering of types (T2-3): the types written in signatures, their
//! arguments and lengths, and `lower_type_in_body` for the types written in
//! a body.

use super::*;

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ types

    pub(super) fn lower_type(&mut self, cx: &Cx<'p>, t: TypeId) -> TyId {
        let te = cx.ast.ty(t);
        match &te.kind {
            // What a syntax error left unread (S-59): no diagnostic.
            TypeKind::Error => self.a.types.error(),
            TypeKind::Unit => self.a.types.unit(),
            TypeKind::Tuple(ts) => {
                let v: Vec<TyId> = ts.iter().map(|&x| self.lower_type(cx, x)).collect();
                self.a.types.intern(Ty::Tuple(v))
            }
            TypeKind::Array { elem, len } => {
                let e = self.lower_type(cx, *elem);
                match self.lower_len(cx, *len) {
                    Some(l) => self.a.types.intern(Ty::Array(e, l)),
                    None => self.a.types.error(),
                }
            }
            TypeKind::Fn { rt, params, ret, effects } => {
                let ps: Vec<(Mode, TyId)> = params.iter().map(|(m, x)| (*m, self.lower_type(cx, *x))).collect();
                let r = match ret {
                    Some(x) => self.lower_type(cx, *x),
                    None => self.a.types.unit(),
                };
                let eff = self.lower_effects(cx, effects.as_ref());
                self.a.types.intern(Ty::Fn(FnTy { rt: *rt, params: ps, ret: r, effects: eff }))
            }
            TypeKind::Path { path, args } => {
                let args_ast = args.clone();
                if path.segments.len() == 1 {
                    let seg = &path.segments[0];
                    if seg.name == "Self" {
                        return match cx.self_ty {
                            Some(t) => t,
                            None => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Names,
                                        Code::E0302,
                                        seg.span,
                                        "`Self` is only valid inside `impl`",
                                    ),
                                );
                                self.a.types.error()
                            }
                        };
                    }
                    if let Some(i) = cx.generics.iter().position(|g| g.name == seg.name) {
                        if !args_ast.is_empty() {
                            self.report(
                                cx.def,
                                Diagnostic::new(
                                    Stage::Names,
                                    Code::E0302,
                                    te.span,
                                    "a type parameter takes no arguments",
                                ),
                            );
                        }
                        return match cx.generics[i].kind {
                            GenericKind::Type { .. } | GenericKind::Const(_) => {
                                self.a.types.intern(Ty::Param(i as u32))
                            }
                            GenericKind::Effect => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Names,
                                        Code::E0302,
                                        seg.span,
                                        "an effect-row variable is not a type",
                                    ),
                                );
                                self.a.types.error()
                            }
                        };
                    }
                }
                let entity = match self.a.resolve_path(cx.m, path) {
                    Ok(e) => e,
                    // What the check does not read (§18.1, S-689, S-690): the
                    // error type, with no diagnostic.
                    Err(e) if self.a.unread_path(cx.def, cx.m, path, &e) => return self.a.types.error(),
                    Err(e) => {
                        self.report(cx.def, e.into_diagnostic());
                        return self.a.types.error();
                    }
                };
                // S-24: a const generic parameter takes an integer literal or a
                // constant's name; which arguments are const depends on the entity.
                let expect_const: Vec<Option<bool>> = match entity {
                    Entity::Def(d) | Entity::Member(d) => {
                        let def = &self.a.defs[d.0 as usize];
                        match &def.kind {
                            DefKind::Struct(_) | DefKind::Enum(_) => {
                                def.generics().iter().map(|g| Some(matches!(g.kind, GenericKind::Const(_)))).collect()
                            }
                            _ => Vec::new(),
                        }
                    }
                    _ => Vec::new(),
                };
                let lowered_args: Vec<TyId> = args_ast
                    .iter()
                    .enumerate()
                    .map(|(i, &x)| self.lower_type_arg(cx, x, expect_const.get(i).copied().flatten()))
                    .collect();
                self.type_of_entity(cx, entity, lowered_args, te.span, path)
            }
            TypeKind::ConstArg(_) => {
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a constant is not a type; const arguments go to `const` parameters",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
        }
    }

    /// One type argument (S-24). `expect_const`: `Some(true)` for a `const`
    /// parameter, `Some(false)` for a type parameter, `None` when the entity
    /// has no declared kinds (builtins, aliases: only types are accepted).
    fn lower_type_arg(&mut self, cx: &Cx<'p>, t: TypeId, expect_const: Option<bool>) -> TyId {
        let te = cx.ast.ty(t);
        match (&te.kind, expect_const) {
            (TypeKind::ConstArg(e), Some(false) | None) => {
                let _ = e;
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a type parameter expects a type, not a constant",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            (TypeKind::ConstArg(e), Some(true)) => {
                match crate::constarg::expr(self.a, cx.m, cx.ast, cx.text, &cx.generics, *e) {
                    Ok((crate::constarg::ConstU32::Value(v), _)) => self.a.types.intern(Ty::ConstVal(v)),
                    Ok((crate::constarg::ConstU32::Param(i), _)) => self.a.types.intern(Ty::Param(i)),
                    Err(crate::constarg::ConstErr::Unknown) => self.a.types.error(),
                    Err(crate::constarg::ConstErr::Report(mut d) | crate::constarg::ConstErr::Uncomputed(mut d)) => {
                        // The whole argument (`-1`), as written in the type.
                        d.span = te.span;
                        d.found = Some(src(cx, te.span));
                        self.report(cx.def, d);
                        self.a.types.error()
                    }
                }
            }
            (TypeKind::Path { path, args }, Some(true)) if args.is_empty() => {
                // `N` of the enclosing item, or a `const` item with a literal value.
                if path.segments.len() == 1
                    && let Some(i) = cx.generics.iter().position(|g| g.name == path.segments[0].name)
                {
                    if matches!(cx.generics[i].kind, GenericKind::Const(_)) {
                        return self.a.types.intern(Ty::Param(i as u32));
                    }
                } else {
                    match crate::constarg::named(self.a, cx.m, cx.ast, cx.text, path, te.span) {
                        Ok(Some(v)) => return self.a.types.intern(Ty::ConstVal(v)),
                        Ok(None) => {}
                        Err(crate::constarg::ConstErr::Unknown) => return self.a.types.error(),
                        Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => {
                            self.report(cx.def, d);
                            return self.a.types.error();
                        }
                    }
                }
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a `const` parameter expects an integer literal or a constant, not a type",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            (_, Some(true)) => {
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a `const` parameter expects an integer literal or a constant, not a type",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            _ => self.lower_type(cx, t),
        }
    }

    fn type_of_entity(
        &mut self,
        cx: &Cx<'p>,
        entity: Entity,
        args: Vec<TyId>,
        span: Span,
        path: &onsa_syntax::ast::Path,
    ) -> TyId {
        let name = path.segments.last().unwrap().name.clone();
        let arity_err = |s: &mut Self, want: usize| {
            s.report(
                cx.def,
                Diagnostic::new(
                    Stage::Names,
                    Code::E0302,
                    span,
                    format!("`{name}` takes {want} type argument(s), {} given", args.len()),
                ),
            );
            s.a.types.error()
        };
        match entity {
            Entity::Builtin(Builtin::Scalar(t)) => {
                if !args.is_empty() {
                    return arity_err(self, 0);
                }
                t
            }
            Entity::Builtin(Builtin::Generic(b)) => {
                if args.len() != b.arity() {
                    return arity_err(self, b.arity());
                }
                self.a.types.builtin(b, args)
            }
            Entity::Def(d) | Entity::Member(d) => {
                self.check_reach(cx, d, path);
                let def = &self.a.defs[d.0 as usize];
                match &def.kind {
                    // A heading a syntax error cut (S-59): its generic parameters
                    // are not known, and its uses are the error type (R-71).
                    DefKind::Struct(_) | DefKind::Enum(_) if self.a.heading_failed(d) => self.a.types.error(),
                    DefKind::Struct(_) | DefKind::Enum(_) => {
                        let want = def.generics().len();
                        if args.len() != want {
                            return arity_err(self, want);
                        }
                        self.a.types.intern(Ty::Named(d, args))
                    }
                    DefKind::Alias(_) => {
                        if !args.is_empty() {
                            return arity_err(self, 0);
                        }
                        self.alias_ty(d)
                    }
                    DefKind::Flow(_) => {
                        let mut d = Diagnostic::new(
                            Stage::Names,
                            Code::E0302,
                            span,
                            format!("`{name}` is a flow, not a type; its state type is `{name}.State` (§11.6)"),
                        );
                        // The type arguments after the path, if any, are what
                        // changes: `Sig[F32]` is `Sig.State` (§18.1, S-251). Not
                        // when `State`, of the flow's visibility, would be an
                        // E0303 there (§15.1).
                        if cx.reach.is_none_or(|r| crate::resolve::reaches(def.vis, r)) {
                            let at = Span { start: path.span.end, ..span };
                            d = d.with_fix(Fix::replace(format!("write `{name}.State`"), at, ".State"));
                        }
                        self.report(cx.def, d);
                        self.a.types.error()
                    }
                    DefKind::Unsupported => self.a.types.error(),
                    _ => {
                        self.report(
                            cx.def,
                            Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is not a type"))
                                .with_found(name.clone()),
                        );
                        self.a.types.error()
                    }
                }
            }
            Entity::Module(_) => {
                self.report(
                    cx.def,
                    Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is a module, not a type")),
                );
                self.a.types.error()
            }
            Entity::Builtin(_) | Entity::Variant(..) => {
                self.report(
                    cx.def,
                    Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is a value, not a type")),
                );
                self.a.types.error()
            }
        }
    }

    /// A type named in a heading that reaches less far than the heading
    /// (§15.1, S-144, S-665): E0303 at the name written, with no candidate.
    /// An alias is judged by the names of the type it stands for, the
    /// narrowest of them (§4.4, S-700); its right side is judged where it is
    /// declared. The type is lowered on (the name is known). A def whose kind
    /// is not known (an E0200, a member of an `extern` block) is judged too.
    // A constant named as the length of an array or a const argument is not
    // judged: it is no type, trait or effect (S-699).
    fn check_reach(&mut self, cx: &Cx<'p>, d: DefId, path: &onsa_syntax::ast::Path) {
        // Nothing reaches less far than `priv`.
        let Some(reach) = cx.reach.filter(|&r| r != Vis::Priv) else { return };
        // Every kind is named, so that a new one is judged or not by choice.
        let named = match self.a.def(d).kind {
            DefKind::Struct(_) | DefKind::Enum(_) | DefKind::Unsupported => vec![d],
            DefKind::Alias(_) => {
                let t = self.alias_ty(d);
                self.a.types.named(t)
            }
            // Not a type: an E0302 of its own.
            DefKind::Fn(_) | DefKind::Flow(_) | DefKind::Const(_) | DefKind::Impl(_) | DefKind::Test { .. } => vec![],
        };
        let vis = |n: DefId| self.a.def(n).vis;
        let narrowest =
            named.into_iter().reduce(|a, b| if crate::resolve::narrower(vis(a), vis(b)) == vis(a) { a } else { b });
        let Some(n) = narrowest.filter(|&n| !crate::resolve::reaches(vis(n), reach)) else { return };
        let def = self.a.def(n);
        let name = src(cx, path.span);
        let it = if n == d { "it".to_string() } else { format!("it stands for `{}`, which", self.a.shown_name(n)) };
        let msg = format!(
            "`{name}` is named in a heading seen {}, but {it} {} (§15.1)",
            crate::resolve::seen(reach),
            crate::resolve::hidden_words(def.vis)
        );
        let d = Diagnostic::new(Stage::Names, Code::E0303, path.span, msg)
            .with_found(name)
            .with_note(def.name_span, "defined here");
        self.report(cx.def, d);
    }

    /// Array length (§4.1): an integer literal, a `const` with a literal
    /// initializer, or a const generic parameter.
    fn lower_len(&mut self, cx: &Cx<'p>, e: onsa_syntax::ast::ExprId) -> Option<Len> {
        match crate::constarg::expr(self.a, cx.m, cx.ast, cx.text, &cx.generics, e) {
            Ok((crate::constarg::ConstU32::Value(v), _)) => Some(Len::Const(v)),
            Ok((crate::constarg::ConstU32::Param(i), _)) => Some(Len::Param(i)),
            Err(crate::constarg::ConstErr::Unknown) => None,
            Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => {
                self.report(cx.def, d);
                None
            }
        }
    }
}

/// Lower a type written inside a body (T2-5): same rules as signatures, with
/// the item's generics and `Self` in scope. Diagnostics are returned, not
/// pushed, so the body checker keeps its first-error rule. The signatures
/// are lowered: it reads them, and writes only the types it interns and
/// [`Analysis::read_held`] (with no package, no alias is lowered again).
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_type_in_body<'p>(
    a: &'p mut Analysis,
    m: ModId,
    ast: &'p Ast,
    text: &'p str,
    generics: &[GenericDef],
    self_ty: Option<TyId>,
    def: DefId,
    t: TypeId,
) -> (TyId, Vec<Diagnostic>) {
    let before = a.diagnostics.len();
    let mut s = Sema::new(a, Vec::new());
    let cx = Cx { m, ast, text, generics: generics.to_vec(), self_ty, def, reach: None };
    let ty = s.lower_type(&cx, t);
    let diags = s.a.diagnostics.drain(before..).collect();
    (ty, diags)
}
