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
                    // A name held as an error (§18.1, S-462, S-675).
                    Err(crate::resolve::ResolveError::Failed) => {
                        self.hold_signature(cx.def);
                        return self.a.types.error();
                    }
                    // A member of a def a syntax error cut (S-260): no diagnostic.
                    Err(_) if self.a.through_partly_read(cx.m, path) => return self.a.types.error(),
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
                match crate::constarg::expr(&mut self.a, cx.m, cx.ast, cx.text, &cx.generics, *e) {
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
                    match crate::constarg::named(&mut self.a, cx.m, cx.ast, cx.text, path, te.span) {
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
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0302,
                                span,
                                format!("`{name}` is a flow, not a type; its state type is `{name}.State` (§11.6)"),
                            )
                            // The type arguments after the path, if any, are what
                            // changes: `Sig[F32]` is `Sig.State` (§18.1, S-251).
                            .with_fix(Fix::replace(
                                format!("write `{name}.State`"),
                                Span { start: path.span.end, ..span },
                                ".State",
                            )),
                        );
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

    /// Array length (§4.1): an integer literal, a `const` with a literal
    /// initializer, or a const generic parameter.
    fn lower_len(&mut self, cx: &Cx<'p>, e: onsa_syntax::ast::ExprId) -> Option<Len> {
        match crate::constarg::expr(&mut self.a, cx.m, cx.ast, cx.text, &cx.generics, e) {
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
/// pushed, so the body checker keeps its first-error rule.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_type_in_body(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    generics: &[GenericDef],
    self_ty: Option<TyId>,
    def: DefId,
    t: TypeId,
) -> (TyId, Vec<Diagnostic>) {
    let before = a.diagnostics.len();
    let mut s = Sema {
        a: std::mem::take(a),
        flat: Vec::new(),
        reported: HashSet::new(),
        expanding: HashSet::new(),
        kind_heads: Vec::new(),
    };
    let is_std = s.a.modules.pkg_of(m) < s.a.modules.names.len() && s.a.modules.names[s.a.modules.pkg_of(m)] == "std";
    let cx = Cx { m, ast, text, generics: generics.to_vec(), self_ty, def, is_std };
    let ty = s.lower_type(&cx, t);
    *a = s.a;
    let diags = a.diagnostics.drain(before..).collect();
    (ty, diags)
}
