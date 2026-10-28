//! The lowering of types (T2-3): the types written in signatures, their
//! arguments and lengths, and `lower_type_in_body` for the types written in
//! a body.

use super::*;
use crate::ResolveError;
use crate::names::PathEnd;
use crate::resolve::NameKind;
use crate::ty::{TYPE_DEPTH_LIMIT, TYPE_SIZE_LIMIT};

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ types

    /// The type `t` as written, within the limits of §4.4 (S-264): the first
    /// type over them is an E0422, at the name of the alias it is the right
    /// side of or at its form written, and is the error type. A type with an
    /// error in it is not judged: a part not read is the error type, and its
    /// users get no diagnostic (§18.1; an alias over the limits is the error
    /// type for the aliases that use it). Over them, it is the error type,
    /// so that no type made of it grows on (a chain of aliases, R-303).
    pub(super) fn lower_type(&mut self, cx: &Cx<'p>, t: TypeId) -> TyId {
        let ty = self.lower_written(cx, t);
        let types = &self.a.types;
        if !types.over_limit(ty) {
            return ty;
        }
        if types.has_error(ty) {
            return self.a.types.error();
        }
        let msg = if types.depth(ty) > TYPE_DEPTH_LIMIT {
            format!("the type is deeper than {TYPE_DEPTH_LIMIT} levels (§4.4)")
        } else {
            format!("the type is larger than {TYPE_SIZE_LIMIT} names and forms (§4.4)")
        };
        let def = self.a.def(cx.def);
        let span = if matches!(def.kind, DefKind::Alias(_)) { def.name_span } else { cx.ast.ty(t).span };
        let rule = "name an inner part of the type with a `struct`: a declared type counts as one name, and an \
                    alias stands for the whole type it names";
        let d = Diagnostic::new(Stage::Names, Code::E0422, span, msg).with_found(src(cx, span)).with_rule(rule);
        self.report(cx.def, d);
        self.a.types.error()
    }

    fn lower_written(&mut self, cx: &Cx<'p>, t: TypeId) -> TyId {
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
                if let Some(t) = self.local_as_type(cx, path, te.span) {
                    return t;
                }
                if path.segments.len() == 1 {
                    let seg = &path.segments[0];
                    if seg.name == "Self" {
                        return match cx.self_ty {
                            Some(t) => t,
                            None => {
                                self.report(cx.def, ResolveError::SelfOutsideImpl { span: seg.span }.into_diagnostic());
                                self.a.types.error()
                            }
                        };
                    }
                    if let Some(i) = cx.generics.iter().position(|g| g.name == seg.name) {
                        self.a.note_use(cx.generics[i].span, seg.span);
                        // A const parameter (R-282) and an effect-row variable
                        // are no type (§15.1).
                        let kind = NameKind::of_generic(&cx.generics[i].kind);
                        if kind != NameKind::Type {
                            return self.not_a_type(cx, None, kind, te.span, path);
                        }
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
                        return self.a.types.intern(Ty::Param(i as u32));
                    }
                }
                // Through `Self` and the aliases (`Self.N`, `Al.N`, §2.2, §4.4).
                let entity = match self.a.path_end(cx.m, path, cx.self_ty) {
                    Ok(PathEnd::Entity(e)) => e,
                    // `F32.PI`, `Str.len` (R-302).
                    Ok(end @ PathEnd::Builtin { .. }) => {
                        return self.not_a_type(cx, None, end.kind(self.a, te.span), te.span, path);
                    }
                    // What the check does not read (§18.1, S-689, S-690): the
                    // error type, with no diagnostic.
                    Err(e) if self.a.unread_path(cx.def, cx.m, path, &e) => return self.a.types.error(),
                    Err(e) => {
                        let d = match self.rate_as_type(cx, t, &e) {
                            Some(Some(d)) => d,
                            Some(None) => return self.a.types.error(),
                            None => self.flow_name_as_type(cx, path, &e).unwrap_or_else(|| e.into_diagnostic()),
                        };
                        self.report(cx.def, d);
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

    /// E0308 for a builtin name of a flow (§11.4, S-720) the head of `path`
    /// names in a type of a flow, its heading or its body, where no item or
    /// `use` takes it (`x: prev at sample`; what `err` did not find).
    fn flow_name_as_type(&self, cx: &Cx<'p>, path: &Path, err: &ResolveError) -> Option<Diagnostic> {
        let head = &path.segments[0];
        let b = crate::flow_names::FlowBuiltin::named(&head.name)?;
        let in_flow = matches!(self.a.def(cx.def).kind, DefKind::Flow(_));
        if !in_flow || !matches!(err, ResolveError::NotFound { name, .. } if *name == head.name) {
            return None;
        }
        Some(b.misplaced(path.segments.iter().map(|s| s.span), cx.text))
    }

    /// E0020 for a rate written as a type `t` (`Sig[F32]`, the row
    /// `rate_as_type`, §11.3, S-120): a name of the list of
    /// [`foreign::RATE_TYPES`] with one type argument, not found (`err`;
    /// a user's `struct Sig[T]` is found). The candidate keeps the argument,
    /// with a clock after it at the type of an input or the output of the flow
    /// `cx.def` with no clock: the rate's of an input, `sample` of the output
    /// (its one clock in this version, §11.6). The argument is lowered first:
    /// an error in it, which the candidate would leave, is the error
    /// (`Some(None)`, §18.1).
    fn rate_as_type(&mut self, cx: &Cx<'p>, t: TypeId, err: &ResolveError) -> Option<Option<Diagnostic>> {
        let te = cx.ast.ty(t);
        let TypeKind::Path { path, args } = &te.kind else { return None };
        let ([seg], [arg]) = (path.segments.as_slice(), args.as_slice()) else { return None };
        let rate = Rate::of_type_name(&seg.name)?;
        if !matches!(err, ResolveError::NotFound { name, .. } if *name == seg.name) {
            return None;
        }
        let inner = self.lower_type(cx, *arg);
        if matches!(self.a.types.get(inner), Ty::Error) {
            return Some(None);
        }
        let (whole, arg) = (te.span, cx.ast.ty(*arg).span);
        let mut kind = self.a.def(cx.def).item.map(|i| &cx.ast.item(i).kind);
        if let Some(ItemKind::Target(inner)) = kind {
            kind = Some(inner);
        }
        let clock = match kind {
            Some(ItemKind::Flow(f)) if f.ret == t && f.ret_clock.is_none() => Some(Rate::Sig),
            Some(ItemKind::Flow(f)) if f.params.iter().any(|p| p.ty == Some(t) && p.clock.is_none()) => Some(rate),
            _ => None,
        };
        let (clock, title) = match clock {
            Some(r) => (format!(" at {}", r.clock()), format!("write the rate as the clock `at {}`", r.clock())),
            None => (String::new(), format!("write `{}` with no rate", src(cx, arg))),
        };
        let edits = vec![
            onsa_diag::Edit::replace(Span { end: arg.start, ..whole }, ""),
            onsa_diag::Edit::replace(Span { start: arg.end, ..whole }, clock),
        ];
        Some(Some(foreign::report(RowId::RateAsType, cx.text, whole, vec![Fix::new(title, edits)])))
    }

    /// One type argument (S-24). `expect_const`: `Some(true)` for a `const`
    /// parameter, `Some(false)` for a type parameter, `None` when the entity
    /// has no declared kinds (builtins, aliases: only types are accepted).
    fn lower_type_arg(&mut self, cx: &Cx<'p>, t: TypeId, expect_const: Option<bool>) -> TyId {
        let te = cx.ast.ty(t);
        match (&te.kind, expect_const) {
            // The kind of an argument is the name stage's, whatever its form
            // (`Wrap[3]`, `Ring[F32, (F32, F32)]`; §4.5, §15.1, S-732).
            (TypeKind::ConstArg(e), Some(false) | None) => {
                // `Option[self]`: a local, as of a path (R-309).
                let local = crate::constarg::path_of(cx.ast, *e).and_then(|p| self.local_as_type(cx, &p, te.span));
                local.unwrap_or_else(|| self.wrong_kind_arg(cx, te.span, "a constant expression", "a type"))
            }
            (TypeKind::ConstArg(e), Some(true)) => {
                match crate::constarg::expr(self.a, cx.m, cx.ast, cx.text, (&cx.generics, cx.self_ty), *e, &cx.local())
                {
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
            (TypeKind::Path { path, args }, Some(true)) => {
                // `N` of the enclosing item, or a constant; a name of another
                // kind is E0417 or E0308 (§4.5, S-713 (a)), with type
                // arguments or not (`Wrap[F32]`, S-732).
                let local = || crate::constarg::value_not_constant(src(cx, path.span), "a local", path.span);
                let named = match crate::constarg::generic(self.a, &cx.generics, path) {
                    _ if cx.is_local(&path.segments[0].name) => Err(local().into()),
                    Some((i, NameKind::ConstParam)) => Ok(Ty::Param(i)),
                    Some((_, kind)) => Err(crate::constarg::not_constant(kind, src(cx, path.span), path.span)),
                    None => crate::constarg::named(self.a, cx.m, (cx.ast, cx.text), path, cx.self_ty, path.span)
                        .map(Ty::ConstVal),
                };
                match named {
                    // A constant with type arguments (`K[F32]`).
                    Ok(_) | Err(crate::constarg::ConstErr::Uncomputed(_)) if !args.is_empty() => {
                        self.not_a_const_arg(cx, te.span)
                    }
                    Ok(ty) => self.a.types.intern(ty),
                    Err(crate::constarg::ConstErr::Unknown) => self.a.types.error(),
                    Err(crate::constarg::ConstErr::Report(d) | crate::constarg::ConstErr::Uncomputed(d)) => {
                        self.report(cx.def, d);
                        self.a.types.error()
                    }
                }
            }
            (_, Some(true)) => self.wrong_kind_arg(cx, te.span, "a type", "a constant"),
            _ => self.lower_type(cx, t),
        }
    }

    /// The E0308 of the path `path` of the type at `span` whose head is a
    /// local, a value (§15.1, S-729, S-741), as `K.x` of a constant `K` has
    /// no members; `None` when its head is no local.
    fn local_as_type(&mut self, cx: &Cx<'p>, path: &Path, span: Span) -> Option<TyId> {
        let [head, rest @ ..] = &path.segments[..] else { return None };
        if !cx.is_local(&head.name) {
            return None;
        }
        let Some(next) = rest.first() else {
            return Some(self.not_a_type(cx, None, NameKind::Local, span, path));
        };
        let d = crate::resolve::no_members(&head.name, NameKind::Local, next.span);
        self.report(cx.def, d.with_found(head.name.clone()));
        Some(self.a.types.error())
    }

    /// E0308 for the type argument at `span`, which is `is` where the
    /// parameter wants `want`.
    fn wrong_kind_arg(&mut self, cx: &Cx<'p>, span: Span, is: &str, want: &str) -> TyId {
        let msg = format!("`{}` is {is}, not {want} (§4.5)", src(cx, span));
        self.report(cx.def, Diagnostic::new(Stage::Names, Code::E0308, span, msg).with_found(src(cx, span)));
        self.a.types.error()
    }

    /// E0401 for the const argument at `span`, a constant with type
    /// arguments (`K[F32]`, a form of its kind, S-713 B4).
    fn not_a_const_arg(&mut self, cx: &Cx<'p>, span: Span) -> TyId {
        let msg = "a `const` parameter expects an integer literal or a constant, not a type";
        self.report(cx.def, Diagnostic::new(Stage::Types, Code::E0401, span, msg).with_found(src(cx, span)));
        self.a.types.error()
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
                    // A type of a cycle (E0311, at its declaration, §18.1) too.
                    DefKind::Struct(_) | DefKind::Enum(_)
                        if self.a.heading_failed(d) || self.a.decls.cyclic.contains(&d) =>
                    {
                        self.a.types.error()
                    }
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
                    // An opaque type of an `extern` block, whose kind is a type.
                    DefKind::Unsupported(Declared::Type | Declared::Block) => self.a.types.error(),
                    _ => self.not_a_type(cx, Some(entity), NameKind::of_named(entity, &self.a.defs, span), span, path),
                }
            }
            Entity::Module(_) | Entity::Builtin(_) | Entity::Variant(..) => {
                self.not_a_type(cx, Some(entity), NameKind::of_named(entity, &self.a.defs, span), span, path)
            }
        }
    }

    /// E0308 for the name `path` at `span` of a type, which is of another
    /// kind `kind` (§15.1, §18.1, S-713, S-719, S-721): a value, a module, a
    /// trait, a flow (with the candidate of its state type, §11.6), what an
    /// E0200 declares, a parameter of the heading that is no type; `entity`
    /// is what the path names, if any. The type is the error type.
    fn not_a_type(&mut self, cx: &Cx<'p>, entity: Option<Entity>, kind: NameKind, span: Span, path: &Path) -> TyId {
        let mut d = kind_error(path, kind, "a type", span);
        let shown = d.found.clone().unwrap_or_default();
        // The type arguments after the path, if any, are what changes:
        // `Sig[F32]` is `Sig.State` (§18.1, S-251). Not when `State`, of the
        // flow's visibility, would be an E0303 there (§15.1).
        if let (Some(Entity::Def(f)), NameKind::Flow) = (entity, kind)
            && cx.reach.is_none_or(|r| crate::resolve::reaches(self.a.def(f).vis, r))
        {
            let at = Span { start: path.span.end, ..span };
            d = d.with_fix(Fix::replace(format!("write `{shown}.State`"), at, ".State"));
        }
        self.report(cx.def, d);
        self.a.types.error()
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
            DefKind::Struct(_) | DefKind::Enum(_) | DefKind::Unsupported(_) => vec![d],
            DefKind::Alias(_) => {
                let t = self.alias_ty(d);
                self.a.types.named(t)
            }
            // Not a type: an E0302 of its own.
            DefKind::Fn(_)
            | DefKind::Flow(_)
            | DefKind::Const(_)
            | DefKind::Impl(_)
            | DefKind::Test { .. }
            | DefKind::Effect { .. } => vec![],
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
        let d = Diagnostic::new(Stage::Types, Code::E0303, path.span, msg)
            .with_found(name)
            .with_note(def.name_span, "defined here");
        self.report(cx.def, d);
    }

    /// Array length (§4.1): an integer literal, a `const` with a literal
    /// initializer, or a const generic parameter.
    fn lower_len(&mut self, cx: &Cx<'p>, e: onsa_syntax::ast::ExprId) -> Option<Len> {
        match crate::constarg::expr(self.a, cx.m, cx.ast, cx.text, (&cx.generics, cx.self_ty), e, &cx.local()) {
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
/// the item's generics and `Self` in scope, and the visible locals it names
/// (`locals`, [`Cx::locals`]). Diagnostics are returned, not
/// pushed, so the body checker keeps its first-error rule. The signatures
/// are lowered: it reads them, and writes only the types it interns and
/// [`Analysis::read_held`] (the aliases are lowered, `decls`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_type_in_body<'p>(
    a: &'p mut Analysis,
    m: ModId,
    ast: &'p Ast,
    text: &'p str,
    generics: &[GenericDef],
    self_ty: Option<TyId>,
    def: DefId,
    (t, locals): (TypeId, HashSet<String>),
) -> (TyId, Vec<Diagnostic>) {
    let before = a.diagnostics.len();
    let mut s = Sema::new(a, Vec::new());
    let cx = Cx { m, ast, text, generics: generics.to_vec(), self_ty, def, reach: None, locals };
    let ty = s.lower_type(&cx, t);
    let diags = s.a.diagnostics.drain(before..).collect();
    (ty, diags)
}
