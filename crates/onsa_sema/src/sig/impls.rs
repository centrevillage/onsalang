//! An inherent `impl` (§6.3): its members and their context, the type it
//! names (E0307) and how far a member reaches; and `impl Copy` and `impl
//! Dup` (§4.6).

use super::*;

impl<'p> Sema<'p> {
    /// The inherent `impl` `i` (the def `id` of the item `item`): its
    /// heading and its members; of `impl Copy` and `impl Dup`, their E0020.
    pub(super) fn lower_impl(&mut self, cx: Cx<'p>, id: DefId, item: onsa_syntax::ast::ItemId, i: &ImplDecl) {
        if i.trait_.is_some() {
            if let Some(dup) = i.trait_.as_ref().and_then(kind_constraint) {
                self.copy_impl(&cx, item, i, dup);
            }
            return;
        }
        let cx = self.impl_cx(cx, i);
        let aliased = self.alias_impl(&cx, i.self_ty);
        let self_ty = cx.self_ty.unwrap_or_else(|| self.a.types.error());
        let (fns, consts) = match &self.a.defs[id.0 as usize].kind {
            DefKind::Impl(imp) => (imp.fns.clone(), imp.consts.clone()),
            _ => unreachable!(),
        };
        if let DefKind::Impl(imp) = &mut self.a.defs[id.0 as usize].kind {
            imp.generics = cx.generics.clone();
            imp.self_ty = self_ty;
        }
        let (key_def, key_builtin) = self.member_key(id).unwrap_or((None, None));
        // The E0307 of an alias is the error of the heading; std's `impl`
        // of the arrays has none (§15.2, S-861).
        if !aliased && !self.std_array_impl(id) {
            self.impl_heading(&cx, i, self_ty, key_def.is_some() || key_builtin.is_some());
        }
        // A name the heading reads and the check does not (§18.1,
        // S-689): the members are checked, and read it too (an unknown
        // bound of their generics, an error type of `self`).
        let held = self.a.read_held.contains(&id);
        // The members are named before, with their E0304
        // (`Sema::name_members`), and a constant lowered in the order
        // of the declarations.
        for &sub in fns.iter().chain(&consts) {
            if held {
                self.a.read_held.insert(sub);
            }
            let sub_item = self.a.defs[sub.0 as usize].item.unwrap();
            let reach = self.type_vis((key_def, key_builtin)).map(|t| self.member_reach(&cx, sub, t));
            // `item_kind`: a `target fn` member too (S-661).
            if let ItemKind::Fn(f) = decls::item_kind(&cx.ast.item(sub_item).kind) {
                self.lower_fn(Cx { def: sub, reach, ..cx_clone(&cx) }, sub, f);
            }
        }
    }

    /// The context of the members of the inherent `impl` `i` (its `cx`): its
    /// generics, and its type as `Self` (§2.2). Its heading has no
    /// visibility (§15.1).
    pub(super) fn impl_cx(&mut self, cx: Cx<'p>, i: &ImplDecl) -> Cx<'p> {
        let mut cx = Cx { reach: None, ..cx };
        cx.generics = self.lower_generics(&cx, &i.generics);
        cx.self_ty = Some(self.lower_type(&cx, i.self_ty));
        cx
    }

    /// E0307 for the type `self_ty` of the inherent `impl` `i` written as it
    /// may not be (§6.3): with no name of a declaration (`keyed` false: a
    /// tuple, an array, `()`, a function type, a parameter; §4.4, R-320), or
    /// with type arguments other than the parameters of the `impl`, each
    /// once in any order (a concrete or compound type, one twice, one left
    /// out; §6.2, S-137), judged as written, of a target of the error type
    /// too. Arguments with an error of a name (its E0302, a name held, §18.1)
    /// are not judged; one of the types stage (an E0417, a length this version
    /// does not compute) is no parameter, and the E0307 of the names stage
    /// comes first.
    pub(super) fn impl_heading(&mut self, cx: &Cx<'p>, i: &ImplDecl, self_ty: TyId, keyed: bool) {
        let target = cx.ast.ty(i.self_ty);
        let shown = one_line(&src(cx, target.span));
        let named = self.reported.get(&cx.def).is_some_and(|&at| self.a.diagnostics[at].stage != Stage::Types);
        let named = named || self.a.read_held.contains(&cx.def);
        // A scalar (`impl F32`) has no arguments.
        let (head, written): (_, &[TypeId]) = match &target.kind {
            TypeKind::Path { path, args } => (self.a.resolve_path(cx.m, path).ok(), args),
            _ => (None, &[]),
        };
        // An opaque type of `extern` is not judged.
        let opaque = matches!(head, Some(Entity::Def(d))
            if matches!(self.a.def(d).kind, DefKind::Unsupported(Declared::Type | Declared::Block)));
        // A target whose own count of arguments is not the declared one is
        // only its E0412 (§4.5, S-759 (2')): its arguments are not judged.
        let miscounted = head.and_then(|e| self.declared_params(e)).is_some_and(|p| p.len() != written.len());
        let types = &self.a.types;
        let failed = match types.get(self_ty) {
            Ty::Named(_, args) | Ty::Builtin(_, args) => args.iter().any(|&t| types.has_error(t)),
            t => matches!(t, Ty::Error),
        };
        if (named && failed) || opaque || miscounted {
            return;
        }
        // The parameter of the `impl` an argument is: its name alone (`T`, not `T[I32]`).
        let param = |a: TypeId| match &cx.ast.ty(a).kind {
            TypeKind::Path { path, args } if args.is_empty() && path.segments.len() == 1 => {
                cx.param(&path.segments[0].name)
            }
            _ => None,
        };
        let mut seen = vec![false; cx.generics.len()];
        let wrong = written.iter().position(|&a| param(a).is_none_or(|p| std::mem::replace(&mut seen[p], true)));
        let (span, what) = match (keyed, wrong, seen.iter().position(|s| !s)) {
            (false, ..) => (target.span, format!("`{shown}` is not the name of a type declaration")),
            (true, Some(k), _) => {
                let at = cx.ast.ty(written[k]).span;
                let twice = param(written[k]).is_some();
                let how = if twice { "is written twice" } else { "is not a parameter of the `impl`" };
                (at, format!("`{}` {how}", one_line(&src(cx, at))))
            }
            (true, None, Some(g)) => {
                let name = &cx.generics[g].name;
                (target.span, format!("the parameter `{name}` of the `impl` is not an argument of `{shown}`"))
            }
            (true, None, None) => return,
        };
        let rule = "the type of an `impl` is the name of its declaration, with the parameters of the `impl` as its arguments, each once (§4.4, §6.2)";
        let d = Diagnostic::new(Stage::Names, Code::E0307, span, what).with_found(src(cx, span)).with_rule(rule);
        self.report(cx.def, d);
    }

    /// `impl Copy for X` and `impl Dup for X` (E0020, `copy_impl`, §4.6,
    /// S-140), at the form (§18.1: from `impl` to its type). The candidate
    /// takes the whole `impl` out with its doc comments and attributes (the
    /// start of its unit, §18.1), and the note names a field of `X` that does
    /// not meet the constraint ([`Sema::name_non_copy_fields`]). No note when
    /// `X` names no struct or enum (its own error goes with the `impl`).
    pub(super) fn copy_impl(&mut self, cx: &Cx<'p>, item: onsa_syntax::ast::ItemId, i: &ImplDecl, dup: bool) {
        let span = cx.ast.item(item).span;
        let units = self.module(cx.m).map(|m| &m.parsed.units);
        let unit = units.and_then(|us| us.of(span).map(|u| us.list[u].span.start));
        let fix = Fix::delete("remove the `impl`", Span { start: unit.unwrap_or(span.start), ..span });
        let form = Span { end: cx.ast.ty(i.self_ty).span.end, ..span };
        let Some(at) = self.keep(cx.def, foreign::report(RowId::CopyImpl, cx.text, form, vec![fix])) else { return };
        let TypeKind::Path { path, .. } = &cx.ast.ty(i.self_ty).kind else { return };
        if let Ok(Entity::Def(t)) = self.a.resolve_path(cx.m, path)
            && matches!(self.a.def(t).kind, DefKind::Struct(_) | DefKind::Enum(_))
        {
            self.kind_heads.push((at, t, dup));
        }
    }

    /// E0307 for an `impl` whose type `t` names a type alias (§4.4, S-91,
    /// R-105): the methods of a type are found by the name of its
    /// declaration. The candidate is the name of the type it stands for when
    /// that one is declared in the module, with no type arguments; the `impl`
    /// is lowered for that type all the same. An alias of the error type is
    /// an E0307 too, with no candidate: it stays when the alias is fixed, and
    /// is no use of the error type (§18.1, S-754). Whether `t` names an alias.
    pub(super) fn alias_impl(&mut self, cx: &Cx<'p>, t: TypeId) -> bool {
        let TypeKind::Path { path, .. } = &cx.ast.ty(t).kind else { return false };
        let Ok(Entity::Def(d)) = self.a.resolve_path(cx.m, path) else { return false };
        if !matches!(self.a.def(d).kind, DefKind::Alias(_)) {
            return false;
        }
        let ty = self.alias_ty(d);
        let shown = src(cx, path.span);
        let mut diag = Diagnostic::new(
            Stage::Names,
            Code::E0307,
            path.span,
            format!("`{shown}` is a type alias; an `impl` names the type it stands for by its declaration (§4.4)"),
        )
        .with_found(shown);
        if let Ty::Named(orig, args) = self.a.types.get(ty)
            && args.is_empty()
            && let def = self.a.def(*orig)
            && def.module == cx.m
            && def.owner.is_none()
        {
            diag = diag.with_fix(Fix::replace(format!("write `{}`", def.name), path.span, def.name.clone()));
        }
        self.report(cx.def, diag);
        true
    }

    /// How far the member `sub` of an inherent `impl` of a type of `ty_vis`
    /// reaches: the narrower of its visibility and its type's (§15.1, S-665).
    /// A `pub` on it wider than the type is redundant (E0020, S-662).
    // The E0020, reported first, is the one error of the member; an E0303 of
    // a name in its heading comes once it is fixed (S-698).
    pub(super) fn member_reach(&mut self, cx: &Cx<'p>, sub: DefId, ty_vis: Vis) -> Vis {
        let own = self.a.def(sub).vis;
        let at = self.a.def(sub).item.and_then(|i| cx.ast.item(i).vis_span);
        if let (Vis::Pub, Vis::Default | Vis::Priv, Some(at)) = (own, ty_vis, at) {
            let blanks =
                cx.text[at.end as usize..].len() - cx.text[at.end as usize..].trim_start_matches([' ', '\t']).len();
            let fix = Fix::delete("remove `pub`", Span { end: at.end + blanks as u32, ..at });
            self.report(sub, foreign::report(RowId::ImplMemberPub, cx.text, at, vec![fix]));
        }
        crate::resolve::narrower(own, ty_vis)
    }
}
