//! An `impl` (§6.3): its members and their context, the type it names
//! (E0307) and how far a member reaches; the heading of `impl Tr for Ty`
//! (§18.1, S-895), whose items are `impl_items`; and `impl Copy` and `impl
//! Dup` (§4.6).

use super::*;
use crate::names::collect::reads_members;
use crate::traits::no_impl;

impl<'p> Sema<'p> {
    /// The `impl` `i` (the def `id` of the item `item`): its heading and, of
    /// one whose members are read, its members; of `impl Tr for Ty`, its
    /// heading, and of `impl Copy` and `impl Dup`, their E0020.
    pub(super) fn lower_impl(&mut self, cx: Cx<'p>, id: DefId, item: onsa_syntax::ast::ItemId, i: &ImplDecl) {
        if let Some(dup) = i.trait_.as_ref().and_then(kind_constraint) {
            return self.copy_impl(&cx, item, i, dup);
        }
        let cx = self.impl_cx(cx, i);
        let aliased = self.alias_impl(&cx, i.self_ty);
        let self_ty = cx.self_ty.unwrap_or_else(|| self.a.types.error());
        if let Some(tr) = &i.trait_ {
            self.trait_heading(&cx, i, tr, aliased, self_ty);
            // The form this version does not have, whatever the trait
            // (S-895): a name held stays an E0200 once it is fixed (X-23).
            if !reads_members(i) {
                if !self.name_reported(id) {
                    self.unsupported(id, self.a.def(id).span, Feature::TraitImpls, &[]);
                }
                return;
            }
        }
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
        if i.trait_.is_none() && !aliased && !self.std_array_impl(id) && !self.orphan_impl(&cx, i, self_ty) {
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
            let reach = self.type_vis((key_def, key_builtin)).map(|t| self.member_reach(&cx, i, sub, t));
            // `item_kind`: a `target fn` member too (S-661).
            if let ItemKind::Fn(f) = decls::item_kind(&cx.ast.item(sub_item).kind) {
                self.lower_fn(Cx { def: sub, reach, ..cx_clone(&cx) }, sub, f);
            }
        }
    }

    /// The context of the members of the `impl` `i` (its `cx`): its
    /// generics, and its type as `Self` (§2.2). Its heading has no
    /// visibility (§15.1).
    pub(super) fn impl_cx(&mut self, cx: Cx<'p>, i: &ImplDecl) -> Cx<'p> {
        let mut cx = Cx { reach: None, ..cx };
        cx.generics = self.lower_generics(&cx, &i.generics);
        cx.self_ty = Some(self.lower_type(&cx, i.self_ty));
        cx
    }

    /// The heading of `impl tr for Ty`, read as that of an inherent `impl` up
    /// to the names stage (§18.1, S-895). Of a trait this version does not
    /// open, what it gets of the types stage (E0412) goes out with the E0200
    /// of the form, and its E0416 is not judged (`Sema::wellformed`).
    fn trait_heading(&mut self, cx: &Cx<'p>, i: &ImplDecl, tr: &Path, aliased: bool, self_ty: TyId) {
        let named = self.lower_trait(cx, tr);
        i.trait_args.iter().for_each(|&t| _ = self.lower_type(cx, t));
        let target = self.target_type(cx, i.self_ty);
        let shown = one_line(&src(cx, cx.ast.ty(i.self_ty).span));
        match (named, target) {
            (Some(Entity::Builtin(Builtin::Trait(row))), _) if TRAITS[row as usize].1.is_some_and(no_impl) => {
                let what = format!("`{}` has no `impl` but the ones of the language", TRAITS[row as usize].0);
                let d = Diagnostic::new(Stage::Names, Code::E0307, tr.span, what).with_found(src(cx, tr.span));
                let rule = "the builtin floats alone are `Float`, and a derive alone makes `Ordinal` (§6.3, §6.4)";
                self.report(cx.def, d.with_rule(rule));
            }
            (Some(t), Some(e)) if !aliased && !self.defines(cx.m, t) && !self.defines(cx.m, e) => {
                let what = format!("neither `{}` nor `{shown}` is defined in this module", src(cx, tr.span));
                self.orphan(cx, i, what);
            }
            _ if !aliased => {
                let keyed = target.is_some_and(|e| self.type_key(e).is_some());
                self.impl_heading(cx, i, self_ty, keyed);
            }
            _ => {}
        }
    }

    /// Whether the unit `def` has a diagnostic out of the types stage.
    fn name_reported(&self, def: DefId) -> bool {
        self.reported.get(&def).is_some_and(|&at| self.a.diagnostics[at].stage != Stage::Types)
    }

    /// The type the path `t` names by its declaration; none for another name.
    fn target_type(&self, cx: &Cx<'p>, t: TypeId) -> Option<Entity> {
        let TypeKind::Path { path, .. } = &cx.ast.ty(t).kind else { return None };
        let e = self.a.resolve_path(cx.m, path).ok()?;
        (NameKind::of(e, &self.a.defs) == Some(NameKind::Type)).then_some(e)
    }

    /// Whether the module `m` defines the type or the trait `e` (§6.3): a
    /// generated type is of the module of its flow (§11.6), and a builtin
    /// type and a trait of the prelude of std.
    fn defines(&self, m: ModId, e: Entity) -> bool {
        match e {
            Entity::Def(d) | Entity::Member(d) => self.a.def(d).module == m,
            _ => self.a.modules.is_std(m),
        }
    }

    /// E0307 for the inherent `impl` `i` out of the module of its type
    /// `self_ty` (§6.3, S-70), whether it is one. A second-class type has its
    /// E0710 (§5.3, §15.2), and a name not read none.
    fn orphan_impl(&mut self, cx: &Cx<'p>, i: &ImplDecl, self_ty: TyId) -> bool {
        let Some(e) = self.target_type(cx, i.self_ty) else { return false };
        if self.defines(cx.m, e) || second_class(self.a, self_ty) {
            return false;
        }
        let shown = one_line(&src(cx, cx.ast.ty(i.self_ty).span));
        self.orphan(cx, i, format!("`{shown}` is not defined in this module"));
        true
    }

    /// The E0307 `what` of the orphan rule, at the target of `i`.
    fn orphan(&mut self, cx: &Cx<'p>, i: &ImplDecl, what: String) {
        let span = cx.ast.ty(i.self_ty).span;
        let rule = "an `impl` is written in the module that defines its type or its trait, and std defines the builtin types (§6.3)";
        let d = Diagnostic::new(Stage::Names, Code::E0307, span, what).with_found(src(cx, span)).with_rule(rule);
        self.report(cx.def, d);
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
        let named = self.name_reported(cx.def) || self.a.read_held.contains(&cx.def);
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

    /// How far the member `sub` of the `impl` `i` of a type of `ty_vis`
    /// reaches: the narrower of its visibility and its type's (§15.1, S-665).
    /// A `pub` on it wider than the type is redundant (E0020, S-662), and any
    /// word on a member of a trait's `impl`, which has its type's (S-904).
    // The E0020, reported first, is the one error of the member; an E0303 of
    // a name in its heading comes once it is fixed (S-698).
    pub(super) fn member_reach(&mut self, cx: &Cx<'p>, i: &ImplDecl, sub: DefId, ty_vis: Vis) -> Vis {
        let own = self.a.def(sub).vis;
        let at = self.a.def(sub).item.and_then(|i| cx.ast.item(i).vis_span);
        if let (true, Some(at)) = (i.trait_.is_some() || (own == Vis::Pub && ty_vis != Vis::Pub), at) {
            let blanks =
                cx.text[at.end as usize..].len() - cx.text[at.end as usize..].trim_start_matches([' ', '\t']).len();
            let fix = Fix::delete(format!("remove `{}`", src(cx, at)), Span { end: at.end + blanks as u32, ..at });
            self.report(sub, foreign::report(RowId::ImplMemberPub, cx.text, at, vec![fix]));
        }
        crate::resolve::narrower(own, ty_vis)
    }
}
