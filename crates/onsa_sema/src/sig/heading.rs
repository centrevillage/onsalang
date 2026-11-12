//! The reading of a heading (§15.1): its lists of parameters with their
//! bounds, the parameters it binds as values, and the effect rows (§8.1),
//! with the one reading of a path of a bound or an effect row.

use super::*;

impl<'p> Sema<'p> {
    pub(super) fn lower_generics(&mut self, cx: &Cx<'p>, gs: &[GenericParam]) -> Vec<GenericDef> {
        self.heading_clashes(cx.def, cx.m, gs, &cx.generics);
        let mut out = cx.generics.clone();
        // The names of the list, each seen in every bound of it.
        let listed = listed(gs, &cx.generics);
        // A bound after a parameter's `.` (`U: T.x`, `T: T.x`, always an
        // error) is read once the whole list it sees (§5.1) is lowered.
        let mut after = Vec::new();
        for g in gs {
            let def = match g {
                GenericParam::Type { name, bounds } => {
                    // The bounds read, each with its `?` and its name (S-747).
                    let mut list = Vec::new();
                    let (mut unknown, mut late) = (false, false);
                    // The path of a bound is resolved as any other (§15.1,
                    // R-278): a trait of the prelude, or a kind constraint; a
                    // user trait is an E0200 (S-719), a name of another kind
                    // an E0308 (S-713 (c)).
                    for (k, b) in bounds.iter().enumerate() {
                        let n = b.path.segments.last().unwrap();
                        if b.path.segments.len() > 1 && listed.iter().any(|l| l.0 == b.path.segments[0].name) {
                            after.push((out.len(), b));
                            late = true;
                            continue;
                        }
                        match heading_name(self.a, cx.m, &b.path, (&listed, &out, &cx.locals), cx.self_ty) {
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(Bound::Dup))))) if b.relaxed => {
                                list.push((Bound::Dup, true, n.span));
                            }
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(Bound::Escape))))) if b.relaxed => {
                                list.push((Bound::Escape, true, n.span));
                            }
                            // `?` on another trait or kind constraint (S-711).
                            Ok((NameKind::Trait | NameKind::KindConstraint, _)) if b.relaxed => {
                                self.report(cx.def, bound_list::relaxed(n));
                                unknown = true;
                            }
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(bound))))) => list.push((bound, false, n.span)),
                            // A trait of the prelude that is a bound; another
                            // trait this version does not take as a bound
                            // (E0200; with an E0308 in the unit, the first by
                            // its place, §18.1, S-731).
                            Ok((NameKind::Trait, e)) => match e {
                                Some(Entity::Builtin(Builtin::Trait(i))) => match TRAITS[i as usize] {
                                    (_, Some(bound)) => list.push((bound, false, n.span)),
                                    (name, None) => self.unsupported(cx.def, n.span, Feature::PreludeBounds, &[name]),
                                },
                                _ => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            },
                            // The Rust `Sized` and `?Sized`, no `Sized` found (S-746).
                            Err(crate::ResolveError::NotFound { .. })
                                if b.path.segments.len() == 1 && n.name == foreign::SIZED =>
                            {
                                self.sized_bound(cx, name.span.end, bounds, k);
                                unknown = true;
                            }
                            // A bound with an error of its name is a part of the
                            // declaration not read (§18.1): unknown to its users, its
                            // implicit `Dup` too (S-768 (1)).
                            r => {
                                self.bound_error(cx, &b.path, r, "a trait or a kind constraint");
                                unknown = true;
                            }
                        }
                    }
                    // A list with a contradiction is unknown to its users (S-747).
                    unknown |= self.bound_list(cx, (name.span.end, bounds), &list, unknown || late);
                    // `Dup` and `Escape` written are the implicit requirements
                    // (S-751), which every parameter has but with its `?`.
                    let bs = list.iter().filter(|b| !b.1 && b.0 != Bound::Escape).map(|b| b.0).collect();
                    let lifted = |bound| list.iter().any(|&(b, relaxed, _)| relaxed && b == bound);
                    let kind = GenericKind::Type {
                        bounds: bs,
                        dup: !lifted(Bound::Dup),
                        escape: !lifted(Bound::Escape),
                        unknown,
                    };
                    GenericDef { name: name.name.clone(), span: name.span, kind }
                }
                // Its type, which sees the whole list too, is lowered below.
                GenericParam::Const { name, .. } => GenericDef {
                    name: name.name.clone(),
                    span: name.span,
                    kind: GenericKind::Const(self.a.types.error()),
                },
                GenericParam::Effect { name } => {
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Effect }
                }
            };
            out.push(def);
        }
        // Read by the bounds known before them: an unknown one holds them.
        for &(_, b) in &after {
            let r = heading_name(self.a, cx.m, &b.path, (&listed, &out, &cx.locals), cx.self_ty);
            self.bound_error(cx, &b.path, r, "a trait or a kind constraint");
        }
        for (i, _) in after {
            if let GenericKind::Type { unknown, .. } = &mut out[i].kind {
                *unknown = true;
            }
        }
        let whole = Cx { generics: out.clone(), locals: cx.locals.clone(), ..*cx };
        for (i, g) in gs.iter().enumerate() {
            let GenericParam::Const { ty, .. } = g else { continue };
            let (t, span) = (self.lower_type(&whole, *ty), cx.ast.ty(*ty).span);
            if !matches!(self.a.types.get(t), Ty::Int(IntKind::U32) | Ty::Error) {
                let d = Feature::ConstGenericKinds.diagnostic(Stage::Names, span, &[]);
                self.report(cx.def, d.with_fix(Fix::replace("write `U32`", span, "U32")));
            }
            out[cx.generics.len() + i].kind = GenericKind::Const(t);
        }
        out
    }

    /// The error of the path `p` of a bound (`want`, "a trait"), which names
    /// a name of the kind `r` (an E0308) or none; of a name held, none (§18.1,
    /// S-689).
    fn bound_error(&mut self, cx: &Cx<'p>, p: &Path, r: Named, want: &'static str) {
        match r {
            Ok((kind, _)) => self.report(cx.def, kind_error(p, kind, want, p.span)),
            Err(e) if self.a.unread_path(cx.def, cx.m, p, &e) => {}
            Err(e) => self.report(cx.def, e.into_diagnostic()),
        }
    }

    /// The trait the path `p` of an `impl p for Ty` names (§6.3, S-895), read
    /// as the path of a bound: none with its error (E0302, E0308), or of a
    /// name held (§18.1).
    pub(super) fn lower_trait(&mut self, cx: &Cx<'p>, p: &Path) -> Option<Entity> {
        let listed = listed(&[], &cx.generics);
        match heading_name(self.a, cx.m, p, (&listed, &cx.generics, &cx.locals), None) {
            Ok((NameKind::Trait, e)) => e,
            r => {
                self.bound_error(cx, p, r, "a trait");
                None
            }
        }
    }

    /// The effects of a row of a signature or a function type
    /// ([`read_effects`]): its errors are reported, and the lowering goes on.
    pub(super) fn lower_effects(&mut self, cx: &Cx<'p>, row: Option<&EffectRow>) -> EffectSet {
        let (set, errors) = read_effects(self.a, cx.def, cx.m, (&cx.generics, cx.self_ty, &cx.locals), row);
        for d in errors {
            self.report(cx.def, d);
        }
        set
    }
}

/// The parameters `params` of a heading of the type, const and effect
/// parameters `generics` (and those of `cx`, of its `impl`), `self` of a
/// method too, of a flow (`flow`) or not: values its whole heading sees
/// (§5.1, S-741, S-733). One that is an E0304 ([`hides`], as the body
/// declares it) is none: its name names what it clashes with (§18.1, S-675).
/// A name of one at the head of a path of `types` (and of the constant
/// expressions in them) or of `paths` (bounds, the effect row) is a use of
/// it, which an E0320 renames (§2.3).
pub(super) fn heading_locals(
    a: &Analysis,
    cx: &Cx<'_>,
    (params, generics, flow): (&[Param], &[GenericParam], bool),
    (types, paths): (Vec<TypeId>, Vec<&Path>),
) -> HashSet<String> {
    let mut seen: HashMap<&str, Span> = cx.generics.iter().map(|g| (g.name.as_str(), g.span)).collect();
    seen.extend(generics.iter().map(crate::names::param_name).map(|n| (n.name.as_str(), n.span)));
    let mut declared = HashMap::default();
    for p in params {
        let (name, span) = match &p.name {
            ParamName::Ident(i) => (i.name.as_str(), i.span),
            ParamName::SelfParam(s) if cx.self_ty.is_some() => (crate::names::SELF_VALUE, *s),
            _ => continue,
        };
        let visible = seen.get(name).copied();
        seen.entry(name).or_insert(span);
        let ident = Ident { name: name.to_string(), span };
        if crate::names::hides(a, cx.m, &ident, visible, flow).is_none() {
            declared.insert(name, span);
        }
    }
    let mut names = Vec::new();
    types.into_iter().for_each(|t| crate::names::body::heads(cx.ast, t, &mut names));
    names.extend(paths.into_iter().filter_map(|p| p.segments.first()));
    for n in names {
        if let Some(&decl) = declared.get(n.name.as_str()) {
            a.note_use(decl, n.span);
        }
    }
    declared.into_keys().map(str::to_string).collect()
}

/// The one reading of an effect row (§8.1, S-74, D-08), of a signature, of a
/// function type and of a closure: a single name of an effect variable of
/// `generics`, else a path as [`heading_name`] reads it (§15.1). `Alloc` (the
/// lang item) is read; another effect is an E0200 at its name, but in std,
/// which declares them (S-659); a name of another kind is an E0308 (S-713
/// (b)). A name not found is its E0302, with the `use` of the effect std
/// declares of that name as the candidate (S-659 (3)); a name the check does
/// not read is left out with no diagnostic (§18.1; read by `def`,
/// [`Analysis::unread_path`]). The same effect or effect row variable twice,
/// as read (`Alloc` and `core.Alloc`), is the E0602 of the second (§8.1,
/// S-750), among the others by its place. The errors go back to the caller,
/// which reports them.
// The effects read stay when a name held as an error is left out, as an
// unknown effect of an open row, and the check goes on (§18.1, S-691).
// A local it sees (`locals`, S-738) is a value, no effect.
pub(crate) fn read_effects(
    a: &mut Analysis,
    def: DefId,
    from: crate::ModId,
    (generics, self_ty, locals): (&[GenericDef], Option<TyId>, &HashSet<String>),
    row: Option<&EffectRow>,
) -> (EffectSet, Vec<Diagnostic>) {
    let mut set = EffectSet::default();
    let mut errors = Vec::new();
    // What each element read names: an effect row variable or a definition.
    let mut read: Vec<(Result<u32, DefId>, &Path)> = Vec::new();
    let listed = listed(&[], generics);
    for p in row.map_or(&[][..], |r| &r.effects[..]) {
        let n = p.segments.last().unwrap();
        let var = generics.iter().position(|g| g.name == n.name && matches!(g.kind, GenericKind::Effect));
        if let (1, Some(i)) = (p.segments.len(), var) {
            a.note_use(generics[i].span, n.span);
            set.vars.push(i as u32);
            read.push((Ok(i as u32), p));
            continue;
        }
        let named = heading_name(a, from, p, (&listed, generics, locals), self_ty);
        if let Ok((_, Some(Entity::Def(d)))) = named {
            read.push((Err(d), p));
        }
        match named {
            Ok((_, Some(Entity::Def(d)))) if Some(d) == a.alloc => set.alloc = true,
            Ok((_, Some(Entity::Def(d))))
                if matches!(a.def(d).kind, DefKind::Effect { .. }) && a.modules.is_std(from) =>
            {
                set.other.push(n.name.clone());
            }
            // Another effect (of a user's `effect`, S-719, E0200); or a name
            // that is no effect (`uses {I32}`, `uses {T}`). With both in a
            // unit, the first by its place is reported (§18.1, S-731).
            Ok((kind, _)) => {
                errors.push(match kind {
                    NameKind::Effect => Feature::Effects.diagnostic(Stage::Names, n.span, &[&n.name]),
                    kind => kind_error(p, kind, "an effect", p.span),
                });
                set.other.push(n.name.clone());
            }
            Err(e) if a.unread_path(def, from, p, &e) => {}
            Err(e) => {
                let fix = match (&e, p.segments.as_slice()) {
                    (crate::ResolveError::NotFound { .. }, [_]) => {
                        a.modules.std_effect_use(from, &n.name, (&a.prelude, &a.defs, &a.builtin_key))
                    }
                    _ => None,
                };
                let d = e.into_diagnostic();
                errors.push(match fix {
                    Some(fix) => d.with_fix(fix),
                    None => d,
                });
            }
        }
    }
    if let Some((before, k)) = onsa_diag::first_repeat(read.iter().map(|r| r.0)) {
        let (key, p) = read[k];
        // By its name, not as written: the two may be spelled apart (`Alloc`, `core.Alloc`).
        let what = match key {
            Ok(i) => format!("the effect row variable `{}`", generics[i as usize].name),
            Err(d) => format!("the effect `{}`", a.def(d).name),
        };
        let d = onsa_diag::repeated(Stage::Names, Code::E0602, p.span, read[before].1.span, &what);
        let place = errors.partition_point(|e| e.span.start <= p.span.start);
        errors.insert(place, d.with_found(p.dotted()));
    }
    (set, errors)
}

/// Whether the path `tr` of `impl[gs] tr for Ty` names a trait by the names
/// alone, read as [`Sema::lower_trait`] reads it before the list `gs` is
/// lowered (§18.1, S-1019): a name not found, held, or of another kind
/// (a parameter of `gs`) is none.
pub(super) fn names_trait(a: &Analysis, m: ModId, gs: &[GenericParam], tr: &Path) -> bool {
    let read = heading_name(a, m, tr, (&listed(gs, &[]), &[], &HashSet::default()), None);
    matches!(read, Ok((NameKind::Trait, _)))
}

/// What [`heading_name`] reads of a path.
type Named = Result<(NameKind, Option<Entity>), crate::ResolveError>;

/// The kind of what the path `p` of a bound or an effect row names (§15.1),
/// and what it names but a parameter of the heading of `listed` (the names a
/// heading binds that are no item of a module, with their kinds, the
/// parameters `generics` lowered so far, and the values `locals` the place
/// sees, [`Cx::locals`]) and an associated name of a builtin type: through
/// `Self` (`self_ty`) and the aliases ([`Analysis::path_end`]). After a
/// parameter of a list is what [`param_member`] reads (of its head not found
/// when it is not lowered yet); a local has no members (its E0308).
fn heading_name(
    a: &Analysis,
    from: ModId,
    p: &Path,
    (listed, generics, locals): (&[(&str, NameKind)], &[GenericDef], &HashSet<String>),
    self_ty: Option<TyId>,
) -> Named {
    let head = &p.segments[0];
    let local = locals.contains(&head.name).then_some(NameKind::Local);
    if let Some(kind) = local.or_else(|| listed.iter().find(|(n, _)| *n == head.name).map(|&(_, k)| k)) {
        return match &p.segments[1..] {
            [] => Ok((kind, None)),
            [next, ..] if kind == NameKind::Local => Err(member_error(head, next, NameKind::Local)),
            _ => param_member(a, generics, p)
                .unwrap_or_else(|| Err(crate::ResolveError::NotFound { name: head.name.clone(), span: head.span }))
                .map(|kind| (kind, None)),
        };
    }
    let end = a.path_end(from, p, self_ty)?;
    let entity = match end {
        crate::names::PathEnd::Entity(e) => Some(e),
        crate::names::PathEnd::Builtin { .. } => None,
    };
    Ok((end.kind(a, p.span), entity))
}

/// What the path `p` names after the parameter of `generics` at its head
/// (§15.1, R-370, R-404): the kind of the member the bounds of
/// a type parameter give (an E0308 where the place takes another kind), the
/// E0302 of one they do not give, held (`Failed`, no diagnostic) when they
/// are unknown (§18.1); after a const parameter, a value, and an effect row
/// variable (R-406), the E0308 of a name with no members. None when `p`
/// starts at no such parameter.
pub(super) fn param_member(a: &Analysis, generics: &[GenericDef], p: &Path) -> Option<Member> {
    let [head, name, rest @ ..] = &p.segments[..] else { return None };
    let g = generics.iter().find(|g| g.name == head.name)?;
    a.note_use(g.span, head.span);
    let GenericKind::Type { bounds, unknown, .. } = &g.kind else {
        return Some(Err(member_error(head, name, NameKind::of_generic(&g.kind))));
    };
    // S-953 (§18.1): a member a known bound gives is held too when another
    // bound is unknown (`T: Float + Gone`, `T: Float + ?Dup` of `T.PI`).
    if *unknown {
        return Some(Err(crate::ResolveError::Failed));
    }
    let Some(member) = crate::traits::member(a, bounds, &name.name) else {
        return Some(Err(crate::ResolveError::NotFound { name: name.name.clone(), span: name.span }));
    };
    let kind = NameKind::of_named(Entity::Member(member), &a.defs, name.span);
    Some(rest.first().map_or(Ok(kind), |next| Err(member_error(name, next, kind))))
}

/// What [`param_member`] reads of a path.
type Member = Result<NameKind, crate::ResolveError>;

/// The error of `next` after `head` of the kind `kind`, a value (a local,
/// a const parameter) or another name with no members (§15.1, S-729,
/// S-741): E0308, in a heading, in a type and after a parameter in a body.
pub(crate) fn member_error(head: &Ident, next: &Ident, kind: NameKind) -> crate::ResolveError {
    crate::ResolveError::NotANamespace { name: head.name.clone(), span: next.span, kind: Some(kind) }
}

/// E0308 for the path `p` at `span`, of the kind `kind`, where `want` is
/// (§15.1): the one form of a signature.
pub(super) fn kind_error(p: &Path, kind: NameKind, want: &'static str, span: Span) -> Diagnostic {
    let shown = p.segments.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join(".");
    crate::ResolveError::Kind { shown, span, kind, want }.into_diagnostic()
}

/// The names a heading binds that are no item of a module, with their kinds
/// ([`heading_name`]): the parameters of the list `gs` being lowered, then
/// those in scope `generics` (of the `impl`, and of the item once lowered).
fn listed<'a>(gs: &'a [GenericParam], generics: &'a [GenericDef]) -> Vec<(&'a str, NameKind)> {
    let lowered = generics.iter().map(|g| (g.name.as_str(), NameKind::of_generic(&g.kind)));
    gs.iter().map(|g| (crate::names::param_name(g).name.as_str(), param_kind(g))).chain(lowered).collect()
}

/// The kind of a parameter of a list of a heading (§15.1).
fn param_kind(g: &GenericParam) -> NameKind {
    match g {
        GenericParam::Type { .. } => NameKind::Type,
        GenericParam::Const { .. } => NameKind::ConstParam,
        GenericParam::Effect { .. } => NameKind::EffectVar,
    }
}
