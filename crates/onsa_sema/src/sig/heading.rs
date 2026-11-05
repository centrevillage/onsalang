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
        for g in gs {
            let def = match g {
                GenericParam::Type { name, bounds } => {
                    // The bounds read, each with its `?` and its name (S-747).
                    let mut list = Vec::new();
                    let mut unknown = false;
                    // The path of a bound is resolved as any other (§15.1,
                    // R-278): a trait of the prelude, or a kind constraint; a
                    // user trait is an E0200 (S-719), a name of another kind
                    // an E0308 (S-713 (c)).
                    for b in bounds {
                        let n = b.path.segments.last().unwrap();
                        match heading_name(self.a, cx.m, &b.path, (&listed, &cx.locals), cx.self_ty) {
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(Bound::Dup))))) if b.relaxed => {
                                list.push((Bound::Dup, true, n.span));
                            }
                            // SPEC-GAP(S-868): `?Escape` is an E0200 (S-862), and the
                            // parameter is read as one without it: its users get the
                            // E0710 of a second-class type argument (b1).
                            Ok((_, Some(Entity::Builtin(Builtin::Kind(Bound::Escape))))) if b.relaxed => {
                                self.unsupported(cx.def, n.span, Feature::RelaxedEscape, &[]);
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
                            // `AnyNum` and `Int` are bounds of std only until W5-05 (D4).
                            Ok((NameKind::Trait, e)) => match e.and_then(prelude_bound) {
                                Some(Bound::AnyNum | Bound::Int) if !self.a.modules.is_std(cx.m) => {
                                    self.unsupported(cx.def, n.span, Feature::TraitBounds, &[])
                                }
                                Some(bound) => list.push((bound, false, n.span)),
                                None => self.unsupported(cx.def, n.span, Feature::TraitBounds, &[]),
                            },
                            // A bound with an error of its name is a part of the
                            // declaration not read (§18.1): unknown to its users, its
                            // implicit `Dup` too (S-768 (1)).
                            Ok((kind, _)) => {
                                let d = kind_error(&b.path, kind, "a trait or a kind constraint", b.path.span);
                                self.report(cx.def, d);
                                unknown = true;
                            }
                            // An unknown bound (§18.1, S-689).
                            Err(e) if self.a.unread_path(cx.def, cx.m, &b.path, &e) => unknown = true,
                            Err(e) => {
                                self.report(cx.def, e.into_diagnostic());
                                unknown = true;
                            }
                        }
                    }
                    // A list with a contradiction is unknown to its users (S-747).
                    unknown |= self.bound_list(cx.def, &list);
                    // SPEC-GAP(S-868): `T: Escape` is the implicit requirement
                    // written, met as `T: Dup` is (a1); every parameter has it.
                    let bs = list.iter().filter(|b| !b.1 && b.0 != Bound::Escape).map(|b| b.0).collect();
                    let dup = !list.iter().any(|b| b.1);
                    let kind = GenericKind::Type { bounds: bs, dup, unknown };
                    GenericDef { name: name.name.clone(), span: name.span, kind }
                }
                GenericParam::Const { name, ty } => {
                    let t = self.lower_type(cx, *ty);
                    if !matches!(self.a.types.get(t), Ty::Int(IntKind::U32) | Ty::Error) {
                        self.report(
                            cx.def,
                            Feature::ConstGenericKinds
                                .diagnostic(Stage::Names, cx.ast.ty(*ty).span, &[])
                                .with_fix(Fix::replace("write `U32`", cx.ast.ty(*ty).span, "U32")),
                        );
                    }
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Const(t) }
                }
                GenericParam::Effect { name } => {
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Effect }
                }
            };
            out.push(def);
        }
        out
    }

    /// The trait the path `p` of an `impl p for Ty` names (§6.3, S-895), read
    /// as the path of a bound: none with its error (E0302, E0308), or of a
    /// name held (§18.1).
    pub(super) fn lower_trait(&mut self, cx: &Cx<'p>, p: &Path) -> Option<Entity> {
        let listed = listed(&[], &cx.generics);
        match heading_name(self.a, cx.m, p, (&listed, &cx.locals), None) {
            Ok((NameKind::Trait, e)) => return e,
            Ok((kind, _)) => self.report(cx.def, kind_error(p, kind, "a trait", p.span)),
            Err(e) if self.a.unread_path(cx.def, cx.m, p, &e) => {}
            Err(e) => self.report(cx.def, e.into_diagnostic()),
        }
        None
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
/// [`Analysis::unread_path`]). The errors go back to the caller, which
/// reports them.
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
    let listed = listed(&[], generics);
    for p in row.map_or(&[][..], |r| &r.effects[..]) {
        let n = p.segments.last().unwrap();
        let var = generics.iter().position(|g| g.name == n.name && matches!(g.kind, GenericKind::Effect));
        if let (1, Some(i)) = (p.segments.len(), var) {
            a.note_use(generics[i].span, n.span);
            set.vars.push(i as u32);
            continue;
        }
        match heading_name(a, from, p, (&listed, locals), self_ty) {
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
    (set, errors)
}

/// The kind of what the path `p` of a bound or an effect row names (§15.1),
/// and what it names but a parameter of the heading of `listed` (the names a
/// heading binds that are no item of a module, with their kinds, and the
/// values `locals` the place sees, [`Cx::locals`]) and an
/// associated name of a builtin type: through `Self` (`self_ty`) and the
/// aliases ([`Analysis::path_end`]). A parameter of a list has no members
/// (the E0302 of its head), a local neither (its E0308).
fn heading_name(
    a: &Analysis,
    from: ModId,
    p: &Path,
    (listed, locals): (&[(&str, NameKind)], &HashSet<String>),
    self_ty: Option<TyId>,
) -> Result<(NameKind, Option<Entity>), crate::ResolveError> {
    let head = &p.segments[0];
    let local = locals.contains(&head.name).then_some(NameKind::Local);
    if let Some(kind) = local.or_else(|| listed.iter().find(|(n, _)| *n == head.name).map(|&(_, k)| k)) {
        return match &p.segments[1..] {
            [] => Ok((kind, None)),
            [next, ..] if kind == NameKind::Local => Err(local_member(head, next)),
            _ => Err(crate::ResolveError::NotFound { name: head.name.clone(), span: head.span }),
        };
    }
    let end = a.path_end(from, p, self_ty)?;
    let entity = match end {
        crate::names::PathEnd::Entity(e) => Some(e),
        crate::names::PathEnd::Builtin { .. } => None,
    };
    Ok((end.kind(a, p.span), entity))
}

/// The bound a trait of the prelude `e` is ([`TRAITS`]); none for another
/// name.
fn prelude_bound(e: Entity) -> Option<Bound> {
    match e {
        Entity::Builtin(Builtin::Trait(i)) => TRAITS[i as usize].1,
        _ => None,
    }
}

/// The error of `next` after the local `head` (§15.1, S-729, S-741): a
/// value, which has no members (E0308), in a heading and in a type.
pub(super) fn local_member(head: &Ident, next: &Ident) -> crate::ResolveError {
    crate::ResolveError::NotANamespace { name: head.name.clone(), span: next.span, kind: Some(NameKind::Local) }
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
        GenericParam::Effect { .. } => NameKind::Effect,
    }
}
