//! The lookups of a path (spec §15.1, R-39, S-611, R-250): its head in the
//! body of a module, and each element after it in what the one before names.
//! A `use` reads the same [`Modules::member`] after its own head
//! ([`Modules::head`]).

use std::collections::HashMap;

use onsa_diag::{Edit, Fix, Span};
use onsa_syntax::ast::{Ident, Path, Vis};

use crate::def::{Declared, Def, DefKind, ModId};
use crate::resolve::{Builtin, DepTarget, Entity, Modules, NameKind, ResolveError, UseAt, UseBinding};

/// The tables a path outside a `use` reads after its head.
pub(crate) type Names<'a> = (&'a HashMap<String, Entity>, &'a [Def], &'a HashMap<BuiltinTy, TyId>);
use crate::ty::{BuiltinTy, TyId};

/// The rule of a path or a `use` that names its own module (§15.1, S-673,
/// S-679).
pub(crate) const OWN_ITEMS: &str = "the items of this module are named by their names alone";

impl Modules {
    /// Whether the head `name` of a path in `from` names its own package,
    /// which no path names (§15.1, S-663, S-673): it is no head of a `use`.
    pub(crate) fn names_own_package(&self, from: ModId, name: &str) -> bool {
        self.head(from, name).is_none() && name == self.names[self.pkg_of(from)]
    }

    /// Whether a `use` added to `from` would bind `name` free in its body: a
    /// name a `use` binds that is not declared there ([`Self::declared`]).
    pub(crate) fn free_in_body(&self, from: ModId, name: &str, prelude: &HashMap<String, Entity>) -> bool {
        super::clash::unbindable(name).is_none() && !self.declared(from, name, prelude)
    }

    /// Whether `name` is declared in the body of `from` (§15.1, §5.1): what
    /// [`Self::lookup`] finds, or a name of an E0304 or an E0305. The name of
    /// a `use` that failed binds nothing, and is no partner of an E0304
    /// (§18.1, S-462). The one test of the space of the body, of a `use`
    /// added there and of a binding declared in it (S-79, S-652).
    pub(crate) fn declared(&self, from: ModId, name: &str, prelude: &HashMap<String, Entity>) -> bool {
        self.lookup(from, name, prelude).is_some() || self.get(from).clashed.body.contains(name)
    }

    /// The head `name` of a path in the body of `from` (§15.1): the prelude
    /// and the builtin types, the module's items, or the names its `use`
    /// bound, which are apart but for an E0304 (`crate::names::clash`), whose
    /// name is none of them (§18.1, S-675). Never another module or a
    /// package: they are named through a `use` alone (R-39).
    pub fn lookup(&self, from: ModId, name: &str, prelude: &HashMap<String, Entity>) -> Option<Entity> {
        let info = self.get(from);
        if info.clashed.body.contains(name) {
            return None;
        }
        if let Some(&e) = prelude.get(name) {
            return Some(e);
        }
        if let Some(&d) = info.items.get(name) {
            return Some(Entity::Def(d));
        }
        info.uses.get(name).and_then(|u| u.entity())
    }

    /// The declaration of `name` in the body of `from` that a binding of
    /// that name would hide (§5.1, S-79): what [`Self::lookup`] finds, or a
    /// name of an E0304 or an E0305, which is declared. The span is of the
    /// item or the first `use` of it, none for the prelude and the builtin
    /// types. The name of a `use` that failed binds nothing (§18.1, S-462).
    pub(crate) fn declared_in_body(
        &self,
        from: ModId,
        name: &str,
        (prelude, defs): (&HashMap<String, Entity>, &[Def]),
    ) -> Option<Option<Span>> {
        if !self.declared(from, name, prelude) {
            return None;
        }
        let info = self.get(from);
        let item = info.items.get(name).map(|d| defs[d.0 as usize].name_span);
        let used = || match info.uses.get(name) {
            Some(&UseBinding::Bound { span, .. }) => Some(span),
            _ => None,
        };
        Some(item.or_else(used))
    }

    /// The head `name` of a path in the body of `from` that [`Self::lookup`]
    /// does not find is an error (§18.1): an E0304 or E0305, the name of a
    /// `use` that failed (S-462), a head that is an E0304 (S-675), or any
    /// name when a `use` was cut before its names (R-180).
    pub(crate) fn held_as_error(&self, from: ModId, name: &str) -> bool {
        let info = self.get(from);
        info.clashed.body.contains(name)
            || info.unread_use
            || matches!(info.uses.get(name), Some(UseBinding::Failed { .. }))
            || self.clashed_heads[self.pkg_of(from)].contains(name)
    }

    /// The head of `path` in the body of `from` that is not in its body:
    /// E0302 (§15.1, R-39, S-673). When the head is one of the path of a `use`
    /// (`std.math.abs`, `util.f`), or names the own package (`fx.util.f`) or
    /// module (`main.other`, `dsp.synth.g` and `synth.g` in `dsp/synth.onsa`),
    /// the candidate reads it in this order: the own path taken off, the `use`
    /// of the head added (after the package name taken off), the own name
    /// taken off. A reading is given when the path is then read whole
    /// ([`Modules::body_fix`]); with none, the rule shows the form.
    fn not_in_body(&self, from: ModId, path: &Path, names: Names<'_>) -> ResolveError {
        let segs = &path.segments;
        let head = &segs[0];
        let is_head = self.head(from, &head.name);
        let own_pkg = self.names_own_package(from, &head.name);
        let own = self.abs_path(from, from);
        // Where the path from the root starts (after the package name), and
        // whether the own path follows.
        let at = own_pkg as usize;
        let own_path = segs.len() > at + own.len() && segs[at..at + own.len()].iter().map(|s| &s.name).eq(own.iter());
        let own_name = own.len() > 1 && own.last() == Some(&head.name);
        if is_head.is_none() && !own_pkg && !own_name {
            return ResolveError::NotFound { name: head.name.clone(), span: head.span };
        }
        let member = |k: usize| segs.get(k).and_then(|s| self.member(Entity::Module(from), s, from, names).ok());
        let root_child = || segs.get(1).and_then(|s| self.get(self.root_of(from)).children.get(&s.name).copied());
        let mut readings = Vec::new();
        if own_path {
            readings.push((at + own.len(), member(at + own.len())));
        }
        if let Some(t) = if own_pkg { root_child() } else { is_head }.filter(|&t| t != from) {
            readings.push((at, Some(Entity::Module(t))));
        }
        if own_name {
            readings.push((1, member(1)));
        }
        // The first reading given. One read whole whose `use` closes a cycle
        // is the reading too, with no candidate (S-682, S-687): the next
        // reading is of a path that is not read whole.
        let (mut fix, mut cycle) = (None, None);
        for (k, entity) in readings {
            match self.body_fix(from, path, k, entity, names) {
                Ok(f) => fix = Some(f),
                Err(Some(c)) => cycle = Some(c),
                Err(None) => continue,
            }
            break;
        }
        let names_own = own_pkg || own_path || (own_name && is_head.is_none());
        let rule = match (&fix, cycle) {
            (Some(_), _) => None,
            (None, Some((form, with))) => Some(self.closes_cycle_rule(from, &form, with)),
            _ if own_pkg => Some(
                "this package is not named in its paths: take a module by its path from the root (`use util`, \
                 then `util.…`)"
                    .to_string(),
            ),
            _ if names_own => Some(match member(at + own.len()).filter(|_| own_path) {
                Some(child @ Entity::Module(_)) => {
                    let (name, own) = (&segs[at + own.len()].name, own.join("."));
                    match self.lookup(from, name, names.0) {
                        Some(e) if e == child => {
                            format!("a child module is named by the name its `use` binds (`{name}.…`)")
                        }
                        _ if self.free_in_body(from, name, names.0) => format!(
                            "a child module is named through a `use` of its path (`use {own}.{name}`, then `{name}.…`)"
                        ),
                        _ => format!(
                            "`{name}` is bound here to another, so the child module of that name is named through \
                             a `use` of what is used from it (`use {own}.{name}.{{…}}`)"
                        ),
                    }
                }
                _ => OWN_ITEMS.to_string(),
            }),
            // A builtin name of a flow, which no `use` binds (S-542); a
            // reserved word (`static`) has its rule from W5-11 (S-674).
            _ => {
                matches!(super::clash::unbindable(&head.name), Some(super::clash::Unbindable::FlowBuiltin)).then(|| {
                    let item = segs.get(1).map_or("f", |s| s.name.as_str());
                    format!(
                        "`{0}` is a builtin name of a flow, which a `use` does not bind: take what is used from it \
                         (`use {0}.{{{item}}}`)",
                        head.name
                    )
                })
            }
        };
        ResolveError::NeedsUse { name: head.name.clone(), span: head.span, own: names_own, fix, rule }
    }

    /// The candidate that takes off the elements of `path` before `k` and
    /// reads `path[k]` as `entity`: by the name already in the body of
    /// `from`, or by a `use` of the module added when the name is free, a
    /// `use` binds it and the `use` closes no cycle. Given only when the path
    /// is then read to a name that is no module (R-268, §18.1): a module alone
    /// at the place of a value or a type (`let x = util`) is not fixed by it.
    /// When only the cycle keeps it back, the error has the path of the `use`
    /// and the module of the cycle (S-682).
    pub(crate) fn body_fix(
        &self,
        from: ModId,
        path: &Path,
        k: usize,
        entity: Option<Entity>,
        names: Names<'_>,
    ) -> Result<Fix, Option<(String, DepTarget)>> {
        let prelude = names.0;
        let segs = &path.segments;
        let (Some(entity), Some(seg)) = (entity, segs.get(k)) else { return Err(None) };
        let add = match (self.lookup(from, &seg.name, prelude), entity) {
            (Some(e), _) if e == entity => None,
            (_, Entity::Module(c)) if self.free_in_body(from, &seg.name, prelude) => {
                Some((self.abs_path(from, c).join("."), self.take_cycle(from, entity, None)))
            }
            _ => return Err(None),
        };
        // A value: the rest is its fields and methods (the types).
        let cur = match self.members(entity, &segs[k + 1..], from, names) {
            (reached, None | Some(ResolveError::NotANamespace { .. })) => reached.last().copied().unwrap_or(entity),
            (_, Some(_)) => return Err(None),
        };
        if matches!(cur, Entity::Module(_)) {
            return Err(None);
        }
        let add = match add {
            Some((added, Some(with))) => return Err(Some((added, with))),
            add => add.map(|(added, _)| added),
        };
        let info = self.get(from);
        let Some(file) = info.file else { return Err(None) };
        let (mut edits, mut title) = (Vec::new(), Vec::new());
        if k > 0 {
            let names: Vec<&str> = segs[..k].iter().map(|s| s.name.as_str()).collect();
            title.push(format!("take off `{}.`", names.join(".")));
            edits.push(Edit::delete(Span::new(file, segs[0].span.start, seg.span.start)));
        }
        if let Some(added) = add {
            title.push(format!("add `use {added}`"));
            edits.push(self.use_edit(from, &added).ok_or(None)?);
        }
        Ok(Fix::new(title.join(" and "), edits))
    }

    /// The edit that adds `use {added}` to the file of `from`, at its place
    /// ([`UseAt`]); none for a module with no file.
    fn use_edit(&self, from: ModId, added: &str) -> Option<Edit> {
        let info = self.get(from);
        let file = info.file?;
        Some(match info.use_at? {
            UseAt::After(offset) => Edit::insert(file, offset, format!("\nuse {added}")),
            UseAt::Before(offset) => Edit::insert(file, offset, format!("use {added}\n")),
        })
    }

    /// The candidate of the effect `name` not found in an effect row of
    /// `from` (§8.1, S-659 (3)): the `use` of the `pub` effect of std of that
    /// very name, when std declares one alone, the name is free in the body
    /// of `from` and the `use` closes no cycle (§18.1).
    pub(crate) fn std_effect_use(&self, from: ModId, name: &str, names: Names<'_>) -> Option<Fix> {
        let (prelude, defs, _) = names;
        let mut found = (defs.iter().enumerate()).filter(|(_, d)| {
            d.name == name && d.vis == Vis::Pub && matches!(d.kind, DefKind::Effect { .. }) && self.is_std(d.module)
        });
        let (Some((d, def)), None) = (found.next(), found.next()) else { return None };
        let taken = Entity::Def(crate::DefId(d as u32));
        if !self.free_in_body(from, name, prelude) || self.take_cycle(from, taken, Some(def.module)).is_some() {
            return None;
        }
        let added = format!("{}.{{{name}}}", self.abs_path(from, def.module).join("."));
        Some(Fix::new(format!("add `use {added}`"), vec![self.use_edit(from, &added)?]))
    }

    /// The rule of a candidate kept back as its `use` of `form`, a dependency
    /// on `target`, would close a cycle (§15.1, S-682): the form, not given
    /// as the one to write, and the modules of the cycle (as its E0310).
    pub(crate) fn closes_cycle_rule(&self, from: ModId, form: &str, target: DepTarget) -> String {
        let mut names: Vec<String> =
            self.cycle_of(from, target).into_iter().map(|m| format!("`{}`", self.get(m).path)).collect();
        names.sort();
        format!(
            "`use {form}` would make the modules {} import each other (E0310), so it is not the fix",
            names.join(", ")
        )
    }

    fn builtin_member(&self, key: TyId, name: &Ident, from: ModId, defs: &[Def]) -> Result<Entity, ResolveError> {
        if let Some(a) = self.assoc_member(self.assoc_builtin.get(&key), &name.name)? {
            let adef = &defs[a.0 as usize];
            if self.visible(adef.vis, adef.module, from) {
                return Ok(Entity::Member(a));
            }
            let why = self.hidden_why(adef.vis, None, from);
            return Err(ResolveError::NotVisible {
                name: name.name.clone(),
                span: name.span,
                defined: adef.name_span,
                why,
            });
        }
        Err(ResolveError::NotFound { name: name.name.clone(), span: name.span })
    }

    /// The member `member` of the type `ty` of the inherent `impl`, named at
    /// `name` in `from`: an E0303 when it is not visible there. It reaches as
    /// far as the narrower of its visibility and the type's (§15.1, R-38,
    /// S-491), whether named through the type (`Point.m()`) or called on a
    /// value (`p.m()`). The `impl` is in the module of the type (§6.3).
    pub(crate) fn member_reach(&self, ty: &Def, member: &Def, name: &Ident, from: ModId) -> Result<(), ResolveError> {
        if self.visible(crate::resolve::narrower(member.vis, ty.vis), ty.module, from) {
            return Ok(());
        }
        let why = self.hidden_why(member.vis, Some(("type", ty)), from);
        Err(ResolveError::NotVisible { name: name.name.clone(), span: name.span, defined: member.name_span, why })
    }

    /// A member `name` of `entity`, as seen from `from`. Of a module, its
    /// namespace: its items and its child modules, not the names its `use`
    /// bound (S-611, R-250). `builtin_key` maps a generic builtin to the
    /// `TyId` its associated items are keyed by.
    pub fn member(&self, entity: Entity, name: &Ident, from: ModId, names: Names<'_>) -> Result<Entity, ResolveError> {
        let (prelude, defs, builtin_key) = names;
        match entity {
            Entity::Module(m) => {
                // Of an E0304 or E0305, neither (§18.1, S-675).
                let info = self.get(m);
                if info.clashed.namespace.contains(&name.name) {
                    return Err(ResolveError::Failed);
                }
                if let Some(&c) = info.children.get(&name.name) {
                    return Ok(Entity::Module(c));
                }
                if let Some(&d) = info.items.get(&name.name) {
                    let def = &defs[d.0 as usize];
                    if self.visible(def.vis, m, from) {
                        return Ok(Entity::Def(d));
                    }
                    return Err(ResolveError::NotVisible {
                        name: name.name.clone(),
                        span: name.span,
                        defined: def.name_span,
                        why: self.hidden_why(def.vis, None, from),
                    });
                }
                // The names `std.core` declares that are the compiler's in
                // this version (S-659 (C)): `Option`, `Result` and the traits;
                // never a variant, `panic`, a kind constraint or a builtin type.
                if Some(m) == self.core
                    && let Some(
                        &e @ Entity::Builtin(
                            Builtin::Generic(BuiltinTy::Option | BuiltinTy::Result) | Builtin::Trait(_),
                        ),
                    ) = prelude.get(&name.name)
                {
                    return Ok(e);
                }
                // A name of a `pub use` of `m` is not found here, also at the
                // end of a path in a body (`inner.g()`, S-693); the last name
                // of a `use` is failed instead (`imports::walk`, S-596).
                Err(ResolveError::NotFound { name: name.name.clone(), span: name.span })
            }
            Entity::Def(d) => {
                let def = &defs[d.0 as usize];
                // Of an E0304, neither the members nor the variant (§18.1, S-737).
                let assoc = self.assoc_member(self.assoc.get(&d), &name.name)?;
                match &def.kind {
                    DefKind::Flow(f) => {
                        // The sizes of the state (`SIZE`, `BULK_SIZE`, the
                        // consts of a flow) are not in its namespace: the C
                        // header and `onsa interface` read them (§11.6, S-32).
                        let named = |(n, m): &&(String, crate::DefId)| {
                            n == &name.name && !matches!(defs[m.0 as usize].kind, DefKind::Const(_))
                        };
                        if let Some((_, m)) = f.members.iter().find(named) {
                            return Ok(Entity::Member(*m));
                        }
                    }
                    DefKind::Enum(e) => {
                        if let Some(i) = e.variants.iter().position(|v| v.name == name.name) {
                            return Ok(Entity::Variant(d, i as u32));
                        }
                    }
                    DefKind::Struct(_) => {}
                    // What is not read of an E0200 (an opaque type of an
                    // `extern` block, an effect): an error with no diagnostic
                    // (§18.1, S-719, S-721).
                    DefKind::Unsupported(Declared::Type | Declared::Effect) => return Err(ResolveError::Failed),
                    kind => {
                        let kind = NameKind::of_def(kind);
                        return Err(ResolveError::NotANamespace { name: def.name.clone(), span: name.span, kind });
                    }
                }
                if let Some(a) = assoc {
                    return self.member_reach(def, &defs[a.0 as usize], name, from).map(|()| Entity::Member(a));
                }
                Err(ResolveError::NotFound { name: format!("{}.{}", def.name, name.name), span: name.span })
            }
            Entity::Member(d) => {
                // `voice.State` is a struct: it may have associated items too.
                self.member(Entity::Def(d), name, from, names)
            }
            Entity::Builtin(Builtin::Scalar(t)) => self.builtin_member(t, name, from, defs),
            Entity::Builtin(Builtin::Generic(b)) => match builtin_key.get(&b) {
                Some(&t) => self.builtin_member(t, name, from, defs),
                None => Err(ResolveError::NotFound { name: name.name.clone(), span: name.span }),
            },
            // The owner's name, as of a def above (`Num.ZERO`: `Num`).
            Entity::Variant(d, i) => {
                let owner = match &defs[d.0 as usize].kind {
                    DefKind::Enum(e) => e.variants.get(i as usize).map(|v| v.name.clone()),
                    _ => None,
                };
                let owner = owner.unwrap_or_else(|| onsa_diag::internal::bug(Some(name.span), "a variant of no enum"));
                Err(ResolveError::NotANamespace { name: owner, span: name.span, kind: Some(NameKind::Variant) })
            }
            Entity::Builtin(b) => {
                let owner = prelude.iter().filter(|&(_, &e)| e == entity).map(|(n, _)| n).min();
                let owner =
                    owner.unwrap_or_else(|| onsa_diag::internal::bug(Some(name.span), "a builtin of no prelude name"));
                let kind = Some(NameKind::of_builtin(b));
                Err(ResolveError::NotANamespace { name: owner.clone(), span: name.span, kind })
            }
        }
    }

    /// Resolve a full path written outside a `use` in `from`.
    pub fn resolve_path(&self, from: ModId, path: &Path, names: Names<'_>) -> Result<Entity, ResolveError> {
        let first = &path.segments[0];
        let Some(head) = self.lookup(from, &first.name, names.0) else {
            return Err(self.head_error(from, path, names));
        };
        match self.members(head, &path.segments[1..], from, names) {
            (_, Some(err)) => Err(err),
            (reached, None) => Ok(reached.last().copied().unwrap_or(head)),
        }
    }

    /// The error of the head of `path` in the body of `from` that
    /// [`Self::lookup`] does not find: a name held as an error (§18.1), or
    /// one not in the body, with the candidate of the whole path.
    pub(crate) fn head_error(&self, from: ModId, path: &Path, names: Names<'_>) -> ResolveError {
        match self.held_as_error(from, &path.segments[0].name) {
            true => ResolveError::Failed,
            false => self.not_in_body(from, path, names),
        }
    }

    /// The members of a path after `head`: what each element of `segs`
    /// names in what the one before names ([`Self::member`]), up to the
    /// first that is no member, with its error (`NotANamespace` after a
    /// value, whose fields and methods follow). The one walk of the
    /// elements of a path outside a `use`.
    pub(crate) fn members<'i>(
        &self,
        head: Entity,
        segs: impl IntoIterator<Item = &'i Ident>,
        from: ModId,
        names: Names<'_>,
    ) -> (Vec<Entity>, Option<ResolveError>) {
        let mut reached = Vec::new();
        let mut cur = head;
        for seg in segs {
            match self.member(cur, seg, from, names) {
                Ok(next) => {
                    reached.push(next);
                    cur = next;
                }
                Err(err) => return (reached, Some(err)),
            }
        }
        (reached, None)
    }
}
