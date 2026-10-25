//! Each `use` (spec §15.1, S-37, R-250, S-611): its path is absolute, and
//! it is resolved from the tables of the items and the modules alone, never
//! from what another `use` bound. So a `use` means the same wherever it is
//! written and whatever the other `use` of the package are (R-50).
//!
//! A `use` whose head is no head of a `use` is E0302 once every `use` is
//! resolved, with the candidate of the path it means (S-37, S-663): its
//! candidate reads what the other `use` bound, never its binding.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Ident, Vis};

use crate::Analysis;
use crate::def::{DefKind, ModId};
use crate::resolve::{Dep, Entity, Import, ResolveError, UseBinding};

use super::lookup::OWN_ITEMS;
use crate::sig::Sema;

/// What the path of a `use` in a module reads: the failure before the names
/// taken, the last module it names before them, and each name taken.
struct Walk<'i> {
    prefix: Result<(), ResolveError>,
    last: Option<ModId>,
    names: Vec<(&'i Ident, Result<Entity, ResolveError>)>,
}

/// The path of a `use` of `m`: `use a.b.{c, d}` takes `c` and `d` from
/// `a.b`, `use a.b` takes `b` from `a`, and `use a` the head itself.
fn walk<'i>(a: &Analysis, m: ModId, segs: &'i [Ident], names: Option<&'i [Ident]>) -> Walk<'i> {
    let (prefix, names): (&[Ident], Vec<&Ident>) = match names {
        Some(names) => (segs, names.iter().collect()),
        None => match segs.split_last() {
            Some((last, prefix)) => (prefix, vec![last]),
            None => (segs, Vec::new()),
        },
    };
    let mut last = None;
    let mut from = None;
    for seg in prefix {
        let next = match from {
            None => head_of(a, m, seg),
            Some(e) => step(a, e, seg, m),
        };
        match next {
            Ok(e) => {
                if let Entity::Module(c) = e {
                    last = Some(c);
                }
                from = Some(e);
            }
            Err(e) => return Walk { prefix: Err(e), last, names: Vec::new() },
        }
    }
    let names = names
        .into_iter()
        .map(|name| {
            let entity = match from {
                None => head_of(a, m, name),
                Some(e) => step(a, e, name, m),
            };
            (name, entity)
        })
        .collect();
    Walk { prefix: Ok(()), last, names }
}

impl<'p> Sema<'p> {
    /// Binds the names of each `use` of `m` in its body.
    pub(crate) fn resolve_imports(&mut self, m: ModId) {
        let imports = self.a.modules.get(m).imports.clone();
        for imp in &imports {
            self.resolve_import(m, imp);
        }
    }

    fn resolve_import(&mut self, m: ModId, imp: &Import) {
        // A head that is no head of a `use` is reported after every `use`
        // ([`Sema::report_use_heads`]), and makes no dependency.
        // SPEC-GAP(S-678): a `use` whose head fails makes no dependency, and
        // one whose path fails after the head one on the last module read.
        let w = walk(&self.a, m, &imp.path.segments, imp.names.as_deref());
        let head_fails = imp.path.segments.first().is_some_and(|h| self.a.modules.head(m, &h.name).is_none());
        let dep = |s: &mut Self, taken: Option<Entity>, name: Span| {
            if let Some(target) = s.a.modules.dep_of(m, taken, w.last) {
                s.a.modules.get_mut(m).deps.push(Dep { target, name, span: imp.span });
            }
        };
        if let Err(e) = w.prefix {
            if !head_fails {
                self.report_mod(e.into_diagnostic());
            }
            return dep(self, None, imp.path.span);
        }
        for (name, entity) in &w.names {
            match *entity {
                Ok(Entity::Module(c)) if c == m => self.report_mod(takes_itself(name)),
                // A module of a directory with no file of its own (`a` of
                // `a/b/c.onsa` alone) is a module with no items (S-666).
                Ok(e) => {
                    dep(self, Some(e), name.span);
                    self.bind(m, name, e);
                }
                Err(ref e) => {
                    if !head_fails {
                        self.report_mod(e.clone().into_diagnostic());
                    }
                    dep(self, None, name.span);
                }
            }
        }
    }

    /// `name` bound by a `use` in the body of `m`: the first of a name is in
    /// the table, and the clashes are E0304 after every `use`
    /// (`crate::names::clash`).
    fn bind(&mut self, m: ModId, name: &Ident, entity: Entity) {
        let info = self.a.modules.get_mut(m);
        info.bound.push((name.name.clone(), name.span));
        info.uses.entry(name.name.clone()).or_insert(UseBinding::Bound { entity, span: name.span });
    }

    /// The E0302 of each `use` whose head is no head of a `use` (§15.1,
    /// S-37, S-663), once every `use` is resolved and the graph is made: the
    /// candidate is the path it means, given when that path is read whole and
    /// closes no cycle (§18.1).
    pub(crate) fn report_use_heads(&mut self) {
        for i in 0..self.a.modules.mods.len() {
            let m = ModId(i as u32);
            for imp in self.a.modules.get(m).imports.clone() {
                let head = &imp.path.segments[0];
                if self.a.modules.head(m, &head.name).is_some() {
                    continue;
                }
                let mut d = ResolveError::NotFound { name: head.name.clone(), span: head.span }.into_diagnostic();
                let (fix, rule) = self.use_head_fix(m, &imp);
                if let Some(fix) = fix {
                    d = d.with_fix(fix);
                }
                if let Some(rule) = rule {
                    d = d.with_rule(rule);
                }
                self.report_mod(d);
            }
        }
    }

    /// The candidate of a `use` of `m` whose head is no head of a `use`, or
    /// the rule that shows the form when there is none. An empty list (the
    /// E0002 of S-515, W5-11) has none.
    fn use_head_fix(&self, m: ModId, imp: &Import) -> (Option<Fix>, Option<String>) {
        let segs = &imp.path.segments;
        let head = &segs[0];
        let span = |a: u32, b: u32| Span::new(head.span.file, a, b);
        if imp.names.as_ref().is_some_and(|list| list.is_empty()) {
            return (None, None);
        }
        if self.a.modules.names_own_package(m, &head.name) {
            let title = format!("take off `{}.`", head.name);
            let fix = match (&segs[1..], &imp.names) {
                ([], None) => {
                    let rule = format!(
                        "a `use` does not take its own package: take a module by its path from the root \
                         (`use util`, not `use {}`)",
                        head.name
                    );
                    return (None, Some(rule));
                }
                // One `use` per element of the list (S-663): `fx.{` and `}`
                // taken off, and a `use` before each element after the first.
                ([], Some(list)) => (distinct(list)
                    && list.iter().all(|n| self.use_reads(m, std::slice::from_ref(n), None)))
                .then(|| {
                    let kw = if imp.vis == Vis::Pub { "\npub use " } else { "\nuse " };
                    let (first, last) = (&list[0], &list[list.len() - 1]);
                    let mut edits = vec![Edit::delete(span(head.span.start, first.span.start))];
                    edits.extend(list.windows(2).map(|w| Edit::replace(span(w[0].span.end, w[1].span.start), kw)));
                    edits.push(Edit::delete(span(last.span.end, imp.span.end)));
                    Fix::new(title, edits)
                }),
                (rest, names) => self
                    .use_reads(m, rest, names.as_deref())
                    .then(|| Fix::delete(title, span(head.span.start, rest[0].span.start))),
            };
            return (fix, None);
        }
        // The head a `use` of this module bound, or a flow of it: the path of
        // what it names (S-37). Of a binding that failed, none.
        let info = self.a.modules.get(m);
        let named = match info.uses.get(&head.name) {
            Some(binding) => binding.entity(),
            None => info.items.get(&head.name).map(|&d| Entity::Def(d)),
        };
        let path = match named {
            Some(Entity::Module(c)) => self.a.modules.abs_path(m, c),
            Some(Entity::Def(d)) if matches!(self.a.def(d).kind, DefKind::Flow(_)) => {
                let def = self.a.def(d);
                let mut path = self.a.modules.abs_path(m, def.module);
                path.push(def.name.clone());
                path
            }
            _ => return (None, None),
        };
        if path.len() < 2 {
            return (None, None);
        }
        let mut new: Vec<Ident> = path.iter().map(|s| Ident { name: s.clone(), span: head.span }).collect();
        new.extend(segs[1..].iter().cloned());
        // The binding is named as the last element of its path: the path
        // before it goes in front of the head.
        let before = format!("{}.", path[..path.len() - 1].join("."));
        let fix = self.use_reads(m, &new, imp.names.as_deref()).then(|| {
            Fix::insert(format!("write the path `{}`", path.join(".")), head.span.file, head.span.start, before)
        });
        (fix, None)
    }

    /// The `use` of `segs` (and `names`) written in `m` is read whole, takes
    /// no module `m` itself, binds names free in the body of `m` and apart
    /// from each other, and none of its dependencies closes a cycle: a
    /// candidate that writes it leaves no E0302, E0303, E0304 or E0310 (§18.1).
    fn use_reads(&self, m: ModId, segs: &[Ident], names: Option<&[Ident]>) -> bool {
        if segs.first().is_none_or(|h| self.a.modules.head(m, &h.name).is_none()) || !names.is_none_or(distinct) {
            return false;
        }
        let w = walk(&self.a, m, segs, names);
        let modules = &self.a.modules;
        w.prefix.is_ok()
            && w.names.iter().all(|(n, e)| match *e {
                _ if !modules.free_in_body(m, &n.name, &self.a.prelude) => false,
                Ok(Entity::Module(c)) if c == m => false,
                Ok(e) => !modules.take_closes_cycle(m, e, w.last),
                Err(_) => false,
            })
    }
}

/// A `use` that takes the module it is written in (§15.1, S-679): E0302,
/// with no candidate.
fn takes_itself(name: &Ident) -> Diagnostic {
    let msg = format!("`{}` is this module, which a `use` does not take (§15.1)", name.name);
    Diagnostic::new(Stage::Names, Code::E0302, name.span, msg).with_found(name.name.clone()).with_rule(OWN_ITEMS)
}

/// The names of a list bind each its own name: two of one name would be the
/// E0304 of a candidate that writes them (§15.1, §18.1).
fn distinct(list: &[Ident]) -> bool {
    let mut seen = std::collections::HashSet::new();
    list.iter().all(|n| seen.insert(&n.name))
}

/// The head of the path of a `use` in `m` (§15.1, S-37): a module under the
/// package's root or a package `m`'s package depends on.
fn head_of(a: &Analysis, m: ModId, name: &Ident) -> Result<Entity, ResolveError> {
    match a.modules.head(m, &name.name) {
        Some(h) => Ok(Entity::Module(h)),
        None => Err(ResolveError::NotFound { name: name.name.clone(), span: name.span }),
    }
}

/// The element `name` after `cur` in the path of a `use` written in `from`
/// (R-250, S-611): the same as after the head of any other path.
fn step(a: &Analysis, cur: Entity, name: &Ident, from: ModId) -> Result<Entity, ResolveError> {
    a.modules.member(cur, name, from, &a.defs, &a.builtin_key)
}
