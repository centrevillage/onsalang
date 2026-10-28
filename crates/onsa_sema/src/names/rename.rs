//! The candidate of an E0320 (spec §2.3, §18.1, S-82, R-87 (5)): it renames
//! the declaration and every name of the package that names it, which the
//! stages note as they resolve it ([`Analysis::note_use`]).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, Note, Span};
use onsa_syntax::ast::Ident;

use super::body::{BindingId, BindingKind, BodyNames, ScopeId};
use super::clash::{hides, unbindable};
use crate::def::{DefId, DefKind, Fields, ModId};
use crate::resolve::Entity;
use crate::{Analysis, Package, flatten};

impl Analysis {
    /// Note the name at `at` that names what is declared at `decl`.
    pub(crate) fn note_use(&self, decl: Span, at: Span) {
        self.uses.borrow_mut().push((decl, at));
    }

    /// Note the name at `at` that names `e`: an item, a member or a variant
    /// (a module and a builtin name have no declaration a candidate edits).
    pub(crate) fn note_entity(&self, e: Entity, at: Span) {
        let decl = match e {
            Entity::Def(d) | Entity::Member(d) => Some(self.def(d).name_span),
            Entity::Variant(d, i) => self.def(d).as_enum().and_then(|en| en.variants.get(i as usize)).map(|v| v.span),
            Entity::Module(_) | Entity::Builtin(_) => None,
        };
        if let Some(decl) = decl {
            self.note_use(decl, at);
        }
    }
}

/// What a declared name is, and the span the uses of it are noted with.
enum Target {
    Item(DefId),
    /// A field of a struct or a variant of an enum, with the names of its
    /// list (and of the members of the enum).
    Member(Vec<String>),
    /// A type, const or effect parameter, with the defs whose lists hold it
    /// (an `impl` and its members).
    Param(Vec<DefId>),
    Local(DefId, BindingId),
}

/// Give each E0320 with a candidate the edits of the uses of its declaration
/// (§2.3), or a note in its place when the name by the rule clashes (S-652).
/// A declaration the analysis does not know (a parameter of a function with
/// no body) keeps the candidate of its name alone.
pub fn rename_fixes(pkg: &Package, a: &Analysis, diagnostics: &mut [Diagnostic]) {
    let flat = flatten(pkg);
    let mut tokens = HashMap::new();
    let texts: HashMap<_, &str> = flat.iter().flat_map(|p| &p.modules).map(|m| (m.file, m.text.as_str())).collect();
    let mut uses: HashMap<Span, Vec<Span>> = HashMap::new();
    for &(decl, at) in a.uses.borrow().iter() {
        uses.entry(decl).or_default().push(at);
    }
    // Built once for all the E0320 (R-305).
    let (mut targets, spaces) = (targets(a, diagnostics), Spaces::new(a));
    for (i, d) in diagnostics.iter_mut().enumerate().filter(|(_, d)| d.code == Code::E0320) {
        let (Some(fix), Some(from)) = (d.fixes.first(), d.found.clone()) else { continue };
        let Some((target, key)) = targets.remove(&i) else { continue };
        let to = fix.edits()[0].replace.clone();
        if clashes(a, &spaces, &target, d.span, &to) {
            d.fixes.clear();
            let rule = format!("the name by the rule, `{to}`, is a name here already (§2.3): rename by hand");
            d.notes.push(Note::rule(rule));
            continue;
        }
        // A name the text spells otherwise (`Self`) names the type, and stays.
        let spelled =
            |s: &&Span| texts.get(&s.file).and_then(|t| t.get(s.start as usize..s.end as usize)) == Some(&from);
        // An input of a flow is a field of the `Params` it generates too
        // (§11.6), whose uses are noted with the name of the flow.
        let params = match target {
            Target::Local(f, b) if a.names[&f].bindings[b.0 as usize].kind == BindingKind::FlowInput => {
                uses.get(&a.def(f).name_span)
            }
            _ => None,
        };
        let named = uses.get(&key).into_iter().chain(params).flatten().filter(spelled);
        let at: BTreeSet<Span> = named.copied().chain([d.span]).collect();
        // A name in a hole of a string (§2.4) is inside the token of the
        // string: the edit replaces that token (§18.1: whole tokens).
        let mut by_token: BTreeMap<Span, Vec<Span>> = BTreeMap::new();
        for s in at {
            let toks = tokens.entry(s.file).or_insert_with(|| onsa_syntax::lex(s.file, texts[&s.file]).tokens);
            let t = toks.get(toks.partition_point(|t| t.span.end <= s.start)).map(|t| t.span);
            by_token.entry(t.filter(|t| t.start <= s.start && s.end <= t.end).unwrap_or(s)).or_default().push(s);
        }
        let edits = by_token.into_iter().map(|(t, names)| {
            let mut text = texts[&t.file][t.start as usize..t.end as usize].to_string();
            for s in names.iter().rev() {
                text.replace_range((s.start - t.start) as usize..(s.end - t.start) as usize, &to);
            }
            Edit::replace(t, text)
        });
        d.fixes[0] = Fix::new(fix.title().to_string(), edits.collect());
    }
}

/// For the E0320 at index `i` of `ds` with a candidate, the declaration
/// whose name it is, and the span its uses are noted with (of the field or
/// variant, of the name of the others), in one walk of the declarations:
/// the first item or member in the order of the defs, else the parameters,
/// else a binding.
fn targets(a: &Analysis, ds: &[Diagnostic]) -> HashMap<usize, (Target, Span)> {
    let mut at: BTreeMap<(FileId, u32), Vec<usize>> = BTreeMap::new();
    for (i, d) in ds.iter().enumerate().filter(|(_, d)| d.code == Code::E0320 && !d.fixes.is_empty()) {
        at.entry((d.span.file, d.span.start)).or_default().push(i);
    }
    // The E0320 within the name `n` declared at `s`.
    let hits = |s: Span, n: &str| {
        let within = at.range((s.file, s.start)..=(s.file, s.end)).flat_map(|(_, is)| is.iter().copied());
        within.filter(|&i| ds[i].span.end <= s.end && ds[i].found.as_deref() == Some(n)).collect::<Vec<_>>()
    };
    let (mut found, mut params, mut locals) = (HashMap::new(), HashMap::<_, Vec<_>>::new(), HashMap::new());
    for (k, def) in a.defs.iter().enumerate() {
        let d = DefId(k as u32);
        for i in hits(def.name_span, &def.name) {
            found.entry(i).or_insert((Target::Item(d), def.name_span));
        }
        let list: Vec<(Span, &str)> = match &def.kind {
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => fs.iter().map(|f| (f.span, f.name.as_str())).collect(),
                _ => Vec::new(),
            },
            DefKind::Enum(e) => e.variants.iter().map(|v| (v.span, v.name.as_str())).collect(),
            _ => Vec::new(),
        };
        // A variant is in one space with the members of its enum (§6.2, S-737).
        let members = a.modules.assoc.get(&d).filter(|_| matches!(def.kind, DefKind::Enum(_))).into_iter().flatten();
        let members: Vec<&String> = members.map(|(n, _)| n).collect();
        for (i, key) in list.iter().flat_map(|&(s, n)| hits(s, n).into_iter().map(move |i| (i, s))) {
            let names =
                || list.iter().map(|(_, n)| n.to_string()).chain(members.iter().map(|n| n.to_string())).collect();
            found.entry(i).or_insert_with(|| (Target::Member(names()), key));
        }
        for i in def.generics().iter().flat_map(|g| hits(g.span, &g.name)) {
            params.entry(i).or_default().push(d);
        }
    }
    for (&d, names) in &a.names {
        for (b, x) in names.bindings.iter().enumerate() {
            for i in hits(x.span, &x.name) {
                locals.entry(i).or_insert(Target::Local(d, BindingId(b as u32)));
            }
        }
    }
    for i in at.into_values().flatten() {
        if !found.contains_key(&i)
            && let Some(t) = params.remove(&i).map(Target::Param).or_else(|| locals.remove(&i))
        {
            found.insert(i, (t, ds[i].span));
        }
    }
    found
}

/// Whether the name `to` declared at `at` in place of `target` would be an
/// E0304 (§5.1, §15.1, S-652), by the one test of a declaration ([`hides`]):
/// what it would see, and what would see it.
fn clashes(a: &Analysis, spaces: &Spaces, target: &Target, at: Span, to: &str) -> bool {
    let name = Ident { name: to.to_string(), span: at };
    match *target {
        Target::Member(ref list) => list.iter().any(|n| n == to),
        Target::Item(d) => item_clashes(a, spaces, d, to),
        Target::Param(ref defs) => {
            let visible = defs.iter().flat_map(|&d| a.def(d).generics()).find(|g| g.name == to).map(|g| g.span);
            hides(a, a.def(defs[0]).module, &name, visible, false).is_some() || defs.iter().any(|&d| binds(a, d, to))
        }
        Target::Local(d, b) => {
            let (def, names) = (a.def(d), &a.names[&d]);
            // A binding sees those declared before it in its scopes, in walk
            // order: a later one inside its scope, an earlier one around it.
            let me = names.bindings[b.0 as usize].scope;
            let sees = |(i, s): (usize, ScopeId)| match i.cmp(&(b.0 as usize)) {
                std::cmp::Ordering::Greater => within(names, s, me),
                _ => within(names, me, s),
            };
            let mut all = names.bindings.iter().enumerate();
            let local = all.find(|(i, x)| x.name == to && sees((*i, x.scope))).map(|(_, x)| x.span);
            let owner = def.owner.map_or(&[][..], |o| a.def(o).generics());
            let heading = def.generics().iter().chain(owner).find(|g| g.name == to).map(|g| g.span);
            let flow = matches!(def.kind, DefKind::Flow(_));
            hides(a, def.module, &name, local.or(heading), flow).is_some()
        }
    }
}

/// An item renamed to `to`: a member of an `impl`, of the associated items
/// and the variants of its type (§6.2); else of the spaces of the module and of the modules
/// whose `use` binds it, and of the bindings and parameters there.
fn item_clashes(a: &Analysis, spaces: &Spaces, d: DefId, to: &str) -> bool {
    let def = a.def(d);
    if def.owner.is_some() {
        let variant = |ty: DefId| a.def(ty).as_enum().is_some_and(|e| e.variants.iter().any(|v| v.name == to));
        let clashes = |(t, ty): &Table| t.contains_key(to) || ty.is_some_and(variant);
        return spaces.assoc.get(&d).is_some_and(|ts| ts.iter().any(clashes));
    }
    let used = |m: ModId| a.modules.get(m).uses.get(&def.name).and_then(|u| u.entity()) == Some(Entity::Def(d));
    let mut seen = (0..a.modules.mods.len() as u32).map(ModId).filter(|&m| m == def.module || used(m));
    let names = (&a.prelude, &a.defs[..]);
    a.modules.get(def.module).children.contains_key(to)
        || unbindable(to).is_some()
        || seen.any(|m| {
            a.modules.declared_in_body(m, to, names).is_some() || spaces.bound.get(&m).is_some_and(|b| b.contains(to))
        })
}

/// A table of associated items, and the user type it is of.
type Table<'a> = (&'a HashMap<String, DefId>, Option<DefId>);

/// The spaces [`item_clashes`] reads, built once (R-305): the tables of
/// associated items that hold each member under its name, of a user type
/// (with its def) or a builtin type, and the names of the parameters and
/// bindings of the defs of each module.
struct Spaces<'a> {
    assoc: HashMap<DefId, Vec<Table<'a>>>,
    bound: HashMap<ModId, HashSet<&'a str>>,
}

impl<'a> Spaces<'a> {
    fn new(a: &'a Analysis) -> Self {
        let mut s = Spaces { assoc: HashMap::new(), bound: HashMap::new() };
        let users = a.modules.assoc.iter().map(|(&ty, t)| (t, Some(ty)));
        for (t, ty) in users.chain(a.modules.assoc_builtin.values().map(|t| (t, None))) {
            for (_, &x) in t.iter().filter(|&(n, &x)| *n == a.def(x).name) {
                s.assoc.entry(x).or_default().push((t, ty));
            }
        }
        for (i, def) in a.defs.iter().enumerate() {
            let body = a.names.get(&DefId(i as u32)).map_or(&[][..], |n| &n.bindings[..]);
            let names = def.generics().iter().map(|g| g.name.as_str());
            s.bound.entry(def.module).or_default().extend(names.chain(body.iter().map(|b| b.name.as_str())));
        }
        s
    }
}

/// Whether the body of `d` binds `to`.
fn binds(a: &Analysis, d: DefId, to: &str) -> bool {
    a.names.get(&d).is_some_and(|n| n.bindings.iter().any(|b| b.name == to))
}

/// Whether the scope `s` is `outer` or inside it.
fn within(names: &BodyNames, mut s: ScopeId, outer: ScopeId) -> bool {
    loop {
        if s == outer {
            return true;
        }
        match names.scopes[s.0 as usize].parent {
            Some(p) => s = p,
            None => return false,
        }
    }
}
