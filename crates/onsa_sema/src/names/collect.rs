//! The module tree of every package (spec §15.1, S-312, S-313) and the defs
//! and the tables of the items of every module.

use std::collections::HashMap;

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{
    Ast, ExprId, ExprKind, Failed, GenericParam, Ident, ImplDecl, Item, ItemId, ItemKind, Lit, StrLit, UseDecl, Vis,
};

use crate::def::*;
use crate::resolve::{Import, ModInfo, UseAt};
use crate::sig::Sema;
use crate::ty::EffectSet;

impl<'p> Sema<'p> {
    /// Each package's root, and each module at the path of its parts from
    /// the root; a part with no module of its own is a module of a
    /// directory only. The modules of a package are one for each path of
    /// parts (§15.1): a second file of the same parts is an internal error.
    /// Then the heads of the paths of `use` ([`crate::resolve::Modules::heads`]).
    pub(crate) fn build_module_tree(&mut self) {
        let flat = self.flat.clone();
        for (pkg, p) in flat.iter().enumerate() {
            let root = self.a.modules.add(new_module(String::new(), pkg, None));
            self.a.modules.roots.push(root);
            self.a.modules.names.push(p.name.clone());
            self.a.modules.roles.push(p.role);
            for (i, m) in p.modules.iter().enumerate() {
                let at = self.module_at(root, &m.segments, Span::empty(m.file, 0));
                let info = self.a.modules.get_mut(at);
                if info.module.is_some() {
                    onsa_diag::internal::bug(
                        Some(Span::empty(m.file, 0)),
                        format!("two files of the package `{}` are the module `{}`", p.name, m.path()),
                    );
                }
                info.module = Some(i);
                info.file = Some(m.file);
            }
        }
        for p in &flat {
            let root = self.a.modules.roots[self.a.modules.heads.len()];
            let mut heads = self.a.modules.get(root).children.clone();
            // A module under the root of the same name as a dependency is an
            // E0304 of the module (S-246, W4-03 U3a); the name is the package.
            for d in &p.deps {
                let Some(i) = flat.iter().position(|q| std::ptr::eq(*q, &**d)) else {
                    onsa_diag::internal::bug(None, format!("the dependency `{}` is not in the graph", d.name))
                };
                heads.insert(d.name.clone(), self.a.modules.roots[i]);
            }
            self.a.modules.heads.push(heads);
            self.a.modules.clashed_heads.push(Default::default());
        }
    }

    /// The module at `segments` under `root`, made with the modules of the
    /// directories on the way when they are not there yet.
    fn module_at(&mut self, root: ModId, segments: &[String], at: Span) -> ModId {
        if segments.is_empty() {
            onsa_diag::internal::bug(Some(at), "a module with no path");
        }
        let pkg = self.a.modules.pkg_of(root);
        let mut cur = root;
        for (k, seg) in segments.iter().enumerate() {
            cur = match self.a.modules.get(cur).children.get(seg) {
                Some(&c) => c,
                None => {
                    let c = self.a.modules.add(new_module(segments[..=k].join("."), pkg, Some(cur)));
                    self.a.modules.get_mut(cur).children.insert(seg.clone(), c);
                    c
                }
            };
        }
        cur
    }

    /// The defs of the items of every module, in the order of the modules
    /// and of the items, with the module's table of their names and its
    /// list of `use` (resolved by [`Sema::resolve_imports`]).
    pub(crate) fn collect_items(&mut self) {
        // The placeholders until the signatures are lowered.
        let error = self.a.types.error();
        let unit = self.a.types.unit();
        for i in 0..self.a.modules.mods.len() {
            let m = ModId(i as u32);
            let Some(module) = self.module(m) else { continue };
            let ast = &module.parsed.ast;
            self.a.modules.get_mut(m).use_at = use_at(&module.parsed);
            let mut tests: HashMap<String, DefId> = HashMap::new();
            for &id in &ast.root {
                let item = ast.item(id);
                // A panic names this item (S-67).
                let _scope = onsa_diag::internal::item_scope(item.span);
                let mut at = Place { m, ast, id, item, error, unit, target: false };
                match &item.kind {
                    ItemKind::Use(u) if matches!(item.failed, Some(Failed::Body | Failed::Heading)) => {
                        self.cut_use(m, u, item.vis)
                    }
                    ItemKind::Use(u) => self.collect_use(m, item, id, u),
                    ItemKind::Impl(decl) => self.collect_impl(&at, decl),
                    ItemKind::Extern(e) => {
                        let d = self.add_def(at.def("<extern>".into(), item.span, DefKind::Unsupported));
                        self.unsupported(d, item.span, Feature::Extern, &[]);
                        // Its functions and types are names of the module, each
                        // of its own visibility (§18.1, R-246, S-491), and E0200
                        // defs, whose uses get no diagnostic.
                        for &sub in &e.items {
                            let member = Place { id: sub, item: ast.item(sub), ..at };
                            let (ItemKind::Fn(onsa_syntax::ast::FnDecl { name, .. }) | ItemKind::OpaqueType { name }) =
                                &member.item.kind
                            else {
                                continue;
                            };
                            let md = self.add_def(member.def(name.name.clone(), name.span, DefKind::Unsupported));
                            self.declare(m, name, md);
                        }
                    }
                    ItemKind::Test { name, body } => self.collect_test(&at, name, *body, &mut tests),
                    ItemKind::Target(inner) => {
                        at.target = true;
                        if let Some(d) = self.collect_named(&at, inner)
                            && !self.a.modules.is_std(m)
                        {
                            self.unsupported(d, item.span, Feature::UserTargets, &[]);
                        }
                    }
                    kind => {
                        self.collect_named(&at, kind);
                    }
                }
            }
        }
    }

    /// A `use` cut before its names were all read is not resolved (§18.1,
    /// R-180, S-462): the names of its list read whole are failed (with no
    /// list, the last name of its path, `double` of `use util.double.`), and
    /// every name not found in the body is an error. One read whole in a unit
    /// with an error of the syntax stage is resolved (S-435).
    fn cut_use(&mut self, m: ModId, u: &UseDecl, vis: Vis) {
        self.fail_taken(m, u, vis);
        self.a.modules.get_mut(m).unread_use = true;
    }

    /// The names a `use` of `m` takes are failed (S-462), and of a `pub use`
    /// in the namespace too (S-596).
    fn fail_taken(&mut self, m: ModId, u: &UseDecl, vis: Vis) {
        for name in taken_names(u) {
            self.fail(m, name);
            if vis == Vis::Pub {
                self.a.modules.get_mut(m).pub_use_names.insert(name.name.clone());
            }
        }
    }

    /// A `use` of `m` read whole, resolved later ([`Sema::resolve_imports`])
    /// unless it is a `pub use`, the E0200 at `pub` (§15.1, S-596) whose names
    /// are failed in the namespace too, and make no dependency (§18.1). A
    /// name taken that is a keyword or a reserved word, the syntax stage's
    /// E0002 or E0200 (R-266, R-275), is failed alone (R-272).
    fn collect_use(&mut self, m: ModId, item: &Item, id: ItemId, u: &UseDecl) {
        if item.vis == Vis::Pub {
            let at = item.vis_span.unwrap_or(item.span);
            let mut form: Vec<&str> = u.path.segments.iter().map(|s| s.name.as_str()).collect();
            let list = u.names.as_ref().map(|l| l.iter().map(|n| n.name.as_str()).collect::<Vec<_>>().join(", "));
            let list = list.map(|l| format!("{{{l}}}"));
            form.extend(list.as_deref());
            let rule = format!(
                "a module that uses the names takes them from the module that defines them (`use {}`)",
                form.join(".")
            );
            self.report_mod(Feature::Reexports.diagnostic(Stage::Names, at, &[]).with_rule(rule));
            self.fail_taken(m, u, item.vis);
            return;
        }
        let names = u.names.clone();
        let import = Import { path: u.path.clone(), names, vis: item.vis, span: item.span, item: id };
        self.a.modules.get_mut(m).imports.push(import);
    }

    /// The def of a `test`, whose name is one in its module (E0306, §11.8).
    /// A name with an interpolation is the syntax stage's E0002, and its item
    /// a failed one (S-244): it has no value, so it is no test and takes no
    /// part in E0306. Anywhere else it is a bug.
    fn collect_test(&mut self, at: &Place<'_>, name: &StrLit, body: ExprId, tests: &mut HashMap<String, DefId>) {
        let Some(value) = onsa_syntax::test_name::value(name) else {
            if at.item.failed.is_none() {
                onsa_diag::internal::bug(Some(name.span), "a test name with an interpolation and no syntax error");
            }
            return;
        };
        let quoted = onsa_syntax::test_name::quote(&value);
        let kind = DefKind::Test { name: value.clone(), body };
        let d = self.add_def(at.def(format!("test {quoted}"), name.span, kind));
        match tests.get(&value) {
            Some(&first) => {
                let msg = format!("test {quoted} is defined twice in this module");
                let diag = Diagnostic::new(Stage::Names, Code::E0306, name.span, msg);
                self.report(d, diag.with_note(self.a.def(first).span, "first defined here"));
            }
            None => {
                tests.insert(value, d);
            }
        }
    }

    /// The def of an item with a name, in the items of its module.
    fn collect_named(&mut self, at: &Place<'_>, kind: &ItemKind) -> Option<DefId> {
        let item = at.item;
        let (name, kind, feature) = match kind {
            ItemKind::Fn(f) => (&f.name, DefKind::Fn(at.fn_def(f.rt, f.body)), None),
            ItemKind::Flow(f) => (
                &f.name,
                DefKind::Flow(FlowDef { inputs: Vec::new(), out: at.error, body: f.body, members: Vec::new() }),
                None,
            ),
            ItemKind::Struct(s) => {
                let def = StructDef { generics: at.generics(&s.generics), ..struct_def(Fields::Named(Vec::new())) };
                (&s.name, DefKind::Struct(def), None)
            }
            ItemKind::OpaqueType { name } => (name, DefKind::Struct(struct_def(Fields::Opaque)), None),
            ItemKind::Enum(e) => (
                &e.name,
                DefKind::Enum(EnumDef {
                    generics: at.generics(&e.generics),
                    variants: Vec::new(),
                    derives: Some(Vec::new()),
                }),
                None,
            ),
            ItemKind::TypeAlias { name, .. } => (name, DefKind::Alias(at.error), None),
            ItemKind::Const(c) => (&c.name, DefKind::Const(at.const_def(c.value)), None),
            ItemKind::Trait(t) => (&t.name, DefKind::Unsupported, Some(Feature::TraitDefinitions)),
            // An effect of std, with no operations in this version (D-08,
            // S-659); a user's is an E0200.
            ItemKind::Effect(e) if self.a.modules.is_std(at.m) => {
                (&e.name, DefKind::Effect { blocking: e.blocking }, None)
            }
            ItemKind::Effect(e) => (&e.name, DefKind::Unsupported, Some(Feature::EffectDefinitions)),
            ItemKind::Handler(h) => (&h.name, DefKind::Unsupported, Some(Feature::HandlerDefinitions)),
            _ => return None,
        };
        let d = self.add_def(at.def(name.name.clone(), name.span, kind));
        if self.a.def(d).as_flow().is_some() {
            self.generated_defs(d);
        }
        self.declare(at.m, name, d);
        if let Some(f) = feature {
            self.unsupported(d, item.span, f, &[]);
        }
        Some(d)
    }

    /// `name` in the items of `m` for the def `d`: E0304 when the module
    /// declares the name already, E0305 when one of the two is a flow, whose
    /// namespace takes the name (§11.2). The name is then an error in the body
    /// and the namespace (§18.1, S-675, S-680).
    fn declare(&mut self, m: ModId, name: &Ident, d: DefId) {
        let info = self.a.modules.get_mut(m);
        let Some(&prev) = info.items.get(&name.name) else {
            info.items.insert(name.name.clone(), d);
            return;
        };
        info.clashed.body.insert(name.name.clone());
        info.clashed.namespace.insert(name.name.clone());
        let first = self.a.def(prev).name_span;
        let is_flow = |x: DefId| self.a.def(x).as_flow().is_some();
        let (code, msg) = if is_flow(prev) || is_flow(d) {
            (
                Code::E0305,
                format!("`{}` is declared twice in this module; a flow and its namespace take the name", name.name),
            )
        } else {
            (Code::E0304, format!("`{}` is already declared in this module", name.name))
        };
        let diag = Diagnostic::new(Stage::Names, code, name.span, msg).with_found(name.name.clone());
        self.report(d, diag.with_note(first, "first declared here"));
    }

    /// The def of an `impl` and the defs of its functions and constants. A
    /// trait implementation is an E0200, and its members have no defs.
    fn collect_impl(&mut self, at: &Place<'_>, decl: &ImplDecl) {
        let item = at.item;
        let empty = ImplDef { generics: Vec::new(), self_ty: at.error, fns: Vec::new(), consts: Vec::new() };
        let d = self.add_def(at.def("<impl>".into(), item.span, DefKind::Impl(empty)));
        if decl.trait_.is_some() {
            self.unsupported(d, item.span, Feature::TraitImpls, &[]);
            return;
        }
        let (mut fns, mut consts) = (Vec::new(), Vec::new());
        for &id in &decl.items {
            let sub = at.ast.item(id);
            let member = Place { id, item: sub, ..*at };
            let (name, kind) = match &sub.kind {
                ItemKind::Fn(f) => (&f.name, DefKind::Fn(member.fn_def(f.rt, f.body))),
                ItemKind::Const(c) => (&c.name, DefKind::Const(member.const_def(c.value))),
                _ => continue,
            };
            let def = Def { owner: Some(d), ..member.def(name.name.clone(), name.span, kind) };
            let sub_def = self.add_def(def);
            if matches!(sub.kind, ItemKind::Fn(_)) { fns.push(sub_def) } else { consts.push(sub_def) }
        }
        if let DefKind::Impl(imp) = &mut self.a.defs[d.0 as usize].kind {
            imp.fns = fns;
            imp.consts = consts;
        }
    }
}

/// Where an item is: its module, its AST item, and the placeholder types.
#[derive(Clone, Copy)]
struct Place<'a> {
    m: ModId,
    ast: &'a Ast,
    id: ItemId,
    item: &'a Item,
    error: crate::ty::TyId,
    unit: crate::ty::TyId,
    /// The item is a `target` declaration (§15.2).
    target: bool,
}

impl Place<'_> {
    fn def(&self, name: String, name_span: Span, kind: DefKind) -> Def {
        Def {
            name,
            module: self.m,
            vis: self.item.vis,
            span: self.item.span,
            name_span,
            kind,
            item: Some(self.id),
            owner: None,
        }
    }

    /// The generic parameters of a type as written, until the signatures
    /// lower them: a type lowered before names it with their number, and
    /// which are `const` (§4.5, R-197).
    fn generics(&self, gs: &[GenericParam]) -> Vec<GenericDef> {
        let one = |g: &GenericParam| {
            let (name, kind) = match g {
                GenericParam::Type { name, .. } => {
                    (name, GenericKind::Type { bounds: Vec::new(), dup: true, unknown: false })
                }
                GenericParam::Const { name, .. } => (name, GenericKind::Const(self.error)),
                GenericParam::Effect { name } => (name, GenericKind::Effect),
            };
            GenericDef { name: name.name.clone(), span: name.span, kind }
        };
        gs.iter().map(one).collect()
    }

    /// A `const` and its value when the initializer is an integer literal.
    fn const_def(&self, value: Option<ExprId>) -> ConstDef {
        let int_value = value.and_then(|v| match &self.ast.expr(v).kind {
            ExprKind::Lit(Lit::Int { value, .. }) => Some(*value),
            _ => None,
        });
        ConstDef { ty: self.error, value, int_value }
    }

    fn fn_def(&self, rt: bool, body: Option<ExprId>) -> FnDef {
        FnDef {
            generics: Vec::new(),
            self_mode: None,
            params: Vec::new(),
            ret: self.unit,
            rt,
            effects: EffectSet::default(),
            body,
            target: self.target,
            flow_fn: None,
            fp_relaxed: self.item.attrs.iter().any(|a| a.is_fp_relaxed()),
        }
    }
}

/// The names a `use` takes: those of its list, or with none the last of its
/// path (`double` of `use util.double`, also when it was cut after it).
fn taken_names(u: &UseDecl) -> impl Iterator<Item = &Ident> {
    let last = if u.names.is_none() { u.path.segments.last() } else { None };
    u.names.iter().flatten().chain(last)
}

fn struct_def(fields: Fields) -> StructDef {
    StructDef { generics: Vec::new(), fields, derives: Some(Vec::new()), flow_ty: None }
}

fn new_module(path: String, pkg: usize, parent: Option<ModId>) -> ModInfo {
    ModInfo {
        path,
        pkg,
        module: None,
        file: None,
        parent,
        children: HashMap::new(),
        items: HashMap::new(),
        uses: HashMap::new(),
        pub_use_names: Default::default(),
        bound: Vec::new(),
        imports: Vec::new(),
        deps: Vec::new(),
        clashed: Default::default(),
        unread_use: false,
        use_at: None,
    }
}

/// Where a candidate adds a `use` in a file ([`UseAt`]): after the last `use`
/// of the top level whose unit has no syntax error (a `use` cut in its list
/// would read the new line in it), or else before the first unit.
fn use_at(parsed: &onsa_syntax::Parsed) -> Option<UseAt> {
    let top = || parsed.units.list.iter().filter(|u| u.parent.is_none());
    let is_use = |u: &&onsa_syntax::units::Unit| {
        !u.syntax_failed && u.item.is_some_and(|id| matches!(parsed.ast.item(id).kind, ItemKind::Use(_)))
    };
    match top().rfind(is_use) {
        Some(u) => Some(UseAt::After(u.span.end)),
        None => top().next().map(|u| UseAt::Before(u.span.start)),
    }
}
