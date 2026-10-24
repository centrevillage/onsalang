//! The module tree of every package (spec §15.1, S-312, S-313) and the defs
//! and scopes of the items of every module.

use std::collections::HashMap;

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Ident, ImplDecl, Item, ItemId, ItemKind, Lit, StrLit, Vis};

use crate::def::*;
use crate::resolve::{Binding, Entity, Import, ModInfo};
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
    /// and of the items, with the module's scope of their names and its
    /// list of `use` (resolved by [`Sema::resolve_imports`]).
    pub(crate) fn collect_items(&mut self) {
        // The placeholders until the signatures are lowered.
        let error = self.a.types.error();
        let unit = self.a.types.unit();
        for i in 0..self.a.modules.mods.len() {
            let m = ModId(i as u32);
            let Some(module) = self.module(m) else { continue };
            let ast = &module.parsed.ast;
            let mut tests: HashMap<String, DefId> = HashMap::new();
            for &id in &ast.root {
                let item = ast.item(id);
                // A panic names this item (S-67).
                let _scope = onsa_diag::internal::item_scope(item.span);
                let mut at = Place { m, ast, id, item, error, unit, target: false };
                match &item.kind {
                    ItemKind::Use(u) => self.a.modules.get_mut(m).imports.push(Import {
                        path: u.path.clone(),
                        names: u.names.clone(),
                        vis: item.vis,
                        span: item.span,
                        item: id,
                    }),
                    ItemKind::Impl(decl) => self.collect_impl(&at, decl),
                    ItemKind::Extern(_) => {
                        let d = self.add_def(at.def("<extern>".into(), item.span, DefKind::Unsupported));
                        self.unsupported(d, item.span, Feature::Extern, &[]);
                    }
                    ItemKind::Test { name, body } => self.collect_test(&at, name, *body, &mut tests),
                    ItemKind::Target(inner) => {
                        at.target = true;
                        if let Some(d) = self.collect_named(&at, inner)
                            && !self.is_std(m)
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

    /// The def of an item with a name, in the scope of its module.
    fn collect_named(&mut self, at: &Place<'_>, kind: &ItemKind) -> Option<DefId> {
        let item = at.item;
        let (name, kind, feature) = match kind {
            ItemKind::Fn(f) => (&f.name, DefKind::Fn(at.fn_def(f.rt, f.body)), None),
            ItemKind::Flow(f) => (
                &f.name,
                DefKind::Flow(FlowDef { inputs: Vec::new(), out: at.error, body: f.body, members: Vec::new() }),
                None,
            ),
            ItemKind::Struct(s) => (&s.name, DefKind::Struct(struct_def(Fields::Named(Vec::new()))), None),
            ItemKind::OpaqueType { name } => (name, DefKind::Struct(struct_def(Fields::Opaque)), None),
            ItemKind::Enum(e) => (
                &e.name,
                DefKind::Enum(EnumDef { generics: Vec::new(), variants: Vec::new(), derives: Some(Vec::new()) }),
                None,
            ),
            ItemKind::TypeAlias { name, .. } => (name, DefKind::Alias(at.error), None),
            ItemKind::Const(c) => (&c.name, DefKind::Const(at.const_def(c.value)), None),
            ItemKind::Trait(t) => (&t.name, DefKind::Unsupported, Some(Feature::TraitDefinitions)),
            ItemKind::Effect(e) => (&e.name, DefKind::Unsupported, Some(Feature::EffectDefinitions)),
            ItemKind::Handler(h) => (&h.name, DefKind::Unsupported, Some(Feature::HandlerDefinitions)),
            _ => return None,
        };
        let d = self.add_def(at.def(name.name.clone(), name.span, kind));
        self.declare(at.m, name, d, item.vis);
        if let Some(f) = feature {
            self.unsupported(d, item.span, f, &[]);
        }
        Some(d)
    }

    /// `name` in the scope of `m` for the def `d`: E0304 when the module
    /// declares the name already, E0305 when one of the two is a flow, whose
    /// namespace takes the name (§11.2); the first keeps it.
    fn declare(&mut self, m: ModId, name: &Ident, d: DefId, vis: Vis) {
        let scope = &mut self.a.modules.get_mut(m).scope;
        let Some(prev) = scope.get(&name.name) else {
            scope.insert(name.name.clone(), Binding { entity: Entity::Def(d), vis, span: name.span, import: false });
            return;
        };
        let (first, prev) = (prev.span, prev.entity);
        let is_flow = |e: Entity| matches!(e, Entity::Def(x) if self.a.def(x).as_flow().is_some());
        let (code, msg) = if is_flow(prev) || is_flow(Entity::Def(d)) {
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
        scope: HashMap::new(),
        imports: Vec::new(),
    }
}
