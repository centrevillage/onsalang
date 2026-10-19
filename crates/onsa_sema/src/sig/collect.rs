//! Collection (T2-2): the module tree and the prelude, the item defs and
//! the module scopes (E0304 / E0305), and the imports.

use super::*;

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ setup

    pub(super) fn build_module_tree(&mut self) {
        let flat = self.flat.clone();
        for (pi, pkg) in flat.iter().enumerate() {
            let root = self.a.modules.add(ModInfo {
                path: String::new(),
                pkg: pi,
                module: None,
                file: None,
                parent: None,
                children: HashMap::new(),
                scope: HashMap::new(),
                imports: Vec::new(),
            });
            self.a.modules.roots.push(root);
            self.a.modules.names.push(pkg.name.clone());
            for (mi, module) in pkg.modules.iter().enumerate() {
                let mut cur = root;
                for seg in module.path.split('.') {
                    cur = match self.a.modules.get(cur).children.get(seg) {
                        Some(&c) => c,
                        None => {
                            let path = {
                                let p = &self.a.modules.get(cur).path;
                                if p.is_empty() { seg.to_string() } else { format!("{p}.{seg}") }
                            };
                            let c = self.a.modules.add(ModInfo {
                                path,
                                pkg: pi,
                                module: None,
                                file: None,
                                parent: Some(cur),
                                children: HashMap::new(),
                                scope: HashMap::new(),
                                imports: Vec::new(),
                            });
                            self.a.modules.get_mut(cur).children.insert(seg.to_string(), c);
                            c
                        }
                    };
                }
                let info = self.a.modules.get_mut(cur);
                info.module = Some(mi);
                info.file = Some(module.file);
            }
        }
    }

    pub(super) fn build_prelude(&mut self) {
        let t = &mut self.a.types;
        let mut p = HashMap::new();
        for name in ["I8", "I16", "I32", "I64", "U8", "U16", "U32", "U64", "F32", "F64", "Bool", "Char"] {
            let id = t.scalar(name).unwrap();
            p.insert(name.to_string(), Builtin::Scalar(id));
        }
        for b in [
            BuiltinTy::Str,
            BuiltinTy::Bytes,
            BuiltinTy::Array,
            BuiltinTy::Map,
            BuiltinTy::Set,
            BuiltinTy::Buf,
            BuiltinTy::Span,
            BuiltinTy::Ptr,
            BuiltinTy::Option,
            BuiltinTy::Result,
        ] {
            p.insert(b.name().to_string(), Builtin::Generic(b));
            let key = t.builtin(b, Vec::new());
            self.a.builtin_key.insert(b, key);
        }
        p.insert("Some".into(), Builtin::Some);
        p.insert("None".into(), Builtin::None);
        p.insert("Ok".into(), Builtin::Ok);
        p.insert("Err".into(), Builtin::Err);
        self.a.prelude = p;
    }

    /// Register `name` in the module scope (E0304 / E0305).
    fn declare(&mut self, m: ModId, name: &Ident, entity: Entity, vis: Vis, is_flow: bool) {
        if let Some(prev) = self.a.modules.get(m).scope.get(&name.name) {
            let prev_flow =
                matches!(prev.entity, Entity::Def(d) if matches!(self.a.defs[d.0 as usize].kind, DefKind::Flow(_)));
            let (code, msg) = if is_flow || prev_flow {
                (
                    Code::E0305,
                    format!("`{}` is declared twice in this module; a flow and its namespace take the name", name.name),
                )
            } else {
                (Code::E0304, format!("`{}` is already declared in this module", name.name))
            };
            let d = Diagnostic::new(Stage::Names, code, name.span, msg)
                .with_found(name.name.clone())
                .with_note(prev.span, "first declared here");
            match entity {
                Entity::Def(id) => self.report(id, d),
                _ => self.report_mod(d),
            }
            return;
        }
        self.a
            .modules
            .get_mut(m)
            .scope
            .insert(name.name.clone(), Binding { entity, vis, span: name.span, import: false });
    }

    pub(super) fn collect_items(&mut self) {
        for mi in 0..self.a.modules.mods.len() {
            let m = ModId(mi as u32);
            let Some(module) = self.module(m) else { continue };
            let ast = &module.parsed.ast;
            for &item in &ast.root {
                // A panic names this item (S-67).
                let _scope = onsa_diag::internal::item_scope(ast.item(item).span);
                self.collect_item(m, ast, item, None);
            }
        }
    }

    fn collect_item(&mut self, m: ModId, ast: &'p Ast, item_id: ItemId, owner: Option<DefId>) {
        let item = ast.item(item_id);
        let is_std = self.is_std(m);
        let placeholder_ty = self.a.types.error();
        let unit = self.a.types.unit();
        let mk = |name: &Ident, kind: DefKind| Def {
            name: name.name.clone(),
            module: m,
            vis: item.vis,
            span: item.span,
            name_span: name.span,
            kind,
            item: Some(item_id),
            owner,
        };
        let mut target = false;
        let mut kind = &item.kind;
        if let ItemKind::Target(inner) = kind {
            target = true;
            kind = inner;
        }
        match kind {
            ItemKind::Fn(f) => {
                let def = mk(
                    &f.name,
                    DefKind::Fn(FnDef {
                        generics: Vec::new(),
                        self_mode: None,
                        params: Vec::new(),
                        ret: unit,
                        rt: f.rt,
                        effects: EffectSet::default(),
                        body: f.body,
                        target,
                        flow_fn: None,
                        fp_relaxed: item.attrs.iter().any(Attr::is_fp_relaxed),
                    }),
                );
                let id = self.add_def(def);
                if owner.is_none() {
                    self.declare(m, &f.name, Entity::Def(id), item.vis, false);
                }
                if target && !is_std {
                    self.unsupported(id, item.span, Feature::UserTargets, &[]);
                }
            }
            ItemKind::Flow(f) => {
                let def = mk(
                    &f.name,
                    DefKind::Flow(FlowDef {
                        inputs: Vec::new(),
                        out: placeholder_ty,
                        body: f.body,
                        members: Vec::new(),
                    }),
                );
                let id = self.add_def(def);
                self.declare(m, &f.name, Entity::Def(id), item.vis, true);
            }
            ItemKind::Struct(s) => {
                let def = mk(
                    &s.name,
                    DefKind::Struct(StructDef {
                        generics: Vec::new(),
                        fields: Fields::Opaque,
                        derives: Some(Vec::new()),
                        flow_ty: None,
                    }),
                );
                let id = self.add_def(def);
                self.declare(m, &s.name, Entity::Def(id), item.vis, false);
            }
            ItemKind::Enum(e) => {
                let def = mk(
                    &e.name,
                    DefKind::Enum(EnumDef { generics: Vec::new(), variants: Vec::new(), derives: Some(Vec::new()) }),
                );
                let id = self.add_def(def);
                self.declare(m, &e.name, Entity::Def(id), item.vis, false);
            }
            ItemKind::TypeAlias { name, .. } => {
                let id = self.add_def(mk(name, DefKind::Alias(placeholder_ty)));
                self.declare(m, name, Entity::Def(id), item.vis, false);
            }
            ItemKind::OpaqueType { name } => {
                let def = mk(
                    name,
                    DefKind::Struct(StructDef {
                        generics: Vec::new(),
                        fields: Fields::Opaque,
                        derives: Some(Vec::new()),
                        flow_ty: None,
                    }),
                );
                let id = self.add_def(def);
                if owner.is_none() {
                    self.declare(m, name, Entity::Def(id), item.vis, false);
                }
                if target && !is_std {
                    self.unsupported(id, item.span, Feature::UserTargets, &[]);
                }
            }
            ItemKind::Const(c) => {
                let int_value = c.value.and_then(|v| match &ast.expr(v).kind {
                    ExprKind::Lit(Lit::Int { value, .. }) => Some(*value),
                    _ => None,
                });
                let def = mk(&c.name, DefKind::Const(ConstDef { ty: placeholder_ty, value: c.value, int_value }));
                let id = self.add_def(def);
                if owner.is_none() {
                    self.declare(m, &c.name, Entity::Def(id), item.vis, false);
                }
            }
            ItemKind::Impl(i) => {
                let name = Ident { name: "<impl>".into(), span: item.span };
                let def = mk(
                    &name,
                    DefKind::Impl(ImplDef {
                        generics: Vec::new(),
                        self_ty: placeholder_ty,
                        fns: Vec::new(),
                        consts: Vec::new(),
                    }),
                );
                let id = self.add_def(def);
                if i.trait_.is_some() {
                    self.unsupported(id, item.span, Feature::TraitImpls, &[]);
                    return;
                }
                let mut fns = Vec::new();
                let mut consts = Vec::new();
                for &sub in &i.items {
                    let n = self.a.defs.len();
                    self.collect_item(m, ast, sub, Some(id));
                    if self.a.defs.len() > n {
                        let sid = DefId(n as u32);
                        match self.a.defs[n].kind {
                            DefKind::Fn(_) => fns.push(sid),
                            DefKind::Const(_) => consts.push(sid),
                            _ => {}
                        }
                    }
                }
                if let DefKind::Impl(imp) = &mut self.a.defs[id.0 as usize].kind {
                    imp.fns = fns;
                    imp.consts = consts;
                }
            }
            ItemKind::Trait(t) => {
                let id = self.add_def(mk(&t.name, DefKind::Unsupported));
                self.declare(m, &t.name, Entity::Def(id), item.vis, false);
                self.unsupported(id, item.span, Feature::TraitDefinitions, &[]);
            }
            ItemKind::Effect(e) => {
                let id = self.add_def(mk(&e.name, DefKind::Unsupported));
                self.declare(m, &e.name, Entity::Def(id), item.vis, false);
                self.unsupported(id, item.span, Feature::EffectDefinitions, &[]);
            }
            ItemKind::Handler(h) => {
                let id = self.add_def(mk(&h.name, DefKind::Unsupported));
                self.declare(m, &h.name, Entity::Def(id), item.vis, false);
                self.unsupported(id, item.span, Feature::HandlerDefinitions, &[]);
            }
            ItemKind::Extern(_) => {
                let name = Ident { name: "<extern>".into(), span: item.span };
                let id = self.add_def(mk(&name, DefKind::Unsupported));
                self.unsupported(id, item.span, Feature::Extern, &[]);
            }
            ItemKind::Use(u) => {
                self.a.modules.get_mut(m).imports.push(Import {
                    path: u.path.clone(),
                    names: u.names.clone(),
                    vis: item.vis,
                    span: item.span,
                    item: item_id,
                });
            }
            ItemKind::Test { name, body } => {
                // A name with an interpolation is the syntax stage's E0002, and
                // its item a failed one (S-244): it has no value, so it is no
                // test and takes no part in E0306. Anywhere else it is a bug.
                let Some(text) = onsa_syntax::test_name::value(name) else {
                    if item.failed.is_none() {
                        onsa_diag::internal::bug(
                            Some(name.span),
                            "a test name with an interpolation and no syntax error",
                        );
                    }
                    return;
                };
                let dup = self
                    .a
                    .defs_of_module(m)
                    .find(|(_, d)| matches!(&d.kind, DefKind::Test { name: n, .. } if *n == text))
                    .map(|(_, d)| d.span);
                // The name as the full name text writes it (§11.8, S-244).
                let quoted = onsa_syntax::test_name::quote(&text);
                let ident = Ident { name: format!("test {quoted}"), span: name.span };
                let id = self.add_def(mk(&ident, DefKind::Test { name: text.clone(), body: *body }));
                if let Some(prev) = dup {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0306,
                            name.span,
                            format!("test {quoted} is defined twice in this module"),
                        )
                        .with_note(prev, "first defined here"),
                    );
                }
            }
            ItemKind::Target(_) => unreachable!("nested target"),
        }
    }

    // ------------------------------------------------------------ imports

    pub(super) fn resolve_imports(&mut self, m: ModId) {
        let imports = std::mem::take(&mut self.a.modules.get_mut(m).imports);
        for imp in &imports {
            let target = match self.a.resolve_path(m, &imp.path) {
                Ok(e) => e,
                Err(e) => {
                    self.report_mod(e.into_diagnostic());
                    continue;
                }
            };
            match &imp.names {
                None => {
                    let last = imp.path.segments.last().unwrap();
                    self.bind_import(m, last, target, imp.vis);
                }
                Some(names) => {
                    for n in names {
                        match self.a.modules.member(target, n, m, &self.a.defs, &self.a.builtin_key) {
                            Ok(e) => self.bind_import(m, n, e, imp.vis),
                            Err(e) => self.report_mod(e.into_diagnostic()),
                        }
                    }
                }
            }
        }
        self.a.modules.get_mut(m).imports = imports;
    }

    fn bind_import(&mut self, m: ModId, name: &Ident, entity: Entity, vis: Vis) {
        if let Some(prev) = self.a.modules.get(m).scope.get(&name.name) {
            let d = Diagnostic::new(
                Stage::Names,
                Code::E0304,
                name.span,
                format!("`{}` is already in scope; a name is bound once per module (§15.1)", name.name),
            )
            .with_found(name.name.clone())
            .with_note(prev.span, "first bound here");
            self.report_mod(d);
            return;
        }
        self.a
            .modules
            .get_mut(m)
            .scope
            .insert(name.name.clone(), Binding { entity, vis, span: name.span, import: true });
    }
}
