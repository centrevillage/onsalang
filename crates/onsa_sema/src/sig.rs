//! Collection of definitions and lowering of signatures (T2-2, T2-3): module
//! tree, item defs and scopes, imports, then every item's signature.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{
    Ast, Attr, AttrArg, EffectRow, ExprKind, GenericParam, Ident, ItemId, ItemKind, Lit, Mode, Param, ParamName,
    StructKind, TypeId, TypeKind, UnOp, Vis,
};

use crate::def::*;
use crate::resolve::{Binding, Builtin, Entity, Import, ModInfo};
use crate::ty::*;
use crate::{Analysis, Module, Package, flatten};

struct Sema<'p> {
    a: Analysis,
    flat: Vec<&'p Package>,
    /// Defs that already have a diagnostic (P-01: first error per item).
    reported: HashSet<DefId>,
    /// Aliases being expanded (cycle guard).
    expanding: HashSet<DefId>,
}

/// Lowering context for one item.
struct Cx<'p> {
    m: ModId,
    ast: &'p Ast,
    text: &'p str,
    /// Generic parameters in scope: the owner's (impl) first, then the item's.
    generics: Vec<GenericDef>,
    self_ty: Option<TyId>,
    def: DefId,
    is_std: bool,
}

pub(crate) fn collect_and_lower(pkg: &Package) -> Analysis {
    let mut s =
        Sema { a: Analysis::default(), flat: flatten(pkg), reported: HashSet::new(), expanding: HashSet::new() };
    s.build_module_tree();
    s.build_prelude();
    s.collect_items();
    let (cycle_diags, order) = s.a.modules.check_cycles();
    s.a.diagnostics.extend(cycle_diags);
    for m in order {
        s.resolve_imports(m);
    }
    s.lower_all();
    s.a
}

impl<'p> Sema<'p> {
    // ------------------------------------------------------------ setup

    fn build_module_tree(&mut self) {
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

    fn build_prelude(&mut self) {
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
        for r in [Rate::Init, Rate::Ctl, Rate::Sig] {
            p.insert(r.name().to_string(), Builtin::Rate(r));
        }
        p.insert("Some".into(), Builtin::Some);
        p.insert("None".into(), Builtin::None);
        p.insert("Ok".into(), Builtin::Ok);
        p.insert("Err".into(), Builtin::Err);
        self.a.prelude = p;
    }

    fn module(&self, m: ModId) -> Option<&'p Module> {
        let info = self.a.modules.get(m);
        self.flat.get(info.pkg).and_then(|p| info.module.and_then(|i| p.modules.get(i)))
    }

    fn is_std(&self, m: ModId) -> bool {
        self.flat[self.a.modules.pkg_of(m)].is_std
    }

    // ------------------------------------------------------------ diagnostics

    fn report(&mut self, def: DefId, d: Diagnostic) {
        if self.reported.insert(def) {
            self.a.diagnostics.push(d);
        }
    }

    fn report_mod(&mut self, d: Diagnostic) {
        self.a.diagnostics.push(d);
    }

    fn unsupported(&mut self, def: DefId, span: Span, what: &str) {
        self.report(
            def,
            Diagnostic::new(Stage::Names, Code::E0200, span, format!("this version does not support {what}")),
        );
    }

    // ------------------------------------------------------------ collection

    fn add_def(&mut self, def: Def) -> DefId {
        self.a.defs.push(def);
        DefId(self.a.defs.len() as u32 - 1)
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

    fn collect_items(&mut self) {
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
                    }),
                );
                let id = self.add_def(def);
                if owner.is_none() {
                    self.declare(m, &f.name, Entity::Def(id), item.vis, false);
                }
                if target && !is_std {
                    self.unsupported(
                        id,
                        item.span,
                        "`target` declarations outside `std` (they need a build target, M4)",
                    );
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
                        derives: Vec::new(),
                        flow_ty: None,
                    }),
                );
                let id = self.add_def(def);
                self.declare(m, &s.name, Entity::Def(id), item.vis, false);
            }
            ItemKind::Enum(e) => {
                let def = mk(
                    &e.name,
                    DefKind::Enum(EnumDef { generics: Vec::new(), variants: Vec::new(), derives: Vec::new() }),
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
                        derives: Vec::new(),
                        flow_ty: None,
                    }),
                );
                let id = self.add_def(def);
                if owner.is_none() {
                    self.declare(m, name, Entity::Def(id), item.vis, false);
                }
                if target && !is_std {
                    self.unsupported(
                        id,
                        item.span,
                        "`target` declarations outside `std` (they need a build target, M4)",
                    );
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
                    self.unsupported(id, item.span, "trait implementations (`impl Trait for Type`)");
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
                self.unsupported(id, item.span, "trait definitions");
            }
            ItemKind::Effect(e) => {
                let id = self.add_def(mk(&e.name, DefKind::Unsupported));
                self.declare(m, &e.name, Entity::Def(id), item.vis, false);
                self.unsupported(id, item.span, "effect definitions");
            }
            ItemKind::Handler(h) => {
                let id = self.add_def(mk(&h.name, DefKind::Unsupported));
                self.declare(m, &h.name, Entity::Def(id), item.vis, false);
                self.unsupported(id, item.span, "handlers");
            }
            ItemKind::Extern(_) => {
                let name = Ident { name: "<extern>".into(), span: item.span };
                let id = self.add_def(mk(&name, DefKind::Unsupported));
                self.unsupported(id, item.span, "`extern` blocks");
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
                let text: String = name
                    .segments
                    .iter()
                    .map(|s| match s {
                        onsa_syntax::ast::StrSeg::Text(t) => t.clone(),
                        onsa_syntax::ast::StrSeg::Interp(_) => String::new(),
                    })
                    .collect();
                let dup = self
                    .a
                    .defs_of_module(m)
                    .find(|(_, d)| matches!(&d.kind, DefKind::Test { name: n, .. } if *n == text))
                    .map(|(_, d)| d.span);
                let ident = Ident { name: format!("test \"{text}\""), span: name.span };
                let id = self.add_def(mk(&ident, DefKind::Test { name: text.clone(), body: *body }));
                if let Some(prev) = dup {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0306,
                            name.span,
                            format!("test \"{text}\" is defined twice in this module"),
                        )
                        .with_found(format!("\"{text}\""))
                        .with_note(prev, "first defined here"),
                    );
                }
            }
            ItemKind::Target(_) => unreachable!("nested target"),
        }
    }

    // ------------------------------------------------------------ imports

    fn resolve_imports(&mut self, m: ModId) {
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

    // ------------------------------------------------------------ lowering

    fn lower_all(&mut self) {
        let n = self.a.defs.len();
        for i in 0..n {
            let id = DefId(i as u32);
            if self.a.defs[i].owner.is_some() {
                continue; // lowered with their owner (impl / flow)
            }
            let _scope = onsa_diag::internal::item_scope(self.a.defs[i].span);
            self.lower_def(id);
        }
    }

    fn cx_for(&self, id: DefId, extra: Vec<GenericDef>, self_ty: Option<TyId>) -> Option<Cx<'p>> {
        let def = &self.a.defs[id.0 as usize];
        let module = self.module(def.module)?;
        Some(Cx {
            m: def.module,
            ast: &module.parsed.ast,
            text: &module.text,
            generics: extra,
            self_ty,
            def: id,
            is_std: self.is_std(def.module),
        })
    }

    fn lower_def(&mut self, id: DefId) {
        let def = &self.a.defs[id.0 as usize];
        let Some(item_id) = def.item else { return };
        let Some(cx) = self.cx_for(id, Vec::new(), None) else { return };
        let item = cx.ast.item(item_id);
        let mut kind = &item.kind;
        if let ItemKind::Target(inner) = kind {
            kind = inner;
        }
        match kind {
            ItemKind::Fn(f) => self.lower_fn(cx, id, f),
            ItemKind::Flow(f) => self.lower_flow(cx, id, f),
            ItemKind::Struct(s) => {
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &s.generics);
                let derives = self.lower_derives(&cx, &item.attrs);
                let fields = match &s.kind {
                    StructKind::Named(fs) => Fields::Named(
                        fs.iter()
                            .map(|f| FieldDef {
                                name: f.name.name.clone(),
                                ty: self.lower_type(&cx, f.ty),
                                vis: f.vis,
                                span: f.span,
                            })
                            .collect(),
                    ),
                    StructKind::Tuple(t) => Fields::Tuple(self.lower_type(&cx, *t)),
                };
                if let DefKind::Struct(sd) = &mut self.a.defs[id.0 as usize].kind {
                    sd.generics = cx.generics;
                    sd.fields = fields;
                    sd.derives = derives;
                }
            }
            ItemKind::Enum(e) => {
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &e.generics);
                let derives = self.lower_derives(&cx, &item.attrs);
                let variants = e
                    .variants
                    .iter()
                    .map(|v| VariantDef {
                        name: v.name.name.clone(),
                        fields: v.fields.iter().map(|&t| self.lower_type(&cx, t)).collect(),
                        span: v.span,
                    })
                    .collect();
                if let DefKind::Enum(ed) = &mut self.a.defs[id.0 as usize].kind {
                    ed.generics = cx.generics;
                    ed.variants = variants;
                    ed.derives = derives;
                }
            }
            ItemKind::TypeAlias { .. } => {
                self.alias_ty(id);
            }
            ItemKind::OpaqueType { .. } => {}
            ItemKind::Const(c) => {
                let ty = self.lower_type(&cx, c.ty);
                if let DefKind::Const(cd) = &mut self.a.defs[id.0 as usize].kind {
                    cd.ty = ty;
                }
            }
            ItemKind::Impl(i) => {
                if i.trait_.is_some() {
                    return;
                }
                let mut cx = cx;
                cx.generics = self.lower_generics(&cx, &i.generics);
                let self_ty = self.lower_type(&cx, i.self_ty);
                let (fns, consts) = match &self.a.defs[id.0 as usize].kind {
                    DefKind::Impl(imp) => (imp.fns.clone(), imp.consts.clone()),
                    _ => unreachable!(),
                };
                if let DefKind::Impl(imp) = &mut self.a.defs[id.0 as usize].kind {
                    imp.generics = cx.generics.clone();
                    imp.self_ty = self_ty;
                }
                // Associated items are keyed by the type's def (or the builtin TyId).
                let key_def = match self.a.types.get(self_ty) {
                    Ty::Named(d, _) => Some(*d),
                    _ => None,
                };
                let key_builtin = match self.a.types.get(self_ty) {
                    Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char => Some(self_ty),
                    Ty::Builtin(b, _) => self.a.builtin_key.get(b).copied(),
                    _ => None,
                };
                if key_def.is_none() && key_builtin.is_none() && !matches!(self.a.types.get(self_ty), Ty::Error) {
                    let span = cx.ast.ty(i.self_ty).span;
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0302,
                            span,
                            "`impl` needs a struct, enum, or builtin type",
                        ),
                    );
                }
                for &sub in fns.iter().chain(&consts) {
                    let sub_item = self.a.defs[sub.0 as usize].item.unwrap();
                    let sub_cx =
                        Cx { generics: cx.generics.clone(), self_ty: Some(self_ty), def: sub, ..cx_clone(&cx) };
                    match &cx.ast.item(sub_item).kind {
                        ItemKind::Fn(f) => self.lower_fn(sub_cx, sub, f),
                        ItemKind::Const(c) => {
                            let ty = self.lower_type(&sub_cx, c.ty);
                            if let DefKind::Const(cd) = &mut self.a.defs[sub.0 as usize].kind {
                                cd.ty = ty;
                            }
                        }
                        _ => {}
                    }
                    let name = self.a.defs[sub.0 as usize].name.clone();
                    let name_span = self.a.defs[sub.0 as usize].name_span;
                    let table = match (key_def, key_builtin) {
                        (Some(d), _) => self.a.modules.assoc.entry(d).or_default(),
                        (None, Some(t)) => self.a.modules.assoc_builtin.entry(t).or_default(),
                        _ => continue,
                    };
                    if let Some(prev) = table.get(&name) {
                        let prev_span = self.a.defs[prev.0 as usize].name_span;
                        self.report(
                            sub,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0304,
                                name_span,
                                format!("`{name}` is defined twice for this type"),
                            )
                            .with_note(prev_span, "first defined here"),
                        );
                    } else {
                        table.insert(name, sub);
                    }
                }
            }
            ItemKind::Test { .. } => {}
            _ => {}
        }
    }

    fn alias_ty(&mut self, id: DefId) -> TyId {
        let current = match &self.a.defs[id.0 as usize].kind {
            DefKind::Alias(t) => *t,
            _ => return self.a.types.error(),
        };
        if !matches!(self.a.types.get(current), Ty::Error) {
            return current;
        }
        if !self.expanding.insert(id) {
            let span = self.a.defs[id.0 as usize].name_span;
            self.report(id, Diagnostic::new(Stage::Names, Code::E0310, span, "type alias refers to itself"));
            return self.a.types.error();
        }
        let ty = match (self.cx_for(id, Vec::new(), None), self.a.defs[id.0 as usize].item) {
            (Some(cx), Some(item)) => match &cx.ast.item(item).kind {
                ItemKind::TypeAlias { ty, .. } => self.lower_type(&cx, *ty),
                _ => self.a.types.error(),
            },
            _ => self.a.types.error(),
        };
        self.expanding.remove(&id);
        if let DefKind::Alias(t) = &mut self.a.defs[id.0 as usize].kind {
            *t = ty;
        }
        ty
    }

    fn lower_generics(&mut self, cx: &Cx<'p>, gs: &[GenericParam]) -> Vec<GenericDef> {
        let mut out = cx.generics.clone();
        for g in gs {
            let def = match g {
                GenericParam::Type { name, bounds } => {
                    let mut bs = Vec::new();
                    let mut dup = true;
                    for b in bounds {
                        let n = b.path.segments.last().unwrap();
                        match Bound::parse(&n.name) {
                            Some(Bound::Dup) if b.relaxed => dup = false,
                            Some(bound) => bs.push(bound),
                            None => self.unsupported(cx.def, n.span, "user-defined traits as bounds"),
                        }
                    }
                    GenericDef { name: name.name.clone(), span: name.span, kind: GenericKind::Type { bounds: bs, dup } }
                }
                GenericParam::Const { name, ty } => {
                    let t = self.lower_type(cx, *ty);
                    if !matches!(self.a.types.get(t), Ty::Int(IntKind::U32) | Ty::Error) {
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0200,
                                cx.ast.ty(*ty).span,
                                "const generics other than `U32` are not supported",
                            )
                            .with_fix(Fix::replace(
                                "write `U32`",
                                cx.ast.ty(*ty).span,
                                "U32",
                            )),
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

    fn lower_derives(&mut self, cx: &Cx<'p>, attrs: &[Attr]) -> Vec<Derive> {
        let mut out = Vec::new();
        for attr in attrs {
            match attr.name.name.as_str() {
                "derive" => {
                    for arg in &attr.args {
                        let AttrArg::Path(p) = arg else {
                            self.report(
                                cx.def,
                                Diagnostic::new(Stage::Names, Code::E0302, attr.span, "`@derive` takes trait names"),
                            );
                            continue;
                        };
                        let n = p.segments.last().unwrap();
                        let d = match n.name.as_str() {
                            "PartialEq" => Derive::PartialEq,
                            "Eq" => Derive::Eq,
                            "PartialOrd" => Derive::PartialOrd,
                            "Ord" => Derive::Ord,
                            "Default" => Derive::Default,
                            "Hash" | "Show" => {
                                self.unsupported(cx.def, n.span, &format!("`@derive({})` (needs `Str`)", n.name));
                                continue;
                            }
                            _ => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Names, Code::E0302,
                                        n.span,
                                        format!("`{}` cannot be derived; the list is PartialEq Eq PartialOrd Ord Hash Show Default (§6.4)", n.name),
                                    )
                                    .with_found(n.name.clone()),
                                );
                                continue;
                            }
                        };
                        out.push(d);
                    }
                }
                "repr" | "relaxed" | "deprecated" | "param" => {}
                other => {
                    self.report(
                        cx.def,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0302,
                            attr.name.span,
                            format!("unknown attribute `@{other}` (§6.5)"),
                        )
                        .with_found(other.to_string()),
                    );
                }
            }
        }
        out
    }

    fn lower_effects(&mut self, cx: &Cx<'p>, row: Option<&EffectRow>) -> EffectSet {
        let mut set = EffectSet::default();
        let Some(row) = row else { return set };
        for p in &row.effects {
            let n = p.segments.last().unwrap();
            if p.segments.len() == 1 && n.name == "Alloc" {
                set.alloc = true;
            } else if p.segments.len() == 1
                && let Some(i) =
                    cx.generics.iter().position(|g| g.name == n.name && matches!(g.kind, GenericKind::Effect))
            {
                set.vars.push(i as u32);
            } else {
                if !cx.is_std {
                    self.unsupported(cx.def, n.span, &format!("effects other than `Alloc` (`{}`)", n.name));
                }
                set.other.push(n.name.clone());
            }
        }
        set
    }

    fn lower_params(&mut self, cx: &Cx<'p>, params: &[Param], in_impl: bool) -> (Option<Mode>, Vec<ParamSig>) {
        let mut self_mode = None;
        let mut out = Vec::new();
        for (i, p) in params.iter().enumerate() {
            match &p.name {
                ParamName::SelfParam(span) => {
                    if i != 0 || !in_impl {
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0002,
                                *span,
                                "`self` must be the first parameter of a method",
                            ),
                        );
                    }
                    self_mode = Some(p.mode);
                }
                name => {
                    let n = match name {
                        ParamName::Ident(id) => id.name.clone(),
                        _ => "_".into(),
                    };
                    let ty = match p.ty {
                        Some(t) => self.lower_type(cx, t),
                        None => {
                            self.report(
                                cx.def,
                                Diagnostic::new(
                                    Stage::Names,
                                    Code::E0002,
                                    p.span,
                                    "parameter needs a type (only closures may omit it)",
                                ),
                            );
                            self.a.types.error()
                        }
                    };
                    out.push(ParamSig { name: n, mode: p.mode, ty, span: p.span });
                }
            }
        }
        (self_mode, out)
    }

    fn lower_fn(&mut self, cx: Cx<'p>, id: DefId, f: &onsa_syntax::ast::FnDecl) {
        let mut cx = cx;
        cx.generics = self.lower_generics(&cx, &f.generics);
        let in_impl = cx.self_ty.is_some();
        let (self_mode, params) = self.lower_params(&cx, &f.params, in_impl);
        let ret = match f.ret {
            Some(t) => self.lower_type(&cx, t),
            None => self.a.types.unit(),
        };
        let effects = self.lower_effects(&cx, f.effects.as_ref());
        // §10 rule 1: an `rt` function cannot have `Alloc` in its effect row (E0902).
        if f.rt && effects.alloc {
            let span = f.effects.as_ref().map(|e| e.span).unwrap_or(f.name.span);
            self.report(
                id,
                Diagnostic::new(
                    Stage::Effects,
                    Code::E0902,
                    span,
                    "`rt fn` cannot have `Alloc` in its effect row (§10)",
                ),
            );
        }
        let target = self.a.defs[id.0 as usize].as_fn().is_some_and(|d| d.target);
        if f.body.is_none() && !target {
            self.report(id, Diagnostic::new(Stage::Names, Code::E0002, f.name.span, "function needs a body"));
        }
        if let DefKind::Fn(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.generics = cx.generics;
            fd.self_mode = self_mode;
            fd.params = params;
            fd.ret = ret;
            fd.effects = effects;
        }
    }

    // ------------------------------------------------------------ types

    fn lower_type(&mut self, cx: &Cx<'p>, t: TypeId) -> TyId {
        let te = cx.ast.ty(t);
        match &te.kind {
            TypeKind::Unit => self.a.types.unit(),
            TypeKind::Tuple(ts) => {
                let v: Vec<TyId> = ts.iter().map(|&x| self.lower_type(cx, x)).collect();
                self.a.types.intern(Ty::Tuple(v))
            }
            TypeKind::Array { elem, len } => {
                let e = self.lower_type(cx, *elem);
                match self.lower_len(cx, *len) {
                    Some(l) => self.a.types.intern(Ty::Array(e, l)),
                    None => self.a.types.error(),
                }
            }
            TypeKind::Fn { rt, params, ret, effects } => {
                let ps: Vec<(Mode, TyId)> = params.iter().map(|(m, x)| (*m, self.lower_type(cx, *x))).collect();
                let r = match ret {
                    Some(x) => self.lower_type(cx, *x),
                    None => self.a.types.unit(),
                };
                let eff = self.lower_effects(cx, effects.as_ref());
                self.a.types.intern(Ty::Fn(FnTy { rt: *rt, params: ps, ret: r, effects: eff }))
            }
            TypeKind::Path { path, args } => {
                let args_ast = args.clone();
                if path.segments.len() == 1 {
                    let seg = &path.segments[0];
                    if seg.name == "Self" {
                        return match cx.self_ty {
                            Some(t) => t,
                            None => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Names,
                                        Code::E0302,
                                        seg.span,
                                        "`Self` is only valid inside `impl`",
                                    ),
                                );
                                self.a.types.error()
                            }
                        };
                    }
                    if let Some(i) = cx.generics.iter().position(|g| g.name == seg.name) {
                        if !args_ast.is_empty() {
                            self.report(
                                cx.def,
                                Diagnostic::new(
                                    Stage::Names,
                                    Code::E0302,
                                    te.span,
                                    "a type parameter takes no arguments",
                                ),
                            );
                        }
                        return match cx.generics[i].kind {
                            GenericKind::Type { .. } | GenericKind::Const(_) => {
                                self.a.types.intern(Ty::Param(i as u32))
                            }
                            GenericKind::Effect => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Names,
                                        Code::E0302,
                                        seg.span,
                                        "an effect-row variable is not a type",
                                    ),
                                );
                                self.a.types.error()
                            }
                        };
                    }
                }
                let entity = match self.a.resolve_path(cx.m, path) {
                    Ok(e) => e,
                    Err(e) => {
                        self.report(cx.def, e.into_diagnostic());
                        return self.a.types.error();
                    }
                };
                // S-24: a const generic parameter takes an integer literal or a
                // constant's name; which arguments are const depends on the entity.
                let expect_const: Vec<Option<bool>> = match entity {
                    Entity::Def(d) | Entity::Member(d) => {
                        let def = &self.a.defs[d.0 as usize];
                        match &def.kind {
                            DefKind::Struct(_) | DefKind::Enum(_) => {
                                def.generics().iter().map(|g| Some(matches!(g.kind, GenericKind::Const(_)))).collect()
                            }
                            _ => Vec::new(),
                        }
                    }
                    _ => Vec::new(),
                };
                let lowered_args: Vec<TyId> = args_ast
                    .iter()
                    .enumerate()
                    .map(|(i, &x)| self.lower_type_arg(cx, x, expect_const.get(i).copied().flatten()))
                    .collect();
                self.type_of_entity(cx, entity, lowered_args, te.span, path)
            }
            TypeKind::ConstArg(_) => {
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a constant is not a type; const arguments go to `const` parameters",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
        }
    }

    /// One type argument (S-24). `expect_const`: `Some(true)` for a `const`
    /// parameter, `Some(false)` for a type parameter, `None` when the entity
    /// has no declared kinds (builtins, aliases: only types are accepted).
    fn lower_type_arg(&mut self, cx: &Cx<'p>, t: TypeId, expect_const: Option<bool>) -> TyId {
        let te = cx.ast.ty(t);
        match (&te.kind, expect_const) {
            (TypeKind::ConstArg(e), Some(false) | None) => {
                let _ = e;
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a type parameter expects a type, not a constant",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            (TypeKind::ConstArg(e), Some(true)) => {
                let expr = cx.ast.expr(*e);
                let value: Option<i128> = match &expr.kind {
                    ExprKind::Lit(Lit::Int { value, .. }) => Some(*value as i128),
                    ExprKind::Unary { expr: inner, .. } => match &cx.ast.expr(*inner).kind {
                        ExprKind::Lit(Lit::Int { value, .. }) => Some(-(*value as i128)),
                        _ => None,
                    },
                    _ => None,
                };
                match value {
                    Some(v) if (0..=u32::MAX as i128).contains(&v) => self.a.types.intern(Ty::ConstVal(v as u32)),
                    _ => {
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Types,
                                Code::E0408,
                                te.span,
                                "a const argument must fit in `U32` (§4.1)",
                            )
                            .with_found(src(cx, te.span)),
                        );
                        self.a.types.error()
                    }
                }
            }
            (TypeKind::Path { path, args }, Some(true)) if args.is_empty() => {
                // `N` of the enclosing item, or a `const` item with a literal value.
                if path.segments.len() == 1
                    && let Some(i) = cx.generics.iter().position(|g| g.name == path.segments[0].name)
                {
                    if matches!(cx.generics[i].kind, GenericKind::Const(_)) {
                        return self.a.types.intern(Ty::Param(i as u32));
                    }
                } else {
                    match self.a.resolve_path(cx.m, path) {
                        Ok(Entity::Def(d)) | Ok(Entity::Member(d)) => {
                            if let DefKind::Const(c) = &self.a.defs[d.0 as usize].kind {
                                if let Some(v) = c.int_value
                                    && v <= u32::MAX as u64
                                {
                                    return self.a.types.intern(Ty::ConstVal(v as u32));
                                }
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Types,
                                        Code::E0408,
                                        te.span,
                                        "a const argument must be an integer literal or a `const` with a literal value",
                                    )
                                    .with_found(src(cx, te.span)),
                                );
                                return self.a.types.error();
                            }
                        }
                        Err(e) => {
                            self.report(cx.def, e.into_diagnostic());
                            return self.a.types.error();
                        }
                        _ => {}
                    }
                }
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a `const` parameter expects an integer literal or a constant, not a type",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            (_, Some(true)) => {
                self.report(
                    cx.def,
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        te.span,
                        "a `const` parameter expects an integer literal or a constant, not a type",
                    )
                    .with_found(src(cx, te.span)),
                );
                self.a.types.error()
            }
            _ => self.lower_type(cx, t),
        }
    }

    fn type_of_entity(
        &mut self,
        cx: &Cx<'p>,
        entity: Entity,
        args: Vec<TyId>,
        span: Span,
        path: &onsa_syntax::ast::Path,
    ) -> TyId {
        let name = path.segments.last().unwrap().name.clone();
        let arity_err = |s: &mut Self, want: usize| {
            s.report(
                cx.def,
                Diagnostic::new(
                    Stage::Names,
                    Code::E0302,
                    span,
                    format!("`{name}` takes {want} type argument(s), {} given", args.len()),
                ),
            );
            s.a.types.error()
        };
        match entity {
            Entity::Builtin(Builtin::Scalar(t)) => {
                if !args.is_empty() {
                    return arity_err(self, 0);
                }
                t
            }
            Entity::Builtin(Builtin::Generic(b)) => {
                if args.len() != b.arity() {
                    return arity_err(self, b.arity());
                }
                self.a.types.builtin(b, args)
            }
            Entity::Builtin(Builtin::Rate(r)) => {
                if args.len() != 1 {
                    return arity_err(self, 1);
                }
                self.a.types.intern(Ty::Rate(r, args[0]))
            }
            Entity::Def(d) | Entity::Member(d) => {
                let def = &self.a.defs[d.0 as usize];
                match &def.kind {
                    DefKind::Struct(_) | DefKind::Enum(_) => {
                        let want = def.generics().len();
                        if args.len() != want {
                            return arity_err(self, want);
                        }
                        self.a.types.intern(Ty::Named(d, args))
                    }
                    DefKind::Alias(_) => {
                        if !args.is_empty() {
                            return arity_err(self, 0);
                        }
                        self.alias_ty(d)
                    }
                    DefKind::Flow(_) => {
                        self.report(
                            cx.def,
                            Diagnostic::new(
                                Stage::Names,
                                Code::E0302,
                                span,
                                format!("`{name}` is a flow, not a type; its state type is `{name}.State` (§11.6)"),
                            )
                            .with_fix(Fix::replace(
                                format!("write `{name}.State`"),
                                span,
                                format!("{name}.State"),
                            )),
                        );
                        self.a.types.error()
                    }
                    DefKind::Unsupported => self.a.types.error(),
                    _ => {
                        self.report(
                            cx.def,
                            Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is not a type"))
                                .with_found(name.clone()),
                        );
                        self.a.types.error()
                    }
                }
            }
            Entity::Module(_) => {
                self.report(
                    cx.def,
                    Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is a module, not a type")),
                );
                self.a.types.error()
            }
            Entity::Builtin(_) | Entity::Variant(..) => {
                self.report(
                    cx.def,
                    Diagnostic::new(Stage::Names, Code::E0302, span, format!("`{name}` is a value, not a type")),
                );
                self.a.types.error()
            }
        }
    }

    /// Array length (§4.1): an integer literal, a `const` with a literal
    /// initializer, or a const generic parameter.
    fn lower_len(&mut self, cx: &Cx<'p>, e: onsa_syntax::ast::ExprId) -> Option<Len> {
        let expr = cx.ast.expr(e);
        match &expr.kind {
            ExprKind::Lit(Lit::Int { value, .. }) => {
                if *value > u32::MAX as u64 {
                    self.report(
                        cx.def,
                        Diagnostic::new(Stage::Types, Code::E0408, expr.span, "array length does not fit in `U32`"),
                    );
                    return None;
                }
                Some(Len::Const(*value as u32))
            }
            ExprKind::Path(p) => {
                if p.segments.len() == 1
                    && let Some(i) = cx.generics.iter().position(|g| g.name == p.segments[0].name)
                {
                    if matches!(cx.generics[i].kind, GenericKind::Const(_)) {
                        return Some(Len::Param(i as u32));
                    }
                    self.report(
                        cx.def,
                        Diagnostic::new(
                            Stage::Names,
                            Code::E0302,
                            expr.span,
                            "array length must be a `const` parameter or constant",
                        ),
                    );
                    return None;
                }
                match self.a.resolve_path(cx.m, p) {
                    Ok(Entity::Def(d)) | Ok(Entity::Member(d)) => match &self.a.defs[d.0 as usize].kind {
                        DefKind::Const(c) => match c.int_value {
                            Some(v) if v <= u32::MAX as u64 => Some(Len::Const(v as u32)),
                            Some(_) => {
                                self.report(
                                    cx.def,
                                    Diagnostic::new(
                                        Stage::Types,
                                        Code::E0408,
                                        expr.span,
                                        "array length does not fit in `U32`",
                                    ),
                                );
                                None
                            }
                            None => {
                                self.unsupported(
                                    cx.def,
                                    expr.span,
                                    "constants computed by expressions as array lengths (evaluated in M3)",
                                );
                                None
                            }
                        },
                        _ => {
                            self.report(
                                cx.def,
                                Diagnostic::new(
                                    Stage::Names,
                                    Code::E0302,
                                    expr.span,
                                    "array length must be a constant",
                                )
                                .with_found(src(cx, expr.span)),
                            );
                            None
                        }
                    },
                    Ok(_) => {
                        self.report(
                            cx.def,
                            Diagnostic::new(Stage::Names, Code::E0302, expr.span, "array length must be a constant"),
                        );
                        None
                    }
                    Err(err) => {
                        self.report(cx.def, err.into_diagnostic());
                        None
                    }
                }
            }
            _ => {
                self.unsupported(cx.def, expr.span, "expressions as array lengths (only literals and constants)");
                None
            }
        }
    }

    // ------------------------------------------------------------ flows

    fn lower_flow(&mut self, cx: Cx<'p>, id: DefId, f: &onsa_syntax::ast::FlowDecl) {
        let mut inputs = Vec::new();
        for p in &f.params {
            let name = match &p.name {
                ParamName::Ident(i) => i.name.clone(),
                ParamName::Wild(_) => "_".into(),
                ParamName::SelfParam(s) => {
                    self.report(id, Diagnostic::new(Stage::Names, Code::E0002, *s, "a flow has no `self`"));
                    continue;
                }
            };
            if p.mode != Mode::Borrow {
                self.report(
                    id,
                    Diagnostic::new(
                        Stage::Flow,
                        Code::E0806,
                        p.span,
                        "flow inputs have no `inout` / `move`; they are read-only signals",
                    ),
                );
            }
            let Some(t) = p.ty else { continue };
            let lowered = self.lower_type(&cx, t);
            let (rate, ty) = match self.a.types.get(lowered).clone() {
                Ty::Rate(r, inner) => (r, inner),
                Ty::Error => continue,
                _ => {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Flow,
                            Code::E0810,
                            cx.ast.ty(t).span,
                            "a flow input needs a rate: `Init[T]`, `Ctl[T]` or `Sig[T]` (§11.3)",
                        )
                        .with_found(src(&cx, cx.ast.ty(t).span))
                        .with_fix(Fix::replace(
                            "write `Sig[...]`",
                            cx.ast.ty(t).span,
                            format!("Sig[{}]", src(&cx, cx.ast.ty(t).span)),
                        )),
                    );
                    continue;
                }
            };
            self.check_rate_value_type(&cx, id, ty, cx.ast.ty(t).span, rate == Rate::Sig);
            let param = self.lower_param_attr(&cx, id, &p.attrs, rate);
            inputs.push(FlowInput { name, rate, ty, param, span: p.span });
        }
        let out_lowered = self.lower_type(&cx, f.ret);
        let out = match self.a.types.get(out_lowered).clone() {
            Ty::Rate(Rate::Sig, inner) => {
                self.check_rate_value_type(&cx, id, inner, cx.ast.ty(f.ret).span, true);
                inner
            }
            Ty::Rate(Rate::Ctl, _) => {
                self.unsupported(id, cx.ast.ty(f.ret).span, "`Ctl` outputs of flows (§19)");
                self.a.types.error()
            }
            Ty::Error => out_lowered,
            _ => {
                self.report(
                    id,
                    Diagnostic::new(
                        Stage::Flow,
                        Code::E0810,
                        cx.ast.ty(f.ret).span,
                        "a flow output is `Sig[T]` (§11.6)",
                    )
                    .with_found(src(&cx, cx.ast.ty(f.ret).span)),
                );
                self.a.types.error()
            }
        };
        let members = self.flow_members(&cx, id, &inputs, out);
        if let DefKind::Flow(fd) = &mut self.a.defs[id.0 as usize].kind {
            fd.inputs = inputs;
            fd.out = out;
            fd.members = members;
        }
    }

    /// §11.3: the value type of a rate must be Copy; §11.6: at the boundary
    /// (`Sig` inputs and the output) only scalars, `[scalar; N]`, and structs
    /// of those.
    fn check_rate_value_type(&mut self, _cx: &Cx<'p>, id: DefId, ty: TyId, span: Span, boundary: bool) {
        if let Some(k) = self.a.kind_of(ty)
            && k != crate::Kind::Copy
        {
            self.report(
                id,
                Diagnostic::new(
                    Stage::Flow,
                    Code::E0810,
                    span,
                    format!("the value type of a signal must be Copy; `{}` is {}", self.a.display_type(ty), k.name()),
                ),
            );
            return;
        }
        if boundary && self.boundary_outputs(ty).is_none() {
            self.report(
                id,
                Diagnostic::new(
                    Stage::Flow, Code::E0810,
                    span,
                    "`Sig` inputs and outputs are scalars, `[scalar; N]`, or structs of those; nested arrays cannot cross the boundary (§11.6)",
                ),
            );
        }
    }

    /// The `process` outputs for an output value type (§11.6): `(name, elem, array len)`.
    fn boundary_outputs(&self, ty: TyId) -> Option<Vec<(String, TyId, Option<Len>)>> {
        let is_scalar = |t: TyId| matches!(self.a.types.get(t), Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char);
        let one = |name: &str, t: TyId| -> Option<(String, TyId, Option<Len>)> {
            match self.a.types.get(t) {
                Ty::Array(e, len) if is_scalar(*e) => Some((name.to_string(), *e, Some(*len))),
                _ if is_scalar(t) => Some((name.to_string(), t, None)),
                _ => None,
            }
        };
        match self.a.types.get(ty) {
            Ty::Named(d, args) if args.is_empty() => match &self.a.defs[d.0 as usize].kind {
                DefKind::Struct(StructDef { fields: Fields::Named(fs), .. }) => {
                    fs.iter().map(|f| one(&f.name, f.ty)).collect()
                }
                _ => None,
            },
            Ty::Error => Some(Vec::new()),
            _ => one("out", ty).map(|o| vec![o]),
        }
    }

    fn lower_param_attr(&mut self, cx: &Cx<'p>, id: DefId, attrs: &[Attr], rate: Rate) -> Option<ParamMeta> {
        let attr = attrs.iter().find(|a| a.name.name == "param")?;
        if rate != Rate::Ctl {
            self.report(
                id,
                Diagnostic::new(Stage::Flow, Code::E0809, attr.span, "`@param` goes on `Ctl` inputs only (§11.7)"),
            );
            return None;
        }
        let mut meta = ParamMeta::empty(attr.span);
        for arg in &attr.args {
            let AttrArg::Named { key, value } = arg else {
                self.report(
                    id,
                    Diagnostic::new(Stage::Flow, Code::E0809, attr.span, "`@param` takes `key: value` pairs"),
                );
                continue;
            };
            let num = |s: &Self, e: onsa_syntax::ast::ExprId| -> Option<f64> {
                match &cx.ast.expr(e).kind {
                    ExprKind::Lit(Lit::Float { text }) => text.replace('_', "").parse().ok(),
                    ExprKind::Lit(Lit::Int { value, .. }) => Some(*value as f64),
                    ExprKind::Unary { op: UnOp::Neg, expr } => match &cx.ast.expr(*expr).kind {
                        ExprKind::Lit(Lit::Float { text }) => text.replace('_', "").parse::<f64>().ok().map(|v| -v),
                        ExprKind::Lit(Lit::Int { value, .. }) => Some(-(*value as f64)),
                        _ => None,
                    },
                    _ => {
                        let _ = s;
                        None
                    }
                }
            };
            let string = |e: onsa_syntax::ast::ExprId| -> Option<String> {
                match &cx.ast.expr(e).kind {
                    ExprKind::Lit(Lit::Str(s)) => Some(
                        s.segments
                            .iter()
                            .map(|seg| match seg {
                                onsa_syntax::ast::StrSeg::Text(t) => t.clone(),
                                _ => String::new(),
                            })
                            .collect(),
                    ),
                    _ => None,
                }
            };
            let vspan = cx.ast.expr(*value).span;
            let bad = |s: &mut Self, what: &str| {
                s.report(
                    id,
                    Diagnostic::new(Stage::Flow, Code::E0809, vspan, format!("`@param` `{}` must be {what}", key.name)),
                );
            };
            match key.name.as_str() {
                "min" | "max" | "default" | "step" => match num(self, *value) {
                    Some(v) => match key.name.as_str() {
                        "min" => meta.min = Some(v),
                        "max" => meta.max = Some(v),
                        "default" => meta.default = Some(v),
                        _ => meta.step = Some(v),
                    },
                    None => bad(self, "a numeric literal"),
                },
                "unit" | "label" | "id" => match string(*value) {
                    Some(v) => match key.name.as_str() {
                        "unit" => meta.unit = Some(v),
                        "label" => meta.label = Some(v),
                        _ => meta.id = Some(v),
                    },
                    None => bad(self, "a string literal"),
                },
                "scale" => match string(*value) {
                    Some(v) if v == "linear" || v == "log" => meta.scale = Some(v),
                    _ => bad(self, "\"linear\" or \"log\""),
                },
                other => {
                    self.report(
                        id,
                        Diagnostic::new(
                            Stage::Flow, Code::E0809,
                            key.span,
                            format!("unknown `@param` key `{other}`; keys are min max default step unit scale label id (§11.7)"),
                        )
                        .with_found(other.to_string()),
                    );
                }
            }
        }
        Some(meta)
    }

    /// Generated namespace items of a flow (§11.6).
    fn flow_members(&mut self, cx: &Cx<'p>, flow: DefId, inputs: &[FlowInput], out: TyId) -> Vec<(String, DefId)> {
        let (module, vis, span, name_span) = {
            let d = &self.a.defs[flow.0 as usize];
            (d.module, d.vis, d.span, d.name_span)
        };
        let mk = |s: &mut Self, name: &str, kind: DefKind| -> DefId {
            s.add_def(Def { name: name.to_string(), module, vis, span, name_span, kind, item: None, owner: Some(flow) })
        };
        let mk_struct = |s: &mut Self, name: &str, fields: Vec<FieldDef>, flow_ty: FlowTy| -> DefId {
            let fields = if flow_ty == FlowTy::State { Fields::Opaque } else { Fields::Named(fields) };
            mk(
                s,
                name,
                DefKind::Struct(StructDef {
                    generics: Vec::new(),
                    fields,
                    derives: Vec::new(),
                    flow_ty: Some(flow_ty),
                }),
            )
        };
        let field = |name: &str, ty: TyId| FieldDef { name: name.to_string(), ty, vis: Vis::Pub, span: name_span };

        let state = mk_struct(self, "State", Vec::new(), FlowTy::State);
        let config_fields = inputs.iter().filter(|i| i.rate == Rate::Init).map(|i| field(&i.name, i.ty)).collect();
        let config = mk_struct(self, "Config", config_fields, FlowTy::Config);
        let params_fields = inputs.iter().filter(|i| i.rate == Rate::Ctl).map(|i| field(&i.name, i.ty)).collect();
        let params = mk_struct(self, "Params", params_fields, FlowTy::Params);

        let outputs = self.boundary_outputs(out).unwrap_or_default();
        let out_fields = outputs
            .iter()
            .map(|(n, e, len)| {
                let buf = self.a.types.builtin(BuiltinTy::Buf, vec![*e]);
                let t = match len {
                    Some(l) => self.a.types.intern(Ty::Array(buf, *l)),
                    None => buf,
                };
                field(n, t)
            })
            .collect();
        let out_struct = mk_struct(self, "Out", out_fields, FlowTy::Out);

        let u32 = self.a.types.int(IntKind::U32);
        let f32 = self.a.types.float(FloatKind::F32);
        let unit = self.a.types.unit();
        let size = mk(self, "SIZE", DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));
        let bulk = mk(self, "BULK_SIZE", DefKind::Const(ConstDef { ty: u32, value: None, int_value: None }));

        let state_ty = self.a.types.intern(Ty::Named(state, Vec::new()));
        let config_ty = self.a.types.intern(Ty::Named(config, Vec::new()));
        let params_ty = self.a.types.intern(Ty::Named(params, Vec::new()));
        let out_ty = self.a.types.intern(Ty::Named(out_struct, Vec::new()));
        let sp = |_s: &mut Self, name: &str, mode: Mode, ty: TyId| ParamSig {
            name: name.to_string(),
            mode,
            ty,
            span: name_span,
        };
        let span_of = |s: &mut Self, elem: TyId, len: Option<Len>| -> TyId {
            let span = s.a.types.builtin(BuiltinTy::Span, vec![elem]);
            match len {
                Some(l) => s.a.types.intern(Ty::Array(span, l)),
                None => span,
            }
        };
        let mk_fn =
            |s: &mut Self, name: &str, params: Vec<ParamSig>, ret: TyId, rt: bool, alloc: bool, which: FlowFn| {
                mk(
                    s,
                    name,
                    DefKind::Fn(FnDef {
                        generics: Vec::new(),
                        self_mode: None,
                        params,
                        ret,
                        rt,
                        effects: EffectSet { alloc, ..Default::default() },
                        body: None,
                        target: false,
                        flow_fn: Some(which),
                    }),
                )
            };

        // Sig inputs become `name: Span[T]` (or `[Span[T]; N]` for planar channels, §5.3).
        let sig_inputs: Vec<(String, TyId, Option<Len>)> = inputs
            .iter()
            .filter(|i| i.rate == Rate::Sig)
            .map(|i| match self.a.types.get(i.ty).clone() {
                Ty::Array(e, l) => (i.name.clone(), e, Some(l)),
                _ => (i.name.clone(), i.ty, None),
            })
            .collect();

        let init = {
            let ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "sample_rate", Mode::Borrow, f32)];
            mk_fn(self, "init", ps, state_ty, false, false, FlowFn::Init)
        };
        let reset = {
            let ps = vec![sp(self, "s", Mode::Inout, state_ty)];
            mk_fn(self, "reset", ps, unit, true, false, FlowFn::Reset)
        };
        let process = {
            let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &sig_inputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Borrow, t));
            }
            for (n, e, l) in &outputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Inout, t));
            }
            mk_fn(self, "process", ps, unit, true, false, FlowFn::Process)
        };
        let mut members = vec![
            ("State".to_string(), state),
            ("Config".to_string(), config),
            ("Params".to_string(), params),
            ("Out".to_string(), out_struct),
            ("SIZE".to_string(), size),
            ("BULK_SIZE".to_string(), bulk),
            ("init".to_string(), init),
            ("reset".to_string(), reset),
            ("process".to_string(), process),
        ];
        // `process_inplace` only when inputs and outputs pair up by type (§11.6).
        let pairs = sig_inputs.len() == outputs.len()
            && !outputs.is_empty()
            && sig_inputs.iter().zip(&outputs).all(|(i, o)| i.1 == o.1 && i.2 == o.2);
        if pairs {
            let mut ps = vec![sp(self, "s", Mode::Inout, state_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &outputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Inout, t));
            }
            let f = mk_fn(self, "process_inplace", ps, unit, true, false, FlowFn::ProcessInplace);
            members.push(("process_inplace".into(), f));
        }
        let render = {
            let mut ps = vec![sp(self, "cfg", Mode::Borrow, config_ty), sp(self, "params", Mode::Borrow, params_ty)];
            for (n, e, l) in &sig_inputs {
                let t = span_of(self, *e, *l);
                ps.push(sp(self, n, Mode::Borrow, t));
            }
            if sig_inputs.is_empty() {
                ps.push(sp(self, "frames", Mode::Borrow, u32));
            }
            ps.push(sp(self, "sample_rate", Mode::Borrow, f32));
            mk_fn(self, "render", ps, out_ty, false, true, FlowFn::Render)
        };
        members.push(("render".into(), render));
        let all_defaults = inputs
            .iter()
            .filter(|i| i.rate == Rate::Ctl)
            .all(|i| i.param.as_ref().is_some_and(|p| p.default.is_some()));
        if all_defaults {
            let f = mk_fn(self, "params_default", Vec::new(), params_ty, false, false, FlowFn::ParamsDefault);
            members.push(("params_default".into(), f));
        }
        let _ = cx;
        members
    }
}

/// Lower a type written inside a body (T2-5): same rules as signatures, with
/// the item's generics and `Self` in scope. Diagnostics are returned, not
/// pushed, so the body checker keeps its first-error rule.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_type_in_body(
    a: &mut Analysis,
    m: ModId,
    ast: &Ast,
    text: &str,
    generics: &[GenericDef],
    self_ty: Option<TyId>,
    def: DefId,
    t: TypeId,
) -> (TyId, Vec<Diagnostic>) {
    let before = a.diagnostics.len();
    let mut s = Sema { a: std::mem::take(a), flat: Vec::new(), reported: HashSet::new(), expanding: HashSet::new() };
    let is_std = s.a.modules.pkg_of(m) < s.a.modules.names.len() && s.a.modules.names[s.a.modules.pkg_of(m)] == "std";
    let cx = Cx { m, ast, text, generics: generics.to_vec(), self_ty, def, is_std };
    let ty = s.lower_type(&cx, t);
    *a = s.a;
    let diags = a.diagnostics.drain(before..).collect();
    (ty, diags)
}

fn cx_clone<'p>(cx: &Cx<'p>) -> Cx<'p> {
    Cx {
        m: cx.m,
        ast: cx.ast,
        text: cx.text,
        generics: cx.generics.clone(),
        self_ty: cx.self_ty,
        def: cx.def,
        is_std: cx.is_std,
    }
}

fn src(cx: &Cx<'_>, span: Span) -> String {
    cx.text[span.start as usize..span.end as usize].to_string()
}
