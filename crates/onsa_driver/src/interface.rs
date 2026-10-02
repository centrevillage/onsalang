//! `onsa interface` (T3-11; spec §18.2): the public signatures of a package,
//! each type's kind (§4.6) and size (§12.1), `@param` metadata (§11.7) and
//! the generated API of every flow in the form of §11.6. The data lives in
//! [`Interface`]; `render_text` / `render_json` print it, so the LSP and the
//! web API can reuse it.
//!
//! JSON shape (stable; `--json`):
//!
//! ```json
//! { "package": "voice",
//!   "modules": [ { "path": "dsp.voice", "items": [
//!     { "kind": "fn", "name": "wrap01", "vis": "pub", "rt": true,
//!       "params": [ { "mode": "borrow", "name": "x", "ty": "F32" } ],
//!       "ret": "F32", "effects": [], "signature": "pub rt fn wrap01(x: F32) -> F32" },
//!     { "kind": "struct", "name": "Poly", "vis": "pub", "value_kind": "Affine",
//!       "size": 1234, "align": 8, "generics": [],
//!       "fields": [ { "name": "voices", "ty": "[voice.State; 8]", "offset": 0 } ] },
//!     { "kind": "enum", "name": "Shape", ..., "variants": [ { "name": "Circle", "fields": ["F32"] } ] },
//!     { "kind": "const", "name": "MAX_VOICES", "ty": "U32", "value": "8" },
//!     { "kind": "alias", "name": "Samples", "ty": "Buf[F32]" },
//!     { "kind": "impl", "ty": "Poly", "fns": [ ...fn items... ], "consts": [ ...const items... ] },
//!     { "kind": "flow", "name": "voice", "vis": "pub",
//!       "inputs": [ { "name": "f0", "rate": "Ctl", "ty": "F32",
//!                     "param": { "min": 20.0, "max": 2000.0, "default": 110.0, "unit": "Hz", "scale": "log" } } ],
//!       "out": "F32", "members": [ ...struct / const / fn items named `voice.State` etc... ] }
//!   ] } ] }
//! ```
//!
//! Sizes are absent (`null`) for generic, heap, second-class and flow-state
//! types (the state layout is computed by flow lowering, T3-6).

use std::collections::HashMap;
use std::fmt::Write as _;

use onsa_sema::def::{DefKind, Fields, FlowTy, GenericKind, ParamMeta};
use onsa_sema::ty::Rate;
use onsa_sema::{Analysis, DefId, ModId};
use onsa_syntax::ast::{Mode, Vis};
use serde::Serialize;

use crate::Analyzed;

#[derive(Debug, Clone, Serialize)]
pub struct Interface {
    pub package: String,
    pub modules: Vec<ModuleIface>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModuleIface {
    pub path: String,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Item {
    Fn(FnIface),
    Struct(TypeIface),
    Enum(TypeIface),
    Alias {
        name: String,
        vis: String,
        ty: String,
    },
    Const {
        name: String,
        vis: String,
        ty: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        value: Option<String>,
    },
    Impl {
        ty: String,
        fns: Vec<FnIface>,
        consts: Vec<Item>,
    },
    Flow(FlowIface),
}

#[derive(Debug, Clone, Serialize)]
pub struct FnIface {
    pub name: String,
    pub vis: String,
    pub rt: bool,
    pub generics: Vec<String>,
    pub params: Vec<ParamIface>,
    pub ret: String,
    pub effects: Vec<String>,
    /// The whole signature as source (`pub rt fn norm(self) -> F32`).
    pub signature: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamIface {
    pub mode: String,
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct TypeIface {
    pub name: String,
    pub vis: String,
    pub generics: Vec<String>,
    /// Copy / Shared / Affine (§4.6); absent when generic.
    pub value_kind: Option<String>,
    pub size: Option<u32>,
    pub align: Option<u32>,
    /// Bytes of the bulk region of a flow `State` (§12.4); only for `State`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bulk_size: Option<u32>,
    pub derives: Vec<String>,
    pub fields: Vec<FieldIface>,
    pub variants: Vec<VariantIface>,
    /// `State` / `Config` / `Params` / `Out` of a flow.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub flow_ty: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FieldIface {
    pub name: String,
    pub ty: String,
    pub offset: Option<u32>,
}

#[derive(Debug, Clone, Serialize)]
pub struct VariantIface {
    pub name: String,
    pub fields: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FlowIface {
    pub name: String,
    pub vis: String,
    pub inputs: Vec<FlowInputIface>,
    pub out: String,
    pub members: Vec<Item>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FlowInputIface {
    pub name: String,
    pub rate: String,
    pub ty: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub param: Option<ParamIfaceMeta>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamIfaceMeta {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub min: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub default: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scale: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
}

fn vis_str(v: Vis) -> &'static str {
    match v {
        Vis::Private => "",
        Vis::Pkg => "pub(pkg)",
        Vis::Pub => "pub",
    }
}

fn mode_str(m: Mode) -> &'static str {
    match m {
        Mode::Borrow => "borrow",
        Mode::Inout => "inout",
        Mode::Move => "move",
    }
}

fn mode_prefix(m: Mode) -> &'static str {
    match m {
        Mode::Borrow => "",
        Mode::Inout => "inout ",
        Mode::Move => "move ",
    }
}

fn param_meta(p: &ParamMeta) -> ParamIfaceMeta {
    ParamIfaceMeta {
        min: p.min,
        max: p.max,
        default: p.default,
        step: p.step,
        unit: p.unit.clone(),
        scale: p.scale.clone(),
        label: p.label.clone(),
        id: p.id.clone(),
    }
}

struct Builder<'a> {
    a: &'a Analysis,
    /// Flow state layouts from Core lowering, keyed by the qualified flow name.
    layouts: HashMap<String, onsa_core::FlowLayout>,
}

impl Builder<'_> {
    /// Layout of a flow's `State`, if lowering produced one. Core names flows by
    /// their qualified name (`voice.voice`); fall back to a unique suffix match.
    fn flow_layout(&self, d: DefId) -> Option<&onsa_core::FlowLayout> {
        let q = self.a.qualified_name(d);
        if let Some(l) = self.layouts.get(&q) {
            return Some(l);
        }
        let suffix = format!(".{}", self.a.def(d).name);
        let mut hits = self.layouts.iter().filter(|(k, _)| k.ends_with(&suffix) || **k == self.a.def(d).name);
        let first = hits.next();
        if hits.next().is_some() { None } else { first.map(|(_, l)| l) }
    }

    fn ty(&self, t: onsa_sema::TyId, generics: &[onsa_sema::def::GenericDef]) -> String {
        self.a.types.display(t, &|d| self.display_name(d), &|i| {
            generics.get(i as usize).map(|g| g.name.clone()).unwrap_or_else(|| format!("<{i}>"))
        })
    }

    /// Flow members print as `voice.State` (§11.6); everything else by its name.
    fn display_name(&self, d: DefId) -> String {
        let def = self.a.def(d);
        match def.owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Flow(_)) => format!("{}.{}", self.a.def(o).name, def.name),
            _ => def.name.clone(),
        }
    }

    fn generics(&self, gs: &[onsa_sema::def::GenericDef]) -> Vec<String> {
        gs.iter()
            .map(|g| match &g.kind {
                GenericKind::Type { bounds, dup } => {
                    let mut s = g.name.clone();
                    let mut bs: Vec<String> = bounds.iter().map(|b| format!("{b:?}")).collect();
                    if !*dup {
                        bs.push("?Dup".into());
                    }
                    if !bs.is_empty() {
                        s.push_str(": ");
                        s.push_str(&bs.join(" + "));
                    }
                    s
                }
                GenericKind::Const(t) => format!("const {}: {}", g.name, self.ty(*t, gs)),
                GenericKind::Effect => g.name.clone(),
            })
            .collect()
    }

    fn fn_item(&self, d: DefId, display: &str) -> FnIface {
        let def = self.a.def(d);
        let f = def.as_fn().expect("fn def");
        // Methods see the impl's generics before their own (sig.rs).
        let generics: Vec<onsa_sema::def::GenericDef> = match def.owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) => {
                let mut g = self.a.def(o).generics().to_vec();
                g.extend(f.generics.iter().cloned());
                g
            }
            _ => f.generics.clone(),
        };
        let mut params: Vec<ParamIface> = Vec::new();
        if let Some(m) = f.self_mode {
            params.push(ParamIface { mode: mode_str(m).into(), name: "self".into(), ty: "Self".into() });
        }
        params.extend(f.params.iter().map(|p| ParamIface {
            mode: mode_str(p.mode).into(),
            name: p.name.clone(),
            ty: self.ty(p.ty, &generics),
        }));
        let ret = self.ty(f.ret, &generics);
        let mut effects = Vec::new();
        if f.effects.alloc {
            effects.push("Alloc".to_string());
        }
        effects.extend(f.effects.other.iter().cloned());
        effects.extend(
            f.effects.vars.iter().map(|&v| generics.get(v as usize).map(|g| g.name.clone()).unwrap_or_default()),
        );
        let own_generics = self.generics(&f.generics);
        let mut sig = String::new();
        if def.vis != Vis::Private {
            sig.push_str(vis_str(def.vis));
            sig.push(' ');
        }
        if f.target {
            sig.push_str("target ");
        }
        if f.rt {
            sig.push_str("rt ");
        }
        let _ = write!(sig, "fn {display}");
        if !own_generics.is_empty() {
            let _ = write!(sig, "[{}]", own_generics.join(", "));
        }
        let ps: Vec<String> = f
            .self_mode
            .map(|m| format!("{}self", mode_prefix(m)))
            .into_iter()
            .chain(f.params.iter().map(|p| format!("{}{}: {}", mode_prefix(p.mode), p.name, self.ty(p.ty, &generics))))
            .collect();
        let _ = write!(sig, "({})", ps.join(", "));
        if ret != "()" {
            let _ = write!(sig, " -> {ret}");
        }
        if !effects.is_empty() {
            let _ = write!(sig, " uses {{{}}}", effects.join(", "));
        }
        FnIface {
            name: display.to_string(),
            vis: vis_str(def.vis).into(),
            rt: f.rt,
            generics: own_generics,
            params,
            ret,
            effects,
            signature: sig,
        }
    }

    fn type_item(&self, d: DefId, display: &str) -> Item {
        let def = self.a.def(d);
        let generics = def.generics().to_vec();
        let no_args: Vec<onsa_sema::TyId> = Vec::new();
        let (kind, layout) = if generics.is_empty() {
            (onsa_sema::kind::kind_of_named(self.a, d, &no_args), onsa_sema::layout::layout_of_def(self.a, d, &no_args))
        } else {
            (None, None)
        };
        let mut iface = TypeIface {
            name: display.to_string(),
            vis: vis_str(def.vis).into(),
            generics: self.generics(&generics),
            value_kind: kind.map(|k| k.name().to_string()),
            size: layout.as_ref().map(|l| l.size),
            align: layout.as_ref().map(|l| l.align),
            bulk_size: None,
            derives: Vec::new(),
            fields: Vec::new(),
            variants: Vec::new(),
            flow_ty: None,
        };
        match &def.kind {
            DefKind::Struct(s) => {
                iface.derives = s.derives.iter().map(|x| format!("{x:?}")).collect();
                iface.flow_ty = s.flow_ty.map(|t| {
                    match t {
                        FlowTy::State => "State",
                        FlowTy::Config => "Config",
                        FlowTy::Params => "Params",
                        FlowTy::Out => "Out",
                    }
                    .to_string()
                });
                match &s.fields {
                    Fields::Named(fs) => {
                        for f in fs {
                            let offset = layout
                                .as_ref()
                                .and_then(|l| l.fields.iter().find(|(n, _)| *n == f.name).map(|(_, o)| *o));
                            iface.fields.push(FieldIface {
                                name: f.name.clone(),
                                ty: self.ty(f.ty, &generics),
                                offset,
                            });
                        }
                    }
                    Fields::Tuple(t) => {
                        iface.fields.push(FieldIface { name: "0".into(), ty: self.ty(*t, &generics), offset: Some(0) });
                    }
                    Fields::Opaque => {}
                }
                Item::Struct(iface)
            }
            DefKind::Enum(e) => {
                iface.derives = e.derives.iter().map(|x| format!("{x:?}")).collect();
                iface.variants = e
                    .variants
                    .iter()
                    .map(|v| VariantIface {
                        name: v.name.clone(),
                        fields: v.fields.iter().map(|&t| self.ty(t, &generics)).collect(),
                    })
                    .collect();
                Item::Enum(iface)
            }
            _ => unreachable!("type_item on a non-type"),
        }
    }

    fn const_item(&self, d: DefId, display: &str) -> Item {
        let def = self.a.def(d);
        let DefKind::Const(c) = &def.kind else { unreachable!() };
        let value =
            self.a.const_values.get(&d).map(|v| format!("{v:?}")).or_else(|| c.int_value.map(|v| v.to_string()));
        Item::Const { name: display.to_string(), vis: vis_str(def.vis).into(), ty: self.ty(c.ty, &[]), value }
    }

    fn flow_item(&self, d: DefId) -> Item {
        let def = self.a.def(d);
        let f = def.as_flow().expect("flow def");
        let inputs = f
            .inputs
            .iter()
            .map(|i| FlowInputIface {
                name: i.name.clone(),
                rate: match i.rate {
                    Rate::Init => "Init",
                    Rate::Ctl => "Ctl",
                    Rate::Sig => "Sig",
                }
                .into(),
                ty: self.ty(i.ty, &[]),
                param: i.param.as_ref().map(param_meta),
            })
            .collect();
        let layout = self.flow_layout(d);
        let mut members = Vec::new();
        for (name, m) in &f.members {
            let display = format!("{}.{}", def.name, name);
            let item = match &self.a.def(*m).kind {
                DefKind::Struct(_) | DefKind::Enum(_) => {
                    let mut item = self.type_item(*m, &display);
                    if let (Item::Struct(t), Some(l)) = (&mut item, layout)
                        && t.flow_ty.as_deref() == Some("State")
                    {
                        // Flow state layout from Core lowering (T3-6, §12.4).
                        t.size = Some(l.size);
                        t.align = Some(l.align);
                        t.bulk_size = Some(l.bulk_size);
                        t.fields = l
                            .fast_fields
                            .iter()
                            .map(|f| (f, "fast"))
                            .chain(l.bulk_fields.iter().map(|f| (f, "bulk")))
                            .map(|(f, region)| FieldIface {
                                name: f.name.clone(),
                                ty: format!("{} bytes, align {}, {region}", f.size, f.align),
                                offset: Some(f.offset),
                            })
                            .collect();
                    }
                    item
                }
                DefKind::Const(_) => {
                    let mut item = self.const_item(*m, &display);
                    if let (Item::Const { value, .. }, Some(l)) = (&mut item, layout) {
                        match name.as_str() {
                            "SIZE" => *value = Some(l.size.to_string()),
                            "BULK_SIZE" => *value = Some(l.bulk_size.to_string()),
                            "ALIGN" => *value = Some(l.align.to_string()),
                            _ => {}
                        }
                    }
                    item
                }
                DefKind::Fn(_) => Item::Fn(self.fn_item(*m, &display)),
                _ => continue,
            };
            members.push(item);
        }
        Item::Flow(FlowIface {
            name: def.name.clone(),
            vis: vis_str(def.vis).into(),
            inputs,
            out: self.ty(f.out, &[]),
            members,
        })
    }

    fn module_items(&self, m: ModId) -> Vec<Item> {
        let mut defs: Vec<(DefId, &onsa_sema::Def)> =
            self.a.defs_of_module(m).filter(|(_, d)| d.owner.is_none()).collect();
        defs.sort_by_key(|(_, d)| d.span.start);
        let mut items = Vec::new();
        for (id, def) in defs {
            let public = def.vis != Vis::Private;
            match &def.kind {
                DefKind::Fn(f) if public && f.flow_fn.is_none() => items.push(Item::Fn(self.fn_item(id, &def.name))),
                DefKind::Struct(s) if public && s.flow_ty.is_none() => items.push(self.type_item(id, &def.name)),
                DefKind::Enum(_) if public => items.push(self.type_item(id, &def.name)),
                DefKind::Alias(t) if public => items.push(Item::Alias {
                    name: def.name.clone(),
                    vis: vis_str(def.vis).into(),
                    ty: self.ty(*t, &[]),
                }),
                DefKind::Const(_) if public => items.push(self.const_item(id, &def.name)),
                DefKind::Flow(_) if public => items.push(self.flow_item(id)),
                DefKind::Impl(i) => {
                    let fns: Vec<FnIface> = i
                        .fns
                        .iter()
                        .filter(|&&f| self.a.def(f).vis != Vis::Private)
                        .map(|&f| self.fn_item(f, &self.a.def(f).name))
                        .collect();
                    let consts: Vec<Item> = i
                        .consts
                        .iter()
                        .filter(|&&c| self.a.def(c).vis != Vis::Private)
                        .map(|&c| self.const_item(c, &self.a.def(c).name))
                        .collect();
                    if !fns.is_empty() || !consts.is_empty() {
                        items.push(Item::Impl { ty: self.ty(i.self_ty, &i.generics), fns, consts });
                    }
                }
                _ => {}
            }
        }
        items
    }
}

/// Build the interface of the user package of an analyzed build. Flow state
/// layouts come from Core lowering (T3-6); when lowering fails (phase-2
/// features), the flow sizes are simply absent.
pub fn interface(analyzed: &Analyzed) -> Interface {
    let a = &analyzed.analysis;
    let core = crate::lower_core(analyzed).ok();
    let layouts: HashMap<String, onsa_core::FlowLayout> =
        core.map(|m| m.flows.into_iter().map(|f| (f.name, f.layout)).collect()).unwrap_or_default();
    let b = Builder { a, layouts };
    let mut modules: Vec<(String, ModId)> =
        analyzed.pkg.modules.iter().filter_map(|m| a.module_of_file(m.file).map(|id| (m.path.clone(), id))).collect();
    modules.sort();
    Interface {
        package: analyzed.pkg.name.clone(),
        modules: modules.into_iter().map(|(path, id)| ModuleIface { path, items: b.module_items(id) }).collect(),
    }
}

pub fn render_json(iface: &Interface) -> String {
    serde_json::to_string_pretty(iface).expect("interface serializes")
}

fn type_header(t: &TypeIface, keyword: &str, out: &mut String, indent: &str) {
    let mut line = indent.to_string();
    if !t.vis.is_empty() {
        line.push_str(&t.vis);
        line.push(' ');
    }
    let _ = write!(line, "{keyword} {}", t.name);
    if !t.generics.is_empty() {
        let _ = write!(line, "[{}]", t.generics.join(", "));
    }
    let mut props = Vec::new();
    if let Some(k) = &t.value_kind {
        props.push(k.clone());
    }
    match (t.size, t.align) {
        (Some(s), Some(a)) => match t.bulk_size {
            Some(b) => props.push(format!("size {s}, bulk {b}, align {a}")),
            None => props.push(format!("size {s}, align {a}")),
        },
        _ if t.flow_ty.as_deref() == Some("State") => props.push("size: not available (lowering failed)".into()),
        _ => {}
    }
    if !t.derives.is_empty() {
        props.push(format!("derive {}", t.derives.join(", ")));
    }
    if !props.is_empty() {
        let _ = write!(line, "  // {}", props.join("; "));
    }
    out.push_str(&line);
    out.push('\n');
}

fn render_type(t: &TypeIface, keyword: &str, out: &mut String, indent: &str) {
    type_header(t, keyword, out, indent);
    for f in &t.fields {
        match f.offset {
            Some(o) => {
                let _ = writeln!(out, "{indent}  {}: {}  // offset {o}", f.name, f.ty);
            }
            None => {
                let _ = writeln!(out, "{indent}  {}: {}", f.name, f.ty);
            }
        }
    }
    for v in &t.variants {
        if v.fields.is_empty() {
            let _ = writeln!(out, "{indent}  {}", v.name);
        } else {
            let _ = writeln!(out, "{indent}  {}({})", v.name, v.fields.join(", "));
        }
    }
}

fn render_item(item: &Item, out: &mut String, indent: &str) {
    match item {
        Item::Fn(f) => {
            let _ = writeln!(out, "{indent}{}", f.signature);
        }
        Item::Struct(t) => render_type(t, "struct", out, indent),
        Item::Enum(t) => render_type(t, "enum", out, indent),
        Item::Alias { name, vis, ty } => {
            let v = if vis.is_empty() { String::new() } else { format!("{vis} ") };
            let _ = writeln!(out, "{indent}{v}type {name} = {ty}");
        }
        Item::Const { name, vis, ty, value } => {
            let v = if vis.is_empty() { String::new() } else { format!("{vis} ") };
            match value {
                Some(val) => {
                    let _ = writeln!(out, "{indent}{v}const {name}: {ty} = {val}");
                }
                None => {
                    let _ = writeln!(out, "{indent}{v}const {name}: {ty}");
                }
            }
        }
        Item::Impl { ty, fns, consts } => {
            let _ = writeln!(out, "{indent}impl {ty}");
            for c in consts {
                render_item(c, out, &format!("{indent}  "));
            }
            for f in fns {
                let _ = writeln!(out, "{indent}  {}", f.signature);
            }
        }
        Item::Flow(f) => {
            let v = if f.vis.is_empty() { String::new() } else { format!("{} ", f.vis) };
            let _ = writeln!(out, "{indent}{v}flow {}(", f.name);
            for i in &f.inputs {
                if let Some(p) = &i.param {
                    let mut kv = Vec::new();
                    if let Some(x) = p.min {
                        kv.push(format!("min: {x:?}"));
                    }
                    if let Some(x) = p.max {
                        kv.push(format!("max: {x:?}"));
                    }
                    if let Some(x) = p.default {
                        kv.push(format!("default: {x:?}"));
                    }
                    if let Some(x) = p.step {
                        kv.push(format!("step: {x:?}"));
                    }
                    if let Some(x) = &p.unit {
                        kv.push(format!("unit: \"{x}\""));
                    }
                    if let Some(x) = &p.scale {
                        kv.push(format!("scale: \"{x}\""));
                    }
                    if let Some(x) = &p.label {
                        kv.push(format!("label: \"{x}\""));
                    }
                    if let Some(x) = &p.id {
                        kv.push(format!("id: \"{x}\""));
                    }
                    let _ = writeln!(out, "{indent}  @param({})", kv.join(", "));
                }
                let _ = writeln!(out, "{indent}  {}: {}[{}],", i.name, i.rate, i.ty);
            }
            let _ = writeln!(out, "{indent}) -> Sig[{}]", f.out);
            for m in &f.members {
                render_item(m, out, &format!("{indent}  "));
            }
        }
    }
}

/// Deterministic text form, module by module in path order.
pub fn render_text(iface: &Interface) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "package {}", iface.package);
    for m in &iface.modules {
        let _ = writeln!(out, "\nmodule {}", if m.path.is_empty() { "(root)" } else { &m.path });
        for item in &m.items {
            out.push('\n');
            render_item(item, &mut out, "");
        }
    }
    out
}
