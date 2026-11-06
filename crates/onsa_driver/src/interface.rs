//! `onsa interface` (T3-11; spec §18.2): the signatures of a package, of the
//! items and members of `pub` and of no word (not `priv`, S-660), each type's kind (§4.6) and size (§12.1), `@param` metadata (§11.7) and
//! the generated API of every flow in the form of §11.6. The data lives in
//! [`Interface`]; `render_text` / `render_json` print it, so the LSP and the
//! web API can reuse it.
//!
//! JSON shape (stable; `--json`): the document of every `--json` (§18.1,
//! `onsa_diag::to_json_document`), so `diagnostics` is there, empty:
//!
//! ```json
//! { "diagnostics": [],
//!   "package": "voice",
//!   "modules": [ { "path": "dsp.voice", "items": [
//!     { "kind": "fn", "name": "wrap01", "vis": "pub", "rt": true,
//!       "params": [ { "mode": "borrow", "name": "x", "ty": "F32" } ],
//!       "ret": "F32", "effects": [], "signature": "pub rt fn wrap01(x: F32) -> F32" },
//!     { "kind": "struct", "name": "Poly", "vis": "pub", "value_kind": "Affine",
//!       "size": 1234, "align": 8, "generics": [],
//!       "fields": [ { "name": "voices", "vis": "", "ty": "[voice.State; 8]", "offset": 0 },
//!                   { "name": "gain", "vis": "", "ty": "F32", "offset": 1024, "default": "0.5" } ] },
//!     { "kind": "enum", "name": "Shape", ..., "variants": [ { "name": "Circle", "fields": ["F32"] } ] },
//!     { "kind": "const", "name": "MAX_VOICES", "ty": "U32", "value": "8" },
//!     { "kind": "alias", "name": "Samples", "ty": "Buf[F32]" },
//!     { "kind": "impl", "ty": "Poly", "fns": [ ...fn items... ], "consts": [ ...const items... ] },
//!     { "kind": "flow", "name": "voice", "vis": "pub",
//!       "inputs": [ { "name": "f0", "clock": "block", "ty": "F32",
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
use onsa_sema::ty::{Env, Rate};
use onsa_sema::{Analysis, ConstValue, DefId, ModId, Ty, TyId};
use onsa_syntax::ast::{Mode, Vis};
use serde::Serialize;

use crate::Analyzed;

#[derive(Debug, Clone, Serialize)]
pub struct Interface {
    pub package: String,
    pub modules: Vec<ModuleIface>,
}

impl Interface {
    /// Keep the module `path` only: the interface of a file passed inside
    /// the package is the declarations of its module (§15.1).
    pub fn narrow(&mut self, path: &str) {
        self.modules.retain(|m| m.path == path);
    }
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
        /// The trait of `impl Tr for Ty`.
        #[serde(rename = "trait", skip_serializing_if = "Option::is_none")]
        of: Option<String>,
        /// The parameters of the `impl`, which its methods see (§18.2).
        generics: Vec<String>,
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
    /// `State` / `Config` / `Params` / `Out` of a flow: by its name in the JSON.
    #[serde(skip_serializing_if = "Option::is_none", serialize_with = "flow_ty_name")]
    pub flow_ty: Option<FlowTy>,
}

fn flow_ty_name<S: serde::Serializer>(t: &Option<FlowTy>, s: S) -> Result<S::Ok, S::Error> {
    t.map(FlowTy::name).serialize(s)
}

#[derive(Debug, Clone, Serialize)]
pub struct FieldIface {
    pub name: String,
    /// `priv`, or empty: the field has the visibility of its struct.
    pub vis: String,
    pub ty: String,
    pub offset: Option<u32>,
    /// The value of its default (§4.4) when the compile-time evaluation
    /// folds it (S-920): none of a default it does not, and of one that reads
    /// a parameter of the struct, which has a value for each instance.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub default: Option<String>,
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
    /// The clock after the type (`init`, `block`, `sample`, §11.3).
    pub clock: String,
    pub ty: String,
    /// The type is a function type, written in parentheses before `at` in
    /// the text form (S-367).
    #[serde(skip)]
    pub parens: bool,
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

/// Whether an item or a member of `v` is shown: `pub` and no word, not
/// `priv` (§18.2, S-660).
fn shown(v: Vis) -> bool {
    v != Vis::Priv
}

/// The fields of a struct value in braces, `{}` when it has none (as `fmt`
/// writes it).
fn braced(each: &[String]) -> String {
    if each.is_empty() { "{}".into() } else { format!("{{ {} }}", each.join(", ")) }
}

fn vis_str(v: Vis) -> &'static str {
    match v {
        Vis::Default => "",
        Vis::Priv => "priv",
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

/// The metadata of `@param`, its numbers shown in the input's type
/// ([`onsa_syntax::float_shown`]).
fn param_meta(p: &ParamMeta) -> ParamIfaceMeta {
    let shown = |x: Option<f64>| x.map(|x| onsa_syntax::float_shown(x, p.width));
    ParamIfaceMeta {
        min: shown(p.min),
        max: shown(p.max),
        default: shown(p.default),
        step: shown(p.step),
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
        self.a.shown_name(d)
    }

    fn generics(&self, gs: &[onsa_sema::def::GenericDef]) -> Vec<String> {
        gs.iter()
            .map(|g| match &g.kind {
                GenericKind::Type { bounds, dup, escape, .. } => {
                    let mut s = g.name.clone();
                    let mut bs: Vec<String> = bounds.iter().map(|b| format!("{b:?}")).collect();
                    if !*dup {
                        bs.push("?Dup".into());
                    }
                    if !*escape {
                        bs.push("?Escape".into());
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
        // A method's generics start with its impl's (sig.rs), which the
        // heading of the `impl` shows (R-382).
        let generics = &f.generics;
        let of_impl = match def.owner {
            Some(o) if matches!(self.a.def(o).kind, DefKind::Impl(_)) => self.a.def(o).generics().len(),
            _ => 0,
        };
        let mut params: Vec<ParamIface> = Vec::new();
        if let Some(m) = f.self_mode {
            params.push(ParamIface { mode: mode_str(m).into(), name: "self".into(), ty: "Self".into() });
        }
        params.extend(f.params.iter().map(|p| ParamIface {
            mode: mode_str(p.mode).into(),
            name: p.name.clone(),
            ty: self.ty(p.ty, generics),
        }));
        let ret = self.ty(f.ret, generics);
        let mut effects = Vec::new();
        if f.effects.alloc {
            effects.push("Alloc".to_string());
        }
        effects.extend(f.effects.other.iter().cloned());
        effects.extend(
            f.effects.vars.iter().map(|&v| generics.get(v as usize).map(|g| g.name.clone()).unwrap_or_default()),
        );
        let own_generics = self.generics(&generics[of_impl.min(generics.len())..]);
        // A member of a trait's `impl` has no word (§15.1).
        let of_trait = def.owner.and_then(|o| self.a.def(o).as_impl()).is_some_and(|i| i.of.is_some());
        let vis = if of_trait { Vis::Default } else { def.vis };
        let mut sig = String::new();
        if vis == Vis::Pub {
            sig.push_str(vis_str(vis));
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
            .chain(f.params.iter().map(|p| format!("{}{}: {}", mode_prefix(p.mode), p.name, self.ty(p.ty, generics))))
            .collect();
        let _ = write!(sig, "({})", ps.join(", "));
        if self.a.types.parens_before_uses(f.ret, !effects.is_empty()) {
            let _ = write!(sig, " -> ({ret})");
        } else if ret != "()" {
            let _ = write!(sig, " -> {ret}");
        }
        if !effects.is_empty() {
            let _ = write!(sig, " uses {{{}}}", effects.join(", "));
        }
        FnIface {
            name: display.to_string(),
            vis: vis_str(vis).into(),
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
                iface.derives = s.derives.iter().flatten().map(|x| format!("{x:?}")).collect();
                iface.flow_ty = s.flow_ty;
                match &s.fields {
                    Fields::Named(fs) => {
                        for f in fs {
                            let offset = layout
                                .as_ref()
                                .and_then(|l| l.fields.iter().find(|(n, _)| *n == f.name).map(|(_, o)| *o));
                            // The word written: `priv` alone (§15.1, S-660).
                            let vis = if f.vis == Vis::Priv { vis_str(Vis::Priv) } else { "" };
                            iface.fields.push(FieldIface {
                                name: f.name.clone(),
                                vis: vis.into(),
                                ty: self.ty(f.ty, &generics),
                                offset,
                                default: f.default.and_then(|d| self.const_text(d)),
                            });
                        }
                    }
                    Fields::Opaque => {}
                }
                Item::Struct(iface)
            }
            DefKind::Enum(e) => {
                iface.derives = e.derives.iter().flatten().map(|x| format!("{x:?}")).collect();
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
        let value = self.const_text(d);
        Item::Const { name: display.to_string(), vis: vis_str(def.vis).into(), ty: self.ty(c.ty, &[]), value }
    }

    /// The value of the constant `d` as it is written, when it is folded.
    fn const_text(&self, d: DefId) -> Option<String> {
        let DefKind::Const(c) = &self.a.def(d).kind else { unreachable!() };
        let value = self.a.const_values.get(&d).map(|v| self.value_text(v, Some(c.ty), None));
        value.or_else(|| c.int_value.map(|v| v.to_string()))
    }

    /// The value `v` of the type `ty` as it is written in the source (§2.4,
    /// §4.1): each float in its type ([`onsa_syntax::float_shown`]), a char
    /// with its escapes (§2.4), and the arrays, tuples and structs of them
    /// (`P { x: 1, y: 2.5 }`).
    /// Of no type known (`None`), the floats are as they are held. The type
    /// is read under the arguments `env` (a field of a generic struct, R-30).
    fn value_text(&self, v: &ConstValue, ty: Option<TyId>, env: Option<&Env>) -> String {
        let (ty, env) = match ty.map(|t| self.a.types.resolve(t, env)) {
            Some((t, env)) => (Some(self.a.types.get(t)), env),
            None => (None, None),
        };
        let list_in = |vs: &[ConstValue], tys: &[TyId], env: Option<&Env>| -> Vec<String> {
            vs.iter().enumerate().map(|(i, v)| self.value_text(v, tys.get(i).copied(), env)).collect()
        };
        let list = |vs: &[ConstValue], tys: &[TyId]| list_in(vs, tys, env);
        match (v, ty) {
            (ConstValue::Int(x), _) => x.to_string(),
            (ConstValue::Float(x), Some(Ty::Float(k))) => format!("{:?}", onsa_syntax::float_shown(*x, k.width())),
            (ConstValue::Float(x), _) => format!("{x:?}"),
            (ConstValue::FloatText(t), _) => t.clone(),
            (ConstValue::Bool(b), _) => b.to_string(),
            (ConstValue::Char(c), _) => format!("'{}'", c.escape_default()),
            (ConstValue::Unit, _) => "()".into(),
            (ConstValue::Array(vs), Some(Ty::Array(elem, _))) => {
                format!("[{}]", list(vs, &vec![*elem; vs.len()]).join(", "))
            }
            (ConstValue::Array(vs), _) => format!("[{}]", list(vs, &[]).join(", ")),
            (ConstValue::Tuple(vs), Some(Ty::Tuple(tys))) => format!("({})", list(vs, tys).join(", ")),
            (ConstValue::Tuple(vs), _) => format!("({})", list(vs, &[]).join(", ")),
            (ConstValue::Struct(vs), Some(Ty::Named(s, args))) => {
                let fields: Vec<(String, TyId)> = match &self.a.def(*s).kind {
                    DefKind::Struct(sd) => match &sd.fields {
                        Fields::Named(fs) => fs.iter().map(|f| (f.name.clone(), f.ty)).collect(),
                        Fields::Opaque => Vec::new(),
                    },
                    _ => Vec::new(),
                };
                let tys: Vec<TyId> = fields.iter().map(|(_, t)| *t).collect();
                let each: Vec<String> = list_in(vs, &tys, Some(&Env { args, outer: env, key: None }))
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| match fields.get(i) {
                        Some((name, _)) => format!("{name}: {v}"),
                        None => v,
                    })
                    .collect();
                format!("{} {}", self.display_name(*s), braced(&each))
            }
            (ConstValue::Struct(vs), _) => braced(&list(vs, &[])),
        }
    }

    fn flow_item(&self, d: DefId) -> Item {
        let def = self.a.def(d);
        let f = def.as_flow().expect("flow def");
        let inputs = f
            .inputs
            .iter()
            .map(|i| FlowInputIface {
                name: i.name.clone(),
                clock: i.rate.clock().into(),
                ty: self.ty(i.ty, &[]),
                parens: self.a.types.parens_before_uses(i.ty, true),
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
                        && t.flow_ty == Some(FlowTy::State)
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
                                vis: String::new(),
                                ty: format!("{} bytes, align {}, {region}", f.size, f.align),
                                offset: Some(f.offset),
                                default: None,
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

    /// Whether the type of an `impl` is shown (§18.2, S-660): a builtin type,
    /// or one not `priv` (of a flow, the flow's visibility).
    fn shown_type(&self, t: TyId) -> bool {
        match self.a.types.get(t) {
            Ty::Named(d, _) => shown(self.a.def(*d).vis),
            _ => true,
        }
    }

    fn module_items(&self, m: ModId) -> Vec<Item> {
        let mut defs: Vec<(DefId, &onsa_sema::Def)> =
            self.a.defs_of_module(m).filter(|(_, d)| d.owner.is_none()).collect();
        defs.sort_by_key(|(_, d)| d.span.start);
        let mut items = Vec::new();
        for (id, def) in defs {
            let public = shown(def.vis);
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
                // The `impl` of a type not shown is not shown (R-265).
                DefKind::Impl(i) if self.shown_type(i.self_ty) => {
                    let fns: Vec<FnIface> = i
                        .fns
                        .iter()
                        .filter(|&&f| shown(self.a.def(f).vis))
                        .map(|&f| self.fn_item(f, &self.a.def(f).name))
                        .collect();
                    let consts: Vec<Item> = i
                        .consts
                        .iter()
                        .filter(|&&c| shown(self.a.def(c).vis))
                        .map(|&c| self.const_item(c, &self.a.def(c).name))
                        .collect();
                    if !fns.is_empty() || !consts.is_empty() {
                        let of = i.of.map(|b| b.name().to_string());
                        let generics = self.generics(&i.generics);
                        items.push(Item::Impl { of, generics, ty: self.ty(i.self_ty, &i.generics), fns, consts });
                    }
                }
                _ => {}
            }
        }
        items
    }
}

/// Build the interface of the user package of an analyzed build. Flow state
/// layouts come from Core lowering (T3-6); when lowering reports features this
/// version does not have (phase-2 features), the flow sizes are simply absent.
/// Its other diagnostics are errors of the program (E0903, S-911) and stop the
/// command, and so does an internal error (a Core the verifier rejects, R-82; S-67).
pub fn interface(analyzed: &Analyzed) -> Result<Interface, crate::LowerError> {
    let core = match crate::lower_core(analyzed) {
        Ok(m) => Some(m),
        Err(crate::LowerError::Diagnostics(mut d)) => {
            d.retain(|d| !onsa_diag::unsupported::is_unsupported(d));
            if !d.is_empty() {
                return Err(crate::LowerError::Diagnostics(d));
            }
            None
        }
        Err(e) => return Err(e),
    };
    Ok(crate::guard(|| interface_of(analyzed, core))?)
}

fn interface_of(analyzed: &Analyzed, core: Option<onsa_core::Module>) -> Interface {
    let a = &analyzed.analysis;
    let layouts: HashMap<String, onsa_core::FlowLayout> =
        core.map(|m| m.flows.into_iter().map(|f| (f.name, f.layout)).collect()).unwrap_or_default();
    let b = Builder { a, layouts };
    let mut modules: Vec<(String, ModId)> =
        analyzed.pkg.modules.iter().filter_map(|m| a.module_of_file(m.file).map(|id| (m.path(), id))).collect();
    modules.sort();
    Interface {
        package: analyzed.pkg.name.clone(),
        modules: modules.into_iter().map(|(path, id)| ModuleIface { path, items: b.module_items(id) }).collect(),
    }
}

pub fn render_json(iface: &Interface) -> String {
    onsa_diag::to_json_document(&onsa_diag::SourceMap::default(), &[], iface)
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
        _ if t.flow_ty == Some(FlowTy::State) => props.push("size: not available (lowering failed)".into()),
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
        let v = if f.vis.is_empty() { String::new() } else { format!("{} ", f.vis) };
        let d = f.default.as_ref().map_or(String::new(), |d| format!(" = {d}"));
        match f.offset {
            Some(o) => {
                let _ = writeln!(out, "{indent}  {v}{}: {}{d}  // offset {o}", f.name, f.ty);
            }
            None => {
                let _ = writeln!(out, "{indent}  {v}{}: {}{d}", f.name, f.ty);
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
        Item::Impl { of, generics, ty, fns, consts } => {
            let of = of.as_ref().map_or(String::new(), |t| format!("{t} for "));
            let params = if generics.is_empty() { String::new() } else { format!("[{}]", generics.join(", ")) };
            let _ = writeln!(out, "{indent}impl{params} {of}{ty}");
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
                let ty = if i.parens { format!("({})", i.ty) } else { i.ty.clone() };
                let _ = writeln!(out, "{indent}  {}: {ty} at {},", i.name, i.clock);
            }
            // The output is at the clock `sample` (§11.6).
            let _ = writeln!(out, "{indent}) -> {} at {}", f.out, Rate::Sig.clock());
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
