//! Core → C11 (T4-2): types, constants, and function bodies.
//!
//! Expressions are emitted as C expression strings; anything C cannot hold
//! in an expression (calls returning aggregates, blocks, `if` / `switch`
//! expressions, loops building arrays, panics) is hoisted into statements
//! with temporaries declared at the point of use. Evaluation order is kept
//! by materialising every earlier operand into a temporary as soon as a
//! later operand needs statements (`operands`), so the C expression that
//! remains has no side effects and its sub-expression order no longer
//! matters.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use onsa_core::prim::{CheckedOp, MathFn, Prim};
use onsa_core::{
    BinOp, Block, CmpOp, ConstId, Expr, ExprKind, FloatKind, FnDef, FnId, IntKind, Lit, LocalId, LogicOp, Mode, Module,
    Overflow, Place, Stmt, StmtKind, Ty, TypeDefKind, TypeId, UnOp,
};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::names::{Entry, TypeNames, float_tag, ident, int_tag, qualified};
use crate::reach::{Reach, has_return, reach, walk_block};
use crate::{CUnit, EmitOptions, PanicMode, no_span, unsupported};

pub(crate) type R<T> = Result<T, Diagnostic>;

/// A flow state split into a fast struct and a bulk struct (spec §12.4).
#[derive(Debug, Clone)]
pub(crate) struct BulkInfo {
    pub struct_name: String,
    /// Field indices of the Core `State` that live in the bulk region.
    pub fields: HashSet<u32>,
}

/// An exported flow, resolved.
#[derive(Debug, Clone)]
pub(crate) struct Export {
    pub meta_index: usize,
    /// `onsa_voice`
    pub symbol: String,
    /// `ONSA_VOICE`
    pub upper: String,
    pub layout: onsa_core::FlowLayout,
}

/// Shared state of one translation unit.
pub(crate) struct Cx<'m> {
    pub m: &'m Module,
    pub opts: &'m EmitOptions,
    pub names: TypeNames<'m>,
    pub bulk: HashMap<TypeId, BulkInfo>,
    pub fn_names: HashMap<FnId, String>,
    pub const_names: HashMap<ConstId, String>,
    pub exports: Vec<Export>,
    /// Params struct types of exported flows: typedef'd from the header.
    pub header_params: HashMap<TypeId, String>,
}

impl Cx<'_> {
    pub fn loc(&self, span: Span) -> String {
        match (&self.opts.locate, self.opts.panic_messages) {
            (Some(l), true) => {
                let (f, line) = l(span);
                format!("{}, {line}", c_string(&f))
            }
            _ => "\"\", 0".into(),
        }
    }

    pub fn msg(&self, text: &str) -> String {
        if self.opts.panic_messages { c_string(text) } else { "\"\"".into() }
    }

    pub fn fn_name(&self, f: FnId) -> &str {
        &self.fn_names[&f]
    }

    /// Fields of a struct type.
    pub fn fields(&self, id: TypeId) -> &[(String, Ty)] {
        match &self.m.ty(id).kind {
            TypeDefKind::Struct { fields } => fields,
            _ => &[],
        }
    }

    pub fn variants(&self, id: TypeId) -> &[(String, Vec<Ty>)] {
        match &self.m.ty(id).kind {
            TypeDefKind::Enum { variants } => variants,
            _ => &[],
        }
    }

    pub fn tag_c(&self, id: TypeId) -> &'static str {
        match self.variants(id).len() {
            0..=256 => "uint8_t",
            257..=65536 => "uint16_t",
            _ => "uint32_t",
        }
    }
}

pub fn c_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c == '\u{7f}' => {
                let _ = write!(out, "\\x{:02x}\"\"", c as u32);
            }
            c if c.is_ascii() => out.push(c),
            c => {
                let mut buf = [0u8; 4];
                for b in c.encode_utf8(&mut buf).bytes() {
                    let _ = write!(out, "\\x{b:02x}");
                }
                out.push_str("\"\"");
            }
        }
    }
    out.push('"');
    out
}

/// Format a float so that C reads back the same value.
pub fn f32_lit(x: f32) -> String {
    if x.is_nan() {
        "NAN".into()
    } else if x.is_infinite() {
        if x > 0.0 { "INFINITY".into() } else { "(-INFINITY)".into() }
    } else {
        let s = format!("{x:?}");
        if s.contains('.') || s.contains('e') { format!("{s}f") } else { format!("{s}.0f") }
    }
}

pub fn f64_lit(x: f64) -> String {
    if x.is_nan() {
        "NAN".into()
    } else if x.is_infinite() {
        if x > 0.0 { "INFINITY".into() } else { "(-INFINITY)".into() }
    } else {
        let s = format!("{x:?}");
        if s.contains('.') || s.contains('e') { s } else { format!("{s}.0") }
    }
}

pub fn int_lit(k: IntKind, v: i128) -> String {
    match k {
        IntKind::I8 => format!("((int8_t){v})"),
        IntKind::I16 => format!("((int16_t){v})"),
        IntKind::I32 => {
            if v == i32::MIN as i128 {
                "INT32_MIN".into()
            } else {
                format!("INT32_C({v})")
            }
        }
        IntKind::I64 => {
            if v == i64::MIN as i128 {
                "INT64_MIN".into()
            } else {
                format!("INT64_C({v})")
            }
        }
        IntKind::U8 => format!("((uint8_t){v})"),
        IntKind::U16 => format!("((uint16_t){v})"),
        IntKind::U32 => format!("UINT32_C({v})"),
        IntKind::U64 => format!("UINT64_C({v})"),
    }
}

fn lit(l: &Lit, ty: &Ty) -> String {
    match (l, ty) {
        (Lit::Int(v), Ty::Int(k)) => int_lit(*k, *v),
        (Lit::Int(v), _) => format!("{v}"),
        (Lit::F32(x), _) => f32_lit(*x),
        (Lit::F64(x), _) => f64_lit(*x),
        (Lit::Bool(b), _) => if *b { "true" } else { "false" }.into(),
        (Lit::Char(c), _) => format!("UINT32_C({})", *c as u32),
        (Lit::Unit, _) => "((onsa_unit){0})".into(),
    }
}

/// Zero value of a scalar type, for dead code after a panic.
fn zero_scalar(ty: &Ty) -> Option<String> {
    Some(match ty {
        Ty::Int(k) => int_lit(*k, 0),
        Ty::Float(FloatKind::F32) => "0.0f".into(),
        Ty::Float(FloatKind::F64) => "0.0".into(),
        Ty::Bool => "false".into(),
        Ty::Char => "UINT32_C(0)".into(),
        Ty::Unit => "((onsa_unit){0})".into(),
        _ => return None,
    })
}

// ------------------------------------------------------------ the unit

pub(crate) fn emit_unit(m: &Module, opts: &EmitOptions) -> Result<CUnit, Vec<Diagnostic>> {
    let mut diags = Vec::new();
    let mut cx = Cx {
        m,
        opts,
        names: TypeNames::new(m),
        bulk: HashMap::new(),
        fn_names: HashMap::new(),
        const_names: HashMap::new(),
        exports: Vec::new(),
        header_params: HashMap::new(),
    };

    // 1. Exports and roots.
    let mut roots: Vec<FnId> = Vec::new();
    for e in &opts.exports {
        let Some(i) = find_flow(m, &e.flow) else {
            diags.push(Diagnostic::new(
                Stage::Build,
                Code::E0302,
                no_span(),
                format!("cannot find the flow `{}` to export", e.flow),
            ));
            continue;
        };
        let meta = &m.flows[i];
        let short = meta.name.rsplit('.').next().unwrap_or(&meta.name).to_string();
        let symbol = format!("{}{}", opts.prefix, ident(&short));
        let upper: String =
            symbol.chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_uppercase() } else { '_' }).collect();
        let layout = onsa_core::flow_layout_for(m, meta.fns.state, opts.bulk_threshold, opts.ptr_size);
        cx.exports.push(Export { meta_index: i, symbol, upper, layout });
        let f = &meta.fns;
        roots.extend([f.init, f.reset, f.ctl, f.tick, f.process]);
        if let Some(p) = f.params_default {
            roots.push(p);
        }
    }
    let mut export_fns: Vec<FnId> = Vec::new();
    for name in &opts.export_fns {
        match m.fns.iter().position(|f| &f.name == name) {
            Some(i) => {
                roots.push(FnId(i as u32));
                export_fns.push(FnId(i as u32));
            }
            None => diags.push(Diagnostic::new(
                Stage::Build,
                Code::E0302,
                no_span(),
                format!("cannot find the function `{name}` to export"),
            )),
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }
    let reach: Reach = reach(m, &roots);

    // 2. Bulk regions of exported states (spec §12.4). A bulk-split state
    //    embedded in another reachable type is not supported yet.
    for e in &cx.exports {
        if e.layout.bulk_size > 0 {
            let state = m.flows[e.meta_index].fns.state;
            let bulk_names: HashSet<&str> = e.layout.bulk_fields.iter().map(|f| f.name.as_str()).collect();
            let fields = cx
                .fields(state)
                .iter()
                .enumerate()
                .filter(|(_, (n, _))| bulk_names.contains(n.as_str()))
                .map(|(i, _)| i as u32)
                .collect();
            cx.bulk.insert(state, BulkInfo { struct_name: format!("{}__Bulk", qualified(&m.ty(state).name)), fields });
        }
    }
    for (i, t) in m.types.iter().enumerate() {
        if let TypeDefKind::Struct { fields } = &t.kind {
            for (_, fty) in fields {
                if let Some(id) = contains_bulk(&cx, fty) {
                    diags.push(unsupported(no_span(), Feature::BulkInType, &[&m.ty(id).name, &m.types[i].name]));
                }
            }
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }

    // 3. Names of functions and constants.
    for f in &reach.fns {
        cx.fn_names.insert(*f, qualified(&m.fn_(*f).name));
    }
    for c in &reach.consts {
        cx.const_names.insert(*c, qualified(&m.const_(*c).name));
    }
    // Exported states keep the public tag; exported params come from the header.
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        cx.names.tags.insert(f.state, e.symbol.clone());
        cx.header_params.insert(f.params, format!("{}_params", e.symbol));
    }

    // 4. Register every type the unit needs (dependency order falls out).
    for c in &reach.consts {
        cx.names.name(&m.const_(*c).ty);
    }
    for f in &reach.fns {
        let def = m.fn_(*f);
        for p in &def.params {
            cx.names.name(&p.ty);
        }
        cx.names.name(&def.ret);
        for l in &def.locals {
            cx.names.name(&l.ty);
        }
        if let Some(b) = &def.body {
            let mut tys = Vec::new();
            walk_block(b, &mut |e| tys.push(e.ty.clone()));
            for t in tys {
                cx.names.name(&t);
            }
        }
    }
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        cx.names.name(&Ty::Struct(f.state));
        cx.names.name(&Ty::Struct(f.config));
        cx.names.name(&Ty::Struct(f.params));
    }

    // 5. Headers (T4-3) and the translation unit.
    let mut headers = Vec::new();
    let mut flows = Vec::new();
    for e in cx.exports.clone() {
        match crate::export::header(&mut cx, &e) {
            Ok((h, parts)) => {
                let header = format!("{}.h", e.symbol);
                flows.push(crate::FlowApi {
                    flow: m.flows[e.meta_index].name.clone(),
                    symbol: e.symbol.clone(),
                    upper: e.upper.clone(),
                    header: header.clone(),
                    init_args: parts.init_args,
                    params_fields: parts.params_fields,
                    process_args: parts.process_args,
                });
                headers.push((header, h));
            }
            Err(d) => diags.push(d),
        }
    }
    let mut fns = Vec::new();
    if !export_fns.is_empty() {
        let header = format!("{}{}.h", opts.prefix, ident(&opts.package));
        match crate::export::fn_header(&mut cx, &export_fns, &header) {
            Ok((h, apis)) => {
                headers.push((header, h));
                fns = apis;
            }
            Err(d) => diags.push(d),
        }
    }

    let mut out = String::new();
    let _ = writeln!(
        out,
        "/* {} — generated by onsa build from package `{}`; do not edit. */",
        CUnit::source_name(&opts.package),
        opts.package
    );
    let _ = writeln!(out, "#define {}", opts.panic.define());
    let _ = writeln!(out, "#include \"{}\"", crate::RUNTIME_HEADER_NAME);
    if opts.provides_alloc {
        let _ = writeln!(out, "#include <stdlib.h>");
    }
    for (name, _) in &headers {
        let _ = writeln!(out, "#include \"{name}\"");
    }
    out.push('\n');

    // Types.
    let _ = writeln!(out, "/* ---- types ---- */");
    let order = cx.names.order.clone();
    for entry in &order {
        match type_def(&mut cx, entry) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        let state = cx.names.defs[&f.state].clone();
        // The C compiler verifies the header's SIZE / ALIGN against the real
        // struct (spec §12.4). The `poison` jmp_buf is a wrapper local (S-26),
        // so the layout is the same on every target.
        let _ = writeln!(
            out,
            "ONSA_STATIC_ASSERT(sizeof({state}) == {}_SIZE, \"{} fast region size (spec §12.4)\");",
            e.upper, e.upper
        );
        let _ = writeln!(
            out,
            "ONSA_STATIC_ASSERT(ONSA_ALIGNOF({state}) == {}_ALIGN, \"{} alignment (spec §12.4)\");",
            e.upper, e.upper
        );
        for mark in ["poisoned", "initialized"] {
            if let Some(p) = e.layout.fast_fields.iter().find(|f| f.name == mark) {
                let _ = writeln!(
                    out,
                    "ONSA_STATIC_ASSERT(offsetof({state}, {mark}) == {}, \"{} layout prefix (spec §12.4)\");",
                    p.offset, e.upper
                );
            }
        }
        if let Some(b) = cx.bulk.get(&f.state) {
            let _ = writeln!(
                out,
                "ONSA_STATIC_ASSERT(sizeof({}) == {}, \"{} bulk region size (spec §12.4)\");",
                b.struct_name, e.layout.bulk_size, e.upper
            );
        }
    }
    out.push('\n');

    // Constants.
    if !reach.consts.is_empty() {
        let _ = writeln!(out, "/* ---- constants ---- */");
        for c in &reach.consts {
            let def = m.const_(*c);
            let ty = cx.names.name(&def.ty);
            match const_init(&mut cx, &def.init) {
                Ok(init) => {
                    let _ = writeln!(out, "static const {ty} {} = {init};", cx.const_names[c]);
                }
                Err(d) => diags.push(d),
            }
        }
        out.push('\n');
    }

    // Functions: prototypes, then definitions.
    let _ = writeln!(out, "/* ---- functions ---- */");
    let mut protos = String::new();
    let mut bodies = String::new();
    for f in &reach.fns {
        let def = m.fn_(*f);
        // A panic names this function (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        match FnEmitter::new(&mut cx, *f).emit() {
            Ok((proto, body)) => {
                let _ = writeln!(protos, "{proto};");
                bodies.push_str(&body);
                bodies.push('\n');
            }
            Err(d) => diags.push(Diagnostic::new(
                d.stage,
                d.code,
                if d.span == no_span() { def.span } else { d.span },
                d.message,
            )),
        }
    }
    out.push_str(&protos);
    out.push('\n');
    out.push_str(&bodies);

    // Export wrappers.
    if opts.panic == PanicMode::Poison {
        out.push_str(&crate::export::take_panic(&cx));
    }
    for e in cx.exports.clone() {
        match crate::export::wrappers(&mut cx, &e) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }
    for f in &export_fns {
        match crate::export::fn_wrapper(&mut cx, *f) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }

    if !diags.is_empty() {
        return Err(diags);
    }
    let take_panic = (opts.panic == PanicMode::Poison).then(|| crate::export::take_panic_name(opts));
    Ok(CUnit { source: out, headers, runtime_header: crate::RUNTIME_HEADER.to_string(), flows, fns, take_panic })
}

/// Index into `Module::flows` by qualified name, or by a unique suffix.
pub(crate) fn find_flow(m: &Module, name: &str) -> Option<usize> {
    if let Some(i) = m.flows.iter().position(|f| f.name == name) {
        return Some(i);
    }
    let suffix = format!(".{name}");
    let hits: Vec<usize> =
        m.flows.iter().enumerate().filter(|(_, f)| f.name.ends_with(&suffix)).map(|(i, _)| i).collect();
    if hits.len() == 1 { Some(hits[0]) } else { None }
}

fn contains_bulk(cx: &Cx, ty: &Ty) -> Option<TypeId> {
    match ty {
        Ty::Struct(id) if cx.bulk.contains_key(id) => Some(*id),
        Ty::Array(e, _) => contains_bulk(cx, e),
        Ty::Tuple(ts) => ts.iter().find_map(|t| contains_bulk(cx, t)),
        _ => None,
    }
}

// ------------------------------------------------------------ types

fn type_def(cx: &mut Cx, entry: &Entry) -> R<String> {
    let mut s = String::new();
    match entry {
        Entry::Synth(ty, name) => match ty {
            Ty::Array(e, n) => {
                let et = cx.names.name(e);
                let n = (*n).max(1);
                let _ = writeln!(s, "typedef struct {name} {{ {et} a[{n}]; }} {name};");
            }
            Ty::Tuple(ts) => {
                let _ = write!(s, "typedef struct {name} {{");
                if ts.is_empty() {
                    let _ = write!(s, " uint8_t onsa_empty;");
                }
                for (i, t) in ts.iter().enumerate() {
                    let tn = cx.names.name(t);
                    let _ = write!(s, " {tn} f{i};");
                }
                let _ = writeln!(s, " }} {name};");
            }
            Ty::Span(e) => {
                let et = cx.names.name(e);
                let tag = cx.names.tag(e);
                let _ = writeln!(s, "ONSA_DEFINE_SPAN({tag}, {et})");
                match &**e {
                    Ty::Float(FloatKind::F32) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_F32({tag})");
                    }
                    Ty::Float(FloatKind::F64) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_F64({tag})");
                    }
                    Ty::Int(k) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_INT({tag}, {})", int_tag(*k));
                    }
                    _ => {}
                }
            }
            Ty::FnPtr(_) => return Err(unsupported(no_span(), Feature::FnValues, &[])),
            Ty::Buf(_) => return Err(unsupported(no_span(), Feature::Buf, &[])),
            _ => {}
        },
        Entry::Def(id) => {
            let name = cx.names.defs[id].clone();
            match &cx.m.ty(*id).kind {
                TypeDefKind::Struct { fields } => {
                    let fields = fields.clone();
                    if let Some(hdr) = cx.header_params.get(id).cloned() {
                        let _ = writeln!(s, "typedef {hdr} {name};");
                        return Ok(s);
                    }
                    let tag = cx.names.tags.get(id).cloned().unwrap_or_else(|| name.clone());
                    if let Some(b) = cx.bulk.get(id).cloned() {
                        let _ = write!(s, "typedef struct {} {{", b.struct_name);
                        for (i, (fname, fty)) in fields.iter().enumerate() {
                            if b.fields.contains(&(i as u32)) {
                                let tn = cx.names.name(fty);
                                let _ = write!(s, " {tn} {};", ident(fname));
                            }
                        }
                        let _ = writeln!(s, " }} {};", b.struct_name);
                        let _ = write!(s, "struct {tag} {{ void* bulk;");
                        for (i, (fname, fty)) in fields.iter().enumerate() {
                            if !b.fields.contains(&(i as u32)) {
                                let tn = cx.names.name(fty);
                                let _ = write!(s, " {tn} {};", ident(fname));
                            }
                        }
                        let _ = writeln!(s, " }};");
                    } else {
                        let _ = write!(s, "struct {tag} {{");
                        if fields.is_empty() {
                            let _ = write!(s, " uint8_t onsa_empty;");
                        }
                        for (fname, fty) in &fields {
                            let tn = cx.names.name(fty);
                            let _ = write!(s, " {tn} {};", ident(fname));
                        }
                        let _ = writeln!(s, " }};");
                    }
                    let _ = writeln!(s, "typedef struct {tag} {name};");
                }
                TypeDefKind::Enum { variants } => {
                    let variants = variants.clone();
                    let tag_ty = cx.tag_c(*id);
                    let _ = write!(s, "typedef struct {name} {{ {tag_ty} tag;");
                    if variants.iter().any(|(_, ts)| !ts.is_empty()) {
                        let _ = write!(s, " union {{");
                        for (vname, ts) in &variants {
                            if ts.is_empty() {
                                continue;
                            }
                            let _ = write!(s, " struct {{");
                            for (i, t) in ts.iter().enumerate() {
                                let tn = cx.names.name(t);
                                let _ = write!(s, " {tn} f{i};");
                            }
                            let _ = write!(s, " }} v_{};", ident(vname));
                        }
                        let _ = write!(s, " }} u;");
                    }
                    let _ = writeln!(s, " }} {name};");
                }
                TypeDefKind::Opaque => {
                    return Err(unsupported(no_span(), Feature::OpaqueType, &[&cx.m.ty(*id).name]));
                }
            }
        }
    }
    Ok(s)
}

// ------------------------------------------------------------ constants

/// A C constant expression (static initializer) for a `const` initializer.
fn const_init(cx: &mut Cx, e: &Expr) -> R<String> {
    match &e.kind {
        ExprKind::Lit(l) => Ok(lit(l, &e.ty)),
        ExprKind::Const(c) => {
            let init = cx.m.const_(*c).init.clone();
            const_init(cx, &init)
        }
        ExprKind::Unary(UnOp::Neg, x) => match (&x.kind, &e.ty) {
            (ExprKind::Lit(Lit::Int(v)), Ty::Int(k)) => Ok(int_lit(*k, -*v)),
            (ExprKind::Lit(Lit::F32(v)), _) => Ok(f32_lit(-*v)),
            (ExprKind::Lit(Lit::F64(v)), _) => Ok(f64_lit(-*v)),
            _ => Err(unsupported(e.span, Feature::ConstInitializer, &[])),
        },
        ExprKind::Cast(x) => {
            let inner = const_init(cx, x)?;
            let ty = cx.names.name(&e.ty);
            Ok(format!("(({ty}){inner})"))
        }
        ExprKind::Array(xs) => {
            let parts: Vec<String> = xs.iter().map(|x| const_init(cx, x)).collect::<R<_>>()?;
            Ok(format!("{{ {{ {} }} }}", parts.join(", ")))
        }
        ExprKind::Repeat { elem, n } => {
            let v = const_init(cx, elem)?;
            Ok(format!("{{ {{ {} }} }}", vec![v; *n as usize].join(", ")))
        }
        ExprKind::Tuple(xs) => {
            let parts: Vec<String> =
                xs.iter().enumerate().map(|(i, x)| Ok(format!(".f{i} = {}", const_init(cx, x)?))).collect::<R<_>>()?;
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        ExprKind::Struct { ty, fields } => {
            let names: Vec<String> = cx.fields(*ty).iter().map(|(n, _)| ident(n)).collect();
            if names.is_empty() {
                return Ok("{ 0 }".into());
            }
            let parts: Vec<String> = fields
                .iter()
                .zip(names)
                .map(|(x, n)| Ok(format!(".{n} = {}", const_init(cx, x)?)))
                .collect::<R<_>>()?;
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        ExprKind::Variant { ty, tag, fields } => {
            let vname = ident(&cx.variants(*ty)[*tag as usize].0);
            if fields.is_empty() {
                return Ok(format!("{{ .tag = {tag} }}"));
            }
            let parts: Vec<String> = fields
                .iter()
                .enumerate()
                .map(|(i, x)| Ok(format!(".f{i} = {}", const_init(cx, x)?)))
                .collect::<R<_>>()?;
            Ok(format!("{{ .tag = {tag}, .u = {{ .v_{vname} = {{ {} }} }} }}", parts.join(", ")))
        }
        // The driver inlines the value of a `const` evaluated at build time (T4-5).
        _ => Err(unsupported(e.span, Feature::ConstInitializer, &[])),
    }
}

// ------------------------------------------------------------ functions

/// How a local is reached from C.
#[derive(Debug, Clone)]
struct LocalC {
    /// A complete C lvalue (`x`, `(*s)`, `(*out)`).
    lvalue: String,
}

pub(crate) struct FnEmitter<'a, 'm> {
    cx: &'a mut Cx<'m>,
    f: FnId,
    def: &'m FnDef,
    out: String,
    indent: usize,
    locals: HashMap<LocalId, LocalC>,
    used_names: HashSet<String>,
    temps: u32,
    /// The local returned through `out` without a copy (§12.7 NRVO).
    nrvo: Option<LocalId>,
}

impl<'a, 'm> FnEmitter<'a, 'm> {
    pub fn new(cx: &'a mut Cx<'m>, f: FnId) -> Self {
        let def = cx.m.fn_(f);
        FnEmitter {
            cx,
            f,
            def,
            out: String::new(),
            indent: 1,
            locals: HashMap::new(),
            used_names: HashSet::new(),
            temps: 0,
            nrvo: None,
        }
    }

    /// `(prototype, definition)`.
    pub fn emit(mut self) -> R<(String, String)> {
        let def = self.def;
        let Some(body) = &def.body else {
            return Err(unsupported(def.span, Feature::TargetFn, &[&def.name]));
        };
        // Signature.
        let name = self.cx.fn_name(self.f).to_string();
        let mut params = Vec::new();
        if def.sret {
            let rt = self.cx.names.name(&def.ret);
            params.push(format!("{rt}* out"));
            self.used_names.insert("out".into());
        }
        let mut used: HashSet<LocalId> = HashSet::new();
        walk_block(body, &mut |e| {
            if let ExprKind::Local(l) = &e.kind {
                used.insert(*l);
            }
        });
        let mut pre = String::new();
        for p in &def.params {
            let cname = self.fresh_local(p.local);
            let tn = self.cx.names.name(&p.ty);
            if matches!(p.ty, Ty::Buf(_)) {
                return Err(unsupported(def.span, Feature::Buf, &[]));
            }
            let (decl, lvalue) = match (p.mode, p.ty.is_aggregate(), matches!(p.ty, Ty::Span(_))) {
                (Mode::Inout, _, false) => (format!("{tn}* {cname}"), format!("(*{cname})")),
                (Mode::Borrow, true, false) => (format!("const {tn}* {cname}"), format!("(*{cname})")),
                _ => (format!("{tn} {cname}"), cname.clone()),
            };
            params.push(decl);
            if !used.contains(&p.local) && !assigned_locals(body).contains(&p.local) {
                let _ = writeln!(pre, "  (void){cname};");
            }
            self.locals.insert(p.local, LocalC { lvalue });
        }
        let ret = if def.sret || def.ret == Ty::Unit { "void".to_string() } else { self.cx.names.name(&def.ret) };
        let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
        let proto = format!("ONSA_INLINE {ret} {name}({plist})");

        // NRVO (§12.7): `let s = ...; ...; s` in an sret function builds `s` in `*out`.
        if def.sret
            && !has_return(def)
            && let Some(v) = &body.value
            && let ExprKind::Local(l) = &v.kind
            && body.stmts.iter().any(|s| matches!(&s.kind, StmtKind::Let(x, _) if x == l))
        {
            self.nrvo = Some(*l);
            self.locals.insert(*l, LocalC { lvalue: "(*out)".into() });
        }

        self.out.push_str(&pre);
        for s in &body.stmts {
            self.stmt(s)?;
        }
        if let Some(v) = &body.value {
            if def.sret {
                if self.nrvo.is_none() {
                    self.assign_into("(*out)", &def.ret, v)?;
                }
            } else if def.ret == Ty::Unit {
                self.expr_stmt(v)?;
            } else {
                let e = self.expr(v)?;
                self.line(&format!("return {e};"));
            }
        }
        let mut body_text = String::new();
        let _ = writeln!(body_text, "{proto} {{");
        body_text.push_str(&self.out);
        let _ = writeln!(body_text, "}}");
        Ok((proto, body_text))
    }

    // -------------------------------------------------------- helpers

    fn line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn open(&mut self, s: &str) {
        self.line(s);
        self.indent += 1;
    }

    fn close(&mut self, s: &str) {
        self.indent -= 1;
        self.line(s);
    }

    fn fresh_local(&mut self, l: LocalId) -> String {
        let base = ident(&self.def.locals[l.0 as usize].name);
        let mut name = base.clone();
        if self.used_names.contains(&name) {
            name = format!("{base}_{}", l.0);
        }
        self.used_names.insert(name.clone());
        name
    }

    fn temp(&mut self, ty: &Ty) -> (String, String) {
        self.temps += 1;
        let name = format!("onsa_t{}", self.temps);
        let tn = self.cx.names.name(ty);
        (name, tn)
    }

    fn loc(&self, span: Span) -> String {
        self.cx.loc(span)
    }

    fn local_ty(&self, l: LocalId) -> Ty {
        self.def.locals[l.0 as usize].ty.clone()
    }

    fn place_ty(&self, p: &Place) -> R<Ty> {
        Ok(match p {
            Place::Local(l) => self.local_ty(*l),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                field_ty(self.cx, &bt, *i)?
            }
            Place::Index(b, _) => match self.place_ty(b)? {
                Ty::Array(e, _) | Ty::Span(e) | Ty::Buf(e) => *e,
                _ => return Err(internal("index of a non-sequence place")),
            },
        })
    }

    /// Render a field access on a C lvalue / rvalue of type `base_ty`.
    fn field_access(&mut self, base: &str, base_ty: &Ty, index: u32) -> R<String> {
        match base_ty {
            Ty::Tuple(_) => Ok(format!("{}f{index}", dot(base))),
            Ty::Struct(id) => {
                let (fname, _) =
                    self.cx.fields(*id).get(index as usize).cloned().ok_or_else(|| internal("field index"))?;
                if let Some(b) = self.cx.bulk.get(id).cloned()
                    && b.fields.contains(&index)
                {
                    return Ok(format!("(*({}*){}bulk).{}", b.struct_name, dot(base), ident(&fname)));
                }
                Ok(format!("{}{}", dot(base), ident(&fname)))
            }
            _ => Err(internal("field of a non-record")),
        }
    }

    fn place(&mut self, p: &Place) -> R<String> {
        match p {
            Place::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                self.field_access(&bs, &bt, *i)
            }
            Place::Index(b, i) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                let idx = self.expr(i)?;
                self.index_access(&bs, &bt, &idx, i.span)
            }
        }
    }

    fn index_access(&mut self, base: &str, base_ty: &Ty, idx: &str, span: Span) -> R<String> {
        let loc = self.loc(span);
        match base_ty {
            Ty::Array(_, n) => Ok(format!("{base}.a[onsa_idx({idx}, UINT32_C({n}), {loc})]")),
            Ty::Span(_) => Ok(format!("{base}.ptr[onsa_idx({idx}, {base}.len, {loc})]")),
            Ty::Buf(_) => Err(unsupported(span, Feature::Buf, &[])),
            _ => Err(internal("index of a non-sequence")),
        }
    }

    /// A stable C expression: unaffected by later side effects.
    fn is_stable(s: &str) -> bool {
        s.starts_with("onsa_t")
            || s.starts_with("INT")
            || s.starts_with("UINT")
            || s.starts_with("((int")
            || s.starts_with("((uint")
            || s.starts_with(|c: char| c.is_ascii_digit())
            || s == "true"
            || s == "false"
            || s == "NAN"
            || s == "INFINITY"
            || s == "(-INFINITY)"
    }

    /// Evaluate operands in order; earlier operands are saved in temporaries
    /// as soon as a later operand needs statements.
    fn operands(&mut self, es: &[&Expr]) -> R<Vec<String>> {
        let mut strs: Vec<String> = Vec::new();
        for e in es {
            let mark = self.out.len();
            let s = self.expr(e)?;
            if self.out.len() != mark {
                // Statements were emitted: snapshot the earlier operands before them.
                let mut decls = String::new();
                for (j, prev) in strs.iter_mut().enumerate() {
                    if !Self::is_stable(prev) {
                        let (t, tn) = self.temp(&es[j].ty);
                        for _ in 0..self.indent {
                            decls.push_str("  ");
                        }
                        let _ = writeln!(decls, "{tn} {t} = {prev};");
                        *prev = t;
                    }
                }
                self.out.insert_str(mark, &decls);
            }
            strs.push(s);
        }
        Ok(strs)
    }

    /// The value of `e` in a temporary (or as is when it is a literal, a
    /// temporary, or a plain local: evaluated exactly where it is used).
    fn materialize(&mut self, e: &Expr) -> R<String> {
        let s = self.expr(e)?;
        if Self::is_stable(&s) || is_c_ident(&s) {
            return Ok(s);
        }
        let (t, tn) = self.temp(&e.ty);
        self.line(&format!("{tn} {t} = {s};"));
        Ok(t)
    }

    /// A place-like C string for `e` (an lvalue, or a temporary holding it).
    fn place_like(&mut self, e: &Expr) -> R<String> {
        if let Some(p) = e.as_place() { self.place(&p) } else { self.materialize(e) }
    }

    // -------------------------------------------------------- statements

    fn stmt(&mut self, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                if Some(*l) == self.nrvo {
                    let ty = self.local_ty(*l);
                    return self.assign_into("(*out)", &ty, e);
                }
                let ty = self.local_ty(*l);
                let name = self.fresh_local(*l);
                self.locals.insert(*l, LocalC { lvalue: name.clone() });
                self.declare(&name, &ty, e)
            }
            StmtKind::Assign(p, e) => {
                let ty = self.place_ty(p)?;
                let target = self.place(p)?;
                self.assign_into(&target, &ty, e)
            }
            StmtKind::Expr(e) => self.expr_stmt(e),
            StmtKind::If(c, a, b) => {
                let cs = self.expr(c)?;
                self.open(&format!("if ({cs}) {{"));
                self.block_into(a, None)?;
                if b.stmts.is_empty() && b.value.is_none() {
                    self.close("}");
                } else {
                    self.indent -= 1;
                    self.line("} else {");
                    self.indent += 1;
                    self.block_into(b, None)?;
                    self.close("}");
                }
                Ok(())
            }
            StmtKind::While(c, b) => {
                // The condition may need statements: evaluate it inside the loop.
                let mark = self.out.len();
                let saved_indent = self.indent;
                self.indent += 1;
                let cs = self.expr(c)?;
                let cond_stmts = self.out.split_off(mark);
                self.indent = saved_indent;
                if cond_stmts.is_empty() {
                    self.open(&format!("while ({cs}) {{"));
                } else {
                    self.open("for (;;) {");
                    self.out.push_str(&cond_stmts);
                    self.line(&format!("if (!({cs})) break;"));
                }
                self.block_into(b, None)?;
                self.close("}");
                Ok(())
            }
            StmtKind::ForRange(l, lo, hi, b) => {
                let los = self.materialize(lo)?;
                let his = {
                    let v = self.expr(hi)?;
                    if Self::is_stable(&v) { v } else { self.materialize_str(&v, &hi.ty) }
                };
                let ty = self.local_ty(*l);
                let tn = self.cx.names.name(&ty);
                let name = self.fresh_local(*l);
                self.locals.insert(*l, LocalC { lvalue: name.clone() });
                self.open(&format!("for ({tn} {name} = {los}; {name} < {his}; {name}++) {{"));
                self.block_into(b, None)?;
                self.close("}");
                Ok(())
            }
            StmtKind::Break => {
                self.line("break;");
                Ok(())
            }
            StmtKind::Continue => {
                self.line("continue;");
                Ok(())
            }
            StmtKind::Return(None) => {
                self.line("return;");
                Ok(())
            }
            StmtKind::Return(Some(e)) => {
                if self.def.sret {
                    let ret = self.def.ret.clone();
                    self.assign_into("(*out)", &ret, e)?;
                    self.line("return;");
                } else if self.def.ret == Ty::Unit {
                    self.expr_stmt(e)?;
                    self.line("return;");
                } else {
                    let v = self.expr(e)?;
                    self.line(&format!("return {v};"));
                }
                Ok(())
            }
        }
    }

    /// `T name = e;` or `T name;` followed by construction in place.
    fn declare(&mut self, name: &str, ty: &Ty, e: &Expr) -> R<()> {
        let tn = self.cx.names.name(ty);
        if matches!(ty, Ty::Buf(_)) {
            return Err(unsupported(e.span, Feature::Buf, &[]));
        }
        if needs_construction(e) {
            self.line(&format!("{tn} {name};"));
            self.assign_into(name, ty, e)
        } else {
            let v = self.expr(e)?;
            self.line(&format!("{tn} {name} = {v};"));
            Ok(())
        }
    }

    /// Store the value of `e` into the C lvalue `target` of type `ty`.
    fn assign_into(&mut self, target: &str, ty: &Ty, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Zeroed if ty.is_aggregate() => {
                let bulk = match ty {
                    Ty::Struct(id) => self.cx.bulk.get(id).cloned(),
                    _ => None,
                };
                match bulk {
                    Some(b) if target == "(*out)" => {
                        // The bulk pointer is set by the caller; zero both regions.
                        self.open("{");
                        self.line(&format!("void* onsa_b = {target}.bulk;"));
                        self.line(&format!("memset(&{target}, 0, sizeof {target});"));
                        self.line(&format!("{target}.bulk = onsa_b;"));
                        self.line(&format!("if (onsa_b) memset(onsa_b, 0, sizeof({}));", b.struct_name));
                        self.close("}");
                    }
                    Some(_) => {
                        return Err(unsupported(e.span, Feature::BulkBuild, &[]));
                    }
                    None => self.line(&format!("memset(&{target}, 0, sizeof {target});")),
                }
                Ok(())
            }
            ExprKind::Call { fn_, args } if self.cx.m.fn_(*fn_).sret => {
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                let mut all = vec![format!("&{target}")];
                all.extend(call);
                self.line(&format!("{name}({});", all.join(", ")));
                Ok(())
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                let cs = self.expr(cond)?;
                self.open(&format!("if ({cs}) {{"));
                self.block_into(then, Some((target, ty)))?;
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.block_into(else_, Some((target, ty)))?;
                self.close("}");
                Ok(())
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let s = self.place_like(scrutinee)?;
                self.switch_into(&s, arms, default.as_ref(), Some((target, ty)))
            }
            ExprKind::Block(b) => self.block_into(b, Some((target, ty))),
            ExprKind::Repeat { elem, n } if *n > 8 => {
                let v = self.materialize(elem)?;
                self.open("{");
                self.line("uint32_t onsa_i;");
                self.line(&format!("for (onsa_i = 0; onsa_i < {n}; onsa_i++) {target}.a[onsa_i] = {v};"));
                self.close("}");
                Ok(())
            }
            ExprKind::Panic(m) => {
                self.panic_stmt(*m, e.span);
                Ok(())
            }
            _ => {
                if let (Ty::Struct(id), true) = (ty, self.cx.bulk.contains_key(&struct_id(ty))) {
                    let _ = id;
                    return Err(unsupported(e.span, Feature::BulkCopy, &[]));
                }
                let v = self.expr(e)?;
                self.line(&format!("{target} = {v};"));
                Ok(())
            }
        }
    }

    /// Emit a block's statements; its value goes to `target` (or is dropped).
    fn block_into(&mut self, b: &Block, target: Option<(&str, &Ty)>) -> R<()> {
        for s in &b.stmts {
            self.stmt(s)?;
        }
        if let Some(v) = &b.value
            && !b.diverges()
        {
            match target {
                Some((t, ty)) => self.assign_into(t, ty, v)?,
                None => self.expr_stmt(v)?,
            }
        }
        Ok(())
    }

    fn switch_into(
        &mut self,
        s: &str,
        arms: &[(u32, Block)],
        default: Option<&Block>,
        target: Option<(&str, &Ty)>,
    ) -> R<()> {
        for (i, (tag, b)) in arms.iter().enumerate() {
            let head =
                if i == 0 { format!("if ({s}.tag == {tag}) {{") } else { format!("}} else if ({s}.tag == {tag}) {{") };
            if i == 0 {
                self.open(&head);
            } else {
                self.indent -= 1;
                self.line(&head);
                self.indent += 1;
            }
            self.block_into(b, target)?;
        }
        if let Some(d) = default {
            if arms.is_empty() {
                self.open("{");
            } else {
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
            }
            self.block_into(d, target)?;
        }
        self.close("}");
        Ok(())
    }

    fn panic_stmt(&mut self, m: onsa_core::MsgId, span: Span) {
        let msg = self.cx.msg(&self.cx.m.messages[m.0 as usize]);
        let loc = self.loc(span);
        self.line(&format!("onsa_panic({msg}, {loc});"));
    }

    /// An expression evaluated for its effects only.
    fn expr_stmt(&mut self, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                if def.sret {
                    let ret = def.ret.clone();
                    let (t, tn) = self.temp(&ret);
                    self.line(&format!("{tn} {t};"));
                    return self.assign_into(&t, &ret, e);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                self.line(&format!("{name}({});", call.join(", ")));
                Ok(())
            }
            ExprKind::Prim { .. } => {
                let v = self.expr(e)?;
                if !Self::is_stable(&v) || e.ty != Ty::Unit {
                    self.line(&format!("(void)({v});"));
                }
                Ok(())
            }
            ExprKind::Panic(m) => {
                self.panic_stmt(*m, e.span);
                Ok(())
            }
            ExprKind::Block(b) => self.block_into(b, None),
            ExprKind::IfExpr { cond, then, else_ } => {
                let cs = self.expr(cond)?;
                self.open(&format!("if ({cs}) {{"));
                self.block_into(then, None)?;
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.block_into(else_, None)?;
                self.close("}");
                Ok(())
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let s = self.place_like(scrutinee)?;
                self.switch_into(&s, arms, default.as_ref(), None)
            }
            ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Zeroed => Ok(()),
            _ => {
                let v = self.expr(e)?;
                self.line(&format!("(void)({v});"));
                Ok(())
            }
        }
    }

    /// Argument strings for a call, following the callee's parameter modes.
    fn call_args(&mut self, f: FnId, args: &[onsa_core::Arg]) -> R<Vec<String>> {
        let callee = self.cx.m.fn_(f);
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        let mut out = Vec::new();
        // Pointer-passed arguments must be places: evaluate them as such.
        let mut strs = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let p = &callee.params[i];
            let by_ptr = matches!(p.mode, Mode::Inout) && !matches!(p.ty, Ty::Span(_))
                || (matches!(p.mode, Mode::Borrow) && p.ty.is_aggregate());
            if by_ptr {
                let s = self.place_like(&a.expr)?;
                strs.push((s, true));
            } else {
                strs.push((String::new(), false));
            }
        }
        // Value arguments in order (place arguments are stable lvalues).
        let value_exprs: Vec<&Expr> = exprs.iter().enumerate().filter(|(i, _)| !strs[*i].1).map(|(_, e)| *e).collect();
        let values = self.operands(&value_exprs)?;
        let mut vi = 0;
        for (s, by_ptr) in strs {
            if by_ptr {
                out.push(format!("&{s}"));
            } else {
                out.push(values[vi].clone());
                vi += 1;
            }
        }
        Ok(out)
    }

    // -------------------------------------------------------- expressions

    fn expr(&mut self, e: &Expr) -> R<String> {
        match &e.kind {
            ExprKind::Lit(l) => Ok(lit(l, &e.ty)),
            ExprKind::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            ExprKind::Const(c) => Ok(self.cx.const_names.get(c).cloned().ok_or_else(|| internal("unknown const"))?),
            ExprKind::Zeroed => {
                if let Some(z) = zero_scalar(&e.ty) {
                    return Ok(z);
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("memset(&{t}, 0, sizeof {t});"));
                Ok(t)
            }
            ExprKind::Unary(op, x) => {
                let v = self.expr(x)?;
                Ok(match (op, &e.ty) {
                    (UnOp::Neg, Ty::Int(k)) => format!("onsa_neg_{}({v}, {})", int_tag(*k), self.loc(e.span)),
                    (UnOp::Neg, Ty::Float(FloatKind::F32)) => format!("(float)(-{v})"),
                    (UnOp::Neg, _) => format!("(-{v})"),
                    (UnOp::Not, Ty::Bool) => format!("(!{v})"),
                    (UnOp::Not, Ty::Int(k)) => format!("(({})~{v})", crate::names::int_c(*k)),
                    (UnOp::Not, _) => format!("(!{v})"),
                })
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                let ops = self.operands(&[lhs, rhs])?;
                let (a, b) = (&ops[0], &ops[1]);
                let loc = self.loc(e.span);
                Ok(match &e.ty {
                    Ty::Float(k) => {
                        let s = match op {
                            BinOp::Add => format!("{a} + {b}"),
                            BinOp::Sub => format!("{a} - {b}"),
                            BinOp::Mul => format!("{a} * {b}"),
                            BinOp::Div => format!("{a} / {b}"),
                            BinOp::Rem => return Ok(format!("onsa_fmod_{}({a}, {b})", float_tag(*k))),
                            _ => return Err(internal("bitwise operator on a float")),
                        };
                        match k {
                            FloatKind::F32 => format!("(float)({s})"),
                            FloatKind::F64 => format!("({s})"),
                        }
                    }
                    Ty::Int(k) => {
                        let t = int_tag(*k);
                        let c = crate::names::int_c(*k);
                        match (op, overflow) {
                            (BinOp::Add, Overflow::Checked) => format!("onsa_add_{t}({a}, {b}, {loc})"),
                            (BinOp::Sub, Overflow::Checked) => format!("onsa_sub_{t}({a}, {b}, {loc})"),
                            (BinOp::Mul, Overflow::Checked) => format!("onsa_mul_{t}({a}, {b}, {loc})"),
                            (BinOp::Add, Overflow::Wrap) => format!("onsa_wadd_{t}({a}, {b})"),
                            (BinOp::Sub, Overflow::Wrap) => format!("onsa_wsub_{t}({a}, {b})"),
                            (BinOp::Mul, Overflow::Wrap) => format!("onsa_wmul_{t}({a}, {b})"),
                            (BinOp::Add, Overflow::Sat) => format!("onsa_sadd_{t}({a}, {b})"),
                            (BinOp::Sub, Overflow::Sat) => format!("onsa_ssub_{t}({a}, {b})"),
                            (BinOp::Mul, Overflow::Sat) => format!("onsa_smul_{t}({a}, {b})"),
                            (BinOp::Div, _) => format!("onsa_div_{t}({a}, {b}, {loc})"),
                            (BinOp::Rem, _) => format!("onsa_rem_{t}({a}, {b}, {loc})"),
                            (BinOp::BitAnd, _) => format!("(({c})({a} & {b}))"),
                            (BinOp::BitOr, _) => format!("(({c})({a} | {b}))"),
                            (BinOp::BitXor, _) => format!("(({c})({a} ^ {b}))"),
                            (BinOp::Shl, _) => format!("onsa_shl_{t}({a}, {b}, {loc})"),
                            (BinOp::Shr, _) => format!("onsa_shr_{t}({a}, {b}, {loc})"),
                        }
                    }
                    Ty::Bool => match op {
                        BinOp::BitAnd => format!("((bool)({a} & {b}))"),
                        BinOp::BitOr => format!("((bool)({a} | {b}))"),
                        BinOp::BitXor => format!("((bool)({a} ^ {b}))"),
                        _ => return Err(internal("arithmetic on Bool")),
                    },
                    _ => return Err(internal("binary operator on a non-scalar")),
                })
            }
            ExprKind::Cmp { op, lhs, rhs } => {
                let ops = self.operands(&[lhs, rhs])?;
                let c = match op {
                    CmpOp::Eq => "==",
                    CmpOp::Ne => "!=",
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                    CmpOp::Gt => ">",
                    CmpOp::Ge => ">=",
                };
                Ok(format!("({} {c} {})", ops[0], ops[1]))
            }
            ExprKind::Logic { op, lhs, rhs } => {
                let a = self.expr(lhs)?;
                let mark = self.out.len();
                let saved = self.indent;
                self.indent += 1;
                let b = self.expr(rhs)?;
                let rhs_stmts = self.out.split_off(mark);
                self.indent = saved;
                let c = match op {
                    LogicOp::And => "&&",
                    LogicOp::Or => "||",
                };
                if rhs_stmts.is_empty() {
                    return Ok(format!("({a} {c} {b})"));
                }
                // Short-circuit with statements on the right-hand side.
                let (t, _) = self.temp(&Ty::Bool);
                self.line(&format!("bool {t} = {a};"));
                let test = if matches!(op, LogicOp::And) { t.clone() } else { format!("!{t}") };
                self.open(&format!("if ({test}) {{"));
                self.out.push_str(&rhs_stmts);
                self.line(&format!("{t} = {b};"));
                self.close("}");
                Ok(t)
            }
            ExprKind::Cast(x) => {
                let v = self.expr(x)?;
                let tn = self.cx.names.name(&e.ty);
                Ok(format!("(({tn}){v})"))
            }
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                let ret = def.ret.clone();
                if def.sret {
                    let (t, tn) = self.temp(&ret);
                    self.line(&format!("{tn} {t};"));
                    self.assign_into(&t, &ret, e)?;
                    return Ok(t);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                if ret == Ty::Unit {
                    self.line(&format!("{name}({});", call.join(", ")));
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(&ret);
                self.line(&format!("{tn} {t} = {name}({});", call.join(", ")));
                Ok(t)
            }
            ExprKind::Prim { prim, args } => self.prim(prim, args, e),
            ExprKind::Field { base, index } => {
                let bs = self.place_like(base)?;
                let bt = base.ty.clone();
                self.field_access(&bs, &bt, *index)
            }
            ExprKind::Index { base, index } => {
                let bs = self.place_like(base)?;
                let idx = self.materialize(index)?;
                let bt = base.ty.clone();
                self.index_access(&bs, &bt, &idx, e.span)
            }
            ExprKind::SpanOf(x) => {
                let xs = self.place_like(x)?;
                match &x.ty {
                    Ty::Array(el, n) => {
                        let tag = self.cx.names.tag(el);
                        let _ = self.cx.names.name(&e.ty);
                        Ok(format!("onsa_span_{tag}_of({xs}.a, UINT32_C({n}))"))
                    }
                    Ty::Span(_) => Ok(xs),
                    Ty::Buf(_) => Err(unsupported(e.span, Feature::Buf, &[])),
                    _ => Err(internal("span of a non-sequence")),
                }
            }
            ExprKind::Struct { ty, fields } => {
                let tn = self.cx.names.name(&e.ty);
                let names: Vec<String> = self.cx.fields(*ty).iter().map(|(n, _)| ident(n)).collect();
                if fields.is_empty() {
                    return Ok(format!("(({tn}){{ .onsa_empty = 0 }})"));
                }
                let refs: Vec<&Expr> = fields.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().zip(names).map(|(v, n)| format!(".{n} = {v}")).collect();
                Ok(format!("(({tn}){{ {} }})", parts.join(", ")))
            }
            ExprKind::Variant { ty, tag, fields } => {
                let tn = self.cx.names.name(&e.ty);
                let vname = ident(&self.cx.variants(*ty)[*tag as usize].0);
                if fields.is_empty() {
                    return Ok(format!("(({tn}){{ .tag = {tag} }})"));
                }
                let refs: Vec<&Expr> = fields.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                Ok(format!("(({tn}){{ .tag = {tag}, .u = {{ .v_{vname} = {{ {} }} }} }})", parts.join(", ")))
            }
            ExprKind::Array(xs) => {
                let tn = self.cx.names.name(&e.ty);
                if xs.is_empty() {
                    return Ok(format!("(({tn}){{ {{ 0 }} }})"));
                }
                let refs: Vec<&Expr> = xs.iter().collect();
                let vs = self.operands(&refs)?;
                Ok(format!("(({tn}){{ {{ {} }} }})", vs.join(", ")))
            }
            ExprKind::Repeat { elem, n } => {
                let tn = self.cx.names.name(&e.ty);
                let v = self.materialize(elem)?;
                if *n <= 8 {
                    return Ok(format!("(({tn}){{ {{ {} }} }})", vec![v; *n as usize].join(", ")));
                }
                let (t, _) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.open("{");
                self.line("uint32_t onsa_i;");
                self.line(&format!("for (onsa_i = 0; onsa_i < {n}; onsa_i++) {t}.a[onsa_i] = {v};"));
                self.close("}");
                Ok(t)
            }
            ExprKind::Tuple(xs) => {
                let tn = self.cx.names.name(&e.ty);
                if xs.is_empty() {
                    return Ok("((onsa_unit){0})".into());
                }
                let refs: Vec<&Expr> = xs.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                Ok(format!("(({tn}){{ {} }})", parts.join(", ")))
            }
            ExprKind::Tag(x) => {
                let xs = self.place_like(x)?;
                Ok(format!("{xs}.tag"))
            }
            ExprKind::Payload { base, tag, index } => {
                let bs = self.place_like(base)?;
                let Ty::Enum(id) = &base.ty else { return Err(internal("payload of a non-enum")) };
                let vname = ident(&self.cx.variants(*id)[*tag as usize].0);
                Ok(format!("{bs}.u.v_{vname}.f{index}"))
            }
            ExprKind::IfExpr { .. } | ExprKind::Switch { .. } => {
                if e.ty == Ty::Unit {
                    self.expr_stmt(e)?;
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                let ty = e.ty.clone();
                self.assign_into(&t, &ty, e)?;
                Ok(t)
            }
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    self.stmt(s)?;
                }
                match &b.value {
                    Some(v) if !b.diverges() => self.expr(v),
                    _ => Ok("((onsa_unit){0})".into()),
                }
            }
            ExprKind::Panic(m) => {
                self.panic_stmt(*m, e.span);
                if let Some(z) = zero_scalar(&e.ty) {
                    return Ok(z);
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("memset(&{t}, 0, sizeof {t});"));
                Ok(t)
            }
        }
    }

    fn prim(&mut self, prim: &Prim, args: &[onsa_core::Arg], e: &Expr) -> R<String> {
        let loc = self.loc(e.span);
        let refs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        match prim {
            Prim::Math(f, k) => {
                let vs = self.operands(&refs)?;
                let (a, b) = (vs[0].clone(), vs.get(1).cloned().unwrap_or_default());
                let sfx = match k {
                    FloatKind::F32 => "f",
                    FloatKind::F64 => "",
                };
                let t = float_tag(*k);
                Ok(match f {
                    MathFn::Exp => format!("exp{sfx}({a})"),
                    MathFn::Exp2 => format!("exp2{sfx}({a})"),
                    MathFn::Log => format!("log{sfx}({a})"),
                    MathFn::Log2 => format!("log2{sfx}({a})"),
                    MathFn::Sin => format!("sin{sfx}({a})"),
                    MathFn::Cos => format!("cos{sfx}({a})"),
                    MathFn::Tan => format!("tan{sfx}({a})"),
                    MathFn::Tanh => format!("tanh{sfx}({a})"),
                    MathFn::Pow => format!("pow{sfx}({a}, {b})"),
                    MathFn::Sqrt => format!("sqrt{sfx}({a})"),
                    MathFn::Floor => format!("floor{sfx}({a})"),
                    MathFn::Ceil => format!("ceil{sfx}({a})"),
                    MathFn::Trunc => format!("trunc{sfx}({a})"),
                    MathFn::Round => format!("onsa_round_{t}({a})"),
                    MathFn::Abs => format!("fabs{sfx}({a})"),
                    MathFn::Min => format!("onsa_fmin_{t}({a}, {b})"),
                    MathFn::Max => format!("onsa_fmax_{t}({a}, {b})"),
                    MathFn::Fmod => format!("onsa_fmod_{t}({a}, {b})"),
                })
            }
            Prim::IntAbs(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_abs_{}({}, {loc})", int_tag(*k), vs[0]))
            }
            Prim::IntMin(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_min_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IntMax(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_max_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::Narrow { from, to } => {
                let vs = self.operands(&refs)?;
                let x = self.materialize_str(&vs[0], &Ty::Int(*from));
                let Ty::Enum(id) = &e.ty else { return Err(internal("narrow result")) };
                let (t, tn) = self.temp(&e.ty);
                let (lo, hi) = int_range(*to);
                let c = crate::names::int_c(*to);
                let some = ident(&self.cx.variants(*id)[1].0);
                self.line(&format!("{tn} {t};"));
                self.open(&format!("if ({x} >= {lo} && {x} <= {hi}) {{"));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = ({c}){x} }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::IntToFloat { to, .. } | Prim::FloatToFloat { to, .. } => {
                let vs = self.operands(&refs)?;
                Ok(format!("(({}){})", crate::names::float_c(*to), vs[0]))
            }
            Prim::TruncToInt { from, to, sat } => {
                let vs = self.operands(&refs)?;
                let (f, t) = (float_tag(*from), int_tag(*to));
                Ok(if *sat {
                    format!("onsa_trunc_sat_{t}_{f}({})", vs[0])
                } else {
                    format!("onsa_trunc_{t}_{f}({}, {loc})", vs[0])
                })
            }
            Prim::ToBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::FromBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_from_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::Checked(op, k) => {
                let vs = self.operands(&refs)?;
                let Ty::Enum(id) = &e.ty else { return Err(internal("checked result")) };
                let (t, tn) = self.temp(&e.ty);
                let (r, rc) = self.temp(&Ty::Int(*k));
                let some = ident(&self.cx.variants(*id)[1].0);
                let opn = match op {
                    CheckedOp::Add => "cadd",
                    CheckedOp::Sub => "csub",
                    CheckedOp::Mul => "cmul",
                    CheckedOp::Div => "cdiv",
                };
                self.line(&format!("{tn} {t};"));
                self.line(&format!("{rc} {r};"));
                self.open(&format!("if (onsa_{opn}_{}({}, {}, &{r})) {{", int_tag(*k), vs[0], vs[1]));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = {r} }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::DivEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_div_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::RemEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_rem_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IsNan(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isnan({}))", vs[0]))
            }
            Prim::IsFinite(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isfinite({}))", vs[0]))
            }
            Prim::Len => {
                let s = self.place_like(&args[0].expr)?;
                match &args[0].expr.ty {
                    Ty::Span(_) => Ok(format!("{s}.len")),
                    Ty::Array(_, n) => Ok(format!("UINT32_C({n})")),
                    _ => Err(unsupported(e.span, Feature::Buf, &[])),
                }
            }
            Prim::Slice => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                Ok(format!("onsa_slice_{tag}({s}, {}, {}, {loc})", vs[0], vs[1]))
            }
            Prim::Get => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let i = self.materialize_str(&vs[0], &Ty::u32());
                let Ty::Enum(id) = &e.ty else { return Err(internal("get result")) };
                let some = ident(&self.cx.variants(*id)[1].0);
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.open(&format!("if ({i} < {s}.len) {{"));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = {s}.ptr[{i}] }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::Fill => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                self.line(&format!("onsa_fill_{tag}({s}, {});", vs[0]));
                Ok("((onsa_unit){0})".into())
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let d = self.span_arg(&args[0].expr)?;
                let s = self.span_arg(&args[1].expr)?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                let f = if matches!(prim, Prim::AddFrom) { "add_from" } else { "copy_from" };
                self.line(&format!("onsa_{f}_{tag}({d}, {s}, {loc});"));
                Ok("((onsa_unit){0})".into())
            }
            Prim::BufZeroed => Err(unsupported(e.span, Feature::Buf, &[])),
            Prim::Std(name) => Err(unsupported(e.span, Feature::StdFn, &[name])),
        }
    }

    fn materialize_str(&mut self, s: &str, ty: &Ty) -> String {
        if Self::is_stable(s) {
            return s.to_string();
        }
        let (t, tn) = self.temp(ty);
        self.line(&format!("{tn} {t} = {s};"));
        t
    }

    /// A span-typed argument as a C value (arrays become spans over the place).
    fn span_arg(&mut self, e: &Expr) -> R<String> {
        match &e.ty {
            Ty::Span(_) => self.place_like(e),
            Ty::Array(el, n) => {
                let p = self.place_like(e)?;
                let tag = self.cx.names.tag(el);
                let _ = self.cx.names.name(&Ty::Span(el.clone()));
                Ok(format!("onsa_span_{tag}_of({p}.a, UINT32_C({n}))"))
            }
            _ => Err(unsupported(e.span, Feature::Buf, &[])),
        }
    }

    fn span_tag(&mut self, ty: &Ty) -> R<String> {
        match ty {
            Ty::Span(el) | Ty::Array(el, _) => Ok(self.cx.names.tag(el)),
            _ => Err(unsupported(no_span(), Feature::Buf, &[])),
        }
    }
}

/// `base.` — or `p->` when `base` is a dereferenced pointer parameter `(*p)`.
fn dot(base: &str) -> String {
    if let Some(inner) = base.strip_prefix("(*").and_then(|r| r.strip_suffix(')'))
        && inner.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return format!("{inner}->");
    }
    format!("{base}.")
}

/// Locals that are assignment targets (roots of `Assign` places).
fn assigned_locals(b: &Block) -> HashSet<LocalId> {
    let mut out = HashSet::new();
    fn block(b: &Block, out: &mut HashSet<LocalId>) {
        for s in &b.stmts {
            stmt(s, out);
        }
        if let Some(v) = &b.value {
            expr(v, out);
        }
    }
    fn stmt(s: &Stmt, out: &mut HashSet<LocalId>) {
        match &s.kind {
            StmtKind::Assign(p, e) => {
                out.insert(p.root());
                expr(e, out);
            }
            StmtKind::Let(_, e) | StmtKind::Expr(e) => expr(e, out),
            StmtKind::If(c, a, b) => {
                expr(c, out);
                block(a, out);
                block(b, out);
            }
            StmtKind::While(c, b) => {
                expr(c, out);
                block(b, out);
            }
            StmtKind::ForRange(_, lo, hi, b) => {
                expr(lo, out);
                expr(hi, out);
                block(b, out);
            }
            StmtKind::Return(Some(e)) => expr(e, out),
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
        }
    }
    fn expr(e: &Expr, out: &mut HashSet<LocalId>) {
        crate::reach::walk_expr(e, &mut |x| match &x.kind {
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    stmt(s, out);
                }
            }
            ExprKind::IfExpr { then, else_, .. } => {
                for s in then.stmts.iter().chain(&else_.stmts) {
                    stmt(s, out);
                }
            }
            ExprKind::Switch { arms, default, .. } => {
                for (_, b) in arms {
                    for s in &b.stmts {
                        stmt(s, out);
                    }
                }
                if let Some(b) = default {
                    for s in &b.stmts {
                        stmt(s, out);
                    }
                }
            }
            _ => {}
        });
    }
    block(b, &mut out);
    out
}

fn is_c_ident(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn struct_id(ty: &Ty) -> TypeId {
    match ty {
        Ty::Struct(id) => *id,
        _ => TypeId(u32::MAX),
    }
}

/// Expressions that are built in place rather than assigned from a C expression.
fn needs_construction(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Zeroed => e.ty.is_aggregate(),
        ExprKind::Call { .. }
        | ExprKind::IfExpr { .. }
        | ExprKind::Switch { .. }
        | ExprKind::Block(_)
        | ExprKind::Panic(_) => true,
        ExprKind::Repeat { n, .. } => *n > 8,
        _ => false,
    }
}

pub(crate) fn field_ty(cx: &Cx, base: &Ty, index: u32) -> R<Ty> {
    match base {
        Ty::Tuple(ts) => ts.get(index as usize).cloned().ok_or_else(|| internal("tuple index")),
        Ty::Struct(id) => {
            cx.fields(*id).get(index as usize).map(|(_, t)| t.clone()).ok_or_else(|| internal("field index"))
        }
        _ => Err(internal("field of a non-record")),
    }
}

pub(crate) fn int_range(k: IntKind) -> (String, String) {
    match k {
        IntKind::I8 => ("INT8_MIN".into(), "INT8_MAX".into()),
        IntKind::I16 => ("INT16_MIN".into(), "INT16_MAX".into()),
        IntKind::I32 => ("INT32_MIN".into(), "INT32_MAX".into()),
        IntKind::I64 => ("INT64_MIN".into(), "INT64_MAX".into()),
        IntKind::U8 => ("0".into(), "UINT8_MAX".into()),
        IntKind::U16 => ("0".into(), "UINT16_MAX".into()),
        IntKind::U32 => ("0".into(), "UINT32_MAX".into()),
        IntKind::U64 => ("0".into(), "UINT64_MAX".into()),
    }
}

/// A state the C backend cannot be in: an internal error (S-67), not E0200.
/// The driver's guard reports it with the function being emitted.
pub(crate) fn internal(msg: &str) -> Diagnostic {
    onsa_diag::internal::bug(None, format!("internal C backend error: {msg}"))
}
