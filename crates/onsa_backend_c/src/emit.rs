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
//!
//! This file holds what the parts share; the parts are `unit` (the order of
//! the unit), `types`, `consts` and `fns` (the function bodies).

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use onsa_core::prim::{CheckedOp, MathFn, Prim};
use onsa_core::walk::{has_return, walk_block};
use onsa_core::{
    BinOp, Block, CmpOp, ConstId, Expr, ExprKind, FloatKind, FnDef, FnId, IntKind, Lit, LocalId, LogicOp, Mode, Module,
    Overflow, Place, Stmt, StmtKind, Ty, TypeDefKind, TypeId, UnOp,
};
use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::names::{Entry, TypeNames, float_tag, ident, int_tag, qualified};
use crate::{CUnit, EmitOptions, PanicMode, no_span, unsupported};

mod consts;
mod fns;
mod types;
mod unit;

use consts::const_init;
pub(crate) use fns::internal;
use fns::{FnEmitter, GUARDED_SUFFIX};
use types::type_def;
pub(crate) use unit::{emit_unit, export_roots};

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
    /// The guarded twins of the functions a `poison` wrapper calls (R-167).
    pub guarded_names: HashMap<FnId, String>,
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

    /// What a `poison` wrapper calls after its `setjmp` for `f`: its guarded
    /// twin (R-167); the function itself outside `poison`.
    pub fn after_setjmp(&self, f: FnId) -> &str {
        self.guarded_names.get(&f).map_or_else(|| self.fn_name(f), String::as_str)
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
