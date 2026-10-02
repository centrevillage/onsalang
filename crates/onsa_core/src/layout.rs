//! Layout of Core types (spec §12.4, T3-6): declaration order, natural
//! alignment, no reordering. Enums: the smallest tag of `U8` / `U16` / `U32`,
//! then the largest variant. The same rules as `onsa_sema::layout`, applied
//! to Core types so that generated flow states can be laid out.

use crate::ir::{FloatKind, IntKind, Module, Ty, TypeDefKind, TypeId};

/// Pointer width of the reference host (`Span` = pointer + length).
pub const PTR_SIZE: u32 = 8;

fn round_up(x: u32, align: u32) -> u32 {
    if align == 0 { x } else { x.div_ceil(align) * align }
}

/// `(size, align)` of a type.
pub fn size_align(m: &Module, ty: &Ty) -> (u32, u32) {
    match ty {
        Ty::Int(k) => {
            let n = match k {
                IntKind::I8 | IntKind::U8 => 1,
                IntKind::I16 | IntKind::U16 => 2,
                IntKind::I32 | IntKind::U32 => 4,
                IntKind::I64 | IntKind::U64 => 8,
            };
            (n, n)
        }
        Ty::Float(FloatKind::F32) => (4, 4),
        Ty::Float(FloatKind::F64) => (8, 8),
        Ty::Bool => (1, 1),
        Ty::Char => (4, 4),
        Ty::Unit => (0, 1),
        Ty::Array(e, n) => {
            let (s, a) = size_align(m, e);
            (s * n, a)
        }
        Ty::Tuple(ts) => {
            let r = record(m, ts.iter().map(|t| ("".to_string(), t.clone())).collect::<Vec<_>>().as_slice());
            (r.size, r.align)
        }
        Ty::Struct(id) => match &m.ty(*id).kind {
            TypeDefKind::Struct { fields } => {
                let r = record(m, fields);
                (r.size, r.align)
            }
            _ => (0, 1),
        },
        Ty::Enum(id) => match &m.ty(*id).kind {
            TypeDefKind::Enum { variants } => {
                let tag = match variants.len() {
                    0..=256 => 1,
                    257..=65536 => 2,
                    _ => 4,
                };
                let mut payload_size = 0;
                let mut payload_align = 1;
                for (_, tys) in variants {
                    let r = record(m, tys.iter().map(|t| ("".to_string(), t.clone())).collect::<Vec<_>>().as_slice());
                    payload_size = payload_size.max(r.size);
                    payload_align = payload_align.max(r.align);
                }
                let align = tag.max(payload_align);
                (round_up(round_up(tag, payload_align) + payload_size, align), align)
            }
            _ => (0, 1),
        },
        Ty::Span(_) => (2 * PTR_SIZE, PTR_SIZE),
        Ty::FnPtr(_) | Ty::Buf(_) => (PTR_SIZE, PTR_SIZE),
    }
}

/// One field placed in a region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldLayout {
    pub name: String,
    pub offset: u32,
    pub size: u32,
    pub align: u32,
}

/// A record laid out in declaration order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordLayout {
    pub fields: Vec<FieldLayout>,
    pub size: u32,
    pub align: u32,
}

pub fn record(m: &Module, fields: &[(String, Ty)]) -> RecordLayout {
    let mut size = 0u32;
    let mut align = 1u32;
    let mut out = Vec::new();
    for (name, ty) in fields {
        let (s, a) = size_align(m, ty);
        size = round_up(size, a);
        out.push(FieldLayout { name: name.clone(), offset: size, size: s, align: a });
        size += s;
        align = align.max(a);
    }
    RecordLayout { fields: out, size: round_up(size, align), align }
}

/// Fast / bulk placement of a flow state (spec §12.4, S-05).
///
/// Top-level array fields whose size is at least `bulk_threshold` go to the
/// bulk region, in declaration order; everything else stays in the fast
/// region, which then starts with the bulk pointer (`PTR_SIZE`, at offset
/// 0). `size` / `bulk_size` / `align` are the `SIZE` / `BULK_SIZE` / `ALIGN`
/// of the generated header. Sub-instance states are placed whole in the
/// fast region (their own large arrays are not split out; M4 may refine).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlowLayout {
    pub fast_fields: Vec<FieldLayout>,
    pub bulk_fields: Vec<FieldLayout>,
    pub size: u32,
    pub bulk_size: u32,
    pub align: u32,
}

pub fn flow_layout(m: &Module, state: TypeId, bulk_threshold: Option<u32>) -> FlowLayout {
    let fields = match &m.ty(state).kind {
        TypeDefKind::Struct { fields } => fields.clone(),
        _ => Vec::new(),
    };
    let is_bulk = |ty: &Ty| -> bool {
        match (bulk_threshold, ty) {
            (Some(t), Ty::Array(..)) => size_align(m, ty).0 >= t,
            _ => false,
        }
    };
    let bulk: Vec<(String, Ty)> = fields.iter().filter(|(_, t)| is_bulk(t)).cloned().collect();
    let mut fast: Vec<(String, Ty)> = Vec::new();
    if !bulk.is_empty() {
        // The bulk pointer: modelled as a pointer-sized, pointer-aligned slot.
        fast.push(("bulk".into(), Ty::Buf(Box::new(Ty::Int(IntKind::U8)))));
    }
    fast.extend(fields.iter().filter(|(_, t)| !is_bulk(t)).cloned());
    let f = record(m, &fast);
    let b = record(m, &bulk);
    FlowLayout {
        fast_fields: f.fields,
        bulk_fields: b.fields,
        size: f.size,
        bulk_size: b.size,
        align: f.align.max(if bulk.is_empty() { 1 } else { b.align }),
    }
}
