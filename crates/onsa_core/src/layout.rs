//! Layout of Core types (spec §12.4, T3-6): declaration order, natural
//! alignment, no reordering. Enums: the smallest tag of `U8` / `U16` / `U32`,
//! then the largest variant. The same rules as `onsa_sema::layout`, applied
//! to Core types so that generated flow states can be laid out.

use crate::ir::{FloatKind, IntKind, Module, Ty, TypeDefKind, TypeId};

/// Pointer width of the reference host (`Span` = pointer + length). Targets
/// with 32-bit pointers pass their width through [`size_align_for`] /
/// [`flow_layout_for`] (T4-5).
pub const PTR_SIZE: u32 = 8;

fn round_up(x: u32, align: u32) -> u32 {
    if align == 0 { x } else { x.div_ceil(align) * align }
}

/// `(size, align)` of a type on the reference host (8-byte pointers).
pub fn size_align(m: &Module, ty: &Ty) -> (u32, u32) {
    size_align_for(m, ty, PTR_SIZE)
}

/// `(size, align)` of a type for a target whose pointers are `ptr` bytes wide.
pub fn size_align_for(m: &Module, ty: &Ty, ptr: u32) -> (u32, u32) {
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
            let (s, a) = size_align_for(m, e, ptr);
            (s * n, a)
        }
        Ty::Tuple(ts) => {
            let r = record_for(m, ts.iter().map(|t| ("".to_string(), t.clone())).collect::<Vec<_>>().as_slice(), ptr);
            (r.size, r.align)
        }
        Ty::Struct(id) => match &m.ty(*id).kind {
            TypeDefKind::Struct { fields } => {
                let r = record_for(m, fields, ptr);
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
                    let r = record_for(
                        m,
                        tys.iter().map(|t| ("".to_string(), t.clone())).collect::<Vec<_>>().as_slice(),
                        ptr,
                    );
                    payload_size = payload_size.max(r.size);
                    payload_align = payload_align.max(r.align);
                }
                let align = tag.max(payload_align);
                (round_up(round_up(tag, payload_align) + payload_size, align), align)
            }
            _ => (0, 1),
        },
        Ty::Span(_) => (2 * ptr, ptr),
        Ty::FnPtr(_) | Ty::Buf(_) => (ptr, ptr),
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
    record_for(m, fields, PTR_SIZE)
}

pub fn record_for(m: &Module, fields: &[(String, Ty)], ptr: u32) -> RecordLayout {
    let mut size = 0u32;
    let mut align = 1u32;
    let mut out = Vec::new();
    for (name, ty) in fields {
        let (s, a) = size_align_for(m, ty, ptr);
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

impl FlowLayout {
    /// End of the last fast field before the trailing padding.
    pub fn fast_end(&self) -> u32 {
        self.fast_fields.iter().map(|f| f.offset + f.size).max().unwrap_or(0)
    }
}

pub fn flow_layout(m: &Module, state: TypeId, bulk_threshold: Option<u32>) -> FlowLayout {
    flow_layout_for(m, state, bulk_threshold, PTR_SIZE)
}

/// [`flow_layout`] for a target whose pointers are `ptr` bytes wide (the bulk
/// pointer slot and any `Span` in the state follow it).
pub fn flow_layout_for(m: &Module, state: TypeId, bulk_threshold: Option<u32>, ptr: u32) -> FlowLayout {
    let fields = match &m.ty(state).kind {
        TypeDefKind::Struct { fields } => fields.clone(),
        _ => Vec::new(),
    };
    let is_bulk = |ty: &Ty| -> bool {
        match (bulk_threshold, ty) {
            (Some(t), Ty::Array(..)) => size_align_for(m, ty, ptr).0 >= t,
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
    let f = record_for(m, &fast, ptr);
    let b = record_for(m, &bulk, ptr);
    FlowLayout {
        fast_fields: f.fields,
        bulk_fields: b.fields,
        size: f.size,
        bulk_size: b.size,
        align: f.align.max(if bulk.is_empty() { 1 } else { b.align }),
    }
}
