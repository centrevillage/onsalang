//! Layout of Core types (spec §12.4, T3-6), and what else is known of a type
//! from its parts ([`TyFacts`]), read from a table filled once for each type.

use onsa_diag::internal::bug;

use crate::dump::type_name;
use crate::ir::{CTy, FloatKind, IntKind, Module, TyKind, TypeDefKind, TypeId};

/// Pointer width of the reference host (`Span` = pointer + length), the one
/// of a module made with no other ([`Facts::default`]).
pub const PTR_SIZE: u32 = 8;

// The sizes saturate at `u32::MAX`: a type larger than `U32` holds is E0409
// (§4.1), which the layout pass reports (W9-04); until then no sum overflows.
fn round_up(x: u32, align: u32) -> u32 {
    if align == 0 { x } else { x.div_ceil(align).saturating_mul(align) }
}

/// What is known of a value of a type from the values it holds, once for each
/// type ([`Module::fill_facts`]). A fact more is a field and a line of each
/// arm of [`combine`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TyFacts {
    pub size: u32,
    pub align: u32,
    /// The value holds a view: a `Span`, or an aggregate with one in an
    /// element, a field or a payload (the element of a `Buf` is not one).
    pub views: bool,
}

/// The facts of the types of a module, by id, at the pointer width of the
/// target it is lowered for.
#[derive(Debug, Clone)]
pub struct Facts {
    ptr: u32,
    of: Vec<Slot>,
}

#[derive(Debug, Clone, Copy)]
enum Slot {
    Empty,
    /// On the stack of [`Module::fill_facts`]: its parts are being filled.
    Open,
    Done(TyFacts),
}

impl Default for Facts {
    fn default() -> Self {
        Facts::new(PTR_SIZE)
    }
}

impl Facts {
    pub fn new(ptr: u32) -> Self {
        Facts { ptr, of: Vec::new() }
    }

    /// The pointer width of the target in bytes (the bulk slot, `Span`s), T4-5.
    pub fn ptr(&self) -> u32 {
        self.ptr
    }
}

impl Module {
    /// Fill the facts of `t` and of the values it holds, each type once, by
    /// a stack of its own (the depth of a type is not the depth of the Rust
    /// stack): a type goes down after its parts. The parts are the values a
    /// value holds (the element of an array, the parts of a tuple, the fields
    /// of a struct, the payloads of every variant of an enum); no type holds
    /// itself so (the check rejects one), and one that would is an internal
    /// error.
    pub fn fill_facts(&mut self, t: CTy) {
        let n = self.tys.kinds().len();
        self.facts.of.resize(n.max(self.facts.of.len()), Slot::Empty);
        if !matches!(self.facts.of[t.index()], Slot::Empty) {
            return;
        }
        self.facts.of[t.index()] = Slot::Open;
        let mut stack = vec![(t, self.value_parts(t))];
        while let Some((top, parts)) = stack.last_mut() {
            let top = *top;
            let Some(p) = parts.pop() else {
                self.facts.of[top.index()] = Slot::Done(combine(self, top));
                stack.pop();
                continue;
            };
            match self.facts.of[p.index()] {
                Slot::Done(_) => {}
                Slot::Open => bug(None, format!("the type `{}` holds itself by value", type_name(self, p))),
                Slot::Empty => {
                    self.facts.of[p.index()] = Slot::Open;
                    stack.push((p, self.value_parts(p)));
                }
            }
        }
    }

    /// [`Module::fill_facts`] of every type. A type made after lowering
    /// has no facts, and [`Module::facts`] of it is an internal error
    /// (nothing interns after lowering).
    pub fn fill_all_facts(&mut self) {
        for t in self.tys.ids() {
            self.fill_facts(t);
        }
    }

    /// The facts of `t`, which [`Module::fill_facts`] filled.
    pub fn facts(&self, t: CTy) -> TyFacts {
        match self.facts.of.get(t.index()) {
            Some(Slot::Done(f)) => *f,
            _ => bug(None, format!("the facts of `{}` read before they are filled", type_name(self, t))),
        }
    }

    /// Whether the module has the type `k` and its facts, making no type.
    pub(crate) fn has_facts(&self, k: &TyKind) -> bool {
        self.tys.find(k).is_some_and(|t| matches!(self.facts.of.get(t.index()), Some(Slot::Done(_))))
    }

    /// The values a value of `t` holds, the last first.
    fn value_parts(&self, t: CTy) -> Vec<CTy> {
        let mut out: Vec<CTy> = match self.tys.kind(t) {
            TyKind::Array(e, _) => vec![*e],
            TyKind::Tuple(ts) => ts.to_vec(),
            TyKind::Struct(id) | TyKind::Enum(id) => match &self.ty(*id).kind {
                TypeDefKind::Struct { fields } => fields.iter().map(|&(_, t)| t).collect(),
                TypeDefKind::Enum { variants } => variants.iter().flat_map(|(_, ts)| ts.iter().copied()).collect(),
                TypeDefKind::Opaque => Vec::new(),
            },
            _ => Vec::new(),
        };
        out.reverse();
        out
    }
}

/// The facts of `t` from those of its parts ([`Module::value_parts`]): the
/// layout of spec §12.4 (declaration order, natural alignment, no
/// reordering; an enum the smallest tag of `U8` / `U16` / `U32`, then the
/// largest variant), the same rules as `onsa_sema::layout`.
fn combine(m: &Module, t: CTy) -> TyFacts {
    let ptr = m.facts.ptr;
    let leaf = |n: u32| TyFacts { size: n, align: n, views: false };
    // The parts in declaration order, at their natural alignment.
    let record = |ts: &mut dyn Iterator<Item = CTy>| {
        let mut views = false;
        let parts = ts.map(|t| {
            let f = m.facts(t);
            views |= f.views;
            (f.size, f.align)
        });
        let (size, align) = extent(parts, |_| {});
        TyFacts { size, align, views }
    };
    // No value is of no bytes, as in C (R-504, S-1156): `()`, a tuple or a
    // struct of no fields hold one byte, aligned to one, an array of none one element.
    let held = |f: TyFacts| TyFacts { size: f.size.max(1), ..f };
    let opaque = TyFacts { size: 0, align: 1, views: false };
    match m.tys.kind(t) {
        TyKind::Int(IntKind::I8 | IntKind::U8) | TyKind::Bool | TyKind::Unit => leaf(1),
        TyKind::Int(IntKind::I16 | IntKind::U16) => leaf(2),
        TyKind::Int(IntKind::I32 | IntKind::U32) | TyKind::Float(FloatKind::F32) | TyKind::Char => leaf(4),
        TyKind::Int(IntKind::I64 | IntKind::U64) | TyKind::Float(FloatKind::F64) => leaf(8),
        TyKind::Array(e, n) => {
            let f = m.facts(*e);
            TyFacts { size: f.size.saturating_mul((*n).max(1)), ..f }
        }
        TyKind::Tuple(ts) => held(record(&mut ts.iter().copied())),
        TyKind::Struct(id) => match &m.ty(*id).kind {
            TypeDefKind::Struct { fields } => held(record(&mut fields.iter().map(|&(_, t)| t))),
            _ => opaque,
        },
        TyKind::Enum(id) => match &m.ty(*id).kind {
            TypeDefKind::Enum { variants } => {
                let tag = match variants.len() {
                    0..=256 => 1,
                    257..=65536 => 2,
                    _ => 4,
                };
                let (mut payload_size, mut payload_align, mut views) = (0, 1, false);
                for (_, tys) in variants {
                    let r = record(&mut tys.iter().copied());
                    payload_size = payload_size.max(r.size);
                    payload_align = payload_align.max(r.align);
                    views |= r.views;
                }
                let align = tag.max(payload_align);
                let size = round_up(round_up(tag, payload_align).saturating_add(payload_size), align);
                TyFacts { size, align, views }
            }
            _ => opaque,
        },
        TyKind::Span(_) => TyFacts { size: 2 * ptr, align: ptr, views: true },
        TyKind::FnPtr(_) | TyKind::Buf(_) => leaf(ptr),
    }
}

/// `(size, align)` of a type at the pointer width of its module.
pub fn size_align(m: &Module, ty: CTy) -> (u32, u32) {
    let f = m.facts(ty);
    (f.size, f.align)
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

/// The record of fields of the sizes and alignments given, in their order.
fn place(fields: impl Iterator<Item = (String, (u32, u32))>) -> RecordLayout {
    let fields: Vec<_> = fields.collect();
    let mut offsets = Vec::with_capacity(fields.len());
    let (size, align) = extent(fields.iter().map(|f| f.1), |o| offsets.push(o));
    let fields = fields.into_iter().zip(offsets);
    let fields = fields.map(|((name, (size, align)), offset)| FieldLayout { name, offset, size, align }).collect();
    RecordLayout { fields, size, align }
}

/// The size and alignment of a record of parts of the sizes and alignments
/// given, each placed in its order at its natural alignment (`at` is given
/// each offset): the one rule of a record.
fn extent(parts: impl Iterator<Item = (u32, u32)>, mut at: impl FnMut(u32)) -> (u32, u32) {
    let (mut size, mut align) = (0u32, 1u32);
    for (s, a) in parts {
        size = round_up(size, a);
        at(size);
        size = size.saturating_add(s);
        align = align.max(a);
    }
    (round_up(size, align), align)
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
        self.fast_fields.iter().map(|f| f.offset.saturating_add(f.size)).max().unwrap_or(0)
    }
}

/// The placement of the state `state` of a flow, at the pointer width of the
/// module (the bulk pointer slot and any `Span` in the state follow it).
pub fn flow_layout(m: &Module, state: TypeId, bulk_threshold: Option<u32>) -> FlowLayout {
    let fields: &[(String, CTy)] = match &m.ty(state).kind {
        TypeDefKind::Struct { fields } => fields,
        _ => &[],
    };
    let is_bulk = |ty: CTy| -> bool {
        match (bulk_threshold, m.tys.kind(ty)) {
            (Some(t), TyKind::Array(..)) => m.facts(ty).size >= t,
            _ => false,
        }
    };
    let sized = |bulk: bool| {
        fields.iter().filter(move |(_, t)| is_bulk(*t) == bulk).map(|(n, t)| (n.clone(), size_align(m, *t)))
    };
    let any_bulk = sized(true).next().is_some();
    let mut fast: Vec<(String, (u32, u32))> = Vec::new();
    if any_bulk {
        // The bulk pointer: modelled as a pointer-sized, pointer-aligned slot
        // (the size and alignment of a `Buf`).
        let ptr = m.facts.ptr;
        fast.push((onsa_sema::flow_names::FixedField::Bulk.name().into(), (ptr, ptr)));
    }
    fast.extend(sized(false));
    let f = place(fast.into_iter());
    let b = place(sized(true));
    FlowLayout {
        fast_fields: f.fields,
        bulk_fields: b.fields,
        size: f.size,
        bulk_size: b.size,
        align: f.align.max(if any_bulk { b.align } else { 1 }),
    }
}

#[cfg(test)]
mod tests;
