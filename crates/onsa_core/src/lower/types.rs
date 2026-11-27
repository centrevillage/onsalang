//! The maker of the instances of the types (W8-14): the first `type_id` of
//! an instance fills its closure, on a stack of its own, before it returns,
//! so that a chain of declarations takes no stack of Rust (R-319).
//!
//! A field is converted until it meets an instance not made yet: that one is
//! made, put on the stack and filled, and then the field is converted again,
//! when it finds the instance made. So the ids are given, and the limits
//! judged (§4.4, §4.5), in the order of a recursion through the fields, and
//! an instance a field meets is made, on the stack (a function type reaches
//! back), or one lowering does not lower ([`BadTy`]): none is left half made.

use onsa_diag::unsupported::Feature;
use onsa_diag::{Span, Stage};
use onsa_sema::DefId;
use onsa_sema::def::{DefKind, Fields};
use onsa_sema::ty::{Measure, TyId};

use super::{Fail, FailKind, GenericArg, Lowerer, R, gated, internal};
use crate::ir::*;

/// Why an instance of a type is not lowered: a type of a feature this
/// version does not lower (E0200). The instances that hold it, and those it
/// was made in, are not lowered either. One unsupported part of a unit's
/// bindings is one E0200 (§18.1, S-67): two of the same value are one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct BadTy {
    pub feature: Feature,
    pub detail: Option<&'static str>,
    /// The field of a declaration of a type it is written in; none when it
    /// is written where it is used (`s: Str`, `Option[Str]`).
    pub field: Option<FieldOf>,
}

/// A field of the declaration of a type: where its type is written, the
/// type, and its place among the fields of every variant in order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct FieldOf {
    pub at: Span,
    pub of: DefId,
    pub part: u32,
}

impl BadTy {
    /// The E0200 of a use at `span`, with the field it is written in as a
    /// note: the one way to a [`FailKind::UnsupportedType`].
    pub(super) fn fail(self, lw: &Lowerer, span: Span) -> Fail {
        let mut d = self.feature.diagnostic(Stage::Build, span, self.detail.as_slice());
        if let Some(f) = self.field {
            d = d.with_note(f.at, lw.field_text(f));
        }
        Fail { kind: FailKind::UnsupportedType(self), ..gated(d) }
    }
}

/// An instance on the stack of the maker.
pub(super) struct Fill {
    id: TypeId,
    d: DefId,
    gargs: Vec<GenericArg>,
    span: Span,
    /// The types of the fields, of every variant in order, and where each is written.
    parts: Vec<(TyId, Span)>,
    /// The Core types of the fields converted.
    done: Vec<CTy>,
    /// The field being converted: where a type over the limits is reported.
    pub(super) at: Option<Span>,
}

/// The failure of a field that met an instance not made yet: it is made, and
/// the field converted again. Never out of [`Lowerer::fill_types`].
fn pending(span: Span) -> Fail {
    Fail { kind: FailKind::Pending, ..internal(span, "an instance of a type made out of the maker") }
}

impl Lowerer<'_> {
    /// The instance of the struct or enum `d` at `gargs`, made and filled if
    /// it is new: the one way to it, which fails as its first use did if it
    /// holds a type lowering does not lower.
    pub(crate) fn named_ty(&mut self, d: DefId, gargs: Vec<GenericArg>, span: Span) -> R<TypeId> {
        let id = self.type_id(d, gargs, span)?;
        match self.bad_types.get(&id) {
            Some(&bad) => Err(bad.fail(self, span)),
            None => Ok(id),
        }
    }

    /// An E0200 of the type at `span` of `feature`: written in the field
    /// being converted, if any.
    pub(super) fn bad_type(&self, span: Span, feature: Feature, detail: Option<&'static str>) -> Fail {
        BadTy { feature, detail, field: self.field_at() }.fail(self, span)
    }

    /// The field of a type being converted, the innermost (`limits` reports
    /// a type over the limits there too).
    pub(super) fn field_at(&self) -> Option<FieldOf> {
        let f = self.fills.iter().rev().find(|f| f.at.is_some())?;
        Some(FieldOf { at: f.at?, of: f.d, part: f.done.len() as u32 })
    }

    /// The note of a type held by the field `f`: ``the field `name` of `Mm`
    /// has the type `Str` ``, of a variant ``a field of the variant `A` of `E`
    /// has the type `Str` ``.
    fn field_text(&self, f: FieldOf) -> String {
        let def = self.a.def(f.of);
        let shown = |t: TyId| self.a.display_under(t, def.generics());
        let mut part = f.part as usize;
        let field = match &def.kind {
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => fs.get(part).map(|x| (format!("the field `{}`", x.name), x.ty)),
                Fields::Opaque => None,
            },
            DefKind::Enum(e) => e.variants.iter().find_map(|v| match v.fields.get(part) {
                Some(&t) => Some((format!("a field of the variant `{}`", v.name), t)),
                None => {
                    part -= v.fields.len();
                    None
                }
            }),
            _ => None,
        };
        match field {
            Some((field, t)) => format!("{field} of `{}` has the type `{}`", def.name, shown(t)),
            // A field is of a struct or an enum only (`type_id`).
            None => format!("a field of `{}`", def.name),
        }
    }

    /// A new type of the module (the one place that makes one).
    pub(super) fn new_type(&mut self, name: String, kind: TypeDefKind) -> TypeId {
        let id = TypeId(self.m.types.len() as u32);
        self.m.types.push(TypeDef { name, kind });
        id
    }

    /// The instance of `d` at `gargs`: of the table, or made, judged and
    /// counted here once, before its fields. A new one in a field being
    /// converted is put on the stack and stops that field ([`pending`]).
    fn type_id(&mut self, d: DefId, gargs: Vec<GenericArg>, span: Span) -> R<TypeId> {
        if let Some(&id) = self.type_ids.get(&(d, gargs.clone())) {
            return Ok(id);
        }
        let a = self.a;
        let parts: Option<Vec<(TyId, Span)>> = match &a.def(d).kind {
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => Some(fs.iter().map(|f| (f.ty, f.ty_span)).collect()),
                // A flow's state: its fields are written after (`set_state_fields`).
                Fields::Opaque => None,
            },
            DefKind::Enum(e) => Some(
                e.variants.iter().flat_map(|v| v.fields.iter().copied().zip(v.field_spans.iter().copied())).collect(),
            ),
            _ => return Err(internal(span, "not a type def")),
        };
        // Before the fields are read: they are where a type grows.
        let args = self.args_measure(&gargs);
        let measure = self.within(args, span)?;
        self.count_instance(d, span)?;
        let name = format!("{}{}", self.qual_name(d), self.mangle_args(&gargs));
        let id = self.new_type(name, TypeDefKind::Opaque);
        if measure != Measure::LEAF {
            self.type_measures.insert(id, measure);
        }
        self.type_ids.insert((d, gargs.clone()), id);
        self.type_defs.insert(id, (d, gargs.clone()));
        let Some(parts) = parts else { return Ok(id) };
        let outermost = self.fills.is_empty();
        self.fills.push(Fill { id, d, gargs, span, parts, done: Vec::new(), at: None });
        if !outermost {
            return Err(pending(span));
        }
        self.fill_types().map(|()| id)
    }

    /// Fill the instances of the stack, the top first. A failure empties it:
    /// of a type lowering does not lower, its instances are bad ([`BadTy`]),
    /// so that no use finds them made. An internal error or a limit stops
    /// lowering (`lower_item`), and no use comes after.
    fn fill_types(&mut self) -> R<()> {
        while let Some(top) = self.fills.last_mut() {
            let Some(&(t, at)) = top.parts.get(top.done.len()) else {
                if let Some(fill) = self.fills.pop() {
                    self.finish(fill);
                }
                continue;
            };
            top.at = Some(at);
            let (span, gargs) = (top.span, std::mem::take(&mut top.gargs));
            let i = self.fills.len() - 1;
            let r = self.core_ty(t, &gargs, span);
            self.fills[i].gargs = gargs;
            match r {
                Ok(ty) => self.fills[i].done.push(ty),
                Err(f) if f.kind == FailKind::Pending => {}
                Err(f) => {
                    for fill in std::mem::take(&mut self.fills) {
                        if let FailKind::UnsupportedType(bad) = f.kind {
                            self.bad_types.entry(fill.id).or_insert(bad);
                        }
                    }
                    return Err(f);
                }
            }
        }
        Ok(())
    }

    /// Write the fields of the instance `fill`, all converted.
    fn finish(&mut self, fill: Fill) {
        let a = self.a;
        let mut done = fill.done.into_iter();
        let kind = match &a.def(fill.d).kind {
            DefKind::Struct(s) => match &s.fields {
                Fields::Named(fs) => {
                    TypeDefKind::Struct { fields: fs.iter().map(|f| f.name.clone()).zip(done).collect() }
                }
                Fields::Opaque => TypeDefKind::Opaque,
            },
            DefKind::Enum(e) => {
                let variants =
                    e.variants.iter().map(|v| (v.name.clone(), done.by_ref().take(v.fields.len()).collect()));
                TypeDefKind::Enum { variants: variants.collect() }
            }
            _ => TypeDefKind::Opaque,
        };
        self.m.types[fill.id.0 as usize].kind = kind;
    }
}
