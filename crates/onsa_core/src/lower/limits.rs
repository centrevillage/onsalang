//! The limits of what lowering makes (§4.4, §4.5, S-290): the types of the
//! instances and their number. The first one over a limit stops lowering, and
//! it is the only diagnostic (§18.1): going on would go on instantiating.
//!
//! The two limits make the worklist finite: the types with a bounded measure
//! over finitely many names are finitely many, and the number stops what is
//! finite but astronomical. Every instance goes through `fn_id`, `type_id` or
//! `const_id`; what they do not count (generated functions, derived members)
//! is at most a few for each instance they count.
//!
//! A type is judged form by form as it is made ([`Lowerer::within`]), each
//! part before the next is made, so that one `core_ty` makes at most about
//! twice the limit of the size, whatever its parameters stand for, and no
//! walk repeats: a parameter is measured when it is copied, in the time of the
//! copy, and an instance of a type once, when it is made.

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Note, Span, Stage};
use onsa_sema::DefId;
use onsa_sema::def::DefKind;
use onsa_sema::ty::Measure;

use super::{Fail, FailKind, GenericArg, Lowerer, R, internal};
use crate::ir::*;

/// The instances a package may have (§4.5): the one place.
pub const INSTANCE_LIMIT: u32 = 65536;

/// The stack `type_id` leaves unused, as `onsa_sema::walk` does.
const STACK_RESERVE: usize = 1 << 20;

/// The notes of the path of an E0422.
const MAX_PATH_NOTES: usize = 3;

fn limit_fail(d: Diagnostic) -> Fail {
    let (span, msg) = (d.span, d.message.clone());
    Fail { kind: FailKind::Limit, span, msg, hole: None, report: Some(Box::new(d)) }
}

impl Lowerer<'_> {
    /// The measure of an instance of a type, read from where it was made.
    /// One with no arguments has no row, and a flow's state of a `par` no
    /// declaration: both are a name.
    pub(super) fn type_measure(&self, id: TypeId) -> Measure {
        self.type_measures.get(&id).copied().unwrap_or(Measure::LEAF)
    }

    /// The measure of a Core type, as the check reads its type (§4.4): a
    /// struct or an enum is the form of its arguments, not a leaf.
    pub(super) fn measure(&self, ty: &Ty) -> Measure {
        let of = |m: Measure, t: &Ty| m.with(self.measure(t));
        match ty {
            Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char => Measure::LEAF,
            Ty::Unit => Measure::form(1),
            Ty::Tuple(ts) => ts.iter().fold(Measure::form(1), of),
            Ty::Array(e, _) | Ty::Span(e) | Ty::Buf(e) => of(Measure::form(2), e),
            Ty::Struct(id) | Ty::Enum(id) => self.type_measure(*id),
            Ty::FnPtr(f) => of(f.params.iter().map(|(_, t)| t).fold(Measure::form(1), of), &f.ret),
        }
    }

    /// The measure of a type of the arguments `args`.
    pub(super) fn args_measure(&self, args: &[GenericArg]) -> Measure {
        if args.is_empty() {
            return Measure::LEAF;
        }
        args.iter().fold(Measure::form(2), |m, a| match a {
            GenericArg::Ty(t) => m.with(self.measure(t)),
            GenericArg::Const(_) => m.with(Measure::LEAF),
        })
    }

    /// The safety net of the recursion of `type_id` through the fields: types
    /// that only turn their arguments around do not grow, so that only the
    /// number of instances bounds it. An internal error, not a diagnostic, as
    /// the deep chains of declarations (R-319; W8-01 ends the recursion).
    pub(super) fn stack_left(&self, span: Span) -> R<()> {
        if onsa_diag::stack::remaining().is_some_and(|left| left < STACK_RESERVE) {
            let levels = self.places.len();
            return Err(internal(span, format!("instances of types {levels} levels deep, more than the stack holds")));
        }
        Ok(())
    }

    /// `m`, unless it is over the limits of §4.4 (E0422): at the field being
    /// read, else at `span`.
    pub(super) fn within(&self, m: Measure, span: Span) -> R<Measure> {
        if !m.over_limit() {
            return Ok(m);
        }
        let rule = "a call or a field wraps its type argument, so that an instance makes a larger type: wrap less, \
                    keep the type of a recursion fixed, or use an array";
        let at = self.place(span);
        let mut d = Diagnostic::new(Stage::Build, Code::E0422, at, m.limit_message()).with_rule(rule);
        d.notes.extend(self.path_notes(at));
        Err(limit_fail(d))
    }

    /// One more instance of `d` (§4.5), at `span`: what it does not count
    /// passes. Over the limit, an E0423.
    pub(super) fn count_instance(&mut self, d: DefId, span: Span) -> R<()> {
        if !self.counted(d) {
            return Ok(());
        }
        self.instances += 1;
        let limit = self.instance_limit;
        if self.instances <= limit {
            return Ok(());
        }
        let msg = format!("the package makes more than {limit} instances of its items (§4.5)");
        let rule = "each set of type arguments makes an instance of its item: use fewer of them";
        let mut report = Diagnostic::new(Stage::Build, Code::E0423, self.place(span), msg).with_rule(rule);
        if let Some((top, n)) = self.most_instances() {
            let note = format!("`{}` has the most instances: {n}", self.qual_name(top));
            report = report.with_note(self.a.def(top).name_span, note);
        }
        Err(limit_fail(report))
    }

    /// `read`, with a type over the limits reported at the field `at`, not at
    /// the position it is given, which an E0200 keeps.
    pub(super) fn at_place<T>(&mut self, at: Span, read: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.places.push(at);
        let r = read(self);
        self.places.pop();
        r
    }

    fn place(&self, span: Span) -> Span {
        self.places.last().copied().unwrap_or(span)
    }

    /// Whether `d` is one that §4.5 counts: not what a flow generates or a
    /// derive makes, and of the constants those of an `impl` and the defaults.
    fn counted(&self, d: DefId) -> bool {
        let def = self.a.def(d);
        match &def.kind {
            DefKind::Fn(f) => f.flow_fn.is_none() && f.derived.is_none(),
            DefKind::Const(_) => def.owner.is_some(),
            _ => true,
        }
    }

    /// The item with the most instances, past one; of those, the first
    /// declared. Counted once, when the limit is passed.
    fn most_instances(&self) -> Option<(DefId, u32)> {
        let keys = self.fn_ids.keys().chain(self.type_ids.keys()).chain(self.const_ids.keys());
        let mut counts: HashMap<DefId, u32> = HashMap::new();
        for (d, _) in keys.filter(|(d, _)| self.counted(*d)) {
            *counts.entry(*d).or_default() += 1;
        }
        counts.into_iter().filter(|&(_, n)| n > 1).max_by_key(|&(d, n)| (n, Reverse(d)))
    }

    /// The path the type arguments came by to the diagnostic at `at`: the
    /// fields being read, innermost first, then the calls that made the
    /// instances up to a root. A position is one note, so a recursion is one,
    /// however long it ran, and `at` none.
    fn path_notes(&self, at: Span) -> Vec<Note> {
        let mut path: Vec<Span> = self.places.iter().rev().copied().collect();
        let mut lowering = self.lowering;
        while let Some(f) = lowering {
            let (call, parent) = self.made_by[&f];
            // A root has no call: it was made at its own declaration.
            if call != self.m.fns[f.0 as usize].span {
                path.push(call);
            }
            lowering = parent;
        }
        let mut seen = HashSet::from([at]);
        path.retain(|s| seen.insert(*s));
        let notes = path.into_iter().take(MAX_PATH_NOTES);
        notes.map(|s| Note::at(s, "the type arguments come through here")).collect()
    }
}
