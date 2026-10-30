//! The captures (W4-07 memo 2.7; §5.3, §5.4): an anonymous function is
//! walked once, in a frame of its own from a new state: it changes no state
//! outside, and what it captures is a copy made with it, read from no state
//! (no E0704). What it captures is the record of the names stage
//! (`BodyInfo::captures`, in the order of the first reads; review 7).

use std::mem::replace;

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::ExprId;

use super::check::Walker;
use super::flow::Run;
use super::walk::Pos;
use super::write::How;
use crate::Kind;
use crate::binding::Bind;
use crate::body::LocalId;

/// An anonymous function the walk is in, and the values it captures that
/// its body has read so far.
pub(super) struct Frame {
    closure: ExprId,
    read: Vec<LocalId>,
}

impl Walker<'_> {
    /// The anonymous function `e` with the body `body`, walked by the walk
    /// that reports only (a loop's summary does not go in, memo 1.3).
    pub(super) fn closure(&mut self, r: &mut Run, e: ExprId, body: ExprId) {
        if !self.reports {
            return;
        }
        self.uncapturable(e);
        let outer = replace(r, Run::new());
        self.inside.frames.push(Frame { closure: e, read: Vec::new() });
        self.expr(r, body, Pos::Return);
        self.inside.frames.pop();
        *r = outer;
    }

    fn captures(&self, e: ExprId) -> &[LocalId] {
        self.info.captures.get(&e).map_or(&[], |c| c.as_slice())
    }

    /// `l` is a value an anonymous function the walk is in captures.
    pub(super) fn captured(&self, l: LocalId) -> bool {
        self.inside.frames.iter().any(|f| self.captures(f.closure).contains(&l))
    }

    /// The E0712 of the anonymous function `e` (§5.3): one, of the first
    /// value its body reads that cannot be captured (S-722): an `inout`
    /// parameter whatever its kind (review 6), an Affine value.
    fn uncapturable(&mut self, e: ExprId) {
        let info = self.info;
        for &l in info.captures.get(&e).into_iter().flatten() {
            let local = &info.locals[l.0 as usize];
            let why = match local.state {
                Bind::Inout => "is an `inout` parameter",
                _ if self.kind_of(local.ty) == Some(Kind::Affine) => "is Affine and cannot be copied",
                _ => continue,
            };
            let message = format!("a closure captures outer values by copy; `{}` {why} (§5.3)", local.name);
            let d = Diagnostic::new(Stage::Modes, Code::E0712, self.ast.expr(e).span, message);
            return self.report(d.with_note(local.span, "captured value declared here"));
        }
    }

    /// `l` is read at `at`: at its first read in an anonymous function that
    /// captures it (memo 2.7, after the E0712 of the function), a
    /// second-class value is E0710 (R-331, S-217) and a Shared one E0200
    /// (R-85 (5), S-80: by its type, so a static value and a `T` with no
    /// bound too); a Copy one is copied.
    pub(super) fn read_captured(&mut self, l: LocalId, at: Span) {
        // Not in a loop's summary, which goes before the walk that reports.
        if !self.reports {
            return;
        }
        let (info, mut first) = (self.info, false);
        for f in &mut self.inside.frames {
            if info.captures.get(&f.closure).is_some_and(|c| c.contains(&l)) && !f.read.contains(&l) {
                f.read.push(l);
                first = true;
            }
        }
        let ty = info.locals[l.0 as usize].ty;
        if !first || info.locals[l.0 as usize].state == Bind::Inout {
            return;
        }
        let d = match (self.class_of(ty), self.kind_of(ty)) {
            (Some(class), _) => self.second_class_error(class, "captured", at),
            (None, Some(Kind::Shared)) => Feature::CapturedShared.diagnostic(Stage::Modes, at, &[]),
            _ => return,
        };
        self.report(d);
    }

    /// R-25: the write `how` at `at` to a place of `l`, which an anonymous
    /// function the walk is in captures, is E0701 whatever `l` is: a value
    /// captured is read-only (§5.3), `var` or not, so with no candidate.
    pub(super) fn captured_write(&mut self, l: LocalId, at: Span, how: How) {
        let local = &self.info.locals[l.0 as usize];
        let message = format!("{}: `{}` is captured by a closure, read-only (§5.3)", how.verb(), local.name);
        let d = Diagnostic::new(Stage::Modes, Code::E0701, at, message);
        self.report(d.with_note(local.span, "captured value declared here"));
    }
}
