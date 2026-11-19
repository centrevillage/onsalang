//! The checks of the flow rules at stage 2 of the walk (§11.3–§11.5): each
//! at its place in the walk, which goes on past an error and keeps the first
//! diagnostic in the order of the file (§18.1). A clock in error is no error
//! of a check (§18.1): the comparisons of [`crate::clock`] pass it. The
//! checks on which the rule of the clock of their expression rests give it
//! in error when they fail: the E0813 of a delay, the E0805 and the E0815 of
//! a call of a function (§11.5), `if~` / `match~`, a node in a branch; the
//! others leave it as the rules give it (the `k` of `e at k`, the output of
//! an instance, the clock of a delay by its first argument, a value whose
//! type holds a function type, E0810). A value made with `Alloc` to drop
//! (E0805) is in error too ([`Walk::fault`]).

use onsa_syntax::ast::{Lit, OperandPlace};

use super::*;
use crate::binding::{aggregate, unit_variant};
use crate::clock::{holds_state, promote, readable_at};
use crate::kind::kind_in_body;
use crate::slot::{Form, Slot};

/// Whether `at` makes a value at the clock `c` one at the clock `k`: it is
/// not slower (§11.3). The one predicate of `e at k` ([`Walk::check_at`])
/// and of the candidate of E0813 that writes `first at sample`
/// ([`Walk::check_first`]), which so passes the check of its `at`.
fn promotable(c: Clock, k: Clock) -> bool {
    promote(c, k).is_ok()
}

/// What the rules of a flow body find wrong with the value of an
/// expression, by its type ([`Walk::fault`]).
#[derive(Debug, Clone, Copy)]
pub(super) enum Fault {
    /// A value made whose drop needs `Alloc` (E0805), and what makes it.
    Alloc(&'static str),
    /// A type that holds a function type (E0810).
    Fn,
}

impl Walk<'_> {
    /// Whether the checks run: at `Check`.
    pub(super) fn checking(&self) -> bool {
        self.mode == Mode::Check
    }

    pub(super) fn src(&self, span: Span) -> String {
        span.text_in(self.text).to_string()
    }

    /// A diagnostic of the walk, kept if it is the first (§18.1).
    pub(super) fn report(&mut self, d: Diagnostic) {
        Diagnostic::keep_first(&mut self.diag, d);
    }

    fn err(&mut self, code: Code, span: Span, msg: String) {
        let found = self.src(span);
        self.report(Diagnostic::new(Stage::Flow, code, span, msg).with_found(found));
    }

    fn gate(&mut self, feature: Feature, span: Span, details: &[&str]) {
        let found = self.src(span);
        self.report(feature.diagnostic(Stage::Flow, span, details).with_found(found));
    }

    fn ty_of(&self, e: ExprId) -> TyId {
        self.body.expr_types.get(&e).copied().unwrap_or(self.error)
    }

    /// §11.3: the value type of a `let` of the body is Copy (E0810).
    pub(super) fn check_let(&mut self, p: &PendingLet) {
        if self.checking()
            && let Some(d) = crate::signal::not_copy_signal(self.a, self.ty_of(p.init), p.span)
        {
            let found = self.src(p.span);
            self.report(d.with_found(found));
        }
    }

    /// §11.3, S-1047 (d): the element of the result of the `par~` at `e` is
    /// the value of a signal, Copy (E0810 at the `par~`, as of a `let`).
    pub(super) fn check_par(&mut self, e: ExprId) {
        let span = self.ast.expr(e).span;
        if let Ty::Array(elem, _) = self.a.types.get(self.ty_of(e))
            && let Some(d) = crate::signal::not_copy_signal(self.a, *elem, span)
        {
            self.report(d.with_found(self.src(span)));
        }
    }

    /// §11.3, S-1047 (d), R-458: the value of the delay at `e` is the value
    /// of a signal, Copy in any place (E0810 at the delay, as of a `let`);
    /// whether it is reported.
    pub(super) fn check_delay_value(&mut self, e: ExprId) -> bool {
        let span = self.ast.expr(e).span;
        let Some(d) = crate::signal::not_copy_signal(self.a, self.ty_of(e), span) else { return false };
        self.report(d.with_found(self.src(span)));
        true
    }

    /// What the rules of a flow body on the type of the value of `e` find
    /// wrong with it, in this order: the same in every mode, reported at
    /// `Check` ([`Self::report_fault`]). A value made with `Alloc` to drop is
    /// in error then (§11.5 gives no rule of its clock): no outer check reads
    /// its clock; one whose type holds a function type keeps the clock its
    /// rule gives, which rests on no type (S-1133).
    // SPEC-GAP(S-1152): every visited expression whose type holds a function
    // is an E0810 and the first by place is the one reported (provisional).
    pub(super) fn fault(&mut self, e: ExprId) -> Option<Fault> {
        let ty = self.ty_of(e);
        // SPEC-GAP(S-1153): of one expression that is both, E0805 is the one
        // (provisional).
        if let Some(what) = self.made(e, ty) {
            return Some(Fault::Alloc(what));
        }
        crate::signal::holds_fn(self.a, ty).then_some(Fault::Fn)
    }

    /// What `e` is if it makes a value whose drop needs `Alloc` (§11.5,
    /// §12.2, S-1043 C2): a string with an interpolation, the result of a
    /// call of a function, or a literal whose own type is not Dup (an
    /// aggregate, a unit variant; a value in a literal that is Dup is made by
    /// an expression in it). A value that needs no drop (§5.4, S-1076) is
    /// none of these.
    fn made(&mut self, e: ExprId, ty: TyId) -> Option<&'static str> {
        let (ast, body) = (self.ast, self.body);
        // `literal`: a literal, whose own type is to be Dup.
        let (what, literal) = match &ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) if s.value().is_none() => ("a string with an interpolation", false),
            ExprKind::Call { .. }
                if matches!(body.targets.get(&e), Some(Target::Fn { .. } | Target::Method { .. })) =>
            {
                ("this call", false)
            }
            _ if aggregate(ast, body, e) || unit_variant(self.a, ast, body, e) => ("this literal", true),
            _ => return None,
        };
        let a = self.a;
        let (dup, drops) = *self.dup_drops.entry(ty).or_insert_with(|| {
            (crate::kind::dup(kind_in_body(a, ty, &[])), crate::drop_alloc::Frame::body(a, vec![]).drops(ty))
        });
        (drops && !(dup && literal)).then_some(what)
    }

    /// The diagnostic of the fault `f` of `e`: E0805 of a value made with
    /// `Alloc` to drop, E0810 of a type that holds a function type (§11.3,
    /// S-372: part of it read too, S-1151).
    /// None when the diagnostic kept starts before it, which [`Self::report`]
    /// would keep: the note of the path of an E0810 walks the type.
    pub(super) fn report_fault(&mut self, e: ExprId, f: Fault) {
        let span = self.ast.expr(e).span;
        if self.diag.as_ref().is_some_and(|d| Diagnostic::place_before(d.span, span)) {
            return;
        }
        let d = match f {
            Fault::Alloc(what) => {
                let msg = format!(
                    "{what} makes a value whose drop needs `Alloc`, which a flow body cannot use (§11.5, §12.2)"
                );
                Diagnostic::new(Stage::Flow, Code::E0805, span, msg)
                    .with_rule("a flow uses no heap: make the value in an `rt fn` that returns a value that is Copy")
            }
            Fault::Fn => {
                let what = "the type of an expression of a flow body";
                crate::signal::fn_type_error(self.a, self.ty_of(e), span, what).with_rule(
                    "move this expression into an `rt fn` or a `const` that gives the flow what it reads (`const GAIN: F32 = P.gain`)",
                )
            }
        };
        let found = self.src(span);
        self.report(d.with_found(found));
    }

    /// `inner at k` at `e` (§11.3), `c` the clock of `inner`: no slower
    /// (E0815). A computed `inner` made faster is hoisted (S-152).
    pub(super) fn check_at(&mut self, e: ExprId, c: Option<Clock>, k: Clock) {
        let Some(c) = c.filter(|_| self.checking()) else { return };
        let span = self.ast.expr(e).span;
        if !promotable(c, k) {
            let (shown, to) = (c.shown(span), k.shown(span));
            let msg = format!(
                "this expression is at the clock `{shown}`, faster than `{to}`; `at` cannot make a value slower (§11.3)"
            );
            self.err(Code::E0815, span, msg);
        }
    }

    /// `if~` / `match~` (`form`) at its `~`: W7-06, in error.
    pub(super) fn tilde(&mut self, tilde: Span, form: &str) -> Option<Clock> {
        if self.checking() {
            self.gate(Feature::TildeBranches, tilde, &[form]);
        }
        Some(Clock::Error)
    }

    /// Whether a node or a `par~` at `e` may be here: not in a branch (K-08,
    /// W7-06).
    pub(super) fn stateful_here(&mut self, e: ExprId) -> bool {
        if self.checking() && self.branch > 0 {
            self.gate(Feature::StatefulInBranch, self.ast.expr(e).span, &[]);
            return false;
        }
        true
    }

    /// The signature of the function `def` has an error type: a call of it
    /// is in error, with no diagnostic (§18.1, R-499), in every stage.
    pub(super) fn signature_failed(&self, def: DefId) -> bool {
        let types = &self.a.types;
        self.a
            .def(def)
            .as_fn()
            .is_some_and(|f| types.has_error(f.ret) || f.params.iter().any(|p| types.has_error(p.ty)))
    }

    /// Whether a call at `e` of the function `def`, `ops` the clocks of its
    /// receiver (`receiver`) and arguments and `r` their join, has a clock
    /// (§11.5): the first `inout self` call held (E0713, §5.2), no effects
    /// (E0805), and a function that is not `rt` takes values at `init` or
    /// constants only (E0815, S-147); one that does is recorded for the
    /// marking. With E0805 or that E0815 the rule of its clock fails, and the
    /// call is in error (§18.1).
    pub(super) fn check_fn_call(
        &mut self,
        e: ExprId,
        def: DefId,
        receiver: bool,
        ops: &[Option<Clock>],
        r: Option<Clock>,
    ) -> bool {
        let Some(f) = self.a.def(def).as_fn().filter(|_| self.checking()) else { return true };
        let span = self.ast.expr(e).span;
        let name = &self.a.def(def).name;
        if f.takes_inout_self() {
            let msg = format!("`{name}` takes `inout self`, and a flow body cannot call it (§5.2, §11.2)");
            let d = Diagnostic::new(Stage::Flow, Code::E0713, span, msg).with_found(self.src(span));
            Diagnostic::keep_first(&mut self.inout_call, d);
        }
        if !f.effects.effects().is_empty() {
            let msg = format!("`{name}` has effects; a flow calls effect-free functions only (§11.5)");
            self.err(Code::E0805, span, msg);
            return false;
        }
        if f.rt || r == Some(Clock::Error) {
            return true;
        }
        let fast = |c: &Option<Clock>| readable_at(c.unwrap_or(Clock::Const), Clock::Init).is_err();
        let Some(k) = ops.iter().position(fast) else {
            self.non_rt.insert(e, ops.iter().any(|c| c.is_some_and(|c| c != Clock::Const)));
            return true;
        };
        let place = match k.checked_sub(usize::from(receiver)) {
            None => "its receiver".to_string(),
            Some(k) => format!("its argument {}", k + 1),
        };
        let shown = ops[k].unwrap_or(Clock::Const).shown(span);
        let msg = format!(
            "`{name}` is not `rt` and takes values at the clock `init` or constants only, but {place} is at `{shown}`; mark it `rt` or pass values at `init` (§11.5)"
        );
        self.err(Code::E0815, span, msg);
        false
    }

    /// The argument `x` at the clock `c` of an instance of `g`, read at
    /// `at`, the clock of its input `input` (§11.3, E0815).
    pub(super) fn check_arg(&mut self, x: ExprId, c: Clock, at: Clock, input: &FlowInput, g: DefId) {
        if !self.checking() || readable_at(c, at).is_ok() {
            return;
        }
        let span = self.ast.expr(x).span;
        let (shown, to, name) = (c.shown(span), at.shown(span), &self.a.def(g).name);
        let msg = format!(
            "this argument is at the clock `{shown}` but the input `{}` of `{name}` is at `{to}`; a value is never made slower (§11.3)",
            input.name
        );
        self.err(Code::E0815, span, msg);
    }

    /// Whether the first argument `first` of a delay, at the clock `c`,
    /// holds its state (§11.4, E0813); one `at` makes `sample`
    /// ([`promotable`]) has the candidate `first at sample` (S-102, S-152),
    /// in parentheses where `at` takes them (§3.1: `(p * 2.0) at sample`),
    /// unless the walk found an error in it, which the candidate would
    /// leave (§18.1), or it is a `^name`.
    pub(super) fn check_first(&mut self, delay: Delay, first: ExprId, c: Clock) -> bool {
        if holds_state(c) {
            return true;
        }
        let span = self.ast.expr(first).span;
        let d = delay.name();
        let msg = match c {
            Clock::Const => {
                format!("the first argument of `{d}~` must be at the clock `sample`; this one is a constant (§11.4)")
            }
            c => format!(
                "the first argument of `{d}~` must be at the clock `sample`; this one is at `{}` (§11.4)",
                c.shown(span)
            ),
        };
        let src = self.src(span);
        let mut diag = Diagnostic::new(Stage::Flow, Code::E0813, span, msg).with_found(src.clone());
        let inside = self.diag.as_ref().is_some_and(|d| span.start <= d.span.start && d.span.end <= span.end);
        // SPEC-GAP(S-1165): `^b` (past parentheses and `at`) has no candidate:
        // the error it would leave may be in the `let` of `b`, walked later.
        let feedback = matches!(self.ast.expr(crate::flow::strip(self.ast, first)).kind, ExprKind::Feedback(_));
        if promotable(c, Clock::SAMPLE) && !inside && !feedback {
            let wrap = Slot::Operand(OperandPlace::AsAtLeft).wraps(Form::of(self.ast, first));
            let (open, close) = if wrap { ("(", ")") } else { ("", "") };
            let title = format!("write `{open}{src}{close} at sample` to delay it per sample");
            let mut edits = vec![Edit::insert(span.file, span.end, format!("{close} at sample"))];
            if wrap {
                edits.insert(0, Edit::insert(span.file, span.start, open));
            }
            diag = diag.with_fix(Fix::new(title, edits));
        }
        self.report(diag);
        false
    }

    /// The `init` `i` of a delay, at the clock `c`, is at `init` or a
    /// constant (§11.4, E0815).
    pub(super) fn check_init(&mut self, delay: Delay, i: ExprId, c: Clock) {
        if !self.checking() || readable_at(c, Clock::Init).is_ok() {
            return;
        }
        let span = self.ast.expr(i).span;
        let msg = format!(
            "the `init` of `{}~` must be at the clock `init` or a constant; this one is at `{}` (§11.4)",
            delay.name(),
            c.shown(span)
        );
        self.err(Code::E0815, span, msg);
    }
}
