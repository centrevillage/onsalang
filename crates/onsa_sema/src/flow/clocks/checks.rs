//! The checks of the flow rules at stage 2 of the walk (§11.3–§11.5): each
//! at its place in the walk, the first diagnostic kept, where the walk
//! stops. A clock in error is no error of a check (§18.1): the comparisons
//! of [`crate::clock`] pass it.

use super::*;
use crate::clock::{holds_state, promote, readable_at};

/// Whether `e` is written as a name or a literal, past parentheses and type
/// arguments (not `^name`): the operand `at` makes faster as written (the
/// E0200 of a computed one, W7-05) and the first argument of a delay the
/// note of E0813 writes again.
pub(crate) fn name_or_literal(ast: &Ast, mut e: ExprId) -> bool {
    loop {
        match &ast.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::TypeArgs { base: x, .. } => e = *x,
            k => return matches!(k, ExprKind::Path(_) | ExprKind::Lit(_)),
        }
    }
}

impl Walk<'_> {
    /// Whether the checks run: at `Check`, before the first diagnostic.
    fn checking(&self) -> bool {
        self.mode == Mode::Check && self.diag.is_none()
    }

    pub(super) fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    /// The first diagnostic: the walk stops.
    pub(super) fn fail(&mut self, d: Diagnostic) -> Option<Clock> {
        self.diag = Some(d);
        Some(Clock::Error)
    }

    fn err(&mut self, code: Code, span: Span, msg: String) -> Option<Clock> {
        let found = self.src(span);
        self.fail(Diagnostic::new(Stage::Flow, code, span, msg).with_found(found))
    }

    fn gate(&mut self, feature: Feature, span: Span, details: &[&str]) -> Option<Clock> {
        let found = self.src(span);
        self.fail(feature.diagnostic(Stage::Flow, span, details).with_found(found))
    }

    fn ty_of(&self, e: ExprId) -> TyId {
        self.body.expr_types.get(&e).copied().unwrap_or(self.error)
    }

    /// §11.3: the value type of a `let` of the body is Copy (E0810).
    pub(super) fn check_let(&mut self, p: &PendingLet) {
        if self.checking()
            && let Some(d) = crate::sig::not_copy_signal(self.a, self.ty_of(p.init), p.span)
        {
            let found = self.src(p.span);
            self.fail(d.with_found(found));
        }
    }

    /// §11.4: `vdelay~` interpolates a float (E0401), after the `let`s.
    pub(super) fn check_floats(&mut self) {
        for &(span, e) in &self.cx.float_checks {
            if !self.checking() {
                return;
            }
            if !matches!(self.a.types.get(self.ty_of(e)), Ty::Float(_) | Ty::Error) {
                let msg = "`vdelay~` interpolates and needs a float signal (`F32` / `F64`, §11.4)";
                self.err(Code::E0401, span, msg.into());
            }
        }
    }

    /// `inner at k` at `e` (§11.3), `c` the clock of `inner`: no slower
    /// (E0815), and faster only as a name, a literal or a constant (W7-05).
    pub(super) fn check_at(&mut self, e: ExprId, inner: ExprId, c: Option<Clock>, k: Clock) {
        let Some(c) = c.filter(|_| self.checking()) else { return };
        let span = self.ast.expr(e).span;
        if promote(c, k).is_err() {
            let (shown, to) = (c.shown(span), k.shown(span));
            let msg = format!(
                "this expression is at the clock `{shown}`, faster than `{to}`; `at` cannot make a value slower (§11.3)"
            );
            self.err(Code::E0815, span, msg);
        } else if c != k && !matches!(c, Clock::Const | Clock::Error) && !name_or_literal(self.ast, inner) {
            self.gate(Feature::ClockPromotion, span, &[]);
        }
    }

    /// `if~` / `match~` (`form`) at its `~`: W7-06.
    pub(super) fn tilde(&mut self, tilde: Span, form: &str) -> Option<Clock> {
        if self.checking() {
            return self.gate(Feature::TildeBranches, tilde, &[form]);
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

    /// A call at `e` of the function `def`, `r` the join of its receiver and
    /// arguments (§11.5): the first `inout self` call held (E0713, §5.2), no
    /// effects (E0805), and a function that is not `rt` takes values at
    /// `init` or constants only (E0805).
    pub(super) fn check_fn_call(&mut self, e: ExprId, def: DefId, r: Option<Clock>) {
        let Some(f) = self.a.def(def).as_fn().filter(|_| self.checking()) else { return };
        let span = self.ast.expr(e).span;
        let name = &self.a.def(def).name;
        if f.takes_inout_self() && self.inout_call.is_none() {
            let msg = format!("`{name}` takes `inout self`, and a flow body cannot call it (§5.2, §11.2)");
            self.inout_call = Some(Diagnostic::new(Stage::Flow, Code::E0713, span, msg).with_found(self.src(span)));
        }
        if !f.effects.effects().is_empty() {
            let msg = format!("`{name}` has effects; a flow calls effect-free functions only (§11.5)");
            self.err(Code::E0805, span, msg);
        } else if !f.rt && readable_at(r.unwrap_or(Clock::Const), Clock::Init).is_err() {
            let msg = format!(
                "`{name}` is not `rt` and takes arguments at the clock `init` or constants only; mark it `rt` or pass values at `init` (§11.5)"
            );
            self.err(Code::E0805, span, msg);
        }
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

    /// The first argument `first` of a delay, at the clock `c`, holds its
    /// state (§11.4, E0813); a name or a literal at `block` has the note of
    /// the form at `sample`.
    pub(super) fn check_first(&mut self, delay: Delay, first: ExprId, c: Clock) {
        if !self.checking() || holds_state(c) {
            return;
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
        if c == Clock::Block && name_or_literal(self.ast, first) {
            diag = diag.with_note(span, format!("write `{d}~({src} at sample)` to delay it per sample"));
        }
        self.fail(diag);
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
