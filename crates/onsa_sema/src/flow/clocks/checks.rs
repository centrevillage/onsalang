//! The checks of the flow rules at stage 2 of the walk (§11.3–§11.5): each
//! at its place in the walk, which goes on past an error and keeps the first
//! diagnostic in the order of the file (§18.1). A clock in error is no error
//! of a check (§18.1): the comparisons of [`crate::clock`] pass it. The
//! checks on which the rule of the clock of their expression rests give it
//! in error when they fail: the E0813 of a delay, the E0805 and the E0815 of
//! a call of a function (§11.5), `if~` / `match~`, a node in a branch; the
//! others leave it as the rules give it (the `k` of `e at k`, the output of
//! an instance, the clock of a delay by its first argument).

use super::*;
use crate::clock::{holds_state, promote, readable_at};
use crate::requirement::{Required, unmet_error, unmet_rules};

/// Whether `e` is written as a name or a literal, past parentheses and type
/// arguments (not `^name`): the operand `at` makes faster as written (the
/// E0200 of a computed one, W7-05) and the first argument of a delay the
/// candidate of E0813 makes faster.
pub(crate) fn name_or_literal(ast: &Ast, mut e: ExprId) -> bool {
    loop {
        match &ast.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::TypeArgs { base: x, .. } => e = *x,
            k => return matches!(k, ExprKind::Path(_) | ExprKind::Lit(_)),
        }
    }
}

impl Walk<'_> {
    /// Whether the checks run: at `Check`.
    pub(super) fn checking(&self) -> bool {
        self.mode == Mode::Check
    }

    pub(super) fn src(&self, span: Span) -> String {
        found(self.text, span)
    }

    /// A diagnostic of the walk, kept if it is the first (§18.1).
    pub(super) fn report(&mut self, d: Diagnostic) {
        keep_first(&mut self.diag, d);
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
            && let Some(d) = crate::sig::not_copy_signal(self.a, self.ty_of(p.init), p.span)
        {
            let found = self.src(p.span);
            self.report(d.with_found(found));
        }
    }

    /// §11.4: the element type `T` of `vdelay~` at `e` meets `T: Float`
    /// (E0416, R-493).
    pub(super) fn check_float(&mut self, e: ExprId) {
        let ty = self.ty_of(e);
        if matches!(self.a.types.get(ty), Ty::Float(_) | Ty::Error) {
            return;
        }
        let span = self.ast.expr(e).span;
        let (shown, bound) = (self.a.display_type(ty), crate::def::Bound::Float);
        let what = Required::Param { param: "T".into(), owner: format!("`{}~`", Delay::Variable.name()), std: true };
        let mut d = unmet_error(span, &what, &shown, bound, &mut |t| self.a.display_type(t));
        d.stage = Stage::Flow;
        let d = unmet_rules(self.a, ty, &shown, bound).fold(d, Diagnostic::with_rule);
        self.report(d.with_found(self.src(span)));
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
            keep_first(&mut self.inout_call, d);
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
            self.non_rt.insert(e);
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
    /// holds its state (§11.4, E0813); a name or a literal of a parameter
    /// kind has the candidate `first at sample` (S-102; a computed one
    /// waits for W7-05).
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
        if matches!(c, Clock::Const | Clock::Init | Clock::Block) && name_or_literal(self.ast, first) {
            let fix = Fix::insert(
                format!("write `{src} at sample` to delay it per sample"),
                span.file,
                span.end,
                " at sample",
            );
            diag = diag.with_fix(fix);
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
