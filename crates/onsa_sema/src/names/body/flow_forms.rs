//! What a flow body cannot contain (§11.2, S-125): the E0806 of the names
//! stage (§18.1, S-267), the one place that decides it (D-15). The walk
//! reports it at the form, in the order of the text (R-286), and does not
//! read the names in it: a statement other than a `let` of the top level, a
//! block with statements, an anonymous function, `?`, `move`, `handle`,
//! `unsafe`, an `inout` or `move` argument of any call (R-342), and a
//! function value (a variant with elements included, S-195). `!(` and `.(`
//! are the flow stage's until W7-04 U1b.

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{Arg, ExprId, ExprKind, Mode, StmtId, StmtKind};

use super::calls::Called;
use super::{Fail, Stop, W, Walker};

impl Walker<'_> {
    /// E0806 at `span` for `what`, which a flow body cannot contain.
    // SPEC-GAP(S-1100): §18.1 orders the diagnostics by their start and then
    // their end, and does not say whether the names stage reads the names in
    // a form of E0806 (as §4.5 says of a constant expression): here it does
    // not, so `nope(x)?`, `nope = x` and the statement `nope(x)` are the E0806
    // of the whole form, not the E0302 of `nope` that starts with it.
    fn forbidden(&mut self, span: Span, what: &str) -> Stop {
        self.e0806(span, format!("a flow body cannot contain {what} (§11.2)"))
    }

    fn e0806(&mut self, span: Span, msg: String) -> Stop {
        let d = Diagnostic::new(Stage::Names, Code::E0806, span, msg).with_found(self.src(span));
        self.fail(Fail::Report(d))
    }

    /// E0806 at the statement `s` of a flow body that is no `let` of its top
    /// level (`walk_flow` walks those): any statement, a `let` of a nested
    /// block (`nested`) too.
    pub(super) fn flow_stmt(&mut self, s: StmtId, nested: bool) -> Stop {
        let what = match &self.ast.stmt(s).kind {
            StmtKind::Let { .. } if nested => {
                let msg =
                    "`let` is written at the top level of a flow body only; nested blocks hold one expression (§11.2)";
                return self.e0806(self.ast.stmt(s).span, msg.into());
            }
            StmtKind::Let { .. } => onsa_diag::internal::bug(Some(self.ast.stmt(s).span), "a `let` of the top level"),
            StmtKind::Var { .. } => "`var`; a flow has no mutable variables, state lives in `prev~` / `delay~`",
            StmtKind::Assign { .. } => "assignment; every signal is defined once by `let`",
            StmtKind::For { .. } => "`for`; a flow body has no loops (use `par~` to replicate structure)",
            StmtKind::While { .. } => "`while`; a flow body has no loops",
            StmtKind::Break | StmtKind::Continue => "loop control; a flow body has no loops",
            StmtKind::Return(_) => "`return`; the output is the final expression",
            StmtKind::Assert(_) => "`assert`; checks are written as tests on `render` (§11.8)",
            StmtKind::Expr(_) => "an expression statement; a flow body is `let`s followed by one output expression",
        };
        self.forbidden(self.ast.stmt(s).span, what)
    }

    /// E0806 at the expression `e` of a flow body when its form is one a
    /// flow body cannot contain, before its names.
    pub(super) fn flow_expr(&mut self, e: ExprId) -> W {
        let what = match &self.ast.expr(e).kind {
            ExprKind::Block(b) if !b.stmts.is_empty() => return Err(self.flow_stmt(b.stmts[0], true)),
            ExprKind::Closure { .. } => "an anonymous function; flows call named `rt` functions only",
            ExprKind::Handle { .. } => "`handle`; flows have no effects",
            ExprKind::Unsafe(_) => "`unsafe`",
            ExprKind::Try(_) => "`?`; a flow has no error path",
            ExprKind::Move(_) => "`move`; signals are values and are never moved",
            _ => return Ok(()),
        };
        Err(self.forbidden(self.ast.expr(e).span, what))
    }

    /// E0806 at the argument `a` of a call of a flow body (an instance, a
    /// delay, a function or a method) with `inout` or `move` (R-342), before
    /// its names.
    pub(super) fn flow_arg(&mut self, a: &Arg) -> W {
        // SPEC-GAP(S-1099): at the argument with its mark (`inout x`), as of
        // an instance before.
        match a.mode {
            Mode::Borrow => Ok(()),
            _ => Err(self.forbidden(a.span, "`inout` / `move` arguments; signals are read-only values")),
        }
    }

    /// E0806 at the chain of names `e` at the place of a value of a flow body
    /// whose names were found, when the value it stops at (before the fields
    /// after it, `g.y`) is a function value: what is called as `f(x)` (a
    /// function, a variant with elements, S-195). The type arguments after
    /// it are not read (`id::[Nope]`).
    pub(super) fn function_value(&mut self, e: ExprId, sites: usize) -> W {
        let mut at = super::named(self.ast, e);
        while let (None, ExprKind::Field { base, .. }) = (self.out.paths.get(&at), &self.ast.expr(at).kind) {
            at = *base;
        }
        match self.out.paths.get(&at).map(|r| self.called(r)) {
            Some(Called::Item) => {
                self.type_sites.truncate(sites);
                let what = "function values; call the function directly";
                Err(self.forbidden(self.ast.expr(at).span, what))
            }
            _ => Ok(()),
        }
    }
}
