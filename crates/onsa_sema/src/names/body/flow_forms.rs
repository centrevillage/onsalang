//! What a flow body cannot contain (§11.2, S-125): the E0806 of the names
//! stage (§18.1, S-267), the one place that decides it (D-15). The walk
//! reports it at the form, in the order of the text (R-286), and does not
//! read the names in it: a statement other than a `let` of the top level, a
//! block with statements, an anonymous function, `?`, `move`, `handle`,
//! `unsafe`, an `inout` or `move` argument of any call (R-342), and a
//! function value (a variant with elements included, S-195), and a body
//! with no output. `!(` and `.(` are decided with the other marks of a
//! call (`flow.rs`).

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, Ast, ExprId, ExprKind, Mode, StmtId, StmtKind};
use onsa_syntax::binds_as_written;

use super::calls::Called;
use super::paths::{Head, Place};
use super::{BindingKind, Fail, PathRes, Stop, W, Walker};

/// A form of an expression that a flow body cannot contain (§11.2), by
/// its kind: the one predicate of the E0806 of the walk and of the types
/// stage's stop at it (`Checker::check_flow_expr`, D-15).
#[derive(Clone, Copy)]
pub(crate) enum NoFlowForm {
    /// A block with statements, at the first of them: a nested block
    /// holds one expression (the body's are its `let`s).
    Stmts(StmtId),
    Closure,
    Handle,
    Unsafe,
    Try,
    Move,
}

/// The form of `e` that a flow body cannot contain, if it is one. The
/// marks of a call, its arguments and a function value are of the names
/// (`flow.rs`, [`Walker::flow_arg`], [`Walker::function_value`]).
pub(crate) fn no_flow_form(ast: &Ast, e: ExprId) -> Option<NoFlowForm> {
    Some(match &ast.expr(e).kind {
        ExprKind::Block(b) => return b.stmts.first().map(|&s| NoFlowForm::Stmts(s)),
        ExprKind::Closure { .. } => NoFlowForm::Closure,
        ExprKind::Handle { .. } => NoFlowForm::Handle,
        ExprKind::Unsafe(_) => NoFlowForm::Unsafe,
        ExprKind::Try(_) => NoFlowForm::Try,
        ExprKind::Move(_) => NoFlowForm::Move,
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Hole
        | ExprKind::Error
        | ExprKind::Paren(_)
        | ExprKind::Tuple(_)
        | ExprKind::Array(_)
        | ExprKind::Repeat { .. }
        | ExprKind::Struct { .. }
        | ExprKind::If { .. }
        | ExprKind::Match { .. }
        | ExprKind::Par { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Cast { .. }
        | ExprKind::At { .. }
        | ExprKind::Feedback(_)
        | ExprKind::Unary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Field { .. }
        | ExprKind::TypeArgs { .. }
        | ExprKind::TupleIndex { .. }
        | ExprKind::Index { .. }
        | ExprKind::Range(_) => return None,
    })
}

const FUNCTION_VALUES: &str = "function values; call the function directly";
const ASSIGNMENT: &str = "assignment; every signal is defined once by `let`";

impl Walker<'_> {
    /// E0806 at `span` for `what`, which a flow body cannot contain.
    // S-1100: the names stage does not read the names in a form of E0806,
    // so `nope(x)?`, `nope = x` and the statement `nope(x)` are the E0806 of
    // the whole form, not the E0302 of `nope` that starts with it.
    fn forbidden(&mut self, span: Span, what: &str) -> Stop {
        self.e0806(span, format!("a flow body cannot contain {what} (§11.2)"))
    }

    fn e0806(&mut self, span: Span, msg: String) -> Stop {
        let d = self.e0806_at(span, msg);
        self.fail(Fail::Report(d))
    }

    fn e0806_at(&self, span: Span, msg: String) -> Diagnostic {
        Diagnostic::new(Stage::Names, Code::E0806, span, msg).with_found(self.src(span))
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
            StmtKind::Assign { target, value } if !nested => return self.flow_assign(s, *target, *value),
            StmtKind::Assign { .. } => ASSIGNMENT,
            StmtKind::For { .. } => "`for`; a flow body has no loops (use `par~` to replicate structure)",
            StmtKind::While { .. } => "`while`; a flow body has no loops",
            StmtKind::Break | StmtKind::Continue => "loop control; a flow body has no loops",
            StmtKind::Return(_) => "`return`; the output is the final expression",
            StmtKind::Assert(_) => "`assert`; checks are written as tests on `render` (§11.8)",
            StmtKind::Expr(_) => "an expression statement; a flow body is `let`s followed by one output expression",
        };
        self.forbidden(self.ast.stmt(s).span, what)
    }

    /// E0806 at the assignment `s` of `value` to `target` at the top level
    /// of a flow body (§11.2, §18.1, R-59). To a name not defined yet, the
    /// candidate writes `let` before it, only when it leaves no error of the
    /// names stage (§18.1): `let` binds the name as written (no E0002, no
    /// E0320), the value walks clean with the name a `let` defined below
    /// (read as `^name` in the first argument of a delay only, §11.2, and no
    /// other error of its names; one that writes a type is not read so and
    /// has none), and the body has its output after
    /// it. To a name a `let` defined, the note of the accumulation of §18.1
    /// and no candidate.
    // S-1102: a tuple or a field as the target has no candidate.
    // S-1105: to an input, an item, a type or a builtin name, no note: `let
    // x = prev~(^x) + x` would be an E0304 or an E0320.
    fn flow_assign(&mut self, s: StmtId, target: ExprId, value: ExprId) -> Stop {
        let d = self.e0806_at(self.ast.stmt(s).span, format!("a flow body cannot contain {ASSIGNMENT} (§11.2)"));
        let ExprKind::Path(p) = &self.ast.expr(target).kind else { return self.fail(Fail::Report(d)) };
        let [name] = &p.segments[..] else { return self.fail(Fail::Report(d)) };
        let output = matches!(&self.ast.expr(self.root).kind, ExprKind::Block(b) if b.tail.is_some());
        let head = self.head(&[name], &[target], Place::Value);
        // The target is no read (§5.1), as of an assignment of the fn world.
        self.unread(&name.name);
        let by_let = match &head {
            Head::Done((records, None)) => {
                matches!(records[..], [PathRes::Local(b)] if self.out.bindings[b.0 as usize].kind == BindingKind::FlowLet)
            }
            _ => false,
        };
        let d = match head {
            Head::NotFound if output && binds_as_written(&name.name) && self.walks_clean_as_let(name, s, value) => {
                let at = d.span;
                d.with_fix(Fix::insert("define it with `let`", at.file, at.start, "let "))
            }
            _ if by_let => d.with_rule(format!(
                "a value that accumulates is written with a delay: `let {0} = prev~(^{0}) + x` (§11.2)",
                name.name
            )),
            _ => d,
        };
        self.fail(Fail::Report(d))
    }

    /// Whether the walk of the value `e` stops nowhere and finds no type in
    /// it (whose names are read later, `lower_types`), with nothing reported
    /// (S-1100) and its instances taken back (no edges of E0817).
    pub(super) fn walks_clean(&mut self, e: ExprId) -> bool {
        let (sites, instances) = (self.type_sites.len(), self.out.instances.len());
        let clean = self.expr(e).is_ok() && self.type_sites.len() == sites;
        self.type_sites.truncate(sites);
        self.out.instances.truncate(instances);
        self.out.instance_of.retain(|_, k| *k < instances);
        clean
    }

    /// E0806 at the closing brace of the flow body `body` with no output
    /// expression (§11.2), after its statements.
    // S-1101: a body with no output is E0806 at its `}`.
    pub(super) fn no_output(&mut self, body: ExprId) -> Stop {
        let span = self.ast.expr(body).span;
        let msg = "a flow body ends with its output expression (§11.2)";
        self.e0806(Span { start: span.end.saturating_sub(1), ..span }, msg.into())
    }

    /// E0806 at the expression `e` of a flow body when its form is one a
    /// flow body cannot contain, before its names.
    pub(super) fn flow_expr(&mut self, e: ExprId) -> W {
        let what = match no_flow_form(self.ast, e) {
            None => return Ok(()),
            Some(NoFlowForm::Stmts(s)) => return Err(self.flow_stmt(s, true)),
            Some(NoFlowForm::Closure) => "an anonymous function; flows call named `rt` functions only",
            Some(NoFlowForm::Handle) => "`handle`; flows have no effects",
            Some(NoFlowForm::Unsafe) => "`unsafe`",
            Some(NoFlowForm::Try) => "`?`; a flow has no error path",
            Some(NoFlowForm::Move) => "`move`; signals are values and are never moved",
        };
        Err(self.forbidden(self.ast.expr(e).span, what))
    }

    /// E0806 at the argument `a` of a call of a flow body (an instance, a
    /// delay, a function or a method) with `inout` or `move` (R-342), before
    /// its names.
    pub(super) fn flow_arg(&mut self, a: &Arg) -> W {
        // S-1099: at the argument with its mark (`inout x`), as of an instance
        // before.
        match a.mode {
            Mode::Borrow => Ok(()),
            _ => Err(self.forbidden(a.span, "`inout` / `move` arguments; signals are read-only values")),
        }
    }

    /// E0806 at the chain of names `e` at the place of a value of a flow body
    /// whose names were found, when the value it stops at (before the fields
    /// after it, `g.y`) is a function value: what is called as `f(x)` (a
    /// function, a variant with elements, S-195), through the type
    /// arguments after it (`id::[F32].y`), which are not read (`id::[Nope]`).
    pub(super) fn function_value(&mut self, e: ExprId, sites: usize) -> W {
        let mut at = super::named(self.ast, e);
        while let (None, ExprKind::Field { base, .. }) = (self.out.paths.get(&at), &self.ast.expr(at).kind) {
            at = super::named(self.ast, *base);
        }
        match self.out.paths.get(&at).map(|r| self.called(r)) {
            Some(Called::Item) => {
                self.type_sites.truncate(sites);
                Err(self.forbidden(self.ast.expr(at).span, FUNCTION_VALUES))
            }
            _ => Ok(()),
        }
    }

    /// E0806 at the receiver of the method of the call whose callee is
    /// `callee` (`g` of `g.foo(x)`), when it is a function value
    /// ([`Self::function_value`]): no record at the callee.
    pub(super) fn function_receiver(&mut self, callee: ExprId, sites: usize) -> W {
        match super::receiver(self.ast, callee) {
            Some(base) if !self.out.paths.contains_key(&super::named(self.ast, callee)) => {
                self.function_value(base, sites)
            }
            _ => Ok(()),
        }
    }

    /// E0806 at the hole `span` of a string whose names stop at `last`, a
    /// function value ([`Self::function_value`]).
    pub(super) fn function_in_hole(&self, last: &PathRes, span: Span) -> Option<Diagnostic> {
        (self.flow && self.called(last) == Called::Item)
            .then(|| self.e0806_at(span, format!("a flow body cannot contain {FUNCTION_VALUES} (§11.2)")))
    }
}
