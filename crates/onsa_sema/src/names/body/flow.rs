//! The `~` of the calls of a flow body (§2.6, §11.2, §11.5; S-267, S-811),
//! which the walk decides by the name of the callee, after the errors of
//! its names and before its arguments (§18.1, R-286). A flow and a builtin
//! delay are called with `~(` (E0811 without it, the E0806 of §11.2 with
//! `!(`, S-813); a `~` on anything else is the E0812 of §2.6, whose candidate
//! takes the `~` off only when the callee is called so (S-590, S-817). An
//! instance of a flow is recorded here, the one place that decides it
//! ([`super::BodyNames::instances`], D-15). The `~` of the branches and of
//! `if~` / `match~` is the flow stage's (§18.1).

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, CallKind, ExprId, Ident, Mode};

use super::calls::Called;
use super::paths::span_of;
use super::{Fail, PathRes, W, Walker};
use crate::DefId;
use crate::flow_names::FlowBuiltin;

/// What the callee of a call is to its `~` (the rows of §2.6).
#[derive(Clone, Copy)]
enum Mark {
    /// What holds state, called with `~`.
    Stateful(Stateful),
    /// What is called without `~`: an item called as `f(x)`, `sample_rate`,
    /// `sample_tick`.
    Plain,
    /// A value: of a name, reached in a chain (`x.prev`, `g.y`, `K.y`), or
    /// what is no chain of names (`g(x).y`, `ops[0]`).
    Value,
    /// What is no value and no flow: a type, a module, a trait.
    NoFlow,
}

#[derive(Clone, Copy)]
enum Stateful {
    Flow(DefId),
    /// A builtin delay (`prev`, `delay`, `vdelay`).
    Delay(&'static str),
}

impl Walker<'_> {
    /// The mark of the call `e` of a flow body, whose callee's names are
    /// found: a flow called with `~` is an instance, recorded; a mark that
    /// does not fit the callee stops the walk (S-811).
    pub(super) fn flow_mark(&mut self, e: ExprId, callee: ExprId, kind: CallKind, args: &[Arg]) -> W {
        let mark = match self.out.paths.get(&callee) {
            Some(&PathRes::FlowBuiltin(FlowBuiltin::Delay(d))) => Mark::Stateful(Stateful::Delay(d.name())),
            Some(PathRes::FlowBuiltin(_)) => Mark::Plain,
            Some(r) => match self.called(r) {
                Called::Flow(d) => Mark::Stateful(Stateful::Flow(d)),
                Called::Item => Mark::Plain,
                Called::Value | Called::UnitVariant => Mark::Value,
                Called::Other => Mark::NoFlow,
            },
            // A chain whose names stop at a value, or no chain. A modifier
            // of an instance (`lp~(x).when~(c)`: `when`, `reset_if`, `down`,
            // `up`, §11.10) is a value here until W7-10 reads its table first.
            None => Mark::Value,
        };
        let (span, end) = (self.ast.expr(e).span, self.ast.expr(callee).span.end);
        // The mark is right after the callee (§2.6, §5.2; the syntax stage
        // reports one apart from it, E0020).
        let mark_span = Span { start: end, end: end + 1, ..span };
        let d = match (mark, kind) {
            (Mark::Stateful(Stateful::Flow(d)), CallKind::Flow) => {
                self.out.instance_of.insert(e, self.out.instances.len());
                self.out.instances.push((e, d, self.ast.expr(callee).span));
                return self.plain_args(args);
            }
            (Mark::Stateful(Stateful::Delay(_)), CallKind::Flow) => return self.plain_args(args),
            (Mark::Stateful(what), CallKind::Plain) => {
                let msg = self.stateful(what);
                let fix = Fix::insert("add `~`", span.file, end, "~");
                Diagnostic::new(Stage::Names, Code::E0811, span, msg).with_fix(fix)
            }
            (Mark::Stateful(what), CallKind::Bang) => {
                let msg = format!("a flow body cannot contain a call with `!` (§11.2): {}", self.stateful(what));
                let fix = Fix::new("write `~` in place of `!`", vec![Edit::replace(mark_span, "~")]);
                Diagnostic::new(Stage::Names, Code::E0806, span, msg).with_fix(fix)
            }
            (Mark::Plain, CallKind::Flow) => self.no_flow(e, callee).with_fix(Fix::delete("remove `~`", mark_span)),
            (Mark::Value, CallKind::Flow) => self.no_flow(e, callee).with_rule(
                "`~` marks the call of a flow and of a builtin delay, which is written `prev~(x, …)` (§2.6, §11.4)",
            ),
            (Mark::NoFlow, CallKind::Flow) => self.no_flow(e, callee),
            _ => return Ok(()),
        };
        Err(self.fail(Fail::Report(d.with_found(self.src(span)))))
    }

    /// An `inout` or `move` argument of an instance or a delay is the flow
    /// stage's E0806 (`plain_args`, §11.2) until W7-04 reports it here
    /// (S-267): the walk stops at the call.
    fn plain_args(&mut self, args: &[Arg]) -> W {
        match args.iter().any(|a| a.mode != Mode::Borrow) {
            true => Err(self.fail(Fail::Later)),
            false => Ok(()),
        }
    }

    /// That a flow or a builtin delay is called with `~`.
    fn stateful(&self, what: Stateful) -> String {
        match what {
            Stateful::Flow(d) => format!(
                "`{}` is a flow; calling it creates a stateful instance and needs `~` (§2.6)",
                self.a.def(d).name
            ),
            Stateful::Delay(name) => {
                format!("`{name}` is a built-in delay; it holds state and is written `{name}~(…)` (§2.6, §11.4)")
            }
        }
    }

    /// E0812 for the `~` of the call `e` on the callee `callee`, no flow
    /// (§2.6), with no candidate.
    fn no_flow(&self, e: ExprId, callee: ExprId) -> Diagnostic {
        let shown = self.src(self.ast.expr(callee).span);
        let msg = format!("`{shown}` is not a flow; `~` creates a flow instance and is written on flows only (§2.6)");
        Diagnostic::new(Stage::Names, Code::E0812, self.ast.expr(e).span, msg)
    }

    /// E0812 for the `~` of the call `e` after the method `segs` named
    /// through its type (`P.get~(p)`, S-814), with no candidate.
    pub(super) fn tilde_on_method(&self, e: ExprId, segs: &[&Ident]) -> Diagnostic {
        let (span, method) = (self.ast.expr(e).span, self.src(span_of(segs)));
        let msg = format!("`{method}` is a method, not a flow; `~` is written on flows only (§2.6)");
        let rule = format!("a method is called on a value, `value.{}(…)` (§6.2)", segs[segs.len() - 1].name);
        Diagnostic::new(Stage::Names, Code::E0812, span, msg).with_found(self.src(span)).with_rule(rule)
    }
}
