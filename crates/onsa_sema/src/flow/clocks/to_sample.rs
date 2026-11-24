//! The candidate of the E0815 of an event value given to a `block` input
//! (§11.11): the declaration of the input `at sample`. It reads the body of
//! the called flow as it is written and the names of it alone, so it does not
//! depend on the order the flows are checked in.

use onsa_syntax::ast::{CallKind, ExprKind};

use super::*;
use crate::clock::readable_at;
use crate::names::body::{Binding, BindingId, BindingKind, PathRes};

impl Walk<'_> {
    /// The candidate of an event value at `c`, the argument of the `block`
    /// input `input` of `g`: its declaration `at sample`, of a flow of this
    /// package (§18.1) with no error before its body is checked, when the
    /// call then reads the event there, the type is one a `sample` input takes
    /// (§11.6), with no `@param`, and the body stays with no new error at the
    /// clock `sample` ([`joined_to_output`]).
    pub(super) fn to_sample_input(&self, c: Clock, input: &FlowInput, g: DefId) -> Option<Fix> {
        let (a, def) = (self.a, self.a.def(g));
        let at = input.clock_span.filter(|_| input.caller_clock() == Clock::Block && input.param.is_none())?;
        let own = a.modules.is_own(def.module) && !a.failures.failed(g);
        let reads = matches!(c, Clock::Event(_)) && readable_at(c, self.frame.tick()).is_ok();
        if !(own && reads && a.crosses_as_input(input.ty)) {
            return None;
        }
        let f = def.as_flow().filter(|f| f.out_clock == Clock::SAMPLE)?;
        let names = a.names.get(&g).filter(|n| n.complete)?;
        let ast = &a.modules.source(self.flat, def.module)?.parsed.ast;
        let bound = |b: &Binding| b.kind == BindingKind::FlowInput && b.name == input.name;
        let p = BindingId(names.bindings.iter().position(bound)? as u32);
        let title = format!("declare the input `{}` of `{}` `at sample`", input.name, def.name);
        joined_to_output(ast, names, f.body, p).then(|| Fix::replace(title, at, Clock::SAMPLE.shown(at)))
    }
}

/// Whether every read of the input `p` in the body `body` of a flow whose
/// output is at `sample` is an operand of the output, through expressions
/// whose clock is the join of their operands' (§11.3) and that take no clock
/// of their own: then the other operands on the way are at `sample` or
/// slower kinds as the output is, and join a `p` at `sample` too. A read in a
/// `let`, under `at`, in an argument of a `~` and in a replication is none.
/// Linear in the body.
fn joined_to_output(ast: &Ast, names: &BodyNames, body: ExprId, p: BindingId) -> bool {
    let mut todo = vec![(body, true)];
    while let Some((x, joined)) = todo.pop() {
        if !joined && matches!(names.paths.get(&x), Some(PathRes::Local(b)) if *b == p) {
            return false;
        }
        let part = |y: ExprId| match &ast.expr(x).kind {
            ExprKind::Block(b) => b.tail == Some(y),
            ExprKind::Call { kind, .. } => matches!(kind, CallKind::Plain),
            ExprKind::If { tilde, .. } => tilde.is_none(),
            ExprKind::Paren(_) | ExprKind::Unary { .. } | ExprKind::Binary { .. } | ExprKind::Cast { .. } => true,
            ExprKind::Field { .. } | ExprKind::TupleIndex { .. } | ExprKind::Index { .. } => true,
            ExprKind::Tuple(_) | ExprKind::Array(_) | ExprKind::Struct { .. } => true,
            _ => false,
        };
        todo.extend(ast.sub_exprs(x).into_iter().map(|y| (y, joined && part(y))));
    }
    true
}
