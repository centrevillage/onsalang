//! The modifiers of an instance in a flow body (§11.9, §11.10; S-555,
//! S-556, S-811): `.name~(` is looked up in the closed list ([`Modifier`])
//! only when its head is the call of an instance (a flow, a built-in delay,
//! a modifier), and a modifier read so is recorded here, the one place that
//! decides it ([`super::BodyNames::modifiers`], D-15). The rows of the
//! receiver, the mark and the name; the others are the rows of §2.6
//! (`flow.rs`). The names of the receiver come first (S-818 (a)): the walk
//! is here after them.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{CallKind, ExprId, ExprKind};
use serde::{Deserialize, Serialize};

use super::{Fail, PathRes, W, Walker};
use crate::flow_names::{Delay, FlowBuiltin, Modifier};

/// The call of a modifier (`lp~(x).down~(2)`).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub(crate) struct ModifierCall {
    pub modifier: Modifier,
    /// The call before the `.` (`lp~(x)`).
    pub receiver: ExprId,
    /// The first call of its chain (§11.9), made once of the record of its
    /// receiver: the one place that finds it (D-15).
    pub head: ExprId,
    /// The name of the modifier, the place of its E0200 of this version.
    pub name: Span,
}

/// What the receiver of `.name~(` is to the modifiers (§11.10): the call
/// of a flow or of a modifier, of a built-in delay, or else a value (a name
/// bound by `let`, `par~`, `if~` / `match~`).
#[derive(Clone, Copy)]
enum Receiver {
    Instance,
    Delay(Delay),
    Value,
}

impl Walker<'_> {
    /// The modifier of the call `e` whose callee `callee` is a member of a
    /// value, `recv.name` (§11.10): recorded, or its error; `None` where the
    /// rows of §2.6 decide the call as before (a method, `.(`, a `~` of a
    /// name not in the list on a value).
    pub(super) fn modifier_mark(&mut self, e: ExprId, callee: ExprId, kind: CallKind) -> Option<W> {
        // The form is `.name~(` (§11.10).
        // S-1201: with type arguments (`.when::[I32]~(c)`) the rows of §2.6, as
        // before.
        let ExprKind::Field { base, name } = &self.ast.expr(callee).kind else { return None };
        // S-1181: a head through its parentheses (`(lp~(x)).down~(2)`), as
        // fmt writes it; the receiver is as written.
        let inner = self.ast.without_parens(*base);
        let head = self.out.modifiers.get(&inner).map_or(inner, |m| m.head);
        let (receiver, listed) = (self.receiver_of(head), Modifier::named(&name.name));
        let (span, end) = (self.ast.expr(e).span, self.ast.expr(callee).span.end);
        let shown = &name.name;
        // An instance takes any; a delay `when~` and `reset_if~`, which keep
        // the rate of its first argument (§11.9).
        // S-1091: `down~` and `up~` of a delay are an E0812 of the receiver.
        let takes = |m: Modifier| match receiver {
            Receiver::Instance => true,
            Receiver::Delay(_) => m.ratio_op().is_none(),
            Receiver::Value => false,
        };
        let d = match (kind, listed, receiver) {
            (CallKind::Flow, Some(m), _) if takes(m) => {
                self.out.modifiers.insert(e, ModifierCall { modifier: m, receiver: *base, head, name: name.span });
                return Some(Ok(()));
            }
            (CallKind::Flow, Some(_), Receiver::Delay(d)) => {
                let msg = format!("the built-in delay `{}~` takes no `.{shown}~` (§11.4)", d.name());
                let rule = format!(
                    "a delay ticks at the clock of its first argument, which `.{shown}~` would set its chain apart from \
                     (§11.4, §11.9); write the delay in a flow, and `.{shown}~` after the call of that flow"
                );
                Diagnostic::new(Stage::Names, Code::E0812, span, msg).with_rule(rule)
            }
            (CallKind::Flow, None, Receiver::Value) => return None,
            (CallKind::Flow, ..) => {
                let msg = match listed {
                    None => format!("`{shown}` is not a modifier of an instance (§11.10)"),
                    Some(_) => format!(
                        "`{}` is not the call of an instance, which the modifier `{shown}~` is written after (§11.10)",
                        self.src(self.ast.expr(*base).span)
                    ),
                };
                Diagnostic::new(Stage::Names, Code::E0812, span, msg).with_rule(listed_rule())
            }
            // S-1178: `down` and `up` with no `~` are a method of the value, as
            // before; `when` and `reset_if` are the E0811 of §11.10.
            // S-1202: of a value, a method of the value, as before (E0413).
            // S-1259: no `~` that leads to an E0801 (`prev~(lp~(x).when(^c))`).
            (CallKind::Plain, Some(m), _) if takes(m) && m.ratio_op().is_none() => {
                let msg = format!("`{shown}` is a modifier of an instance, written `.{shown}~(…)` (§11.10)");
                let d = Diagnostic::new(Stage::Names, Code::E0811, span, msg);
                self.add_tilde(e, end, true).into_iter().fold(d, Diagnostic::with_fix)
            }
            // The candidate of S-811: the `!` that a flow body cannot contain
            // (§11.2) to the `~` of the modifier.
            (CallKind::Bang, Some(m), _) if takes(m) => {
                let msg = format!(
                    "a flow body cannot contain a call with `!` (§11.2): `{shown}` is a modifier of an instance, \
                     written `.{shown}~(…)` (§11.10)"
                );
                let fix = Fix::replace("write `~` in place of `!`", Span { start: end, end: end + 1, ..span }, "~");
                Diagnostic::new(Stage::Names, Code::E0806, span, msg).with_fix(fix)
            }
            _ => return None,
        };
        Some(Err(self.fail(Fail::Report(d.with_found(self.src(span))))))
    }

    /// What the head `base` of a chain (a receiver that is no modifier) is,
    /// by the records of the walk of it, which came first.
    fn receiver_of(&self, base: ExprId) -> Receiver {
        match &self.ast.expr(base).kind {
            _ if self.out.instance_of.contains_key(&base) => Receiver::Instance,
            ExprKind::Call { callee, kind: CallKind::Flow, .. } => {
                match self.out.paths.get(&super::named(self.ast, *callee)) {
                    Some(&PathRes::FlowBuiltin(FlowBuiltin::Delay(d))) => Receiver::Delay(d),
                    _ => Receiver::Value,
                }
            }
            _ => Receiver::Value,
        }
    }
}

/// The note of an E0812 of a modifier (§11.10): the receivers and the list.
// S-1085: of a value with a name of the list, this note.
// S-1086: of an instance with a name not in the list too, and of a value
// with one the general note of §2.6.
fn listed_rule() -> String {
    let names: Vec<String> = Modifier::ALL.iter().map(|m| format!("`{}~`", m.name())).collect();
    format!(
        "the modifiers of an instance are {}, written after the call of a flow or of a built-in delay, or after \
         another modifier (`lp~(x).when~(c)`); a name bound by `let`, a value, `par~`, `if~` and `match~` take none \
         (§11.10)",
        names.join(", ")
    )
}
