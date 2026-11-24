//! The checks of the flow rules at stage 2 of the walk (§11.3–§11.5): each
//! at its place in the walk, which goes on past an error and keeps the first
//! diagnostic in the order of the file (§18.1). Those that give a clock in
//! error decide it in every mode too (R-496). A clock in error is no error
//! of a check (§18.1): the comparisons of [`crate::clock`] pass it. The
//! checks on which the rule of the clock of their expression rests give it
//! in error when they fail: the E0813 of a delay, the E0805 and the E0815 of
//! a call of a function (§11.5), a node in a branch (E0811, E0806); the
//! others leave it as the rules give it (the `k` of `e at k`, the output of
//! an instance, the clock of a delay by its first argument, a value whose
//! type holds a function type, E0810). A value made with `Alloc` to drop
//! (E0805) is in error too ([`Walk::fault`]).

use onsa_syntax::ast::{Lit, OperandPlace};
use onsa_syntax::foreign::{self, RowId};

use super::*;
use crate::binding::{aggregate, unit_variant};
use crate::clock::{grounded, keeps_delay_state, promote, readable_at};
use crate::kind::kind_in_body;
use crate::slot::{Form, Slot};

/// Whether `at` makes a value at the clock `c` one at the clock `k`: it is
/// not slower (§11.3). The one predicate of `e at k` ([`Walk::check_at`])
/// and of the candidate of E0813 that writes `first at sample`
/// ([`Walk::check_first`]), which so passes the check of its `at`.
fn promotable(c: Clock, k: Clock) -> bool {
    promote(c, k).is_ok()
}

/// The clock `c` of a value as a diagnostic writes it: `sample_tick()`
/// [`grounded`] (§11.4).
fn shown(c: Clock, at: Span) -> String {
    grounded(c).shown(at)
}

/// The note of the E0815 of `sample_tick()` read at a `sample * N` of the
/// caller (S-1218): the two flows that write its time at the ticks of a
/// burst and copy it, of N = 2.
const SAMPLE_TICK_AT_BURSTS: &str = "here `sample_tick()` is the time at the `sample` of this body (§11.4); a conversion flow makes the time of each tick, as `flow mkt() -> U32 at (sample * 2) { [sample_tick() *% 2, sample_tick() *% 2 +% 1] }`, or copies a value to each, as `flow hold2(x: U32 at sample) -> U32 at (sample * 2) { [x, x] }`";

/// The tick `tick` as a title names it: `sample`, ``tick of `sample / 2` ``.
pub(super) fn per_tick(tick: Clock, at: Span) -> String {
    let shown = tick.shown(at);
    if tick == Clock::SAMPLE { shown } else { format!("tick of `{shown}`") }
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

/// The branching an `if~` or a `match~` is ([`Walk::check_tilde`]): its
/// word and what its parts are called.
#[derive(Debug, Clone, Copy)]
pub(super) enum Branching {
    If,
    Match,
}

impl Branching {
    fn words(self) -> (&'static str, &'static str) {
        match self {
            Branching::If => ("if", "branches"),
            Branching::Match => ("match", "arms"),
        }
    }
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

    pub(super) fn ty_of(&self, e: ExprId) -> TyId {
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
            let (shown, to) = (shown(c, span), k.shown(span));
            let msg = format!(
                "this expression is at the clock `{shown}`, faster than `{to}`; `at` cannot make a value slower (§11.3)"
            );
            self.err(Code::E0815, span, msg);
        }
    }

    /// The E0815 at `e` of two operands whose clocks do not meet (§11.3,
    /// M-7), with a note at the expression of each. `looped`: they enter one
    /// loop of `let`s, which has one clock, and `e` is the initializer of the
    /// `let` that the second enters.
    // SPEC-GAP(S-1198): the E0815 of a loop of `let`s is one, at the
    // initializer of the `let` that the second operand enters (provisional).
    // SPEC-GAP(S-1083): `sample * N` of the caller with another operand is
    // this E0815 (provisional).
    pub(super) fn report_clash(&mut self, e: ExprId, ops: Clashed, looped: bool) {
        let span = self.ast.expr(e).span;
        let [a, b] = ops.map(|(_, c)| shown(c, span));
        let events = ops.iter().all(|(_, c)| matches!(c, Clock::Event(_)));
        let what = if looped { "operands that enter a loop of `let`s, which has one clock," } else { "operands" };
        let msg = match ops.iter().find(|(_, c)| c.burst()) {
            Some((_, c)) => format!(
                "a value at `{}` takes no operation at the call side for now; a conversion flow takes it (§11.9)",
                c.shown(span)
            ),
            None if events => {
                format!(
                    "the {what} are at the clocks of two events, which have no order and do not meet (§11.3, §11.11)"
                )
            }
            None => format!("the {what} are at the clocks `{a}` and `{b}`, which do not meet (§11.3, §11.9)"),
        };
        let mut d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
        for (x, c) in ops.iter().filter_map(|&(x, c)| Some((x?, c))) {
            let at = self.event_name(c).unwrap_or_else(|| format!("`{}`", shown(c, span)));
            d = d.with_note(self.ast.expr(x).span, format!("this operand is at {at}"));
        }
        if events {
            let rule = "write `at` on each event value, which reads its last value at that clock (`(a at sample) + b`, §11.11); `at` around the expression does not help";
            return self.report(d.with_rule(rule));
        }
        let rule = "a slower value is read at a faster clock with `at` (`a at sample`), and a value at `sample * N` meets no other for now (§11.3, §11.9)";
        self.report(d.with_rule(rule));
    }

    /// The event clock `c` as a note names it, by its source: none of another
    /// clock.
    pub(super) fn event_name(&self, c: Clock) -> Option<String> {
        let Clock::Event(src) = c else { return None };
        Some(match src.place(self.cx.inputs.len()) {
            Err(i) => {
                let l = self.cx.inputs.get(i)?;
                format!("the event clock of `{}`", self.body.locals[l.0 as usize].name)
            }
            Ok(i) => match self.cx.calls.get(i)?.kind {
                NodeKind::Instance(g) => {
                    format!("the event clock of the output of this call of `{}`", self.a.def(g).name)
                }
                NodeKind::Delay(..) => return None,
            },
        })
    }

    /// The E0815 of the `par~` at `e` whose body gives out the event of the
    /// call at `call` in it (§11.5, S-1096).
    pub(super) fn report_par_event(&mut self, e: ExprId, call: Span) {
        let span = self.ast.expr(e).span;
        let msg = "the event of a call in the body of a `par~` is at a clock of its own in each replica, which have no order, so it is no value of the `par~` (§11.5, §11.11)";
        let d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
        let d = d.with_note(call, "this call gives out the event");
        self.report(d.with_rule(
            "give the event to an event input in the body, or write `at sample` on it in the body; `at` outside the `par~` does not help (§11.5)",
        ));
    }

    /// The clock the event input `input` of `g` reads its argument `x`, at
    /// the clock `c`, at: the clock of an event value itself (§11.11). Of
    /// another value E0815 at `x`, and in error.
    pub(super) fn bound_event(&mut self, x: ExprId, c: Clock, input: &FlowInput, g: DefId) -> Clock {
        if matches!(c, Clock::Event(_) | Clock::Error) {
            return c;
        }
        let span = self.ast.expr(x).span;
        let msg = format!(
            "this argument is at the clock `{}` but the input `{}` of `{}` is at `{}`, which takes an event value (§11.11)",
            shown(c, span),
            input.name,
            self.a.def(g).name,
            crate::clock::EVENT
        );
        let d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
        self.report(d.with_rule(
            "an event value is an event input of the flow, the event output of a call, or an expression of one of them with values at `block`, `init` or of constants",
        ));
        Clock::Error
    }

    /// The `if~` / `match~` (`of` and its `~` `tilde`) whose branches or
    /// arm bodies are `bodies` and whose first condition or scrutinee is
    /// `next` (§11.5, S-1177): E0812 at its `~` (S-392) when no body holds
    /// state, with the candidate that takes the `~` off (a space before a
    /// `next` it touches). Its clock stays the join of its parts.
    // SPEC-GAP(S-392): the main place of the E0812 is the `~` (provisional).
    // SPEC-GAP(S-1191): a later condition or a guard with state is no
    // branch, so not counted: E0812 too (provisional).
    // SPEC-GAP(S-1192): the `if~` / `match~` of the E0812 keeps its clock, as
    // a `par~` that holds none (provisional).
    pub(super) fn check_tilde(
        &mut self,
        tilde: Span,
        of: Branching,
        mut bodies: impl Iterator<Item = ExprId>,
        next: ExprId,
    ) {
        if bodies.any(|x| super::super::nodes::holds_state(self.ast, x)) {
            return;
        }
        let (word, parts) = of.words();
        let msg = format!("this `{word}~` holds no state in its {parts} and is written `{word}` (§2.6, §11.5)");
        let touches = self.ast.expr(next).span.start == tilde.end;
        let fix = Fix::replace("remove `~`", tilde, if touches { " " } else { "" });
        let d = Diagnostic::new(Stage::Flow, Code::E0812, tilde, msg).with_found(self.src(tilde));
        self.report(d.with_fix(fix));
    }

    /// The bindings of the pattern `pat` of an arm of `match~`, each the
    /// default of its type on a sample that does not take the arm (§11.5):
    /// at `Check`, E0816 at the binding of a type that does not satisfy
    /// `Default`. Its bindings, in the order of the text (none but at
    /// `Check`).
    // SPEC-GAP(S-1174): every binding of every arm, read or not
    // (provisional).
    // SPEC-GAP(S-392): the main place of the E0816 is the binding
    // (provisional).
    pub(super) fn check_arm_bindings(&mut self, pat: PatId) -> Vec<LocalId> {
        let mut bound = Vec::new();
        if !self.checking() {
            return bound;
        }
        let (a, ast, body) = (self.a, self.ast, self.body);
        crate::pat::each_bind(ast, pat, true, &mut |q, name| {
            let Some(&l) = body.pat_locals.get(&q) else { return };
            bound.push(l);
            let (ty, span) = (body.locals[l.0 as usize].ty, ast.pat(q).span);
            let what = format!("the binding `{}` of an arm of `match~`, on a sample that does not take it,", name.name);
            if let Some(d) = crate::signal::no_default_signal(a, ty, span, &what, "§11.5") {
                let found = self.src(span);
                self.report(d.with_found(found));
            }
        });
        bound
    }

    /// The `~` of the replication `e` written with `tilde`, whose body holds
    /// state if `holds` (§11.5, S-1177), at its head (S-392): E0811 of a
    /// `par` that holds it, with the candidate that adds the `~`; E0812 of a
    /// `par~` that holds none, with the one that takes it off (a space
    /// between `par` and its index, which it touches).
    // SPEC-GAP(S-1183): in a branch too, where the E0811 of the branch is
    // left (provisional): the `par`'s, at the same place, comes first.
    pub(super) fn par_mark(&mut self, e: ExprId, tilde: Option<Span>, holds: bool) {
        let span = self.ast.expr(e).span;
        let head = crate::names::body::par_head(span, tilde);
        let (code, msg, fix) = match (tilde, holds) {
            (None, true) => {
                let msg = "this `par` holds state in its body and is written `par~` (§2.6, §11.5)";
                (Code::E0811, msg, Fix::insert("add `~`", span.file, head.end, "~"))
            }
            (Some(t), false) => {
                let ExprKind::Par { var, .. } = &self.ast.expr(e).kind else {
                    onsa_diag::internal::bug(Some(span), "the `~` of no replication")
                };
                let msg = "this `par~` holds no state in its body and is written `par` (§2.6, §11.5)";
                let gap = if var.span.start == t.end { " " } else { "" };
                (Code::E0812, msg, Fix::replace("remove `~`", t, gap))
            }
            _ => return,
        };
        let found = self.src(head);
        self.report(Diagnostic::new(Stage::Flow, code, head, msg).with_found(found).with_fix(fix));
    }

    /// Whether a node or a `par~` at `e`, of the kind `kind` (§11.6), in the
    /// frame `frame` (§11.9; none of a delay), may be here: in no place that
    /// is not evaluated on every sample (§11.5), in every mode (R-496).
    /// Else, at `Check`, the E0811 of a branch, a guard or a later condition
    /// of a chain, or the E0806 of the right of `&&` / `||`, of the innermost
    /// place, at `e` (S-392), with the candidates that can be made (§2.6,
    /// S-394): the `~` of a branch, which leaves the outer places in error
    /// (S-1183), then the lift into a `let`.
    // SPEC-GAP(S-1183): the `~` of the innermost branch, of a place in others
    // (provisional).
    // SPEC-GAP(S-1173): the E0806 at the flow check stage (provisional).
    // SPEC-GAP(S-392): the main place of the E0811 / E0806 is the whole thing
    // with state, `lp~(x)` (provisional).
    // SPEC-GAP(S-1189): the thing in error has the error clock (its callers
    // give `Clock::Error` on false), so an `at` around it reports nothing
    // (provisional).
    pub(super) fn stateful_here(&mut self, e: ExprId, kind: &str, frame: Option<ClockFrame>) -> bool {
        let Some(&site) = self.sites.last() else { return true };
        let span = self.ast.expr(e).span;
        if !self.checking() || self.diag.as_ref().is_some_and(|d| Diagnostic::place_before(d.span, span)) {
            return false;
        }
        let (code, place) = match site {
            Site::Branch { .. } => {
                (Code::E0811, "in a branch of `if` / `match`, evaluated on the samples that take it only")
            }
            Site::Choose => {
                (Code::E0811, "in a guard or a later condition of a chain, evaluated until one is taken only")
            }
            Site::Right => (Code::E0806, "on the right of `&&` / `||`, evaluated when the left does not decide only"),
        };
        let msg = format!("a flow instance, a delay or a `par~` cannot be {place} (§11.5)");
        let mut d = Diagnostic::new(Stage::Flow, code, span, msg).with_found(self.src(span));
        if let Site::Branch { head } = site {
            let at = self.ast.expr(head).span;
            let word = if matches!(self.ast.expr(head).kind, ExprKind::If { .. }) { "if" } else { "match" };
            let title = format!("write `{word}~`, which evaluates every branch");
            d = d.with_fix(Fix::insert(title, at.file, at.start + word.len() as u32, "~"));
        }
        if let Some(fix) = self.lift(e, kind, frame) {
            d = d.with_fix(fix);
        }
        self.report(d);
        false
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
    /// (§11.5), in every mode (R-496): no effects (E0805), and a function
    /// that is not `rt` takes values at `init` or constants only (E0815,
    /// S-147), which `ops` that read a ⊥ (`partial`, [`Walk::bottoms`]) do
    /// not decide. At `Check`, those reported, the first `inout self` call held
    /// (E0713, §5.2), and a call of a function not `rt` recorded for the
    /// marking. With E0805 or that E0815 the rule of its clock fails, and the
    /// call is in error (§18.1).
    pub(super) fn check_fn_call(
        &mut self,
        e: ExprId,
        def: DefId,
        receiver: bool,
        ops: (&[Op], bool),
        r: Option<Clock>,
    ) -> bool {
        let (Some(f), (ops, partial)) = (self.a.def(def).as_fn(), ops) else { return true };
        let (check, span) = (self.checking(), self.ast.expr(e).span);
        let name = &self.a.def(def).name;
        if check && f.takes_inout_self() {
            let msg = format!("`{name}` takes `inout self`, and a flow body cannot call it (§5.2, §11.2)");
            let d = Diagnostic::new(Stage::Flow, Code::E0713, span, msg).with_found(self.src(span));
            Diagnostic::keep_first(&mut self.inout_call, d);
        }
        if !f.effects.effects().is_empty() {
            if check {
                let msg = format!("`{name}` has effects; a flow calls effect-free functions only (§11.5)");
                self.err(Code::E0805, span, msg);
            }
            return false;
        }
        if f.rt || r == Some(Clock::Error) || partial {
            return true;
        }
        let fast = |o: &Op| readable_at(o.1.unwrap_or(Clock::Const), Clock::Init).is_err();
        let Some(k) = ops.iter().position(fast) else {
            if check {
                self.non_rt.insert(e, ops.iter().any(|o| o.1.is_some_and(|c| c != Clock::Const)));
            }
            return true;
        };
        if !check {
            return false;
        }
        let place = match k.checked_sub(usize::from(receiver)) {
            None => "its receiver".to_string(),
            Some(k) => format!("its argument {}", k + 1),
        };
        let shown = shown(ops[k].1.unwrap_or(Clock::Const), span);
        let msg = format!(
            "`{name}` is not `rt` and takes values at the clock `init` or constants only, but {place} is at `{shown}`; mark it `rt` or pass values at `init` (§11.5)"
        );
        self.err(Code::E0815, span, msg);
        false
    }

    /// The argument `x` at the clock `c` of an instance of `g`, read at
    /// `at`, the clock of its input `input` (§11.3, E0815): to a `sample *
    /// N` of the caller, a value comes through a conversion flow (§11.9),
    /// and `sample_tick()`, which is there of the `sample` of the body
    /// however the argument holds it (§11.4, S-1218), with a note of the
    /// flows that make its time or its copies.
    pub(super) fn check_arg(&mut self, x: ExprId, c: Clock, at: Clock, input: &FlowInput, g: DefId) {
        let time = c == Clock::Ambient && at.burst();
        if !self.checking() || (readable_at(c, at).is_ok() && !time) {
            return;
        }
        let span = self.ast.expr(x).span;
        let (shown, to, name) = (shown(c, span), at.shown(span), &self.a.def(g).name);
        let how = match (promotable(c, at), at.burst()) {
            _ if matches!(c, Clock::Event(_)) && !at.burst() => {
                "an event is read at `sample` and `(sample / N)`, never slower (§11.11)".into()
            }
            (true, _) => format!("read it at `{to}` with `at` (§11.3)"),
            (false, true) => "a conversion flow takes it (§11.9)".into(),
            (false, false) => "a value is never made slower (§11.3)".into(),
        };
        let msg = format!(
            "this argument is at the clock `{shown}` but the input `{}` of `{name}` is at `{to}`; {how}",
            input.name
        );
        let d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
        let d = self.to_sample_input(c, input, g).into_iter().fold(d, Diagnostic::with_fix);
        self.report(if time { d.with_note(span, SAMPLE_TICK_AT_BURSTS) } else { d });
    }

    /// The E0816 of the part `g` run at `e` heads, gathered and dealt at a
    /// boundary of its chain (§11.9, S-578, S-1186, S-1207, S-1214,
    /// [`super::super::plan::bounds::bounds`]): of an input a boundary
    /// gathers, whose first tick gathers it before any sample, at its
    /// argument in `args`, and of an output a boundary deals before its
    /// first tick, or a `.when~` holds before it first runs (§11.10), at the
    /// whole chain (S-1203 (1)), of a value type that does not satisfy
    /// `Default` ([`crate::signal::no_default_signal`]). Its type is the same
    /// at every boundary and guard: one of each input and one of the output.
    // SPEC-GAP(S-1203): the places, provisional (1).
    pub(super) fn check_gather_deal(&mut self, e: ExprId, g: DefId, args: &[ExprId]) {
        let (a, name) = (self.a, &self.a.def(g).name);
        // Of a flow with a port in error, none (§18.1).
        let Some(f) = a.def(g).as_flow().filter(|f| !f.ports_in_error) else { return };
        let Some(chain) = self.cx.chains.get(&e) else { return };
        let ports = super::super::plan::bounds::Ports::of(f);
        let (bounds, guards, _) = super::super::plan::bounds::bounds(chain.mods.iter().map(|m| &m.plan), ports);
        let gathered = |i: usize| bounds.iter().any(|b| b.gathers.iter().any(|g| g.0 == Port::Input(i as u32)));
        let mut found = Vec::new();
        for (_, (&x, input)) in args.iter().zip(&f.inputs).enumerate().filter(|&(i, _)| gathered(i)) {
            let what = format!("the part of the input `{}` of `{name}` gathered before the first samples", input.name);
            found.extend(crate::signal::no_default_signal(a, input.ty, self.ast.expr(x).span, &what, "§11.9"));
        }
        let at = chain.mods.last().map_or(e, |m| m.call);
        let what = format!("the array `{name}` deals before its first tick");
        if bounds.iter().any(|b| b.deals) {
            found.extend(crate::signal::no_default_signal(a, f.out, self.ast.expr(at).span, &what, "§11.9"));
        } else if !guards.is_empty() {
            // One error with the dealt array (S-1214 (1)).
            found.extend(self.held_default(e, name));
        }
        for d in found {
            let at = self.src(d.span);
            self.report(d.with_found(at));
        }
    }

    /// The E0816 of the output of `name` at `e` a `.when~` of its chain
    /// holds, of a part that has not run (§11.10, S-558: `T.default()`, an
    /// `init` of a delay too), at the whole chain (S-1203 (1)), of a type
    /// that does not satisfy `Default`; none of a chain with no `.when~`.
    // SPEC-GAP(S-1203): the place, provisional (1).
    pub(super) fn held_default(&self, e: ExprId, name: &str) -> Option<Diagnostic> {
        let chain = self.cx.chains.get(&e)?;
        chain.mods.iter().find(|m| m.plan.modifier == crate::flow_names::Modifier::When)?;
        let at = self.ast.expr(chain.mods.last()?.call).span;
        let what = format!("the output of `{name}` a `.when~` holds before it first runs");
        let d = crate::signal::no_default_signal(self.a, self.ty_of(e), at, &what, "§11.10")?;
        Some(d.with_found(self.src(at)))
    }

    /// The output `out` at the clock `c`, read at `at`, the clock the body
    /// writes the output at (§11.3, §11.9, S-1098 (b): a slower tick is read
    /// with `at`, a value is never made slower, E0815).
    pub(super) fn check_out(&mut self, out: ExprId, c: Clock, at: Clock) {
        if readable_at(c, at).is_ok() {
            return;
        }
        let span = self.ast.expr(out).span;
        let (shown, to) = (shown(c, span), at.shown(span));
        let how = if promotable(c, at) {
            format!("read it at `{to}` with `at`")
        } else {
            "a value is never made slower".into()
        };
        let msg = format!("the output is at the clock `{shown}` but the flow outputs at `{to}`; {how} (§11.3)");
        self.err(Code::E0815, span, msg);
    }

    /// The argument `d` of a `vdelay~`, at the clock `c`, read at `at`, the
    /// clock of the delay: its first argument's, or a parameter kind (§11.4;
    /// a tick of another ratio is read with `at`, §11.3, E0815).
    pub(super) fn check_d(&mut self, d: ExprId, c: Clock, at: Clock) {
        if !self.checking() || readable_at(c, at).is_ok() {
            return;
        }
        let span = self.ast.expr(d).span;
        let (shown, to) = (shown(c, span), at.shown(span));
        let how = match at {
            Clock::Event(_) => {
                "a delay of an event reads values of that event and of the parameter kinds (§11.4, §11.11)".into()
            }
            _ => format!("read it at `{to}` with `at` (§11.3, §11.4)"),
        };
        let msg = format!("the `d` of `vdelay~` is at the clock `{shown}` but the delay is at `{to}`; {how}");
        self.err(Code::E0815, span, msg);
    }

    /// The clock of the first argument of a delay, `c`, when it holds no
    /// state of the delay (§11.4, E0813): in every mode (R-496), but of one
    /// that reads a ⊥ (`partial`, [`Walk::bottoms`]), whose clock is not
    /// known until its loop is solved ([`delay_out`]).
    pub(super) fn first_fails(c: Option<Clock>, partial: bool) -> Option<Clock> {
        c.filter(|&c| !keeps_delay_state(c) && !partial)
    }

    /// The E0813 of the first argument `first` of a delay, at the clock `c`
    /// ([`Self::first_fails`]); one `at` makes `sample` (in the head
    /// of a chain, the tick of its frame, §11.9) ([`promotable`]) has the
    /// candidate `first at sample` (S-102, S-152), in parentheses where `at` takes them (§3.1: `(p * 2.0) at sample`),
    /// unless the walk found an error in it, which the candidate would
    /// leave (§18.1), or it is a `^name`.
    pub(super) fn report_first(&mut self, delay: Delay, first: ExprId, c: Clock) {
        let span = self.ast.expr(first).span;
        let d = delay.name();
        // Of a `.up~` frame, whose ticks keep no state (S-1097), the `sample`.
        let to = self.frame.tick();
        let must = if keeps_delay_state(to) { to } else { Clock::SAMPLE }.shown(span);
        let msg = match c {
            Clock::Const => {
                format!("the first argument of `{d}~` must be at the clock `{must}`; this one is a constant (§11.4)")
            }
            c => format!(
                "the first argument of `{d}~` must be at the clock `{must}`; this one is at `{}` (§11.4)",
                c.shown(span)
            ),
        };
        let src = self.src(span);
        let mut diag = Diagnostic::new(Stage::Flow, Code::E0813, span, msg).with_found(src.clone());
        if !matches!(c, Clock::Tick(_)) {
            let rule = "a delay counts the ticks of its first argument: `at sample` delays per sample, `at (sample / N)` per tick of a slower clock (`prev~(p at (sample / 32))`, §11.4)";
            diag = diag.with_rule(rule);
        }
        let inside = self.diag.as_ref().is_some_and(|d| span.start <= d.span.start && d.span.end <= span.end);
        // SPEC-GAP(S-1165): `^b` (past parentheses and `at`) has no candidate:
        // the error it would leave may be in the `let` of `b`, walked later.
        let mut bare = first;
        while let ExprKind::Paren(x) | ExprKind::At { expr: x, .. } = &self.ast.expr(bare).kind {
            bare = *x;
        }
        let feedback = matches!(self.ast.expr(bare).kind, ExprKind::Feedback(_));
        if promotable(c, to) && !inside && !feedback {
            let wrap = Slot::Operand(OperandPlace::AsAtLeft).wraps(Form::of(self.ast, first));
            let (open, close) = if wrap { ("(", ")") } else { ("", "") };
            let (shown, per) = (to.shown(span), per_tick(to, span));
            let at = if to == Clock::SAMPLE { shown } else { format!("({shown})") };
            let title = format!("write `{open}{src}{close} at {at}` to delay it per {per}");
            let mut edits = vec![Edit::insert(span.file, span.end, format!("{close} at {at}"))];
            if wrap {
                edits.insert(0, Edit::insert(span.file, span.start, open));
            }
            diag = diag.with_fix(Fix::new(title, edits));
        }
        self.report(diag);
    }

    /// The modifier `e` of the chain of the head `head`, a built-in delay that
    /// ticks at an event (§11.10): `.when~`, which stops nothing, is E0020,
    /// with the candidate that takes every one of the chain off; of `.reset_if~`, a condition at
    /// a periodic clock, faster than W (the event clock of the delay), E0815.
    pub(super) fn event_delay_modifier(&mut self, e: ExprId, head: ExprId) {
        let mods = || self.cx.chains.get(&head).into_iter().flat_map(|c| &c.mods);
        let Some(m) = mods().find(|m| m.call == e) else { return };
        let (plan, receiver) = (m.plan, self.ast.expr(m.receiver).span);
        if !self.checking() {
            return;
        }
        let d = match (plan.modifier, plan.cond) {
            (crate::flow_names::Modifier::When, _) => {
                // From the `.` at the name: what is between it and the receiver stays.
                let whole = |m: &ChainModifier| {
                    let dot = m.plan.name.start.saturating_sub(1).max(self.ast.expr(m.receiver).span.end);
                    Span { start: dot, ..self.ast.expr(m.call).span }
                };
                let whens = mods().filter(|m| m.plan.modifier == crate::flow_names::Modifier::When);
                let fix = Fix::new("remove `.when~(…)`", whens.map(|m| Edit::delete(whole(m))).collect());
                foreign::report(RowId::EventDelayWhen, self.text, whole(m), vec![fix])
            }
            (crate::flow_names::Modifier::ResetIf, Some(cond)) => {
                let Some(&c @ Clock::Tick(_)) = self.out.exprs.get(&cond) else { return };
                let span = self.ast.expr(cond).span;
                let msg = format!(
                    "the condition of `.reset_if~` is at the clock `{}`, faster than the event clock of the delay, the fastest it resets at (§11.10)",
                    c.shown(span)
                );
                let d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(self.src(span));
                d.with_note(receiver, "this delay ticks at an event").with_rule(
                    "reset it at an event, or write the delay in a flow and `.reset_if~` after the call of that flow",
                )
            }
            _ => return,
        };
        self.report(d);
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
            shown(c, span)
        );
        self.err(Code::E0815, span, msg);
    }
}
