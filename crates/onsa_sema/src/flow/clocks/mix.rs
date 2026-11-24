//! The four places of §11.11 whose clock decides when something happens (the
//! first argument of a built-in delay, a loop of `let`s, the condition of
//! `.reset_if~`, the expression of an event output): at a periodic clock, an
//! event value with no `at` over it is E0815 (S-563), reported only, which
//! changes no clock. Made once after the walk, of the clocks it recorded,
//! and nothing in a flow with no event. Each expression is searched once for
//! its `let` and once for the place it is in (a place ends at the nodes in
//! it): linear in the body.

use onsa_syntax::ast::OperandPlace;

use super::*;
use crate::slot::{Form, Slot, slot_of};

/// A place of §11.11.
#[derive(Debug, Clone, Copy)]
enum Place<'a> {
    Delay(Delay, &'a NodeCall),
    Loop,
    Reset,
    Output,
}

/// A place at the periodic clock `clock` whose expression `root` reads the
/// event values `events`, each the largest expression of its clock with no
/// `at` over it.
#[derive(Debug)]
struct Mixed<'a> {
    place: Place<'a>,
    root: ExprId,
    clock: Clock,
    events: Vec<ExprId>,
}

/// The search of the event values of the expressions of the walk `w`.
struct Mix<'w, 'a> {
    w: &'w Walk<'a>,
    /// A node counted as an event value (of a candidate that makes it one).
    made: Option<ExprId>,
    /// The first event value of each `let` made, in their order: a name reads
    /// an earlier one, with no recursion through the chain of the `let`s.
    lets: Vec<Option<ExprId>>,
    /// The arm of the `match` that binds a name, and the first event value of
    /// what chooses it.
    arms: HashMap<LocalId, (ExprId, usize)>,
    chosen: HashMap<(ExprId, usize), Option<ExprId>>,
}

/// The E0815 of the first place in the order of the file (§18.1).
pub(super) fn check(w: &mut Walk) {
    if first_event(w.a, w.def, w.cx).is_none() {
        return;
    }
    let mixed = Mix::new(w, None).mixed();
    let span = |m: &Mixed| w.ast.expr(m.root).span;
    let first = mixed.into_iter().reduce(|x, y| if Diagnostic::place_before(span(&y), span(&x)) { y } else { x });
    if let Some(d) = first.map(|m| m.diagnostic(w)) {
        w.report(d);
    }
}

impl<'w, 'a> Mix<'w, 'a> {
    fn new(w: &'w Walk<'a>, made: Option<ExprId>) -> Self {
        let mut arms = HashMap::default();
        for &e in w.out.exprs.keys() {
            let ExprKind::Match { arms: of, .. } = &w.ast.expr(e).kind else { continue };
            for (k, arm) in of.iter().enumerate() {
                crate::pat::each_bind(w.ast, arm.pat, true, &mut |p, _| {
                    arms.extend(w.body.pat_locals.get(&p).map(|&l| (l, (e, k))));
                });
            }
        }
        let mut s = Mix { w, made, lets: Vec::new(), arms, chosen: HashMap::default() };
        for p in &w.cx.pending {
            let first = s.first(p.init);
            s.lets.push(first);
        }
        s
    }

    /// The places at a periodic clock that read an event value.
    fn mixed(mut self) -> Vec<Mixed<'a>> {
        let (w, cx) = (self.w, self.w.cx);
        let mut places: Vec<(Place<'a>, Vec<ExprId>)> = Vec::new();
        for call in &cx.calls {
            if let NodeKind::Delay(d, _) = call.kind {
                places.push((Place::Delay(d, call), vec![call.delay_parts().0]));
            }
            let mods = cx.chains.get(&call.expr).into_iter().flat_map(|c| &c.mods);
            let resets = mods.filter(|m| m.plan.modifier == crate::flow_names::Modifier::ResetIf);
            places.extend(resets.filter_map(|m| Some((Place::Reset, vec![m.plan.cond?]))));
        }
        // Of a loop, its first `let` that reads one.
        places.extend(w.loops.iter().map(|l| (Place::Loop, l.iter().map(|&k| cx.pending[k].init).collect())));
        if w.a.def(w.def).as_flow().is_some_and(FlowDef::gives_events) {
            places.push((Place::Output, cx.output.into_iter().collect()));
        }
        let mut out = Vec::new();
        for (place, roots) in places {
            let mut of = roots.into_iter().filter_map(|root| {
                let clock = *w.out.exprs.get(&root)?;
                let clock = matches!(clock, Clock::Tick(_)).then_some(clock)?;
                let events = self.events(root);
                (!events.is_empty()).then_some(Mixed { place, root, clock, events })
            });
            out.extend(of.next());
        }
        out
    }

    /// The event values `root` reads, each once, in the order of the text: through
    /// the names of the `let`s (a `^y` of one made) and the bindings of an arm,
    /// its fields not apart, to an `at` and the output of a flow (§11.11).
    fn events(&mut self, root: ExprId) -> Vec<ExprId> {
        let w = self.w;
        let (mut out, mut seen, mut todo) = (Vec::new(), HashSet::default(), vec![root]);
        while let Some(x) = todo.pop() {
            let kind = &w.ast.expr(x).kind;
            let (clock, node) = (w.out.exprs.get(&x), w.calls.contains_key(&x) || w.names.modifier(x).is_some());
            // A block is searched to its tail, where `at` is written.
            let event = matches!(clock, Some(Clock::Event(_))) && !matches!(kind, ExprKind::Block(_));
            match (kind, w.body.targets.get(&x)) {
                _ if event || self.made == Some(x) => out.extend(seen.insert(x).then_some(x)),
                // None of a callee.
                _ if node || !matches!(clock, Some(Clock::Event(_) | Clock::Tick(_)) | None) => {}
                (ExprKind::At { .. }, _) => {}
                (_, Some(&Target::Local(l))) => out.extend(self.of_name(l).filter(|&x| seen.insert(x))),
                (ExprKind::If { .. }, _) => {
                    let chain = crate::flow::branching::chain(w.ast, x);
                    todo.extend(chain.last);
                    todo.extend(chain.links.iter().rev().flat_map(|l| [l.then, l.cond]));
                }
                _ => todo.extend(w.ast.sub_exprs(x).into_iter().rev()),
            }
        }
        out
    }

    fn first(&mut self, root: ExprId) -> Option<ExprId> {
        self.events(root).first().copied()
    }

    /// The first event value of the name `l`: of a `let`, its initializer's;
    /// of a binding of an arm, its scrutinee's and the guards' to the arm,
    /// which its clock is the join of (S-1131).
    fn of_name(&mut self, l: LocalId) -> Option<ExprId> {
        if let Some(&k) = self.w.cx.let_of_local.get(&l) {
            return self.lets.get(k).copied().flatten();
        }
        let &(e, arm) = self.arms.get(&l)?;
        if let Some(&made) = self.chosen.get(&(e, arm)) {
            return made;
        }
        let ExprKind::Match { scrutinee, arms, .. } = &self.w.ast.expr(e).kind else { return None };
        // The guard of the arm reads the binding too, which adds no other.
        self.chosen.insert((e, arm), None);
        let parts = std::iter::once(*scrutinee).chain(arms[..=arm].iter().filter_map(|a| a.guard));
        let first = parts.filter_map(|x| self.first(x)).next();
        self.chosen.insert((e, arm), first);
        first
    }
}

impl Mixed<'_> {
    /// The E0815 at the expression of the place, with a note at the event
    /// value, and of a delay its candidates (§11.11).
    fn diagnostic(&self, w: &Walk) -> Diagnostic {
        let span = w.ast.expr(self.root).span;
        let (what, when) = match self.place {
            Place::Delay(d, _) => (format!("the first argument of `{}~`", d.name()), "the delay ticks at its clock"),
            Place::Loop => ("this value of a loop of `let`s".into(), "the loop is stepped at its clock"),
            Place::Reset => ("the condition of `.reset_if~`".into(), "the part is reset at its clock"),
            Place::Output => ("the expression of the event output".into(), "the events are given out at its clock"),
        };
        let msg = format!(
            "{what} is at the clock `{}` and reads an event value with no `at`; {when}, so the two are not mixed here (§11.11)",
            self.clock.shown(span)
        );
        let mut d = Diagnostic::new(Stage::Flow, Code::E0815, span, msg).with_found(w.src(span));
        if let Some(&e) = self.events.first() {
            let of = w.out.exprs.get(&e).and_then(|&c| w.event_name(c));
            let of = of.unwrap_or_else(|| "an event clock".into());
            d = d.with_note(w.ast.expr(e).span, format!("this event value is at {of}"));
        }
        let at = self.clock.written(span);
        let d = d.with_rule(format!(
            "write `at {at}` on the event value to read its last value at each tick of `{}`, or keep the event value alone here",
            self.clock.shown(span)
        ));
        self.outside(w).into_iter().chain(self.pinned(w)).fold(d, Diagnostic::with_fix)
    }

    /// The candidate `prev~(E) + x` of `prev~(E + x)` (§11.11): of a `prev~`
    /// with no `init` and no modifier whose first argument is one operation of
    /// an event value and a value of a tick. Not where `x` reads a `^y`, which
    /// is in a delay only, nor where the value of the `prev~` then mixes in
    /// another place (§18.1).
    fn outside(&self, w: &Walk) -> Option<Fix> {
        let Place::Delay(Delay::Prev, call) = self.place else { return None };
        let ExprKind::Binary { op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div), lhs, rhs, .. } =
            w.ast.expr(self.root).kind
        else {
            return None;
        };
        let plain = call.init_expr.is_none() && !w.cx.chains.contains_key(&call.expr);
        let event = |x: ExprId| matches!(w.out.exprs.get(&x), Some(Clock::Event(_)));
        let (e, x) = if event(lhs) { (lhs, rhs) } else { (rhs, lhs) };
        if !plain || !event(e) || event(x) || reads_back(w.ast, x) {
            return None;
        }
        let mixes = |m: &Mixed| m.events.contains(&call.expr);
        if Mix::new(w, Some(call.expr)).mixed().iter().any(mixes) {
            return None;
        }
        let [call_at, l, r, e_at] = [call.expr, lhs, rhs, e].map(|y| w.ast.expr(y).span);
        let text = |start, end| Span { start, end, ..call_at }.text_in(w.text);
        let (open, close) = (text(call_at.start, l.start), text(r.end, call_at.end));
        if open.contains("//") || close.trim() != ")" {
            return None;
        }
        let root = w.cx.pending.iter().map(|p| p.init).chain(w.cx.output);
        let place = root.filter_map(|y| slot_of(w.ast, y, call.expr)).next()?;
        let wrap = place.slot.wraps(Form::Binary(op));
        let at = |offset, s: &str| Edit::insert(call_at.file, offset, s);
        let cut = |start, end, s: &str| Edit::replace(Span { start, end, ..call_at }, s);
        let edits = match (e == lhs, wrap) {
            (true, true) => vec![at(call_at.start, "("), at(e_at.end, ")")],
            (true, false) => vec![at(e_at.end, ")"), cut(call_at.end - 1, call_at.end, "")],
            // The `(` of the call stays (§18.1, the least edit).
            (false, true) => {
                let paren = open.find('(').map_or(l.start, |i| call_at.start + i as u32);
                vec![cut(call_at.start, paren, ""), at(e_at.start, open.trim_end()), at(call_at.end, ")")]
            }
            (false, false) => vec![cut(call_at.start, l.start, ""), at(e_at.start, open.trim_end())],
        };
        Some(Fix::new("delay the event value alone, per event", edits))
    }

    /// The candidate that writes `at` the clock of the place on each event
    /// value of the first argument of a delay (§11.11): where all are written
    /// in it and their types satisfy `Default` (E0816 else, §18.1), and one
    /// that is computed is in no branching, whose condition may refuse it
    /// (E0815, S-1158 (c)).
    fn pinned(&self, w: &Walk) -> Option<Fix> {
        let default = |x| {
            let span = w.ast.expr(x).span;
            crate::signal::no_default_signal(w.a, w.ty_of(x), span, "", "").is_none()
        };
        let computed = |x| match &w.ast.expr(x).kind {
            ExprKind::Field { base, .. } => !matches!(w.ast.expr(*base).kind, ExprKind::Path(_)),
            kind => !matches!(kind, ExprKind::Path(_)),
        };
        let chosen = |x| computed(x) && under_branching(w.ast, self.root, x);
        if !matches!(self.place, Place::Delay(..)) || self.events.iter().any(|&x| !default(x) || chosen(x)) {
            return None;
        }
        let mut edits = Vec::with_capacity(2 * self.events.len());
        let at = self.clock.written(w.ast.expr(self.root).span);
        for &e in &self.events {
            let span = w.ast.expr(e).span;
            let inner = Slot::Operand(OperandPlace::AsAtLeft).wraps(Form::of(w.ast, e));
            // None of one read through a name, written elsewhere.
            let outer = slot_of(w.ast, self.root, e)?.slot.wraps(Form::AsAt);
            let (open, close) = ("(".repeat(inner.into()), if inner { ")" } else { "" });
            let (open, end) = if outer { (format!("({open}"), ")") } else { (open, "") };
            if !open.is_empty() {
                edits.push(Edit::insert(span.file, span.start, open));
            }
            edits.push(Edit::insert(span.file, span.end, format!("{close} at {at}{end}")));
        }
        Some(Fix::new(
            format!(
                "read the event value `at {at}`, to delay it per {}",
                checks::per_tick(self.clock, w.ast.expr(self.root).span)
            ),
            edits,
        ))
    }
}

/// Whether `e` is in a branching or a short-circuit under `root`.
fn under_branching(ast: &Ast, root: ExprId, e: ExprId) -> bool {
    let mut todo = vec![(root, false)];
    while let Some((x, under)) = todo.pop() {
        if x == e {
            return under;
        }
        let branching = match ast.expr(x).kind {
            ExprKind::If { .. } | ExprKind::Match { .. } => true,
            ExprKind::Binary { op, .. } => matches!(op, BinOp::And | BinOp::Or),
            _ => false,
        };
        todo.extend(ast.sub_exprs(x).into_iter().map(|y| (y, under || branching)));
    }
    true
}

/// Whether `e` reads a `^y`.
fn reads_back(ast: &Ast, e: ExprId) -> bool {
    let mut todo = vec![e];
    while let Some(x) = todo.pop() {
        if matches!(ast.expr(x).kind, ExprKind::Feedback(_)) {
            return true;
        }
        todo.extend(ast.sub_exprs(x));
    }
    false
}

#[cfg(test)]
mod tests;
