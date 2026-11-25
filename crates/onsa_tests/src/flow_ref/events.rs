//! The event stages of a flow (§11.11, W7-11 U2, the straight line): a source (an input of `at event`, the event output of a call) has a stage of its own, `Clock::Event`, that runs once for each event it gives, in
//! the middle of the stage that gave it. It is the same walk as a tick's (`flow::stage`, `hoist::walk`): the `let`s of the source's clock are made, a call that takes the source as an argument ticks the input
//! (`tick_receivers`, in the order of the declaration, each with the events it gives done first, S-1236), and the call that gave the event has done its work of the stage first (`fire_emitted`, S-1234). A name of an event
//! keeps its last value, `T.default()` before the first (`default_events`); what a delay saves reads the names of an event as they were where the read is written, a `^name` and a part with one excepted (`snapshot`, S-1240, S-1249).

use std::sync::atomic::{AtomicU64, Ordering};

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_sema::{LocalId, Target};
use onsa_syntax::ast::{ExprId, ExprKind};

use super::expr::{Frame, Stop};
use super::flow::{Clock, Known, Step, clock_of, enter, stage};
use super::hoist::{caret, field_of, kept, kids, made_at, stage_of};
use super::rate::{Bound, chain_of};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Body, Called, Stage, input_clock, output_stage};
use super::state::{NodeKey, Role};
use super::value::Value;

/// Is `e` a `^name` or a name alone, under parentheses and `at`s?
fn bare_name(body: &Body, e: ExprId) -> bool {
    match &body.ast.expr(e).kind {
        ExprKind::Feedback(_) => true,
        ExprKind::Paren(x) | ExprKind::At { expr: x, .. } => bare_name(body, *x),
        _ => false,
    }
}

/// Does `e` read one of the locals `chosen`?
fn reads_any(body: &Body, e: ExprId, chosen: &[LocalId]) -> bool {
    matches!(body.target(e), Ok(Target::Local(l)) if body.names(e) && chosen.contains(l))
        || body.ast.sub_exprs(e).into_iter().any(|x| reads_any(body, x, chosen))
}

/// The bindings of the arms of the `match`es and `match~`es in `e` that a `^name` chooses (S-1249): the object or a guard of any arm has a `^name`, or reads a binding that one chooses (the outer match comes first).
fn chosen_bindings(body: &Body, e: ExprId, chosen: &mut Vec<LocalId>) {
    if let ExprKind::Match { scrutinee, arms, .. } = &body.ast.expr(e).kind {
        let reads = |x: ExprId, chosen: &[LocalId]| caret(body, x) || reads_any(body, x, chosen);
        if reads(*scrutinee, chosen) || arms.iter().any(|a| a.guard.is_some_and(|g| reads(g, chosen))) {
            for a in arms {
                chosen.extend(body.pat_locals(a.pat).unwrap_or_default());
            }
        }
    }
    for x in body.ast.sub_exprs(e) {
        chosen_bindings(body, x, chosen);
    }
}

/// A read of an event a delay saved where it is written: the expression, the replicas of the `par`s the read is in below the delay (empty outside a `par`), and its value.
pub(super) type Snap = (ExprId, Vec<u32>, Value);

/// A number for each run of an event stage, whichever instance (a delay of an event keeps what it gave for the run it gave it in).
pub(super) fn next_serial() -> u64 {
    static SERIAL: AtomicU64 = AtomicU64::new(1);
    SERIAL.fetch_add(1, Ordering::Relaxed)
}

/// The clock of the events the call `e` gives: a source of its own for each call (the clocks of two calls are not compared, §11.11).
pub(super) fn call_src(e: ExprId) -> Clock {
    Clock::Event(0x8000_0000 | e.0)
}

/// The clock `e` is a part of that an event stage makes and keeps: of an event clock, under the guard (a field read of a name is free of it, S-1197), and kept (`hoist::kept`). It is the one judgment of `default_parts`.
fn event_part(body: &Body, known: &Known, root: ExprId, (e, guard): (ExprId, Clock)) -> Result<Option<Clock>, Fault> {
    let clock = stage_of(body, known, root, e)?;
    let free = field_of(body, e)
        .is_some_and(|n| !matches!(body.target(n), Ok(Target::Local(l)) if body.bound_within(*l, root)));
    let clock = made_at(body, e, (clock, if free { Clock::Const } else { guard }));
    Ok((matches!(clock, Clock::Event(_)) && kept(body, known, e)?).then_some(clock))
}

/// Does `e`, or what is in it, hold a part that `default_parts` gives a default?
fn holds_part(body: &Body, known: &Known, root: ExprId, (e, guard): (ExprId, Clock)) -> Result<bool, Fault> {
    if event_part(body, known, root, (e, guard))?.is_some() {
        return Ok(true);
    }
    for (x, k, g) in kids(body, known, root, e, guard)? {
        if holds_part(body, &k, root, (x, g))? {
            return Ok(true);
        }
    }
    Ok(false)
}

impl<'a> Frame<'a> {
    /// The output step gave `v`, an `Option` of the event: a `Some` is an event of this entry (the value of the output from now), `None` gives none.
    pub(super) fn emit(&mut self, v: &Value) {
        if let (Value::Enum { tag: 1, fields }, Some(run)) = (v, self.run.as_mut()) {
            run.emitted.extend(fields.first().cloned());
        }
    }

    /// The names of an event are `T.default()` until the first event (§11.11), at `init` and after a reset: the inputs, the `let`s of an event clock, and the output of a flow that has an event clock (not the event output of a call,
    /// which `start_events` gives its type).
    pub(super) fn default_events(&mut self, steps: &[Step], decl: &FlowDef, out: &mut Value) -> Result<(), Stop> {
        let (body, at) = (self.body, self.body.ast.expr(decl.body).span);
        let here = |fault| Stop { fault, at };
        for (n, i) in decl.inputs.iter().enumerate() {
            if matches!(input_clock(decl, n).map_err(here)?, Clock::Event(_)) {
                let local = body.input(&i.name).ok_or(here(Internal("an input with no local")))?;
                if let Some(d) = self.shape(body.view.ty(i.ty), at)?.default_value() {
                    self.locals.insert(local, d);
                }
            }
        }
        // The parts of an event clock that a stage of a faster clock reads are `T.default()` until their stage has made them.
        for st in steps.iter().filter(|s| !matches!(s.clock, Clock::Event(_))) {
            self.default_parts(&st.known, st.init, (st.init, Clock::Const), at)?;
        }
        for st in steps.iter().filter(|s| matches!(s.clock, Clock::Event(_)) && !s.emits) {
            let ty = body.ty(st.init).map_err(here)?;
            match (st.pat, self.shape(ty, at)?.default_value()) {
                (Some(pat), Some(d)) => self.destructure(pat, &d, ty)?,
                (None, Some(d)) => *out = d,
                _ => {}
            }
        }
        Ok(())
    }

    /// The largest parts of `e` (a step of a faster clock) that an event stage makes and keeps (`hoist::walk`) start at `T.default()`; a step of the event clock itself is run whole in its stage and has no part. A part under a condition
    /// of a later stage (`sample`) is not made by the event stage, as `walk` goes (`guard` is the clock of the conditions on the way to it), but a field read of a name is, whatever the conditions say (S-1197, `hoist::free`).
    /// The body of a `par~` has a part for each replica (S-1140, `hoist::walk`), each starting at its default; one with no part is not walked.
    fn default_parts(
        &mut self,
        known: &Known,
        root: ExprId,
        (e, guard): (ExprId, Clock),
        at: Span,
    ) -> Result<(), Stop> {
        let (body, here) = (self.body, |fault| Stop { fault, at });
        if let Some(clock) = event_part(&body, known, root, (e, guard)).map_err(here)? {
            // A part that holds a `^name` is one read made whole at the end of the stage (S-1249): the parts in it are not parts of their own, and it is `T.default()` before its first stage like any other (§11.3).
            // A bare `^name` is no computed part (a name has a place of its own, and may be written where a `sample` condition chooses it, which no stage of the event reaches): it is read where it is written.
            if !bare_name(&body, e) {
                let ty = body.ty(e).map_err(here)?;
                // A type with no default (an `Option`) has none to start from: such a part is made where it is read.
                if let Some(d) = self.shape(ty, at).ok().and_then(|s| s.default_value()) {
                    let replicas = self.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default();
                    self.hoisted.entry(e).or_insert((clock, Default::default())).1.insert(replicas, d);
                }
            }
            return Ok(());
        }
        let kids = kids(&body, known, root, e, guard).map_err(here)?;
        let in_par = matches!(body.ast.expr(e).kind, ExprKind::Par { .. });
        if in_par && !holds_part(&body, known, root, (e, guard)).map_err(here)? {
            return Ok(());
        }
        let each = |f: &mut Self| kids.iter().try_for_each(|(x, k, g)| f.default_parts(k, root, (*x, *g), at));
        match in_par {
            true => self.replicate(e, |_: &()| 0, each).map(drop),
            false => each(self),
        }
    }

    /// The instance of a flow that gives events, made by the call `call`: its output is `T.default()` of the type of the event until it gives one.
    pub(super) fn start_events(&mut self, key: &NodeKey, call: ExprId) -> Result<(), Stop> {
        let at = self.body.ast.expr(call).span;
        let here = |fault| Stop { fault, at };
        let def = self.run.as_ref().and_then(|r| r.state.children.get(key)).map(|c| c.def);
        let decl = self.body.view.flow(def.ok_or(here(Internal("an instance with no state")))?).map_err(here)?;
        if !matches!(output_stage(decl).map_err(here)?, Stage::Event(_)) {
            return Ok(());
        }
        let ty = self.body.ty(call).map_err(here)?;
        let d = self.shape(ty, at)?.default_value().ok_or(here(Internal("an event of a type with no default")))?;
        if let Some(c) = self.run.as_mut().and_then(|r| r.state.children.get_mut(key)) {
            c.out = d;
        }
        Ok(())
    }

    /// The call at `key` did its work and gave an event: the stage of its source runs now, before the rest of this stage (S-1234).
    pub(super) fn fire_emitted(&mut self, key: &NodeKey) -> Result<(), Stop> {
        let given =
            self.run.as_mut().and_then(|r| r.state.children.get_mut(key)).map(|c| std::mem::take(&mut c.emitted));
        // Each event of the entry (the events of the runs of a body under `.up~(N)` come in order) ticks after the work of the entry, with the value of that event as the output of the call.
        for v in given.unwrap_or_default() {
            if let Some(c) = self.run.as_mut().and_then(|r| r.state.children.get_mut(key)) {
                c.out = v;
            }
            self.fire(key, self.body.ast.expr(key.call).span)?;
        }
        Ok(())
    }

    /// The stage `src` of this instance, run in the middle of the stage it is in: its `let`s and the work of its calls, then what its delays saved is stored (only those it saved). The stage and the step it is in are put back after.
    fn fire(&mut self, key: &NodeKey, at: Span) -> Result<(), Stop> {
        let Clock::Event(k) = call_src(key.call) else { return Ok(()) };
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        let Some(steps) = run.steps.clone() else {
            return Err(Stop { fault: Fault::Unavailable("an event stage outside an instance"), at });
        };
        let (was, gathered, step, from, serial) =
            (run.stage, std::mem::take(&mut run.gathered), run.step.take(), run.saves_len(), run.serial);
        run.stage = Stage::Event(k);
        run.serial = next_serial();
        // A maker in a replica of a `par~` runs the stage of that replica: the walk goes through the replicas the call is in, whichever it is called from (`Frame::replicate`).
        let inside = (std::mem::take(&mut run.replicas), std::mem::take(&mut run.scope));
        let pin = run.pin.replace((key.call, key.replicas.clone()));
        let (mut out, mine) = (Value::Unit, Stage::Event(k));
        let ran = steps.last().is_some_and(|s| s.pat.is_none() && !s.emits && s.clock.runs_at(mine));
        let done = stage(self, &steps, &mut out, mine).and_then(|()| self.commit_from(at, from));
        if let Some(run) = self.run.as_mut() {
            (run.stage, run.gathered, run.step, run.serial) = (was, gathered, step, serial);
            (run.replicas, run.scope, run.pin) = (inside.0, inside.1, pin);
            if ran && done.is_ok() {
                run.set_out = Some(out);
            }
        }
        done
    }

    /// The `reset_if~`s of the chain `e` whose condition is an event of the source `here` (§11.10, S-1236): each condition is read in the order written, and each that holds puts back what it wraps, before the inputs of the call that
    /// tick in this stage (`tick_receivers`: the reset is first for an input of the same source, §11.10 "戻してから足す"). An instance goes back at once; a delay of another clock than the event goes back now, or after the store of the
    /// stage it is in when it has been read in it and is not stored yet (S-1250 (B), `Frame::reset_delay`). A delay of the clock of the event reads its condition where it is written (`delay_chain`).
    pub(super) fn reset_on_event(
        &mut self,
        e: ExprId,
        here: Clock,
        parts: Option<(&Known, ExprId)>,
    ) -> Result<(), Stop> {
        let (body, at) = (self.body, self.body.ast.expr(e).span);
        let stop = |fault| Stop { fault, at };
        let (Some(chain), Some((known, root))) = (chain_of(&body, e).map_err(stop)?, parts) else { return Ok(()) };
        let own = clock_of(&body, known, root, chain.head).map_err(stop)?;
        let delay = matches!(body.called(chain.head).map_err(stop)?, Called::Builtin(_));
        let mut due = Vec::new();
        for (i, b) in chain.bounds.iter().enumerate() {
            let Bound::ResetIf(c) = b else { continue };
            if clock_of(&body, known, root, *c).map_err(stop)? == here
                && !(delay && own == here)
                && self.truth(*c, at)?
            {
                due.push(i);
            }
        }
        for i in due {
            match delay {
                true => {
                    let key = self.key(chain.head, Role::Delay);
                    self.reset_delay(&key, at)?;
                    // The output each `when~` inside the reset holds goes back too (§11.10): a reset inside the `when~` leaves it.
                    if let Some(m) = self.run.as_mut().and_then(|r| r.state.mods.get_mut(&key)) {
                        m.put_back(i);
                    }
                }
                false => {
                    let key = self.key(chain.head, Role::Child);
                    self.gate(&key, i + 1, at)?.due = true;
                    self.put_back(&key, i + 1, at)?;
                }
            }
        }
        Ok(())
    }

    /// The call `e` (of `head`) in the stage of the event source `here`: each input of an event whose argument has that clock ticks, in the order of the declaration, with the events it gives done before the next input (S-1236).
    pub(super) fn tick_receivers(
        &mut self,
        e: ExprId,
        head: ExprId,
        here: Clock,
        parts: Option<(&Known, ExprId)>,
    ) -> Result<(), Stop> {
        let (body, at) = (self.body, self.body.ast.expr(e).span);
        let stop = |fault| Stop { fault, at };
        let (Called::Flow(def), Some((known, root))) = (body.called(head).map_err(stop)?, parts) else {
            return Ok(());
        };
        let (key, decl) = (self.key(head, Role::Child), body.view.flow(def).map_err(stop)?);
        let args = self.args_of_call(key.call, decl)?;
        for (n, i) in decl.inputs.iter().enumerate() {
            let event = matches!(input_clock(decl, n).map_err(stop)?, Clock::Event(_));
            if !event || clock_of(&body, known, root, args[n].expr).map_err(stop)? != here {
                continue;
            }
            let v = self.eval(args[n].expr)?;
            // A `reset_if~` of a tick that held before this stage (a slower tick, read before the `sample` stage) puts the part back before the input ticks, as it does before the work of its own stage (§11.10).
            let levels = self.levels_of(&key, at)?;
            if levels.len() > 1 {
                self.cut(&key, &levels, 0, 0, at)?;
            }
            let scope = self.run.as_ref().and_then(|r| r.state.children.get(&key)).map(|c| c.scope.clone());
            let scope = scope.ok_or(stop(Internal("an instance with no state")))?;
            self.with_bindings(&[], scope, |f| {
                f.in_child(&key, |f, inst, decl| enter(f, inst, decl, Stage::Event(n as u32), &[(i.name.as_str(), v)]))
            })?;
            self.fire_emitted(&key)?;
        }
        Ok(())
    }

    /// What the delay saved at `slot` reads of the names of an event, as they are where the delay is written (S-1240, §11.3, S-1249): every read but a `^name` and a part of an event clock that has one (that is made at the end of the stage), wherever it is written
    /// (a branch, a guard, the right side of `&&`, an arm, a part of a slower clock): the place of a read is where it is written, whatever the condition that chooses it reads. The first argument of a delay in it is the same: the place is the one of the outer.
    pub(super) fn snapshot(&mut self, slot: usize, expr: ExprId) {
        let parts = self.event_reads(expr);
        if let Some(save) = self.run.as_mut().and_then(|r| r.save_mut(slot)) {
            save.snap_parts = parts;
        }
    }

    /// The reads of the names of an event in `expr` and what they are now (S-1240): for a delay that saves `expr`, and for a part of a slower clock that reads a `^name` and is made at the end of its stage (S-1249: the `p` of `(p at (sample / 4)) * 2 + ^k`).
    pub(super) fn event_reads(&self, expr: ExprId) -> Vec<Snap> {
        let known = self.run.as_ref().and_then(|r| r.steps.clone()).and_then(|s| s.first().map(|s| s.known.clone()));
        known.map_or_else(Vec::new, |known| self.event_reads_in(&known, expr))
    }

    /// [`Self::event_reads`] with the clocks of the names `known` as the walk that reaches `expr` has them (the index of a `par` around it too).
    pub(super) fn event_reads_in(&self, known: &Known, expr: ExprId) -> Vec<Snap> {
        let (mut parts, mut chosen) = (Vec::new(), Vec::new());
        chosen_bindings(&self.body, expr, &mut chosen);
        self.reads_of_events(known, (expr, &chosen), expr, &mut parts);
        parts
    }

    /// `root` and the bindings of the arms that a `^name` chooses (S-1249); a part of an event clock that reads one is made at the end of the stage whole, as one that has a `^name` is.
    fn reads_of_events(&self, known: &Known, (root, chosen): (ExprId, &[LocalId]), e: ExprId, out: &mut Vec<Snap>) {
        let body = self.body;
        // A part in a `par` has a clock only with the index of the `par` (`clock_of` stops at it), so the part a stage kept says it is of an event clock.
        let kept = self.hoisted.get(&e).filter(|k| matches!(k.0, Clock::Event(_) | Clock::Const));
        let event = matches!(clock_of(&body, known, root, e), Ok(Clock::Event(_)))
            || kept.is_some_and(|k| matches!(k.0, Clock::Event(_)));
        if matches!(body.ast.expr(e).kind, ExprKind::Feedback(_))
            || (event && (caret(&body, e) || reads_any(&body, e, chosen)))
        {
            return;
        }
        // A part of an event clock that a stage kept is read as it is where the delay is written too, and so is a read that the delay around this one saved where it is written (`Clock::Const`: no part of a stage, `commit_from`). A part
        // in a `par` has a value for each replica, all of them are read (S-1140).
        let replicas = self.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default();
        if let Some(k) = kept {
            let before = out.len();
            out.extend(
                k.1.iter()
                    .filter(|(r, _)| r.starts_with(&replicas))
                    .map(|(r, v)| (e, r[replicas.len()..].to_vec(), v.clone())),
            );
            if out.len() > before {
                return;
            }
        }
        if let (true, Ok(Target::Local(l))) = (body.names(e), body.target(e)) {
            let read = known.get(l).and_then(|s| s.read);
            if let (Some(Clock::Event(_)), Some(v)) = (read, self.locals.get(l)) {
                out.push((e, Vec::new(), v.clone()));
            }
        }
        for x in body.ast.sub_exprs(e) {
            self.reads_of_events(known, (root, chosen), x, out);
        }
    }
}
