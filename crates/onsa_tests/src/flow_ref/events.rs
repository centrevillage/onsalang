//! The event stages of a flow (§11.11, W7-11 U2, the straight line): a source (an input of `at event`, the event output of a call) has a stage of its own, `Clock::Event`, that runs once for each event it gives, in
//! the middle of the stage that gave it. It is the same walk as a tick's (`flow::stage`, `hoist::walk`): the `let`s of the source's clock are made, a call that takes the source as an argument ticks the input
//! (`tick_receivers`, in the order of the declaration, each with the events it gives done first, S-1236), and the call that gave the event has done its work of the stage first (`fire_emitted`, S-1234). A name of an event
//! keeps its last value, `T.default()` before the first (`default_events`); what a delay saves reads the names of an event as they were where the read is written, a `^name` and a part with one excepted (`snapshot`, S-1240, S-1249).

use onsa_diag::Span;
use onsa_sema::Target;
use onsa_sema::def::FlowDef;
use onsa_syntax::ast::{ExprId, ExprKind};

use super::expr::{Frame, Stop};
use super::flow::{Clock, Known, Step, clock_of, enter, stage};
use super::hoist::{caret, kept, stage_of};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Called, Stage, input_clock, output_stage};
use super::state::{NodeKey, Role};
use super::value::Value;

/// The clock of the events the call `e` gives: a source of its own for each call (the clocks of two calls are not compared, §11.11).
pub(super) fn call_src(e: ExprId) -> Clock {
    Clock::Event(0x8000_0000 | e.0)
}

impl<'a> Frame<'a> {
    /// The output step gave `v`, an `Option` of the event: a `Some` is an event of this entry (the value of the output from now), `None` gives none.
    pub(super) fn emit(&mut self, v: &Value) {
        if let (Value::Enum { tag: 1, fields }, Some(run)) = (v, self.run.as_mut()) {
            run.emitted = fields.first().cloned();
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
            self.default_parts(&st.known, st.init, st.init, at)?;
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

    /// The largest parts of `e` (a step of a faster clock) that an event stage makes and keeps (`hoist::walk`) start at `T.default()`; a step of the event clock itself is run whole in its stage and has no part.
    fn default_parts(&mut self, known: &Known, root: ExprId, e: ExprId, at: Span) -> Result<(), Stop> {
        let (body, here) = (self.body, |fault| Stop { fault, at });
        let clock = stage_of(&body, known, root, e).map_err(here)?;
        // A part that reads a `^name` is made at the end of its stage (S-1244), with what the delays save, and is read fresh before.
        if matches!(clock, Clock::Event(_)) && kept(&body, known, e).map_err(here)? {
            // A part that holds a `^name` is one read made whole at the end of the stage (S-1249): the parts in it are not parts of their own, and the value it has before its first stage is not read (it is made where it is read).
            if caret(&body, e) {
                return Ok(());
            }
            let ty = body.ty(e).map_err(here)?;
            // A type with no default (an `Option`) has none to start from: such a part is made where it is read.
            if let Some(d) = self.shape(ty, at).ok().and_then(|s| s.default_value()) {
                self.hoisted.entry(e).or_insert((clock, Default::default())).1.insert(Vec::new(), d);
            }
            return Ok(());
        }
        for x in body.ast.sub_exprs(e) {
            self.default_parts(known, root, x, at)?;
        }
        Ok(())
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
        let given = self.run.as_mut().and_then(|r| r.state.children.get_mut(key)).and_then(|c| c.emitted.take());
        match given {
            Some(_) => self.fire(call_src(key.call), self.body.ast.expr(key.call).span),
            None => Ok(()),
        }
    }

    /// The stage `src` of this instance, run in the middle of the stage it is in: its `let`s and the work of its calls, then what its delays saved is stored (only those it saved). The stage and the step it is in are put back after.
    fn fire(&mut self, src: Clock, at: Span) -> Result<(), Stop> {
        let Clock::Event(k) = src else { return Ok(()) };
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        let Some(steps) = run.steps.clone() else {
            return Err(Stop { fault: Fault::Unavailable("an event stage outside an instance"), at });
        };
        let (was, gathered, step, from) =
            (run.stage, std::mem::take(&mut run.gathered), run.step.take(), run.saves_len());
        run.stage = Stage::Event(k);
        let (mut out, mine) = (Value::Unit, Stage::Event(k));
        let ran = steps.last().is_some_and(|s| s.pat.is_none() && !s.emits && s.clock.runs_at(mine));
        let done = stage(self, &steps, &mut out, mine).and_then(|()| self.commit_from(at, from));
        if let Some(run) = self.run.as_mut() {
            (run.stage, run.gathered, run.step) = (was, gathered, step);
            if ran && done.is_ok() {
                run.set_out = Some(out);
            }
        }
        done
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
    pub(super) fn event_reads(&self, expr: ExprId) -> Vec<(ExprId, Value)> {
        let known = self.run.as_ref().and_then(|r| r.steps.clone()).and_then(|s| s.first().map(|s| s.known.clone()));
        let mut parts = Vec::new();
        if let Some(known) = known {
            self.reads_of_events(&known, expr, expr, &mut parts);
        }
        parts
    }

    fn reads_of_events(&self, known: &Known, root: ExprId, e: ExprId, out: &mut Vec<(ExprId, Value)>) {
        let body = self.body;
        let event = matches!(clock_of(&body, known, root, e), Ok(Clock::Event(_)));
        if matches!(body.ast.expr(e).kind, ExprKind::Feedback(_)) || (event && caret(&body, e)) {
            return;
        }
        // A part of an event clock that a stage kept is read as it is where the delay is written too, and so is a read that the delay around this one saved where it is written (`Clock::Const`: no part of a stage, `commit_from`).
        let replicas = self.run.as_ref().map(|r| r.replicas.clone()).unwrap_or_default();
        if let Some(v) = self
            .hoisted
            .get(&e)
            .filter(|k| matches!(k.0, Clock::Event(_) | Clock::Const))
            .and_then(|k| k.1.get(&replicas))
        {
            out.push((e, v.clone()));
            return;
        }
        if let (true, Ok(Target::Local(l))) = (body.names(e), body.target(e)) {
            let read = known.get(l).and_then(|s| s.read);
            if let (Some(Clock::Event(_)), Some(v)) = (read, self.locals.get(l)) {
                out.push((e, v.clone()));
            }
        }
        for x in body.ast.sub_exprs(e) {
            self.reads_of_events(known, root, x, out);
        }
    }
}
