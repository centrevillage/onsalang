//! The run of an instance that a chain of modifiers makes (§11.9, S-1207): each `.down~(N)` and `.up~(N)` wraps the whole part on its left and runs it in the stages of its own caller, so the chain is a list of boundaries
//! (`rate::Level`), the head inside. `run_level` runs the stage `s` of the part `b` in a frame of it at the time `ctx`, one boundary at a time: a `.down~(N)` runs the part inside in the frames that are multiples of N (with the
//! elements of the ring of an input it gathers, and the array of an output it deals), a `.up~(N)` runs it N times (the run `j` takes its part of the burst of the frame), and `level_out` reads what the part gives, the
//! same way. The stages of a frame are run slowest first by what calls `run_unit` (`Frame::run_children`, `read_call`).

use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::def::FlowDef;
use onsa_syntax::ast::ExprId;

use super::expr::{Eval, Frame, LOW_STACK, Stop};
use super::flow::{Ctx, Inst, enter};
use super::rate::{
    Guard, Level, counted, dealt, elements, n_of, on_tick, phase, port_exprs, port_stage, slice, time_of,
};
use super::scalar::{Fault, Fault::Internal};
use super::sema_view::{Called, Stage, input_stage};
use super::state::{NodeKey, Role, Store};
use super::value::Value;

const NO_GATE: &str = "a `when~` with no state";

/// What a `.when~(c)` of a chain keeps (§11.9, §11.10): the condition the caller read for it, whether it read true at the last tick of W, the frames the part ran (the counter of the grid of the part), and the output it holds,
/// `start` (`T.default()`, a burst of them for an output at `sample * N`) until the part makes one. `init` and the generated `reset` put them back (`InstState::reset`), a `reset_if~` the output alone. A `.reset_if~(c)` keeps
/// the condition and whether its part is `due` to be put back (`Frame::cut`). A chain on a delay keeps the same (`delay_mods.rs`).
#[derive(Clone, Debug)]
pub(super) struct Gate {
    cond: Value,
    on: bool,
    due: bool,
    pub(super) runs: u64,
    pub(super) held: Value,
    start: Value,
}

impl Gate {
    pub(super) fn new(start: Value) -> Gate {
        Gate { cond: Value::Unit, on: false, due: false, runs: 0, held: start.clone(), start }
    }

    pub(super) fn reset(&mut self, soft: bool) {
        match soft {
            true => self.held = self.start.clone(),
            false => *self = Gate::new(self.start.clone()),
        }
    }
}

impl<'a> Frame<'a> {
    /// A call of a flow (§11.5), alone or the head of a chain (§11.9): the instance it makes runs the stages of its parts in the stages of this one (`run_children`), and the call reads its output where the last part makes it
    /// (`made`; its arguments are read there, so the call is always evaluated there), else the output of the stage that made it, held until the next one (a tick, the elements of an array that a `.down~` boundary deals).
    pub(super) fn read_call(&mut self, head: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let Called::Flow(_) = self.body.called(head).map_err(here)? else {
            return Err(here(Internal("a call of a delay read as an instance")));
        };
        let (key, caller) = (self.key(head, Role::Child), self.time(at)?);
        let levels = self.levels_of(&key, at)?;
        let made = Stage::Tick(levels[levels.len() - 1].made);
        if self.run.as_ref().is_some_and(|run| run.stage == made) {
            self.run_unit(&key, made)?;
        }
        self.level_out(&key, &levels, levels.len() - 1, caller, at)
    }

    fn child_mut(&mut self, key: &NodeKey, at: Span) -> Result<&mut Inst, Stop> {
        let child = self.run.as_mut().and_then(|run| run.state.children.get_mut(key));
        child.ok_or(Stop { fault: Internal("an instance with no state"), at })
    }

    fn levels_of(&self, key: &NodeKey, at: Span) -> Result<Rc<[Level]>, Stop> {
        let child = self.run.as_ref().and_then(|run| run.state.children.get(key));
        child.map(|c| c.levels.clone()).ok_or(Stop { fault: Internal("an instance with no state"), at })
    }

    /// The stages of the instance at `key` that are in the stage `s` of this one, for this frame of it, once (`Inst::done`): the stage `y` of a part is in the stage the boundaries put it in (`rate::levels`, §11.9, S-1088). The
    /// arguments are read here in the frame of the call (`feed`), the time the head runs in is that of the boundaries (`time_of`), and `run_level` runs the parts.
    // SPEC-GAP(S-1206): the stage of this one that an instance runs a stage of its body in is the one the boundaries say, and its output at `sample` is made where the call is read; the spec does not say the
    // order of the stages of the parts of a call (only a panic shows it). The argument of a gathered input is made at the stage of its own clock, in the walk of the instances of that stage before they run (`hoist::gathered`), when it is
    // a part that is kept (Copy, not a name); any other is made in the second phase, after them (`Frame::save_gathers`): where in the stage the spec does not say either, and again only a panic shows it.
    pub(super) fn run_unit(&mut self, key: &NodeKey, s: Stage) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let child = run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?;
        let (def, levels, caller, done) = (child.def, child.levels.clone(), run.ctx, child.done);
        let decl = self.body.view.flow(def).map_err(here)?;
        let Stage::Tick(sx) = s else {
            let params = self.param_inputs(key, decl, s)?;
            return match s {
                Stage::Block => self.in_child(key, |f, inst, decl| enter(f, inst, decl, s, &params)),
                _ => Ok(()),
            };
        };
        let top = &levels[levels.len() - 1];
        if !top.stages.contains(&sx) || done == Some((caller.total(), s)) {
            return Ok(());
        }
        self.feed(key, decl, &levels, sx)?;
        self.read_conds(key, &levels, sx)?;
        let ins = self.run.as_ref().and_then(|r| r.state.children.get(key)).map(|c| c.fed.clone());
        self.run_level(key, &levels, levels.len() - 1, sx, caller, ins.ok_or(here(Internal("no instance")))?)?;
        self.child_mut(key, at)?.done = Some((caller.total(), s));
        Ok(())
    }

    /// The arguments of the ports of the head that this frame reads at the stage `sx` of this one (the inputs of the head and the conditions a boundary gathers, `rate::port_exprs`): those the last boundary does not gather, at
    /// the clock `q` they have in the call (at the stage `rate::port_stage`: `q`, `sample` for `q > 0`, S-1131: the bindings of an arm they read are those of the stage). A burst is `2^q` values for `q > 0` (a value of the parameter kinds is each of them).
    fn feed(&mut self, key: &NodeKey, decl: &'a FlowDef, levels: &[Level], sx: i32) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        let top = &levels[levels.len() - 1];
        let args = port_exprs(self.args_of_call(key.call, decl)?.iter().map(|a| a.expr), levels);
        for (n, a) in args.into_iter().enumerate() {
            let Some(q) = top.ins[n].filter(|q| port_stage(levels, n, *q) == sx && !top.gathers.contains(&n)) else {
                continue;
            };
            let v = match self.eval_staged(key.call, a, Stage::Tick(sx))? {
                Value::Burst(es) => counted(&es, q).map(|()| Value::Burst(es)).map_err(here)?,
                // The elements are made after the limit has been asked: `x: F32 at (sample * 2147483648)` of a value of the parameter kinds is not 2^31 of them.
                v if q > 0 => self.holds_burst(q, at).map(|()| Value::Burst(vec![v; n_of(q) as usize]))?,
                v => v,
            };
            self.child_mut(key, at)?.fed[n] = v;
        }
        Ok(())
    }

    /// The stage `s` of the part `b` (of the chain at `key`) in its frame at the time `ctx` whose inputs are `ins` (a burst of `2^k` elements for an input at `sample * 2^k` of the part, else the value of the stream here): the parts
    /// inside run in the stages that `rate::caller_stage` puts in `s`, the ring an input is gathered in is written at its stage after them, and the array an output is dealt in at the stage of the boundary (`s == r`, whether
    /// the part inside has a run there or not, S-1206).
    fn run_level(
        &mut self,
        key: &NodeKey,
        levels: &Rc<[Level]>,
        b: usize,
        s: i32,
        ctx: Ctx,
        ins: Vec<Value>,
    ) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        if self.low_stack() {
            return Err(here(LOW_STACK));
        }
        if s != 0 && !on_tick(ctx, s) {
            return Ok(());
        }
        if b == 0 {
            self.cut(key, levels, 0, s, at)?;
            return self.run_head(key, &levels[0], s, ctx, &ins);
        }
        let (lv, inside) = (&levels[b], &levels[b - 1]);
        if lv.when().is_some() {
            return self.run_when(key, levels, b, s, ctx, ins);
        }
        if lv.reset().is_some() {
            return self.run_reset(key, levels, b, s, ctx, ins);
        }
        let r = lv.ratio;
        let n = r.unsigned_abs();
        if r < 0 {
            let y = s + n as i32;
            if y <= 0 && inside.stages.contains(&y) {
                // The runs read the rings it gathers: a part due to be put back at this tick is put back first (`cut`), its rings too, so that all the runs read them put back (S-1226 (γ)).
                if !lv.gathers.is_empty() {
                    self.cut(key, levels, b, s, at)?;
                }
                let mut now = Vec::new();
                for (i, v) in ins.iter().enumerate() {
                    now.push(if lv.gathers.contains(&i) { self.ring(key, b, i, at)? } else { v.clone() });
                }
                self.run_level(key, levels, b - 1, y, time_of(ctx, r, 0), now)?;
            }
            // No `cut` before the array is dealt: a reset due at this tick put the part back at a work of the run of the part inside just before (its stage 0 makes the output), or puts it back, the array too, at the end of this stage.
            if lv.deals && s == r {
                let Value::Burst(es) = self.level_out(key, levels, b - 1, time_of(ctx, r, 0), at)? else {
                    return Err(here(Internal("an output at `sample * N` that is not a burst")));
                };
                let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
                let cell =
                    run.state.cells.get_mut(&key.role(Role::Deal(b))).ok_or(here(Internal("a deal with no array")))?;
                cell.current = Store::Last(Value::Array(es));
            }
            // The ring of the last boundary is written after the frame (`save_gathers`).
            for &i in lv.gathers.iter().filter(|_| b + 1 < levels.len()) {
                if lv.ins[i].is_some_and(|k| k.min(0) == s) {
                    self.cut(key, levels, b, s, at)?;
                    let items = match &ins[i] {
                        Value::Burst(es) => es.clone(),
                        v => vec![v.clone()],
                    };
                    self.write_ring(key, b, i, items, at)?;
                }
            }
        } else {
            // The runs of the frame: the stages slower than the boundary's `sample` once (the run 0), its own `sample` in each of the runs, and the elements of the output of the runs in a row at the stage that makes them.
            if lv.out > 0 && s == 0 && lv.made == 0 {
                self.holds_burst(lv.out, at)?;
            }
            let mut outs = Vec::new();
            for j in 0..1u32 << r {
                let (cj, now) = (time_of(ctx, r, j), self.slices(&inside.ins, r, j, &ins, at)?);
                let runs = if s < 0 {
                    (j == 0).then_some(s - r).into_iter().collect()
                } else {
                    inside.stages.iter().copied().filter(|y| *y >= -r).collect::<Vec<_>>()
                };
                for y in runs.into_iter().filter(|y| inside.stages.contains(y)) {
                    self.run_level(key, levels, b - 1, y, cj, now.clone())?;
                }
                if lv.out > 0 && s == 0 && lv.made == 0 {
                    self.cut(key, levels, b, s, at)?;
                    match self.level_out(key, levels, b - 1, cj, at)? {
                        Value::Burst(es) => outs.extend(es),
                        v if inside.out >= 0 || on_tick(cj, inside.out) => outs.push(v),
                        _ => {}
                    }
                }
            }
            if lv.out > 0 && s == 0 && lv.made == 0 {
                counted(&outs, lv.out).map_err(here)?;
                self.child_mut(key, at)?.bursts[b] = outs;
            }
        }
        Ok(())
    }

    /// The condition of each `when~` and `reset_if~` of the chain at `key` that is read in the stage `sx` of this one (`Guard::at`, §11.10: at its W or its tick, where the arguments of the head of that clock are read), but one that
    /// a boundary gathers, which its part reads from its port (`cond_of`). Those of one stage are read outermost first.
    // SPEC-GAP(S-1221): the condition of a `when~` or `reset_if~` inside a `when~` is read at its W or tick whether or not the outer one runs the part (provisional, as the arguments of the head are; only a panic shows it), and
    // the conditions of a stage outermost first (the order the spec does not say either).
    fn read_conds(&mut self, key: &NodeKey, levels: &[Level], sx: i32) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        for (b, when) in levels.iter().enumerate().rev().filter_map(|(b, lv)| lv.guard.map(|w| (b, w))) {
            if when.at == sx && when.port.is_none() {
                let v = self.eval_staged(key.call, when.cond, Stage::Tick(sx))?;
                self.gate(key, b, at)?.cond = v;
            }
        }
        Ok(())
    }

    /// The condition of the modifier that makes the part `b` of the chain at `key`, whose ports are `ins`: from its port where a boundary gathers it (`rate::gathered`), else what the caller read (`read_conds`).
    fn cond_of(&mut self, key: &NodeKey, levels: &[Level], b: usize, ins: &[Value], at: Span) -> Eval {
        match levels[b].guard.and_then(|g| g.port) {
            Some(n) => Ok(ins[n].clone()),
            None => Ok(self.gate(key, b, at)?.cond.clone()),
        }
    }

    /// What the `when~` that makes the part `b` of the chain at `key` keeps.
    fn gate(&mut self, key: &NodeKey, b: usize, at: Span) -> Result<&mut Gate, Stop> {
        let gate = self.child_mut(key, at)?.whens.get_mut(b).and_then(Option::as_mut);
        gate.ok_or(Stop { fault: Internal(NO_GATE), at })
    }

    /// The stage `s` of the part `b`, a `.when~(c)` (§11.10, S-1209), in its frame at the time `ctx`: at W it takes the condition the caller read (`read_conds`) and, while it holds, runs the stages of the part
    /// slower than W (on the grid of the frames the part ran, the slowest first) before the stage W; any other stage of the part runs while it holds. At W it holds the output of the part that ran, else keeps the last one (an
    /// output at `sample * N` is then its last element at each of its N ticks, S-1222), and the `sample` of P counts the frames the part ran (§11.9). The time goes on as the caller's (§11.4, S-1129 (1)).
    fn run_when(
        &mut self,
        key: &NodeKey,
        levels: &Rc<[Level]>,
        b: usize,
        s: i32,
        ctx: Ctx,
        ins: Vec<Value>,
    ) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let Some(Guard { w, .. }) = levels[b].when() else { return Err(Stop { fault: Internal(NO_GATE), at }) };
        // A stage slower than W is the tick an input of the head is read at by the caller (`rate::when_level`); the part reads it in W.
        if s < w {
            return Ok(());
        }
        if s == w {
            let Value::Bool(on) = self.cond_of(key, levels, b, &ins, at)? else {
                return Err(Stop { fault: Internal("a condition of a `when~` that was not read at its W"), at });
            };
            self.gate(key, b, at)?.on = on;
        }
        let (on, runs) = self.gate(key, b, at).map(|g| (g.on, g.runs))?;
        let part = ctx.with_grid(runs);
        let inside = &levels[b - 1];
        if on {
            let slower = inside.stages.iter().copied().filter(|y| s == w && *y < w);
            for y in slower.chain(inside.stages.contains(&s).then_some(s)).collect::<Vec<_>>() {
                self.run_level(key, levels, b - 1, y, part, ins.clone())?;
            }
        }
        if s == w {
            self.cut(key, levels, b, w, at)?;
            let held = match (on, &self.gate(key, b, at)?.held) {
                (true, _) => self.level_out(key, levels, b - 1, part, at)?,
                (false, Value::Burst(es)) => {
                    let last = es.last().ok_or(Stop { fault: Internal("an empty burst held"), at })?;
                    Value::Burst(vec![last.clone(); es.len()])
                }
                (false, v) => v.clone(),
            };
            self.gate(key, b, at)?.held = held;
        }
        if on && s == 0 {
            let gate = self.gate(key, b, at)?;
            gate.runs = gate.runs.wrapping_add(1);
        }
        Ok(())
    }

    /// The stage `s` of the part `b`, a `.reset_if~(c)` (§11.10, S-1186, S-1218), in its frame at the time `ctx`: at its tick it takes its condition (`cond_of`), and if it holds the part is due to be put back before the first
    /// work of it that is not in a slower stage (`cut`), or else after the stage it makes its output in (`Level::made`, before the caller reads it there) or its last stage of the frame (a part with no such work here: one that a
    /// `when~` inside stops, a boundary that deals an array made at a slower tick).
    fn run_reset(
        &mut self,
        key: &NodeKey,
        levels: &Rc<[Level]>,
        b: usize,
        s: i32,
        ctx: Ctx,
        ins: Vec<Value>,
    ) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        if levels[b].reset().is_some_and(|r| r.w == s) {
            let Value::Bool(due) = self.cond_of(key, levels, b, &ins, at)? else {
                return Err(Stop { fault: Internal("a condition of a `reset_if~` that was not read at its tick"), at });
            };
            self.gate(key, b, at)?.due = due;
        }
        if levels[b - 1].stages.contains(&s) {
            self.run_level(key, levels, b - 1, s, ctx, ins)?;
        }
        if levels[b].made == s || levels[b].stages.last() == Some(&s) {
            self.put_back(key, b, at)?;
        }
        Ok(())
    }

    /// Before a work of the part `b` at its stage `s` (the stage of a head, the rings it reads and writes, the output a `when~` holds), each `reset_if~` outside it that is due and whose tick is not faster than the stage
    /// of its caller the work is in puts its part back (§11.10: "その刻みに続く x の段の前に"; S-1228 (P)): the work of a slower stage writes first ("条件の刻みより遅い刻みは、…その位置で先に書いた後に戻す"). That stage is
    /// `s` moved out of the parts between as their stages are (`Level::outer`): out of a boundary by `caller_stage`, and to W by a `when~`, which runs the work of the slower ticks inside in its W (§11.9,
    /// `rate::when_level`), so a `reset_if~` outside it puts the part back before that work, and one inside it after.
    fn cut(&mut self, key: &NodeKey, levels: &[Level], b: usize, s: i32, at: Span) -> Result<(), Stop> {
        let mut label = s;
        for (c, lv) in levels.iter().enumerate().skip(b + 1) {
            label = lv.outer(label);
            if lv.reset().is_some_and(|r| label >= r.w) {
                self.put_back(key, c, at)?;
            }
        }
        Ok(())
    }

    /// The part inside the `reset_if~` `c` of the chain at `key`, if it is due, back to its start (§11.10, S-1186): the rings of the boundaries inside (their elements; the place goes on, so the frames after write
    /// in order) and the arrays they deal, the output each `when~` inside holds, and the head as the generated `reset` puts it back but for the phase counters and what the `when~`s remember (`InstState::reset`), with
    /// the fields that a tick writes and a faster stage reads at `T.default()` (`Frame::restart`).
    fn put_back(&mut self, key: &NodeKey, c: usize, at: Span) -> Result<(), Stop> {
        let gate = self.gate(key, c, at)?;
        if !std::mem::take(&mut gate.due) {
            return Ok(());
        }
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        let inside = |k: &NodeKey| match k.role {
            Role::Gather { bound, .. } | Role::Deal(bound) => {
                k.call == key.call && k.replicas == key.replicas && bound < c
            }
            _ => false,
        };
        run.state.cells.iter_mut().filter(|(k, _)| inside(k)).for_each(|(_, cell)| cell.back(true));
        let child = self.child_mut(key, at)?;
        child.whens.iter_mut().take(c).flatten().for_each(|g| g.reset(true));
        child.state.reset(true);
        self.restart(key, false)
    }

    /// A burst of the stream at `sample * 2^q` is not made of more elements than the evaluator holds (`Limits`): a run of `.up~(N)`s, or an input of a parameter kind, of a large N.
    fn holds_burst(&self, q: i32, at: Span) -> Result<(), Stop> {
        match self.limits.holds(n_of(q) as usize) {
            true => Ok(()),
            false => Err(Stop {
                fault: Fault::Unavailable("a burst at `sample * N` of more elements than the evaluator holds"),
                at,
            }),
        }
    }

    /// The inputs of the part inside an `.up~(N)` boundary of the ratio `r`, for its run `j` (`rate::slice`).
    fn slices(&self, inside: &[Option<i32>], r: i32, j: u32, ins: &[Value], at: Span) -> Result<Vec<Value>, Stop> {
        let one = |(k, v): (&Option<i32>, &Value)| slice(*k, r, j, v).map_err(|fault| Stop { fault, at });
        inside.iter().zip(ins).map(one).collect()
    }

    /// The head runs its stage `s` at the time `ctx` with the inputs at that stage (an input at `sample * 2^k` is an array of its `2^k` elements).
    fn run_head(&mut self, key: &NodeKey, head: &Level, s: i32, ctx: Ctx, ins: &[Value]) -> Result<(), Stop> {
        let at = self.body.ast.expr(key.call).span;
        let here = |fault| Stop { fault, at };
        let view = self.body.view;
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let child = run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?;
        let decl = view.flow(child.def).map_err(here)?;
        let stage = Stage::Tick(s);
        let mut now = Vec::new();
        for (n, i) in decl.inputs.iter().enumerate() {
            if input_stage(i).map_err(here)? == stage {
                if matches!(ins[n], Value::Unit) {
                    return Err(here(Internal("an input of the head that was not made before its stage")));
                }
                now.push((
                    i.name.as_str(),
                    match (&ins[n], head.ins[n]) {
                        (Value::Burst(es), Some(k)) if k > 0 => Value::Array(es.clone()),
                        (v, _) => v.clone(),
                    },
                ));
            }
        }
        self.in_child(key, |f, inst, decl| {
            f.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?.ctx = ctx;
            enter(f, inst, decl, stage, &now)
        })
    }

    /// What the part `b` of the chain at `key` gives in its frame at the time `ctx`, the output boundary (§11.9): `m` its clock, a burst of its `2^m` values for `m > 0` (`Value::Burst`) and one value for `m <= 0`. The head gives
    /// the output of its last run (the `2^m` elements of its array for `m > 0`); a `.down~(N)` boundary that deals gives the elements from `phase * 2^m` of the array it dealt (or the one that the tick of `sample / 2^-m` it is in has), another
    /// the output of the part inside, held until its next tick; an `.up~(N)` boundary gives the elements of its N runs in a row for `m > 0`, else the output of the last run.
    pub(super) fn level_out(&self, key: &NodeKey, levels: &[Level], b: usize, ctx: Ctx, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let run = self.run.as_ref().ok_or(here(Internal("no run")))?;
        let child = run.state.children.get(key).ok_or(here(Internal("an instance with no state")))?;
        let (lv, burst) = (&levels[b], |es: Vec<Value>, m| counted(&es, m).map(|()| Value::Burst(es)).map_err(here));
        let r = lv.ratio;
        if lv.when().is_some() {
            return child.whens.get(b).and_then(Option::as_ref).map(|g| g.held.clone()).ok_or(here(Internal(NO_GATE)));
        }
        if lv.reset().is_some() {
            return self.level_out(key, levels, b - 1, ctx, at);
        }
        match (b, r.cmp(&0)) {
            (0, _) if lv.out > 0 => burst(elements(lv.out, &child.out).map_err(here)?, lv.out),
            (0, _) => Ok(child.out.clone()),
            (_, std::cmp::Ordering::Less) if lv.deals => {
                let cell = run.state.cells.get(&key.role(Role::Deal(b))).map(|c| &c.current);
                let Some(Store::Last(Value::Array(vs))) = cell else {
                    return Err(here(Internal("a deal with no array")));
                };
                let (from, n) = dealt(levels[b - 1].out, r, phase(ctx, r));
                match (vs.get(from..from + n), lv.out > 0) {
                    (Some(part), true) => burst(part.to_vec(), lv.out),
                    (Some([one]), false) => Ok(one.clone()),
                    _ => Err(here(Internal("a dealt array that is not `sample * N` long"))),
                }
            }
            (_, std::cmp::Ordering::Less) => self.level_out(key, levels, b - 1, time_of(ctx, r, 0), at),
            _ if lv.out > 0 && lv.made < 0 => {
                self.holds_burst(lv.out, at)?;
                let mut outs = Vec::new();
                for j in 0..1u32 << r {
                    let cj = time_of(ctx, r, j);
                    match self.level_out(key, levels, b - 1, cj, at)? {
                        Value::Burst(es) => outs.extend(es),
                        v if levels[b - 1].out >= 0 || on_tick(cj, levels[b - 1].out) => outs.push(v),
                        _ => {}
                    }
                }
                burst(outs, lv.out)
            }
            _ if lv.out > 0 => burst(child.bursts[b].clone(), lv.out),
            _ => self.level_out(key, levels, b - 1, time_of(ctx, r, (1 << r) - 1), at),
        }
    }

    /// The elements the ring of the input number `input` of the boundary `b` of the chain at `key` holds, the oldest first (the last is the one of the frame before): the `2^k` the part inside reads at its tick. The frames between
    /// two ticks write all of the ring (`2^q` of each of the `2^-r` frames, the one of each tick of a slower stream), so at a tick it is back at its first place and the buffer is in order.
    fn ring(&self, key: &NodeKey, b: usize, input: usize, at: Span) -> Eval {
        let run = self.run.as_ref().ok_or(Stop { fault: Internal("no run"), at })?;
        let cell = run.state.cells.get(&key.role(Role::Gather { bound: b, input })).map(|c| &c.current);
        let Some(Store::Ring { buf, .. }) = cell else {
            return Err(Stop { fault: Internal("a gather with no ring"), at });
        };
        Ok(Value::Burst(buf.clone()))
    }

    /// The elements of the frame of an input of the boundary `b` go into its ring, in order.
    fn write_ring(&mut self, key: &NodeKey, b: usize, input: usize, items: Vec<Value>, at: Span) -> Result<(), Stop> {
        let run = self.run.as_mut().ok_or(Stop { fault: Internal("no run"), at })?;
        let cell = run.state.cells.get_mut(&key.role(Role::Gather { bound: b, input })).map(|c| &mut c.current);
        let Some(Store::Ring { buf, w }) = cell else {
            return Err(Stop { fault: Internal("a gather with no ring"), at });
        };
        for v in items {
            buf[*w] = v;
            *w = (*w + 1) % buf.len();
        }
        Ok(())
    }
}
