//! A chain of `.when~(c)` and `.reset_if~(r)` on a built-in delay (§11.10: "受け手は flow の呼び出し（組込みの遅延を含む。括弧で包んでもよい）"). The delay ticks at K, the clock of its first
//! argument (§11.4), and takes no `.down~`/`.up~` (E0812), so the place P of each modifier is K and so is the W of a `when~` (§11.10, §11.9: "組込みの遅延は第 1 引数のクロック"). The chain
//! is the expression, made at each tick of K (or by the stage of K that `hoist.rs` gives it), so a tick of it is one evaluation: the modifiers are taken from the outermost in. A
//! `reset_if~` whose condition holds at its tick R (the clock of the condition, `at` included, or K for a value of the parameter kinds and `sample_tick()`) puts the values and the write
//! position of the delay back to its `init` (the copy made at `init`, which keeps a value of the kind `init`) and the output each `when~` inside it holds to `T.default()`, before the delay
//! reads. R is not faster than K (E0815): a slower one is on the grid of the part it wraps, which is the caller's outside every `when~` (§11.9: the tick of R comes first at its position,
//! and the delay has no other work there) and, inside one, the frames the part ran ("`when~` の中の格子は動いた刻みで数える"; a run at K is 2^-K frames of `sample`). A `when~` whose condition
//! does not hold stops the part: the delay neither reads nor stores, and the caller reads the last output it held, `T.default()` if it never ran, whatever `init` the delay has ("一度も動いていなければ
//! `T.default()`"); "受け手の本体の `sample` は動いた刻みを指し（…`prev~` と遅延の長さはそこから数え…）". The arguments of the delay are the caller's ("頭の引数…は呼び出し側のもので、止まっている間も評価する"): the `d` of a `vdelay~` is evaluated at each
//! tick, and the value it stores in the second phase too, which stores it only where the delay ran. The conditions are read at each tick from the outermost in, a `reset_if~`'s outside
//! every `when~` at its R alone, and one inside a `when~` whether it runs the part or not (S-1221, as the conditions of an instance, `Frame::read_conds`).

use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::flow_names::Delay;
use onsa_syntax::ast::{ExprId, ExprKind};

use super::chain::Gate;
use super::expr::{Eval, Frame, Stop};
use super::flow::{Clock, Ctx, Inst};
use super::rate::{Bound, cond_tick, n_of, on_tick};
use super::scalar::Fault::{self, Internal};
use super::state::{NodeKey, Role, read_store};
use super::value::Value;

/// A modifier of a chain on a delay: its condition, and the tick R of a `reset_if~` (`None` for a `when~`, read at each tick of K).
#[derive(Clone, Copy, Debug)]
pub(super) struct Mod {
    cond: ExprId,
    reset: Option<i32>,
    /// A `reset_if~` whose condition is an event of another source than the clock of the delay: it is read and puts the delay back at the stage of that event (`Frame::reset_on_event`), not where the delay is read.
    ev: bool,
}

/// What a chain on a delay keeps besides the cell of the delay: K, the modifiers innermost first with a `Gate` for each (a `when~` holds its output and counts the frames its part ran), and the
/// time of the caller it last ticked at with what it gave: a frame may evaluate the chain twice (the object of a `match~` whose binding a ring gathers, `Frame::commit` evaluates again with
/// `eval_in_arms`), and the second gives the same and moves nothing, as `Inst::done` runs a stage of an instance once a frame.
#[derive(Clone, Debug)]
pub(super) struct DelayMods {
    k: i32,
    /// Does the delay tick at an event (`k` is 0 then)? What it gave is kept for the run of its stage (`Run::serial`) and not for the time, which has many events.
    event: bool,
    mods: Rc<[Mod]>,
    gates: Vec<Gate>,
    last: Option<(u64, Value)>,
}

impl DelayMods {
    /// `init` and the generated `reset` (`soft` false), and a `reset_if~` of a part it is in (true): as the `when~`s of an instance (`InstState::reset`).
    pub(super) fn reset(&mut self, soft: bool) {
        self.gates.iter_mut().for_each(|g| g.reset(soft));
        self.last = None;
    }
}

impl DelayMods {
    /// A `reset_if~` of an event that wraps the first `inside` modifiers comes: the output each `when~` among them holds goes back to `T.default()`.
    pub(super) fn put_back(&mut self, inside: usize) {
        self.gates.iter_mut().take(inside).for_each(|g| g.reset(true));
    }
}

/// Is the time `grid` at a tick of R of a chain on a delay that ticks at K (every tick of K for an R that is not slower)?
fn on_r(grid: Ctx, r: i32, k: i32) -> bool {
    r >= k || on_tick(grid, r)
}

impl<'a> Frame<'a> {
    /// What the chain of the modifiers `bounds` on the delay `head` keeps, made at `init` (its places held first); the clocks are those of the plan of this body (`rate::slow_ticks`).
    pub(super) fn make_mods(&mut self, head: ExprId, bounds: &[Bound]) -> Result<(), Stop> {
        let at = self.body.ast.expr(head).span;
        let here = |fault| Stop { fault, at };
        let plans = self.run.as_ref().map(|r| r.plans.clone()).ok_or(here(Internal("no run")))?;
        let conds = Inst::planned(self.body.view, self.body.def, &plans)?.conds;
        let clock = |c: ExprId| conds.get(&c).copied().ok_or(here(Internal("a condition of a modifier with no clock")));
        let own = clock(head)?.clock.rooted();
        let (k, event) = match own {
            Clock::Tick(k) => (k, false),
            Clock::Event(_) => (0, true),
            _ => return Err(here(Internal("a delay that is not at a tick"))),
        };
        let (mut mods, mut gates) = (Vec::new(), Vec::new());
        for b in bounds {
            let (cond, reset, ev) = match *b {
                Bound::When(c) => (c, None, false),
                Bound::ResetIf(c) => {
                    let cc = clock(c)?.clock;
                    (c, Some(cond_tick(cc, k, &[])), matches!(cc, Clock::Event(_)) && cc != own)
                }
                Bound::Rate(_) => return Err(here(Internal("a delay with a `.down~` or an `.up~`"))),
            };
            mods.push(Mod { cond, reset, ev });
            if reset.is_some() {
                gates.push(Gate::new(Value::Unit));
                continue;
            }
            let shape = self.shape(self.body.ty(head).map_err(here)?, at)?;
            self.hold(Some(shape.places()), at)?;
            gates.push(Gate::new(shape.default_value().ok_or(here(Internal("a held type with no default")))?));
        }
        let key = self.key(head, Role::Delay);
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        run.state.mods.insert(key, DelayMods { k, event, mods: mods.into(), gates, last: None });
        Ok(())
    }

    /// A tick of the chain on the delay `head` (`d` of it): its arguments and the conditions read at it first, then the resets, the `when~`s that stop it, the read of the delay and the save of
    /// what it stores (the module).
    pub(super) fn delay_chain(&mut self, head: ExprId, d: Delay, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let ast = self.body.ast;
        let ExprKind::Call { args, .. } = &ast.expr(head).kind else {
            return Err(here(Internal("a chain with no head call")));
        };
        let arg = |i: usize| args.get(i).map(|a| a.expr).ok_or(here(Internal("a delay with too few arguments")));
        let (key, now) = (self.key(head, Role::Delay), self.time(at)?);
        let (k, mods, last, event) = self.mods_of(&key, at).map(|m| (m.k, m.mods.clone(), m.last.clone(), m.event))?;
        let stamp = if event { self.run.as_ref().map_or(0, |r| r.serial) } else { now.total() };
        if let Some((_, v)) = last.filter(|(t, _)| *t == stamp) {
            return Ok(v);
        }
        let saved = arg(Delay::SAVED)?;
        let slot = self.reserve_save(key.clone(), saved, at)?;
        self.early_calls(saved)?;
        self.snapshot(slot, saved);
        let dc = match d.d_index() {
            Some(i) => Some(self.eval(arg(i)?)?),
            None => None,
        };
        let events: Vec<ExprId> = mods.iter().filter(|m| m.ev).map(|m| m.cond).collect();
        self.early_conditions(slot, &events)?;
        // SPEC-GAP(S-1221): the `d` of a `vdelay~` is evaluated before the conditions, and a condition inside a `when~` is read whether or not it runs the part, the conditions leftmost first
        // (provisional, as `Frame::read_conds` reads those of an instance after the arguments of its head; only a panic shows it).
        // A `reset_if~` outside every `when~` is read at its R alone, and is due where it holds; one inside is due at the R of the grid of the part (below).
        // The conditions are read in the order written, the leftmost first (S-1233); one is inside a `when~` when a `when~` is outside it, to its right.
        let mut read = vec![false; mods.len()];
        for (b, m) in mods.iter().enumerate() {
            let inside = mods[b + 1..].iter().any(|o| o.reset.is_none());
            if m.ev {
                continue;
            }
            if inside || m.reset.is_none_or(|r| on_r(now, r, k)) {
                let Value::Bool(v) = self.eval(m.cond)? else {
                    return Err(here(Internal("a condition that is no `Bool`")));
                };
                read[b] = v;
            }
        }
        let run = self.run.as_mut().ok_or(here(Internal("no run")))?;
        let (cells, all) = (&mut run.state.cells, &mut run.state.mods);
        let (cell, state) = (cells.get_mut(&key), all.get_mut(&key));
        let (Some(cell), Some(state)) = (cell, state) else { return Err(here(Internal("a delay with no state"))) };
        // From the outermost in: a reset puts the part back, a `when~` that holds moves the grid to the frames its part ran, one that does not stops it.
        let (mut grid, mut stop, mut inside) = (now, None, false);
        for (b, m) in mods.iter().enumerate().rev() {
            match m.reset {
                Some(r) if read[b] && (!inside || on_r(grid, r, k)) => {
                    cell.current = cell.initial.clone();
                    state.gates[..b].iter_mut().for_each(|g| g.reset(true));
                }
                Some(_) => {}
                None if read[b] => (grid, inside) = (now.with_grid(state.gates[b].runs), true),
                None => {
                    stop = Some(b);
                    break;
                }
            }
        }
        let out = match stop {
            None => read_store(&cell.current, dc.as_ref()).map_err(here)?,
            Some(b) => state.gates[b].held.clone(),
        };
        for (g, _) in
            state.gates.iter_mut().zip(mods.iter()).skip(stop.map_or(0, |b| b + 1)).filter(|(_, m)| m.reset.is_none())
        {
            g.held = out.clone();
            g.runs = g.runs.wrapping_add(n_of(k));
        }
        state.last = Some((stamp, out.clone()));
        self.set_keep(slot, stop.is_none());
        Ok(out)
    }

    fn mods_of(&self, key: &NodeKey, at: Span) -> Result<&DelayMods, Stop> {
        let mods = self.run.as_ref().and_then(|r| r.state.mods.get(key));
        mods.ok_or(Stop { fault: Fault::Internal("a chain on a delay with no state"), at })
    }
}
