//! The chains of `.down~(N)` and `.up~(N)` in the functions of the stages
//! (§11.9, S-1207): the counter of a frame, folded from the counter of the
//! phase of this flow and the run j of each `.up~` around, and the place of
//! a window of a ring or an array at it; the work of an instance in the
//! function of a stage as the table of the plan gives it ([`Entry`]: the
//! rings it writes, the runs of the stages of its head, the arrays it deals
//! in, each by one copy, the N runs of an `.up~` in a loop) and the array
//! it is read from.

use super::*;
use onsa_sema::flow::{CondRead, PlanGuard};

/// The walk of the ops of an entry of the instance `id` (`n`) in the scope
/// of `state` (§11.9): the run j of each `.up~` around the ops lowered, by
/// its boundary ([`counter`]); the arguments and the conditions its ops
/// read, lowered before them ([`ports`]); the value the ops make in a loop, a
/// local made at the head of the entry.
struct Walk<'a> {
    info: &'a FlowInfo,
    id: NodeId,
    n: &'a PlanNode,
    state: &'a Expr,
    span: Span,
    js: Vec<(usize, Expr)>,
    /// Each with the exponent of its port, of a burst, in the frame of the call.
    ports: Vec<(Port, Expr, Option<Ratio>)>,
    value: Option<Expr>,
}

impl<'a> Walk<'a> {
    fn new(info: &'a FlowInfo, id: NodeId, state: &'a Expr, span: Span) -> Self {
        Walk { info, id, n: info.node(id), state, span, js: Vec::new(), ports: Vec::new(), value: None }
    }

    fn field(&self, lw: &Lowerer, part: Part) -> R<Expr> {
        sfield(lw, self.info, self.state, FieldOf::Node(self.id, part), self.span)
    }

    /// `_ran` of a delay a guard stops set to `on` (§11.10: its store is of the ticks it ran).
    fn ran(&self, lw: &Lowerer, out: &mut Vec<Stmt>, on: bool) -> R<()> {
        match self.info.field_at(FieldOf::Node(self.id, Part::Ran)) {
            Some(_) => assign(out, &self.field(lw, Part::Ran)?, lit(Ty::Bool, self.span, Lit::Bool(on))),
            None => Ok(()),
        }
    }

    fn bound(&self, b: u32) -> R<&'a onsa_sema::flow::PlanBound> {
        self.n.bounds.get(b as usize).ok_or_else(|| internal(self.span, format!("no boundary {b}")))
    }

    fn guard(&self, g: u32) -> R<&'a onsa_sema::flow::PlanGuard> {
        self.n.guards.get(g as usize).ok_or_else(|| internal(self.span, format!("no guard {g}")))
    }

    /// The condition of the modifier at `place` of the chain, as its op reads
    /// it (§11.10): the slot of the ring that gathers it in the frame of the
    /// modifier ([`Walk::ring`]; one element, its port being no faster than
    /// W) in a local, which a reset of the ring after does not change; else
    /// its value ([`Walk::port`]).
    fn cond(&self, lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, place: u32) -> R<Expr> {
        let Some(o) = self.ring(place) else { return Ok(self.port(Port::Cond(place))?.0) };
        let (part, f, span) = (Part::Gather { bound: o, port: Port::Cond(place) }, self.frame(place), self.span);
        let x = self.n.chain.get(place as usize).and_then(|m| m.port);
        let (x, e) = (x.ok_or_else(|| internal(span, "a ring of a condition of no port"))?, exp(self.n, part, span)?);
        let v = index(self.field(lw, part)?, at(lw, cx, self, (f, o as usize), x, e)?)?;
        let l = cx.temp("__on", Ty::Bool);
        out.push(stmt(span, StmtKind::Let(l, v)));
        Ok(local_expr(cx, l, span))
    }

    /// The argument or the condition of `port`, lowered before the ops ([`ports`]).
    fn port(&self, port: Port) -> R<(Expr, Option<Ratio>)> {
        let found = self.ports.iter().find(|x| x.0 == port);
        found.map(|x| (x.1.clone(), x.2)).ok_or_else(|| internal(self.span, format!("{port:?} not lowered")))
    }

    /// The frame of the modifier at `place`: the count of the boundaries
    /// inside it.
    fn frame(&self, place: u32) -> usize {
        self.n.inside(place) as usize
    }

    /// The boundary whose ring the condition of the modifier at `place` is
    /// read from in its frame ([`PlanNode::ring_of`]), if one gathers it.
    fn ring(&self, place: u32) -> Option<u32> {
        self.n.ring_of(self.frame(place), Port::Cond(place))
    }

    /// The frame a guard is in, by the count of the boundaries inside it,
    /// and the exponent of the output of the part it wraps there.
    fn guard_frame(&self, g: u32) -> R<(usize, Ratio)> {
        let guard = self.guard(g)?;
        let out = guard.out.ok_or_else(|| internal(self.span, "a held output of no clock"))?;
        Ok((self.n.inside(guard.at) as usize, out))
    }

    /// The exponent of the output of the head in the frame of the call of
    /// the innermost boundary (of the call of the chain with none).
    fn head_out(&self) -> R<Ratio> {
        let out = match (self.n.bounds.first(), self.n.clock) {
            (Some(b), _) => b.out,
            (None, Clock::Tick(o)) => Some(o),
            (None, _) => None,
        };
        out.ok_or_else(|| internal(self.span, "a run of no output"))
    }

    /// The run j of the `.up~` of the boundary `b` the ops are lowered in.
    fn j(&self, b: usize) -> Option<&Expr> {
        self.js.iter().find(|x| x.0 == b).map(|x| &x.1)
    }
}

/// The words of a count of the frames of the caller of a boundary of the
/// ratio `r` as those of the part it wraps (§11.4, S-1217): of a
/// `.down~(2^s)`, `[c >> s]` of one (the phase, its low word alone),
/// `[(t >> s) | (t_hi << (32 − s)), t_hi >> s]` of two (the time, divided
/// before it is cut to `U32`); of an `.up~(2^s)` at its run `j`, the count
/// 2^s times and j: `[(c << s) | j]`,
/// `[(t << s) | j, (t_hi << s) | (t >> (32 − s))]`; the arm of j there and
/// of none else (an `.up~` around the stage of an event has no j, its time the
/// run 0, [`child_time`]). The one step of the counters and the time.
fn fold(words: &[Expr], r: Ratio, j: Option<&Expr>, span: Span) -> R<Vec<Expr>> {
    let s = Some(r.0.unsigned_abs()).filter(|&s| s > 0 && s < 32);
    let s = s.ok_or_else(|| internal(span, format!("a count under a boundary of the ratio {r:?}")))?;
    let shift = |op, x: &Expr, by| checked_binary(op, x.clone(), u32_lit(span, by));
    let or = |a, b| checked_binary(BinOp::BitOr, a, b);
    match (words, j) {
        ([c], None) => Ok(vec![shift(BinOp::Shr, c, s)]),
        ([t, hi], None) => {
            Ok(vec![or(shift(BinOp::Shr, t, s), shift(BinOp::Shl, hi, 32 - s)), shift(BinOp::Shr, hi, s)])
        }
        ([c], Some(j)) => Ok(vec![or(shift(BinOp::Shl, c, s), j.clone())]),
        ([t, hi], Some(j)) => {
            Ok(vec![or(shift(BinOp::Shl, t, s), j.clone()), or(shift(BinOp::Shl, hi, s), shift(BinOp::Shr, t, 32 - s))])
        }
        _ => Err(internal(span, format!("a count of {} words", words.len()))),
    }
}

/// The time the callee of the walk takes from that of its caller (§11.4,
/// S-1217): two words folded out of each boundary, the outermost first, in
/// `let`s `t_in`, `t_hi_in` into `out` that the next shares, cut to `words`.
fn child_time(cx: &mut FnCx, out: &mut Vec<Stmt>, w: &Walk, words: usize) -> R<Vec<Expr>> {
    let mut time = cx.flow.as_ref().expect("flow context").now.time.clone();
    // The stage of an event in an `.up~` is of no run of it: the run 0 (§11.4).
    let first = u32_lit(w.span, 0);
    for (k, b) in w.n.bounds.iter().enumerate().rev() {
        // One word divided would lose the upper (S-1211): the table gives two under a `.down~`.
        if b.ratio.slower_than_body() && time.len() != 2 {
            return Err(internal(w.span, "one word of time"));
        }
        let j = w.j(k).or((!b.ratio.slower_than_body()).then_some(&first));
        let kept = fold(&time, b.ratio, j, w.span)?.into_iter().take(if k == 0 { words } else { 2 });
        time = kept.zip(["t_in", "t_hi_in"]).map(|(e, name)| materialize(cx, e, out, name)).collect();
    }
    let time = time.get(..words).ok_or_else(|| internal(w.span, format!("a callee of {words} words of time")))?;
    Ok(time.to_vec())
}

/// The counter of the frame inside the boundary `from` of the walk (§11.9):
/// the counter of the phase of this flow (`_tick`) folded out of each
/// boundary from the outermost to `from` ([`fold`], at the run j of an
/// `.up~`); 0 at the start of one whose `_tick` is not of a grid (S-1217),
/// whose work is all at its `sample`, where the start is masked out of each
/// window ([`at`]).
fn counter(lw: &Lowerer, cx: &FnCx, w: &Walk, from: usize, own: usize) -> R<Expr> {
    let (f, span) = (cx.flow.as_ref().expect("flow context"), w.span);
    let root = f.now.scopes.first().ok_or_else(|| internal(span, "a chain outside the state"))?;
    let mut c = match f.info.counter() {
        Counter::Tick => vec![sfield(lw, f.info, &root.state, FieldOf::Tick, span)?],
        Counter::None | Counter::Process => vec![u32_lit(span, 0)],
    };
    let (bounds, len) = (&w.n.bounds, w.n.bounds.len());
    for k in (from..=len).rev() {
        // A guard in the frame inside the boundary k that counts the ticks it ran counts
        // those of the part it wraps (§11.9, S-1217), outermost first, of a window of
        // a boundary it wraps (outside `own`, of none of the caller's).
        let here = |g: &&PlanGuard| k > own && g.at > bounds[k - 1].at && (k == len || g.at < bounds[k].at);
        for (g, _) in (0u32..).zip(&w.n.guards).filter(|g| here(&g.1)).collect::<Vec<_>>().into_iter().rev() {
            if f.info.field_at(FieldOf::Node(w.id, Part::Count(g))).is_some() {
                c = vec![w.field(lw, Part::Count(g))?];
            }
        }
        if k > from {
            c = fold(&c, bounds[k - 1].ratio, w.j(k - 1), span)?;
        }
    }
    c.pop().ok_or_else(|| internal(span, "a counter of no word"))
}

/// The place in a window of 2^e elements (a ring, an array, §11.9) of the
/// elements of the frame inside the boundary `from` of the walk, 2^x of
/// each of its frames ([`counter`] C): `(C & (2^(e − x) − 1)) >> −x` of x ≤
/// 0 (`>> 0` too), `<< x` of 0 < x < e, 0 of the whole window ([`whole`]).
/// The one place of the places of the rings and the arrays of a chain.
fn at(lw: &Lowerer, cx: &FnCx, w: &Walk, (from, own): (usize, usize), x: Ratio, e: Ratio) -> R<Expr> {
    let span = w.span;
    if whole(x, e) {
        return Ok(u32_lit(span, 0));
    }
    let mask = u32::try_from(e.0 - x.0).ok().and_then(|w| 1u32.checked_shl(w)).map(|m| m - 1);
    let mask = mask.ok_or_else(|| internal(span, format!("a window of 2^{} of 2^{}", e.0, x.0)))?;
    let c = checked_binary(BinOp::BitAnd, counter(lw, cx, w, from, own)?, u32_lit(span, mask));
    let (op, by) = if x.0 <= 0 { (BinOp::Shr, x.0.unsigned_abs()) } else { (BinOp::Shl, x.0.unsigned_abs()) };
    Ok(checked_binary(op, c, u32_lit(span, by)))
}

/// Whether the 2^x elements of a frame are the whole of a window of 2^e
/// (§11.9): x ≥ e, or e ≤ 0, a value of one element. The one test of it
/// (D-15): the places ([`at`]), the copies ([`copy`]) and the reads
/// ([`window`]) of the windows.
fn whole(x: Ratio, e: Ratio) -> bool {
    x.0 >= e.0 || e.0 <= 0
}

/// The exponent `e` of the ring or the array `part` of `n` (`2^e`, S-1208),
/// of a port of the part its boundary wraps faster than its `sample`: of
/// an input the boundary gathers, of the output it deals.
fn exp(n: &PlanNode, part: Part, span: Span) -> R<Ratio> {
    let e = match part {
        Part::Gather { bound, port: Port::Input(i) } => {
            n.bounds.get(bound as usize).and_then(|b| *b.ins.get(i as usize)?)
        }
        Part::Gather { bound, port: Port::Cond(at) } => {
            n.bounds.get(bound as usize).and_then(|b| b.conds.iter().find(|c| c.0 == at).map(|c| c.1))
        }
        Part::Deal(bound) => n.bounds.get(bound as usize).and_then(|b| b.out),
        _ => None,
    };
    e.filter(|e| e.faster_than_body()).ok_or_else(|| internal(span, format!("a ring or an array {part:?} of {e:?}")))
}

/// The length of the ring or the array `part` of `n` ([`exp`]), of a
/// clock the Core makes ([`Ratio::made_n`]).
pub(super) fn len(n: &PlanNode, part: Part, span: Span) -> R<u32> {
    let len = exp(n, part, span)?.made_n().and_then(|n| u32::try_from(n).ok());
    len.ok_or_else(|| internal(span, format!("a ring or an array {part:?}, past `U32`")))
}

/// The entry of the instance `id` (or the delay of a chain) in the function
/// of the stage: its arguments and its conditions ([`ports`]), then its ops,
/// if it has one, in their order (§11.9, [`Entry`]), in the scope of `state` (the
/// rings, the runs, the copies and the loops of [`ops`]), and the value
/// they make: of a run out of a loop the value of the run, else, made in
/// the loop of an `.up~`, a local made at the head, `Zeroed` (every element
/// written, the memo of U6b 2.5).
pub(super) fn entry(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<Option<Expr>> {
    let (f, n) = (cx.flow.as_ref().expect("flow context"), cx.flow.as_ref().expect("flow context").info.node(id));
    let (info, list) = (f.info, n.entry(f.now.stage).map_or(&[][..], |e| &e.ops));
    let mut w = Walk::new(info, id, state, cx.ast.expr(info.node(id).expr).span);
    // The value made in a loop or under a guard (of a burst, the review of the memo of W7-10, its middle 1).
    let mut looped = false;
    for op in list.iter().filter(|op| matches!(op, Op::Each { .. } | Op::When { .. })) {
        Op::walk(std::slice::from_ref(op), &mut |op| looped |= op.makes_value());
    }
    if looped {
        let t = cx.info.expr_types.get(&w.n.expr).ok_or_else(|| internal(w.span, "an instance of no type"))?;
        let ty = burst_ty(Some(w.n.clock), lw.core_ty(*t, &[], w.span)?);
        w.value = Some(zeroed(cx, out, "__value", ty, w.span));
    }
    // A delay that a guard stops has not run until its run says so (§11.10, its store).
    let mut runs = false;
    Op::walk(list, &mut |op| runs |= matches!(op, Op::Run { .. }));
    if runs {
        w.ran(lw, out, false)?;
    }
    // The `d` of a `vdelay~` a run reads, read while it stops (§11.10), once.
    if let PlanKind::Vdelay { d, .. } = w.n.kind
        && runs
    {
        let v = lower_expr(lw, cx, d)?;
        let v = hold(cx, out, v, "__d");
        cx.flow.as_mut().expect("flow context").now.expr_override.insert(d, v);
    }
    let reads = reads(lw, &w, list)?;
    // The one op that reads a port reads it where it is (of a run, as any call does).
    let all = !matches!(list, [Op::Ring { .. } | Op::Run { .. } | Op::Reset { .. }]);
    ports(lw, cx, out, &mut w, &reads, all)?;
    let made = ops(lw, cx, out, &mut w, list)?;
    Ok(made.or(w.value))
}

/// The ops `list` of the walk `w` into `out`, in their order (§11.9): a
/// ring written at its place from the argument or the ring outside it, a
/// run of a stage of the head as a statement, into the array of the
/// boundary that deals it or as the value, the copy of an array into the
/// one outside it or into the value, each by [`copy`], and the N runs of an
/// `.up~` ([`Op::Each`]): of its `once`, the run j = 0 alone; else a loop of
/// j, each run the ops of each stage of the part when j is at its tick
/// ([`drive`]).
fn ops(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &mut Walk, list: &[Op]) -> R<Option<Expr>> {
    let (n, span, mut value) = (w.n, w.span, None);
    // The condition of each guard read in this list, as it read it.
    let mut read: Vec<(u32, Expr)> = Vec::new();
    for op in list {
        match *op {
            Op::Ring { bound: b, port, from } => {
                let part = Part::Gather { bound: b, port };
                let k = exp(n, part, span)?;
                let (x, f) = (w.bound(b)?.outside(k), b as usize + 1);
                let (dst, pos) = (w.field(lw, part)?, at(lw, cx, w, (f, b as usize), x, k)?);
                let caller = n.bounds.len();
                let src = match from {
                    Feed::Arg => match w.port(port)? {
                        (v, Some(q)) => {
                            let v = materialize(cx, v, out, "__arg");
                            Src::At(v, at(lw, cx, w, (f, caller), x, q)?, q)
                        }
                        (v, None) => Src::Value(v),
                    },
                    Feed::Ring(o) => {
                        let part = Part::Gather { bound: o, port };
                        let q = exp(n, part, span)?;
                        Src::At(w.field(lw, part)?, at(lw, cx, w, (f, o as usize), x, q)?, q)
                    }
                };
                copy(cx, out, (dst, k), pos, src, x, span)?;
            }
            Op::Run { body, out: Out::Event } => {
                let v = run(lw, cx, w, body)?;
                give(lw, cx, out, w, v)?;
            }
            Op::Run { body, out: to } => {
                let v = run(lw, cx, w, body)?;
                value = put(lw, cx, out, w, to, v, |w| Ok((0, w.head_out()?)))?.or(value);
            }
            Op::Hold { guard: g, out: to } => {
                let on = read.iter().find(|x| x.0 == g).map(|x| x.1.clone());
                let on = on.ok_or_else(|| internal(span, "a hold of a guard not read"))?;
                let ((from, o), held) = (w.guard_frame(g)?, w.field(lw, Part::Held(g))?);
                if !o.faster_than_body() {
                    value = put(lw, cx, out, w, to, held, |_| Ok((from, o)))?.or(value);
                    continue;
                }
                // A burst, made in the window of its frame of the local of the value or the
                // array that deals it: its last element held when it ran, else that N times,
                // each tick of its output reading the last element (§11.10, S-1222).
                let (v, e, own) = target(lw, w, if let Out::Deal(b) = to { To::Array(b) } else { To::Value })?;
                let (pos, n) = (at(lw, cx, w, (from, own), o, e)?, count(o, span)?);
                let last = if whole(o, e) {
                    u32_lit(span, n - 1)
                } else {
                    checked_binary(BinOp::Add, pos.clone(), u32_lit(span, n - 1))
                };
                let (mut ran, mut not) = (Vec::new(), Vec::new());
                assign(&mut ran, &held, index(v.clone(), last)?)?;
                let ty = Ty::Array(Box::new(held.ty.clone()), n);
                let all = Expr::new(ty, span, ExprKind::Repeat { elem: Box::new(held), n });
                copy(cx, &mut not, (v, e), pos, Src::Value(all), o, span)?;
                let (ran, not) = (Block { stmts: ran, value: None }, Block { stmts: not, value: None });
                out.push(stmt(span, StmtKind::If(on, ran, not)));
            }
            Op::When { guard: g, cond, due, ops: ref inner, advance } => {
                let on = match cond {
                    CondRead::Read => {
                        let v = w.cond(lw, cx, out, w.guard(g)?.at)?;
                        let v = materialize(cx, v, out, "__on");
                        if w.info.field_at(FieldOf::Node(w.id, Part::On(g))).is_some() {
                            assign(out, &w.field(lw, Part::On(g))?, v.clone())?;
                        }
                        v
                    }
                    CondRead::Local => read
                        .iter()
                        .find(|x| x.0 == g)
                        .map(|x| x.1.clone())
                        .ok_or_else(|| internal(span, "a guard of a condition not read before it"))?,
                    CondRead::Kept => w.field(lw, Part::On(g))?,
                };
                read.push((g, on.clone()));
                let mut body = Vec::new();
                // The ops under a guard make no value: they write the held output or a local.
                if ops(lw, cx, &mut body, w, inner)?.is_some() {
                    return Err(internal(span, "a value made under a guard"));
                }
                if let Some(y) = due {
                    let mut runs = Vec::new();
                    drive(vec![(y, body)], &w.field(lw, Part::Count(g))?, span, &mut runs)?;
                    body = runs;
                }
                if advance {
                    let t = w.field(lw, Part::Count(g))?;
                    assign(&mut body, &t, super::phases::wrap_add(t.clone(), span))?;
                }
                if !body.is_empty() {
                    out.push(stmt(span, StmtKind::If(on, Block { stmts: body, value: None }, Block::default())));
                }
            }
            Op::Reset { at } => {
                let on = w.cond(lw, cx, out, at)?;
                let mut body = Vec::new();
                reset(lw, cx, &mut body, w, at)?;
                if w.info.field_at(FieldOf::Node(w.id, Part::Back(at))).is_some() {
                    let mut late = Vec::new();
                    assign(&mut late, &w.field(lw, Part::Back(at))?, lit(Ty::Bool, span, Lit::Bool(true)))?;
                    let (late, now) = (Block { stmts: late, value: None }, Block { stmts: body, value: None });
                    body = vec![stmt(span, StmtKind::If(w.field(lw, Part::Open)?, late, now))];
                }
                out.push(stmt(span, StmtKind::If(on, Block { stmts: body, value: None }, Block::default())));
            }
            Op::Deal { to, from, by } => {
                // The output of the part inside `by`; of none, of the chain (the caller's frame).
                let x = match (w.n.bounds.get(by as usize), w.n.clock) {
                    (Some(b), _) => b.out,
                    (None, Clock::Tick(o)) => Some(o),
                    (None, _) => None,
                };
                let x = x.ok_or_else(|| internal(span, "a copy of no window"))?;
                let (array, (dst, e, own)) = (Part::Deal(from), target(lw, w, to)?);
                let (pos, q) = (at(lw, cx, w, (by as usize, own), x, e)?, exp(n, array, span)?);
                let src = Src::At(w.field(lw, array)?, at(lw, cx, w, (by as usize, from as usize), x, q)?, q);
                copy(cx, out, (dst, e), pos, src, x, span)?;
            }
            Op::Each { bound: u, once, ref groups } => {
                let l = (!once).then(|| cx.temp("__j", Ty::u32()));
                let j = l.map_or_else(|| u32_lit(span, 0), |l| local_expr(cx, l, span));
                w.js.push((u as usize, j.clone()));
                let mut runs = Vec::new();
                for (y, list) in groups {
                    let mut body = Vec::new();
                    ops(lw, cx, &mut body, w, list)?;
                    runs.push((*y, body));
                }
                w.js.pop();
                let Some(l) = l else {
                    runs.into_iter().for_each(|r| out.extend(r.1));
                    continue;
                };
                let (mut body, n) = (Vec::new(), count(w.bound(u)?.ratio, span)?);
                drive(runs, &j, span, &mut body)?;
                let body = Block { stmts: body, value: None };
                out.push(stmt(span, StmtKind::ForRange(l, u32_lit(span, 0), u32_lit(span, n), body)));
            }
        }
    }
    Ok(value)
}

/// The part the `.reset_if~` at `at` of the walk wraps back to its start
/// (§11.10): its head as a soft reset does ([`super::phases::reset_node`]:
/// an instance by its `_reset_kept`, a delay its value and its write place
/// from the copy of its `init`), the rings and the arrays of the boundaries
/// inside it and the held outputs of the guards inside it at `T.default()`;
/// not the conditions and the counts of the guards, nor what is outside it (§11.9).
fn reset(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &Walk, at: u32) -> R<()> {
    let (n, span) = (w.n, w.span);
    super::phases::reset_node(lw, cx, out, w.id, w.state, super::phases::Keep::Kept)?;
    // A held output of a guard the table reads alone has a field (S-1220).
    let kept = |p: &Part| !matches!(p, Part::Held(_)) || w.info.field_at(FieldOf::Node(w.id, *p)).is_some();
    for part in n.reset_parts(at).into_iter().filter(kept) {
        let place = w.field(lw, part)?;
        let v = crate::lower::derived::default_value(lw, &place.ty, span)?;
        assign(out, &place, v)?;
    }
    Ok(())
}

/// The delay `id`, read at this place, open to its store (§11.3, S-1250): a
/// reset that an event of another stage ticks in between waits ([`stored`]).
pub(super) fn opened(lw: &Lowerer, cx: &FnCx, out: &mut Vec<Stmt>, id: NodeId) -> R<()> {
    let (f, open) = (cx.flow.as_ref().expect("flow context"), FieldOf::Node(id, Part::Open));
    if f.now.saving || f.info.field_at(open).is_none() {
        return Ok(());
    }
    let (span, (_, state)) = (f.info.node(id).span, super::branches::here(cx, f.info.node(id).span)?);
    assign(out, &sfield(lw, f.info, &state, open, span)?, lit(Ty::Bool, span, Lit::Bool(true)))
}

/// The resets that waited for the store of the delay `id` ([`opened`]), after it.
pub(super) fn stored(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let w = Walk::new(info, id, state, info.node(id).span);
    for flag in w.n.late_flags() {
        let (on, mut body) = (w.field(lw, flag)?, Vec::new());
        assign(&mut body, &on, lit(Ty::Bool, w.span, Lit::Bool(false)))?;
        if let Part::Back(at) = flag {
            reset(lw, cx, &mut body, &w, at)?;
            body = vec![stmt(w.span, StmtKind::If(on, Block { stmts: body, value: None }, Block::default()))];
        }
        out.append(&mut body);
    }
    Ok(())
}

/// The stage of the events of the instance of the walk (§11.11) after its run
/// that gave `v`, the event or none: of an event its function, the one place
/// that calls it, at the time of this one, which gives the event of the
/// output or none to this function that gives it (`FlowInfo::gives`,
/// [`Gave`]); in a `par~`, of this replica. Of a callee that gives several
/// (`FlowInfo::burst`), of each in their order, after all its work (S-1251).
fn give(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &Walk, v: Expr) -> R<()> {
    let (span, none) = (w.span, || internal(w.span, "an event given out of no source"));
    let Clock::Event(src) = w.n.clock else { return Err(none()) };
    let f = cx.flow.as_ref().expect("flow context");
    let x = ClockStage::Event(src);
    let &(_, f_id) = f.events.iter().find(|e| e.0 == x).ok_or_else(none)?;
    let state = f.now.scopes.first().ok_or_else(none)?.state.clone();
    let (time, gave) = (f.now.time.clone(), f.now.gave.clone().filter(|_| f.info.gives(x)));
    let mut arm = Vec::new();
    let mut one = Vec::new();
    let (v, each) = match v.ty {
        Ty::Array(_, n) => {
            let (all, i) = (materialize(cx, v, out, "__events"), cx.temp("__i", Ty::u32()));
            (hold(cx, &mut one, index(all, local_expr(cx, i, span))?, "__event"), Some((i, n)))
        }
        _ => (materialize(cx, v, out, "__event"), None),
    };
    let some = super::event_option(lw.a, span)?.keep;
    let event = payload(lw, v.clone(), some, 0)?;
    let vars = around(w.info, w.n.owner).into_iter().map(|p| range(w.info, p, span));
    let vars = vars.map(|r| Ok(local_expr(cx, LocalId(r?.0.0), span)));
    let inputs = vars.chain([Ok(event)]).collect::<R<Vec<_>>>()?;
    let gave = gave.map(|g| Ok((g.place()?, g.next))).transpose()?;
    let ret = gave.as_ref().map_or(Ty::Unit, |g| g.0.ty.clone());
    let stage = StageRun { g: w.info, f: f_id, ret, x, state, time, lets: Vec::new(), inputs };
    let call = call_stage(stage, span)?;
    match gave {
        Some((place, next)) => {
            assign(&mut arm, &place, call)?;
            if let Some(n) = next {
                assign(&mut arm, &n, checked_binary(BinOp::Add, n.clone(), u32_lit(span, 1)))?;
            }
        }
        None => expr_stmt(&mut arm, call),
    }
    let arms = vec![(some, Block { stmts: arm, value: None })];
    let default = Some(Block::default());
    expr_stmt(&mut one, Expr::new(Ty::Unit, span, ExprKind::Switch { scrutinee: Box::new(v), arms, default }));
    match each {
        None => out.append(&mut one),
        Some((i, n)) => {
            let body = Block { stmts: one, value: None };
            out.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), u32_lit(span, n), body)));
        }
    }
    Ok(())
}

/// The result `v` of an op to `to` (§11.9, §11.10): nowhere, the value
/// (made in a loop or under a guard: its window of it), the array of a
/// boundary or the held output of a guard, each a window of the 2^m
/// elements of each frame inside the boundary `from` (`frame` of the walk
/// gives both). The value when it is not made in a local.
fn put(
    lw: &Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    w: &Walk,
    to: Out,
    v: Expr,
    frame: impl FnOnce(&Walk) -> R<(usize, Ratio)>,
) -> R<Option<Expr>> {
    let to = match to {
        Out::None => {
            expr_stmt(out, v);
            return Ok(None);
        }
        Out::Value if w.value.is_none() => return Ok(Some(v)),
        Out::Value => To::Value,
        Out::Deal(b) => To::Array(b),
        Out::Held(g) => To::Held(g),
        // [`give`].
        Out::Event => return Err(internal(w.span, "an event given out as a value")),
    };
    let (from, m) = frame(w)?;
    // Of the value of a tick of the caller made once in a loop, e ≤ 0 (the memo of U6b 2.5).
    let (dst, e, own) = target(lw, w, to)?;
    let pos = at(lw, cx, w, (from, own), m, e)?;
    copy(cx, out, (dst, e), pos, Src::Value(v), m, w.span)?;
    Ok(None)
}

/// Where a run or a copy writes (§11.9), with the exponent of its window
/// and the boundary whose it is ([`counter`]): the array of a boundary, the
/// value the ops make in a loop, the held output of a guard (the caller's).
fn target(lw: &Lowerer, w: &Walk, to: To) -> R<(Expr, Ratio, usize)> {
    let caller = w.n.bounds.len();
    match (to, &w.value, w.n.clock) {
        (To::Array(b), ..) => Ok((w.field(lw, Part::Deal(b))?, exp(w.n, Part::Deal(b), w.span)?, b as usize)),
        (To::Held(g), ..) => Ok((w.field(lw, Part::Held(g))?, Ratio(0), caller)),
        (To::Value, Some(v), Clock::Tick(o)) => Ok((v.clone(), o, caller)),
        (To::Value, ..) => Err(internal(w.span, "a value made in a loop of no local")),
    }
}

/// The ports the ops `list` of an entry read of no ring: the inputs of the
/// runs, the conditions, what a ring is written from.
fn reads(lw: &Lowerer, w: &Walk, list: &[Op]) -> R<BTreeSet<Port>> {
    let (mut ports, mut bodies, mut whens) = (BTreeSet::new(), Vec::new(), Vec::new());
    Op::walk(list, &mut |op| match *op {
        Op::Ring { port, from: Feed::Arg, .. } => drop(ports.insert(port)),
        Op::Run { body, .. } => bodies.push(body),
        Op::When { guard, cond: CondRead::Read, .. } => whens.push(guard),
        Op::Reset { at } if w.ring(at).is_none() => drop(ports.insert(Port::Cond(at))),
        _ => {}
    });
    for guard in whens {
        let at = w.guard(guard)?.at;
        ports.extend(Some(Port::Cond(at)).filter(|_| w.ring(at).is_none()));
    }
    for body in bodies {
        let read = head_inputs(lw, w, body)?.into_iter().map(Port::Input);
        ports.extend(read.filter(|&p| w.n.ring_of(0, p).is_none()));
    }
    Ok(ports)
}

/// The ports the entry of the stage of the node `id` reads ([`reads`]).
pub(super) fn ports_read(lw: &Lowerer, cx: &FnCx, id: NodeId) -> R<BTreeSet<Port>> {
    let f = cx.flow.as_ref().expect("flow context");
    let span = cx.ast.expr(f.info.node(id).expr).span;
    let state = super::branches::here(cx, span)?.1;
    let list = f.info.node(id).entry(f.now.stage).map_or(&[][..], |e| &e.ops);
    reads(lw, &Walk::new(f.info, id, &state, span), list)
}

/// The arguments and then the conditions of the node of the walk in the
/// order of the text (§11.3, S-1233): those of `reads` lowered for its ops,
/// as values ([`hold`], of `all`: read in a loop, the places of the nodes in
/// them would be in it, which the reads after it do not see, the review of
/// U6b0, its low 5); of the others the work of the stage in them
/// ([`super::hoist::work`]), after the values before them.
fn ports(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    w: &mut Walk,
    reads: &BTreeSet<Port>,
    all: bool,
) -> R<()> {
    let args: &[ExprId] = if let PlanKind::Instance { args, .. } = &w.n.kind { args } else { &[] };
    let args = (0u32..).zip(args).map(|(i, &e)| (Port::Input(i), e));
    // SPEC-GAP(S-1221): the condition of a guard or a `.reset_if~` inside one that
    // stops it is read too, as the arguments of the head are (provisional).
    let conds = (0u32..).zip(&w.n.chain).filter_map(|(at, m)| Some((Port::Cond(at), m.cond?)));
    for (port, e) in args.chain(conds).collect::<Vec<_>>() {
        if !reads.contains(&port) {
            let mut work = Vec::new();
            super::hoist::walk(lw, cx, e, &mut work)?;
            if !work.is_empty() {
                w.ports.iter_mut().for_each(|p| p.1 = hold(cx, out, p.1.clone(), "__arg"));
                out.append(&mut work);
            }
            continue;
        }
        let v = lower_expr(lw, cx, e)?;
        let (v, q) = match (port, w.n.args.iter().find(|a| a.expr == e).map(|a| a.at)) {
            (Port::Input(_), Some(p @ Clock::Tick(q))) if p.burst() => (spread(cx, e, p, v), Some(q)),
            (_, Some(_)) => (v, None),
            (_, None) => return Err(internal(w.span, "an argument read at no clock")),
        };
        let name = if let Port::Cond(_) = port { "__cond" } else { "__arg" };
        w.ports.push((port, if all { hold(cx, out, v, name) } else { v }, q));
    }
    Ok(())
}

/// The inputs of the stage of the function of the instance `id`, `init` or
/// `block`, in their order, after the work of the stage in the others ([`ports`]).
pub(super) fn inputs_of(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    id: NodeId,
    state: &Expr,
) -> R<Vec<Expr>> {
    let f = cx.flow.as_ref().expect("flow context");
    let (s, mut w) = (f.now.stage, Walk::new(f.info, id, state, cx.ast.expr(f.info.node(id).expr).span));
    let reads = head_inputs(lw, &w, s)?.into_iter().map(Port::Input).collect();
    ports(lw, cx, out, &mut w, &reads, false)?;
    Ok(w.ports.into_iter().map(|p| p.1).collect())
}

/// `v` as a value read later (§3.5): a `let` in `out`, of a place with an
/// index too, whose panic is here ([`materialize`] leaves it where the place
/// is read); a literal and a place with no index as they are, but, in a flow
/// with events, a field: the stage of an event may write it before the read
/// (§11.11).
pub(super) fn hold(cx: &mut FnCx, out: &mut Vec<Stmt>, v: Expr, name: &str) -> Expr {
    let mut place = &v;
    while let ExprKind::Field { base, .. } = &place.kind {
        place = base;
    }
    let events = cx.flow.as_ref().is_some_and(|f| !f.info.events.is_empty());
    let field = matches!(v.kind, ExprKind::Field { .. });
    if matches!(place.kind, ExprKind::Lit(_) | ExprKind::Local(_)) && !(events && field) {
        return v;
    }
    let (l, span) = (cx.temp(name, v.ty.clone()), v.span);
    out.push(stmt(span, StmtKind::Let(l, v)));
    local_expr(cx, l, span)
}

/// The inputs of the head of the walk a run of its stage `body` reads, by
/// index; none of a delay, which reads its state.
fn head_inputs(lw: &Lowerer, w: &Walk, body: ClockStage) -> R<Vec<u32>> {
    let (a, PlanKind::Instance { callee, .. }) = (lw.a, &w.n.kind) else {
        return if w.n.kind.delay().is_some() { Ok(Vec::new()) } else { Err(internal(w.span, "a run of no instance")) };
    };
    let (Some(g), Some(fd)) = (a.flows.get(callee), a.def(*callee).as_flow()) else {
        return Err(internal(w.span, "an instance of no checked flow"));
    };
    Ok((0u32..).zip(inputs(g, fd, w.span)?).filter(|(_, i)| i.stage == body).map(|(k, _)| k).collect())
}

/// What a chunk of elements is copied from ([`copy`]): a value of them
/// (one element, or an array of them), or an array of a window of 2^q at a
/// place.
enum Src {
    Value(Expr),
    At(Expr, Expr, Ratio),
}

/// The count of the elements of a frame of 2^x of them: 2^max(x, 0).
fn count(x: Ratio, span: Span) -> R<u32> {
    let n = Ratio(x.0.max(0)).n().and_then(|n| u32::try_from(n).ok());
    n.ok_or_else(|| internal(span, format!("a chunk of 2^{}", x.0)))
}

/// The copy of the 2^max(x, 0) elements of a frame ([`count`]) of `src`
/// into `dst`, a window of 2^e, at `pos` (§11.9, the memo of U6b 2.3): of
/// the whole of both ([`whole`]) one assignment, of one element one, else
/// `for i in 0..count { dst[pos + i] = src[at + i] }` (a value of them
/// first in a `let`). Every window is in its array, so the indices are in
/// range. The one copy of the windows of a chain.
fn copy(
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    (dst, e): (Expr, Ratio),
    pos: Expr,
    src: Src,
    x: Ratio,
    span: Span,
) -> R<()> {
    let count = count(x, span)?;
    let (a, at) = match src {
        Src::Value(v) if whole(x, e) || count == 1 => {
            let place = if whole(x, e) { dst } else { index(dst, pos)? };
            return assign(out, &place, of_type(v, &place.ty)?);
        }
        Src::At(a, _, q) if whole(x, e) && whole(x, q) => return assign(out, &dst, a),
        Src::At(a, at, _) if whole(x, e) && count == 1 => return assign(out, &dst, index(a, at)?),
        Src::At(a, at, _) if count == 1 => return assign(out, &index(dst, pos)?, index(a, at)?),
        Src::Value(v) => (materialize(cx, v, out, "__chunk"), u32_lit(span, 0)),
        Src::At(a, at, _) => (a, at),
    };
    let i = cx.temp("__i", Ty::u32());
    let place = index(dst, checked_binary(BinOp::Add, pos, local_expr(cx, i, span)))?;
    let mut body = Vec::new();
    assign(&mut body, &place, index(a, checked_binary(BinOp::Add, at, local_expr(cx, i, span)))?)?;
    let block = Block { stmts: body, value: None };
    out.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), u32_lit(span, count), block)));
    Ok(())
}

/// A local `name` of the type `ty` made `Zeroed`, whose elements are all
/// written before it is read (the memo of U6b 3.3).
fn zeroed(cx: &mut FnCx, out: &mut Vec<Stmt>, name: &str, ty: Ty, span: Span) -> Expr {
    let l = cx.temp(name, ty.clone());
    out.push(stmt(span, StmtKind::Let(l, Expr::new(ty, span, ExprKind::Zeroed))));
    local_expr(cx, l, span)
}

/// The 2^max(k, 0) elements of `src`, a window of 2^e (§11.9), at the
/// place `at` gives: `src` itself of its whole (and of a value, e ≤ 0),
/// one element, or a copy into an array of its own `name` ([`zeroed`]).
/// The one read of a part of a window: of a value from the array of a
/// boundary ([`dealt`]) and of an input of a head ([`run`]).
fn window(
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    src: Expr,
    (k, e): (Ratio, Ratio),
    at: impl FnOnce(&FnCx) -> R<Expr>,
    name: &str,
    span: Span,
) -> R<Expr> {
    if whole(k, e) {
        return Ok(src);
    }
    let (at, count) = (at(cx)?, count(k, span)?);
    match src.ty.clone() {
        _ if count == 1 => index(src, at),
        Ty::Array(t, _) => {
            let l = zeroed(cx, out, name, Ty::Array(t, count), span);
            copy(cx, out, (l.clone(), k), u32_lit(span, 0), Src::At(src, at, e), k, span)?;
            Ok(l)
        }
        t => Err(internal(span, format!("a window of the type {t:?}"))),
    }
}

/// The call of the function of the stage `body` of the head of the walk
/// (§11.9, S-1088, [`call_stage`]): its state, the time of a stage that
/// takes it ([`child_time`], of the words of the callee) and its inputs of
/// that stage, those its chain gathers of their rings
/// ([`PlanNode::ring_of`]), the others lowered before the ops, each the
/// window of the frame of the head ([`window`], the memo of U6b 2.4).
fn run(lw: &mut Lowerer, cx: &mut FnCx, w: &Walk, body: ClockStage) -> R<Expr> {
    let (a, n, span) = (lw.a, w.n, w.span);
    // A delay reads its value, and stores after it (§11.4, §11.10).
    if n.kind.delay().is_some() {
        let mut lets = Vec::new();
        let v = super::nodes::delay_value(lw, cx, &mut lets, w.state, w.id)?;
        w.ran(lw, &mut lets, true)?;
        return Ok(after(lets, v));
    }
    let PlanKind::Instance { callee, .. } = n.kind else {
        return Err(internal(span, format!("a run of {body:?} of no instance")));
    };
    let sub = lw.ensure_flow(callee)?;
    let g = a.flows.get(&callee).ok_or_else(|| internal(span, "an instance of no checked flow"))?;
    let f = sub.stage_fn(body).ok_or_else(|| internal(span, format!("a callee with no stage {body:?}")))?;
    let own = w.field(lw, Part::Own)?;
    let (words, mut lets) = (g.time_words(body), Vec::new());
    let time = if words > 0 { child_time(cx, &mut lets, w, words)? } else { Vec::new() };
    let mut inputs = Vec::new();
    for input in head_inputs(lw, w, body)? {
        let (src, e, owner) = match n.ring_of(0, Port::Input(input)) {
            Some(bound) => {
                let part = Part::Gather { bound, port: Port::Input(input) };
                (w.field(lw, part)?, exp(n, part, span)?, bound as usize)
            }
            None => {
                let (v, q) = w.port(Port::Input(input))?;
                (v, q.unwrap_or(Ratio(0)), n.bounds.len())
            }
        };
        let v = match n.bounds.first().and_then(|b| *b.ins.get(input as usize)?) {
            Some(k) => window(cx, &mut lets, src, (k, e), |cx| at(lw, cx, w, (0, owner), k, e), "__in", span)?,
            None => src,
        };
        inputs.push(v);
    }
    let ret = lw.m.fn_(f).ret.clone();
    call_stage(StageRun { g, f, ret, x: body, state: own, time, lets, inputs }, span)
}

/// The value of the instance `id` of a chain that deals, in the scope of
/// `state` (§11.9): the array of its boundary `b` ([`Read::Array`]) at the
/// place of the frame of this flow, the elements of the tick of its output
/// ([`window`]).
pub(super) fn dealt(
    lw: &Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    id: NodeId,
    state: &Expr,
    b: u32,
    span: Span,
) -> R<Expr> {
    let w = Walk::new(cx.flow.as_ref().expect("flow context").info, id, state, span);
    let (n, part) = (w.n, Part::Deal(b));
    let o = n.bounds.last().and_then(|l| l.out.map(|e| l.outside(e)));
    let (o, e) = (o.ok_or_else(|| internal(span, "a value of no output"))?, exp(n, part, span)?);
    window(
        cx,
        out,
        w.field(lw, part)?,
        (o, e),
        |cx| at(lw, cx, &w, (n.bounds.len(), b as usize), o, e),
        "__dealt",
        span,
    )
}
