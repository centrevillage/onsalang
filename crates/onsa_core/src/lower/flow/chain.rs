//! The chains of `.down~(N)` in the functions of the stages (§11.9,
//! S-1207): the phase of a boundary, folded from the counter of the phase
//! of this flow; the slot of a ring or an array at it; the work of an
//! instance in the function of a stage as the table of the plan gives it
//! ([`Entry`]: the rings it writes, the runs of the stages of its head, the
//! array it deals in) and the array it is read from. Of the boundaries the
//! gate passes ([`PlanNode::lowered_chain`]): an `.up~` (W7-16 U6b) is an
//! internal error here.

use super::*;

/// The words of a count of the frames of the caller of a boundary of the
/// ratio `r` as those of the part it wraps, of a `.down~(2^s)`: `[c >> s]`
/// of one (the phase, its low word alone), `[(t >> s) | (t_hi << (32 −
/// s)), t_hi >> s]` of two (the time, divided before it is cut to `U32`,
/// §11.4). The one step of it (U6b adds `.up~`).
fn fold(words: &[Expr], r: Ratio, span: Span) -> R<Vec<Expr>> {
    let s = u32::try_from(-r.0).ok().filter(|&s| r.slower_than_body() && s < 32);
    let s = s.ok_or_else(|| internal(span, format!("a count under a boundary of the ratio {r:?}")))?;
    let shift = |op, x: &Expr, by| checked_binary(op, x.clone(), u32_lit(span, by));
    match words {
        [c] => Ok(vec![shift(BinOp::Shr, c, s)]),
        [t, hi] => Ok(vec![
            checked_binary(BinOp::BitOr, shift(BinOp::Shr, t, s), shift(BinOp::Shl, hi, 32 - s)),
            shift(BinOp::Shr, hi, s),
        ]),
        _ => Err(internal(span, format!("a count of {} words", words.len()))),
    }
}

/// The time the callee of `n` takes from that of its caller (§11.4,
/// S-1217): two words folded out of each boundary, the outermost first, in
/// `let`s `t_in`, `t_hi_in` into `out` that the next shares, cut to `words`.
fn child_time(cx: &mut FnCx, out: &mut Vec<Stmt>, n: &PlanNode, words: usize, span: Span) -> R<Vec<Expr>> {
    let mut time = cx.flow.as_ref().expect("flow context").time.clone();
    for (k, b) in n.bounds.iter().enumerate().rev() {
        // One word divided would lose the upper (S-1211): the table gives two.
        let two = Some(&time[..]).filter(|t| t.len() == 2).ok_or_else(|| internal(span, "one word of time"))?;
        let kept = fold(two, b.ratio, span)?.into_iter().take(if k == 0 { words } else { 2 });
        time = kept.zip(["t_in", "t_hi_in"]).map(|(e, name)| materialize(cx, e, out, name)).collect();
    }
    let time = time.get(..words).ok_or_else(|| internal(span, format!("a callee of {words} words of time")))?;
    Ok(time.to_vec())
}

/// The phase of the boundary `b` of `n` (§11.9): the counter of the phase
/// of this flow (`_tick` of its `State`, which starts at 0 with those of
/// its callees) folded out of each boundary outside `b`, the outermost
/// first, as the frames around `b`, masked to the frames of one of its
/// ticks.
fn phase(lw: &Lowerer, cx: &FnCx, n: &PlanNode, b: usize, span: Span) -> R<Expr> {
    let f = cx.flow.as_ref().expect("flow context");
    let root = f.scopes.first().ok_or_else(|| internal(span, "a chain outside the state"))?;
    // S-1217: the counter of the time alone advances in `process` only.
    if f.info.counter() != Counter::Tick {
        return Err(internal(span, "the phase of a chain of a flow whose `_tick` is not of a grid"));
    }
    let mut c = vec![sfield(lw, f.info, &root.state, FieldOf::Tick, span)?];
    for o in n.bounds.iter().skip(b + 1).rev() {
        c = fold(&c, o.ratio, span)?;
    }
    let c = c.pop().ok_or_else(|| internal(span, "a phase of no word"))?;
    let r = n.bounds.get(b).map(|x| x.ratio);
    let mask = r.and_then(|r| r.n()).and_then(|m| u32::try_from(m - 1).ok());
    let mask = mask.ok_or_else(|| internal(span, format!("no phase of the boundary {b}")))?;
    Ok(checked_binary(BinOp::BitAnd, c, u32_lit(span, mask)))
}

/// The slot of a ring or an array of 2^e at a boundary of the ratio `r` at
/// the phase `phase` (§11.9): `phase >> (−r − e)`, the frame of one of its
/// elements; of the rings it gathers and the arrays it deals (the one
/// place of it).
fn slot(phase: Expr, r: Ratio, e: Ratio, span: Span) -> R<Expr> {
    let by = u32::try_from(-r.0 - e.0).map_err(|_| internal(span, format!("a slot of 2^{} under {r:?}", e.0)))?;
    Ok(checked_binary(BinOp::Shr, phase, u32_lit(span, by)))
}

/// The exponent `e` of the ring or the array `part` of `n` (`2^e`, S-1208),
/// of a port of the part its boundary wraps faster than its `sample`: of
/// an input the boundary gathers, of the output it deals.
fn exp(n: &PlanNode, part: Part, span: Span) -> R<Ratio> {
    let e = match part {
        Part::Gather { bound, input } => n.bounds.get(bound as usize).and_then(|b| *b.ins.get(input as usize)?),
        Part::Deal(bound) => n.bounds.get(bound as usize).and_then(|b| b.out),
        _ => None,
    };
    e.filter(|e| e.faster_than_body()).ok_or_else(|| internal(span, format!("a ring or an array {part:?} of {e:?}")))
}

/// The length of the ring or the array `part` of `n` ([`exp`]).
pub(super) fn len(n: &PlanNode, part: Part, span: Span) -> R<u32> {
    let len = exp(n, part, span)?.n().and_then(|n| u32::try_from(n).ok());
    len.ok_or_else(|| internal(span, format!("a ring or an array {part:?}, past `U32`")))
}

/// The ops of the entry `e` of the instance `id` in the function of its
/// stage, in their order (§11.9, [`Entry`]), in the scope of `state`: a
/// ring written from the argument at its slot, a run of a stage of the head
/// as a statement, into the array of the boundary that deals it, or as the
/// value given back (of an entry read). A ring written from another, the
/// copy of an array and the runs of an `.up~`, which the gate stops, are an
/// internal error (W7-16 U6b).
// SPEC-GAP(S-1206): an argument is evaluated in the walk of the runs of the
// stages, at the place of its node before its runs; the reference
// evaluator evaluates that of the outermost boundary after them, which
// differs in the order of the panics alone.
pub(super) fn entry(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    id: NodeId,
    state: &Expr,
    e: &Entry,
) -> R<Option<Expr>> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let (n, mut value) = (info.node(id), None);
    let span = cx.ast.expr(n.expr).span;
    for op in &e.ops {
        match *op {
            Op::Ring { bound, input, from: Feed::Arg } => {
                let (part, PlanKind::Instance { args, .. }) = (Part::Gather { bound, input }, &n.kind) else {
                    return Err(internal(span, "a ring of no instance"));
                };
                let arg = args.get(input as usize).ok_or_else(|| internal(span, "a ring of no argument"))?;
                let r = n.bounds.get(bound as usize).ok_or_else(|| internal(span, "a ring of no boundary"))?.ratio;
                let at = slot(phase(lw, cx, n, bound as usize, span)?, r, exp(n, part, span)?, span)?;
                let place = index(sfield(lw, info, state, FieldOf::Node(id, part), span)?, at)?;
                let v = lower_expr(lw, cx, *arg)?;
                assign(out, &place, of_type(v, &place.ty)?)?;
            }
            Op::Run { body, out: to } => {
                let v = run(lw, cx, id, state, body)?;
                match to {
                    Out::None => expr_stmt(out, v),
                    Out::Deal(b) => assign(out, &sfield(lw, info, state, FieldOf::Node(id, Part::Deal(b)), span)?, v)?,
                    Out::Value => value = Some(v),
                }
            }
            Op::Ring { .. } | Op::Deal { .. } | Op::Each { .. } => {
                return Err(internal(span, format!("{op:?} of a chain the Core does not lower yet")));
            }
        }
    }
    Ok(value)
}

/// The call of the function of the stage `body` of the callee of the
/// instance `id`, in the scope of `state` (§11.9, S-1088, [`call_stage`]):
/// its state, the time of a stage that takes it ([`child_time`], of the
/// words of the callee) and its inputs of that stage, lowered here, those
/// its chain gathers of their rings ([`PlanNode::ring_of`]).
fn run(lw: &mut Lowerer, cx: &mut FnCx, id: NodeId, state: &Expr, body: ClockStage) -> R<Expr> {
    let (a, info) = (lw.a, cx.flow.as_ref().expect("flow context").info);
    let n = info.node(id);
    let span = cx.ast.expr(n.expr).span;
    // A chain the gate stops (`.up~`, `.when~`, `.reset_if~`, one that gathers or deals) runs no stage here.
    let (&PlanKind::Instance { callee, ref args, .. }, ClockStage::Tick(k), true) = (&n.kind, body, n.lowered_chain())
    else {
        return Err(internal(span, format!("a run of {body:?} of no instance, or of one with a chain not lowered")));
    };
    let sub = lw.ensure_flow(callee)?;
    let g = a.flows.get(&callee).ok_or_else(|| internal(span, "an instance of no checked flow"))?;
    let f = sub.stage_fn(body).ok_or_else(|| internal(span, format!("a callee with no stage {k:?}")))?;
    let own = sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?;
    let (words, mut lets) = (g.time_words(body), Vec::new());
    let time = if words > 0 { child_time(cx, &mut lets, n, words, span)? } else { Vec::new() };
    let mut rings = Vec::new();
    for (input, _) in (0u32..).zip(args) {
        if let Some(bound) = n.ring_of(0, input) {
            rings.push((input, sfield(lw, info, state, FieldOf::Node(id, Part::Gather { bound, input }), span)?));
        }
    }
    let inputs = instance_args(lw, cx, (callee, args), Phase::Tick(k), &rings, span)?;
    let ret = lw.m.fn_(f).ret.clone();
    call_stage(StageRun { g, f, ret, x: body, state: own, time, lets, inputs }, span)
}

/// The value of the instance `id` of a chain that deals, in the scope of
/// `state` (§11.9): the array of its boundary `b` ([`Read::Array`]) at the
/// slot of the phase, the element of the tick of its output.
pub(super) fn dealt(lw: &Lowerer, cx: &FnCx, id: NodeId, state: &Expr, b: u32, span: Span) -> R<Expr> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let n = info.node(id);
    let part = Part::Deal(b);
    let r = n.bounds.get(b as usize).ok_or_else(|| internal(span, "an array of no boundary"))?.ratio;
    let at = slot(phase(lw, cx, n, b as usize, span)?, r, exp(n, part, span)?, span)?;
    index(sfield(lw, info, state, FieldOf::Node(id, part), span)?, at)
}
