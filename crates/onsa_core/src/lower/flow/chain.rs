//! The chains of `.down~(N)` in the functions of the stages (§11.9,
//! S-1207): the phase of a boundary, folded from the counter of the phase
//! of this flow; the slot of a ring or an array at it; the rings an
//! instance writes, the array it deals in and the one it is read from. Of
//! the boundaries the gate passes ([`PlanNode::lowered_chain`]): an `.up~`
//! (W7-16 U6b) is an internal error here.

use super::*;

/// The ratio of the boundary `b` of the chain of `n`.
fn ratio(n: &PlanNode, b: &PlanBound, span: Span) -> R<Ratio> {
    let r = n.chain.get(b.at as usize).and_then(|m| m.ratio);
    r.ok_or_else(|| internal(span, "a boundary of no modifier with a ratio"))
}

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
pub(super) fn child_time(cx: &mut FnCx, out: &mut Vec<Stmt>, n: &PlanNode, words: usize, span: Span) -> R<Vec<Expr>> {
    let mut time = cx.flow.as_ref().expect("flow context").time.clone();
    for (k, b) in n.bounds.iter().enumerate().rev() {
        // One word divided would lose the upper (S-1211): the table gives two.
        let two = Some(&time[..]).filter(|t| t.len() == 2).ok_or_else(|| internal(span, "one word of time"))?;
        let kept = fold(two, ratio(n, b, span)?, span)?.into_iter().take(if k == 0 { words } else { 2 });
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
        c = fold(&c, ratio(n, o, span)?, span)?;
    }
    let c = c.pop().ok_or_else(|| internal(span, "a phase of no word"))?;
    let r = n.bounds.get(b).map(|x| ratio(n, x, span)).transpose()?;
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

/// The inputs the innermost boundary of `n` gathers, each with the stage
/// of this flow whose function writes its ring: that of the frame around
/// the boundary moved out ([`PlanNode::outer_stage`]), none of one with no
/// `maps`. The one reading of them (D-15): [`rings_at`], [`rings`] and the
/// check of `init` read it.
pub(super) fn gathered(n: &PlanNode) -> impl Iterator<Item = (u32, Option<ClockStage>)> + '_ {
    let gathers = n.bounds.first().into_iter().flat_map(|b| &b.gathers);
    gathers.map(|&(input, q)| (input, n.outer_stage(0, q)))
}

/// The inputs whose rings the node `n` writes in the function of the
/// stage `s` (§11.9, [`gathered`]). The one test of them (D-15): the walk
/// of the runs of the stages ([`super::phases`]) and the writes read it.
pub(super) fn rings_at(n: &PlanNode, s: ClockStage) -> impl Iterator<Item = u32> + '_ {
    gathered(n).filter(move |g| g.1 == Some(s)).map(|g| g.0)
}

/// The ring fields of the inputs the innermost boundary of the instance
/// `id` gathers, in the scope of `state`, by the index of the input: the
/// arguments of its head (§11.9: the array of the values gathered).
pub(super) fn rings(lw: &Lowerer, info: &FlowInfo, id: NodeId, state: &Expr, span: Span) -> R<Vec<(u32, Expr)>> {
    let ring =
        |(input, _)| Ok((input, sfield(lw, info, state, FieldOf::Node(id, Part::Gather { bound: 0, input }), span)?));
    gathered(info.node(id)).map(ring).collect()
}

/// The writes of the rings of the instance `id` in the function of the
/// stage lowered (§11.9), in the scope of `state`: of each input it
/// gathers there ([`rings_at`]), its argument at the slot of the phase.
// SPEC-GAP(S-1206): the argument is evaluated in the walk of the runs of
// the stages, at the place of its node before its runs; the reference
// evaluator evaluates that of the outermost boundary after them, which
// differs in the order of the panics alone.
pub(super) fn write_rings(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let f = cx.flow.as_ref().expect("flow context");
    let (info, n, stage) = (f.info, f.info.node(id), f.phase.stage());
    let (span, PlanKind::Instance { args, .. }) = (cx.ast.expr(n.expr).span, &n.kind) else { return Ok(()) };
    let Some(b) = n.bounds.first() else { return Ok(()) };
    for input in rings_at(n, stage) {
        let (part, arg) = (Part::Gather { bound: 0, input }, args.get(input as usize));
        let arg = arg.ok_or_else(|| internal(span, "a ring of no argument"))?;
        let at = slot(phase(lw, cx, n, 0, span)?, ratio(n, b, span)?, exp(n, part, span)?, span)?;
        let place = index(sfield(lw, info, state, FieldOf::Node(id, part), span)?, at)?;
        let v = lower_expr(lw, cx, *arg)?;
        assign(out, &place, of_type(v, &place.ty)?)?;
    }
    Ok(())
}

/// The array the run `run` of the instance `id` deals its output in, in
/// the scope of `state` (§11.9): of the run of the stage that makes the
/// output of its head, of a chain that deals ([`PlanNode::deals`]); none
/// of another.
pub(super) fn dealt_by(
    lw: &Lowerer,
    info: &FlowInfo,
    id: NodeId,
    state: &Expr,
    run: Run,
    span: Span,
) -> R<Option<Expr>> {
    let n = info.node(id);
    let (PlanKind::Instance { callee, .. }, Some(b)) = (&n.kind, n.dealt_at()) else { return Ok(None) };
    if lw.a.flows.get(callee).and_then(|g| g.out_stage) != Some(run.body) {
        return Ok(None);
    }
    sfield(lw, info, state, FieldOf::Node(id, Part::Deal(b)), span).map(Some)
}

/// The value of the instance `id` of a chain that deals, in the scope of
/// `state` (§11.9): its array at the slot of the phase, the element of the
/// tick of its output.
pub(super) fn dealt(lw: &Lowerer, cx: &FnCx, id: NodeId, state: &Expr, span: Span) -> R<Expr> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let n = info.node(id);
    let b = n.dealt_at().ok_or_else(|| internal(span, "a chain that deals nothing"))?;
    let part = Part::Deal(b);
    let at =
        slot(phase(lw, cx, n, b as usize, span)?, ratio(n, &n.bounds[b as usize], span)?, exp(n, part, span)?, span)?;
    index(sfield(lw, info, state, FieldOf::Node(id, part), span)?, at)
}
