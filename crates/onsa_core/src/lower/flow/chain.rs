//! The chains of `.down~(N)` in the functions of the stages (§11.9,
//! S-1207): the counter of a frame, folded from the counter of the phase
//! of this flow, and the place of a window of a ring or an array at it; the
//! work of an instance in the function of a stage as the table of the plan
//! gives it ([`Entry`]: the rings it writes, the runs of the stages of its
//! head, the arrays it deals in, each by one copy) and the array it is read
//! from. Of the boundaries the gate passes ([`PlanNode::lowered_chain`]):
//! an `.up~` (W7-16 U6b3) is an internal error here.

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

/// The counter of the frame inside the boundary `from` of `n` (§11.9): the
/// counter of the phase of this flow (`_tick`) folded out of each boundary
/// from the outermost to `from` ([`fold`]); 0 at the start of one whose
/// `_tick` is not of a grid (S-1217), whose work is all at its `sample`,
/// where the start is masked out of each window ([`at`]).
fn counter(lw: &Lowerer, cx: &FnCx, n: &PlanNode, from: usize, span: Span) -> R<Expr> {
    let f = cx.flow.as_ref().expect("flow context");
    let root = f.scopes.first().ok_or_else(|| internal(span, "a chain outside the state"))?;
    let mut c = match f.info.counter() {
        Counter::Tick => vec![sfield(lw, f.info, &root.state, FieldOf::Tick, span)?],
        Counter::None | Counter::Process => vec![u32_lit(span, 0)],
    };
    for b in n.bounds.iter().skip(from).rev() {
        c = fold(&c, b.ratio, span)?;
    }
    c.pop().ok_or_else(|| internal(span, "a counter of no word"))
}

/// The place in a window of 2^e elements (a ring, an array, §11.9) of the
/// elements of the frame inside the boundary `from` of `n`, 2^x of each of
/// its frames ([`counter`] C): `(C & (2^(e − x) − 1)) >> −x` of x ≤ 0 (`>>
/// 0` too), `<< x` of 0 < x < e, 0 of x ≥ e (the whole window). The one
/// place of the places of the rings and the arrays of a chain.
fn at(lw: &Lowerer, cx: &FnCx, n: &PlanNode, from: usize, x: Ratio, e: Ratio, span: Span) -> R<Expr> {
    if x.0 >= e.0 {
        return Ok(u32_lit(span, 0));
    }
    let mask = u32::try_from(e.0 - x.0).ok().and_then(|w| 1u32.checked_shl(w)).map(|m| m - 1);
    let mask = mask.ok_or_else(|| internal(span, format!("a window of 2^{} of 2^{}", e.0, x.0)))?;
    let c = checked_binary(BinOp::BitAnd, counter(lw, cx, n, from, span)?, u32_lit(span, mask));
    let (op, by) = if x.0 <= 0 { (BinOp::Shr, x.0.unsigned_abs()) } else { (BinOp::Shl, x.0.unsigned_abs()) };
    Ok(checked_binary(op, c, u32_lit(span, by)))
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
/// ring written at its place from the argument or the ring outside it, a
/// run of a stage of the head as a statement, into the array of the
/// boundary that deals it or as the value given back (of an entry read),
/// and the copy of an array into the one outside it, each by [`copy`]. The
/// runs of an `.up~` and a copy to the value, which the gate stops, are an
/// internal error (W7-16 U6b3).
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
    let field = |lw: &Lowerer, part| sfield(lw, info, state, FieldOf::Node(id, part), span);
    let bound = |b: u32| n.bounds.get(b as usize).ok_or_else(|| internal(span, format!("no boundary {b}")));
    for op in &e.ops {
        match *op {
            Op::Ring { bound: b, input, from } => {
                let (part, PlanKind::Instance { args, .. }) = (Part::Gather { bound: b, input }, &n.kind) else {
                    return Err(internal(span, "a ring of no instance"));
                };
                let k = exp(n, part, span)?;
                let (x, f) = (bound(b)?.outside(k), b as usize + 1);
                let (dst, pos) = (field(lw, part)?, at(lw, cx, n, f, x, k, span)?);
                let src = match from {
                    Feed::Arg => {
                        let arg = args.get(input as usize).ok_or_else(|| internal(span, "a ring of no argument"))?;
                        Src::Value(lower_expr(lw, cx, *arg)?)
                    }
                    Feed::Ring(o) => {
                        let part = Part::Gather { bound: o, input };
                        Src::At(field(lw, part)?, at(lw, cx, n, f, x, exp(n, part, span)?, span)?)
                    }
                };
                copy(cx, out, dst, pos, src, count(x, span)?, span)?;
            }
            Op::Run { body, out: to } => {
                let v = run(lw, cx, id, state, body)?;
                match to {
                    Out::None => expr_stmt(out, v),
                    Out::Value => value = Some(v),
                    Out::Deal(b) => {
                        let (m, part) = (bound(0)?.out, Part::Deal(b));
                        let m = m.ok_or_else(|| internal(span, "a run that deals of no output"))?;
                        let pos = at(lw, cx, n, 0, m, exp(n, part, span)?, span)?;
                        copy(cx, out, field(lw, part)?, pos, Src::Value(v), count(m, span)?, span)?;
                    }
                }
            }
            Op::Deal { to: To::Array(b), from, by } => {
                let x = bound(by)?.out.ok_or_else(|| internal(span, "a copy of no window"))?;
                let (to, from) = (Part::Deal(b), Part::Deal(from));
                let pos = at(lw, cx, n, by as usize, x, exp(n, to, span)?, span)?;
                let src = Src::At(field(lw, from)?, at(lw, cx, n, by as usize, x, exp(n, from, span)?, span)?);
                copy(cx, out, field(lw, to)?, pos, src, count(x, span)?, span)?;
            }
            Op::Deal { to: To::Value, .. } | Op::Each { .. } => {
                return Err(internal(span, format!("{op:?} of a chain the Core does not lower yet")));
            }
        }
    }
    Ok(value)
}

/// What a chunk of elements is copied from ([`copy`]): a value of them
/// (one element, or an array of them), or an array at a place.
enum Src {
    Value(Expr),
    At(Expr, Expr),
}

/// The count of the elements of a frame of 2^x of them: 2^max(x, 0).
fn count(x: Ratio, span: Span) -> R<u32> {
    let n = Ratio(x.0.max(0)).n().and_then(|n| u32::try_from(n).ok());
    n.ok_or_else(|| internal(span, format!("a chunk of 2^{}", x.0)))
}

/// The copy of `count` elements of `src` into the array `dst` at `pos`
/// (§11.9, the memo of U6b 2.3): of the whole of both one assignment, of
/// one element one, else `for i in 0..count { dst[pos + i] = src[at + i] }`
/// (a value of them first in a `let`). Every window is in its array, so
/// the indices are in range. The one copy of the windows of a chain.
fn copy(cx: &mut FnCx, out: &mut Vec<Stmt>, dst: Expr, pos: Expr, src: Src, count: u32, span: Span) -> R<()> {
    let whole = |e: &Expr| matches!(e.ty, Ty::Array(_, n) if n == count);
    let (a, at) = match src {
        Src::Value(v) if whole(&dst) || count == 1 => {
            let place = if whole(&dst) { dst } else { index(dst, pos)? };
            return assign(out, &place, of_type(v, &place.ty)?);
        }
        Src::At(a, _) if whole(&dst) && whole(&a) => return assign(out, &dst, a),
        Src::At(a, at) if count == 1 => return assign(out, &index(dst, pos)?, index(a, at)?),
        Src::Value(v) => (materialize(cx, v, out, "__chunk"), u32_lit(span, 0)),
        Src::At(a, at) => (a, at),
    };
    let i = cx.temp("__i", Ty::u32());
    let place = index(dst, checked_binary(BinOp::Add, pos, local_expr(cx, i, span)))?;
    let mut body = Vec::new();
    assign(&mut body, &place, index(a, checked_binary(BinOp::Add, at, local_expr(cx, i, span)))?)?;
    let block = Block { stmts: body, value: None };
    out.push(stmt(span, StmtKind::ForRange(i, u32_lit(span, 0), u32_lit(span, count), block)));
    Ok(())
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
/// place of the frame of this flow, the element of the tick of its output.
pub(super) fn dealt(lw: &Lowerer, cx: &FnCx, id: NodeId, state: &Expr, b: u32, span: Span) -> R<Expr> {
    let info = cx.flow.as_ref().expect("flow context").info;
    let n = info.node(id);
    let part = Part::Deal(b);
    let o = n.bounds.last().and_then(|l| l.out.map(|e| l.outside(e)));
    let o = o.ok_or_else(|| internal(span, "a value of no output"))?;
    let at = at(lw, cx, n, n.bounds.len(), o, exp(n, part, span)?, span)?;
    index(sfield(lw, info, state, FieldOf::Node(id, part), span)?, at)
}
