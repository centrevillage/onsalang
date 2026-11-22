//! The chains of `.down~(N)` and `.up~(N)` in the functions of the stages
//! (§11.9, S-1207): the counter of a frame, folded from the counter of the
//! phase of this flow and the run j of each `.up~` around, and the place of
//! a window of a ring or an array at it; the work of an instance in the
//! function of a stage as the table of the plan gives it ([`Entry`]: the
//! rings it writes, the runs of the stages of its head, the arrays it deals
//! in, each by one copy, the N runs of an `.up~` in a loop) and the array
//! it is read from.

use super::*;

/// The walk of the ops of an entry of the instance `id` (`n`) in the scope
/// of `state` (§11.9): the run j of each `.up~` around the ops lowered, by
/// its boundary ([`counter`]); the arguments its loops read, lowered before
/// them ([`prelower`], [`arg_value`]); the value the ops make in a loop, a
/// local made at the head of the entry.
struct Walk<'a> {
    info: &'a FlowInfo,
    id: NodeId,
    n: &'a PlanNode,
    state: &'a Expr,
    span: Span,
    js: Vec<(usize, Expr)>,
    args: Vec<(u32, Expr, Option<Ratio>)>,
    value: Option<Expr>,
}

impl<'a> Walk<'a> {
    fn new(info: &'a FlowInfo, id: NodeId, state: &'a Expr, span: Span) -> Self {
        Walk { info, id, n: info.node(id), state, span, js: Vec::new(), args: Vec::new(), value: None }
    }

    fn field(&self, lw: &Lowerer, part: Part) -> R<Expr> {
        sfield(lw, self.info, self.state, FieldOf::Node(self.id, part), self.span)
    }

    fn bound(&self, b: u32) -> R<&'a onsa_sema::flow::PlanBound> {
        self.n.bounds.get(b as usize).ok_or_else(|| internal(self.span, format!("no boundary {b}")))
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
/// of none else. The one step of the counters and the time.
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
    let mut time = cx.flow.as_ref().expect("flow context").time.clone();
    for (k, b) in w.n.bounds.iter().enumerate().rev() {
        // One word divided would lose the upper (S-1211): the table gives two under a `.down~`.
        if b.ratio.slower_than_body() && time.len() != 2 {
            return Err(internal(w.span, "one word of time"));
        }
        let kept = fold(&time, b.ratio, w.j(k), w.span)?.into_iter().take(if k == 0 { words } else { 2 });
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
fn counter(lw: &Lowerer, cx: &FnCx, w: &Walk, from: usize) -> R<Expr> {
    let (f, span) = (cx.flow.as_ref().expect("flow context"), w.span);
    let root = f.scopes.first().ok_or_else(|| internal(span, "a chain outside the state"))?;
    let mut c = match f.info.counter() {
        Counter::Tick => vec![sfield(lw, f.info, &root.state, FieldOf::Tick, span)?],
        Counter::None | Counter::Process => vec![u32_lit(span, 0)],
    };
    for (b, bound) in w.n.bounds.iter().enumerate().skip(from).rev() {
        c = fold(&c, bound.ratio, w.j(b), span)?;
    }
    c.pop().ok_or_else(|| internal(span, "a counter of no word"))
}

/// The place in a window of 2^e elements (a ring, an array, §11.9) of the
/// elements of the frame inside the boundary `from` of the walk, 2^x of
/// each of its frames ([`counter`] C): `(C & (2^(e − x) − 1)) >> −x` of x ≤
/// 0 (`>> 0` too), `<< x` of 0 < x < e, 0 of the whole window ([`whole`]).
/// The one place of the places of the rings and the arrays of a chain.
fn at(lw: &Lowerer, cx: &FnCx, w: &Walk, from: usize, x: Ratio, e: Ratio) -> R<Expr> {
    let span = w.span;
    if whole(x, e) {
        return Ok(u32_lit(span, 0));
    }
    let mask = u32::try_from(e.0 - x.0).ok().and_then(|w| 1u32.checked_shl(w)).map(|m| m - 1);
    let mask = mask.ok_or_else(|| internal(span, format!("a window of 2^{} of 2^{}", e.0, x.0)))?;
    let c = checked_binary(BinOp::BitAnd, counter(lw, cx, w, from)?, u32_lit(span, mask));
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
        Part::Gather { bound, input } => n.bounds.get(bound as usize).and_then(|b| *b.ins.get(input as usize)?),
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

/// The ops of the entry `e` of the instance `id` in the function of its
/// stage, in their order (§11.9, [`Entry`]), in the scope of `state` (the
/// rings, the runs, the copies and the loops of [`ops`]), and the value
/// they make: of a run out of a loop the value of the run, else, made in
/// the loop of an `.up~`, a local made at the head, `Zeroed` (every element
/// written, the memo of U6b 2.5).
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
    let mut w = Walk::new(info, id, state, cx.ast.expr(info.node(id).expr).span);
    let value = |op: &Op| matches!(op, Op::Run { out: Out::Value, .. } | Op::Deal { to: To::Value, .. });
    let mut looped = false;
    for op in e.ops.iter().filter(|op| matches!(op, Op::Each { .. })) {
        Op::walk(std::slice::from_ref(op), &mut |op| looped |= value(op));
    }
    if looped {
        let t = cx.info.expr_types.get(&w.n.expr).ok_or_else(|| internal(w.span, "an instance of no type"))?;
        let ty = burst_ty(Some(w.n.clock), lw.core_ty(*t, &[], w.span)?);
        w.value = Some(zeroed(cx, out, "__value", ty, w.span));
    }
    let made = ops(lw, cx, out, &mut w, &e.ops)?;
    Ok(made.or(w.value))
}

/// The ops `list` of the walk `w` into `out`, in their order (§11.9): a
/// ring written at its place from the argument or the ring outside it, a
/// run of a stage of the head as a statement, into the array of the
/// boundary that deals it or as the value, the copy of an array into the
/// one outside it or into the value, each by [`copy`], and the N runs of an
/// `.up~` ([`Op::Each`]): of its `once`, the run j = 0 alone; else a loop of
/// j, each run the ops of each stage of the part when j is at its tick
/// ([`drive`]), the arguments they read lowered before the outermost.
fn ops(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &mut Walk, list: &[Op]) -> R<Option<Expr>> {
    let (n, span, mut value) = (w.n, w.span, None);
    for op in list {
        match *op {
            Op::Ring { bound: b, input, from } => {
                let part = Part::Gather { bound: b, input };
                let k = exp(n, part, span)?;
                let (x, f) = (w.bound(b)?.outside(k), b as usize + 1);
                let (dst, pos) = (w.field(lw, part)?, at(lw, cx, w, f, x, k)?);
                let src = match from {
                    Feed::Arg => match arg_value(lw, cx, out, w, input)? {
                        (v, Some(q)) => Src::At(v, at(lw, cx, w, f, x, q)?, q),
                        (v, None) => Src::Value(v),
                    },
                    Feed::Ring(o) => {
                        let part = Part::Gather { bound: o, input };
                        let q = exp(n, part, span)?;
                        Src::At(w.field(lw, part)?, at(lw, cx, w, f, x, q)?, q)
                    }
                };
                copy(cx, out, (dst, k), pos, src, x, span)?;
            }
            Op::Run { body, out: to } => {
                let v = run(lw, cx, w, body)?;
                let to = match to {
                    Out::None => {
                        expr_stmt(out, v);
                        continue;
                    }
                    Out::Value if w.value.is_none() => {
                        value = Some(v);
                        continue;
                    }
                    Out::Value => To::Value,
                    Out::Deal(b) => To::Array(b),
                };
                let m = w.bound(0)?.out.ok_or_else(|| internal(span, "a run of no output"))?;
                // Of the value of a tick of the caller made once in a loop, e ≤ 0 (the memo of U6b 2.5).
                let (dst, e) = target(lw, w, to)?;
                let pos = at(lw, cx, w, 0, m, e)?;
                copy(cx, out, (dst, e), pos, Src::Value(v), m, span)?;
            }
            Op::Deal { to, from, by } => {
                let x = w.bound(by)?.out.ok_or_else(|| internal(span, "a copy of no window"))?;
                let (from, (dst, e)) = (Part::Deal(from), target(lw, w, to)?);
                let (pos, q) = (at(lw, cx, w, by as usize, x, e)?, exp(n, from, span)?);
                let src = Src::At(w.field(lw, from)?, at(lw, cx, w, by as usize, x, q)?, q);
                copy(cx, out, (dst, e), pos, src, x, span)?;
            }
            Op::Each { bound: u, once, ref groups } => {
                if w.js.is_empty() {
                    prelower(lw, cx, out, w, std::slice::from_ref(op))?;
                }
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

/// Where a run or a copy writes (§11.9), with the exponent of its window:
/// the array of a boundary, or the value the ops make in a loop.
fn target(lw: &Lowerer, w: &Walk, to: To) -> R<(Expr, Ratio)> {
    match (to, &w.value, w.n.clock) {
        (To::Array(b), ..) => Ok((w.field(lw, Part::Deal(b))?, exp(w.n, Part::Deal(b), w.span)?)),
        (To::Value, Some(v), Clock::Tick(o)) => Ok((v.clone(), o)),
        (To::Value, ..) => Err(internal(w.span, "a value made in a loop of no local")),
    }
}

/// The arguments the ops `list` read in the loops of their `.up~` (of a
/// ring written from one, of an input a run reads of no ring), lowered
/// once before them in the order of the inputs, each in a `let` (the review
/// of U6b0, its low 5): read in a loop, the places of the nodes in them
/// would be in it, which the reads after it do not see.
fn prelower(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &mut Walk, list: &[Op]) -> R<()> {
    let (mut read, mut bodies) = (BTreeSet::new(), Vec::new());
    Op::walk(list, &mut |op| match *op {
        Op::Ring { input, from: Feed::Arg, .. } => {
            read.insert(input);
        }
        Op::Run { body, .. } => bodies.push(body),
        _ => {}
    });
    for body in bodies {
        read.extend(head_inputs(lw, w, body)?.into_iter().filter(|&i| w.n.ring_of(0, i).is_none()));
    }
    for input in read {
        let (v, q) = arg_value(lw, cx, out, w, input)?;
        w.args.push((input, materialize(cx, v, out, "__arg"), q));
    }
    Ok(())
}

/// The argument of the input `input` of the walk, in the frame of the
/// call, with the exponent q of its port there if it is a burst (§11.9):
/// that lowered before the loops ([`prelower`]), else lowered here, of a
/// burst its 2^q elements in a `let` ([`spread`]).
fn arg_value(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, w: &Walk, input: u32) -> R<(Expr, Option<Ratio>)> {
    if let Some((_, v, q)) = w.args.iter().find(|x| x.0 == input) {
        return Ok((v.clone(), *q));
    }
    let PlanKind::Instance { args, .. } = &w.n.kind else { return Err(internal(w.span, "an argument of no instance")) };
    let arg = *args.get(input as usize).ok_or_else(|| internal(w.span, "no argument of an input"))?;
    let port = w.n.args.iter().find(|a| a.expr == arg).map(|a| a.at);
    let port = port.ok_or_else(|| internal(w.span, "an argument read at no clock"))?;
    let v = lower_expr(lw, cx, arg)?;
    Ok(match port {
        Clock::Tick(q) if port.burst() => (materialize(cx, spread(cx, arg, port, v), out, "__arg"), Some(q)),
        _ => (v, None),
    })
}

/// The inputs of the head of the walk a run of its stage `body` reads, by
/// index ([`instance_args`]).
fn head_inputs(lw: &Lowerer, w: &Walk, body: ClockStage) -> R<Vec<u32>> {
    let (a, PlanKind::Instance { callee, .. }) = (lw.a, &w.n.kind) else {
        return Err(internal(w.span, "a run of no instance"));
    };
    let (Some(g), Some(fd)) = (a.flows.get(callee), a.def(*callee).as_flow()) else {
        return Err(internal(w.span, "an instance of no checked flow"));
    };
    Ok((0u32..).zip(inputs(g, fd, w.span)?).filter(|(_, i)| i.phase.stage() == body).map(|(k, _)| k).collect())
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
/// that stage, lowered here, those its chain gathers of their rings
/// ([`PlanNode::ring_of`]) and those lowered before the loops, each the
/// window of the frame of the head ([`window`], the memo of U6b 2.4).
fn run(lw: &mut Lowerer, cx: &mut FnCx, w: &Walk, body: ClockStage) -> R<Expr> {
    let (a, n, span) = (lw.a, w.n, w.span);
    let (&PlanKind::Instance { callee, ref args, .. }, ClockStage::Tick(k)) = (&n.kind, body) else {
        return Err(internal(span, format!("a run of {body:?} of no instance")));
    };
    let sub = lw.ensure_flow(callee)?;
    let g = a.flows.get(&callee).ok_or_else(|| internal(span, "an instance of no checked flow"))?;
    let f = sub.stage_fn(body).ok_or_else(|| internal(span, format!("a callee with no stage {k:?}")))?;
    let own = w.field(lw, Part::Own)?;
    let (words, mut lets) = (g.time_words(body), Vec::new());
    let time = if words > 0 { child_time(cx, &mut lets, w, words)? } else { Vec::new() };
    let mut given = Vec::new();
    for input in head_inputs(lw, w, body)? {
        let (src, e) = match (n.ring_of(0, input), w.args.iter().find(|x| x.0 == input)) {
            (Some(bound), _) => {
                let part = Part::Gather { bound, input };
                (w.field(lw, part)?, exp(n, part, span)?)
            }
            (None, Some((_, v, q))) => (v.clone(), q.unwrap_or(Ratio(0))),
            (None, None) => continue,
        };
        let v = match n.bounds.first().and_then(|b| *b.ins.get(input as usize)?) {
            Some(k) => window(cx, &mut lets, src, (k, e), |cx| at(lw, cx, w, 0, k, e), "__in", span)?,
            None => src,
        };
        given.push((input, v));
    }
    let inputs = instance_args(lw, cx, (callee, args), Phase::Tick(k), &given, span)?;
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
    window(cx, out, w.field(lw, part)?, (o, e), |cx| at(lw, cx, &w, n.bounds.len(), o, e), "__dealt", span)
}
