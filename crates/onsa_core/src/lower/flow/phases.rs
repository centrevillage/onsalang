//! The phase functions of a flow (§11.4): `init`, `reset`, `ctl`, `tick`
//! and those of the slower ticks, each with the work of its nodes, and the
//! driver of the slower ticks ([`drive`]).

use super::*;

/// `init(cfg, sample_rate) -> State`.
pub(super) fn gen_init<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let state_ty = Ty::Struct(shape.state_ty);
    let mut g = Gen::new(lw, shape, info, Phase::Init, state_ty.clone())?;
    let [cfg, sr] = &g.member_params(lw, shape, FlowFn::Init)?[..] else {
        return Err(internal(g.span, "`init` with another number of parameters"));
    };
    let (cfg, sr) = (cfg.clone(), sr.clone());
    let s = g.temp("s", state_ty.clone());
    let span = g.span;
    g.stmts.push(stmt(
        span,
        StmtKind::Let(
            LocalId(s.as_place().map(|p| p.root()).unwrap().0),
            Expr::new(state_ty.clone(), span, ExprKind::Zeroed),
        ),
    ));
    g.flow().sample_rate = sr.clone();
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    if info.stored(Kept::SampleRate) {
        let f = sfield(lw, info, &s, FieldOf::SampleRate, span)?;
        assign(&mut g.stmts, &f, sr.clone())?;
    }
    restart(lw, &mut g.cx, &mut g.stmts, &s)?;
    g.inputs_from(lw, shape, info, &cfg, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: Some(ClockStage::Init), loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut |lw, cx, out, id, s| {
        init_node(lw, cx, out, id, s, &sr)
    })?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    // S-27: the last store of `init`; a panic before it leaves the instance uninitialized.
    let initialized = sfield(lw, info, &s, FieldOf::Initialized, span)?;
    assign(&mut g.stmts, &initialized, lit(Ty::Bool, span, Lit::Bool(true)))?;
    g.finish(lw, fns.init, state_ty, false, Some(s));
    Ok(())
}

/// The plan of the flow `cx` lowers.
fn plan<'b>(cx: &FnCx<'b>) -> &'b FlowInfo {
    cx.flow.as_ref().expect("flow context").info
}

/// The work of a phase function on one node, in the scope of the state
/// given ([`each_node`]).
type NodeWork<'f> = dyn FnMut(&mut Lowerer, &mut FnCx, &mut Vec<Stmt>, NodeId, &Expr) -> R<()> + 'f;

/// How a phase function walks the nodes ([`each_node`]).
#[derive(Clone, Copy)]
struct Walk {
    /// The stage the arms of the `match~`s around a node are chosen at
    /// before its work ([`super::branches::choose_arms`]), if the function
    /// chooses them.
    arms: Option<ClockStage>,
    /// Whether a `par~` of the children given, which holds state when the
    /// flag is set, has a loop of its replicas in the function of the stage.
    loops: fn(&FlowInfo, &[NodeId], bool, ClockStage) -> bool,
}

/// A `par~` that holds state has a loop of its replicas, of no work too
/// (one of delays only in `ctl`).
fn held(_: &FlowInfo, _: &[NodeId], holds: bool, _: ClockStage) -> bool {
    holds
}

/// The phase of the function `cx` lowers.
fn phase(cx: &FnCx) -> Phase {
    cx.flow.as_ref().expect("flow context").phase
}

/// The work `f` of each of the nodes `ids` in the order of the table, in
/// the scope of `state`: the arms around a node chosen first; after the
/// work of a `par~`, its children in a loop of its replicas, each in the
/// scope of its element of the state.
fn each_node(
    lw: &mut Lowerer,
    cx: &mut FnCx,
    out: &mut Vec<Stmt>,
    ids: &[NodeId],
    state: &Expr,
    walk: Walk,
    f: &mut NodeWork,
) -> R<()> {
    let info = plan(cx);
    for &id in ids {
        let n = info.node(id);
        let span = cx.ast.expr(n.expr).span;
        if let Some(s) = walk.arms {
            super::branches::choose_arms(lw, cx, &n.arms, s, state, out)?;
        }
        f(lw, cx, out, id, state)?;
        let PlanKind::Par { children, state: holds, .. } = &n.kind else { continue };
        if !(walk.loops)(info, children, *holds, phase(cx).stage()) {
            continue;
        }
        let r = replica_loop(cx, &n.kind, span)?;
        let elem = index(sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?, r.index(cx, span))?;
        let mut body = Vec::new();
        cx.flow.as_mut().unwrap().push_scope(elem.clone());
        each_node(lw, cx, &mut body, children, &elem, walk, f)?;
        cx.flow.as_mut().unwrap().scopes.pop();
        out.push(r.each(cx, span, body));
    }
    Ok(())
}

/// Node initialisation (§11.4): stores, buffers, sub `init`s.
fn init_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr, sr: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, name, at) = (cx.ast.expr(n.expr).span, &n.path, |p| FieldOf::Node(id, p));
    match &n.kind {
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let v = init_value(lw, init, &t, span, |lw, e| lower_expr(lw, cx, e))?;
            let v = materialize(cx, v, out, &format!("{name}.init"));
            if info.field(at(Part::Init)).is_some() {
                assign(out, &sfield(lw, info, state, at(Part::Init), span)?, v.clone())?;
            }
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
        }
        PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = ring_len(&n.kind, span)?;
            let v = init_value(lw, init, &t, span, |lw, e| lower_expr(lw, cx, e))?;
            let v = materialize(cx, v, out, &format!("{name}.init"));
            if info.field(at(Part::Init)).is_some() {
                assign(out, &sfield(lw, info, state, at(Part::Init), span)?, v.clone())?;
            }
            let buf = sfield(lw, info, state, at(Part::Buf), span)?;
            let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
            assign(out, &buf, fill)?;
            assign(out, &sfield(lw, info, state, at(Part::W), span)?, u32_lit(span, 0))?;
        }
        PlanKind::Instance { callee, args, .. } => {
            // W7-21 U1: a chain of a callee with no table (in error) has no entries.
            if !n.chain.is_empty() && n.entries.is_empty() {
                return Err(internal(span, "a chain of an instance with no entries"));
            }
            let sub = lw.ensure_flow(*callee)?;
            let fields = instance_args(lw, cx, (*callee, args), Phase::Init, &[], span)?;
            let cfg = Expr::new(Ty::Struct(sub.config), span, ExprKind::Struct { ty: sub.config, fields });
            let sr = super::child_rate(sr, n, span)?;
            let c = call(sub.init, Ty::Struct(sub.state), span, vec![borrow(cfg), borrow(sr)]);
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, c)?;
        }
        PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// The time of `init` and `reset` in the state `s` (§11.6, §11.9): the
/// counter of the phase and `_tick_hi` at 0, the one place that
/// writes it (`reset_if~` does not, W7-10), then the fields written at a
/// tick and read at a faster stage at `T.default()` ([`defaults`]).
fn restart(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, s: &Expr) -> R<()> {
    let (info, span) = (plan(cx), s.span);
    if info.counts_time() {
        assign(out, &sfield(lw, info, s, FieldOf::Tick, span)?, u32_lit(span, 0))?;
    }
    if info.wide() {
        assign(out, &sfield(lw, info, s, FieldOf::TickHi, span)?, u32_lit(span, 0))?;
    }
    defaults(lw, cx, out, &info.fields, s)
}

/// The fields of `fields` of the struct `state` that start at
/// `T.default()` (§11.3, S-1186, [`FlowInfo::starts_default`]) set to it,
/// written so and not left to the zeroed state (a hand-written `Default`),
/// and those of the replicas of a `par~` among them in a loop of them.
fn defaults(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, fields: &[Field], state: &Expr) -> R<()> {
    let (info, span) = (plan(cx), state.span);
    for f in fields {
        if info.starts_default(f.of) {
            let place = sfield(lw, info, state, f.of, span)?;
            let v = crate::lower::derived::default_value(lw, &place.ty, span)?;
            assign(out, &place, v)?;
        }
        let FieldOf::Node(id, Part::Own) = f.of else { continue };
        let kind = &info.node(id).kind;
        let PlanKind::Par { fields: inner, .. } = kind else { continue };
        if !starts_default(info, inner) {
            continue;
        }
        let r = replica_loop(cx, kind, span)?;
        let elem = index(sfield(lw, info, state, f.of, span)?, r.index(cx, span))?;
        let mut body = Vec::new();
        defaults(lw, cx, &mut body, inner, &elem)?;
        out.push(r.each(cx, span, body));
    }
    Ok(())
}

/// Whether one of `fields` starts at `T.default()`, in a replica too.
fn starts_default(info: &FlowInfo, fields: &[Field]) -> bool {
    fields.iter().any(|f| {
        info.starts_default(f.of)
            || matches!(f.of, FieldOf::Node(id, Part::Own)
                if matches!(&info.node(id).kind, PlanKind::Par { fields, .. } if starts_default(info, fields)))
    })
}

/// `reset(inout s)`.
pub(super) fn gen_reset<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Init, Ty::Unit)?;
    let span = g.span;
    let [s] = &g.member_params(lw, shape, FlowFn::Reset)?[..] else {
        return Err(internal(span, "`reset` with another number of parameters"));
    };
    let s = s.clone();
    g.flow().push_scope(s.clone());
    restart(lw, &mut g.cx, &mut g.stmts, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: None, loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut reset_node)?;
    let poisoned = sfield(lw, info, &s, FieldOf::Poisoned, span)?;
    assign(&mut g.stmts, &poisoned, lit(Ty::Bool, span, Lit::Bool(false)))?;
    g.finish(lw, fns.reset, Ty::Unit, true, None);
    Ok(())
}

/// A node back to its value after `init` (§11.4), from the copy of its
/// `init` value the state keeps.
fn reset_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    match &n.kind {
        PlanKind::Prev { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, state, at(Part::Init), span))?;
            assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v)?;
        }
        PlanKind::Delay { init, ty, .. } | PlanKind::Vdelay { init, ty, .. } => {
            let t = lw.core_ty(*ty, &[], span)?;
            let len = ring_len(&n.kind, span)?;
            let v = init_value(lw, init, &t, span, |lw, _| sfield(lw, info, state, at(Part::Init), span))?;
            let buf = sfield(lw, info, state, at(Part::Buf), span)?;
            let fill = Expr::new(buf.ty.clone(), span, ExprKind::Repeat { elem: Box::new(v), n: len });
            assign(out, &buf, fill)?;
            assign(out, &sfield(lw, info, state, at(Part::W), span)?, u32_lit(span, 0))?;
        }
        PlanKind::Instance { callee, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            let st = sfield(lw, info, state, at(Part::Own), span)?;
            expr_stmt(out, call(sub.reset, Ty::Unit, span, vec![inout(st)]));
            // The condition and the count of each guard of its chain (§11.9: `reset`, not `reset_if~`).
            for g in 0..n.guards.len() as u32 {
                for (part, v) in
                    [(Part::On(g), lit(Ty::Bool, span, Lit::Bool(false))), (Part::Count(g), u32_lit(span, 0))]
                {
                    if info.field_at(at(part)).is_some() {
                        assign(out, &sfield(lw, info, state, at(part), span)?, v)?;
                    }
                }
            }
        }
        PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// `ctl(inout s, p: Params)`.
pub(super) fn gen_ctl<'b>(lw: &mut Lowerer<'b>, shape: &FlowShape, info: &'b FlowInfo, fns: &FlowFns) -> R<()> {
    let mut g = Gen::new(lw, shape, info, Phase::Ctl, Ty::Unit)?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    let p = g.param("p", Mode::Borrow, Ty::Struct(shape.params_ty));
    g.flow().push_scope(s.clone());
    g.slots(info)?;
    g.inputs_from(lw, shape, info, &p, &s)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: Some(ClockStage::Block), loops: held };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut ctl_node)?;
    g.finish(lw, fns.ctl, Ty::Unit, true, None);
    Ok(())
}

/// Sub `ctl`s with the sub's `Params` built from the `Ctl`-input arguments.
fn ctl_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let span = cx.ast.expr(n.expr).span;
    match &n.kind {
        PlanKind::Instance { callee, args, .. } => {
            let sub = lw.ensure_flow(*callee)?;
            let fields = instance_args(lw, cx, (*callee, args), Phase::Ctl, &[], span)?;
            let params = Expr::new(Ty::Struct(sub.params), span, ExprKind::Struct { ty: sub.params, fields });
            let st = sfield(lw, info, state, FieldOf::Node(id, Part::Own), span)?;
            expr_stmt(out, call(sub.ctl, Ty::Unit, span, vec![inout(st), borrow(params)]));
        }
        PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } | PlanKind::Par { .. } => {}
    }
    Ok(())
}

/// The function of the tick `stage` (§11.4, §11.9): `tick(inout s, [t],
/// <Sig inputs>)` of the `sample` of the body, `tick_<N>(inout s, [t],
/// <its inputs>)` of a slower one, which [`drive`] or a caller
/// ([`super::chain::entry`]) calls through [`call_stage`]; the words of the
/// time `t`, `t_hi` of a stage that takes them (`FlowInfo::time_words`).
/// In order: its inputs the state keeps stored,
/// its `let`s and the fields hoisted to it ([`Gen::stage_lets`]), the
/// output of the stage that makes it (`FlowInfo::out_stage`), the stages
/// of the callees that run in it ([`child_runs`]), the stores of its
/// nodes, and last in `tick` the counter of the phase advanced when it is
/// the grid of the slower stages (`FlowInfo::counter`).
// SPEC-GAP(S-1206): the order in a stage is that of the reference
// evaluator (S-1159 provisional): its `let`s, then the stages of the
// callees, then the stores.
pub(super) fn gen_tick<'b>(
    lw: &mut Lowerer<'b>,
    shape: &FlowShape,
    info: &'b FlowInfo,
    fns: &FlowFns,
    stage: ClockStage,
) -> R<()> {
    let span = shape.span;
    let (ClockStage::Tick(k), Some(fid)) = (stage, fns.stage_fn(stage)) else {
        return Err(internal(span, format!("no function of the tick {stage:?}")));
    };
    let phase = Phase::Tick(k);
    let makes_out = info.out_stage == Some(stage);
    let out_ty = if makes_out { shape.out_val.clone() } else { Ty::Unit };
    let mut g = Gen::new(lw, shape, info, phase, out_ty.clone())?;
    let s = g.param("s", Mode::Inout, Ty::Struct(shape.state_ty));
    for name in ["t", "t_hi"].into_iter().take(info.time_words(stage)) {
        let t = g.param(name, Mode::Borrow, Ty::u32());
        g.flow().time.push(t);
    }
    let inputs: Vec<&Input> = shape.inputs.iter().filter(|i| i.phase == phase).collect();
    for i in &inputs {
        g.param_local(LocalId(i.local.0), Mode::Borrow);
    }
    g.flow().push_scope(s.clone());
    // S-1213: an input at `sample / N` is the argument of its tick,
    // kept until the next (an argument of a parameter kind too).
    for i in inputs {
        if let Some(of) = info.kept_field(i.local) {
            let v = local_expr(&g.cx, LocalId(i.local.0), i.decl.span);
            assign(&mut g.stmts, &sfield(lw, info, &s, of, i.decl.span)?, v)?;
        }
    }
    g.slots(info)?;
    g.state_overrides(lw, info, &s)?;
    g.const_lets(lw, info)?;
    g.stage_lets(lw, info, &s)?;
    let mut out = None;
    if makes_out {
        let output = info.output.ok_or_else(|| internal(span, "flow without an output expression"))?;
        let v = lower_expr(lw, &mut g.cx, output)?;
        let v = of_type(v, &out_ty)?;
        // Materialised before the stores so a `prev` inside the output reads first (§11.4).
        out = Some(g.let_("__out", v));
    }
    let nodes: Vec<NodeId> = info.top().collect();
    let walk = Walk { arms: None, loops: |info, children, _, s| runs_in(info, children, s) };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut child_runs)?;
    let walk = Walk { arms: None, loops: |info, children, _, s| stores(info, children, s) };
    each_node(lw, &mut g.cx, &mut g.stmts, &nodes, &s, walk, &mut store_node)?;
    if phase == Phase::SAMPLE && info.counter() == Counter::Tick {
        let t = sfield(lw, info, &s, FieldOf::Tick, span)?;
        assign(&mut g.stmts, &t, wrap_add(t.clone(), span))?;
    }
    g.finish(lw, fid, out_ty, true, out);
    Ok(())
}

/// The work of the instance `id` in the function of the stage lowered
/// that does not make its value where it is read (§11.9, S-1088: that
/// does, [`super::nodes`]): its entry not read ([`super::chain::entry`]),
/// the arms around it chosen first for the arguments that read their
/// bindings.
fn child_runs(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let (info, stage) = (plan(cx), phase(cx).stage());
    let n = info.node(id);
    let Some(e) = n.entry(stage, false) else { return Ok(()) };
    super::branches::choose_arms(lw, cx, &n.arms, stage, state, out)?;
    // An entry not read makes no value.
    super::chain::entry(lw, cx, out, id, state, e)?;
    Ok(())
}

/// Whether one of the nodes `ids` has work in the function of the stage
/// `s` ([`child_runs`]), in a `par~` of them too.
fn runs_in(info: &FlowInfo, ids: &[NodeId], s: ClockStage) -> bool {
    ids.iter().any(|&id| match &info.node(id).kind {
        PlanKind::Par { children, .. } => runs_in(info, children, s),
        _ => info.node(id).entry(s, false).is_some(),
    })
}

/// A run of the stage `x` of a flow whose plan is `g` (§11.9, S-1088):
/// its function `f` of the result `ret` on `state`, with the words of the
/// time it takes cut from `time` (made in `lets`) and its inputs of that
/// stage, lowered.
pub(super) struct StageRun<'g> {
    pub g: &'g FlowInfo,
    pub f: FnId,
    pub ret: Ty,
    pub x: ClockStage,
    pub state: Expr,
    pub time: Vec<Expr>,
    pub lets: Vec<Stmt>,
    pub inputs: Vec<Expr>,
}

/// The call of the run `r`, after its `lets`: the one place that calls
/// the function of a stage of a flow, of `process` ([`drive`]) and of a
/// caller ([`super::chain::entry`]); the time cut to the words its stage
/// takes (`FlowInfo::time_words`).
pub(super) fn call_stage(r: StageRun, span: Span) -> R<Expr> {
    let time = r.time.get(..r.g.time_words(r.x)).ok_or_else(|| internal(span, "a stage of more time"))?;
    let time = time.iter().cloned().map(borrow);
    let args = [inout(r.state)].into_iter().chain(time).chain(r.inputs.into_iter().map(borrow)).collect();
    Ok(after(r.lets, call(r.f, r.ret, span, args)))
}

/// The statements of each stage of `runs` (slowest first, S-578, S-1079),
/// each run when the counter `c` is at the ticks of its stage, a multiple
/// of its N, so the first frame runs it and the tick does not depend on how
/// the host splits the frames (§11.9). The one drive of the stages of a
/// part: of `process` (`c` the counter of the phase of its state, a run of
/// [`call_stage`] of each stage; the runs j of an `.up~`, `c` the j, and
/// the grid of a `when~` of W7-10 too). The stage of `sample` runs at each.
pub(super) fn drive(runs: Vec<(ClockStage, Vec<Stmt>)>, c: &Expr, span: Span, out: &mut Vec<Stmt>) -> R<()> {
    for (stage, run) in runs {
        if stage == ClockStage::SAMPLE {
            out.extend(run);
            continue;
        }
        let mask = match stage {
            ClockStage::Tick(k) => k.made_n().and_then(|n| u32::try_from(n - 1).ok()),
            _ => None,
        };
        let mask = mask.ok_or_else(|| internal(span, format!("no counter of the tick {stage:?}")))?;
        let low = checked_binary(BinOp::BitAnd, c.clone(), u32_lit(span, mask));
        let due = cmp(CmpOp::Eq, low, u32_lit(span, 0));
        out.push(stmt(span, StmtKind::If(due, Block { stmts: run, value: None }, Block::default())));
    }
    Ok(())
}

/// The time of the outermost advanced after its `tick` (§11.4, S-1217,
/// S-1211): the counter of the time alone ([`Counter::Process`]), then
/// `_tick_hi` when `_tick` goes round. The one place of it.
pub(super) fn advance(lw: &Lowerer, info: &FlowInfo, s: &Expr, span: Span, out: &mut Vec<Stmt>) -> R<()> {
    let t = || sfield(lw, info, s, FieldOf::Tick, span);
    if info.counter() == Counter::Process {
        assign(out, &t()?, wrap_add(t()?, span))?;
    }
    if info.wide() {
        let (hi, mut carry) = (sfield(lw, info, s, FieldOf::TickHi, span)?, Vec::new());
        assign(&mut carry, &hi, wrap_add(hi.clone(), span))?;
        let round = cmp(CmpOp::Eq, t()?, u32_lit(span, 0));
        out.push(stmt(span, StmtKind::If(round, Block { stmts: carry, value: None }, Block::default())));
    }
    Ok(())
}

/// `x +% 1` of a `U32`.
pub(super) fn wrap_add(x: Expr, span: Span) -> Expr {
    let (lhs, rhs) = (Box::new(x), Box::new(u32_lit(span, 1)));
    Expr::new(Ty::u32(), span, ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Wrap, lhs, rhs })
}

/// The end-of-tick store of a node (§11.4) in node order: `prev` saves its
/// argument, `delay` / `vdelay` write the argument at `w` and advance; a
/// `par~` that stores ([`stores`]) stores its replicas in a loop of its own
/// at its place in the order ([`each_node`]).
///
/// They are the second phase of §11.4 (read all, then store all) with no
/// temporaries of their own: each node is read once where it is lowered
/// (memoised), a node of the body before all the stores, and a node first
/// lowered here (in the first argument of a delay) in the store of the
/// nearest delay around it, which the order (preorder, the outer first)
/// puts before the node's own store. So no read sees a store of this tick.
/// A change of the order of the stores (W7-06, W7-09) keeps that: the read
/// of a node first lowered here comes before its store.
// SPEC-GAP(S-1154): the stores (and their panics) are in the preorder of
// the table; S-1126 (1): after every `let` and the output of the body.
fn store_node(lw: &mut Lowerer, cx: &mut FnCx, out: &mut Vec<Stmt>, id: NodeId, state: &Expr) -> R<()> {
    let info = plan(cx);
    let n = info.node(id);
    let Some(arg) = stored_arg(info, id, phase(cx).stage()) else { return Ok(()) };
    let (span, at) = (cx.ast.expr(n.expr).span, |p| FieldOf::Node(id, p));
    let ring = match n.kind {
        PlanKind::Prev { .. } => None,
        PlanKind::Delay { .. } | PlanKind::Vdelay { .. } => Some(ring_len(&n.kind, span)?),
        PlanKind::Instance { .. } | PlanKind::Par { .. } => return Err(internal(span, "a store of no delay")),
    };
    let v = lower_expr(lw, cx, arg)?;
    let Some(len) = ring else {
        return assign(out, &sfield(lw, info, state, at(Part::Own), span)?, v);
    };
    let buf = sfield(lw, info, state, at(Part::Buf), span)?;
    let w = sfield(lw, info, state, at(Part::W), span)?;
    assign(out, &index(buf, w.clone())?, v)?;
    let next = checked_binary(BinOp::Rem, checked_binary(BinOp::Add, w.clone(), u32_lit(span, 1)), u32_lit(span, len));
    assign(out, &w, next)
}

/// The argument the node `id` stores at the end of the function of the
/// stage `s` ([`store_node`]), the one list of the nodes that store: a
/// `prev` into its field, a `delay` / `vdelay` into its ring, in the
/// function of its tick; an instance stores in its own `tick`, a `par~` in
/// the loop of its replicas.
fn stored_arg(info: &FlowInfo, id: NodeId, s: ClockStage) -> Option<ExprId> {
    let n = info.node(id);
    let arg = match &n.kind {
        PlanKind::Prev { arg, .. } | PlanKind::Delay { arg, .. } | PlanKind::Vdelay { arg, .. } => *arg,
        PlanKind::Instance { .. } | PlanKind::Par { .. } => return None,
    };
    (info.node_stage(id) == Some(s)).then_some(arg)
}

/// Whether the nodes `ids` store in the function of the stage `s`
/// ([`stored_arg`]), in a `par~` of them too.
fn stores(info: &FlowInfo, ids: &[NodeId], s: ClockStage) -> bool {
    ids.iter().any(|&id| match &info.node(id).kind {
        PlanKind::Par { children, .. } => stores(info, children, s),
        PlanKind::Prev { .. } | PlanKind::Delay { .. } | PlanKind::Vdelay { .. } | PlanKind::Instance { .. } => {
            stored_arg(info, id, s).is_some()
        }
    })
}
