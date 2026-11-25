//! The table of the event stages (§11.11, W7-11 U2), worked out by hand from
//! the text and the traces of the memo of U2, and not of what it makes: the
//! source of each event clock, the stage that ticks it, the work of each
//! instance at the events, the stages that give out the events of the
//! output, and the words of the time; the forms not run; and what a delay
//! reads of events where it is written (S-1240).

use super::super::{Entry, EventFrom, Op, Out, Words};
use crate::clock::ClockStage;
use crate::flow::FlowInfo;
use crate::tests::{analyze, pkg};
use crate::{Analysis, Package};

/// A part that gives out an event at `sample`, at `sample / 4`, of an event
/// and of the first of two; that takes an event; and that does both.
const HEAD: &str = "flow gen(x: U32 at sample) -> U32 at event {
  if x % 3 != 0 { Some(x) } else { None }
}
flow gen4(x: U32 at (sample / 4)) -> U32 at event {
  if x != 0 { Some(x) } else { None }
}
flow cnt(e: U32 at event) -> U32 at sample {
  let n = prev~(^n) + e
  n at sample
}
flow fwd(e: U32 at event) -> U32 at event {
  Some(e + 1)
}
flow both(a: U32 at event, b: U32 at event) -> U32 at event {
  let _ = b
  Some(a)
}
flow g5(x: U32 at sample, c: U32 at event) -> U32 at event {
  let r = cnt~(c)
  if (x + r) % 3 != 0 { Some(x + r) } else { None }
}
";

fn analysis(src: &str) -> (Package, Analysis, String) {
    let text = format!("{HEAD}{src}");
    let p = pkg(&[("main", &text)]);
    let a = analyze(&p);
    assert!(a.diagnostics.is_empty(), "{src}: {:?}", a.diagnostics);
    (p, a, text)
}

fn flow<'a>(a: &'a Analysis, name: &str) -> &'a FlowInfo {
    &a.flows[&crate::tests::def(a, name)]
}

/// The stage `s` of `f`: the exponent of a tick, the name of the input or the
/// path of the call of an event.
fn stage(f: &FlowInfo, s: ClockStage) -> String {
    match s {
        ClockStage::Tick(k) => k.0.to_string(),
        ClockStage::Event(src) => match f.event(src).expect("a source").from {
            EventFrom::Input(i) => f.body.locals[f.inputs[i as usize].0 as usize].name.clone(),
            EventFrom::Call(id) => f.node(id).path.clone(),
        },
        s => format!("{s:?}"),
    }
}

/// The work of the nodes of `f` at `path`, of the callee `g`: `<stage of the
/// caller>: <stage of g>><where its result goes>` of each entry.
fn work(a: &Analysis, f: &FlowInfo, path: &str, g: &str) -> Vec<String> {
    let g = flow(a, g);
    let op = |op: &Op| match op {
        Op::Run { body, out } => {
            let out = match out {
                Out::None => "-",
                Out::Value => "value",
                Out::Event => "event",
                other => panic!("{other:?}"),
            };
            format!("{}>{out}", stage(g, *body))
        }
        other => panic!("{other:?}"),
    };
    let entry = |e: &Entry| format!("{}: {}", stage(f, e.caller), e.ops.iter().map(op).collect::<Vec<_>>().join(", "));
    let n = f.nodes.iter().find(|n| n.path == path).unwrap_or_else(|| panic!("no node {path}"));
    n.entries.iter().map(entry).collect()
}

/// Each source of `f` with the stage that ticks it (`!` of one that gives),
/// and the stage that gives out the events of its output.
fn events(f: &FlowInfo) -> (Vec<String>, Option<String>) {
    assert!(f.planned());
    let one = |p: &super::EventPlan| {
        let by = p.parent.map_or("-".to_string(), |s| stage(f, s));
        assert_eq!(f.gives(ClockStage::Event(p.src)), p.gives);
        format!("{}{} < {by}", stage(f, ClockStage::Event(p.src)), if p.gives { "!" } else { "" })
    };
    (f.events.iter().map(one).collect(), f.emit.map(|s| stage(f, s)))
}

fn no<T>() -> Vec<T> {
    Vec::new()
}

/// x1, x3, x5 and n3 of the memo: the call of the event runs at `sample` and
/// gives; a receiver above the call that gives (x1), in an argument of it
/// (x3) and the giving call itself (x5) has its work at the event; of events
/// of events (n3), each is ticked by the one before it.
#[test]
fn the_stages_of_the_events_of_a_straight_line() {
    let (_, a, _) = analysis(
        "pub flow x1(x: U32 at sample) -> U32 at sample {\n  let h = cnt~(prev~(^d))\n  let d = gen~(x)\n  h\n}\n\
         pub flow x3(x: U32 at sample) -> U32 at sample {\n  let d = gen~(cnt~(prev~(^d)) + x)\n  d at sample\n}\n\
         pub flow x5(x: U32 at sample) -> U32 at sample {\n  let d = g5~(x, prev~(^d))\n  d at sample\n}\n\
         rt fn add(a: U32, b: U32) -> U32 {\n  a + b\n}\n\
         pub flow n3(x: U32 at sample) -> U32 at sample {\n  let d = fwd~(fwd~(gen~(x)))\n  let n = add(d, prev~(^n))\n  n at sample\n}\n\
         pub flow n5(m: U32 at event) -> U32 at sample {\n  let n = both~(m, prev~(^n))\n  n at sample\n}\n",
    );
    let f = flow(&a, "x1");
    assert_eq!(events(f), (vec!["d.gen_0 < 0".into()], None));
    assert_eq!(work(&a, f, "h", "cnt"), ["0: 0>value", "d.gen_0: e>-"]);
    assert_eq!(work(&a, f, "d.gen_0", "gen"), ["0: 0>event"]);
    let f = flow(&a, "x3");
    assert_eq!(events(f), (vec!["d.gen_0 < 0".into()], None));
    assert_eq!(work(&a, f, "d.cnt_0", "cnt"), ["0: 0>value", "d.gen_0: e>-"]);
    let g = flow(&a, "g5");
    assert_eq!(events(g), (vec!["c < -".into()], Some("0".into())));
    assert_eq!(work(&a, g, "r", "cnt"), ["0: 0>value", "c: e>-"]);
    let f = flow(&a, "x5");
    assert_eq!(events(f), (vec!["d.g5_0 < 0".into()], None));
    assert_eq!(work(&a, f, "d.g5_0", "g5"), ["0: 0>event", "d.g5_0: c>-"]);
    let g = flow(&a, "fwd");
    assert_eq!(events(g), (vec!["e! < -".into()], Some("e".into())));
    let f = flow(&a, "n3");
    let mut all = events(f).0;
    all.sort();
    assert_eq!(all, ["d.fwd_0 < d.fwd_1", "d.fwd_1 < d.gen_0", "d.gen_0 < 0"]);
    assert_eq!(work(&a, f, "d.fwd_0", "fwd"), ["0: 0>-", "d.fwd_1: e>event"]);
    assert_eq!(work(&a, f, "d.fwd_1", "fwd"), ["0: 0>-", "d.gen_0: e>event"]);
    assert_eq!(work(&a, f, "d.gen_0", "gen"), ["0: 0>event"]);
    // Ticked by `m`, the call takes its own event too.
    let f = flow(&a, "n5");
    assert_eq!(events(f), (vec!["m < -".into(), "n.both_0 < m".into()], None));
    assert_eq!(work(&a, f, "n.both_0", "both"), ["0: 0>-", "m: a>event", "n.both_0: b>-"]);
}

/// D2e: one event bound to two inputs is two ticks in one entry, in the order
/// declared (S-1236), and two events are two entries; a flow whose events
/// come of the first input gives them at it.
#[test]
fn the_entry_of_one_event_of_two_inputs() {
    let (_, a, _) = analysis(
        "pub flow d2e(m: U32 at event) -> U32 at sample {\n  let e = both~(m, m)\n  e at sample\n}\n\
         pub flow two(m: U32 at event, k: U32 at event) -> U32 at sample {\n  let e = both~(k, m)\n  e at sample\n}\n",
    );
    assert_eq!(events(flow(&a, "both")), (vec!["a! < -".into(), "b < -".into()], Some("a".into())));
    let f = flow(&a, "d2e");
    assert_eq!(events(f), (vec!["m < -".into(), "e.both_0 < m".into()], None));
    assert_eq!(work(&a, f, "e.both_0", "both"), ["0: 0>-", "m: a>event, b>-"]);
    let f = flow(&a, "two");
    assert_eq!(events(f), (vec!["m < -".into(), "k < -".into(), "e.both_0 < k".into()], None));
    assert_eq!(work(&a, f, "e.both_0", "both"), ["0: 0>-", "m: b>-", "k: a>event"]);
}

/// b1w: the events of the output come of a call two events down, so each
/// stage on the way gives; its caller has them of its `sample`. A flow that
/// gives out at `sample / 4` (S-1196: of the `at` of a value of `block`; of a
/// call of one, the tick of the caller) gives at that stage alone.
#[test]
fn the_stage_that_gives_out_the_events() {
    let (_, a, _) = analysis(
        "flow b1w(x: U32 at sample) -> U32 at event {\n  let a = gen~(x)\n  let b = fwd~(a)\n  Some(b)\n}\n\
         pub flow calls(x: U32 at sample) -> U32 at sample {\n  cnt~(b1w~(x))\n}\n\
         flow slow(p: U32 at block) -> U32 at event {\n  Some(p) at (sample / 4)\n}\n\
         pub flow at4(p: U32 at block, x: U32 at (sample / 4)) -> U32 at sample {\n  cnt~(slow~(p)) + cnt~(gen4~(x))\n}\n\
         pub flow keep(x: U32 at sample, m: U32 at event) -> U32 at event {\n  let k = cnt~(m)\n  if x > 0 { Some(k) } else { None }\n}\n",
    );
    let f = flow(&a, "b1w");
    assert_eq!(events(f), (vec!["a.gen_0! < 0".into(), "b.fwd_0! < a.gen_0".into()], Some("0".into())));
    assert_eq!(work(&a, f, "b.fwd_0", "fwd"), ["0: 0>-", "a.gen_0: e>event"]);
    assert!(f.gives(ClockStage::SAMPLE) && !f.gives(ClockStage::Block));
    let f = flow(&a, "calls");
    assert_eq!(events(f), (vec!["_out.b1w_0 < 0".into()], None));
    assert_eq!(work(&a, f, "_out.b1w_0", "b1w"), ["0: 0>event"]);
    let tick4 = ClockStage::Tick(crate::clock::Ratio(-2));
    let f = flow(&a, "slow");
    assert_eq!(events(f), (no(), Some("-2".into())));
    assert!(f.gives(tick4) && !f.gives(ClockStage::SAMPLE));
    let f = flow(&a, "at4");
    assert_eq!(work(&a, f, "_out.slow_0", "slow"), ["-2: -2>event", "0: 0>-"]);
    assert_eq!(work(&a, f, "_out.gen4_0", "gen4"), ["-2: -2>event", "0: 0>-"]);
    assert_eq!(events(f), (vec!["_out.slow_0 < -2".into(), "_out.gen4_0 < -2".into()], None));
    // Given out at `sample`, and an event of an input beside it.
    assert_eq!(events(flow(&a, "keep")), (vec!["m < -".into()], Some("0".into())));
}

/// The time of the stage of an event (`sample_tick()` in it, §11.4) is of the
/// stages that tick it, of a caller by the tick of its input, and two words
/// under a `.down~`.
#[test]
fn the_time_of_an_event_is_of_the_stages_that_tick_it() {
    let (_, a, _) = analysis(
        "flow tke(e: U32 at event) -> U32 at event {\n  Some(sample_tick() + e)\n}\n\
         pub flow line(x: U32 at sample) -> U32 at sample {\n  let d = fwd~(gen~(x))\n  let t = tke~(d)\n  t at sample\n}\n\
         pub flow slow(x: U32 at (sample / 2)) -> U32 at sample {\n  line~(x).down~(2) at sample\n}\n",
    );
    let time = |name: &str| {
        let f = flow(&a, name);
        let mut t: Vec<_> = f.time.iter().map(|(&s, &w)| (stage(f, s), w)).collect();
        t.sort_by(|x, y| x.0.cmp(&y.0));
        t
    };
    use Words::{One, Two};
    assert_eq!(time("tke"), [("e".into(), One)]);
    let line = [("0".into(), One), ("d.fwd_0".into(), One), ("d.gen_0".into(), One)];
    assert_eq!(time("line"), line);
    assert_eq!(time("slow"), [("-1".into(), Two)]);
}

/// The text of the form not run of the flow `top` of `src`, and whether it
/// has its tables; the E0200 of it is still of a word `event`.
fn form(src: &str) -> Option<String> {
    let (_, a, text) = analysis(src);
    let f = flow(&a, "top");
    assert_eq!(f.event_form.is_none(), f.planned(), "{src}");
    assert!(f.event_gate().is_some(), "{src}");
    if f.event_form.is_some() {
        assert!(f.nodes.iter().all(|n| n.entries.is_empty()) && f.fields.is_empty() && f.emit.is_none(), "{src}");
    }
    f.event_form.map(|s| s.text_in(&text).to_string())
}

fn forms(body: &str) -> Option<String> {
    form(&format!(
        "flow own(x: U32 at sample) -> U32 at sample {{\n  cnt~(gen~(x))\n}}\n\
         pub flow top(x: U32 at sample, m: U32 at event, c: Bool at sample) -> U32 at sample {{\n  let _ = m\n  let _ = c\n{body}\n}}\n"
    ))
}

/// The forms of a chain: of a call of a flow with an event port, of a
/// condition at an event and of a delay at one; not of a flow with events
/// inside alone, and of a condition with `at sample`.
#[test]
fn the_chains_not_run() {
    assert_eq!(forms("  cnt~(m).reset_if~(c)").as_deref(), Some("cnt~(m)"));
    assert_eq!(forms("  let d = gen~(x).when~(c)\n  d at sample").as_deref(), Some("gen~(x)"));
    assert_eq!(forms("  let q = m > 3\n  own~(x).reset_if~(q)").as_deref(), Some("reset_if"));
    assert_eq!(forms("  own~(x).when~(m > 3)").as_deref(), Some("when"));
    assert_eq!(forms("  let d = prev~(m).reset_if~(m > 3)\n  d at sample").as_deref(), Some("prev~(m)"));
    assert_eq!(forms("  own~(x).when~(c) + own~(x).reset_if~(c)"), None);
    assert_eq!(forms("  let q = m > 3\n  own~(x).when~(q at sample) + prev~(x).reset_if~(q at sample)"), None);
    // The first in the order of the text.
    assert_eq!(forms("  own~(x).when~(m > 3) + cnt~(m).reset_if~(c)").as_deref(), Some("when"));
}

/// The forms in a `par~`, an `if~` and a `match~` (the conditions, the
/// scrutinee and the guards too): a call of a flow with an event port, a
/// delay at an event, a computed part of one; not a name of one.
#[test]
fn the_branches_not_run() {
    let par = "  let y = par~ i in 0..<2 { cnt~(m) + i }\n  y[0] + y[1]";
    assert_eq!(forms(par).as_deref(), Some("cnt~(m)"));
    let par = "  let y = par~ i in 0..<2 { (prev~(m) at sample) + prev~(x) + i }\n  y[0] + y[1]";
    assert_eq!(forms(par).as_deref(), Some("prev~(m)"));
    let par = "  let y = par~ i in 0..<2 { ((m * 2) at sample) + prev~(x) + i }\n  y[0] + y[1]";
    assert_eq!(forms(par).as_deref(), Some("m * 2"));
    // The fields of a `par` are of each replica too.
    let par = "  let y = par i in 0..<2 { ((m * 2) at sample) + x + i }\n  y[0] + y[1]";
    assert_eq!(forms(par).as_deref(), Some("m * 2"));
    let par = "  let y = par~ i in 0..<2 { (m at sample) + prev~(x) + i + own~(x) }\n  y[0] + y[1]";
    assert_eq!(forms(par), None);
    let if_ = "  if~ c { cnt~(gen~(x)) } else { prev~(x) }";
    assert_eq!(forms(if_).as_deref(), Some("cnt~(gen~(x))"));
    let if_ = "  if~ ((m * 2) at sample) > x { prev~(x) } else { x }";
    assert_eq!(forms(if_).as_deref(), Some("m * 2"));
    let if_ = "  if~ (m at sample) > x { prev~(x) } else { m at sample }";
    assert_eq!(forms(if_), None);
    let m_ = "  match~ cnt~(m) { 0 => prev~(x), v => v }";
    assert_eq!(forms(m_).as_deref(), Some("cnt~(m)"));
    let m_ = "  let y = match~ m { v if m > 3 => prev~(v), v => v }\n  y at sample";
    assert_eq!(forms(m_).as_deref(), Some("prev~(v)"));
    let m_ = "  match~ (m at sample) { 0 => own~(x), v => v }";
    assert_eq!(forms(m_), None);
    // A plain `if` and `match` hold computed parts under a guard.
    assert_eq!(forms("  let y = if m > 3 { m * 2 } else { m }\n  y at sample"), None);
}

/// S-1237: a source nothing outside it ticks, on the way to the output, not
/// on it, and two that tick one another, with one after them; at the first
/// call of the loop in the text. One that the `sample` also ticks is run.
#[test]
fn a_source_its_own_output_ticks_is_not_run() {
    let d = "  let d = fwd~(prev~(^d))\n  d at sample";
    assert_eq!(forms(d).as_deref(), Some("fwd~(prev~(^d))"));
    let d = "  let d = fwd~(prev~(^d))\n  let n = cnt~(d)\n  x + n - n";
    assert_eq!(forms(d).as_deref(), Some("fwd~(prev~(^d))"));
    let long = "  let t = fwd~(prev~(^b))\n  let a = fwd~(prev~(^b))\n  let b = fwd~(a)\n  cnt~(t) + cnt~(b)";
    assert_eq!(forms(long).as_deref(), Some("fwd~(prev~(^b))"));
    let (_, a, text) = analysis(&format!("pub flow top(x: U32 at sample) -> U32 at sample {{\n{long} + x\n}}\n"));
    let at = flow(&a, "top").event_form.expect("a loop");
    // The loop is of `a` and `b`; `t` is after it.
    assert_eq!(&text[..at.start as usize].lines().last().unwrap_or_default(), &"  let a = ");
    let own = form("pub flow top() -> U32 at event {\n  let d = fwd~(prev~(^d))\n  Some(d)\n}\n");
    assert_eq!(own.as_deref(), Some("fwd~(prev~(^d))"));
    assert_eq!(forms("  let d = g5~(x, prev~(^d))\n  d at sample"), None);
}

/// A caller of a flow of a form not run is of a form that is (the source of
/// the call is in its table, ticked by none): the lowering stops at the
/// callee, and the check at no internal error.
#[test]
fn a_caller_of_a_form_not_run_has_its_sources() {
    let (_, a, _) = analysis(
        "flow bad(x: U32 at sample, m: U32 at event) -> U32 at event {\n  let y = par~ i in 0..<2 { cnt~(m) + i }\n  if y[0] > x { Some(y[1]) } else { None }\n}\n\
         pub flow top(x: U32 at sample, m: U32 at event) -> U32 at sample {\n  let d = bad~(x, m)\n  let n = cnt~(d)\n  n + (prev~(d) at sample)\n}\n\
         pub flow on(x: U32 at sample, m: U32 at event) -> U32 at event {\n  let d = bad~(x, m)\n  Some(d)\n}\n\
         pub flow last(x: U32 at sample, m: U32 at event) -> U32 at sample {\n  cnt~(on~(x, m))\n}\n",
    );
    assert!(!flow(&a, "bad").planned() && flow(&a, "bad").events.len() == 1);
    let f = flow(&a, "top");
    assert_eq!(events(f), (vec!["m < -".into(), "d.bad_0 < -".into()], None));
    assert_eq!(work(&a, f, "n", "cnt"), ["0: 0>value", "d.bad_0: e>-"]);
    assert_eq!(events(flow(&a, "on")).1, None);
    assert_eq!(events(flow(&a, "last")), (vec!["m < -".into(), "_out.on_0 < -".into()], None));
    assert_eq!(work(&a, flow(&a, "last"), "_out.on_0", "on"), ["0: 0>-", "m: m>-"]);
}

/// The texts of what the delay `path` of the flow `top` of `body` reads of
/// events where it is written (`p`, at the event of the input `m` or, of a
/// call below, `e`).
fn saved(body: &str, path: &str) -> Vec<String> {
    let (p, a, text) = analysis(&format!(
        "pub flow top(x: U32 at sample, m: U32 at event, x4: U32 at (sample / 4)) -> U32 at sample {{\n  let _ = m\n  let _ = x4\n{body}\n}}\n"
    ));
    let (f, ast) = (flow(&a, "top"), &p.modules[0].parsed.ast);
    let n = f.nodes.iter().find(|n| n.path == path).unwrap_or_else(|| panic!("no node {path}"));
    n.saved.iter().map(|&e| ast.expr(e).span.text_in(&text).to_string()).collect()
}

/// S-1240, of a delay whose value is `y`: its `p` is at the event of `gen~`
/// below.
fn stored(arg: &str) -> Vec<String> {
    saved(
        &format!(
            "  let p = prev~(^z)\n  let y = prev~({arg})\n  let k: U32 = x + 1\n  let z: U32 = gen~(x)\n  y + k + (p at sample)"
        ),
        "y",
    )
}

#[test]
fn a_delay_reads_the_events_of_what_it_stores_where_it_is_written() {
    assert_eq!(stored("(p at sample) + x"), ["p"]);
    assert_eq!(stored("((p * 2) at sample) + x"), ["p * 2"]);
    assert_eq!(stored("((p * 2) at sample) + (p at sample)"), ["p * 2", "p"]);
    assert_eq!(stored("(m at sample) + x"), ["m"]);
    assert_eq!(stored("(gen~(x) at sample) + x"), ["gen~(x)"]);
    // Not a `^name`, nor a part that reads one.
    assert_eq!(stored("(^z at sample) + x"), no::<String>());
    assert_eq!(stored("((^z * 2) at sample) + (p at sample)"), ["p"]);
    // In the branches of an `if`, its condition, the scrutinees and the guards.
    assert_eq!(stored("if x > 1 { p at sample } else { x }"), ["p"]);
    assert_eq!(stored("if (p at sample) > 1 { m at sample } else { x }"), ["p", "m"]);
    assert_eq!(stored("match (p at sample) { 0 => x, v => v + 1 }"), ["p"]);
    assert_eq!(stored("match~ (p at sample) { 0 => prev~(x), v => v + 1 }"), ["p"]);
    assert_eq!(stored("match x { v if (p at sample) > v => x, v => v + (m at sample) }"), ["p", "m"]);
    assert_eq!(stored("if~ (p at sample) > 3 { prev~(x) } else { m at sample }"), ["p", "m"]);
    assert_eq!(stored("if x > 3 && (p at sample) > 3 { x } else { 0 }"), ["p"]);
    // Not under a condition that reads a `^name`, a binding one chooses, or
    // what an outer one chooses; under one that reads a delay of a `^name`.
    assert_eq!(stored("if ^k > 0 { p at sample } else { x }"), no::<String>());
    assert_eq!(stored("(if ^k > 0 { p at sample } else { x }) + (p at sample)"), ["p"]);
    assert_eq!(stored("match ^k { 0 => p at sample, v => v }"), no::<String>());
    assert_eq!(stored("if ^k > 0 { if x > 1 { p at sample } else { x } } else { x }"), no::<String>());
    assert_eq!(stored("if prev~(^k) > 0 { p at sample } else { x }"), ["p"]);
    // The arms of a `match~` are no conditional positions (§11.3).
    assert_eq!(stored("match~ ^k { 0 => prev~(x), v => v + (p at sample) }"), ["p"]);
}

/// Not in what another place makes: a part of a slower tick, a call and its
/// arguments, the condition of a modifier, and another delay, whose own list
/// it is; but for the `d` of a `vdelay~` in it, of the rest.
#[test]
fn what_another_place_makes_is_not_of_the_list() {
    let none = no::<String>();
    assert_eq!(stored("(p at (sample / 4)) at sample"), none);
    assert_eq!(stored("cnt~(gen~(x)) + (p at sample)"), ["p"]);
    assert_eq!(stored("prev~(x).reset_if~((p at sample) > 3)"), none);
    let nest = "  let p = prev~(^z)\n  let y = prev~(prev~(p at sample) + x)\n  let z = gen~(x)\n  y";
    assert_eq!((saved(nest, "y"), saved(nest, "y.prev_0")), (none.clone(), vec!["p".to_string()]));
    let b4 = "  let p = prev~(^z)\n  let y = prev~(prev~((p at sample) + x) + cnt~(gen~(x)) + (m at sample))\n  let z = gen~(x)\n  y";
    assert_eq!((saved(b4, "y"), saved(b4, "y.prev_0")), (vec!["m".to_string()], vec!["p".to_string()]));
    let vd = "  let p = prev~(^z)\n  let y = prev~(U32.trunc_from(vdelay~(F32.round_from(x), F32.round_from(p at sample), 8)))\n  let z = gen~(x)\n  y";
    assert_eq!((saved(vd, "y"), saved(vd, "y.vdelay_0")), (vec!["p".to_string()], none.clone()));
    let vd = "  let p = prev~(^z)\n  let y = prev~(prev~(vdelay~(F32.round_from(m at sample), F32.round_from(p) at sample, 8)))\n  let z = gen~(x)\n  U32.trunc_from(y)";
    assert_eq!((saved(vd, "y"), saved(vd, "y.prev_0")), (none.clone(), vec!["F32.round_from(p)".to_string()]));
    assert_eq!(saved(vd, "y.vdelay_0"), ["m"]);
    // A delay at `sample / 4`; of an event, none, of which all is of its stage.
    let slow = "  let p = prev~(^z)\n  let y = prev~((p at (sample / 4)) + x4)\n  let z = gen4~(x4)\n  y at sample";
    assert_eq!(saved(slow, "y.prev_0"), ["p"]);
    assert_eq!(saved("  let p = prev~(m) + 1\n  p at sample", "p.prev_0"), none);
    assert_eq!(saved("  let p = delay~(m + m, 3)\n  p at sample", "p.delay_0"), none);
    // A flow with no event.
    let (_, a, _) = analysis(
        "pub flow top(x: U32 at sample, b: U32 at block) -> U32 at sample {\n  let y = prev~(x + b * 2 + ^k)\n  let k = x + 1\n  y + k\n}\n",
    );
    assert!(flow(&a, "top").nodes.iter().all(|n| n.saved.is_empty()) && flow(&a, "top").events.is_empty());
}

/// A node that is the whole value of a `let` at an event is named apart from
/// the field of the value (§11.6, S-1139).
#[test]
fn the_fields_of_a_let_at_an_event() {
    let (_, a, _) = analysis(
        "pub flow top(x: U32 at sample) -> U32 at sample {\n  let d = gen~(x)\n  let v = prev~(d)\n  (d at sample) + (v at sample)\n}\n",
    );
    let names: Vec<&str> = flow(&a, "top").fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["d", "d.gen_0", "v", "v.prev_0", "_poisoned", "_initialized"]);
}
