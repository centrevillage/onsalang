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
/// caller>: <stage of g>><where its result goes>` of each entry, `reset <its
/// place in the chain>` of a reset; of a delay, `g` is the flow of `f`.
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
        Op::Reset { at } => format!("reset {at}"),
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

/// The work of a chain of `.reset_if~` with an event (§11.10): a reset is in
/// the one entry of the event of its condition, first of its ops, the outer
/// first, and of a tick where it was.
#[test]
fn the_resets_of_an_event_are_in_the_entry_of_its_source() {
    let head = "x: U32 at sample, m: U32 at event, k: U32 at event, c: Bool at sample, b: Bool at block, s: U32 at (sample / 4)";
    let own = "flow lp(x: U32 at sample) -> U32 at sample {\n  x + prev~(x)\n}\n";
    let table = |body: &str, path: &str, g: &str| {
        let (_, a, _) = analysis(&format!(
            "{own}pub flow top({head}) -> U32 at sample {{\n  let _ = (m, c, b)\n  let _ = k\n  let _ = s\n  let y = {body}\n  y at sample\n}}\n"
        ));
        work(&a, flow(&a, "top"), path, g)
    };
    let call = |body: &str, g: &str| table(body, if g == "fwd" { "y.fwd_0" } else { "y" }, g);
    assert_eq!(call("lp~(x).reset_if~(m > 0)", "lp"), ["0: 0>value", "m: reset 0"]);
    assert_eq!(call("cnt~(m).reset_if~(m >= 4)", "cnt"), ["0: 0>value", "m: reset 0, e>-"]);
    assert_eq!(call("cnt~(m).reset_if~(k >= 5)", "cnt"), ["0: 0>value", "m: e>-", "k: reset 0"]);
    assert_eq!(call("cnt~(k).reset_if~(m >= 5)", "cnt"), ["0: 0>value", "m: reset 0", "k: e>-"]);
    let two = call("cnt~(m).reset_if~(m >= 5).reset_if~(m >= 7)", "cnt");
    assert_eq!(two, ["0: 0>value", "m: reset 1, reset 0, e>-"]);
    let mixed = call("lp~(x).reset_if~(c).reset_if~(m >= 5)", "lp");
    assert_eq!(mixed, ["0: reset 0, 0>value", "m: reset 1"]);
    let slow = call("cnt~(m).reset_if~(s > 0)", "cnt");
    assert_eq!(slow, ["-2: reset 0", "0: 0>value", "m: e>-"]);
    assert_eq!(call("cnt~(m).reset_if~(b)", "cnt"), ["0: reset 0, 0>value", "m: e>-"]);
    // The call that gives the event, of no tick of its own but `sample`.
    let gives = call("fwd~(m).reset_if~(k > 0)", "fwd");
    assert_eq!(gives, ["0: 0>-", "m: e>event", "k: reset 0"]);
    // Delays, of `sample` and of an event; a condition of no event at the event of the delay.
    let delay = |body: &str| table(body, if body.contains("(x") { "y" } else { "y.prev_0" }, "top");
    assert_eq!(delay("prev~(x, 9).reset_if~(m > 0)"), ["0: 0>value", "m: reset 0"]);
    assert_eq!(delay("prev~(m, 9).reset_if~(m == 0)"), ["m: reset 0, m>value"]);
    assert_eq!(delay("prev~(m, 9).reset_if~(k == 0)"), ["m: m>value", "k: reset 0"]);
    assert_eq!(delay("prev~(m, 9).reset_if~(b).reset_if~(m == 0)"), ["m: reset 1, reset 0, m>value"]);
    assert_eq!(delay("prev~(m, 9).reset_if~(sample_tick() > 3)"), ["m: reset 0, m>value"]);
    assert_eq!(delay("prev~(m, 9).reset_if~(true)"), ["m: reset 0, m>value"]);
    let (_, a, _) = analysis(
        "flow two(a: U32 at event, b: U32 at event) -> U32 at sample {\n  cnt~(a) + cnt~(b)\n}\n\
         pub flow top(m: U32 at event) -> U32 at sample {\n  two~(m, m).reset_if~(m > 3)\n}\n",
    );
    let f = flow(&a, "top");
    assert_eq!(work(&a, f, "_out.two_0", "two"), ["0: 0>value", "m: reset 0, a>-, b>-"]);
}

/// The condition of a delay at an event is read at the event (§11.3): its
/// part of `block` is hoisted, and `sample_tick()` is of that stage.
#[test]
fn the_condition_of_a_delay_at_an_event_is_read_at_it() {
    let top = |cond: &str| {
        let (p, a, text) = analysis(&format!(
            "pub flow top(m: U32 at event, k: U32 at block, f: Bool at block) -> U32 at sample {{\n  let _ = (k, f)\n  let y = prev~(m, 9).reset_if~({cond})\n  y at sample\n}}\n"
        ));
        let (f, ast) = (flow(&a, "top"), &p.modules[0].parsed.ast);
        let hoists = f.hoists.iter().map(|h| ast.expr(h.expr).span.text_in(&text).to_string());
        let time = f.time.keys().map(|&s| stage(f, s)).collect::<Vec<_>>();
        (hoists.collect::<Vec<_>>(), time)
    };
    assert_eq!(top("k * 2 > 3 && m > 1"), (vec!["k * 2 > 3".to_string()], no()));
    assert_eq!(top("f && 100 / k > m"), (vec!["100 / k".to_string()], no()));
    assert_eq!(top("sample_tick() > 3 && m > 1"), (no(), vec!["m".to_string()]));
    assert_eq!(top("sample_tick() > 3"), (no(), vec!["m".to_string()]));
}

/// S-1250: the flags of a delay whose reset an event may tick between its
/// place and its store: one given out in the function of its stage by a call
/// after it in the text (after its whole chain, the conditions of it too), or
/// ticked by such a one; not of an input, of a call before it, in its own
/// conditions, or of another stage, nor of a periodic condition or its own.
#[test]
fn the_flags_of_a_delay_a_late_event_resets() {
    let fields = |body: &str| {
        let (_, a, _) = analysis(&format!(
            "flow on(x: U32 at sample) -> U32 at event {{\n  if x > 1 {{ Some(x) }} else {{ None }}\n}}\n\
             pub flow top(x: U32 at sample, x4: U32 at (sample / 4), m: U32 at event, k: U32 at event, c: Bool at sample) -> U32 at sample {{\n  let _ = (x, c)\n  let _ = x4\n  let _ = m\n  let _ = k\n{body}\n}}\n"
        ));
        let names = flow(&a, "top").fields.iter().map(|f| f.name.clone());
        names.filter(|n| n.contains("._open") || n.contains("._back")).collect::<Vec<String>>()
    };
    // `y` on the event of a call `d` below it (or of `f`, which that ticks).
    let below = |y: &str| fields(&format!("  let e = prev~(^d)\n  let y = {y}\n  let d: U32 = gen~(x)\n  y"));
    assert_eq!(below("prev~(x).reset_if~(e > 3)"), ["y._open", "y._back_0"]);
    let chain = "delay~(x, 2).reset_if~(e > 3).reset_if~(c).reset_if~(m > 3).when~(c).reset_if~(e > 5)";
    assert_eq!(below(chain), ["y._open", "y._back_0", "y._back_4"]);
    assert_eq!(below("prev~(prev~(x, 9).reset_if~(e > 3), 7)"), ["y.prev_0._open", "y.prev_0._back_0"]);
    let par = "(par~ i in 0..<2 { prev~(x).reset_if~(e > i) })[1]";
    assert_eq!(below(par), no::<String>(), "the fields of a replica are of its own struct");
    let mid = "  let e = prev~(^f)\n  let y = prev~(x).reset_if~(e > 3)\n  let d = gen~(x)\n  let f = fwd~(d)\n  y";
    assert_eq!(fields(mid), ["y._open", "y._back_0"]);
    let of =
        "  let e = prev~(^f)\n  let d = gen~(x)\n  let y = prev~(d).reset_if~(e > 3)\n  let f = fwd~(d)\n  y at sample";
    assert_eq!(fields(of), ["y.prev_0._open", "y.prev_0._back_0"]);
    let slow = "  let e = prev~(^d)\n  let y = prev~(x4).reset_if~(e > 3)\n  let d = gen4~(x4)\n  y at sample";
    assert_eq!(fields(slow), ["y.prev_0._open", "y.prev_0._back_0"]);
    // In the chain and in the head of the call that gives it out (read before its work).
    for d in [
        "gen~(x).reset_if~(prev~(x, 9).reset_if~(e >= 3) > 7)",
        "gen~(x).when~(prev~(x, 9).reset_if~(e >= 3) > 7)",
        "gen~(3).up~(2).when~(c).reset_if~(prev~(x, 9).reset_if~(e >= 3) > 7)",
        "gen~(prev~(x, 9).reset_if~(e >= 3))",
        "gen~(x + prev~(x, 9).reset_if~(e >= 3)).when~(c)",
        "gen~(x).reset_if~(prev~(x > 3).reset_if~(e >= 3))",
    ] {
        let d = format!("  let e = prev~(^d)\n  let d: U32 = {d}\n  d at sample");
        assert_eq!(fields(&d), ["d.prev_0._open", "d.prev_0._back_0"], "{d}");
    }
    // Before it, of an input (and what it ticks), of another stage, or in its own conditions.
    for body in [
        "  let d = gen~(x)\n  let y = prev~(x).reset_if~(d > 3)\n  y",
        "  let d = gen~(x)\n  let f = fwd~(d)\n  let y = prev~(x).reset_if~(f > 3)\n  y",
        "  prev~(x).reset_if~(gen~(x) > 3)",
        "  prev~(x).reset_if~(c).reset_if~(gen~(x) > 3)",
        "  let y = prev~(x).reset_if~(m > 3)\n  y",
        "  let y = prev~(m).reset_if~(k > 3)\n  y at sample",
        "  let e = prev~(^f)\n  let y = prev~(x).reset_if~(e > 3)\n  let f = fwd~(m)\n  y",
        "  let e = prev~(^f)\n  let y = prev~(k).reset_if~(e > 3)\n  let f = fwd~(m)\n  y at sample",
        "  let e = prev~(^d)\n  let y = prev~(x).reset_if~(e > 3)\n  let d = gen4~(x4)\n  y",
        "  let e = prev~(^d)\n  let y = prev~(x4).reset_if~(e > 3)\n  let d = gen~(x)\n  y at sample",
        "  let e = prev~(^d)\n  let y = prev~(e).reset_if~(e > 3)\n  let d = gen~(x)\n  y at sample",
        "  let e = prev~(^d)\n  let d: U32 = gen~(3).reset_if~(prev~(x, 9).reset_if~(e >= 3) > 7).up~(2).down~(2)\n  d at sample",
        "  let y = prev~(m).reset_if~(m > 3)\n  y at sample",
        "  let y = prev~(x).reset_if~(c)\n  y",
        "  let e = prev~(^d)\n  let y = cnt~(m).reset_if~(e > 3)\n  let d = gen~(x)\n  y",
    ] {
        assert_eq!(fields(body), no::<String>(), "{body}");
    }
    // In a replica, of the call after it there alone.
    let of = |body: &str| {
        let (_, a, _) = analysis(&format!(
            "pub flow top(x: U32 at sample, m: U32 at event) -> U32 at sample {{\n  let _ = m\n{body}\n}}\n"
        ));
        let f = flow(&a, "top");
        f.nodes.iter().filter(|n| !n.late.is_empty()).map(|n| n.path.clone()).collect::<Vec<String>>()
    };
    let par = |y: &str| format!("  let y = par~ i in 0..<2 {{ {y} }}");
    let below = format!("  let e = prev~(^d)\n{}\n  let d = gen~(x)\n  y[1]", par("prev~(x + i).reset_if~(e > 3)"));
    assert_eq!(of(&below), ["y.prev_0"]);
    let input = format!("{}\n  y[1]", par("prev~(x + i).reset_if~(m > 3)"));
    assert_eq!(of(&input), no::<String>());
    let own = format!("{}\n  y[1]", par("prev~(x + i).reset_if~(gen~(x + i) > 3)"));
    assert_eq!(of(&own), no::<String>());
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

/// The most events a run of the stage that gives them out gives (§11.9,
/// §11.11, `FlowInfo::burst`), and that stage, of the flow `top` whose output
/// is the events `d`: of the event of an `.up~(N)`, the N runs of its maker
/// at `sample`, N >> k of one at `sample / 2^k` (one once of a stage slower
/// than the `sample` around); of those of a callee, of each run; one of the
/// stage of an event, of a `.down~` and of a guard.
#[test]
fn the_most_events_of_a_run() {
    let most = |d: &str| {
        let (_, a, _) = analysis(&format!(
            "flow tick2() -> U32 at event {{\n  Some(1) at (sample / 2)\n}}\n\
             flow two() -> U32 at event {{\n  let d = gen~(3).up~(2)\n  Some(d)\n}}\n\
             flow of(d: U32 at event) -> U32 at event {{\n  let a = fwd~(d)\n  Some(a)\n}}\n\
             pub flow top(m: U32 at event, c: Bool at sample) -> U32 at event {{\n  let _ = (m, c)\n  let d = {d}\n  Some(d)\n}}\n"
        ));
        let f = flow(&a, "top");
        (stage(f, f.emit.expect("a stage")), f.burst)
    };
    for (d, at, n) in [
        ("gen~(3)", "0", 1),
        ("gen~(3).up~(2)", "0", 2),
        ("gen~(3).up~(4).up~(2)", "0", 8),
        ("tick2~()", "-1", 1),
        ("tick2~().up~(2)", "0", 1),
        ("tick2~().up~(4)", "0", 2),
        ("tick2~().up~(4).up~(2)", "0", 4),
        ("tick2~().up~(2).up~(2)", "0", 2),
        ("gen4~(3).up~(2)", "-1", 1),
        ("gen4~(3).up~(8)", "0", 2),
        ("gen~(3).up~(2).down~(2)", "-1", 2),
        ("gen~(3).up~(2).down~(4)", "-2", 2),
        ("gen~(3).up~(4).down~(2)", "-1", 4),
        ("gen~(3).up~(2).down~(4).up~(2)", "-1", 2),
        ("gen~(3).up~(2).down~(2).up~(4)", "0", 4),
        ("tick2~().up~(4).down~(2)", "-1", 2),
        ("gen~(3).down~(2)", "-1", 1),
        ("gen~(3).when~(c)", "0", 1),
        ("gen~(3).up~(2).when~(c)", "0", 2),
        ("gen~(3).when~(c).up~(2)", "0", 2),
        // Each run may be at its tick of the ticks it ran: two of the eight at most do.
        ("tick2~().when~(m > 1).up~(8)", "0", 8),
        ("two~()", "0", 2),
        ("two~().up~(4)", "0", 8),
        ("two~().down~(2)", "-1", 2),
        ("two~().when~(c)", "0", 2),
        ("fwd~(two~())", "0", 2),
        ("of~(fwd~(two~().up~(2)))", "0", 4),
        ("m", "m", 1),
        ("fwd~(m).up~(4)", "m", 1),
        ("of~(m).up~(4)", "m", 1),
        ("of~(fwd~(m).up~(4)).when~(c)", "m", 1),
    ] {
        assert_eq!(most(d), (at.to_string(), n), "{d}");
    }
    // Another stage of the flow gives several, and is not on the way to its output.
    let (_, a, _) =
        analysis("pub flow top(m: U32 at event) -> U32 at event {\n  let _ = gen~(3).up~(2)\n  Some(m)\n}\n");
    assert_eq!(flow(&a, "top").burst, 1);
    // Past 2^24 (E0808, S-1089) the count stops at the maximum.
    let up = "let d = gen~(3).up~(16777216)\n  Some(d)\n}\n";
    let src = format!(
        "{HEAD}flow one() -> U32 at event {{\n  {up}pub flow top() -> U32 at event {{\n  let d = one~().up~(16777216)\n  Some(d)\n}}\n"
    );
    let a = analyze(&pkg(&[("main", &src)]));
    assert!(!a.diagnostics.is_empty() && a.diagnostics.iter().all(|d| d.code == onsa_diag::Code::E0808));
    assert_eq!(flow(&a, "one").burst, 1 << 24);
    assert_eq!(flow(&a, "top").burst, u32::MAX);
}

/// The stage that ticks the events of a maker under a guard and an `.up~`
/// (its stage W, the `sample` of the caller), which gives them out in a named
/// flow and takes the time of their stage (§11.4).
#[test]
fn the_events_of_a_chain_are_ticked_by_the_stage_of_its_runs() {
    let of = |d: &str| {
        let (_, a, _) = analysis(&format!(
            "flow tke(e: U32 at event) -> U32 at event {{\n  Some(sample_tick() + e)\n}}\n\
             pub flow top(c: Bool at sample) -> U32 at event {{\n  let _ = c\n  let d = {d}\n  let t = tke~(d)\n  Some(t)\n}}\n"
        ));
        let f = flow(&a, "top");
        let time: Vec<String> = f.time.iter().map(|(&s, w)| format!("{} {w:?}", stage(f, s))).collect();
        (events(f), time)
    };
    for (d, by) in [
        ("gen~(3).when~(c)", "0"),
        ("gen~(3).up~(2)", "0"),
        ("gen~(3).up~(2).down~(4)", "-2"),
        ("gen4~(3).up~(2)", "-1"),
    ] {
        let made = vec![format!("d.gen_0! < {by}"), "t.tke_0! < d.gen_0".to_string()];
        let (found, time) = of(d);
        let found = (found.0.into_iter().map(|s| s.replace("gen4_0", "gen_0")).collect::<Vec<_>>(), found.1);
        assert_eq!(found, (made, Some(by.to_string())), "{d}");
        assert_eq!(time.len(), 2, "{d}: {time:?}");
        assert!(time.contains(&format!("{by} One")), "{d}: {time:?}");
    }
}

/// The text of the form not run of the flow `top` of `src`, and whether it
/// has its tables, with the E0200 of it alone.
fn form(src: &str) -> Option<String> {
    let (_, a, text) = analysis(src);
    let f = flow(&a, "top");
    assert_eq!(f.event_form.is_none(), f.planned(), "{src}");
    assert_eq!(f.event_gate().map(|d| d.span), f.event_form, "{src}");
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

/// A chain of any modifiers of a call of a flow with an event port, of a flow
/// with none and of a delay runs, with a condition at an event in it
/// (§11.10): a `.when~`, a ratio and a `.reset_if~` in any order.
#[test]
fn the_chains_run() {
    for run in [
        "  cnt~(m).reset_if~(c)",
        "  let d = gen~(x).when~(c)\n  d at sample",
        "  let q = m > 3\n  own~(x).reset_if~(q)",
        "  let d = prev~(m).reset_if~(m > 3)\n  d at sample",
        "  cnt~(m).reset_if~(m > 3).reset_if~(c)",
        "  own~(x).when~(c).reset_if~(m > 3)",
        "  own~(x).reset_if~(m > 3).when~(m > 4)",
        "  prev~(x).reset_if~(m > 3).when~(c)",
        "  cnt~(m).reset_if~(m > 3).when~(c)",
        "  own~(x).when~(c) + own~(x).reset_if~(c)",
        "  let q = m > 3\n  own~(x).when~(q at sample) + prev~(x).reset_if~(q at sample)",
        "  (own~(3).when~(m > 3).down~(2) at sample) + cnt~(m).when~(c)",
        "  cnt~(m).down~(2) at sample",
        "  cnt~(m).up~(2).down~(2).reset_if~(m > 3).when~(m > 4)",
        // The level of an event.
        "  own~(x).when~(m > 3).reset_if~(c).when~(m < 9)",
        "  own~(x).reset_if~(c).when~(m > 3)",
        "  prev~(x).when~(m > 3)",
        "  let q = m > 3\n  prev~(prev~(x).when~(q))",
        "  own~(gen~(x) at sample).when~(gen~(x) > 3 && c)",
        "  own~(3).down~(2).when~(m > 3) at sample",
        "  own~(x).when~(c).reset_if~(m > 3).when~(m > 4)",
        "  cnt~(m).when~(m > 3)",
    ] {
        assert_eq!(forms(run), None, "{run}");
    }
}

/// The forms in a `par~`, a `par`, an `if~` and a `match~` (the conditions, the
/// scrutinee and the guards too): a call of a flow with an event port, a
/// delay at an event, a condition at one and a computed part of one run.
#[test]
fn the_replicas_and_the_arms() {
    for run in [
        "  let y = par~ i in 0..<2 { cnt~(m) + i }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { cnt~(gen~(x + i)) }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { (prev~(m) at sample) + prev~(x) + i }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { ((m * 2) at sample) + prev~(x) + i }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { own~(x).reset_if~(m > 3) + i }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { cnt~(m).reset_if~(gen~(x + i) > 3) }\n  y[0] + y[1]",
        "  let y = par~ i in 0..<2 { own~(x).when~(m > 3) + i }\n  y[0]",
        "  let y = par i in 0..<2 { ((m * 2) at sample) + x + i }\n  y[0] + y[1]",
        "  prev~((par i in 0..<2 { ((m * 2) at sample) + x + i })[1])",
        "  if~ c { cnt~(gen~(x)) } else { prev~(x) }",
        "  if~ c { own~(x).when~(m > 3) } else { x }",
        "  if~ ((m * 2) at sample) > x { prev~(x) } else { x }",
        "  match~ cnt~(m) { 0 => prev~(x), v => v }",
        "  let y = match~ m { v if m > 3 => prev~(v), v => v }\n  y at sample",
        "  match~ x { 0 => prev~(x).when~(m > 3), v => cnt~(m).reset_if~(m > 3) + v }",
    ] {
        assert_eq!(forms(run), None, "{run}");
    }
    // A chain in them too.
    for run in [
        "  let y = par~ i in 0..<2 { cnt~(m).when~(c) + i }\n  y[0]",
        "  let y = par~ i in 0..<2 { own~(x + i).when~(c).reset_if~(m > 3) }\n  y[0]",
        "  let y = par~ i in 0..<2 { par~ j in 0..<2 { cnt~(gen~(x)).down~(2) at sample } }\n  y[0][0]",
        "  if~ c { own~(3).when~(m > 3).down~(2) at sample } else { prev~(x) }",
        "  if~ cnt~(m).when~(c) > 3 { prev~(x) } else { x }",
        "  match~ x { 0 => prev~(x).when~(c).reset_if~(m > 3), v => v }",
    ] {
        assert_eq!(forms(run), None, "{run}");
    }
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
        "flow bad(x: U32 at sample, m: U32 at event) -> U32 at event {\n  let _ = (x, m)\n  let d = fwd~(prev~(^d))\n  Some(d)\n}\n\
         pub flow top(x: U32 at sample, m: U32 at event) -> U32 at sample {\n  let d = bad~(x, m)\n  let n = cnt~(d)\n  n + (prev~(d) at sample)\n}\n\
         pub flow on(x: U32 at sample, m: U32 at event) -> U32 at event {\n  let d = bad~(x, m)\n  Some(d)\n}\n\
         pub flow last(x: U32 at sample, m: U32 at event) -> U32 at sample {\n  cnt~(on~(x, m))\n}\n",
    );
    assert!(!flow(&a, "bad").planned() && flow(&a, "bad").events.len() == 2);
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
    // Under a condition that reads a `^name` or a binding one chooses too
    // (S-1249), a part of an event with no `^` of its own as well.
    assert_eq!(stored("if ^k > 0 { p at sample } else { x }"), ["p"]);
    assert_eq!(stored("if ^k > (p at sample) { p at sample } else { x }"), ["p", "p"]);
    assert_eq!(stored("match ^k { 0 => p at sample, v => v }"), ["p"]);
    let g4 = "  let p = prev~(^z)\n  let y = prev~(if ^h > 0 { (p * 2) at sample } else { x })\n  let h = U32.trunc_from(sample_rate())\n  let z = gen~(x)\n  y";
    assert_eq!(saved(g4, "y"), ["p * 2"]);
    assert_eq!(stored("match~ x { v if v > ^k => prev~(x), v if v > (p at sample) => v, _ => 0 }"), ["p"]);
    assert_eq!(stored("if~ ^k > x { prev~(x) } else if (p at sample) > 3 { 1 } else { m at sample }"), ["p", "m"]);
    assert_eq!(stored("if x > 3 || (^k > 3 && (p at sample) > 3) { x } else { 0 }"), ["p"]);
    // A binding one chooses, of a `match` with no `~` too, is one (S-1249), and so
    // is one that reads it to choose; not the parts beside it.
    let plain = |arms: &str| {
        let body = format!(
            "  let p = prev~(^z)\n  let n = U32.trunc_from(sample_rate())\n  let y = prev~(match {arms})\n  let h: Option[U32] = if sample_rate() > 1.0 {{ Some(n) }} else {{ None }}\n  let z = gen~(x)\n  y"
        );
        saved(&body, "y")
    };
    assert_eq!(plain("^h { Some(v) => (p * v) at sample, None => (p * 2) at sample }"), ["p * 2"]);
    assert_eq!(plain("^h { Some(v) => match v { 0 => p at sample, w => (p * w) at sample }, None => x }"), ["p"]);
    let guard =
        "n { v if v > 9 => (p * v) at sample, v if Some(v) == ^h => x, v => ((p + v) at sample) + (m at sample) }";
    assert_eq!(plain(guard), ["m"]);
    assert_eq!(plain("n { 4 => if ^h == Some(1) { x } else { 0 }, v => (p * v) at sample }"), ["p * v"]);
    // The arms of a `match~` are no conditional positions (§11.3).
    assert_eq!(stored("match~ ^k { 0 => prev~(x), v => v + (p at sample) }"), ["p"]);
}

/// S-1249: the parts of a slower tick of the end of the stage, which the
/// delay does not read into, each with a list of its own by the same rule; no
/// other part has one.
#[test]
fn a_part_of_the_end_of_a_slower_tick_reads_the_events_where_it_is_written() {
    let parts = |arg: &str| {
        let (p, a, text) = analysis(&format!(
            "pub flow top(x: U32 at sample, x4: U32 at (sample / 4), b: U32 at block) -> U32 at sample {{\n  let p = prev~(^z)\n  let y = prev~({arg})\n  let k = x4 + 1\n  let z = gen4~(x4)\n  y + (k at sample) + b\n}}\n"
        ));
        let (f, ast) = (flow(&a, "top"), &p.modules[0].parsed.ast);
        let text = |e| ast.expr(e).span.text_in(&text).to_string();
        let y = f.nodes.iter().find(|n| n.path == "y").expect("the delay").saved.iter().map(|&e| text(e)).collect();
        let parts = f.hoists.iter().map(|h| (text(h.expr), h.saved.iter().map(|&e| text(e)).collect()));
        (y, parts.filter(|h: &(String, Vec<String>)| !h.1.is_empty()).collect())
    };
    let list =
        |of: &str, saved: &[&str]| vec![(of.to_string(), saved.iter().map(|s| s.to_string()).collect::<Vec<_>>())];
    let none = no::<String>();
    let f1 = "((p at (sample / 4)) * 2 + ^k) at sample";
    assert_eq!(parts(f1), (none.clone(), list("(p at (sample / 4)) * 2 + ^k", &["p"])));
    let both = "(((p at (sample / 4)) * 2 + ^k) at sample) + (p at sample)";
    assert_eq!(parts(both), (vec!["p".into()], list("(p at (sample / 4)) * 2 + ^k", &["p"])));
    let part = "(((p * 2) at (sample / 4)) + ((^z + 1) at (sample / 4)) + ^k) at sample";
    let of = "((p * 2) at (sample / 4)) + ((^z + 1) at (sample / 4)) + ^k";
    assert_eq!(parts(part), (none.clone(), list(of, &["p * 2"])));
    // Evaluated where it is written.
    assert_eq!(parts("((p at (sample / 4)) * 2 + x4) at sample"), (none, Vec::new()));
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
