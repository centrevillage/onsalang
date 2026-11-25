//! The order of the stores of `tick` (§11.4, W7-07) and the time of the
//! lowering of a flow, which grows with its state linearly (R-498).

use std::time::{Duration, Instant};

/// The `tick` of the flow `name` of `src`, as in the dump of the Core.
fn tick(src: &str, name: &str) -> String {
    crate::dump::dump_item(&crate::tests::core(src), &format!("t.{name}.tick"))
}

/// The place of `what` in `text`, which holds it once.
fn at(text: &str, what: &str) -> usize {
    assert_eq!(text.matches(what).count(), 1, "`{what}` once in:\n{text}");
    text.find(what).unwrap_or_default()
}

/// §11.4: the inner delay of `prev~(prev~(x))` is read in the store of the
/// outer one, before its own store, so the outer one keeps the inner one's
/// output of this tick (x[n-2]), not what the inner one stores now.
#[test]
fn a_delay_inside_a_delay_is_read_in_the_outer_store_before_its_own_store() {
    let t = tick("pub flow f(x: F32 at sample) -> F32 at sample { prev~(prev~(x)) }", "f");
    let (out, outer, inner_read, inner) = (at(&t, "let __out"), at(&t, "s.0 = "), at(&t, "= s.1\n"), at(&t, "s.1 = x"));
    assert!(out < outer && outer < inner_read && inner_read < inner, "{t}");
}

/// R-03: a replica of a `par~` stores in a loop of its own after the output,
/// so the `^y` its stored value reads is the `y` of this tick; the loop that
/// computes the replicas stores nothing.
#[test]
fn the_replicas_of_a_par_store_in_a_loop_after_the_output() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {
  let a = par~ i in 0 ..< 2 { prev~(x * F32.round_from(i) + ^y) }
  let y = a[0] + x
  y
}";
    let t = tick(src, "f");
    let (out, store) = (at(&t, "let __out"), at(&t, "s.0[i].0 = "));
    assert!(out < store && t[out..store].contains("for i in"), "{t}");
    assert_eq!(t.matches("for i in").count(), 2, "{t}");
}

/// A `par~` whose replicas are instances alone stores nothing in `tick` (an
/// instance stores in its own), so no loop is made for it.
#[test]
fn a_par_of_instances_alone_has_no_loop_of_stores() {
    let src = "pub flow lp(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample) -> F32 at sample {
  let a = par~ i in 0 ..< 2 { lp~(x) }
  a[0] + a[1]
}";
    let t = tick(src, "f");
    assert_eq!(t.matches("for i in").count(), 1, "{t}");
    assert!(at(&t, "lp.tick") < at(&t, "let __out"), "{t}");
}

/// A flow of `n` pairs of `let`s, each pair a `let` the state keeps and a
/// `let` with a `prev~` and a `delay~` (the form of R-498): about 4 `n`
/// fields of the state.
fn wide(n: usize) -> String {
    let mut src = String::from("pub flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {\n");
    let mut prev = "x".to_string();
    for k in 0..n {
        src += &format!("  let a{k}: F32 = p * {k}.5\n  let t{k} = {prev} + prev~(x * a{k}) + delay~(x, 2)\n");
        prev = format!("t{k}");
    }
    src + &format!("  {prev}\n}}\n")
}

/// The time of the lowering alone (not the analysis, not `dump`) of
/// [`wide`] of `n`: the least of three, apart from a pause of the machine.
fn lowering_time(n: usize) -> Duration {
    let (_, pkg) = crate::tests::package(&wide(n));
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.is_empty(), "{} diagnostics", a.diagnostics.len());
    let once = |_| {
        let start = Instant::now();
        let m = crate::lower(&pkg, &a);
        let took = start.elapsed();
        assert!(m.is_ok(), "the lowering failed");
        took
    };
    (0..3).map(once).min().unwrap_or_default()
}

/// Four times the state takes about four times as long (linear), not
/// sixteen (the square of R-498): less than eight, apart from the speed of
/// the machine.
#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_the_lowering_of_a_flow_is_linear_in_its_state() {
    let (small, large) = (lowering_time(1000), lowering_time(4000));
    let ratio = large.as_secs_f64() / small.as_secs_f64();
    println!("1000: {small:?}, 4000: {large:?}, ratio {ratio:.2}");
    assert!(ratio < 8.0, "1000: {small:?}, 4000: {large:?}, ratio {ratio:.2}");
}

/// §11.5, S-1094: an `if~` evaluates its conditions to the one that holds,
/// then every branch in the order of the text (each instance goes on), then
/// chooses; in `ctl`, the field of a later condition is written while the
/// one before it is false, that of a branch with no condition (§11.3).
#[test]
fn an_if_tilde_evaluates_its_conditions_then_every_branch() {
    let src = "pub flow acc(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample, p: F32 at block, q: F32 at block) -> F32 at sample {
  if~ p > 1.0 { acc~(x) } else if q * 2.0 > 1.0 { acc~(x * (q + 1.0)) } else { x }
}";
    let t = tick(src, "f");
    let (taken, first, second, choice) =
        (at(&t, "let __taken"), at(&t, "acc.tick(inout s.0"), at(&t, "acc.tick(inout s.1"), at(&t, "(__taken == 0"));
    assert!(taken < first && first < second && second < choice, "{t}");
    let ctl = crate::dump::dump_item(&crate::tests::core(src), "t.f.ctl");
    let (c1, guard, c2, body) = (at(&ctl, "p@4.0 > 1.0"), at(&ctl, "if (!s."), at(&ctl, "* 2.0"), at(&ctl, "+ 1.0"));
    assert!(c1 < guard && guard < c2 && c2 < body, "{ctl}");
}

/// §11.5, S-1094 (1): a `match~` chooses its arm first (the scrutinee, then
/// the pattern and the guard of each arm while none is taken), then
/// evaluates every arm body in the order of the text (each instance goes
/// on), then takes the value of the arm chosen.
#[test]
fn a_match_tilde_chooses_its_arm_then_evaluates_every_arm_body() {
    let src = "pub flow acc(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {
  match~ k { 0 => acc~(x), n if n > 5 => acc~(x * 2.0), _ => x }
}";
    let t = tick(src, "f");
    let (arm, first, second, body0, body1, choice) = (
        at(&t, "let __arm: U32 = 3:U32"),
        at(&t, "if ((__arm == 3:U32) && (k == 0:U32))"),
        at(&t, "if (n > 5:U32)"),
        at(&t, "acc.tick(inout s.0"),
        at(&t, "acc.tick(inout s.1"),
        at(&t, "if (__arm == 0:U32)"),
    );
    assert!(arm < first && first < second && second < body0 && body0 < body1 && body1 < choice, "{t}");
}

/// S-1131: a binding read at `block` has a place in `ctl`, declared at its
/// head; the arm of a node is chosen before it, once in a scope however
/// many nodes of the arm read it, and the arms before it with it.
#[test]
fn the_bindings_read_at_block_have_places_and_an_arm_is_chosen_once() {
    let src = "pub flow lp(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }
pub flow f(x: F32 at sample, o: Option[F32] at block, n: I32 at block) -> F32 at sample {
  match~ o {
    Some(v) if n > 0 => lp~(x, v + 1.0),
    Some(w) => lp~(x, w) + lp~(x, w * 2.0) + lp~(x, w * 3.0),
    None => x,
  }
}";
    let ctl = crate::dump::dump_item(&crate::tests::core(src), "t.f.ctl");
    let (v, w, first) =
        (at(&ctl, "let __bind.v: F32 = zeroed"), at(&ctl, "let __bind.w: F32 = zeroed"), at(&ctl, "s.0 = p.0"));
    assert!(v < first && w < first, "{ctl}");
    // One choice of all the arms, with the field of the guard (S-1233: the
    // walk of the `match~` at its place chooses before the work of its arms).
    assert_eq!(ctl.matches(": U32 = 3:U32").count(), 1, "{ctl}");
    assert_eq!(ctl.matches("__bind.v = v").count(), 1, "{ctl}");
    assert_eq!(ctl.matches("__bind.w = w").count(), 1, "{ctl}");
    let (w_set, lp1) = (at(&ctl, "__bind.w = w"), at(&ctl, "Params { g: __bind.w }"));
    assert!(w_set < lp1, "{ctl}");
}

/// S-1244, S-1245: a `match~` that a `^name` chooses is chosen at the end of
/// the stage alone: the calls in its arms are where the delay is written, and
/// its binding has its value at the stage of a slower delay in an arm too.
#[test]
fn a_match_tilde_a_past_value_chooses_is_chosen_at_the_end_and_its_calls_are_where_they_are_written() {
    let src = "pub flow acc(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample, o: Option[F32] at block) -> F32 at sample {
  let y = prev~(match~ ^v { Some(b) => acc~(x) + ((prev~(b at (sample / 4))) at sample), None => acc~(x * 2.0) })
  let v: Option[F32] = o
  y + x
}";
    let t = tick(src, "f");
    let (call0, call1, read, choice) =
        (at(&t, "acc.tick(inout s.2"), at(&t, "acc.tick(inout s.4"), at(&t, "= s.1\n"), at(&t, "let __arm: U32"));
    assert!(call0 < call1 && call1 < read && read < choice, "{t}");
    let slow = crate::dump::dump_item(&crate::tests::core(src), "t.f.tick_4");
    let (bound, store) = (at(&slow, "__bind.b = b\n"), at(&slow, "= __bind.b\n"));
    assert!(bound < store, "{slow}");
}

/// §11.4, S-1131: a binding read in the first argument of a delay in a
/// `par~` has a place of each replica, which the stores at the end of
/// `tick` read.
#[test]
fn a_binding_a_delay_stores_in_a_par_has_a_place_of_each_replica() {
    let src = "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {
  (par~ i in 0..<2 { match~ k { 0 => prev~(x), n => prev~(F32.round_from(n)) } })[0]
}";
    let t = tick(src, "f");
    let (place, write, store) = (
        at(&t, "let __bind.n: [U32; 2] = zeroed:[U32; 2]"),
        at(&t, "__bind.n[i] = n"),
        at(&t, "s.0[i].1 = round.U32.F32(__bind.n[i])"),
    );
    // The store is in the loop of the stores after the output.
    let stores = t.rfind("for i in").unwrap_or_default();
    assert!(place < write && write < stores && stores < store, "{t}");
}

/// §11.9: the body of `.down~(N)` reads a `sample_rate()` of 1/N, divided
/// at each boundary, the outermost first (as each part runs the one it
/// wraps), not once by the product, which rounds otherwise below the normal
/// floats; a call with no modifier passes the rate as it is. The value of
/// the chain is the output of its head, read at the tick of its frame.
#[test]
fn the_rate_of_a_child_under_down_is_divided_at_each_boundary() {
    let src = "flow rate() -> F32 at sample { sample_rate() }
pub flow f() -> F32 at sample {
  (rate~().down~(2).down~(4) at sample) + rate~()
}";
    let m = crate::tests::core(src);
    let init = crate::dump::dump_item(&m, "t.f.init");
    assert!(init.contains("t.rate.init(t.rate.Config {}, ((sample_rate / 4.0:F32) / 2.0:F32))"), "{init}");
    assert!(init.contains("t.rate.init(t.rate.Config {}, sample_rate)"), "{init}");
    let slow = crate::dump::dump_item(&m, "t.f.tick_8");
    assert!(slow.contains("t.rate.tick(inout s.1)"), "{slow}");
}

/// The flows of the tests of events, and `body` the rest of the module.
fn events(body: &str) -> String {
    let flows = "flow gen(x: U32 at sample) -> U32 at event { if x % 3 != 0 { Some(x) } else { None } }
flow fwd(m: U32 at event) -> U32 at event { Some(m) }
flow part(x: U32 at sample, c: U32 at event) -> U32 at event { let _ = 100 / c\n  Some(x) }
flow both(a: U32 at event, b: U32 at event) -> U32 at event { let _ = b\n  Some(a) }
flow cnt(m: U32 at event) -> U32 at sample { let n = prev~(^n) + m\n  n }
flow stamp(m: U32 at event) -> U32 at event { Some(m + sample_tick()) }
";
    format!("{flows}{body}")
}

/// The function `t.<name>` of [`events`] of `body`, as in the dump of the Core.
fn event_fn(body: &str, name: &str) -> String {
    crate::dump::dump_item(&crate::tests::core(&events(body)), &format!("t.{name}"))
}

/// That `text` holds each of `parts` once, in their order.
fn in_order(text: &str, parts: &[&str]) {
    let places: Vec<usize> = parts.iter().map(|p| at(text, p)).collect();
    assert!(places.is_sorted(), "{parts:?} at {places:?} in:\n{text}");
}

/// §11.11, S-1234, S-1235: the stage of the events of a call is run once,
/// where the call is written, after its run; a receiver above it has run by
/// then, and its own tick is in that stage, as what the delay there stores.
#[test]
fn the_stage_of_an_event_runs_after_the_run_of_the_call_that_gives_it() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let h = cnt~(prev~(^d))
  let d = gen~(x)
  h + (d at sample)
}";
    let t = event_fn(f, "f.tick");
    in_order(
        &t,
        &["t.cnt.tick(inout", "let __event", "t.gen.tick(inout", "Some =>", "t.f.ev_0(inout s, payload(", "let __out"],
    );
    let e = event_fn(f, "f.ev_0");
    in_order(&e, &["ev: U32) -> ()", "t.cnt.ev_0(inout", "let d: U32 = ev\n", "= d\n}"]);
    assert!(!e.contains("t.gen."), "{e}");
}

/// The call that gives an event and takes one of it (S-1235): at its event
/// its arguments, its tick, then the event as its value.
#[test]
fn a_call_that_takes_its_own_event_ticks_before_it_is_read() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let d = part~(x, prev~(^d))
  d at sample
}";
    let t = event_fn(f, "f.tick");
    in_order(&t, &["t.part.tick(inout", "t.f.ev_0("]);
    assert!(!t.contains("t.part.ev_0"), "{t}");
    in_order(&event_fn(f, "f.ev_0"), &["t.part.ev_0(inout", "d.prev_0: U32 = s.", "    ev\n", "= d\n}"]);
}

/// S-1236: one event of two inputs is a tick of each, in their order, and
/// what the first gives is done before the second.
#[test]
fn the_events_of_the_first_tick_are_before_the_second() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let m = gen~(x)
  let e = both~(m, m)
  e at sample
}";
    in_order(&event_fn(f, "f.ev_0"), &["t.both.ev_0(inout", "t.f.ev_1(inout s, payload(", "t.both.ev_1(inout"]);
}

/// An output that is the event of a call goes through the functions from the
/// stage that makes it to the one the caller runs, after the stores of each.
#[test]
fn the_functions_on_the_way_give_the_event_of_the_output() {
    let f = "pub flow line(x: U32 at sample) -> U32 at event {
  let a = gen~(x)
  let n = prev~(^n) + a
  let b = fwd~(n)
  Some(b)
}
pub flow f(x: U32 at sample) -> U32 at sample { cnt~(line~(x)) }";
    let option = "std.core.Option__U32";
    let (t, a, b) = (event_fn(f, "line.tick"), event_fn(f, "line.ev_0"), event_fn(f, "line.ev_1"));
    in_order(
        &t,
        &[&format!("let __out: {option} = {option}.None"), "__out = t.line.ev_0(", "t.fwd.tick(", "  __out\n}"],
    );
    in_order(&a, &[&format!("let __out: {option} = {option}.None"), "__out = t.line.ev_1(", "= n\n", "  __out\n}"]);
    in_order(&b, &[&format!("let __out: {option} = {option}.Some(b)"), "  __out\n}"]);
    // No function of the boundary of a flow with an event (W10-07).
    let m = crate::tests::core(&events(f));
    let made =
        |n: &str| m.flows.iter().find(|x| x.name == n).map(|x| (x.fns.process.is_some(), x.fns.render.is_some()));
    assert_eq!([made("t.line"), made("t.f")], [Some((false, false)), Some((true, true))]);
}

/// §3.5, S-1241: a condition read where it is written is kept in a local
/// before the call below that gives the event it reads.
#[test]
fn a_condition_of_an_event_is_kept_before_the_stage_of_the_event() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let q = prev~(^z) > 3
  let y = prev~(prev~(x).reset_if~(q at sample))
  let z = gen~(x)
  y
}";
    in_order(&event_fn(f, "f.tick"), &["let y.prev_0@5: Bool = s.0\n", "t.gen.tick(", "t.f.ev_0(", "if y.prev_0@5 {"]);
}

/// S-1240, S-1249: what a delay stores reads an event with no `^` in a local
/// made where it is written, after the work in it and whatever a condition
/// with a `^` chooses; a `^name` at the end of the stage. A part of
/// `sample / 4` of the end of its stage too, in the function of that tick.
#[test]
fn what_a_delay_stores_of_events_is_read_where_it_is_written() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~((gen~(x + 1) at sample) + (if ^k > 1 { p at sample } else { ^d at sample }))
  let k = x + 1
  let d = gen~(x)
  q
}";
    let t = event_fn(f, "f.tick");
    let (inner, outer) = (at(&t, "(x + 1:U32))"), at(&t, "let k: U32"));
    let reads: Vec<usize> = t.match_indices("let q@").map(|x| x.0).collect();
    assert_eq!(
        reads.iter().filter(|&&r| inner < r && r < outer).count(),
        3,
        "two reads and the value of the delay:\n{t}"
    );
    let f = "pub flow f(x: U32 at (sample / 4)) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(((p at (sample / 4)) * 2 + ^k) at sample)
  let k = x + 1
  let d = gen4~(x)
  q
}
flow gen4(x: U32 at (sample / 4)) -> U32 at event { Some(x) }";
    let t = event_fn(f, "f.tick_4");
    in_order(
        &t,
        &["let q._hoist_0: U32 = s.", "let k: U32", "t.gen4.tick_4(", "t.f.ev_0(", "((q._hoist_0 * 2:U32) + k)"],
    );
    assert!(!event_fn(f, "f.tick").contains("_hoist"), "{t}");
}

/// S-1250: a reset that an event ticks between the place a delay is written
/// at and its store waits for the store, of a delay in another too, whose
/// condition is read at the place of the delay; `reset` drops the flags, the
/// soft one does not read them.
#[test]
fn the_reset_of_an_event_in_the_stage_of_a_delay_is_after_its_store() {
    let f = "flow inner(x: U32 at sample) -> U32 at sample {
  let e = prev~(^d)
  let y = prev~(prev~(x, 9).reset_if~(e > 5), 7)
  let d = gen~(x)
  y
}
pub flow f(x: U32 at sample, c: Bool at sample) -> U32 at sample { inner~(x).reset_if~(c) }";
    let t = event_fn(f, "inner.tick");
    in_order(
        &t,
        &[
            "s.3 = true",
            "t.gen.tick(",
            "t.inner.ev_0(",
            "let y.prev_0: U32 = s.2",
            "s.2 = x\n",
            "s.3 = false",
            "if s.4 {",
            "s.4 = false",
            "s.2 = 9:U32",
        ],
    );
    let ev = event_fn(f, "inner.ev_0");
    in_order(&ev, &["if (e > 5:U32) {", "if s.3 {", "s.4 = true", "} else {", "s.2 = 9:U32"]);
    in_order(&event_fn(f, "inner.reset"), &["s.2 = 9:U32", "s.3 = false", "s.4 = false"]);
    let kept = event_fn(f, "inner._reset_kept");
    assert!(kept.contains("s.2 = 9:U32") && !kept.contains("s.3") && !kept.contains("s.4"), "{kept}");
}

/// §11.4: the stage of an event takes the time of the stage that ticks it.
#[test]
fn the_stage_of_an_event_takes_the_time_of_its_position() {
    let f = "pub flow f(x: U32 at sample) -> U32 at sample {
  let a = gen~(x)
  let b = stamp~(a)
  b at sample
}";
    at(&event_fn(f, "f.tick"), "t.f.ev_0(inout s, t, payload(");
    in_order(
        &event_fn(f, "f.ev_0"),
        &["(inout s: t.f.State, t: U32, ev: U32)", "t.stamp.ev_0(inout s.", "t.f.ev_1(inout s, payload("],
    );
}
