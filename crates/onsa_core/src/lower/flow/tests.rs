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
    // The writes of the field of the guard (which choose no arm), the arm 0
    // and the arm 1 once, which writes `v` too.
    assert_eq!(ctl.matches(": U32 = 3:U32").count(), 3, "{ctl}");
    assert_eq!(ctl.matches("__bind.v = v").count(), 2, "{ctl}");
    assert_eq!(ctl.matches("__bind.w = w").count(), 1, "{ctl}");
    let (w_set, lp1) = (at(&ctl, "__bind.w = w"), at(&ctl, "Params { g: __bind.w }"));
    assert!(w_set < lp1, "{ctl}");
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
