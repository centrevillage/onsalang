//! The time of the lowering of a flow grows with its state linearly (R-498).

use std::time::{Duration, Instant};

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
