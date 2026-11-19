//! The stores and the reads of the hoisted fields (§11.3, W7-05 U1): the
//! function of a stage writes the fields of its stage, a field at `block`
//! reads one at `init`, and the later stages read the fields.

/// The function `t.f.<phase>` of `src`, as in the dump of the Core.
fn phase(src: &str, phase: &str) -> String {
    crate::dump::dump_item(&crate::tests::core(src), &format!("t.f.{phase}"))
}

/// The place of `what` in `text`, which holds it once.
fn at(text: &str, what: &str) -> usize {
    assert_eq!(text.matches(what).count(), 1, "`{what}` once in:\n{text}");
    text.find(what).unwrap_or_default()
}

/// `init` writes the field of `make(a)`, `ctl` the fields at `block` at the
/// places of their `let`s and those of the output last (S-1159), the one of
/// `make(a) * level` reading the one of `make(a)`; `tick` reads the fields
/// and calls no function that is not `rt` (R-17).
#[test]
fn each_stage_writes_its_fields_and_the_later_ones_read_them() {
    let src = "pub fn make(v: F32) -> F32 { v * 2.0 }
pub flow f(x: F32 at sample, a: F32 at init, level: F32 at block) -> F32 at sample {
  let h = x * (level + 1.0)
  let k = level * 3.0
  h + x * (make(a) * level) + k * x
}";
    let d = crate::dump::dump(&crate::tests::core(src));
    assert!(
        d.contains(
            "{ k: F32, h._hoist_0: F32, _out._hoist_0: F32, _out._hoist_1: F32, _poisoned: Bool, _initialized: Bool }"
        ),
        "{d}"
    );
    let init = phase(src, "init");
    assert!(init.contains("s.3 = t.make(cfg.0)\n"), "{init}");
    let ctl = phase(src, "ctl");
    let (h, k, out) = (at(&ctl, "s.1 = (p.0 + 1.0:F32)\n"), at(&ctl, "s.0 = k\n"), at(&ctl, "s.2 = (s.3 * p.0)\n"));
    assert!(h < k && k < out, "{ctl}");
    let tick = phase(src, "tick");
    assert!(tick.contains("let h: F32 = (x * s.1)\n"), "{tick}");
    assert!(tick.contains("((h + (x * s.2)) + (s.0 * x))"), "{tick}");
    assert!(!tick.contains("make") && !tick.contains("s.3"), "{tick}");
}

/// The argument of a delay is hoisted in its `let`, and the store of the
/// delay reads its field; the argument of an instance at `block` is read at
/// `block`, and is not hoisted.
#[test]
fn the_store_of_a_delay_reads_the_field_of_its_argument() {
    let src = "pub flow lp(x: F32 at sample, g: F32 at block) -> F32 at sample { x * g }
pub flow f(x: F32 at sample, level: F32 at block) -> F32 at sample {
  let k = prev~((level * 2.0) at sample)
  k + lp~(x, level + 1.0) * x
}";
    let ctl = phase(src, "ctl");
    assert!(ctl.contains("s.2 = (p.0 * 2.0:F32)\n"), "{ctl}");
    assert!(ctl.contains("t.lp.Params { g: (p.0 + 1.0:F32) }"), "{ctl}");
    let tick = phase(src, "tick");
    assert!(tick.contains("s.0 = s.2\n"), "{tick}");
    assert!(!tick.contains("2.0:F32"), "{tick}");
}
