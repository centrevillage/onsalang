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

/// S-1157: `ctl` writes a guarded field under its condition read at `block`
/// (its field, written first): an `if`, the left of `&&` and of `||` (its
/// negation), and the arm of a `match` that binds what it reads; a checked
/// constant (S-888 (c′)) is evaluated there for its panic. `tick` reads.
#[test]
fn a_guarded_field_is_written_under_its_condition() {
    let src =
        "pub flow f(x: F32 at sample, n: I32 at block, o: Option[F32] at block, k: F32 at block) -> F32 at sample {
  let p = if n != 0 { x * F32.round_from(100 / n) } else { x }
  let q = n > 2 && x > F32.round_from(10 / n)
  let r = n < 2 || x > F32.round_from(20 / n)
  let m = match o { Some(v) => v * k + x, None => x }
  let t = if n == 0 { panic(\"bad n\") } else { x }
  p + m + t + (if q || r { 1.0 } else { 0.0 })
}";
    let ctl = phase(src, "ctl");
    let want = [
        "  s.1 = (p@11.0 != 0:I32)\n  if s.1 {\n    s.2 = round.I32.F32((100:I32 / p@11.0))\n  }\n",
        "  s.3 = (p@11.0 > 2:I32)\n  if s.3 {\n    s.4 = round.I32.F32((10:I32 / p@11.0))\n  }\n",
        "  s.5 = (p@11.0 < 2:I32)\n  if (!s.5) {\n    s.6 = round.I32.F32((20:I32 / p@11.0))\n  }\n",
        "  switch p@11.1 {\n    Some => {\n      let v: F32 = payload(p@11.1, Some, 0)\n      s.7 = (v * p@11.2)\n    }\n",
        "  s.8 = (p@11.0 == 0:I32)\n  if s.8 {\n    panic(\"bad n\")\n  }\n",
    ];
    for w in want {
        assert!(ctl.contains(w), "{w}\nin\n{ctl}");
    }
    let tick = phase(src, "tick");
    assert!(tick.contains("(x * s.2)") && tick.contains("(s.7 + x)"), "{tick}");
    assert!(!tick.contains("100:I32"), "{tick}");
}

/// S-1140: a field of the body of a `par~` is of each replica: the stage
/// writes it in a loop over the replicas, of the nested one too, one at
/// `block` reading one at `init` of its replica, and `tick` reads it of the
/// replica it lowers. A replica with hoisted fields only gets no loop to
/// set, reset or run its nodes.
#[test]
fn the_fields_of_the_body_of_a_par_are_written_and_read_in_each_replica() {
    let src = "pub fn make(v: F32) -> F32 { v * 2.0 }
pub rt fn pair(xs: [F32; 2]) -> F32 { xs[0] + xs[1] }
pub flow f(x: F32 at sample, level: F32 at block) -> F32 at sample {
  let a = par i in 0 ..< 2 { pair(par j in 0 ..< 2 { x * make(F32.round_from(i + j)) }) }
  let b = par i in 0 ..< 2 { x * (level * F32.round_from(i)) }
  a[0] + b[1]
}";
    let d = crate::dump::dump(&crate::tests::core(src));
    // S-1175: a `par~` whose body holds no node is named as one with no name.
    assert!(d.contains("type t.f.a.par_0.par_0.State = struct { _hoist_0: F32 }"), "{d}");
    assert!(d.contains("type t.f.a.par_0.State = struct { par_0: [t.f.a.par_0.par_0.State; 2] }"), "{d}");
    assert!(d.contains("type t.f.b.par_0.State = struct { _hoist_0: F32, _hoist_1: F32 }"), "{d}");
    let init = phase(src, "init");
    let nested = "for i@4 in 0:U32..2:U32 {\n    for j in 0:U32..2:U32 {\n      s.0[i@4].0[j].0 = t.make(round.U32.F32((i@4 + j)))\n";
    assert!(init.contains(nested), "{init}");
    assert!(init.contains("for i@6 in 0:U32..2:U32 {\n    s.1[i@6].1 = round.U32.F32(i@6)\n"), "{init}");
    assert_eq!(init.matches("for ").count(), 3, "{init}");
    let ctl = phase(src, "ctl");
    assert!(ctl.contains("for i@6 in 0:U32..2:U32 {\n    s.1[i@6].0 = (p.0 * s.1[i@6].1)\n"), "{ctl}");
    assert_eq!(ctl.matches("for ").count(), 1, "{ctl}");
    let tick = phase(src, "tick");
    assert!(tick.contains("(x * s.0[i@4].0[j].0)") && tick.contains("(x * s.1[i@6].0)"), "{tick}");
    assert!(!tick.contains("make") && !tick.contains("round"), "{tick}");
    assert!(!phase(src, "reset").contains("for "), "the replicas have no node");
}
