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
/// negation), and the arm of a `match` that binds what it reads (and reads
/// it for nothing, as each block of the work, S-1247); a checked
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
        "  switch p@11.1 {\n    Some => {\n      let v: F32 = payload(p@11.1, Some, 0)\n      v\n      s.7 = (v * p@11.2)\n    }\n",
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

/// §11.3, S-1094 (1): `ctl` writes the field of a guard of `match~` while
/// the arms before it are not taken and its pattern matches, and the field
/// of an arm body under no condition (every arm body is evaluated, R-14).
#[test]
fn the_field_of_a_guard_of_match_tilde_is_guarded_and_that_of_a_body_is_not() {
    let src = "pub flow acc(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample, o: Option[I32] at block, n: I32 at block) -> F32 at sample {
  match~ o {
    Some(_) if n > 7 => acc~(x),
    Some(v) if v > 100 / n => acc~(x),
    Some(_) => acc~(x) * F32.round_from(200 / n),
    None => x,
  }
}";
    let ctl = phase(src, "ctl");
    let open = "if ((__arm == 4:U32) && (tag(p.0) == 1:U8)) {\n";
    let first = at(&ctl, &format!("{open}    s.4 = (p.1 > 7:I32)\n"));
    let second =
        at(&ctl, &format!("{open}    let v: I32 = payload(p.0, Some, 0)\n    v\n    s.5 = (v > (100:I32 / p.1))\n"));
    let body = at(&ctl, "\n  s.6 = round.I32.F32((200:I32 / p.1))\n");
    assert!(first < second && second < body, "{ctl}");
}

/// W7-16 U6a2: a field in an argument a chain of `.down~` gathers, which
/// the function of the ring lowers and reads, is written by the function
/// of its stage before the call: in a field of that stage (the call lifted
/// with `at`) or of a slower one, in a `let` of that stage or a slower
/// one, and in a `par~` (its replica's). The ring is written of the field
/// the slower function writes; the lowering checks that every field read
/// is written ([`super::HoistUses`]).
#[test]
fn a_field_in_an_argument_a_chain_gathers_is_written_at_its_stage() {
    let head = "flow cnt(i0: U32 at block) -> U32 at sample {
  let n = (i0 + prev~(^n)) % 997
  n
}
flow g2(a: U32 at (sample * 2)) -> U32 at sample { a[0] * 10 + a[1] }
flow g4(a: U32 at (sample * 4)) -> U32 at sample { a[0] + a[1] + a[2] + a[3] }
";
    let bodies = [
        "g2~((h + 1) at sample).down~(2) at sample",
        "g4~((h + 1) at sample).down~(4) at sample",
        "let r = g2~((h + 1) at sample).down~(2)\n  r at sample",
        "let r = g4~((h + 1) at sample).down~(4)\n  r at sample",
        "let ys = par~ i in 0 ..< 2 { g2~((h + 1) at sample).down~(2) at sample }\n  ys[0] + ys[1]",
    ];
    for body in bodies {
        let src =
            format!("{head}pub flow f(p: U32 at block) -> U32 at sample {{\n  let h = cnt~(p).down~(2)\n  {body}\n}}");
        let m = crate::tests::core(&src);
        let tick = crate::dump::dump_item(&m, "t.f.tick");
        let ring = tick.lines().find(|l| l.contains(")] = ")).unwrap_or_default();
        let read = ring.rsplit(" = ").next().unwrap_or_default();
        assert!(read.starts_with("s."), "{body}: no ring written of a field in:\n{tick}");
        let slow = crate::dump::dump_item(&m, "t.f.tick_2");
        let write = at(&slow, &format!("{read} = (h + 1:U32)\n"));
        let call = slow.find("t.g2.tick(").or(slow.find("t.g4.tick(")).unwrap_or(usize::MAX);
        assert!(write < call, "{body}: the field written after the call:\n{slow}");
    }
}

/// S-1197: a field read of a name of a tick is written at each tick, before
/// the conditions on its path and once, in a loop over the replicas of the
/// `par` that holds it; what is computed beside it, under them.
#[test]
fn a_field_read_of_a_name_is_written_under_no_condition() {
    let src = "pub struct D: Default { vel: F32, on: Bool }
flow lp(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample, g: Bool at sample, i: I32 at init) -> F32 at sample {
  let k = prev~(^k at (sample / 4)) + 1.0
  let s = D { vel: k, on: k > 1.0 }
  let a = if i > 0 { (if g { s.vel at sample } else { x }) + ((s.vel * 3.0) at sample) } else { x }
  let b = if g { par j in 0 ..< 3 { (s.vel at sample) * x } } else { par j in 0 ..< 3 { x } }
  let c = if~ g { lp~(x) } else if x > 0.0 && (s.on at sample) { lp~(x) } else { x }
  let d = match~ g { true if (s.on at sample) => lp~(x), _ => x }
  a + b[0] + c + d
}";
    let slow = phase(src, "tick_4");
    let free = "  s@11.7 = s@4.0\n";
    let held = "  if s@11.6 {\n    s@11.8 = (s@4.0 * 3.0:F32)\n  }\n";
    let each = "  for j@9 in 0:U32..3:U32 {\n    s@11.2[j@9].0 = s@4.0\n  }\n";
    at(&slow, &format!("{free}{held}{each}  s@11.9 = s@4.1\n  s@11.10 = s@4.1\n  s@11.1 = k\n"));
    assert_eq!(slow.matches("if ").count(), 1, "{slow}");
}

/// S-1197: the field read of a name in a guard of a `match~`, beside a part
/// computed there, is written once, before the guarded one.
#[test]
fn a_field_read_beside_a_guarded_part_of_a_guard_is_written_once() {
    let src = "pub struct D: Default { vel: F32, q: F32 }
flow lp(x: F32 at sample) -> F32 at sample { x + prev~(x) }
pub flow f(x: F32 at sample) -> F32 at sample {
  let k = prev~(^k at (sample / 4)) + 1.0
  let s = D { vel: k + 10.0, q: k }
  let r = sample_rate()
  match~ r > 2.0 { true if ((s.q * 2.0) at sample) > 3.0 && (s.vel at sample) > 12.0 => lp~(x), _ => lp~(x + 1.0) }
}";
    let slow = phase(src, "tick_4");
    assert_eq!((slow.matches(" = s@2.0\n").count(), slow.matches("* 2.0:F32)\n").count()), (1, 1), "{slow}");
}
