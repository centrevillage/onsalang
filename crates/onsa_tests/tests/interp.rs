//! End-to-end interpreter tests over Onsa source (T3-7 to T3-9): aliasing
//! through `inout`, `const` evaluation through function calls, and flows run
//! through their generated API.

use onsa_diag::SourceMap;
use onsa_interp::{Interp, Value};

/// A one-module package `t` (no manifest, spec §15.1), as the CLI loads one.
fn load(src: &str) -> (onsa_driver::Loaded, onsa_driver::Analyzed) {
    let mut loaded = onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file("t.onsa", src)).unwrap();
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    (loaded, analyzed)
}

/// Check, lower and run every `test` of a one-module package; returns the
/// outcomes as `(name, failure message)`.
fn run(src: &str) -> (Vec<(String, Option<String>)>, SourceMap) {
    let (loaded, analyzed) = load(src);
    let sources = loaded.sources;
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analyzed.diagnostics));
    let module = onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&sources)));
    let report = match onsa_driver::run_tests(&sources, &module, &onsa_driver::TestOptions::default()) {
        Ok(onsa_driver::TestRun::Ran(r)) => r,
        Ok(onsa_driver::TestRun::Unsupported(d)) => panic!("{}", onsa_diag::to_text(&sources, &d)),
        Ok(onsa_driver::TestRun::NoMatch) => panic!("no test selected without `--filter`"),
        Err(e) => panic!("{}", e.render(&sources)),
    };
    (report.tests.into_iter().map(|t| (t.name.clone(), t.message().map(str::to_string))).collect(), sources)
}

fn all_pass(src: &str) {
    let (tests, _) = run(src);
    assert!(!tests.is_empty());
    for (name, msg) in tests {
        assert!(msg.is_none(), "test {name:?} failed: {}", msg.unwrap());
    }
}

#[test]
fn inout_aliases_fields_and_elements() {
    all_pass(
        r#"
pub struct P {
  xs: [I32; 3],
  n: I32,
}

fn bump(inout x: I32) {
  x = x + 1
}

fn bump_all(inout p: P) {
  bump(inout p.n)
  bump(inout p.xs[1])
}

test "writes through inout land in the caller" {
  var p = P { xs: [0, 0, 0], n: 10 }
  bump_all(inout p)
  bump(inout p.xs[2])
  let i: U32 = 1
  let j: U32 = 2
  assert p.n == 11
  assert p.xs[i] == 1
  assert p.xs[j] == 1
}

test "value semantics copy arrays" {
  let a: [I32; 2] = [1, 2]
  var b = a
  bump(inout b[0])
  let z: U32 = 0
  assert a[z] == 1
  assert b[z] == 2
}
"#,
    );
}

#[test]
fn spans_write_through_and_builtins_work() {
    all_pass(
        r#"
fn zero_first(inout xs: Span[F32]) {
  xs[0] = 0.0
}

test "span writes reach the array" {
  var a: [F32; 3] = [1.0, 2.0, 3.0]
  zero_first(inout a)
  let z: U32 = 0
  assert a[z] == 0.0
  a.fill!(5.0)
  let one: U32 = 1
  assert a[one] == 5.0
  let b: [F32; 3] = [1.0, 1.0, 1.0]
  a.add_from!(b)
  assert a[one] == 6.0
  assert a.len() == 3
  assert a.slice(1, 3).len() == 2
  match a.get(7) {
    Some(_) => { assert false },
    None => { assert true },
  }
}
"#,
    );
}

/// S-1116 (§5.3): the tails of an `if` at a view, of other kinds and lengths, each converted on its
/// own (an array, a partial view, a `Buf`, the whole of a longer array; a planar literal, an array
/// of arrays and of `Buf`s, a `const`, a call and a repetition bound to a temporary, a binding of
/// the arm), and a planar argument that is no place written at the argument itself.
#[test]
fn view_tails_of_other_kinds_run() {
    all_pass(
        r#"
pub fn take(s: Span[F32]) -> F32 { s[0] + F32.round_from(s.len()) }
pub fn two(xs: [Span[F32]; 2]) -> F32 { xs[0][0] + xs[1][0] + F32.round_from(xs[0].len() + xs[1].len()) }
const PS: [[F32; 4]; 2] = [[1.0; 4], [2.0; 4]]
fn mk2(v: F32) -> [[F32; 4]; 2] { [[v; 4], [v + 1.0; 4]] }
pub fn span_mixed(k: U32, x: [F32; 4], y: [F32; 8], b: Buf[F32]) -> F32 {
  take(if k == 0 { x } else if k == 1 { y.slice(2, 4) } else if k == 2 { b } else { y })
}
pub fn planar_mixed(k: U32, x: [F32; 4], y: [F32; 8], ps: [[F32; 4]; 2], bs: [Buf[F32]; 2]) -> F32 {
  two(if k == 0 { [x, y.slice(1, 3)] } else if k == 1 { ps } else if k == 2 { bs } else if k == 3 { PS } else if k == 4 { mk2(5.0) } else if k == 5 { [x; 2] } else {
    let t = mk2(7.0)
    t
  })
}
pub fn planar_temp(v: F32) -> F32 { two(mk2(v)) + two(PS) + two([[v; 2]; 2]) }
test "each tail is passed as the view" {
  let x = [1.0; 4]
  var y = [0.0; 8]
  for i in 0..<8 { y[i] = F32.round_from(i) }
  let b = Buf.zeroed(3)
  assert span_mixed(0, x, y, b) == 5.0
  assert span_mixed(1, x, y, b) == 4.0
  assert span_mixed(2, x, y, b) == 3.0
  assert span_mixed(3, x, y, b) == 8.0
  let ps = [[3.0; 4], [4.0; 4]]
  let bs = [Buf.zeroed(1), Buf.zeroed(2)]
  assert planar_mixed(0, x, y, ps, bs) == 8.0
  assert planar_mixed(1, x, y, ps, bs) == 15.0
  assert planar_mixed(2, x, y, ps, bs) == 3.0
  assert planar_mixed(3, x, y, ps, bs) == 11.0
  assert planar_mixed(4, x, y, ps, bs) == 19.0
  assert planar_mixed(5, x, y, ps, bs) == 10.0
  assert planar_mixed(6, x, y, ps, bs) == 23.0
  assert planar_temp(5.0) == 44.0
}
"#,
    );
}

#[test]
fn const_initializers_run_through_the_interpreter() {
    all_pass(
        r#"
const N: U32 = 4
const TABLE: [F32; 4] = make_table()
const HALF: F32 = half_of(3.0)

fn make_table() -> [F32; 4] {
  var t: [F32; 4] = [0.0; 4]
  for i in 0..<N {
    t[i] = F32.round_from(i) * 2.0
  }
  t
}

fn half_of(x: F32) -> F32 {
  x / 2.0
}

test "consts computed by functions" {
  let three: U32 = 3
  assert TABLE[three] == 6.0
  assert HALF == 1.5
}
"#,
    );
}

#[test]
fn panics_report_their_position() {
    let (tests, sources) = run(r#"
test "boom" {
  let xs: [I32; 1] = [0]
  let i: U32 = 3
  assert xs[i] == 0
}
"#);
    assert_eq!(tests.len(), 1);
    let msg = tests[0].1.as_deref().unwrap();
    assert!(msg.contains("out of range"), "{msg}");
    let _ = sources;
}

#[test]
fn flows_render_through_the_generated_api() {
    all_pass(
        r#"
use std.math.{exp, cos}
use std.math.{sum}
use std.dsp.test.{impulse, energy}

const UNISON: U32 = 4

pub flow saw(f0: F32 at block) -> F32 at sample {
  let phase = wrap01(prev~(^phase) + (f0 / sample_rate()))
  (2.0 * phase) - 1.0
}

pub rt fn wrap01(x: F32) -> F32 {
  x - (F32.round_from(I32.trunc_sat_from(x)))
}

pub rt fn spread(i: U32, n: U32) -> F32 {
  (F32.round_from(i) / F32.round_from(n - 1)) - 0.5
}

pub flow unison(f0: F32 at block, detune: F32 at block) -> F32 at sample {
  let saws = par~ i in 0..<UNISON {
    saw~(f0 * (1.0 + (detune * spread(i, UNISON))))
  }
  sum(saws) * 0.25
}

pub flow resonator(x: F32 at sample, fc: F32 at block, bw: F32 at block) -> F32 at sample {
  let r  = exp(-(F32.PI * bw) / sample_rate())
  let w  = (2.0 * F32.PI * fc) / sample_rate()
  let b1 = 2.0 * r * cos(w)
  let b2 = r * r
  let y1 = prev~(^y)
  let y2 = prev~(y1)
  let y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)
  y
}

test "unison produces a signal in range" {
  let o = unison.render(unison.Params { f0: 110.0, detune: 0.01 }, 4800, 48000.0)
  let e = energy(o.out, 0, 4800)
  assert e > 0.0
  assert e < 4800.0
}

test "resonator rings then decays" {
  let o = resonator.render(resonator.Params { fc: 500.0, bw: 100.0 }, impulse(48000), 48000.0)
  assert energy(o.out, 0, 1000) > 0.0
  assert energy(o.out, 47000, 48000) < 1.0e-12
}

test "process runs block by block with reset" {
  var st = resonator.init(48000.0)
  var input: [F32; 8] = [0.0; 8]
  input[0] = 1.0
  var out: [F32; 8] = [0.0; 8]
  let p = resonator.Params { fc: 500.0, bw: 100.0 }
  resonator.process(inout st, p, input, inout out)
  let z: U32 = 0
  let one: U32 = 1
  assert out[z] > 0.0
  assert out[one] > 0.0
  resonator.reset(inout st)
  var silence: [F32; 8] = [0.0; 8]
  resonator.process(inout st, p, silence, inout out)
  assert out[z] == 0.0
}
"#,
    );
}

#[test]
fn interp_api_calls_functions_directly() {
    let (_, analyzed) = load("pub fn twice(x: I32) -> I32 { x * 2 }\n");
    let module = onsa_driver::lower_core(&analyzed).unwrap();
    // The interpreter runs on the stack of a command (R-05).
    onsa_diag::stack::run(|| {
        let interp = Interp::new(&module);
        let f = interp.fn_by_name("t.twice").expect("fn");
        let v = interp.call(f, vec![Value::I32(21)]).unwrap();
        assert_eq!(v.to_i128(), Some(42));
    });
}
