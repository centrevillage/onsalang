//! End-to-end interpreter tests over Onsa source (T3-7 to T3-9): aliasing
//! through `inout`, `const` evaluation through function calls, and flows run
//! through their generated API.

use onsa_diag::SourceMap;
use onsa_interp::{Interp, Value};

/// A one-module package `t` (no manifest, spec §15.1), as the CLI loads one.
fn load(src: &str) -> (onsa_driver::Loaded, onsa_driver::Analyzed) {
    let input = onsa_driver::PackageInput {
        manifest: None,
        files: vec![onsa_driver::SourceFile { path: "t.onsa".into(), text: src.into() }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
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
    t[i] = i.round_f32() * 2.0
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
use std.dsp.{sum}
use std.dsp.test.{impulse, energy}

const UNISON: U32 = 4

pub flow saw(f0: Ctl[F32]) -> Sig[F32] {
  let phase = wrap01(prev(phase, 0.0) + (f0 / sample_rate()))
  (2.0 * phase) - 1.0
}

pub rt fn wrap01(x: F32) -> F32 {
  x - (x.trunc_i32_sat().round_f32())
}

pub rt fn spread(i: U32, n: U32) -> F32 {
  (i.round_f32() / (n - 1).round_f32()) - 0.5
}

pub flow unison(f0: Ctl[F32], detune: Ctl[F32]) -> Sig[F32] {
  let saws = par i in 0..<UNISON {
    saw~(f0 * (1.0 + (detune * spread(i, UNISON))))
  }
  sum(saws) * 0.25
}

pub flow resonator(x: Sig[F32], fc: Ctl[F32], bw: Ctl[F32]) -> Sig[F32] {
  let r  = exp(-(F32.PI * bw) / sample_rate())
  let w  = (2.0 * F32.PI * fc) / sample_rate()
  let b1 = 2.0 * r * cos(w)
  let b2 = r * r
  let y1 = prev(y, 0.0)
  let y2 = prev(y1, 0.0)
  let y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)
  y
}

test "unison produces a signal in range" {
  let o = unison.render(unison.Config {}, unison.Params { f0: 110.0, detune: 0.01 }, 4800, 48000.0)
  let e = energy(o.out, 0, 4800)
  assert e > 0.0
  assert e < 4800.0
}

test "resonator rings then decays" {
  let o = resonator.render(resonator.Config {}, resonator.Params { fc: 500.0, bw: 100.0 }, impulse(48000), 48000.0)
  assert energy(o.out, 0, 1000) > 0.0
  assert energy(o.out, 47000, 48000) < 1.0e-12
}

test "process runs block by block with reset" {
  var st = resonator.init(resonator.Config {}, 48000.0)
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
