//! Unit tests for lowering, monomorphization and the verifier.

use onsa_diag::{FileId, SourceMap};
use onsa_sema::{Module as SModule, Package};

use crate::ir::*;
use crate::{dump, lower, verify};

const STD: &[(&str, &str)] = &[
    ("math", include_str!("../../../std/math.onsa")),
    ("dsp", include_str!("../../../std/dsp.onsa")),
    ("dsp.test", include_str!("../../../std/dsp/test.onsa")),
    ("array", include_str!("../../../std/array.onsa")),
    ("test", include_str!("../../../std/test.onsa")),
    ("test.gen", include_str!("../../../std/test/gen.onsa")),
];

fn package(src: &str) -> (SourceMap, Package) {
    let mut sources = SourceMap::default();
    let std_mods: Vec<SModule> = STD
        .iter()
        .map(|(path, text)| {
            let file = sources.add(format!("std/{path}.onsa"), *text);
            SModule { path: path.to_string(), file, text: text.to_string(), parsed: onsa_syntax::parse(file, text) }
        })
        .collect();
    let std = Package { name: "std".into(), modules: std_mods, deps: Vec::new(), is_std: true };
    let file = sources.add("t.onsa", src);
    let parsed = onsa_syntax::parse(file, src);
    let user = SModule { path: "t".into(), file, text: src.to_string(), parsed };
    (sources, Package { name: "t".into(), modules: vec![user], deps: vec![std], is_std: false })
}

/// Lower a one-module package; panics on check or lowering diagnostics.
fn core(src: &str) -> Module {
    let (sources, pkg) = package(src);
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.is_empty(), "check diagnostics:\n{}", onsa_diag::to_text(&sources, &a.diagnostics));
    match lower(&pkg, &a) {
        Ok(m) => {
            verify(&m).unwrap_or_else(|e| panic!("{e}\n{}", dump(&m)));
            m
        }
        Err(d) => panic!("lowering diagnostics:\n{}", onsa_diag::to_text(&sources, &d)),
    }
}

/// Lowering diagnostics of a source that checks cleanly.
fn core_err(src: &str) -> Vec<onsa_diag::Diagnostic> {
    let (sources, pkg) = package(src);
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.is_empty(), "check diagnostics:\n{}", onsa_diag::to_text(&sources, &a.diagnostics));
    lower(&pkg, &a).expect_err("expected a lowering error")
}

fn text(src: &str) -> String {
    dump(&core(src))
}

#[test]
fn operators_carry_overflow_modes() {
    let d = text(
        "pub fn f(a: I32, b: I32) -> I32 {\n  let c = a + b\n  let w = a +% b\n  let s = a *| b\n  let q = a / b\n  let r = a % b\n  let sh = a << 3\n  (c - w) & s\n}\n",
    );
    assert!(d.contains("(a + b)"), "{d}");
    assert!(d.contains("(a +% b)"), "{d}");
    assert!(d.contains("(a *| b)"), "{d}");
    assert!(d.contains("(a / b)"), "{d}");
    assert!(d.contains("(a << 3:U32)"), "{d}");
}

#[test]
fn float_rem_is_fmod_and_literals_keep_their_kind() {
    let d = text("pub fn f(x: F32, y: F64) -> F32 {\n  let z = y % 2.0\n  x % 1.5\n}\n");
    assert!(d.contains("math.fmod.F64(y, 2.0:F64)"), "{d}");
    assert!(d.contains("math.fmod.F32(x, 1.5:F32)"), "{d}");
}

#[test]
fn try_lowers_to_switch_with_early_return() {
    let d = text("pub fn f(x: Option[I32]) -> Option[I32] {\n  let v = x?\n  Some(v + 1)\n}\n");
    assert!(d.contains("type Option__I32 = enum { None, Some(I32) }"), "{d}");
    assert!(d.contains("switch x {"), "{d}");
    assert!(d.contains("return Option__I32.None"), "{d}");
    assert!(d.contains("payload(x, Some, 0)"), "{d}");
    assert!(d.contains("Option__I32.Some((v + 1:I32))"), "{d}");
}

#[test]
fn match_on_enum_is_a_switch() {
    let d = text(
        "pub enum Shape {\n  Circle(F32),\n  Rect(F32, F32),\n}\n\npub fn area(s: Shape) -> F32 {\n  match s {\n    Shape.Circle(r) => r * r,\n    Shape.Rect(w, h) => w * h,\n  }\n}\n",
    );
    assert!(d.contains("switch s {"), "{d}");
    assert!(d.contains("Circle => {"), "{d}");
    assert!(d.contains("let r: F32 = payload(s, Circle, 0)"), "{d}");
    assert!(d.contains("Rect => {"), "{d}");
}

#[test]
fn match_with_guard_uses_if_chain() {
    let d = text(
        "pub fn f(x: Option[I32]) -> I32 {\n  match x {\n    Some(v) if v > 0 => v,\n    Some(v) => -v,\n    None => 0,\n  }\n}\n",
    );
    assert!(d.contains("__done"), "{d}");
    assert!(d.contains("(tag(x) == 1:U8)"), "{d}");
    assert!(d.contains("__result"), "{d}");
}

#[test]
fn option_equality_uses_generated_eq() {
    let d = text("pub fn f(a: Option[U8], b: U8) -> Bool {\n  a == Some(b)\n}\n");
    assert!(d.contains("__eq.Option__U8(a, Option__U8.Some(b))"), "{d}");
    assert!(d.contains("rt fn __eq.Option__U8(a: Option__U8, b: Option__U8) -> Bool"), "{d}");
    assert!(d.contains("if (tag(a) != tag(b)) {"), "{d}");
}

#[test]
fn for_over_array_is_an_index_loop() {
    let d = text("pub fn sum(xs: [F32; 4]) -> F32 {\n  var acc = 0.0\n  for x in xs { acc = acc + x }\n  acc\n}\n");
    assert!(d.contains("for __i in 0:U32..4:U32 {"), "{d}");
    assert!(d.contains("let x: F32 = xs[__i]"), "{d}");
}

#[test]
fn for_over_span_uses_len_prim() {
    let d =
        text("pub rt fn total(xs: Span[F32]) -> F32 {\n  var acc = 0.0\n  for x in xs { acc = acc + x }\n  acc\n}\n");
    assert!(d.contains("..len(xs) {"), "{d}");
}

#[test]
fn from_fn_closure_is_inlined() {
    let d = text(
        "use std.array\n\npub fn squares(k: F32) -> [F32; 3] {\n  array.from_fn(fn(i) { (i.round_f32()) * k })\n}\n",
    );
    assert!(d.contains("let __arr: [F32; 3] = zeroed:[F32; 3]"), "{d}");
    assert!(d.contains("for __i in 0:U32..3:U32 {"), "{d}");
    assert!(d.contains("let i: U32 = __i"), "{d}");
    assert!(d.contains("__arr[__i] = (round.U32.F32(i) * k)"), "{d}");
    assert!(d.contains("sret"), "{d}");
}

#[test]
fn generics_are_monomorphized_and_deduplicated() {
    let d = text(
        "pub fn clamp[T: PartialOrd](x: T, lo: T, hi: T) -> T {\n  if x < lo { lo } else if x > hi { hi } else { x }\n}\n\npub fn f(a: F32, b: I32) -> F32 {\n  let p = clamp(a, 0.0, 1.0)\n  let q = clamp(a, 0.5, 1.0)\n  let r = clamp(b, 0, 10)\n  p + q\n}\n",
    );
    assert_eq!(d.matches("fn t.clamp__F32(").count(), 1, "{d}");
    assert_eq!(d.matches("fn t.clamp__I32(").count(), 1, "{d}");
    assert!(d.contains("t.clamp__F32(a, 0.0:F32, 1.0:F32)"), "{d}");
}

#[test]
fn const_generics_name_instances() {
    let d = text("use std.dsp.{sum}\n\npub fn f(xs: [F32; 4]) -> F32 {\n  sum(xs)\n}\n");
    assert!(d.contains("std.dsp.sum__4(xs)"), "{d}");
    assert!(d.contains("rt fn std.dsp.sum__4(xs: [F32; 4]) -> F32"), "{d}");
    assert!(d.contains("for i in 0:U32..4:U32 {"), "{d}");
}

#[test]
fn consts_and_assoc_consts() {
    let d =
        text("const N: U32 = 8\nconst TWO_PI: F32 = 6.283\n\npub fn f() -> F32 {\n  let k = N\n  F32.PI * TWO_PI\n}\n");
    assert!(d.contains("const t.N: U32 = 8:U32"), "{d}");
    assert!(d.contains("3.1415927:F32"), "{d}");
    assert!(d.contains("const t.TWO_PI"), "{d}");
}

#[test]
fn methods_and_builtin_prims() {
    let d = text(
        "pub fn f(x: F64, n: I64) -> I32 {\n  let a = x.trunc_i32_sat()\n  let b = n.narrow_i32().unwrap_or(0)\n  let c = x.to_bits()\n  a + b\n}\n",
    );
    assert!(d.contains("trunc_sat.F64.I32(x)"), "{d}");
    assert!(d.contains("narrow.I64.I32(n)"), "{d}");
    assert!(d.contains("to_bits.F64(x)"), "{d}");
    assert!(d.contains("switch "), "{d}");
}

#[test]
fn span_coercions_and_bang_methods() {
    let d = text(
        "pub rt fn fill(inout out: Span[F32]) {\n  out.fill!(0.0)\n}\n\npub rt fn g(inout buf: [F32; 8]) {\n  fill(inout buf)\n  buf.fill!(1.0)\n  let n = buf.len()\n}\n",
    );
    assert!(d.contains("fill(inout span(buf))"), "{d}");
    assert!(d.contains("fill(inout span(buf), 1.0:F32)"), "{d}");
    assert!(d.contains("let n: U32 = 8:U32"), "{d}");
}

#[test]
fn flow_members_are_lowered_when_referenced() {
    let d = text(
        "pub flow one(x: Sig[F32]) -> Sig[F32] {\n  x\n}\n\npub fn mk(sr: F32) -> one.State {\n  one.init(one.Config {}, sr)\n}\n",
    );
    assert!(d.contains("type t.one.State = struct { poisoned: Bool }"), "{d}");
    assert!(d.contains("fn t.one.init(cfg: t.one.Config, sample_rate: F32) -> t.one.State sret {"), "{d}");
    assert!(d.contains("rt fn t.one.tick(inout s: t.one.State, x: F32) -> F32 {"), "{d}");
}

#[test]
fn unsupported_features_are_e0200() {
    let diags = core_err("pub fn f() -> Str {\n  \"abc\"\n}\n");
    assert_eq!(diags[0].code, onsa_diag::Code::E0200, "{diags:?}");
}

#[test]
fn verifier_rejects_bad_modules() {
    let span = onsa_diag::Span::new(FileId(0), 0, 0);
    let mut m = Module::default();
    m.fns.push(FnDef {
        name: "bad".into(),
        params: Vec::new(),
        ret: Ty::Int(IntKind::I32),
        sret: false,
        rt: false,
        locals: vec![Local { name: "x".into(), ty: Ty::Int(IntKind::I32) }],
        body: Some(Block {
            stmts: Vec::new(),
            value: Some(Box::new(Expr::new(Ty::Int(IntKind::I32), span, ExprKind::Local(LocalId(0))))),
        }),
        span,
    });
    let err = verify(&m).unwrap_err();
    assert!(err.message.contains("read before definition"), "{err}");
    // Type mismatch: a Bool body for an I32 function.
    m.fns[0].body = Some(Block {
        stmts: Vec::new(),
        value: Some(Box::new(Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(true))))),
    });
    let err = verify(&m).unwrap_err();
    assert!(err.message.contains("mismatch"), "{err}");
}

// ---------------------------------------------------------------- flows (T3-5, T3-6)

fn core_with(src: &str, bulk_threshold: Option<u32>) -> Module {
    let (sources, pkg) = package(src);
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.is_empty(), "check diagnostics:\n{}", onsa_diag::to_text(&sources, &a.diagnostics));
    let opts = crate::LowerOptions { bulk_threshold };
    match crate::lower_with(&pkg, &a, &opts) {
        Ok(m) => {
            verify(&m).unwrap_or_else(|e| panic!("{e}\n{}", dump(&m)));
            m
        }
        Err(d) => panic!("lowering diagnostics:\n{}", onsa_diag::to_text(&sources, &d)),
    }
}

/// Byte offset of `needle` in `hay`, panicking with the dump when absent.
fn pos(hay: &str, needle: &str) -> usize {
    hay.find(needle).unwrap_or_else(|| panic!("`{needle}` not found in:\n{hay}"))
}

const RESONATOR: &str = "use std.math.{exp, cos}

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
";

#[test]
fn resonator_lowers_to_the_five_functions() {
    let m = core(RESONATOR);
    let d = dump(&m);
    // State fields (S-05): sample_rate, the Ctl lets read at Sig, the prev nodes, poisoned.
    assert!(
        d.contains("type t.resonator.State = struct { sample_rate: F32, r: F32, b1: F32, b2: F32, y1: F32, y2: F32, poisoned: Bool }"),
        "{d}"
    );
    // ctl: Ctl lets in order, state ones stored; `w` is a plain local.
    let ctl = pos(&d, "rt fn t.resonator.ctl(");
    let tick = pos(&d, "rt fn t.resonator.tick(inout s: t.resonator.State, x: F32) -> F32 {");
    assert!(ctl < tick);
    assert!(d[ctl..tick].contains("s.1 = r\n"), "{d}");
    assert!(d[ctl..tick].contains("let w: F32 ="), "{d}");
    assert!(!d[ctl..tick].contains("= w\n"), "{d}");
    // tick: prev reads first, the output is materialised, then the stores in node order.
    let read_y1 = pos(&d, "= s.4\n");
    let read_y2 = pos(&d, "= s.5\n");
    let out = pos(&d, "let __out: F32 = y\n");
    let store_y1 = pos(&d, "  s.4 = y\n");
    let store_y2 = pos(&d, "  s.5 = y1");
    assert!(read_y1 < read_y2 && read_y2 < out && out < store_y1 && store_y1 < store_y2, "{d}");
    // init / reset / process / process_inplace / render exist with the §11.6 shapes.
    assert!(
        d.contains("fn t.resonator.init(cfg: t.resonator.Config, sample_rate: F32) -> t.resonator.State sret {"),
        "{d}"
    );
    assert!(d.contains("rt fn t.resonator.reset(inout s: t.resonator.State) -> () {\n  s.4 = 0.0:F32\n  s.5 = 0.0:F32\n  s.6 = false\n}"), "{d}");
    assert!(d.contains("rt fn t.resonator.process_inplace("), "{d}");
    assert!(d.contains("t.resonator.process(inout s, params, out, inout out)"), "{d}");
    assert!(d.contains("-> t.resonator.Out sret {"), "{d}");
    // Layout (T3-6): 6 × F32 + Bool, padded to the F32 alignment.
    let f = &m.flows[0];
    assert_eq!((f.layout.size, f.layout.bulk_size, f.layout.align), (28, 0, 4));
    assert_eq!(
        f.layout.fast_fields.iter().map(|x| x.name.as_str()).collect::<Vec<_>>(),
        ["sample_rate", "r", "b1", "b2", "y1", "y2", "poisoned"]
    );
    assert!(d.contains("const t.resonator.SIZE: U32 = 28:U32"), "{d}");
}

#[test]
fn process_reads_all_inputs_then_writes_all_outputs() {
    let d = text(RESONATOR);
    let process = pos(&d, "rt fn t.resonator.process(");
    let p = &d[process..];
    let len = pos(p, "let len: U32 = len(x");
    let check = pos(p, "if (len(out) != len) {\n    panic(\"span lengths differ\")");
    let ctl = pos(p, "t.resonator.ctl(inout s, params)");
    let read = pos(p, "[i]\n");
    let tick = pos(p, "t.resonator.tick(inout s, x");
    let write = pos(p, "out[i] = v");
    assert!(len < check && check < ctl && ctl < read && read < tick && tick < write, "{p}");
}

#[test]
fn delay_ring_buffer_order() {
    let d = text("pub flow dl(x: Sig[F32]) -> Sig[F32] {\n  let y = delay(x, 4, 0.0)\n  y\n}\n");
    assert!(d.contains("type t.dl.State = struct { y.buf: [F32; 4], y.w: U32, poisoned: Bool }"), "{d}");
    // init: buffer filled with init, w = 0.
    assert!(d.contains("s.0 = [0.0:F32; 4]\n  s.1 = 0:U32"), "{d}");
    // tick: output = buf[w], then (at the end) buf[w] = e, w = (w + 1) % N.
    let read = pos(&d, "= s.0[s.1]\n");
    let store = pos(&d, "s.0[s.1] = x\n");
    let advance = pos(&d, "s.1 = ((s.1 + 1:U32) % 4:U32)\n");
    assert!(read < store && store < advance, "{d}");
}

#[test]
fn vdelay_formula_order() {
    let d = text(
        "pub flow ec(x: Sig[F32], fb: Ctl[F32], t: Ctl[F32]) -> Sig[F32] {\n  let d = t * 100.0\n  let y = x + (fb * vdelay(y, d, 8, 0.0))\n  y\n}\n",
    );
    assert!(d.contains("vdelay_0.buf: [F32; 9], vdelay_0.w: U32"), "{d}");
    let tick = pos(&d, "rt fn t.ec.tick(");
    let t = &d[tick..];
    let mut last = 0;
    for name in ["vdelay_0.d", "vdelay_0.dc", "vdelay_0.k", "vdelay_0.f", "vdelay_0.wlk", "vdelay_0.a", "vdelay_0.b"] {
        let p = pos(t, &format!("let {name}: "));
        assert!(p > last, "{name} out of order in:\n{t}");
        last = p;
    }
    // dc clamps to [1, MAX] with NaN -> 1.0; k = trunc; f = dc - k; a and b read the ring.
    assert!(t.contains("if (vdelay_0.d >= 1.0:F32) {"), "{t}");
    assert!(t.contains("if (vdelay_0.d <= 8.0:F32) {"), "{t}");
    assert!(t.contains("trunc.F32.U32(vdelay_0.dc)"), "{t}");
    assert!(t.contains("(vdelay_0.dc - round.U32.F32(vdelay_0.k))"), "{t}");
    assert!(t.contains("(vdelay_0.wlk % 9:U32)"), "{t}");
    assert!(t.contains("((vdelay_0.wlk - 1:U32) % 9:U32)"), "{t}");
    assert!(t.contains("(((1.0:F32 - vdelay_0.f) * vdelay_0.a) + (vdelay_0.f * vdelay_0.b))"), "{t}");
    // The store and advance come after the output is materialised.
    let out = pos(t, "let __out");
    let store = pos(t, "] = y\n");
    let advance = pos(t, "% 9:U32)\n  __out\n}");
    assert!(out < store && store < advance, "{t}");
}

#[test]
fn echo_bulk_layout() {
    let src = "const MAX_ECHO: U32 = 96000\n\npub flow echo(x: Sig[F32], time: Ctl[F32], feedback: Ctl[F32]) -> Sig[F32] {\n  let d = time * sample_rate()\n  let y = x + (feedback * vdelay(y, d, MAX_ECHO, 0.0))\n  y\n}\n";
    let m = core_with(src, Some(4096));
    let f = &m.flows[0];
    assert_eq!(f.layout.bulk_size, 384004);
    assert_eq!(f.layout.bulk_fields.iter().map(|x| x.name.as_str()).collect::<Vec<_>>(), ["vdelay_0.buf"]);
    assert_eq!(
        f.layout.fast_fields.iter().map(|x| (x.name.as_str(), x.offset)).collect::<Vec<_>>(),
        [("bulk", 0), ("sample_rate", 8), ("feedback", 12), ("d", 16), ("vdelay_0.w", 20), ("poisoned", 24)]
    );
    assert_eq!((f.layout.size, f.layout.align), (32, 8));
    assert!(dump(&m).contains("const t.echo.BULK_SIZE: U32 = 384004:U32"));
    // Without a threshold everything is fast.
    let m = core_with(src, None);
    assert_eq!((m.flows[0].layout.size, m.flows[0].layout.bulk_size), (384024, 0));
}

#[test]
fn sub_instances_are_wired_per_phase() {
    let src = "pub flow saw(f0: Ctl[F32]) -> Sig[F32] {\n  let phase = prev(phase, 0.0) + (f0 / sample_rate())\n  phase\n}\n\npub flow smooth(x: Ctl[F32], time: Init[F32]) -> Sig[F32] {\n  let a = 1.0 / (time * sample_rate())\n  let y = x + (a * (prev(y, 0.0) - x))\n  y\n}\n\npub flow voice(f0: Ctl[F32], gain: Ctl[F32]) -> Sig[F32] {\n  let src = saw~(f0)\n  src * smooth~(gain, 0.01)\n}\n";
    let d = text(src);
    assert!(
        d.contains("type t.voice.State = struct { src: t.saw.State, smooth_0: t.smooth.State, poisoned: Bool }"),
        "{d}"
    );
    // init: sub inits with Config from the Init args; ctl: sub ctls with Params from the Ctl args; tick: sub ticks.
    assert!(d.contains("s.0 = t.saw.init(t.saw.Config {}, sample_rate)"), "{d}");
    assert!(d.contains("s.1 = t.smooth.init(t.smooth.Config { time: 0.01:F32 }, sample_rate)"), "{d}");
    assert!(d.contains("t.saw.ctl(inout s.0, t.saw.Params { f0: p.0 })"), "{d}");
    assert!(d.contains("t.smooth.ctl(inout s.1, t.smooth.Params { x: p.1 })"), "{d}");
    assert!(d.contains("= t.saw.tick(inout s.0)"), "{d}");
    assert!(d.contains("= t.smooth.tick(inout s.1)"), "{d}");
    assert!(d.contains("t.saw.reset(inout s.0)\n  t.smooth.reset(inout s.1)"), "{d}");
    // The sub states store the inputs they read at Sig and the Init let.
    assert!(d.contains("type t.saw.State = struct { sample_rate: F32, f0: F32, prev_0: F32, poisoned: Bool }"), "{d}");
    assert!(d.contains("type t.smooth.State = struct { x: F32, a: F32, prev_0: F32, poisoned: Bool }"), "{d}");
    // No Sig inputs: `process_inplace` is not generated, `render` takes `frames`.
    assert!(!d.contains("t.voice.process_inplace"), "{d}");
    assert!(d.contains("frames: U32, sample_rate: F32) -> t.voice.Out sret"), "{d}");
}

#[test]
fn par_replicates_state_and_loops() {
    let src = "use std.dsp.{sum}\n\nconst N: U32 = 4\n\npub flow saw(f0: Ctl[F32]) -> Sig[F32] {\n  let phase = prev(phase, 0.0) + (f0 / sample_rate())\n  phase\n}\n\npub flow uni(f0: Ctl[F32]) -> Sig[F32] {\n  let saws = par i in 0..N {\n    saw~(f0 * (1.0 + (i.round_f32() * 0.01)))\n  }\n  sum(saws)\n}\n";
    let d = text(src);
    assert!(d.contains("type t.uni.State = struct { saws: [t.uni.saws.State; 4], poisoned: Bool }"), "{d}");
    assert!(d.contains("type t.uni.saws.State = struct { saw_0: t.saw.State }"), "{d}");
    assert!(d.contains("for i in 0:U32..4:U32 {\n    s.0[i].0 = t.saw.init(t.saw.Config {}, sample_rate)"), "{d}");
    assert!(
        d.contains("t.saw.ctl(inout s.0[i].0, t.saw.Params { f0: (p.0 * (1.0:F32 + (round.U32.F32(i) * 0.01:F32))) })"),
        "{d}"
    );
    assert!(d.contains("= t.saw.tick(inout s.0[i].0)"), "{d}");
    assert!(d.contains("t.saw.reset(inout s.0[i].0)"), "{d}");
    assert!(d.contains("std.dsp.sum__4("), "{d}");
}

#[test]
fn planar_and_struct_outputs() {
    let src = "pub struct Stereo {\n  l: F32,\n  r: F32,\n}\n\npub flow pan(x: Sig[F32], p: Ctl[F32]) -> Sig[Stereo] {\n  Stereo { l: x * (1.0 - p), r: x * p }\n}\n\npub flow dup(x: Sig[[F32; 2]]) -> Sig[[F32; 2]] {\n  x\n}\n";
    let d = text(src);
    assert!(d.contains("inout l: Span[F32], inout r: Span[F32]) -> () {"), "{d}");
    assert!(d.contains("l[i] = v.0\n    r[i] = v.1"), "{d}");
    assert!(d.contains(": [Span[F32]; 2], inout out: [Span[F32]; 2]) -> () {"), "{d}");
    assert!(d.contains("[0:U32])\n  if (len(out[0:U32]) != len) {"), "{d}");
    assert!(d.contains("[0:U32][i], x"), "{d}");
    assert!(d.contains("[1:U32][i]]\n"), "{d}");
    assert!(d.contains("out[0:U32][i] = v[0:U32]\n    out[1:U32][i] = v[1:U32]"), "{d}");
    assert!(d.contains("t.pan.Out { l: l, r: r }"), "{d}");
}

#[test]
fn params_default_from_param_attributes() {
    let src =
        "pub flow g(x: Sig[F32], @param(min: 0.0, max: 1.0, default: 0.5) k: Ctl[F32]) -> Sig[F32] {\n  x * k\n}\n";
    let d = text(src);
    assert!(d.contains("fn t.g.params_default() -> t.g.Params sret {\n  t.g.Params { k: 0.5:F32 }\n}"), "{d}");
}
