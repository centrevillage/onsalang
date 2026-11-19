//! Unit tests for flow body checking (T3-1): rates, nodes, and E08xx.

use std::path::Path;

use onsa_diag::Code;

use crate::body::LocalId;
use crate::clock::{Clock, ClockStage, Ratio};
use crate::flow::{FlowInfo, InitArg, Owner, PlanKind};
use crate::tests::{check, codes_of as codes};
use crate::{Analysis, DefId};

fn ok(src: &str) -> Analysis {
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "unexpected diagnostics: {:?}", a.diagnostics);
    a
}

fn def(a: &Analysis, name: &str) -> DefId {
    DefId(a.defs.iter().position(|d| d.name == name).unwrap_or_else(|| panic!("no def {name}")) as u32)
}

fn flow<'a>(a: &'a Analysis, name: &str) -> &'a FlowInfo {
    let f = &a.flows[&def(a, name)];
    assert!(f.complete, "flow {name} incomplete");
    f
}

/// The paths of the nodes no `par~` holds, in their order (§11.6).
fn top_names(f: &FlowInfo) -> Vec<&str> {
    f.top().map(|id| f.node(id).path.as_str()).collect()
}

/// The `i`-th node no `par~` holds.
fn top_kind(f: &FlowInfo, i: usize) -> &PlanKind {
    &f.node(f.top().nth(i).unwrap_or_else(|| panic!("no node {i}"))).kind
}

fn let_rate(f: &FlowInfo, name: &str) -> (Clock, bool) {
    let l = f.lets.iter().find(|l| l.name.as_deref() == Some(name)).unwrap_or_else(|| panic!("no let {name}"));
    (l.clock, l.state)
}

fn spec(path: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec").join(path)).unwrap()
}

const RESONATOR: &str = r#"
use std.math.{exp, cos}

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
"#;

// ---------------------------------------------------------------- spec examples

#[test]
fn spec_flow_examples_check_clean() {
    for p in ["flow/one_pole.onsa", "flow/unison.onsa", "flow/gain.onsa", "examples/voice.onsa"] {
        let a = check(&spec(p));
        assert!(a.diagnostics.is_empty(), "{p}: {:?}", a.diagnostics);
    }
}

/// Each generated type of a flow is named by [`crate::def::FlowTy::name`]
/// (K8 of W4-18): the later stages select it by its `FlowTy`, and show that
/// name; the types are there, each once (`resonator` has no input of
/// `init`, so no `Config`, §11.6, S-112; one input of `sample`, so no `In`,
/// and a scalar output, so no `Out`, S-30, S-1087).
#[test]
fn the_generated_types_are_named_by_their_role() {
    use crate::def::{DefKind, FlowTy};
    let a = ok(RESONATOR);
    let fd = a.def(def(&a, "resonator")).as_flow().unwrap();
    let mut tys = Vec::new();
    for &(ref name, d) in &fd.members {
        if let DefKind::Struct(s) = &a.def(d).kind
            && let Some(t) = s.flow_ty
        {
            assert_eq!(t.name(), name);
            tys.push(t);
        }
    }
    assert_eq!(tys, [FlowTy::State, FlowTy::Params, FlowTy::Rendered]);
}

#[test]
fn resonator_rates_and_state() {
    let a = ok(RESONATOR);
    let f = flow(&a, "resonator");
    // `r` is read at `sample` only in `1.0 - r`, hoisted to `block` (§11.3).
    assert_eq!(let_rate(f, "r"), (Clock::Block, false));
    assert_eq!(let_rate(f, "w"), (Clock::Block, false));
    assert_eq!(let_rate(f, "b1"), (Clock::Block, true));
    assert_eq!(let_rate(f, "b2"), (Clock::Block, true));
    assert_eq!(let_rate(f, "y1"), (Clock::SAMPLE, false));
    assert_eq!(let_rate(f, "y2"), (Clock::SAMPLE, false));
    assert_eq!(let_rate(f, "y"), (Clock::SAMPLE, false));
    // Two `prev` nodes named by their `let`s, constant inits.
    assert_eq!(top_names(f), vec!["y1", "y2"]);
    assert!(matches!(top_kind(f, 0), PlanKind::Prev { init: InitArg::Const(_), .. }));
    // `sample_rate()` is read at Ctl rate: stored in the state (S-05).
    assert_eq!(f.sample_rate_at, Some(ClockStage::Block));
    assert_eq!(f.sample_rate_calls.len(), 2);
    assert_eq!(
        f.hoists.iter().map(|h| (h.path.as_str(), h.stage)).collect::<Vec<_>>(),
        [("y._hoist_0", ClockStage::Block)]
    );
    assert_eq!(f.inputs.len(), 3);
    assert_eq!(f.clocks.locals[&f.inputs[0]], Clock::SAMPLE);
    assert_eq!(f.clocks.locals[&f.inputs[1]], Clock::Block);
    assert_eq!(f.clocks.exprs[&f.output.unwrap()], Clock::SAMPLE);
}

#[test]
fn smooth_init_let_is_state() {
    let a = ok(r#"
use std.math.{exp}

pub flow smooth(x: F32 at block, time: F32 at init) -> F32 at sample {
  let a = exp(-1.0 / (time * sample_rate()))
  let y = x + (a * (prev~(^y) - x))
  y
}
"#);
    let f = flow(&a, "smooth");
    assert_eq!(let_rate(f, "a"), (Clock::Init, true));
    assert_eq!(let_rate(f, "y"), (Clock::SAMPLE, false));
    assert_eq!(f.sample_rate_at, Some(ClockStage::Init));
    assert_eq!(top_names(f), vec!["y.prev_0"]);
}

#[test]
fn voice_instances_are_named() {
    let a = ok(&spec("examples/voice.onsa"));
    let f = flow(&a, "voice");
    assert_eq!(top_names(f), vec!["src", "f1", "f2", "_out.smooth_0"]);
    assert!(
        matches!(top_kind(f, 1), PlanKind::Instance { callee, args, .. } if a.def(*callee).name == "resonator" && args.len() == 3)
    );
    assert_eq!(f.node_of.len(), 4);
    // `saw`: the `prev` inside `wrap01(...)` is qualified by its `let`;
    // `f0 / sample_rate()` is hoisted to `block` (§11.3).
    let saw = flow(&a, "saw");
    assert_eq!(top_names(saw), vec!["phase.prev_0"]);
    assert_eq!(saw.sample_rate_at, Some(ClockStage::Block));
}

#[test]
fn echo_vdelay_from_const() {
    let a = ok(&spec("examples/voice.onsa"));
    let f = flow(&a, "echo");
    assert_eq!(let_rate(f, "d"), (Clock::Block, true));
    assert_eq!(top_names(f)[0], "y.vdelay_0");
    assert!(matches!(top_kind(f, 0), PlanKind::Vdelay { max: 96000, init: InitArg::Const(_), .. }));
}

#[test]
fn unison_par_nests_instances() {
    let a = ok(&spec("flow/unison.onsa"));
    let f = flow(&a, "unison");
    assert_eq!(let_rate(f, "saws"), (Clock::SAMPLE, false));
    let par = f.top().next().expect("a node");
    let PlanKind::Par { from, count, var, .. } = &f.node(par).kind else { panic!("expected par: {:?}", f.nodes) };
    assert_eq!((f.node(par).name.as_str(), *from, *count), ("saws", 0, 4));
    let inner: Vec<(&str, &str)> =
        f.roots(Owner::Par(par)).iter().map(|&id| (f.node(id).name.as_str(), f.node(id).path.as_str())).collect();
    assert_eq!(inner, vec![("saw_0", "saws.saw_0")]);
    assert_eq!(f.clocks.locals[var], Clock::Init);
}

// ---------------------------------------------------------------- rates

#[test]
fn at_promotes_and_cannot_lower() {
    let a = ok("pub flow f(p: F32 at block) -> F32 at sample {\n  let ps = p at sample\n  prev~(ps)\n}\n");
    let f = flow(&a, "f");
    assert_eq!(let_rate(f, "ps"), (Clock::SAMPLE, false));
    // `at` does not make a value slower: E0815 (§11.3; the annotation of the
    // draft was E0810).
    assert_eq!(
        codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let c = x at block\n  c\n}\n"),
        vec![Code::E0815]
    );
}

#[test]
fn match_and_if_are_pointwise() {
    let a = ok(
        "pub flow f(x: F32 at sample, g: Bool at block) -> F32 at sample {\n  let y = if g { x } else { 0.0 }\n  let o = match Some(y) {\n    Some(v) => v,\n    None => 1.0,\n  }\n  o\n}\n",
    );
    let f = flow(&a, "f");
    assert_eq!(let_rate(f, "y"), (Clock::SAMPLE, false));
    assert_eq!(let_rate(f, "o"), (Clock::SAMPLE, false));
}

#[test]
fn non_rt_function_only_at_init() {
    let src = "pub fn make(n: F32) -> F32 { n * 2.0 }\npub flow f(t: F32 at init, c: F32 at block) -> F32 at sample {\n  let a = make(t)\n  let b = make(2.0)\n  a + b + c\n}\n";
    let a = ok(src);
    let f = flow(&a, "f");
    // Read only in `a + b`, hoisted to `init` in `a + b + c`, hoisted to
    // `block` (§11.3).
    assert_eq!(let_rate(f, "a"), (Clock::Init, false));
    assert_eq!(let_rate(f, "b"), (Clock::Init, false));
    assert_eq!(
        f.hoists.iter().map(|h| (h.path.as_str(), h.stage)).collect::<Vec<_>>(),
        [("_out._hoist_0", ClockStage::Block), ("_out._hoist_1", ClockStage::Init)]
    );
    assert_eq!(
        codes("pub fn make(n: F32) -> F32 { n * 2.0 }\npub flow f(c: F32 at block) -> F32 at sample {\n  make(c)\n}\n"),
        vec![Code::E0815]
    );
}

#[test]
fn constant_lets_are_never_state() {
    let a = ok("pub flow f(x: F32 at sample) -> F32 at sample {\n  let two = 2.0\n  x * two\n}\n");
    assert_eq!(let_rate(flow(&a, "f"), "two"), (Clock::Const, false));
}

// ---------------------------------------------------------------- reads

/// The highest rate at which the one local named `name` is read
/// (`FlowInfo::read_at`; `None`: never read).
fn read_at(f: &FlowInfo, name: &str) -> Option<ClockStage> {
    let ids: Vec<usize> = f.body.locals.iter().enumerate().filter(|(_, l)| l.name == name).map(|(i, _)| i).collect();
    assert_eq!(ids.len(), 1, "locals named {name}");
    f.read_at.get(&LocalId(ids[0] as u32)).and_then(|rs| rs.last()).copied()
}

#[test]
fn read_at_inputs() {
    let a = ok(
        "pub flow f(x: F32 at sample, c: F32 at block, k: F32 at block, t: F32 at init, u: F32 at init) -> F32 at sample {\n  let a = c * k\n  let y = prev~(x, t)\n  (y * a) + c\n}\n",
    );
    let f = flow(&a, "f");
    // The first argument of a delay at `Sig`, its `init` at `Init`.
    assert_eq!(read_at(f, "x"), Some(ClockStage::Tick(Ratio(0))));
    assert_eq!(read_at(f, "t"), Some(ClockStage::Init));
    // `c` is read at `Ctl` in `a` and at `Sig` in the output: the faster.
    assert_eq!(read_at(f, "c"), Some(ClockStage::Tick(Ratio(0))));
    assert_eq!(read_at(f, "k"), Some(ClockStage::Block));
    assert_eq!(read_at(f, "u"), None);
}

#[test]
fn read_at_lets() {
    let a = ok(
        "pub flow g(k: F32 at block) -> F32 at sample { k }\npub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let a = c * 2.0\n  let b = a + 1.0\n  let s = g~(b)\n  let y = x + prev~(^y)\n  let _ = y\n  let e = a + x\n  let d = a * c\n  e + d + s\n}\n",
    );
    let f = flow(&a, "f");
    // Read at `Ctl` in `b`, at `Sig` in `e` and at `Ctl` again in `d` after
    // it: the fastest read, not the last, and so state (S-05).
    assert_eq!(read_at(f, "a"), Some(ClockStage::Tick(Ratio(0))));
    assert_eq!(let_rate(f, "a"), (Clock::Block, true));
    // An instance argument is read at the rate of the callee's input.
    assert_eq!(read_at(f, "b"), Some(ClockStage::Block));
    assert_eq!(let_rate(f, "b"), (Clock::Block, false));
    assert_eq!(read_at(f, "s"), Some(ClockStage::Tick(Ratio(0))));
    // `y` is read by `^y`, in the first argument of a delay, at `Sig`, and by
    // a `let _` of its clock (a `let` read only by `^y` is unused, §5.1).
    assert_eq!(read_at(f, "y"), Some(ClockStage::Tick(Ratio(0))));
}

#[test]
fn read_at_constant_lets() {
    let a = ok(
        "const K: I32 = 2\npub flow f(x: I32 at sample, p: I32 at block, c: I32 at init) -> I32 at sample {\n  let l0 = K\n  let l1 = l0\n  let b = l1 * l1\n  let _ = l0 + 1\n  let t = c * l0\n  let q = p * l0\n  x + b + t + q\n}\n",
    );
    let f = flow(&a, "f");
    let rates = |name: &str| {
        let id = f.body.locals.iter().position(|l| l.name == name).unwrap();
        f.read_at.get(&LocalId(id as u32)).map(|rs| rs.iter().copied().collect::<Vec<_>>())
    };
    use ClockStage::*;
    // Every stage, not the latest alone: `l0` is defined in `init`, `ctl`
    // and `tick` (R-488, §11.3). The read of the constant `let _` is at
    // `init`, the stage of a constant read (`flow/reads.rs`).
    assert_eq!(rates("l0"), Some(vec![Init, Block, Tick(Ratio(0))]));
    // A constant `let` read by a constant `let` at the stages of the reader.
    assert_eq!(rates("l1"), Some(vec![Tick(Ratio(0))]));
    assert_eq!(rates("b"), Some(vec![Tick(Ratio(0))]));
}

#[test]
fn read_at_a_constant_let_read_only_by_an_underscore_is_init() {
    // `l` is read by nothing but a `let _` of a constant, which no stage reads (a `let` that is read by nothing is an E0309, §5.1), so the
    // stages that read `l` are the constant read's alone: `Init` (`flow/reads.rs`), not a stage of the flow's output.
    let a =
        ok("const K: I32 = 2\npub flow f(x: I32 at sample) -> I32 at sample {\n  let l = K\n  let _ = l + 1\n  x\n}\n");
    let f = flow(&a, "f");
    let id = f.body.locals.iter().position(|l| l.name == "l").unwrap();
    let rates = f.read_at.get(&LocalId(id as u32)).map(|rs| rs.iter().copied().collect::<Vec<_>>());
    assert_eq!(rates, Some(vec![ClockStage::Init]));
}

#[test]
fn read_at_par_variables() {
    let a = ok(
        "use std.math.{sum}\npub flow g(k: F32 at block) -> F32 at sample { k }\npub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let p = par~ i in 0..<2 { g~(c + F32.round_from(i)) }\n  let q = par~ j in 0..<2 { x * F32.round_from(j) }\n  sum(p) + sum(q)\n}\n",
    );
    let f = flow(&a, "f");
    // `i` in an argument of an instance whose input is at `block`.
    assert_eq!(read_at(f, "i"), Some(ClockStage::Block));
    assert_eq!(read_at(f, "j"), Some(ClockStage::Tick(Ratio(0))));
}

#[test]
fn read_at_match_bindings() {
    let a = ok(
        "pub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let m = match Some(c) {\n    Some(v) => v,\n    None => 0.0,\n  }\n  let n = match Some(x) {\n    Some(w) => w * m,\n    None => 0.0,\n  }\n  n\n}\n",
    );
    let f = flow(&a, "f");
    assert_eq!(read_at(f, "v"), Some(ClockStage::Block));
    assert_eq!(read_at(f, "w"), Some(ClockStage::Tick(Ratio(0))));
    assert_eq!(read_at(f, "m"), Some(ClockStage::Tick(Ratio(0))));
    assert_eq!(let_rate(f, "m"), (Clock::Block, true));
}

/// The kinds of the locals of a flow body, as the table of `flow.rs` gives
/// them: the inputs first, in their order, as borrowed parameters.
#[test]
fn locals_have_the_kinds_of_the_table() {
    use crate::body::LocalKind;
    let a = ok(
        "pub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let p = par~ i in 0..<2 { x }\n  let m = match Some(c) {\n    Some(v) => v,\n    None => 0.0,\n  }\n  p[0] + m\n}\n",
    );
    let f = flow(&a, "f");
    let kinds: Vec<(&str, LocalKind)> = f.body.locals.iter().map(|l| (l.name.as_str(), l.kind)).collect();
    let borrow = LocalKind::Param(onsa_syntax::ast::Mode::Borrow);
    assert_eq!(&kinds[..2], &[("x", borrow), ("c", borrow)]);
    let of = |name: &str| kinds.iter().find(|(n, _)| *n == name).map(|&(_, k)| k);
    assert_eq!(of("p"), Some(LocalKind::Let));
    assert_eq!(of("i"), Some(LocalKind::Let));
    assert_eq!(of("v"), Some(LocalKind::MatchBind));
}

// ---------------------------------------------------------------- diagnostics

#[test]
fn e0801_forward_reference() {
    assert_eq!(
        codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = b\n  let b = x\n  a\n}\n"),
        vec![Code::E0801]
    );
    // Its own initializer, outside a look-back.
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let y = x + y\n  y\n}\n"), vec![Code::E0801]);
    // Look-back through a function call in the first argument is fine.
    ok(
        "pub rt fn id(x: F32) -> F32 { x }\npub flow f(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(id(^y))\n  y\n}\n",
    );
}

#[test]
fn e0805_effects() {
    assert_eq!(
        codes(
            "pub fn alloc_it() -> F32 uses {Alloc} { 1.0 }\npub flow f(x: F32 at sample) -> F32 at sample {\n  x * alloc_it()\n}\n"
        ),
        vec![Code::E0805]
    );
}

#[test]
fn e0806_forms() {
    for body in [
        "var a = 1.0\n  a",
        "let a = x\n  a = x\n  a",
        "for i in 0..<4 { }\n  x",
        "while true { }\n  x",
        "return x",
        "assert true\n  x",
        "let g = fn(v: F32) -> F32 { v }\n  x",
        "let a = move x\n  a",
        "let a = if true { let b = x\n b } else { x }\n  a",
        "x\n  x",
    ] {
        let src = format!("pub flow f(x: F32 at sample) -> F32 at sample {{\n  {body}\n}}\n");
        assert_eq!(codes(&src), vec![Code::E0806], "{body}");
    }
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = x\n}\n"), vec![Code::E0806]);
}

#[test]
fn e0807_e0808_delay_lengths() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {\n  delay~(x, 1)\n}\n";
    let a = check(src);
    assert_eq!(a.diagnostics[0].code, Code::E0807);
    assert_eq!(crate::fixed_region(src, &a.diagnostics[0], 0), "prev~(x)");
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  delay~(x, 0)\n}\n"), vec![Code::E0808]);
    // Not a constant: E0417 (§11.4).
    assert_eq!(
        codes("pub flow f(x: F32 at sample, n: U32 at init) -> F32 at sample {\n  delay~(x, n)\n}\n"),
        vec![Code::E0417]
    );
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  vdelay~(x, 2.0, 0)\n}\n"), vec![Code::E0808]);
    // The `[F32; 0]` output is its own E0810 at the heading (S-1110, S-407).
    assert_eq!(
        codes("pub flow f(x: F32 at sample) -> [F32; 0] at sample {\n  par~ i in 2..<2 { x }\n}\n"),
        vec![Code::E0808, Code::E0810]
    );
    // An `init` written as the default value is accepted too (S-539 (c3a)).
    ok(
        "const N: U32 = 8\npub flow f(x: F32 at sample) -> F32 at sample {\n  prev~(x, 0.0) + delay~(x, N, 0.0) + vdelay~(x, 2.0, N, 0.0)\n}\n",
    );
}

#[test]
fn par_ranges() {
    let par = |ret: &str, head: &str| {
        codes(&format!(
            "pub flow f(x: F32 at sample, n: U32 at init) -> {ret} at sample {{\n  par~ i in {head} {{ x }}\n}}\n"
        ))
    };
    // The bounds: integer constants (§7 E0401, §11.5 E0417), not empty (E0808).
    assert_eq!(par("[F32; 2]", "0.0..<2.0"), vec![Code::E0401]);
    assert_eq!(par("[F32; 2]", "0..<n"), vec![Code::E0417]);
    // The `[F32; 0]` output is its own E0810 at the heading (S-1110, S-407).
    assert_eq!(par("[F32; 0]", "3..=2"), vec![Code::E0808, Code::E0810]);
    // `..=` gives `b - a + 1` instances (S-257), one for `2..=2`; a count past
    // `U32` is E0808 for now (S-1147).
    assert_eq!(par("[F32; 1]", "2..=2"), vec![]);
    assert_eq!(par("[F32; 3]", "0..=2"), vec![]);
    assert_eq!(par("[F32; 2]", "0..=4294967295"), vec![Code::E0808]);
    // Not read by the modes (a local is no constant): no move happens in a
    // `par` head, unlike a `for` head (R-194).
    assert_eq!(par("[F32; 2]", "0..<n.min(2)"), vec![Code::E0417]);
    // The forms of §4.5 that this version does not compute: E0200 until
    // W9-03 (R-195); a prefix `-` on a `U32` is E0401 (S-228).
    assert_eq!(par("[F32; 4]", "0..<3 + 1"), vec![Code::E0200]);
    assert_eq!(par("[F32; 4]", "0..<(2 * 2)"), vec![Code::E0200]);
    assert_eq!(par("[F32; 4]", "(0)..<(4)"), vec![]);
    assert_eq!(par("[F32; 3]", "-1..<2"), vec![Code::E0401]);
    assert_eq!(par("[F32; 2]", "0..<n + 1"), vec![Code::E0417]);
    let computed = "const N: U32 = 2\nconst M: U32 = N * 2\npub flow f(x: F32 at sample) -> [F32; 4] at sample {\n  par~ i in 0..<M { x }\n}\n";
    assert_eq!(codes(computed), vec![Code::E0200]);
    let delay = "const N: U32 = 4\npub flow f(x: F32 at sample) -> F32 at sample {\n  delay~(x, N + 1)\n}\n";
    assert_eq!(codes(delay), vec![Code::E0200]);
    // The names of the leaves are resolved first (§18.1): a name that is not
    // declared is E0302, a function is no constant (E0417).
    let g = "pub fn g() -> U32 { 3 }\npub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  par~ i in 0..<g + 1 { x }\n}\n";
    assert_eq!(codes(g), vec![Code::E0417]);
    assert_eq!(par("[F32; 2]", "0..<zzz + 1"), vec![Code::E0302]);
    assert_eq!(par("[F32; 2]", "0..<1 + zzz"), vec![Code::E0302]);
    assert_eq!(par("[F32; 2]", "0..<n + zzz"), vec![Code::E0302]);
    // An associated constant of std is a constant (§6.6): `I32.BITS` as `N`.
    assert_eq!(par("[F32; 32]", "0..<I32.BITS"), vec![]);
    assert_eq!(par("[F32; 2]", "0..<F32.PI"), vec![Code::E0401]);
    let bits = "pub flow f(x: F32 at sample) -> F32 at sample {\n  delay~(x, I32.BITS)\n}\n";
    assert_eq!(codes(bits), vec![]);
    // A float literal among the operands is a type error (E0401).
    let float = "const N: U32 = 2\npub flow f(x: F32 at sample) -> F32 at sample {\n  delay~(x, N + 1.5)\n}\n";
    assert_eq!(codes(float), vec![Code::E0401]);
    assert_eq!(par("[F32; 2]", "-1.5..<3"), vec![Code::E0401]);
    // A literal that no `U32` holds is E0408 in a computed expression too.
    assert_eq!(par("[F32; 2]", "0..<4294967296"), vec![Code::E0408]);
    assert_eq!(par("[F32; 2]", "0..<4294967296 + 1"), vec![Code::E0408]);
    let big = "const N: U32 = 2\npub flow f(x: F32 at sample) -> [F32; 2] at sample {\n  par~ i in 0..<N + 4294967296 { x }\n}\n";
    assert_eq!(codes(big), vec![Code::E0408]);
}

#[test]
fn e0810_non_copy_let() {
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let s = \"a\"\n  x\n}\n"), vec![Code::E0810]);
}

#[test]
fn e0811_e0812_marks() {
    let src = "pub flow g(x: F32 at sample) -> F32 at sample { x }\npub flow f(x: F32 at sample) -> F32 at sample {\n  g(x)\n}\n";
    let a = check(src);
    assert_eq!(a.diagnostics[0].code, Code::E0811);
    assert_eq!(crate::fixed_region(src, &a.diagnostics[0], 0), "g~(x)");
    let src = "pub rt fn h(x: F32) -> F32 { x }\npub flow f(x: F32 at sample) -> F32 at sample {\n  h~(x)\n}\n";
    let a = check(src);
    assert_eq!(a.diagnostics[0].code, Code::E0812);
    assert_eq!(crate::fixed_region(src, &a.diagnostics[0], 0), "h(x)");
    // A delay is written `prev~(` (S-44); `prev(` is E0811 with the candidate `~`.
    ok("pub flow f(x: F32 at sample) -> F32 at sample {\n  prev~(x)\n}\n");
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {\n  prev(x)\n}\n";
    let a = check(src);
    assert_eq!(a.diagnostics[0].code, Code::E0811);
    assert_eq!(crate::fixed_region(src, &a.diagnostics[0], 0), "prev~(x)");
}

#[test]
fn e0813_e0815_delay_argument_rates() {
    let src = "pub flow f(p: F32 at block) -> F32 at sample {\n  prev~(p)\n}\n";
    let a = check(src);
    assert_eq!(a.diagnostics[0].code, Code::E0813);
    assert_eq!(crate::fixed_region(src, &a.diagnostics[0], 0), "p at sample");
    // The `init` of a delay is faster than `init`: E0815 (S-147; E0814 is retired).
    assert_eq!(
        codes("pub flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {\n  prev~(x, p)\n}\n"),
        vec![Code::E0815]
    );
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  prev~(x, x)\n}\n"), vec![Code::E0815]);
    ok("pub flow f(x: F32 at sample, t: F32 at init) -> F32 at sample {\n  prev~(x, t)\n}\n");
    let a =
        ok("pub flow f(x: F32 at sample, t: F32 at init) -> F32 at sample {\n  let y = prev~(x, t * 2.0)\n  y\n}\n");
    assert!(matches!(top_kind(flow(&a, "f"), 0), PlanKind::Prev { init: InitArg::Init(_), .. }));
}

/// The omitted `init` (§11.4, S-29): a literal of a number, `Default` of
/// another type that satisfies the bound, E0816 of one that does not; of a
/// value type that is not Copy, E0810 alone (S-1155, provisional).
#[test]
fn the_omitted_init_is_the_default_of_the_value_type() {
    let flow_of = |t: &str, e: &str| {
        format!(
            "pub rt fn k(v: {t}) -> F32 {{ 1.0 }}\npub flow f(x: F32 at sample) -> F32 at sample {{\n  x * k(prev~({e}))\n}}\n"
        )
    };
    let a = ok(&flow_of("F32", "x"));
    assert!(matches!(top_kind(flow(&a, "f"), 0), PlanKind::Prev { init: InitArg::Const(_), .. }));
    let char = "if x > 0.0 { 'a' } else { 'b' }";
    for (t, e) in [("Bool", "x > 0.0"), ("[F32; 2]", "[x, x]"), ("(F32, Bool)", "(x, x > 0.0)"), ("[F32; 0]", "[x; 0]")]
    {
        let a = ok(&flow_of(t, e));
        assert!(matches!(top_kind(flow(&a, "f"), 0), PlanKind::Prev { init: InitArg::Default, .. }), "{t}");
    }
    assert_eq!(codes(&flow_of("Char", char)), vec![Code::E0816]);
    assert_eq!(codes(&flow_of("[Char; 0]", &format!("[{char}; 0]"))), vec![Code::E0816]);
    let some = "if x > 0.0 { Some(\"a\") } else { None }";
    assert_eq!(codes(&flow_of("Option[Str]", some)), vec![Code::E0810]);
}

#[test]
fn e0815_argument_rate_too_high() {
    assert_eq!(
        codes(
            "pub flow g(c: F32 at block) -> F32 at sample { prev~(x) }\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x)\n}\n"
        )
        .iter()
        .filter(|&&c| c == Code::E0815)
        .count(),
        1
    );
    assert_eq!(
        codes(
            "pub flow g(t: F32 at init, x: F32 at sample) -> F32 at sample { x * t }\npub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  g~(c, x)\n}\n"
        ),
        vec![Code::E0815]
    );
}

#[test]
fn e0412_instance_arity_and_e0401_type() {
    assert_eq!(
        codes(
            "pub flow g(x: F32 at sample) -> F32 at sample { x }\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x, x)\n}\n"
        ),
        vec![Code::E0412]
    );
    assert_eq!(
        codes(
            "pub flow g(x: F32 at sample) -> F32 at sample { x }\npub flow f(x: I32 at sample) -> F32 at sample {\n  g~(x)\n}\n"
        ),
        vec![Code::E0401]
    );
}

#[test]
fn let_patterns_destructure() {
    let a = ok(
        "pub struct P { l: F32, r: F32 }\npub rt fn mk(x: F32) -> P { P { l: x, r: x } }\npub flow f(x: F32 at sample) -> F32 at sample {\n  let P { l: l, r: r } = mk(x)\n  let (a, b) = (l, r)\n  a + b\n}\n",
    );
    let f = flow(&a, "f");
    assert_eq!(f.lets.len(), 2);
    assert_eq!(f.lets[0].locals.len(), 2);
    assert_eq!(f.lets[0].clock, Clock::SAMPLE);
    assert!(f.lets[0].name.is_none());
}

#[test]
fn no_shadowing_in_flows() {
    assert_eq!(codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let x = 1.0\n  x\n}\n"), vec![Code::E0304]);
    assert_eq!(
        codes("pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = x\n  let a = x\n  a\n}\n"),
        vec![Code::E0304]
    );
}
