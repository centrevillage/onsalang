//! Unit tests for flow body checking (T3-1): rates, nodes, and E08xx.

use std::path::Path;

use onsa_diag::{Code, FileId};

use crate::flow::{FlowInfo, FlowRate, InitArg, Node};
use crate::{Analysis, DefId, Module, Package, analyze};

/// The standard library from the repository's `std/` directory (D-07), so that
/// the spec examples (`use std.math.{exp, cos}`) check here as they do in the driver.
fn std_package() -> Package {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let files = [("math", "math.onsa"), ("dsp", "dsp.onsa"), ("dsp.test", "dsp/test.onsa"), ("array", "array.onsa")];
    let modules = files
        .iter()
        .enumerate()
        .map(|(i, (path, file))| {
            let text = std::fs::read_to_string(root.join(file)).unwrap();
            let id = FileId(100 + i as u32);
            Module { path: path.to_string(), file: id, text: text.clone(), parsed: onsa_syntax::parse(id, &text) }
        })
        .collect();
    Package { name: "std".into(), modules, deps: Vec::new(), is_std: true }
}

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        path: "main".into(),
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package { name: "t".into(), modules, deps: vec![std_package()], is_std: false })
}

fn codes(src: &str) -> Vec<Code> {
    let a = check(src);
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

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

fn let_rate(f: &FlowInfo, name: &str) -> (FlowRate, bool) {
    let l = f.lets.iter().find(|l| l.name.as_deref() == Some(name)).unwrap_or_else(|| panic!("no let {name}"));
    (l.rate, l.state)
}

fn spec(path: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec").join(path)).unwrap()
}

const RESONATOR: &str = r#"
use std.math.{exp, cos}

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
"#;

// ---------------------------------------------------------------- spec examples

#[test]
fn spec_flow_examples_check_clean() {
    for p in ["flow/one_pole.onsa", "flow/unison.onsa", "flow/gain.onsa", "examples/voice.onsa"] {
        let a = check(&spec(p));
        assert!(a.diagnostics.is_empty(), "{p}: {:?}", a.diagnostics);
    }
}

#[test]
fn resonator_rates_and_state() {
    let a = ok(RESONATOR);
    let f = flow(&a, "resonator");
    assert_eq!(let_rate(f, "r"), (FlowRate::Ctl, true));
    assert_eq!(let_rate(f, "w"), (FlowRate::Ctl, false));
    assert_eq!(let_rate(f, "b1"), (FlowRate::Ctl, true));
    assert_eq!(let_rate(f, "b2"), (FlowRate::Ctl, true));
    assert_eq!(let_rate(f, "y1"), (FlowRate::Sig, false));
    assert_eq!(let_rate(f, "y2"), (FlowRate::Sig, false));
    assert_eq!(let_rate(f, "y"), (FlowRate::Sig, false));
    // Two `prev` nodes named by their `let`s, constant inits.
    let names: Vec<&str> = f.nodes.iter().map(|n| n.name()).collect();
    assert_eq!(names, vec!["y1", "y2"]);
    assert!(matches!(&f.nodes[0], Node::Prev { init: InitArg::Const(_), .. }));
    // `sample_rate()` is read at Ctl rate: stored in the state (S-05).
    assert_eq!(f.sample_rate_at, Some(FlowRate::Ctl));
    assert_eq!(f.sample_rate_calls.len(), 2);
    assert_eq!(f.inputs.len(), 3);
    assert_eq!(f.local_rates[&f.inputs[0]], FlowRate::Sig);
    assert_eq!(f.local_rates[&f.inputs[1]], FlowRate::Ctl);
    assert_eq!(f.expr_rates[&f.output.unwrap()], FlowRate::Sig);
}

#[test]
fn smooth_init_let_is_state() {
    let a = ok(r#"
use std.math.{exp}

pub flow smooth(x: Ctl[F32], time: Init[F32]) -> Sig[F32] {
  let a = exp(-1.0 / (time * sample_rate()))
  let y = x + (a * (prev(y, 0.0) - x))
  y
}
"#);
    let f = flow(&a, "smooth");
    assert_eq!(let_rate(f, "a"), (FlowRate::Init, true));
    assert_eq!(let_rate(f, "y"), (FlowRate::Sig, false));
    assert_eq!(f.sample_rate_at, Some(FlowRate::Init));
    assert_eq!(f.nodes.iter().map(|n| n.name()).collect::<Vec<_>>(), vec!["prev_0"]);
}

#[test]
fn voice_instances_are_named() {
    let a = ok(&spec("examples/voice.onsa"));
    let f = flow(&a, "voice");
    let names: Vec<&str> = f.nodes.iter().map(|n| n.name()).collect();
    assert_eq!(names, vec!["src", "f1", "f2", "smooth_0"]);
    assert!(
        matches!(&f.nodes[1], Node::Instance { callee, args, .. } if a.def(*callee).name == "resonator" && args.len() == 3)
    );
    assert_eq!(f.node_of_expr.len(), 4);
    // `saw`: the `prev` inside `wrap01(...)` is unnamed.
    let saw = flow(&a, "saw");
    assert_eq!(saw.nodes.iter().map(|n| n.name()).collect::<Vec<_>>(), vec!["prev_0"]);
    assert_eq!(saw.sample_rate_at, Some(FlowRate::Sig));
}

#[test]
fn echo_vdelay_from_const() {
    let a = ok(&spec("examples/voice.onsa"));
    let f = flow(&a, "echo");
    assert_eq!(let_rate(f, "d"), (FlowRate::Ctl, true));
    assert!(
        matches!(&f.nodes[0], Node::Vdelay { name, max: 96000, init: InitArg::Const(_), .. } if name == "vdelay_0")
    );
}

#[test]
fn unison_par_nests_instances() {
    let a = ok(&spec("flow/unison.onsa"));
    let f = flow(&a, "unison");
    assert_eq!(let_rate(f, "saws"), (FlowRate::Sig, false));
    let Node::Par { name, from, to, nodes, .. } = &f.nodes[0] else { panic!("expected par: {:?}", f.nodes) };
    assert_eq!((name.as_str(), *from, *to), ("saws", 0, 4));
    assert_eq!(nodes.iter().map(|n| n.name()).collect::<Vec<_>>(), vec!["saw_0"]);
    let Node::Par { var, .. } = &f.nodes[0] else { unreachable!() };
    assert_eq!(f.local_rates[var], FlowRate::Init);
}

// ---------------------------------------------------------------- rates

#[test]
fn annotation_promotes_and_cannot_lower() {
    let a = ok("pub flow f(p: Ctl[F32]) -> Sig[F32] {\n  let ps: Sig[F32] = p\n  prev(ps, 0.0)\n}\n");
    let f = flow(&a, "f");
    assert_eq!(let_rate(f, "ps"), (FlowRate::Sig, false));
    assert_eq!(f.lets[0].annotated, Some(FlowRate::Sig));
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let c: Ctl[F32] = x\n  c\n}\n"), vec![Code::E0810]);
}

#[test]
fn match_and_if_are_pointwise() {
    let a = ok(
        "pub flow f(x: Sig[F32], g: Ctl[Bool]) -> Sig[F32] {\n  let y = if g { x } else { 0.0 }\n  let o = match Some(y) {\n    Some(v) => v,\n    None => 1.0,\n  }\n  o\n}\n",
    );
    let f = flow(&a, "f");
    assert_eq!(let_rate(f, "y"), (FlowRate::Sig, false));
    assert_eq!(let_rate(f, "o"), (FlowRate::Sig, false));
}

#[test]
fn non_rt_function_only_at_init() {
    let src = "pub fn make(n: F32) -> F32 { n * 2.0 }\npub flow f(t: Init[F32], c: Ctl[F32]) -> Sig[F32] {\n  let a = make(t)\n  let b = make(2.0)\n  a + b + c\n}\n";
    let a = ok(src);
    let f = flow(&a, "f");
    assert_eq!(let_rate(f, "a"), (FlowRate::Init, true));
    assert_eq!(let_rate(f, "b"), (FlowRate::Init, true));
    assert_eq!(
        codes("pub fn make(n: F32) -> F32 { n * 2.0 }\npub flow f(c: Ctl[F32]) -> Sig[F32] {\n  make(c)\n}\n"),
        vec![Code::E0805]
    );
}

#[test]
fn constant_lets_are_never_state() {
    let a = ok("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let two = 2.0\n  x * two\n}\n");
    assert_eq!(let_rate(flow(&a, "f"), "two"), (FlowRate::Const, false));
}

// ---------------------------------------------------------------- diagnostics

#[test]
fn e0801_forward_reference() {
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let a = b\n  let b = x\n  a\n}\n"), vec![Code::E0801]);
    // Its own initializer, outside a look-back.
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let y = x + y\n  y\n}\n"), vec![Code::E0801]);
    // Look-back through a function call in the first argument is fine.
    ok(
        "pub rt fn id(x: F32) -> F32 { x }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  let y = x + prev(id(y), 0.0)\n  y\n}\n",
    );
}

#[test]
fn e0805_effects() {
    assert_eq!(
        codes(
            "pub fn alloc_it() -> F32 uses {Alloc} { 1.0 }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  x * alloc_it()\n}\n"
        ),
        vec![Code::E0805]
    );
}

#[test]
fn e0806_forms() {
    for body in [
        "var a = 1.0\n  a",
        "let a = x\n  a = x\n  a",
        "for i in 0..4 { }\n  x",
        "while true { }\n  x",
        "return x",
        "assert true\n  x",
        "let f = fn(v: F32) -> F32 { v }\n  x",
        "let a = move x\n  a",
        "let a = if true { let b = x\n b } else { x }\n  a",
        "x\n  x",
    ] {
        let src = format!("pub flow f(x: Sig[F32]) -> Sig[F32] {{\n  {body}\n}}\n");
        assert_eq!(codes(&src), vec![Code::E0806], "{body}");
    }
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let a = x\n}\n"), vec![Code::E0806]);
}

#[test]
fn e0807_e0808_delay_lengths() {
    let a = check("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  delay(x, 1, 0.0)\n}\n");
    assert_eq!(a.diagnostics[0].code, Code::E0807);
    assert!(
        a.diagnostics[0]
            .fixes
            .iter()
            .any(|f| matches!(f, onsa_diag::Fix::Replace { replace } if replace == "prev(x, 0.0)"))
    );
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  delay(x, 0, 0.0)\n}\n"), vec![Code::E0808]);
    assert_eq!(
        codes("pub flow f(x: Sig[F32], n: Init[U32]) -> Sig[F32] {\n  delay(x, n, 0.0)\n}\n"),
        vec![Code::E0808]
    );
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  vdelay(x, 2.0, 0, 0.0)\n}\n"), vec![Code::E0808]);
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[[F32; 0]] {\n  par i in 2..2 { x }\n}\n"), vec![Code::E0808]);
    ok("const N: U32 = 8\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  delay(x, N, 0.0) + vdelay(x, 2.0, N, 0.0)\n}\n");
}

#[test]
fn e0810_non_copy_let() {
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let s = \"a\"\n  x\n}\n"), vec![Code::E0810]);
}

#[test]
fn e0811_e0812_marks() {
    let a = check("pub flow g(x: Sig[F32]) -> Sig[F32] { x }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  g(x)\n}\n");
    assert_eq!(a.diagnostics[0].code, Code::E0811);
    assert!(
        a.diagnostics[0].fixes.iter().any(|f| matches!(f, onsa_diag::Fix::Replace { replace } if replace == "g~(x)"))
    );
    let a = check("pub rt fn h(x: F32) -> F32 { x }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  h~(x)\n}\n");
    assert_eq!(a.diagnostics[0].code, Code::E0812);
    assert!(
        a.diagnostics[0].fixes.iter().any(|f| matches!(f, onsa_diag::Fix::Replace { replace } if replace == "h(x)"))
    );
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  prev~(x, 0.0)\n}\n"), vec![Code::E0812]);
}

#[test]
fn e0813_e0814_delay_argument_rates() {
    let a = check("pub flow f(p: Ctl[F32]) -> Sig[F32] {\n  prev(p, 0.0)\n}\n");
    assert_eq!(a.diagnostics[0].code, Code::E0813);
    assert!(a.diagnostics[0].notes.iter().any(|(_, n)| n.contains("let ps: Sig[F32] = p")));
    assert_eq!(codes("pub flow f(x: Sig[F32], p: Ctl[F32]) -> Sig[F32] {\n  prev(x, p)\n}\n"), vec![Code::E0814]);
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  prev(x, x)\n}\n"), vec![Code::E0814]);
    ok("pub flow f(x: Sig[F32], t: Init[F32]) -> Sig[F32] {\n  prev(x, t)\n}\n");
    let a = ok("pub flow f(x: Sig[F32], t: Init[F32]) -> Sig[F32] {\n  let y = prev(x, t * 2.0)\n  y\n}\n");
    assert!(matches!(&flow(&a, "f").nodes[0], Node::Prev { init: InitArg::Init(_), .. }));
}

#[test]
fn e0815_argument_rate_too_high() {
    assert_eq!(
        codes(
            "pub flow g(c: Ctl[F32]) -> Sig[F32] { prev(x, 0.0) }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  g~(x)\n}\n"
        )
        .iter()
        .filter(|&&c| c == Code::E0815)
        .count(),
        1
    );
    assert_eq!(
        codes(
            "pub flow g(t: Init[F32], x: Sig[F32]) -> Sig[F32] { x * t }\npub flow f(x: Sig[F32], c: Ctl[F32]) -> Sig[F32] {\n  g~(c, x)\n}\n"
        ),
        vec![Code::E0815]
    );
}

#[test]
fn e0412_instance_arity_and_e0401_type() {
    assert_eq!(
        codes("pub flow g(x: Sig[F32]) -> Sig[F32] { x }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  g~(x, x)\n}\n"),
        vec![Code::E0412]
    );
    assert_eq!(
        codes("pub flow g(x: Sig[F32]) -> Sig[F32] { x }\npub flow f(x: Sig[I32]) -> Sig[F32] {\n  g~(x)\n}\n"),
        vec![Code::E0401]
    );
}

#[test]
fn let_patterns_destructure() {
    let a = ok(
        "pub struct P { l: F32, r: F32 }\npub rt fn mk(x: F32) -> P { P { l: x, r: x } }\npub flow f(x: Sig[F32]) -> Sig[F32] {\n  let P { l: l, r: r } = mk(x)\n  let (a, b) = (l, r)\n  a + b\n}\n",
    );
    let f = flow(&a, "f");
    assert_eq!(f.lets.len(), 2);
    assert_eq!(f.lets[0].locals.len(), 2);
    assert_eq!(f.lets[0].rate, FlowRate::Sig);
    assert!(f.lets[0].name.is_none());
}

#[test]
fn no_shadowing_in_flows() {
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let x = 1.0\n  x\n}\n"), vec![Code::E0304]);
    assert_eq!(codes("pub flow f(x: Sig[F32]) -> Sig[F32] {\n  let a = x\n  let a = x\n  a\n}\n"), vec![Code::E0304]);
}
