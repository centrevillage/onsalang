//! `sample_tick()` in the commands of `onsa` (W7-09 U4b/t; spec §11.4, §11.3, §11.9, §18.1, `spec/tools.md` §1.1; S-565, S-567 (K6), Q-09):
//! what the case files in `tests/spec/flow_clock/` cannot pin.
//!
//! - The counter of the phase is in the Core of the ticks, W7-16, so `build`, `dump --core` and `test` stop at a package that has a flow
//!   that reads `sample_tick()` with E0200 and with nothing else (no internal error), on the file of the flow, while `check` reads it with
//!   no diagnostic and `onsa interface` ends with 0.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::test_support::{Dir, code_of, diagnostics, doc_of, run, test_json, tests_of};

const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// The bodies of `main.onsa` that read `sample_tick()` in the places of §11.4 (a `let`, the output, a `par`, the head of a chain, the
/// body of a conversion flow), each with the module `ticks.onsa` that it uses or none (an empty text).
const SOURCES: [(&str, &str); 6] = [
    ("pub flow f(x: F32 at sample) -> F32 at sample {\n  let t = sample_tick()\n  x * F32.round_from(t)\n}\n", ""),
    ("pub flow f(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n", ""),
    (
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let ys = par i in 0 ..< 2 { x * F32.round_from(sample_tick() + i) }\n  ys[0] + ys[1]\n}\n",
        "",
    ),
    (
        "flow pass_u32(g: U32 at sample) -> U32 at sample {\n  g\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  pass_u32~(sample_tick()).down~(4) at sample\n}\n",
        "",
    ),
    (
        "flow g(x: F32 at (sample * 2)) -> F32 at sample {\n  x[1] * F32.round_from(sample_tick())\n}\n\npub flow f(x: F32 at sample) -> F32 at sample {\n  g~(x).down~(2) at sample\n}\n",
        "",
    ),
    (
        "use ticks\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  ticks.elapsed~(x)\n}\n",
        "pub flow elapsed(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n",
    ),
];

fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

fn package(tag: &str, main: &str, ticks: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", &format!("{main}\ntest \"reads\" {{\n  assert 1 + 1 == 2\n}}\n"));
    if !ticks.is_empty() {
        d.write("ticks.onsa", ticks);
    }
    d
}

/// A package whose flows read `sample_tick()` is read by `check` with no diagnostic (a `U32` of the clock of the place, §11.4), and `build`,
/// `dump --core` and `test` stop at it with E0200 and nothing else, on the file of the flow (Q-09: what the spec has and this version does
/// not carry is E0200, not a wrong output; the counter is the Core of W7-16), with no internal error.
#[test]
fn a_package_that_reads_sample_tick_is_e0200_for_build_dump_core_and_test() {
    for (k, (main, ticks)) in SOURCES.iter().enumerate() {
        let d = package(&format!("sample_tick_core_gate_{k}"), main, ticks);

        let out = run(d.root(), &["check", "--json"]);
        assert_eq!(out.code, 0, "{main}: check reads the flows: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "{main}: {}", out.stdout);

        let dir = d.arg();
        let commands: [(&str, Vec<&str>); 3] = [
            ("build", vec!["build", "--target", "host"]),
            ("dump --core", vec!["dump", "--core", dir.as_str()]),
            ("test", vec!["test"]),
        ];
        for (name, args) in commands {
            let out = run(d.root(), &args);
            assert_eq!(out.code, 1, "{main}: {name}: {}{}", out.stdout, out.stderr);
            let both = format!("{}{}", out.stdout, out.stderr);
            let lines = error_lines(&both);
            assert!(!lines.is_empty(), "{main}: {name}: an error line: {both}");
            for l in &lines {
                assert!(l.contains("error[E0200]"), "{main}: {name}: only E0200: {l}");
                assert!(l.contains(".onsa:"), "{main}: {name}: E0200 is on the file of the flow: {l}");
            }
            assert!(!both.contains("internal error"), "{main}: {name}: {both}");
        }

        let (out, doc) = test_json(d.root(), &[]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        let ds = diagnostics(&doc);
        assert!(!ds.is_empty() && ds.iter().all(|x| code_of(x) == "E0200"), "{main}: {doc}");
        assert!(tests_of(&doc).is_empty(), "{main}: nothing is run: {doc}");
    }
}

/// `onsa interface` reads the signatures only (§18), so a flow that reads `sample_tick()` in its body is listed with its ports and the
/// command ends with 0 and with no internal error.
#[test]
fn interface_of_a_flow_that_reads_sample_tick_ends_with_0() {
    let d = Dir::pkg("sample_tick_interface");
    let file = d.file(
        "m.onsa",
        "pub flow g(x: F32 at sample, p: F32 at block) -> U32 at sample {\n  let t = sample_tick()\n  t + 1\n}\n",
    );
    let out = run(d.root(), &["interface", &file]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    let lines: Vec<&str> = out.stdout.lines().map(str::trim).collect();
    assert!(lines.iter().any(|l| l.starts_with("x: F32 at sample")), "the input is listed:\n{}", out.stdout);
    assert!(lines.iter().any(|l| l.starts_with(") -> U32 at sample")), "the output is listed:\n{}", out.stdout);
}

/// W7-09 U4b/i2: what `check` reads with no diagnostic, `onsa graph` and `onsa interface` end with 0 and with no internal error (§18.2,
/// `spec/tools.md` §1.1): a `par` that is no root whose body reads `sample_tick()` (its node is labelled with the clock of the place that uses
/// it, §11.4), in a `let` and in the output, of the `sample` of the body and of `sample / 4`.
#[test]
fn graph_and_interface_of_a_par_that_reads_sample_tick_end_with_0() {
    let sources = [
        "pub flow f(x: U32 at sample) -> U32 at sample {\n  let v = (par i in 0 ..< 2 { sample_tick() + i })[0]\n  v\n}\n",
        "pub flow f(x: U32 at sample) -> U32 at sample {\n  (par i in 0 ..< 2 { sample_tick() + i })[0]\n}\n",
        "pub flow f(x: U32 at sample) -> U32 at (sample / 4) {\n  (par i in 0 ..< 2 { sample_tick() * i })[1]\n}\n",
    ];
    for (k, src) in sources.iter().enumerate() {
        let d = Dir::pkg(&format!("sample_tick_par_graph_{k}"));
        let file = d.file("m.onsa", src);
        let out = run(d.root(), &["check", "--json", &file]);
        assert_eq!(out.code, 0, "{src}: check: {}{}", out.stdout, out.stderr);
        for args in [vec!["graph", "f", file.as_str()], vec!["interface", file.as_str()]] {
            let out = run(d.root(), &args);
            assert_eq!(out.code, 0, "{src}: {args:?}: {}{}", out.stdout, out.stderr);
            assert!(!out.stderr.contains("internal error"), "{src}: {args:?}: {}", out.stderr);
        }
    }
}
