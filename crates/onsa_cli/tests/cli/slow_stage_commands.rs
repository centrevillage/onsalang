//! A flow with a stage of `sample / N` and a flow that reads `sample_tick()` in the commands of `onsa` (W7-16 U5a/t; spec §11.3, §11.4, §11.6, §11.9,
//! §12.4, §18.1, `spec/tools.md` §1.1; S-565, S-578, S-1079, S-1179, Q-09): what the case files in `tests/spec/flow_semantics/` cannot pin.
//!
//! - A flow with no modifier whose body has a stage of `sample / N` (a delay or a `let` of a tick, a part computed at a tick, `sample_tick()`) is lowered:
//!   `build`, `dump --core` and `test` end with 0 and with no internal error, and the tests of the package are run (U5a).
//! - What stays E0200 after U5a is the work of the later units: a child instance that has a stage of its own or reads `sample_tick()`, with no
//!   modifier (U5b), a chain of `.down~(N)` and `.up~(N)` (U6a, U6b) and a conversion flow (U5b, U6a, U6b). The commands report E0200 and nothing else,
//!   no internal error, and run no test (Q-09: what the spec has and this version does not carry is E0200, not a wrong output).
//! - Of two ticks at one position that both panic, the slower one is the one that is reported (§11.9: "遅い方から並ぶ", S-1079): the `failure` of `onsa test`
//!   is at the expression of that tick.
//! - `onsa interface` shows the phase counter of a flow that has a stage of `sample / N` or reads `sample_tick()`, after `_sample_rate` and before the fields of
//!   the `let`s (§12.4, S-1179 (2)), as a field that the compiler puts (its name starts with `_`, §11.6, S-1137); a flow with neither has none.
//!
//! The texts are written from the spec; none is taken from the output of the compiler.

use crate::test_support::{
    Dir, code_of, diagnostics, doc_of, failure_of, record, run, span_of, str_of, test_json, tests_of,
};

pub const BUILD_MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

pub fn error_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.contains("error[")).collect()
}

/// A package of `main.onsa` (the text of the flows and a test `reads` that holds no flow) and the other files `(name, text)`.
pub fn package(tag: &str, flows: &str, others: &[(&str, &str)]) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", BUILD_MANIFEST);
    d.write("main.onsa", &format!("{flows}\ntest \"reads\" {{\n  assert 1 + 1 == 2\n}}\n"));
    for (name, text) in others {
        d.write(name, text);
    }
    d
}

/// `check` reads the package with no diagnostic, and `build`, `dump --core` and `test` end with 0 and no internal error; the test `reads` is run and passes.
pub fn assert_lowers(tag: &str, flows: &str, others: &[(&str, &str)]) {
    let d = package(tag, flows, others);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 0, "{flows}: check: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{flows}: {}", out.stdout);

    let dir = d.arg();
    let build = run(d.root(), &["build", "--target", "host"]);
    let both = format!("{}{}", build.stdout, build.stderr);
    assert_eq!(build.code, 0, "{flows}: build: {both}");
    assert!(!both.contains("internal error") && !both.contains("E0200"), "{flows}: build: {both}");
    let dump = run(d.root(), &["dump", "--core", dir.as_str()]);
    let both = format!("{}{}", dump.stdout, dump.stderr);
    assert_eq!(dump.code, 0, "{flows}: dump --core: {both}");
    assert!(
        !dump.stdout.trim().is_empty() && !both.contains("internal error") && !both.contains("E0200"),
        "{flows}: dump --core: {both}"
    );

    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 0, "{flows}: test: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{flows}: {doc}");
    assert_eq!(str_of(record(&doc, "main", "reads"), "status"), "ok", "{flows}: {doc}");
}

/// `check` reads the package with no diagnostic, and `build`, `dump --core` and `test` stop at it with E0200 and nothing else (no internal error), on a file of the
/// package, and `test` runs nothing. When `first_line` is given, the first diagnostic (§18.1: the order of the file, the line and the column) is on that line of `main.onsa`.
pub fn assert_e0200(tag: &str, flows: &str, others: &[(&str, &str)], first_line: Option<u64>) {
    let d = package(tag, flows, others);
    let out = run(d.root(), &["check", "--json"]);
    assert_eq!(out.code, 0, "{flows}: check reads the flows: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc_of(&out)).is_empty(), "{flows}: {}", out.stdout);

    let dir = d.arg();
    let commands: [(&str, Vec<&str>); 3] = [
        ("build", vec!["build", "--target", "host"]),
        ("dump --core", vec!["dump", "--core", dir.as_str()]),
        ("test", vec!["test"]),
    ];
    for (name, args) in commands {
        let out = run(d.root(), &args);
        assert_eq!(out.code, 1, "{flows}: {name}: {}{}", out.stdout, out.stderr);
        let both = format!("{}{}", out.stdout, out.stderr);
        let lines = error_lines(&both);
        assert!(!lines.is_empty(), "{flows}: {name}: an error line: {both}");
        for l in &lines {
            assert!(l.contains("error[E0200]"), "{flows}: {name}: only E0200: {l}");
            assert!(l.contains(".onsa:"), "{flows}: {name}: E0200 is on a file of the package: {l}");
        }
        assert!(!both.contains("internal error"), "{flows}: {name}: {both}");
    }

    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let ds = diagnostics(&doc);
    assert!(!ds.is_empty() && ds.iter().all(|x| code_of(x) == "E0200"), "{flows}: {doc}");
    assert!(tests_of(&doc).is_empty(), "{flows}: nothing is run: {doc}");
    if let Some(line) = first_line {
        let first = span_of(&ds[0]["span"]);
        assert_eq!((first.file.as_str(), first.line), ("main.onsa", line), "{flows}: the first E0200: {doc}");
    }
}

// ----------------------------------------------------------------------------- what U5a lowers

/// Flows with no modifier and no child, each with a stage of `sample / N` or a `sample_tick()`: a delay read at `sample`, a part computed at a tick and read
/// at `sample`, two ticks of different ratios where one reads the other, the arms of an `if~` and the replicas of a `par~`, `sample_tick()` in a stage of `sample / 4`.
const LOWERING: [&str; 5] = [
    "pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  let lf = prev~(p at (sample / 4))\n  x * (lf at sample)\n}\n",
    "pub flow f(p: F32 at block, q: F32 at block, x: F32 at sample) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  let c = prev~(q at (sample / 4))\n  let b = (a * 2.0) at sample\n  x * b + (c at sample)\n}\n",
    "pub flow f(p: F32 at block) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  let b = (a at (sample / 2)) + 1.0\n  b at sample\n}\n",
    "pub flow f(c: Bool at block, p: F32 at block) -> F32 at sample {\n  let y = if~ c { prev~(p at (sample / 4)) } else { prev~((p * 2.0) at (sample / 4)) }\n  let zs = par~ i in 0 ..< 2 { prev~((p * F32.round_from(i + 1)) at (sample / 8)) }\n  (y at sample) + (zs[1] at sample)\n}\n",
    "pub flow f(x: F32 at sample) -> F32 at sample {\n  let t4 = sample_tick() at (sample / 4)\n  x + F32.round_from(t4 at sample) + F32.round_from(sample_tick())\n}\n",
];

/// The flows above are read by `check`, lowered by the commands, and the package runs its tests (U5a: the Core of the stages of one flow).
#[test]
fn a_flow_with_a_stage_of_sample_over_n_is_lowered_by_build_dump_core_and_test() {
    for (k, flows) in LOWERING.iter().enumerate() {
        assert_lowers(&format!("slow_stage_lowers_{k}"), flows, &[]);
    }
}

// ----------------------------------------------------------------------------- what stays E0200 after U5a

const SLOW_CHILD: &str = "flow ch(p: F32 at block) -> F32 at sample {\n  prev~(p at (sample / 4)) at sample\n}\n\n";

/// A child that has a stage of its own, or reads `sample_tick()`, run by a parent with no modifier (S-1088: the stages of the child are the stages of the parent
/// at the position of the call, U5b): the child alone is lowered, the call is not, and the instance is E0200 and not a value that leaves the stage of the child unrun.
/// Each body is a form that `check` reads with no diagnostic.
#[test]
fn a_child_with_a_stage_of_its_own_is_e0200_until_w7_16_u5b() {
    let bodies: [(String, Vec<(&str, &str)>); 6] = [
        (format!("{SLOW_CHILD}pub flow f(p: F32 at block, x: F32 at sample) -> F32 at sample {{\n  x * ch~(p)\n}}\n"), vec![]),
        (
            "flow tk(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  tk~(x)\n}\n".to_string(),
            vec![],
        ),
        (
            format!("{SLOW_CHILD}flow mid(p: F32 at block) -> F32 at sample {{\n  ch~(p) * 2.0\n}}\n\npub flow f(p: F32 at block) -> F32 at sample {{\n  mid~(p)\n}}\n"),
            vec![],
        ),
        (
            format!("{SLOW_CHILD}pub flow f(c: Bool at block, p: F32 at block) -> F32 at sample {{\n  let ys = par~ i in 0 ..< 2 {{ ch~(p) * F32.round_from(i + 1) }}\n  let y = if~ c {{ ch~(p) }} else {{ ys[1] }}\n  y + ys[0]\n}}\n"),
            vec![],
        ),
        (
            "use slow\n\npub flow f(p: F32 at block) -> F32 at sample {\n  slow.ch~(p)\n}\n".to_string(),
            vec![("slow.onsa", "pub flow ch(p: F32 at block) -> F32 at sample {\n  prev~(p at (sample / 4)) at sample\n}\n")],
        ),
        (
            "use slow\n\npub flow f(x: F32 at sample) -> U32 at sample {\n  slow.elapsed~(x)\n}\n".to_string(),
            vec![("slow.onsa", "pub flow elapsed(x: F32 at sample) -> U32 at sample {\n  sample_tick()\n}\n")],
        ),
    ];
    for (k, (flows, others)) in bodies.iter().enumerate() {
        assert_e0200(&format!("slow_stage_child_{k}"), flows, others, None);
    }
}

// ----------------------------------------------------------------------------- the slower tick first

/// Two ticks at the frame 4 both read a 0 and divide by it. The stage of `sample / 2` is written first and the one of `sample / 4` second, so that the order of the
/// text and the order of the stages differ: the slower tick (`sample / 4`, the expression `100 / a`, line 5) is the one that stops the run (§11.9: "比の違う遅い刻みどうしは
/// 遅い方（N の大きい方）から並び"; S-1079), not the first written (`200 / b`, line 3).
#[test]
fn of_two_ticks_that_panic_at_one_position_the_slower_is_reported() {
    let src = "pub flow both(p: I32 at block) -> I32 at sample {
  let b = delay~(p at (sample / 2), 2, 1)
  let qb = 200 / b
  let a = prev~(p at (sample / 4), 1)
  let qa = 100 / a
  (qa at sample) + (qb at sample)
}

test \"stops\" {
  let o = both.render(both.Params { p: 0 }, 5, 8.0)
  assert o.out[0] == 300
}
";
    let d = Dir::pkg("slow_stage_slower_first");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "stops"));
    let at = span_of(&f["span"]);
    assert_eq!((at.file.as_str(), at.line), ("m.onsa", 5), "the division of the tick of sample / 4: {f}");
}

// ----------------------------------------------------------------------------- the interface

/// The lines of the fields of `<flow>.State` in the text of `onsa interface`: (name, offset, the line).
fn state_fields(text: &str, flow: &str) -> Vec<(String, u64, String)> {
    let head = format!("pub struct {flow}.State");
    let mut lines = text.lines().skip_while(|l| !l.trim_start().starts_with(&head));
    assert!(lines.next().is_some(), "no `{head}` in:\n{text}");
    lines
        .take_while(|l| l.contains(" bytes, align "))
        .map(|l| {
            let name = l.trim().split(':').next().unwrap_or("").to_string();
            let offset = l
                .rsplit("offset ")
                .next()
                .and_then(|n| n.trim().parse::<u64>().ok())
                .unwrap_or_else(|| panic!("an offset in `{l}`"));
            (name, offset, l.to_string())
        })
        .collect()
}

/// §12.4 (S-1179 (2)): after `_sample_rate` (when it is there) come the phase counter, then the fields of the `let`s, and `_poisoned` and `_initialized` are last. The counter
/// is a `U32` (4 bytes, align 4) that the compiler puts (§11.6: "処理系が置くものだと印を付ける": a name that starts with `_`, §2.3, S-1137); it is next to `_sample_rate` with no padding.
/// A flow with no stage of `sample / N` and no `sample_tick()` has no counter (the state of the flows in the cases `state_names_*` stays).
#[test]
fn the_interface_puts_the_phase_counter_after_sample_rate_and_before_the_lets() {
    let src = "pub flow slow(p: F32 at block, x: F32 at sample) -> F32 at sample {
  let a = prev~(p at (sample / 4))
  x * (a at sample) * sample_rate()
}

pub flow counted(x: F32 at sample) -> U32 at sample {
  sample_tick()
}

pub flow plain(x: F32 at sample) -> F32 at sample {
  x * 0.5
}
";
    let d = Dir::pkg("slow_stage_interface");
    d.write("m.onsa", src);
    let out = run(d.root(), &["interface"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("not available"), "the size of the state is known: {}", out.stdout);

    let slow = state_fields(&out.stdout, "slow");
    let names: Vec<&str> = slow.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(&names[..2], ["_sample_rate", "_tick"], "{names:?}");
    assert_eq!((slow[0].1, slow[1].1), (0, 4), "the counter is next to `_sample_rate`: {slow:?}");
    assert!(slow[1].2.contains("4 bytes, align 4"), "{}", slow[1].2);
    assert_eq!(&names[names.len() - 2..], ["_poisoned", "_initialized"], "{names:?}");
    assert!(names[2..names.len() - 2].iter().all(|n| !n.starts_with("_tick")), "one counter: {names:?}");

    let counted = state_fields(&out.stdout, "counted");
    let names: Vec<&str> = counted.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(names, ["_tick", "_poisoned", "_initialized"], "a flow that reads only `sample_tick()`: {names:?}");
    assert_eq!(counted.iter().map(|f| f.1).collect::<Vec<_>>(), [0, 4, 5], "{counted:?}");
    assert!(out.stdout.contains("pub struct counted.State  // Affine; size 8, bulk 0, align 4"), "{}", out.stdout);

    let plain = state_fields(&out.stdout, "plain");
    let names: Vec<&str> = plain.iter().map(|f| f.0.as_str()).collect();
    assert_eq!(names, ["_poisoned", "_initialized"], "a flow with no time has no counter: {names:?}");
}
