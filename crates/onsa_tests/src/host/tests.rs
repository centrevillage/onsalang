//! Self-tests of the host steps (K-14): the harness does not let a wrong
//! expectation, a malformed step or a sequence that never runs pass.

use std::os::unix::process::ExitStatusExt as _;
use std::path::PathBuf;

use super::plan::{self, SeqPlan};
use super::*;
use crate::fragment;
use crate::pending;
use crate::run::{self, Report};
use crate::scalar::Scalar;

const HEAD: &str = "// onsa.toml\n// [package]\n// name = \"m\"\n// edition = \"2026\"\n//\n// [export]\n\
                    // prefix = \"onsa_\"\n// flows = [\"m.f\"]\n// fns = [\"m.sub\"]\n//\n// [targets.t]\n\
                    // kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"poison\"\n\
                    // provides = []\n//\n// [test]\n";

const SRC: &str = "\npub flow f(\n  x: Sig[F32],\n  @param(min: 0.0, max: 10.0, default: 1.0)\n  k: Ctl[F32],\n) -> Sig[F32] {\n  x * k\n}\n\n\
                   pub fn sub(a: I32, b: I32) -> I32 {\n  a - b\n}\n";

/// A flow sequence and a function sequence that pass.
const GOOD: &str = "// [[test.host]]\n// name = \"scale\"\n// target = \"t\"\n// flow = \"m.f\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 48000.0, status = 0 },\n\
//   { call = \"process\", params = { k = 2.0 }, frames = 3, input = [1.0, -0.5, 0.25], status = 0, output = [2.0, -1.0, 0.5] },\n\
//   { call = \"reset\" },\n\
//   { call = \"process\", params = { k = 0.5 }, frames = 0, null = [\"input\", \"output\"], status = 0 },\n\
// ]\n\
//\n\
// [[test.host]]\n// name = \"sub\"\n// target = \"t\"\n// fn = \"m.sub\"\n// steps = [\n\
//   { call = \"fn\", args = { a = 5, b = 2 }, status = 0, result = 3 },\n\
//   { call = \"fn\", args = { a = -2147483648, b = 1 }, status = 1 },\n\
// ]\n";

fn case(hosts: &str) -> String {
    format!("{HEAD}{hosts}{SRC}")
}

fn parse_err(hosts: &str) -> String {
    match fragment::parse(&case(hosts)) {
        Ok(_) => panic!("accepted:\n{hosts}"),
        Err(e) => e,
    }
}

/// One sequence of the flow with `steps` (each a line of the array).
fn flow_seq(steps: &[&str]) -> String {
    let mut s = "// [[test.host]]\n// name = \"s\"\n// target = \"t\"\n// flow = \"m.f\"\n// steps = [\n".to_string();
    for st in steps {
        s.push_str(&format!("//   {st},\n"));
    }
    s.push_str("// ]\n");
    s
}

const INIT: &str = "{ call = \"init\", config = {}, sample_rate = 48000.0, status = 0 }";

#[test]
fn the_forms_of_a_sequence() {
    let f = fragment::parse(&case(GOOD)).unwrap().unwrap();
    assert_eq!(f.test.host.len(), 2);
    assert_eq!(f.test.host[0].line, 19);
    assert_eq!(f.test.host[0].steps[1].line, 25);
    assert_eq!(f.test.host[1].fn_.as_deref(), Some("m.sub"));
    let bad: &[(&str, String)] = &[
        ("unknown field `nmae`", GOOD.replacen("name = \"scale\"", "nmae = \"scale\"", 1)),
        ("unknown field `stauts`", flow_seq(&[INIT, "{ call = \"reset\", stauts = 0 }"])),
        ("unknown variant `run`", flow_seq(&[INIT, "{ call = \"run\" }"])),
        (
            "`steps` is empty",
            "// [[test.host]]\n// name = \"s\"\n// target = \"t\"\n// flow = \"m.f\"\n// steps = []\n".into(),
        ),
        (
            "exactly one of `flow` and `fn`",
            GOOD.replacen("// flow = \"m.f\"\n", "// flow = \"m.f\"\n// fn = \"m.sub\"\n", 1),
        ),
        ("exactly one of `flow` and `fn`", GOOD.replacen("// flow = \"m.f\"\n", "", 1)),
        ("used twice", GOOD.replacen("name = \"sub\"", "name = \"scale\"", 1)),
        ("no `::`", GOOD.replacen("name = \"sub\"", "name = \"a::b\"", 1)),
        ("space at its ends", GOOD.replacen("name = \"sub\"", "name = \"sub \"", 1)),
        ("the first step of a flow is `init`", flow_seq(&["{ call = \"reset\" }"])),
        ("returns nothing, S-198", flow_seq(&[INIT, "{ call = \"reset\", status = 0 }"])),
        ("needs `sample_rate`", flow_seq(&["{ call = \"init\", config = {}, status = 0 }"])),
        ("needs `config`", flow_seq(&["{ call = \"init\", sample_rate = 8.0, status = 0 }"])),
        (
            "passes no `Config`",
            flow_seq(&["{ call = \"init\", config = {}, null = [\"cfg\"], sample_rate = 8.0, status = 0 }"]),
        ),
        ("needs `status`", flow_seq(&["{ call = \"init\", config = {}, sample_rate = 8.0 }"])),
        (
            "needs `params`",
            flow_seq(&[INIT, "{ call = \"process\", frames = 0, input = [], status = 0, output = [] }"]),
        ),
        (
            "needs `frames`",
            flow_seq(&[INIT, "{ call = \"process\", params = {}, input = [], status = 0, output = [] }"]),
        ),
        (
            "needs `output`",
            flow_seq(&[INIT, "{ call = \"process\", params = {}, frames = 0, input = [], status = 0 }"]),
        ),
        (
            "needs `frames = 0`",
            flow_seq(&[
                INIT,
                "{ call = \"process\", params = {}, frames = 1, null = [\"input\"], status = 0, output = [0.0] }",
            ]),
        ),
        (
            "`fill` with `inplace`",
            flow_seq(&[
                INIT,
                "{ call = \"process\", params = {}, frames = 1, input = [1.0], inplace = true, fill = [0.0], status = 0, output = [0.0] }",
            ]),
        ),
        (
            "passes no output",
            flow_seq(&[
                INIT,
                "{ call = \"process\", params = {}, frames = 0, input = [], null = [\"output\"], fill = [], status = 0 }",
            ]),
        ),
        (
            "not an argument of `process`",
            flow_seq(&[
                INIT,
                "{ call = \"process\", params = {}, frames = 0, input = [], null = [\"bulk\"], status = 0, output = [] }",
            ]),
        ),
        (
            "names `input` twice",
            flow_seq(&[
                INIT,
                "{ call = \"process\", params = {}, frames = 0, null = [\"input\", \"input\"], status = 0, output = [] }",
            ]),
        ),
        (
            "`status = 3`",
            flow_seq(&[INIT, "{ call = \"process\", params = {}, frames = 0, input = [], status = 3, output = [] }"]),
        ),
        ("`status = 2`", GOOD.replacen("status = 1 }", "status = 2 }", 1)),
        ("belongs to a sequence of `fn`", flow_seq(&[INIT, "{ call = \"fn\", args = {}, status = 0 }"])),
        (
            "is not a field of `call = \"init\"`",
            flow_seq(&["{ call = \"init\", config = {}, sample_rate = 8.0, status = 0, frames = 1 }"]),
        ),
    ];
    for (needle, hosts) in bad {
        let e = parse_err(hosts);
        assert!(e.contains(needle), "{needle:?} not in: {e}");
        assert!(e.contains("line "), "no line in: {e}");
    }
    // mode parse never builds
    let parse_mode = format!("// onsa.toml\n// [test]\n// mode = \"parse\"\n{GOOD}{SRC}");
    let e = fragment::parse(&parse_mode).unwrap_err();
    assert!(e.contains("[[test.host]] needs `mode"), "{e}");
}

#[test]
fn values_are_exact_in_their_type() {
    use plan::scalar_value;
    let v = |s: &str| -> toml::Value { toml::from_str::<toml::Table>(&format!("v = {s}")).unwrap()["v"].clone() };
    let i32_ = Scalar::Int(onsa_core::IntKind::I32);
    let u8_ = Scalar::Int(onsa_core::IntKind::U8);
    for (s, ty, needle) in [
        ("0.1", Scalar::F32, "not exact in F32 (the nearest F32 is 0.10000000149011612)"),
        ("2", Scalar::F32, "write a float (`2.0`)"),
        ("300", u8_, "outside U8"),
        ("-1", u8_, "outside U8"),
        ("1.5", i32_, "the float 1.5 for a value of I32"),
        ("\"ab\"", Scalar::Char, "not one character"),
        ("\"\"", Scalar::Char, "not one character"),
        ("1", Scalar::Bool, "the integer 1 for a value of Bool"),
    ] {
        let e = scalar_value(&v(s), ty).unwrap_err();
        assert!(e.contains(needle), "{s}: {e}");
    }
    let ok = |s: &str, ty: Scalar| scalar_value(&v(s), ty).unwrap();
    assert!(matches!(ok("nan", Scalar::F32), onsa_interp::Value::F32(x) if x.is_nan()));
    assert!(matches!(ok("-0.0", Scalar::F32), onsa_interp::Value::F32(x) if x == 0.0 && x.is_sign_negative()));
    assert!(matches!(ok("inf", Scalar::F32), onsa_interp::Value::F32(x) if x.is_infinite()));
    assert!(matches!(ok("1e10", Scalar::F32), onsa_interp::Value::F32(x) if x == 1e10));
    assert!(matches!(ok("0.1", Scalar::F64), onsa_interp::Value::F64(x) if x == 0.1));
    assert!(matches!(ok("true", Scalar::Bool), onsa_interp::Value::Bool(true)));
    assert!(matches!(ok("\"\\u00e9\"", Scalar::Char), onsa_interp::Value::Char('é')));
    assert!(matches!(ok("-2147483648", i32_), onsa_interp::Value::I32(i32::MIN)));
}

/// The build of the case `hosts` for target `t`, and the plan of its sequences.
fn plans(hosts: &str) -> (onsa_driver::BuildOutput, Vec<Result<SeqPlan, String>>) {
    let text = case(hosts);
    let frag = fragment::parse(&text).unwrap().unwrap();
    let input = onsa_driver::PackageInput {
        manifest: frag.manifest,
        files: vec![onsa_driver::SourceFile { path: "m.onsa".into(), text }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
    assert!(analyzed.diagnostics.is_empty(), "{:?}", analyzed.diagnostics);
    let out = onsa_driver::build_analyzed(&loaded, &analyzed, "t").unwrap_or_else(|_| panic!("the build failed"));
    let p = frag
        .test
        .host
        .iter()
        .map(|s| {
            plan::plan(s, &out).map_err(|e| match e {
                plan::PlanError::Case(m) => m,
                plan::PlanError::Harness(m) => panic!("an error of the harness: {m}"),
            })
        })
        .collect();
    (out, p)
}

#[test]
fn values_are_checked_against_the_build() {
    let errs = [
        (
            "is not exact in F32",
            "{ call = \"process\", params = { k = 0.1 }, frames = 0, input = [], status = 0, output = [] }",
        ),
        ("has no `k`", "{ call = \"process\", params = {}, frames = 0, input = [], status = 0, output = [] }"),
        (
            "has `j`, which is not one of its fields",
            "{ call = \"process\", params = { k = 1.0, j = 1.0 }, frames = 0, input = [], status = 0, output = [] }",
        ),
        (
            "has 2 values, but `frames = 1`",
            "{ call = \"process\", params = { k = 1.0 }, frames = 1, input = [1.0, 2.0], status = 0, output = [1.0] }",
        ),
        ("needs `input`", "{ call = \"process\", params = { k = 1.0 }, frames = 0, status = 0, output = [] }"),
        (
            "unwritten pattern",
            "{ call = \"process\", params = { k = 1.0 }, frames = 1, input = [1.0], status = 0, output = [-2.8735182454018313e-16] }",
        ),
    ];
    for (needle, step) in errs {
        let (_, p) = plans(&flow_seq(&[INIT, step]));
        let e = p[0].as_ref().map(|_| ()).unwrap_err();
        assert!(e.contains(needle) && e.contains("step 2"), "{needle}: {e}");
    }
    let fn_errs = [
        ("needs `result`", "{ call = \"fn\", args = { a = 1, b = 2 }, status = 0 }"),
        ("writes no result", "{ call = \"fn\", args = { a = 1, b = 2 }, status = 1, result = 0 }"),
        ("has no `b`", "{ call = \"fn\", args = { a = 1 }, status = 0, result = 1 }"),
    ];
    for (needle, step) in fn_errs {
        let hosts = format!(
            "// [[test.host]]\n// name = \"g\"\n// target = \"t\"\n// fn = \"m.sub\"\n// steps = [\n//   {step},\n// ]\n"
        );
        let (_, p) = plans(&hosts);
        let e = p[0].as_ref().map(|_| ()).unwrap_err();
        assert!(e.contains(needle), "{needle}: {e}");
    }
    let unexported = GOOD.replacen("fn = \"m.sub\"", "fn = \"m.nope\"", 1);
    let (_, p) = plans(&unexported);
    assert!(p[1].as_ref().map(|_| ()).unwrap_err().contains("is not exported for target `t`"));
}

fn finished(code: i32, stdout: Vec<u8>) -> c::Finished {
    c::Finished { status: Some(std::process::ExitStatus::from_raw(code << 8)), stdout, stderr: String::new() }
}

/// The records of the good flow sequence, as a correct program writes them.
fn good_records() -> Vec<u8> {
    let mut b = Vec::new();
    b.extend(0u32.to_le_bytes());
    b.extend(0i32.to_le_bytes());
    b.extend(1u32.to_le_bytes());
    b.extend(0i32.to_le_bytes());
    for x in [2.0f32, -1.0, 0.5] {
        b.extend(x.to_le_bytes());
    }
    b.extend(2u32.to_le_bytes());
    b.extend(super::driver::RESET_DONE.to_le_bytes());
    b.extend(3u32.to_le_bytes());
    b.extend(0i32.to_le_bytes());
    b
}

#[test]
fn records_are_compared() {
    let (_, p) = plans(GOOD);
    let p = p[0].as_ref().unwrap();
    let end = |mut b: Vec<u8>| {
        b.extend(u32::MAX.to_le_bytes());
        b
    };
    assert_eq!(compare::outcome(p, &finished(0, end(good_records())), None).unwrap(), Outcome::Passed { compared: 6 });
    // one output differs: the step, the output, the frame and the bits
    let mut b = good_records();
    b[20..24].copy_from_slice(&1.0f32.to_le_bytes());
    let Outcome::Failed(m) = compare::outcome(p, &finished(0, end(b)), None).unwrap() else { panic!() };
    assert_eq!(m, "step 2 (process, line 25): output `out` frame 1: expected -1.0 (0xbf800000), got 1.0 (0x3f800000)");
    // a status differs
    let mut b = good_records();
    b[4..8].copy_from_slice(&1i32.to_le_bytes());
    let Outcome::Failed(m) = compare::outcome(p, &finished(0, end(b)), None).unwrap() else { panic!() };
    assert_eq!(m, "step 1 (init, line 24): status: expected 0, got 1");
    // an output the call did not write
    let mut b = good_records();
    for x in &mut b[16..28] {
        *x = PATTERN;
    }
    let Outcome::Failed(m) = compare::outcome(p, &finished(0, end(b)), None).unwrap() else { panic!() };
    assert!(
        m.contains("frame 0: expected 2.0 (0x40000000), got nothing written") && m.contains("2 more frames"),
        "{m}"
    );
    // NaNs are equal, -0.0 is not 0.0 (§13.4)
    let mut b = good_records();
    b[16..20].copy_from_slice(&(-0.0f32).to_le_bytes());
    assert!(matches!(compare::outcome(p, &finished(0, end(b)), None).unwrap(), Outcome::Failed(_)));
    // the program ended inside step 2 (a caught signal): that step fails
    let b = good_records()[..14].to_vec();
    let Outcome::Failed(m) = compare::outcome(p, &finished(c::SIGNAL_EXIT, b), None).unwrap() else { panic!() };
    assert!(m.starts_with("step 2 (process, line 25): the program ended inside the call: a fatal signal"), "{m}");
    assert!(m.contains("steps 3..4 did not run"), "{m}");
    // the time budget
    let late = c::Finished { status: None, stdout: good_records()[..8].to_vec(), stderr: String::new() };
    let Outcome::Failed(m) = compare::outcome(p, &late, None).unwrap() else { panic!() };
    assert!(m.contains("step 2 (process, line 25): the program ended before the call: it ran longer"), "{m}");
    // errors of the harness: never a pass
    assert!(compare::outcome(p, &finished(0, good_records()), None).unwrap_err().contains("no end mark"));
    assert!(compare::outcome(p, &finished(0, Vec::new()), None).unwrap_err().contains("records of 0 of 4 steps"));
    let mut extra = end(good_records());
    extra.push(0);
    assert!(compare::outcome(p, &finished(0, extra), None).unwrap_err().contains("more than its records"));
    let mut skip = good_records();
    skip[8..12].copy_from_slice(&2u32.to_le_bytes());
    assert!(compare::outcome(p, &finished(0, skip), None).unwrap_err().contains("record of step 3 where step 2"));
    assert!(
        compare::outcome(p, &finished(c::INPUT_EXIT, Vec::new()), None)
            .unwrap_err()
            .contains("could not read its input")
    );
}

// ---- end to end: the case runner with a C compiler

struct Repo(PathBuf);

impl Repo {
    fn new(tag: &str, files: &[(&str, &str)]) -> Repo {
        let root = std::env::temp_dir().join(format!("onsa_host_test_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for (p, text) in files {
            let p = root.join(p);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, text).unwrap();
        }
        if !root.join(pending::PATH).exists() {
            std::fs::write(root.join(pending::PATH), "").unwrap();
        }
        Repo(root)
    }

    fn run(&self) -> Report {
        run::run_all(&self.0)
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn entry(target: &str) -> String {
    format!(
        "[[pending]]\nkind = \"test-case\"\ntarget = \"{target}\"\nreasons = [\"R-12\"]\nuntil = \"W2-08\"\nnote = \"n\"\n\n"
    )
}

fn failures<'a>(r: &'a Report, path: &str) -> &'a [String] {
    &r.cases.iter().find(|c| c.run.path == path).unwrap_or_else(|| panic!("no case {path}")).failures
}

#[test]
fn the_runner_runs_and_compares() {
    c::require("clang").unwrap();
    let wrong_output = GOOD.replacen("output = [2.0, -1.0, 0.5]", "output = [2.0, -1.0, 0.75]", 1);
    let wrong_status = GOOD.replacen(
        "{ a = -2147483648, b = 1 }, status = 1",
        "{ a = -2147483648, b = 1 }, status = 0, result = 0",
        1,
    );
    let wrong_result = GOOD.replacen("result = 3", "result = 4", 1);
    let null_cfg = GOOD.replacen(
        "{ call = \"init\", config = {}, sample_rate = 48000.0, status = 0 }",
        "{ call = \"init\", null = [\"cfg\"], sample_rate = 48000.0, status = 0 }",
        1,
    );
    // W1-11/b `un1`: a step the C API cannot express after a wrong value: both are reported
    let mid = GOOD.replacen("output = [2.0, -1.0, 0.5]", "output = [2.0, -1.0, 0.75]", 1).replacen(
        "null = [\"input\", \"output\"], status = 0 },\n",
        "null = [\"input\", \"output\"], status = 0 },\n\
             //   { call = \"init\", null = [\"cfg\"], sample_rate = 8.0, status = 0 },\n//   { call = \"reset\" },\n",
        1,
    );
    let trap = case(GOOD).replace("panic = \"poison\"", "panic = \"trap\"");
    let halt = case(GOOD).replace("panic = \"poison\"", "panic = \"halt\"");
    let no_target = case(&GOOD.replace("target = \"t\"", "target = \"u\""));
    let check_fails = case(GOOD).replace("x * k", "x * j");
    let same_as_test = format!(
        "{}{SRC}\ntest \"sub\" {{\n  assert 1 == 1\n}}\n",
        case(GOOD).replace("// [test]\n", "// [test]\n// mode = \"test\"\n").replace(SRC, "")
    );
    let list = [
        entry("tests/listed_failing.onsa::scale"),
        entry("tests/listed_passing.onsa::scale"),
        entry("tests/listed_unknown.onsa::nope"),
        entry("tests/listed_case_error.onsa::scale"),
    ]
    .concat();
    let repo = Repo::new(
        "e2e",
        &[
            ("tests/good/m.onsa", &case(GOOD)),
            ("tests/wrong_output/m.onsa", &case(&wrong_output)),
            ("tests/wrong_status/m.onsa", &case(&wrong_status)),
            ("tests/wrong_result/m.onsa", &case(&wrong_result)),
            ("tests/null_cfg/m.onsa", &case(&null_cfg)),
            ("tests/mid/m.onsa", &case(&mid)),
            ("tests/trap/m.onsa", &trap),
            ("tests/halt/m.onsa", &halt),
            ("tests/no_target/m.onsa", &no_target),
            ("tests/check_fails/m.onsa", &check_fails),
            ("tests/same_as_test/m.onsa", &same_as_test),
            (
                "tests/listed_failing.onsa",
                &case(&wrong_output)
                    .replace("name = \"m\"", "name = \"listed_failing\"")
                    .replace("m.", "listed_failing."),
            ),
            (
                "tests/listed_passing.onsa",
                &case(GOOD).replace("name = \"m\"", "name = \"listed_passing\"").replace("m.", "listed_passing."),
            ),
            (
                "tests/listed_unknown.onsa",
                &case(GOOD).replace("name = \"m\"", "name = \"listed_unknown\"").replace("m.", "listed_unknown."),
            ),
            (
                "tests/listed_case_error.onsa",
                &trap.replace("name = \"m\"", "name = \"listed_case_error\"").replace("m.", "listed_case_error."),
            ),
            (pending::PATH, &list),
        ],
    );
    let r = repo.run();
    let has = |p: &str, needle: &str| {
        let f = failures(&r, p);
        assert!(f.iter().any(|x| x.contains(needle)), "{p}: {needle:?} not in {f:#?}");
    };
    assert!(failures(&r, "tests/good/m.onsa").is_empty(), "{:?}", failures(&r, "tests/good/m.onsa"));
    let good = &r.cases.iter().find(|c| c.run.path == "tests/good/m.onsa").unwrap().run.hosts;
    assert!(good.iter().all(|h| matches!(h.outcome, Outcome::Passed { .. })) && good.len() == 2, "{good:?}");
    has(
        "tests/wrong_output/m.onsa",
        "step 2 (process, line 25): output `out` frame 2: expected 0.75 (0x3f400000), got 0.5",
    );
    has("tests/wrong_status/m.onsa", "step 2 (fn, line 36): status: expected 0, got 1");
    has("tests/wrong_result/m.onsa", "step 1 (fn, line 35): result: expected 4, got 3");
    has("tests/null_cfg/m.onsa", "step 1 (init, line 24): this version's C API cannot express it");
    let mid = failures(&r, "tests/mid/m.onsa");
    let m = mid.iter().find(|x| x.contains("host \"scale\"")).unwrap_or_else(|| panic!("{mid:#?}"));
    assert!(m.contains("step 2 (process, line 25): output `out` frame 2: expected 0.75"), "{m}");
    assert!(m.contains("step 5 (init, line 28): this version's C API cannot express it"), "{m}");
    assert!(m.contains("step 6 did not run"), "{m}");
    has("tests/trap/m.onsa", "`panic = \"trap\"` never returns from a panic");
    has("tests/halt/m.onsa", "`panic = \"halt\"` never returns from a panic");
    has("tests/no_target/m.onsa", "`target = \"u\"` is not a target of the case");
    has("tests/check_fails/m.onsa", "host \"scale\" did not run: the check reports");
    has("tests/same_as_test/m.onsa", "a `test` block has the same name");
    // the list: a listed sequence that fails is pending, and only it
    let c = r.cases.iter().find(|c| c.run.path == "tests/listed_failing.onsa").unwrap();
    assert!(c.failures.is_empty(), "{:?}", c.failures);
    assert_eq!(c.pending_hosts, ["scale"]);
    has("tests/listed_passing.onsa", "the host sequence \"scale\" passes but is listed");
    has("tests/listed_unknown.onsa", "lists the test \"nope\"");
    // an error of the case is not silenced by the entry of a sequence
    has("tests/listed_case_error.onsa", "never returns from a panic");
    assert!(r.summary().contains("host sequences:"), "{}", r.summary());
}

const SHAPES_HEAD: &str = "// onsa.toml\n// [package]\n// name = \"s\"\n// edition = \"2026\"\n//\n// [export]\n\
// prefix = \"onsa_\"\n\
// flows = [\"s.swap\", \"s.mirror\", \"s.gate\", \"s.acc\", \"s.lin\", \"s.gain\", \"s.rate\"]\n\
// fns = [\"s.first\"]\n//\n// [targets.t]\n\
// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n// panic = \"poison\"\n// provides = []\n//\n// [test]\n";

/// Every sequence passes on a correct harness, and each catches a harness
/// that drops or reorders something (the mutants of W1-11/b): a second
/// channel or output, `fill`, in-place buffers, `reset`, `sample_rate`, the
/// order of `config`, `params` and `args`.
const SHAPES_HOSTS: &str = "// [[test.host]]\n// name = \"swap /* in C */ \\\\\"\n// target = \"t\"\n// flow = \"s.swap\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 2, input = { l = [1.0, 2.0], r = [3.0, 4.0] }, status = 0, output = { a = [3.0, 4.0], b = [1.0, 2.0] } },\n\
//   { call = \"process\", params = {}, frames = 2, input = { l = [5.0, 6.0], r = [7.0, 8.0] }, inplace = true, status = 0, output = { a = [7.0, 8.0], b = [5.0, 6.0] } },\n\
//   { call = \"process\", params = {}, frames = 1, input = { l = [1.0], r = [2.0] }, fill = { a = [9.0], b = [-9.0] }, status = 0, output = { a = [2.0], b = [1.0] } },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"mirror\"\n// target = \"t\"\n// flow = \"s.mirror\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 2, input = [[1.0, 2.0], [3.0, 4.0]], status = 0, output = [[3.0, 4.0], [1.0, 2.0]] },\n\
//   { call = \"process\", params = {}, frames = 1, input = [[1.0], [-0.0]], inplace = true, status = 0, output = [[-0.0], [1.0]] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"gate\"\n// target = \"t\"\n// flow = \"s.gate\"\n// steps = [\n\
//   { call = \"init\", config = { on = true }, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 2, input = [1, -32768], status = 0, output = [1, -32768] },\n\
//   { call = \"init\", config = { on = false }, null = [\"bulk\"], sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 2, input = [1, 2], status = 0, output = [0, 0] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"acc\"\n// target = \"t\"\n// flow = \"s.acc\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 2, input = [1.0, 1.0], status = 0, output = [1.0, 2.0] },\n\
//   { call = \"reset\" },\n\
//   { call = \"process\", params = {}, frames = 2, input = [1.0, 1.0], status = 0, output = [1.0, 2.0] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"lin\"\n// target = \"t\"\n// flow = \"s.lin\"\n// steps = [\n\
//   { call = \"init\", config = { a = 2.0, b = 0.5 }, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 1, input = [2.0], status = 0, output = [4.5] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"gain\"\n// target = \"t\"\n// flow = \"s.gain\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = { g = 3.0, o = 1.0 }, frames = 1, input = [2.0], status = 0, output = [7.0] },\n\
//   { call = \"process\", params = { g = 3.0, o = 1.0 }, frames = 1, input = [nan], status = 0, output = [-nan] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"rate\"\n// target = \"t\"\n// flow = \"s.rate\"\n// steps = [\n\
//   { call = \"init\", config = {}, sample_rate = 8.0, status = 0 },\n\
//   { call = \"process\", params = {}, frames = 1, input = [0.5], status = 0, output = [4.0] },\n\
// ]\n//\n\
// [[test.host]]\n// name = \"first\"\n// target = \"t\"\n// fn = \"s.first\"\n// steps = [\n\
//   { call = \"fn\", args = { xs = [2.5, 1.0] }, status = 0, result = 2.5 },\n\
//   { call = \"fn\", args = { xs = [] }, status = 1 },\n\
// ]\n";

/// The output fields are not named as the inputs: this version's C API puts
/// both in one parameter list, where the names collide.
const SHAPES_SRC: &str = "\npub struct Stereo {\n  a: F32,\n  b: F32,\n}\n\n\
pub flow swap(l: Sig[F32], r: Sig[F32]) -> Sig[Stereo] {\n  Stereo { a: r, b: l }\n}\n\n\
pub flow mirror(x: Sig[[F32; 2]]) -> Sig[[F32; 2]] {\n  [x[1], x[0]]\n}\n\n\
pub flow gate(x: Sig[I16], on: Init[Bool]) -> Sig[I16] {\n  if on { x } else { 0 }\n}\n\n\
pub flow acc(x: Sig[F32]) -> Sig[F32] {\n  let y = x + prev(y, 0.0)\n  y\n}\n\n\
pub flow lin(x: Sig[F32], a: Init[F32], b: Init[F32]) -> Sig[F32] {\n  (x * a) + b\n}\n\n\
pub flow gain(\n  x: Sig[F32],\n  @param(min: 0.0, max: 10.0, default: 1.0)\n  g: Ctl[F32],\n  \
@param(min: 0.0, max: 10.0, default: 0.0)\n  o: Ctl[F32],\n) -> Sig[F32] {\n  (x * g) + o\n}\n\n\
pub flow rate(x: Sig[F32]) -> Sig[F32] {\n  x * sample_rate()\n}\n\n\
pub fn first(xs: Span[F32]) -> F32 {\n  xs[0]\n}\n";

fn shapes(hosts: &str) -> String {
    format!("{SHAPES_HEAD}{hosts}{SHAPES_SRC}")
}

/// The build of a case and the plans of its sequences (the plan must succeed).
fn build_and_plan(text: &str) -> (onsa_driver::BuildOutput, Vec<SeqPlan>) {
    let frag = fragment::parse(text).unwrap().unwrap();
    let input = onsa_driver::PackageInput {
        manifest: frag.manifest,
        files: vec![onsa_driver::SourceFile { path: "s.onsa".into(), text: text.into() }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
    assert!(analyzed.diagnostics.is_empty(), "{:?}", analyzed.diagnostics);
    let out = onsa_driver::build_analyzed(&loaded, &analyzed, "t").unwrap_or_else(|_| panic!("the build failed"));
    let plans = frag.test.host.iter().map(|s| plan::plan(s, &out).unwrap()).collect();
    (out, plans)
}

/// The forms of §11.6 at the boundary, end to end: two inputs (`In`), a
/// struct output (`Out`), planar channels, in-place buffers, `fill`, integer
/// and `Bool` values, state and `reset`, `sample_rate`, two `Init` and two
/// `Ctl` inputs, a span argument. A wrong value in the second channel or the
/// second output fails.
#[test]
fn the_shapes_of_the_signals() {
    c::require("clang").unwrap();
    let good = shapes(SHAPES_HOSTS);
    let wrong = |from: &str, to: &str| {
        assert_eq!(good.matches(from).count(), 1, "{from}");
        good.replacen(from, to, 1)
    };
    let negzero = wrong("output = [[-0.0], [1.0]]", "output = [[0.0], [1.0]]");
    let channel = wrong("output = [[3.0, 4.0], [1.0, 2.0]]", "output = [[3.0, 4.0], [1.0, 9.0]]");
    let second = wrong("output = { a = [3.0, 4.0], b = [1.0, 2.0] }", "output = { a = [3.0, 4.0], b = [1.0, 9.0] }");
    let repo = Repo::new(
        "shapes",
        &[
            ("tests/good/s.onsa", &good),
            ("tests/negzero/s.onsa", &negzero),
            ("tests/channel/s.onsa", &channel),
            ("tests/second/s.onsa", &second),
        ],
    );
    let r = repo.run();
    assert!(failures(&r, "tests/good/s.onsa").is_empty(), "{:#?}", failures(&r, "tests/good/s.onsa"));
    let passed = &r.cases.iter().find(|c| c.run.path == "tests/good/s.onsa").unwrap().run.hosts;
    assert_eq!(passed.len(), 8, "{passed:?}");
    assert!(passed.iter().all(|h| matches!(h.outcome, Outcome::Passed { .. })), "{passed:?}");
    let has = |p: &str, needle: &str| {
        let f = failures(&r, p);
        assert!(f.iter().any(|x| x.contains(needle)), "{p}: {needle:?} not in {f:#?}");
    };
    // -0.0 is not 0.0 (§13.4)
    has("tests/negzero/s.onsa", "output `out` channel 0 frame 0: expected 0.0 (0x00000000), got -0.0 (0x80000000)");
    has("tests/channel/s.onsa", "output `out` channel 1 frame 1: expected 9.0 (0x41100000), got 2.0 (0x40000000)");
    has("tests/second/s.onsa", "output `b` frame 1: expected 9.0 (0x41100000), got 2.0 (0x40000000)");
}

/// What a correct implementation does not show in its outputs, seen in the
/// program and its input: the in-place buffers are the input's, `fill`
/// reaches the buffer, `reset` is called, the storage holds the pattern
/// before `init`, and no name of a sequence reaches the C.
#[test]
fn the_program_and_its_input() {
    let (out, plans) = build_and_plan(&shapes(SHAPES_HOSTS));
    let src = driver::program(&out, &plans).source;
    let has = |needle: &str| assert!(src.contains(needle), "{needle:?} not in the program:\n{src}");
    // in place: the same buffers as input and output (swap, step 3; mirror, step 3)
    has("onsa_swap_process(s, &p, in2_0_0, in2_1_0, in2_0_0, in2_1_0, 2u)");
    has("float* out2_0[2] = { in2_0_0, in2_0_1 };");
    has("onsa_mirror_process(s, &p, in2_0, out2_0, 1u)");
    // fill: read into the output buffers before the call
    has("static float out3_0_0[1]; onsa_host_read(out3_0_0, sizeof(float) * 1u);");
    // reset is called, and its end is marked
    has("onsa_host_step(2u);\n    onsa_acc_reset(s);\n    { uint32_t done = 0x52455354u;");
    // the storage holds the pattern before init
    has("memset(onsa_host_mem_0, 0xa5, sizeof onsa_host_mem_0);");
    assert!(!src.contains("swap /*") && !src.contains("in C */"), "a name reached the C:\n{src}");
    // the bytes of the input: sample_rate, the order of config, params and args, fill
    let bytes = |p: &SeqPlan| plan::input_bytes(p, p.steps.len());
    let f32s = |xs: &[f32]| xs.iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>();
    let pat = |n: usize| vec![PATTERN; n];
    let swap = [
        f32s(&[8.0]),
        f32s(&[1.0, 2.0, 3.0, 4.0]),
        pat(16),
        f32s(&[5.0, 6.0, 7.0, 8.0]),
        f32s(&[1.0, 2.0]),
        f32s(&[9.0, -9.0]),
    ]
    .concat();
    assert_eq!(bytes(&plans[0]), swap);
    assert_eq!(bytes(&plans[4]), [f32s(&[2.0, 0.5, 8.0]), f32s(&[2.0]), pat(4)].concat());
    let gain = bytes(&plans[5]);
    assert_eq!(gain[..20], [f32s(&[8.0]), f32s(&[3.0, 1.0, 2.0]), pat(4)].concat());
    assert_eq!(bytes(&plans[7]), [f32s(&[2.5, 1.0])].concat());
    // the order of a function's arguments
    let (_, p) = plans_of(GOOD);
    assert_eq!(
        bytes(p[1].as_ref().unwrap()),
        [5i32, 2, i32::MIN, 1].iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<_>>()
    );
}

/// The records of the C backend are what its headers declare (D-15): the
/// arguments of `init` and `process`, the fields of `params`, the functions.
#[test]
fn the_records_are_the_headers() {
    let (out, _) = build_and_plan(&shapes(SHAPES_HOSTS));
    let header = |name: &str| &out.unit.headers.iter().find(|(n, _)| n == name).unwrap_or_else(|| panic!("{name}")).1;
    assert_eq!(out.unit.flows.len(), 7);
    for api in &out.unit.flows {
        let h = header(&api.header);
        let sym = &api.symbol;
        let fields: String = if api.params_fields.is_empty() {
            " uint8_t onsa_empty;".into()
        } else {
            api.params_fields.iter().map(|f| format!(" {} {};", f.c_type, f.c_name)).collect()
        };
        let params = format!("typedef struct {sym}_params {{{fields} }} {sym}_params;");
        let init_args: String = api.init_args.iter().map(|f| format!("{} {}, ", f.c_type, f.c_name)).collect();
        let init = format!("int  {sym}_init({sym}* s, void* bulk, {init_args}float sample_rate);");
        let io: String = api
            .process_args
            .iter()
            .map(|a| match (a.planar, a.output) {
                (None, false) => format!("const {}* {}, ", a.c_type, a.c_name),
                (None, true) => format!("{}* {}, ", a.c_type, a.c_name),
                (Some(_), false) => format!("const {}* const* {}, ", a.c_type, a.c_name),
                (Some(_), true) => format!("{}* const* {}, ", a.c_type, a.c_name),
            })
            .collect();
        let process = format!("int  {sym}_process({sym}* s, const {sym}_params* p, {io}uint32_t frames);");
        for line in [params, init, process] {
            assert!(h.contains(&line), "{line:?} not in {}:\n{h}", api.header);
        }
    }
    let swap = out.unit.flows.iter().find(|a| a.flow == "s.swap").unwrap();
    let io: Vec<(&str, bool)> = swap.process_args.iter().map(|a| (a.name.as_str(), a.output)).collect();
    assert_eq!(io, [("l", false), ("r", false), ("a", true), ("b", true)]);
    let lin = out.unit.flows.iter().find(|a| a.flow == "s.lin").unwrap();
    assert_eq!(lin.init_args.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["a", "b"]);
    let f = &out.unit.fns[0];
    assert_eq!((f.fn_.as_str(), f.symbol.as_str(), f.ret.as_deref()), ("s.first", "onsa_first", Some("float")));
    assert!(header(&f.header).contains("float onsa_first(const float* xs, uint32_t xs_len);"));
    assert_eq!(out.unit.take_panic.as_deref(), Some("onsa_take_panic"));
}

/// The plans of `hosts` on the module of [`case`].
fn plans_of(hosts: &str) -> (onsa_driver::BuildOutput, Vec<Result<SeqPlan, String>>) {
    plans(hosts)
}

/// Synthetic records: a second channel and a second output are compared; a
/// step the C API cannot express fails there and the steps before it are
/// compared; a run that ends inside `reset` fails the `reset`; the panics of
/// the run go with a difference.
#[test]
fn records_of_channels_outputs_and_stops() {
    let (_, plans) = build_and_plan(&shapes(SHAPES_HOSTS));
    let f32s = |xs: &[f32]| xs.iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>();
    let rec = |k: u32, status: i32, rest: &[u8]| {
        [k.to_le_bytes().to_vec(), status.to_le_bytes().to_vec(), rest.to_vec()].concat()
    };
    let end = || u32::MAX.to_le_bytes().to_vec();
    // mirror: step 2's second channel differs
    let mirror = &plans[1];
    let ok = [rec(0, 0, &[]), rec(1, 0, &f32s(&[3.0, 4.0, 1.0, 2.0])), rec(2, 0, &f32s(&[-0.0, 1.0])), end()].concat();
    assert!(matches!(compare::outcome(mirror, &finished(0, ok), None).unwrap(), Outcome::Passed { .. }));
    let bad = [rec(0, 0, &[]), rec(1, 0, &f32s(&[3.0, 4.0, 1.0, 5.0])), rec(2, 0, &f32s(&[-0.0, 1.0])), end()].concat();
    let Outcome::Failed(m) = compare::outcome(mirror, &finished(0, bad), None).unwrap() else { panic!() };
    assert!(m.contains("output `out` channel 1 frame 1: expected 2.0 (0x40000000), got 5.0"), "{m}");
    // swap: step 2's second output differs
    let swap = &plans[0];
    let steps = |b2: f32| {
        [
            rec(0, 0, &[]),
            rec(1, 0, &f32s(&[3.0, 4.0, 1.0, b2])),
            rec(2, 0, &f32s(&[7.0, 8.0, 5.0, 6.0])),
            rec(3, 0, &f32s(&[2.0, 1.0])),
            end(),
        ]
        .concat()
    };
    assert!(matches!(compare::outcome(swap, &finished(0, steps(2.0)), None).unwrap(), Outcome::Passed { .. }));
    let Outcome::Failed(m) = compare::outcome(swap, &finished(0, steps(3.0)), None).unwrap() else { panic!() };
    assert!(m.contains("output `b` frame 1: expected 2.0 (0x40000000), got 3.0"), "{m}");
    // with the panics of the run
    let mut done = finished(0, steps(3.0));
    done.stderr = "onsa-host-panic: index out of range (s.onsa:9)".into();
    let Outcome::Failed(m) = compare::outcome(swap, &done, None).unwrap() else { panic!() };
    assert!(m.contains("the panics of the run:\n  onsa-host-panic: index out of range (s.onsa:9)"), "{m}");
    // acc: the program ends inside `reset` (its index, no mark)
    let acc = &plans[3];
    let b = [rec(0, 0, &[]), rec(1, 0, &f32s(&[1.0, 2.0])), 2u32.to_le_bytes().to_vec()].concat();
    let Outcome::Failed(m) = compare::outcome(acc, &finished(c::SIGNAL_EXIT, b), None).unwrap() else { panic!() };
    assert!(m.starts_with("step 3 (reset, line ") && m.contains("ended inside the call: a fatal signal"), "{m}");
    // a `reset` without its mark is an error of the harness
    let b =
        [rec(0, 0, &[]), rec(1, 0, &f32s(&[1.0, 2.0])), rec(2, 7, &[]), rec(3, 0, &f32s(&[1.0, 2.0])), end()].concat();
    assert!(compare::outcome(acc, &finished(0, b), None).unwrap_err().contains("no mark of a finished `reset`"));
    // a step the C API cannot express: the steps before it are compared, the ones after it do not run
    let u = super::driver::Unsupported { step: 2, message: "no `cfg` pointer".into() };
    let b = [rec(0, 0, &[]), rec(1, 0, &f32s(&[1.0, 9.0])), end()].concat();
    let Outcome::Failed(m) = compare::outcome(acc, &finished(0, b), Some(&u)).unwrap() else { panic!() };
    let lines: Vec<&str> = m.lines().collect();
    assert_eq!(lines.len(), 3, "{m}");
    assert!(lines[0].contains("step 2 (process") && lines[0].contains("frame 1: expected 2.0"), "{m}");
    assert!(lines[1].contains("step 3 (reset") && lines[1].ends_with("cannot express it: no `cfg` pointer"), "{m}");
    assert_eq!(lines[2], "step 4 did not run");
}
