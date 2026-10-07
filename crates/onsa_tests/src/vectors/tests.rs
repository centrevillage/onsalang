//! The harness of the vectors on small data of its own: the reader, the
//! comparison, the list, and both implementations end to end.

use std::path::{Path, PathBuf};

use onsa_interp::Value;

use super::bind::{RowPlan, Shape};
use super::data::{Data, Expect, Op, Row, Want};
use super::judge::{self, Got, OpRun, Verdict, judge, op_result};
use super::*;
use crate::ccheck::{FailureKind, ItemReport};
use crate::scalar::Scalar;

const MANIFEST_TEXT: &str = "format 1\nseed 0x4f4e5341\n";

const REGISTRY_TEXT: &str = "# op\tfn\tfile\tpkg\targs\tret\tspec\ttokens\tonsa
i32.add\tadd\tt.tsv\tp\tI32 I32\tI32\t§3.4\t+\ta + b
u8.checked_mul\tcm\tt.tsv\tp\tU8 U8\tOption[U8]\t§3.4\tchecked_mul\ta.checked_mul(b)
f32.half\thalf\tt.tsv\tp\tF32\tF32\t§3.4\t/\ta / 2.0
u32.K\tk\tt.tsv\tp\t()\tU32\t§6.6\tK\tK
";

const DATA_TEXT: &str = "# a comment
@ i32.add edge
1 2\t3
2147483647 1\tpanic:overflow\tS-1
@ i32.add held-S207
0 0\t?
@ u8.checked_mul edge
16 16\tnone
2 3\tsome:6
@ f32.half edge
0x7fc00000\tnan
0x40000000\t0x3f800000
0x80000000\t0x80000000
@ u32.K rand
()\t7
";

const MANIFEST_P: &str = r#"[package]
name = "vt"
edition = "2026"

[export]
prefix = "vt_"
fns = ["ops.add", "ops.cm_some", "ops.cm_val", "ops.half", "ops.k"]

[targets.host]
kind = "source"
lang = "c"
platform = "host"
panic = "poison"
provides = []
"#;

const SOURCE_P: &str = "pub fn add(a: I32, b: I32) -> I32 { a + b }

pub fn cm_some(a: U8, b: U8) -> Bool {
  match a.checked_mul(b) {
    Some(_) => true,
    None => false,
  }
}

pub fn cm_val(a: U8, b: U8) -> U8 { a * b }

pub fn half(a: F32) -> F32 { a / 2.0 }

pub fn k() -> U32 { 7 }
";

/// A repository root of its own with the vectors `data` (`t.tsv`) of the package `p`.
struct Root(PathBuf);

impl Root {
    fn new(data: &str, pending: &str) -> Root {
        let dir = crate::c::scratch_dir("onsa_test", "vectors");
        let v = dir.join(DIR);
        let w = |p: &Path, t: &str| {
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, t).unwrap();
        };
        w(&v.join(MANIFEST), MANIFEST_TEXT);
        w(&v.join(REGISTRY), REGISTRY_TEXT);
        w(&v.join("t.tsv"), data);
        w(&v.join(FIXTURE).join("p/onsa.toml"), MANIFEST_P);
        w(&v.join(FIXTURE).join("p/ops.onsa"), SOURCE_P);
        w(&dir.join(crate::pending::PATH), pending);
        Root(dir)
    }

    fn interp(&self) -> ItemReport {
        run_item(&self.0, Impl::Interp)
    }

    fn c(&self) -> ItemReport {
        run_item_with(&self.0, Impl::C, &[crate::c::item("c-clang").unwrap()])
    }
}

impl Drop for Root {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The id of the row `1 2` of `i32.add`, and of `2147483647 1` ([`Row::id`]).
const ADD_ROW: &str = "t.tsv @ i32.add edge : 1 2";
const ADD_ROW_2: &str = "t.tsv @ i32.add edge : 2147483647 1";

/// An entry of the list that holds the row `1 2` of `i32.add`.
fn entry(target: &str, expect: Option<&str>) -> String {
    held(target, expect, Some(&[ADD_ROW]))
}

/// An entry of the list; for the vectors' items, the failing rows `ids` it holds (`rows` and `digest`).
fn held(target: &str, expect: Option<&str>, ids: Option<&[&str]>) -> String {
    let rows = ids.map_or_else(String::new, |ids| {
        let mut ids: Vec<String> = ids.iter().map(|s| s.to_string()).collect();
        ids.sort();
        format!("rows = {}\ndigest = \"{}\"\n", ids.len(), judge::digest(&ids))
    });
    format!(
        "[[pending]]\nkind = \"gate\"\ntarget = \"{target}\"\nreasons = [\"R-19\"]\nuntil = \"W2-03\"\nnote = \"n\"\n{}{rows}\n",
        expect.map_or_else(String::new, |e| format!("expect = \"{e}\"\n")),
    )
}

fn failing(r: &ItemReport) -> Vec<&str> {
    r.run.results.iter().filter(|c| !c.problems.is_empty()).map(|c| c.id.as_str()).collect()
}

#[test]
fn good_data_passes_in_the_interpreter() {
    let root = Root::new(DATA_TEXT, "");
    let r = root.interp();
    assert_eq!(r.exit_code(), 0, "{}", text(&r));
    assert_eq!(r.run.results.len(), 4);
    assert!(failing(&r).is_empty());
    let t = text(&r);
    assert!(t.contains("interpreter: 4 operations run, 8 rows compared, 1 held rows run"), "{t}");
}

#[test]
fn one_wrong_expectation_fails_and_an_entry_holds_it() {
    let root = Root::new(&DATA_TEXT.replace("1 2\t3", "1 2\t4"), "");
    let r = root.interp();
    assert_eq!(r.exit_code(), 1);
    assert_eq!(failing(&r), ["i32.add"]);
    let t = text(&r);
    assert!(t.contains("FAIL    vectors-interp/i32.add"), "{t}");
    assert!(t.contains("t.tsv:3  i32.add(1, 2)  expected 4  got 3"), "{t}");
    assert!(t.contains("error: vectors-interp/i32.add: fails"), "{t}");
    // listed: pending
    let listed = Root::new(&DATA_TEXT.replace("1 2\t3", "1 2\t4"), &entry("vectors-interp/i32.add", None));
    let r = listed.interp();
    assert_eq!(r.exit_code(), 0, "{}", text(&r));
    assert!(text(&r).contains("PENDING vectors-interp/i32.add"));
    // the entry holds those rows: another failure of the operation is not held (W2-02/b)
    let broken2 = "2147483647 1\t0";
    let two = Root::new(
        &DATA_TEXT.replace("1 2\t3", "1 2\t4").replace("2147483647 1\tpanic:overflow", broken2),
        &entry("vectors-interp/i32.add", None),
    );
    let r = two.interp();
    let f = r.failures.join("\n");
    assert!(f.contains("the failing rows are not the entry's"), "{f}");
    assert!(f.contains("the entry holds `rows = 1`"), "{f}");
    assert!(f.contains("now `rows = 2`"), "{f}");
    assert!(f.contains(&format!("\n  {ADD_ROW}")) && f.contains(&format!("\n  {ADD_ROW_2}")), "{f}");
    // nor one row failing instead of another, the count the same (N1)
    let swapped =
        Root::new(&DATA_TEXT.replace("2147483647 1\tpanic:overflow", broken2), &entry("vectors-interp/i32.add", None));
    let r = swapped.interp();
    let f = r.failures.join("\n");
    assert!(f.contains("the failing rows are not the entry's") && f.contains("now `rows = 1`"), "{f}");
    // fewer rows fail than the entry holds
    let fewer = Root::new(
        &DATA_TEXT.replace("1 2\t3", "1 2\t4"),
        &held("vectors-interp/i32.add", None, Some(&[ADD_ROW, ADD_ROW_2])),
    );
    let r = fewer.interp();
    assert!(r.failures.iter().any(|f| f.contains("the entry holds `rows = 2`")), "{:?}", r.failures);
    // the same rows, written in another order: held
    let both = Root::new(
        &DATA_TEXT.replace("1 2\t3", "1 2\t4").replace("2147483647 1\tpanic:overflow", broken2),
        &held("vectors-interp/i32.add", None, Some(&[ADD_ROW_2, ADD_ROW])),
    );
    assert_eq!(both.interp().exit_code(), 0);
    // an entry without them
    let none = Root::new(&DATA_TEXT.replace("1 2\t3", "1 2\t4"), &held("vectors-interp/i32.add", None, None));
    let r = none.interp();
    let f = r.failures.join("\n");
    assert!(f.contains("the entry has neither") && f.contains("now `rows = 1`, `digest = \""), "{f}");
    // listed with `expect = "internal"`, but the failure is a value: fails
    let wrong = Root::new(&DATA_TEXT.replace("1 2\t3", "1 2\t4"), &entry("vectors-interp/i32.add", Some("internal")));
    let r = wrong.interp();
    assert!(r.failures.iter().any(|f| f.contains("fails otherwise")), "{:?}", r.failures);
}

#[test]
fn an_entry_that_holds_nothing_fails() {
    // listed but passes
    let root = Root::new(DATA_TEXT, &entry("vectors-interp/i32.add", None));
    let r = root.interp();
    assert!(r.failures.iter().any(|f| f.contains("passes but is listed")), "{:?}", r.failures);
    // names no operation
    let root = Root::new(DATA_TEXT, &entry("vectors-interp/i32.nope", None));
    let r = root.interp();
    assert!(r.failures.iter().any(|f| f.contains("names no case of `vectors-interp`")), "{:?}", r.failures);
}

#[test]
fn zeros_differ_and_any_nan_is_nan() {
    // -0.0 / 2 is -0.0, not 0.0
    let root = Root::new(&DATA_TEXT.replace("0x80000000\t0x80000000", "0x80000000\t0x00000000"), "");
    assert_eq!(failing(&root.interp()), ["f32.half"]);
    // a NaN of another payload is `nan`; a NaN is not a number
    let root = Root::new(&DATA_TEXT.replace("0x7fc00000\tnan", "0xffc00001\tnan"), "");
    assert!(failing(&root.interp()).is_empty());
    let root = Root::new(&DATA_TEXT.replace("0x40000000\t0x3f800000", "0x40000000\tnan"), "");
    assert_eq!(failing(&root.interp()), ["f32.half"]);
    // a NaN result is written `nan`: its bits as a result are an error of the data (FORMAT.md)
    for bits in ["0x7fc00000", "0xffc00001", "0x7f800001"] {
        let root = Root::new(&DATA_TEXT.replace("0x7fc00000\tnan", &format!("0x7fc00000\t{bits}")), "");
        let r = root.interp();
        assert_eq!(r.exit_code(), 2, "{bits}");
        assert!(r.run.errors.iter().any(|e| e.contains("FORMAT.md writes it `nan`")), "{:?}", r.run.errors);
    }
}

#[test]
fn panics_options_and_held_rows() {
    // a panic where a value is due, a value where a panic is due
    let root = Root::new(&DATA_TEXT.replace("2147483647 1\tpanic:overflow", "2147483647 1\t0"), "");
    assert!(text(&root.interp()).contains("got panic"));
    let root = Root::new(&DATA_TEXT.replace("1 2\t3", "1 2\tpanic:overflow"), "");
    assert_eq!(failing(&root.interp()), ["i32.add"]);
    // `none` and `some:`
    let root = Root::new(&DATA_TEXT.replace("16 16\tnone", "16 16\tsome:0"), "");
    assert!(text(&root.interp()).contains("expected some:0  got none"));
    let root = Root::new(&DATA_TEXT.replace("2 3\tsome:6", "2 3\tsome:7"), "");
    assert!(text(&root.interp()).contains("expected some:7  got some:6"));
    let root = Root::new(&DATA_TEXT.replace("2 3\tsome:6", "2 3\tnone"), "");
    assert_eq!(failing(&root.interp()), ["u8.checked_mul"]);
    // a held row only runs: any result passes, an overflow too
    let root = Root::new(&DATA_TEXT.replace("0 0\t?", "2147483647 1\t?"), "");
    assert!(failing(&root.interp()).is_empty());
}

#[test]
fn errors_of_the_data_are_never_pending() {
    for (from, to, needle) in [
        ("@ u32.K rand", "@ u32.L rand", "`u32.L` is not in OPS.tsv"),
        ("@ u32.K rand", "@ u32.K wild", "the stage `wild`"),
        ("1 2\t3", "1 2\t?", "`?` is the expectation of a `held-*` section"),
        ("0 0\t?", "0 0\t0", "`?` is the expectation of a `held-*` section"),
        ("1 2\t3", "1\t3", "the arguments `1` for the 2"),
        ("1 2\t3", "1 02\t3", "`02` is not a I32"),
        ("1 2\t3", "1 2147483648\t3", "out of the range of I32"),
        ("0x40000000\t0x3f800000", "0x4000000\t0x3f800000", "`0x4000000` is not a F32"),
        ("0x40000000\t0x3f800000", "0x40000000\t0x3F800000", "`0x3F800000` is not a F32"),
        ("16 16\tnone", "16 16\t16", "`16` for `u8.checked_mul`"),
        ("1 2\t3", "1 2\tnone", "`none` for `i32.add`"),
        ("1 2\t3", "1 2\tpanic:", "a panic without its kind"),
        ("()\t7", "()\tnan", "`nan` for a U32"),
        ("# a comment\n", "1 2\t3\n# a comment\n", "a row outside a section"),
        ("@ u32.K rand\n()\t7\n", "", "no row of `u32.K`"),
        ("2 3\tsome:6", "2 3\tsome:nan", "`nan` is not a U8"),
    ] {
        let data = DATA_TEXT.replace(from, to);
        assert_ne!(data, DATA_TEXT, "{from}");
        let root = Root::new(&data, &entry("vectors-interp/i32.add", None));
        let r = root.interp();
        assert_eq!(r.exit_code(), 2, "{to}: {}", text(&r));
        assert!(r.run.errors.iter().any(|e| e.contains(needle)), "{needle}: {:?}", r.run.errors);
    }
    let root = Root::new(DATA_TEXT, "");
    std::fs::write(root.0.join(DIR).join(MANIFEST), "format 2\n").unwrap();
    let r = root.interp();
    assert!(r.run.errors.iter().any(|e| e.contains("not `format 1`")), "{:?}", r.run.errors);
}

#[test]
fn the_rows_of_an_operation_that_does_not_run_are_checked() {
    // package `q` is held by the list as a whole: its operation does not run, its rows are still read
    let case = "[[pending]]\nkind = \"test-case\"\ntarget = \"tests/vectors/fixture/q\"\nreasons = [\"R-79\"]\n\
                until = \"W5-02\"\nnote = \"n\"\n\n";
    let with_q = |row: &str| {
        let root = Root::new(&format!("{DATA_TEXT}@ i8.neg edge\n{row}\n"), case);
        let ops = root.0.join(DIR).join(REGISTRY);
        let reg = std::fs::read_to_string(&ops).unwrap() + "i8.neg\tneg\tt.tsv\tq\tI8\tI8\t§3.4\t-\t-a\n";
        std::fs::write(&ops, reg).unwrap();
        let q = root.0.join(DIR).join(FIXTURE).join("q");
        std::fs::create_dir_all(&q).unwrap();
        std::fs::write(q.join("onsa.toml"), MANIFEST_P.replace("name = \"vt\"", "name = \"vq\"")).unwrap();
        std::fs::write(q.join("ops.onsa"), "pub fn neg(a: I8) -> I8 { a.nope() }\n").unwrap();
        root
    };
    let r = with_q("-1\t1").interp();
    assert_eq!(r.exit_code(), 0, "{}", text(&r));
    assert!(text(&r).contains("not run: 1 operations"), "{}", text(&r));
    for (row, needle) in [
        ("-1280\t1", "out of the range of I8"),
        ("-1\t0x01", "`0x01` is not a I8"),
        ("-1\tnone", "`none` for `i8.neg`"),
    ] {
        let r = with_q(row).interp();
        assert_eq!(r.exit_code(), 2, "{row}");
        assert!(r.run.errors.iter().any(|e| e.contains(needle)), "{needle}: {:?}", r.run.errors);
    }
}

#[test]
fn every_scalar_name_reads_back() {
    for s in Scalar::ALL {
        assert_eq!(Scalar::from_name(&s.name()), Some(s));
    }
    assert_eq!(Scalar::from_name("Option"), None);
}

#[test]
fn the_registry_and_the_fixture_must_agree() {
    let root = Root::new(DATA_TEXT, "");
    let ops = root.0.join(DIR).join(REGISTRY);
    let text_of = |p: &Path| std::fs::read_to_string(p).unwrap();
    std::fs::write(&ops, text_of(&ops).replace("I32 I32\tI32", "I32 I32\tI64")).unwrap();
    let r = root.interp();
    assert!(
        r.run.errors.iter().any(|e| e.contains("(I32, I32) -> I32 in the build, (I32, I32) -> I64")),
        "{:?}",
        r.run.errors
    );
    let root = Root::new(DATA_TEXT, "");
    let src = root.0.join(DIR).join(FIXTURE).join("p/onsa.toml");
    std::fs::write(&src, MANIFEST_P.replace("\"ops.k\"", "\"ops.k\", \"ops.extra\"")).unwrap();
    let srcf = root.0.join(DIR).join(FIXTURE).join("p/ops.onsa");
    std::fs::write(&srcf, format!("{SOURCE_P}\npub fn extra() -> U32 {{ 1 }}\n")).unwrap();
    let r = root.interp();
    assert!(r.run.errors.iter().any(|e| e.contains("`extra` is no operation's")), "{:?}", r.run.errors);
    // a fixture directory no operation names
    let root = Root::new(DATA_TEXT, "");
    std::fs::create_dir_all(root.0.join(DIR).join(FIXTURE).join("q")).unwrap();
    let r = root.interp();
    assert!(r.run.errors.iter().any(|e| e.contains("fixture/q: no operation")), "{:?}", r.run.errors);
}

#[test]
fn a_package_that_does_not_build() {
    let broken = |root: &Root| {
        let srcf = root.0.join(DIR).join(FIXTURE).join("p/ops.onsa");
        std::fs::write(&srcf, SOURCE_P.replace("a / 2.0", "a.nope()")).unwrap();
    };
    // not listed: an error of the item
    let root = Root::new(DATA_TEXT, "");
    broken(&root);
    let r = root.interp();
    assert_eq!(r.exit_code(), 2);
    assert!(
        r.run.errors.iter().any(|e| e.contains("tests/vectors/fixture/p: `onsa check` reports")),
        "{:?}",
        r.run.errors
    );
    // listed as a whole test case: not run, counted
    let case = "[[pending]]\nkind = \"test-case\"\ntarget = \"tests/vectors/fixture/p\"\nreasons = [\"R-79\"]\n\
                until = \"W5-02\"\nnote = \"n\"\n\n";
    let root = Root::new(DATA_TEXT, case);
    broken(&root);
    let r = root.interp();
    // the only package: nothing runs, which never passes
    assert_eq!(r.exit_code(), 2, "{}", text(&r));
    assert!(r.run.errors.iter().any(|e| e.contains("no operation ran")), "{:?}", r.run.errors);
    assert!(
        text(&r)
            .contains("not run: 4 operations of the packages the list holds as a whole test case: p (4, until W5-02)")
    );
    // and an entry for one of its operations holds nothing
    let root = Root::new(DATA_TEXT, &format!("{case}{}", entry("vectors-interp/i32.add", None)));
    broken(&root);
    let r = root.interp();
    assert!(r.run.errors.iter().any(|e| e.contains("does not run")), "{:?}", r.run.errors);
}

#[test]
fn the_c_against_the_data() {
    if crate::c::require("clang").is_err() {
        panic!("clang is needed (the C checks need it too, Q-07)");
    }
    let root = Root::new(DATA_TEXT, "");
    let r = root.c();
    assert_eq!(r.exit_code(), 0, "{}", text(&r));
    assert_eq!(r.run.results.len(), 4);
    assert!(text(&r).contains("c-clang: 4 operations run, 8 rows compared, 1 held rows run"), "{}", text(&r));
    let root = Root::new(&DATA_TEXT.replace("2 3\tsome:6", "2 3\tsome:5"), "");
    let r = root.c();
    assert_eq!(failing(&r), ["u8.checked_mul[c-clang]"]);
    assert!(text(&r).contains("expected some:5  got some:6"), "{}", text(&r));
    let root = Root::new(
        &DATA_TEXT.replace("2 3\tsome:6", "2 3\tsome:5"),
        &held("vectors-c/u8.checked_mul[c-clang]", None, Some(&["t.tsv @ u8.checked_mul edge : 2 3"])),
    );
    assert_eq!(root.c().exit_code(), 0);
    // the interpreter's case name is not the C's
    let root = Root::new(&DATA_TEXT.replace("2 3\tsome:6", "2 3\tsome:5"), &entry("vectors-c/u8.checked_mul", None));
    // (and `cm_val` panics on 16 * 16: the `none` row passing shows `_val` was not called, FORMAT.md)
    let r = root.c();
    assert!(r.failures.iter().any(|f| f.contains("names no case")), "{:?}", r.failures);
}

fn plan_of(shape: Shape, want: Want) -> RowPlan {
    RowPlan { row: 0, op: 0, shape, args: Vec::new(), want }
}

#[test]
fn a_call_that_ended_the_program_fails_its_row() {
    // `_some` ended the program; `_val` was not made: the row fails (W2-02: it was taken as not run).
    let p = plan_of(Shape::Opt { some: 0, val: 1 }, Want::None);
    let v = judge(&p, &[Got::Ended("a sanitizer".into())]);
    assert!(matches!(v, Verdict::Fail { internal: false, .. }), "{v:?}");
    assert_eq!(judge(&p, &[Got::NotRun]), Verdict::NotRun);
    let held = plan_of(Shape::Plain(0), Want::Held);
    assert!(matches!(judge(&held, &[Got::Ended("x".into())]), Verdict::Fail { .. }));
    assert!(matches!(judge(&held, &[Got::Internal("x".into())]), Verdict::Fail { internal: true, .. }));
    assert_eq!(judge(&held, &[Got::Panic("x".into())]), Verdict::Pass);
    let panic = plan_of(Shape::Plain(0), Want::Panic);
    assert!(matches!(judge(&panic, &[Got::Internal("x".into())]), Verdict::Fail { internal: true, .. }));
    assert!(matches!(judge(&panic, &[Got::Boundary("x".into())]), Verdict::Fail { .. }));
    // `none`: `_some` alone; `some:`: both
    assert_eq!(judge(&p, &[Got::Value(Value::Bool(false))]), Verdict::Pass);
    let some = plan_of(Shape::Opt { some: 0, val: 1 }, Want::Some(Value::U8(6)));
    assert_eq!(judge(&some, &[Got::Value(Value::Bool(true)), Got::Value(Value::U8(6))]), Verdict::Pass);
    assert!(matches!(judge(&some, &[Got::Value(Value::Bool(false))]), Verdict::Fail { .. }));
}

#[test]
fn the_boundary_records() {
    let r = |status, handler| c::Raw::Returned { status, handler, bytes: vec![7, 0, 0, 0] };
    let s = Scalar::Int(onsa_core::IntKind::U32);
    assert!(matches!(c::got(&r(0, false), s), Got::Value(Value::U32(7))));
    assert!(matches!(c::got(&r(1, true), s), Got::Panic(_)));
    assert!(matches!(c::got(&r(1, false), s), Got::Boundary(_)));
    assert!(matches!(c::got(&r(0, true), s), Got::Boundary(_)));
    assert!(matches!(c::got(&r(2, true), s), Got::Boundary(_)));
    let b = c::Raw::Returned { status: 0, handler: false, bytes: vec![2] };
    assert!(matches!(c::got(&b, Scalar::Bool), Got::Boundary(_)));
}

#[test]
fn op_results_count_the_rows_not_made() {
    let data = Data {
        ops: vec![Op {
            id: "u64.mul".into(),
            fn_: "m".into(),
            file: "f".into(),
            pkg: "p".into(),
            args: vec![],
            ret: "U64".into(),
        }],
        types: vec![(vec![], Scalar::Int(onsa_core::IntKind::U64), false)],
        rows: (0..50)
            .map(|i| Row {
                op: 0,
                file: "f".into(),
                line: i + 1,
                stage: "edge".into(),
                args: vec![i.to_string()],
                expect: Expect::Panic("overflow".into()),
            })
            .collect(),
    };
    let args = |_: usize| String::new();
    let run = |failed: usize, internal: usize, not_run: usize| OpRun {
        compared: 3,
        not_run: (failed..failed + not_run).collect(),
        ended: (not_run > 0).then(|| "the time budget: it ran longer than 60s and was killed".to_string()),
        failed: (0..failed).map(|i| (i, "x".to_string())).collect(),
        internal,
        ..Default::default()
    };
    let ok = op_result(&data, "u64.mul".into(), &run(0, 0, 0), &args);
    assert!(ok.problems.is_empty());
    assert_eq!(ok.rows, Some(0));
    assert_eq!(op_result(&data, "x".into(), &run(2, 0, 0), &args).failure, FailureKind::Ordinary);
    assert_eq!(op_result(&data, "x".into(), &run(2, 2, 0), &args).failure, FailureKind::Internal);
    assert_eq!(op_result(&data, "x".into(), &run(2, 1, 0), &args).failure, FailureKind::Mixed);
    let ended = op_result(&data, "x".into(), &run(1, 0, 40), &args);
    assert_eq!(ended.rows, Some(41));
    // the rows not made are in the digest, each by its id
    assert_eq!(ended.failing.len(), 41);
    assert!(ended.failing.contains(&"f @ u64.mul edge : 40".to_string()), "{:?}", ended.failing);
    assert_eq!(ended.digest, Some(judge::digest(&ended.failing)));
    assert_ne!(ended.digest, op_result(&data, "x".into(), &run(1, 0, 39), &args).digest);
    assert!(
        ended.problems[0].contains("40 of them not run: the program ended in an earlier row (the time budget"),
        "{:?}",
        ended.problems
    );
    let none = op_result(&data, "x".into(), &OpRun::default(), &args);
    assert!(none.problems.iter().any(|p| p.contains("no row ran")), "{:?}", none.problems);
}

#[test]
fn a_run_that_ends_starts_again_at_the_next_operation() {
    crate::c::require("clang").unwrap();
    let dir = crate::c::scratch_dir("onsa_test", "vectors_restart");
    std::fs::create_dir_all(&dir).unwrap();
    // A row: `u32 k`. `k` 1..=6: one record of a `U8` result `k`; 10..: an `Option` row, `_some` true
    // when k is even, then `_val` k; 7 ends the program.
    let src = format!(
        "{}#include <stdint.h>\nstatic void rec(unsigned char r) {{\n  int32_t s = 0; unsigned char h = 0;\n  \
         onsa_driver_write(&s, 4); onsa_driver_write(&h, 1); onsa_driver_write(&r, 1);\n}}\n\
         int main(void) {{\n  setvbuf(stdout, NULL, _IONBF, 0);\n  if (!onsa_driver_signals()) return 5;\n  \
         uint32_t k;\n  while (fread(&k, sizeof k, 1, stdin) == 1) {{\n    if (k == 7) _Exit({});\n    \
         if (k < 10) rec((unsigned char)k);\n    else {{ rec(k % 2 == 0); if (k % 2 == 0) rec((unsigned char)k); }}\n  }}\n  \
         uint32_t end = 0xffffffffu; onsa_driver_write(&end, 4);\n  return 0;\n}}\n",
        crate::c::driver_preamble(&[]),
        crate::c::SIGNAL_EXIT
    );
    std::fs::write(dir.join("p.c"), src).unwrap();
    let exe = dir.join("p");
    let mut cc = std::process::Command::new("clang");
    cc.args(["-std=c11", "-w"]).arg(dir.join("p.c")).arg("-o").arg(&exe);
    crate::c::compile(&mut cc, "p").unwrap();
    let ks = [1u32, 12, 11, 7, 3, 4];
    let inputs: Vec<Vec<u8>> = ks.iter().map(|k| k.to_le_bytes().to_vec()).collect();
    use c::RowRecords::{Opt, Plain};
    let records = [Plain(1), Opt(1), Opt(1), Plain(1), Plain(1), Plain(1)];
    let rows = c::run_rows(&exe, crate::c::Runner::Native, &inputs, &[0, 1, 1, 2, 2, 3], &records).unwrap();
    assert!(matches!(&rows[0][..], [c::Raw::Returned { status: 0, bytes, .. }] if bytes == &[1]), "{rows:?}");
    assert!(
        matches!(&rows[1][..], [c::Raw::Returned { bytes: s, .. }, c::Raw::Returned { bytes: v, .. }] if s == &[1] && v == &[12]),
        "{rows:?}"
    );
    assert!(matches!(&rows[2][..], [c::Raw::Returned { bytes, .. }] if bytes == &[0]), "{rows:?}");
    assert!(matches!(&rows[3][..], [c::Raw::Ended(m)] if m.contains("a fatal signal (caught)")), "{rows:?}");
    assert_eq!(rows[4], [c::Raw::NotRun]);
    assert!(matches!(&rows[5][..], [c::Raw::Returned { bytes, .. }] if bytes == &[4]), "{rows:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_toolchains_are_the_c_checks_that_run() {
    let names: Vec<&str> = c::toolchains().iter().map(|i| i.name).collect();
    assert_eq!(names, ["c-clang", "c-gcc", "c-sanitize", "c-x86"]);
}

#[test]
fn the_repository_data_reads() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let data = Data::load(&root).unwrap_or_else(|e| panic!("{e:?}"));
    assert!(data.ops.len() > 400 && data.rows.len() > 100_000, "{} {}", data.ops.len(), data.rows.len());
    assert!(item::check_packages(&root, &data).is_empty());
}
