//! The Core verifier at the stage boundaries (R-82): a Core that breaks a
//! rule comes back as a failure with the stage, the item, the rule and the
//! item's Core, and every arm of the case runner turns a stage's failure
//! into a failed case.

use std::path::Path;

use onsa_core::{Block, ConstId, Expr, ExprKind, FnId, Lit, LocalId, MsgId, Stmt, StmtKind, Ty, TypeId, VerifyError};
use onsa_driver::{BuildError, CoreStage, LowerError, VerifyFailure};
use onsa_tests::case::{Case, CaseKind, Setup};
use onsa_tests::run::{HostSteps, Problem, RunOptions, StageFailure, Stages, run_case_with, stage_problem};

const SRC: &str = "const K: I32 = 3\n\npub fn f(x: I32) -> I32 {\n  x + K\n}\n";

/// The lowered Core of [`SRC`]; `lower_core` verifies it.
fn core() -> (onsa_driver::Loaded, onsa_core::Module) {
    let input = onsa_driver::PackageInput {
        manifest: None,
        files: vec![onsa_driver::SourceFile { path: "t.onsa".into(), text: SRC.into() }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    let module = onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    (loaded, module)
}

/// Replace the body of `t.f` by `stmts` and `value`.
fn set_body(m: &mut onsa_core::Module, stmts: Vec<Stmt>, value: Expr) {
    let f = m.fns.iter_mut().find(|f| f.name == "t.f").expect("t.f");
    f.body = Some(Block { stmts, value: Some(Box::new(value)) });
}

fn span_of_f(m: &onsa_core::Module) -> onsa_diag::Span {
    m.fns.iter().find(|f| f.name == "t.f").expect("t.f").span
}

fn bool_lit(span: onsa_diag::Span) -> Expr {
    Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(true)))
}

/// The Core of [`SRC`] with `t.f` returning a `Bool`, and the verifier's failure.
fn broken() -> (onsa_driver::Loaded, VerifyFailure) {
    let (loaded, mut m) = core();
    let span = span_of_f(&m);
    set_body(&mut m, Vec::new(), bool_lit(span));
    let v = onsa_driver::verify_core(&m, CoreStage::Lower).expect_err("the verifier accepts a broken Core");
    (loaded, v)
}

#[test]
fn a_broken_function_is_reported_with_its_stage_rule_and_core() {
    let (_, m) = core();
    assert_eq!(onsa_driver::verify_core(&m, CoreStage::Lower), Ok(()));
    let (loaded, v) = broken();
    assert_eq!(v.stage, CoreStage::Lower);
    assert_eq!(v.error.fn_name, "t.f");
    assert!(v.error.message.contains("type mismatch"), "{v}");
    // The Core of the item, and only of it.
    assert!(v.item_core.starts_with("fn t.f("), "{}", v.item_core);
    assert!(v.item_core.contains("true"), "{}", v.item_core);
    assert!(!v.item_core.contains("const t.K"), "{}", v.item_core);
    let report = v.report();
    for part in ["internal error", "lowering", "`t.f`", "type mismatch", "fn t.f("] {
        assert!(report.contains(part), "`{part}` missing from:\n{report}");
    }
    // The same report through the lowering error: the internal error of S-67.
    let rendered = LowerError::Internal(v.clone().into()).render(&loaded.sources);
    assert!(rendered.starts_with(&report), "{rendered}");
    assert!(rendered.contains("a bug in the compiler"), "{rendered}");
}

#[test]
fn a_broken_const_is_reported_at_the_const_stage() {
    let (_, mut m) = core();
    let c = m.consts.iter_mut().find(|c| c.name == "t.K").expect("t.K");
    c.init = bool_lit(c.init.span);

    let v = onsa_driver::verify_core(&m, CoreStage::Consts).expect_err("the verifier accepts a broken Core");
    assert_eq!(v.stage, CoreStage::Consts);
    assert_eq!(v.error.fn_name, "t.K");
    assert!(v.item_core.starts_with("const t.K: I32 = true"), "{}", v.item_core);
    assert!(v.report().contains("the build-time `const` evaluation"), "{}", v.report());
}

/// W1-05/b: a local out of range. The verifier reports it as a value, and
/// the report (with the item's Core) is made without a panic.
#[test]
fn a_local_out_of_range_is_reported_without_a_panic() {
    let (_, mut m) = core();
    let span = span_of_f(&m);
    set_body(&mut m, Vec::new(), Expr::new(Ty::Int(onsa_core::IntKind::I32), span, ExprKind::Local(LocalId(999))));
    let v = onsa_driver::verify_core(&m, CoreStage::Lower).expect_err("the verifier accepts a local out of range");
    assert_eq!(v.error.fn_name, "t.f");
    assert!(v.error.message.contains("local out of range"), "{v}");
    assert!(v.item_core.contains("<bad local 999>"), "{}", v.item_core);
    let report = v.report();
    for part in ["`t.f`", "local out of range", "<bad local 999>"] {
        assert!(report.contains(part), "`{part}` missing from:\n{report}");
    }
}

/// The dump marks every id out of range instead of panicking (the verifier
/// itself is not run here: its own checks of these ids are W8-02).
#[test]
fn the_dump_marks_ids_out_of_range() {
    let (_, mut m) = core();
    let span = span_of_f(&m);
    let unit = |kind| Stmt { span, kind: StmtKind::Expr(Expr::new(Ty::Unit, span, kind)) };
    let stmts = vec![
        Stmt { span, kind: StmtKind::Let(LocalId(998), Expr::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(true)))) },
        unit(ExprKind::Call { fn_: FnId(999), args: Vec::new() }),
        unit(ExprKind::Const(ConstId(999))),
        unit(ExprKind::Struct { ty: TypeId(999), fields: Vec::new() }),
        unit(ExprKind::Variant { ty: TypeId(997), tag: 0, fields: Vec::new() }),
        unit(ExprKind::Zeroed),
    ];
    let value = Expr::new(Ty::Struct(TypeId(996)), span, ExprKind::Panic(MsgId(999)));
    set_body(&mut m, stmts, value);
    let text = onsa_core::dump_item(&m, "t.f");
    for part in [
        "let <bad local 998>: <bad local 998> = true",
        "<bad fn 999>()",
        "<bad const 999>",
        "<bad type 999> {}",
        "<bad type 997>.0",
        "panic(<bad message 999>)",
    ] {
        assert!(text.contains(part), "`{part}` missing from:\n{text}");
    }
    // The whole module too.
    assert!(onsa_core::dump(&m).contains("<bad fn 999>()"));
}

#[test]
fn every_kind_of_stage_failure_is_an_internal_error() {
    let (loaded, v) = broken();
    let sources = &loaded.sources;
    let internal: onsa_driver::InternalError = v.clone().into();
    let lower = LowerError::Internal(internal.clone());
    let build = BuildError::Internal { sources: sources.clone(), error: Box::new(internal.clone()) };
    for (failure, at) in [
        (StageFailure::Lower(&lower), None),
        (StageFailure::Build { target: "host", error: &build }, Some("build of `host`")),
        (StageFailure::Interface(&internal), None),
    ] {
        let Problem::Internal(text) = stage_problem(sources, failure) else {
            panic!("not an internal error: {failure:?}")
        };
        for part in ["internal error", "`t.f`", "type mismatch", "fn t.f("] {
            assert!(text.contains(part), "`{part}` missing from:\n{text}");
        }
        assert_eq!(text.contains("build of"), at.is_some(), "{text}");
        if let Some(at) = at {
            assert!(text.contains(at), "{text}");
        }
    }
}

// ---------------------------------------------------------------- the runner's arms

fn injected(what: &str) -> VerifyFailure {
    VerifyFailure {
        stage: CoreStage::Lower,
        error: VerifyError { fn_name: "m.f".into(), message: format!("injected at {what}") },
        item_core: String::new(),
    }
}

/// Stages that fail with the verifier, each with its own message.
const FAILING: Stages = Stages {
    lower_core: |_| Err(LowerError::Internal(injected("lower_core").into())),
    build: |_, _, _| {
        Err(BuildError::Internal {
            sources: onsa_diag::SourceMap::default(),
            error: Box::new(injected("build").into()),
        })
    },
    interface: |_| Err(injected("interface").into()),
};

/// A case that reaches every stage: a target (the build), `mode = "test"`
/// (lowering) and the golden interface.
const CASE: &str = "// onsa.toml
// [package]
// name = \"m\"
// edition = \"2026\"
//
// [targets.a]
// kind = \"source\"
// lang = \"c\"
// platform = \"host\"
// panic = \"trap\"
// provides = []
//
// [test]
// mode = \"test\"
// golden = [\"core\", \"interface\"]

pub fn f(x: I32) -> I32 {
  x + 1
}

test \"f\" {
  assert f(1) == 2
}
";

/// Every arm of the runner that gets a stage's failure reports it: a
/// swallowed arm loses its message.
#[test]
fn the_runner_reports_the_failure_of_every_stage() {
    let frag = onsa_tests::fragment::parse(CASE).expect("fragment").expect("a fragment");
    let input = onsa_driver::PackageInput {
        manifest: frag.manifest,
        files: vec![onsa_driver::SourceFile { path: "m.onsa".into(), text: CASE.into() }],
        root: None,
    };
    let case = Case {
        path: "tests/verify/m.onsa".into(),
        kind: CaseKind::File,
        name: "m".into(),
        setup: Ok(Setup { input, test: frag.test }),
    };
    let run = run_case_with(
        &FAILING,
        Path::new("/nonexistent"),
        &case,
        RunOptions { write_golden: false, host_steps: HostSteps::Run },
    );
    assert!(run.ran, "{:?}", run.problems);
    let failed: Vec<&String> = run
        .problems
        .iter()
        .filter_map(|p| match p {
            Problem::Internal(t) => Some(t),
            _ => None,
        })
        .collect();
    assert_eq!(failed.len(), 3, "{:?}", run.problems);
    for (what, at) in [("lower_core", None), ("build", Some("build of `a`")), ("interface", None)] {
        let hit = failed.iter().find(|t| t.contains(&format!("injected at {what}")));
        let Some(text) = hit else { panic!("the failure of `{what}` is not reported: {:?}", run.problems) };
        assert!(text.contains("`m.f`"), "{text}");
        if let Some(at) = at {
            assert!(text.contains(at), "{text}");
        }
    }
    // Nothing ran on the Core that did not come.
    assert!(run.tests.is_empty(), "{:?}", run.tests);
}
