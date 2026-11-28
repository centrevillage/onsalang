//! The Core verifier at the stage boundaries (R-82): a Core that breaks a
//! rule comes back as a failure with the stage, the item, the rule and the
//! item's Core, and every arm of the case runner turns a stage's failure
//! into a failed case.

use std::path::Path;

use onsa_core::{
    Block, ConstId, Expr, ExprKind, FnId, Lit, LocalId, MsgId, PanicOrigin, Rule, Stmt, StmtKind, TyKind, TypeId,
    Types, VerifyError,
};
use onsa_driver::{BuildError, CoreStage, LowerError, VerifyFailure};
use onsa_tests::case::{Case, CaseKind, Setup};
use onsa_tests::run::{HostSteps, Problem, RunOptions, StageFailure, Stages, run_case_with, stage_problem};

const SRC: &str = "const K: I32 = 3\n\npub fn f(x: I32) -> I32 {\n  x + K\n}\n";

/// [`SRC`] checked.
fn analyzed() -> (onsa_driver::Loaded, onsa_driver::Analyzed) {
    let mut loaded = onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file("t.onsa", SRC)).unwrap();
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    (loaded, analyzed)
}

/// The lowered Core of [`SRC`]; lowering verifies it.
fn core() -> (onsa_driver::Loaded, onsa_core::Module) {
    let (loaded, analyzed) = analyzed();
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
    Expr::new(Types::BOOL, span, ExprKind::Lit(Lit::Bool(true)))
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
    assert_eq!((v.error.rule, v.error.span), (Rule::V01, Some(span_of_f(&core().1))), "{v}");
    // The Core of the item, and only of it.
    assert!(v.item_core.starts_with("fn t.f("), "{}", v.item_core);
    assert!(v.item_core.contains("true"), "{}", v.item_core);
    assert!(!v.item_core.contains("const t.K"), "{}", v.item_core);
    let report = v.report();
    for part in ["internal error", "lowering", "V-01", "`t.f`", "type mismatch", "fn t.f("] {
        assert!(report.contains(part), "`{part}` missing from:\n{report}");
    }
    // The same report through the lowering error: the internal error of S-67.
    let rendered = LowerError::Internal(v.clone().into()).render(&loaded.sources);
    assert!(rendered.starts_with(&report), "{rendered}");
    assert!(rendered.contains("a bug in the compiler"), "{rendered}");
    // The position of the node, from the verifier.
    assert!(rendered.contains("  --> t.onsa:3:"), "{rendered}");
}

/// Lowering verifies its own output (W8-02 U5c): its failure is the
/// verifier's at the stage of lowering, with the rule and the position.
#[test]
fn the_verify_failure_of_lowering_is_reported_at_its_stage() {
    let (loaded, v) = broken();
    let (error, item_core) = (v.error.clone(), v.item_core.clone());
    let lowered = LowerError::from(onsa_core::LowerFailure::Verify { error, item_core });
    let LowerError::Internal(_) = &lowered else { panic!("not an internal error: {lowered:?}") };
    let rendered = lowered.render(&loaded.sources);
    assert!(rendered.starts_with(&v.report()), "{rendered}");
    for part in ["the output of lowering", "V-01", "`t.f`", "  --> t.onsa:3:", "a bug in the compiler"] {
        assert!(rendered.contains(part), "`{part}` missing from:\n{rendered}");
    }
}

/// The one way of lowering, in every build (no flag turns the verifier
/// off): the driver's stage enters the verifier once, inside lowering.
#[test]
fn lowering_runs_the_verifier_once() {
    let (_, analyzed) = analyzed();
    let (lowered, times) = onsa_diag::timing::record(|| onsa_driver::lower_core(&analyzed));
    assert!(lowered.is_ok());
    let entered = |p| times.phases.iter().find(|&&(q, _, _)| q == p).map(|&(_, _, n)| n);
    use onsa_diag::timing::Phase;
    assert_eq!((entered(Phase::Lower), entered(Phase::Verify)), (Some(1), Some(1)), "{times:?}");
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
    set_body(&mut m, Vec::new(), Expr::new(Types::int(onsa_core::IntKind::I32), span, ExprKind::Local(LocalId(999))));
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
/// itself is not run here: its own checks of these ids, V-20, are
/// `onsa_core`'s tests).
#[test]
fn the_dump_marks_ids_out_of_range() {
    let (_, mut m) = core();
    let span = span_of_f(&m);
    let unit = |kind| Stmt { span, kind: StmtKind::Expr(Expr::new(Types::UNIT, span, kind)) };
    let mut other = Types::default();
    let n = m.tys.kinds().len();
    let far = (0..).map(|i| other.intern(TyKind::Array(Types::U32, i))).find(|t| t.index() > n).expect("a type");
    let stmts = vec![
        Stmt { span, kind: StmtKind::Let(LocalId(998), Expr::new(Types::BOOL, span, ExprKind::Lit(Lit::Bool(true)))) },
        unit(ExprKind::Call { fn_: FnId(999), args: Vec::new() }),
        unit(ExprKind::Const(ConstId(999))),
        unit(ExprKind::Struct { ty: TypeId(999), fields: Vec::new() }),
        unit(ExprKind::Variant { ty: TypeId(997), tag: 0, fields: Vec::new() }),
        unit(ExprKind::Zeroed),
        // A type of another table, out of this one.
        Stmt { span, kind: StmtKind::Expr(Expr::new(far, span, ExprKind::Zeroed)) },
    ];
    let value = Expr::new(
        m.tys.intern(TyKind::Struct(TypeId(996))),
        span,
        ExprKind::Panic { msg: MsgId(999), origin: PanicOrigin::Panic, shown: Vec::new() },
    );
    set_body(&mut m, stmts, value);
    let text = onsa_core::dump_item(&m, "t.f");
    for part in [
        "let <bad local 998>: <bad local 998> = true",
        "<bad fn 999>()",
        "<bad const 999>",
        "<bad type 999> {}",
        "<bad type 997>.0",
        "panic(<bad message 999>)",
        &format!("zeroed:<bad ty {}>", far.index()),
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
        error: VerifyError {
            rule: Rule::V01,
            fn_name: "m.f".into(),
            span: None,
            message: format!("injected at {what}"),
        },
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
        manifest: frag.manifest_source("m.onsa"),
        files: vec![onsa_driver::SourceFile { path: "m.onsa".into(), text: CASE.into() }],
        ..Default::default()
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
        RunOptions { golden: onsa_tests::golden::Update::Off, host_steps: HostSteps::Run },
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

// ---------------------------------------------------------------- V-22 of a lowered Core (W8-02 U5b)

/// Structs `S0` to `S{n}`, each holding the next, and `const`s that read
/// each other, each writing up to 100 levels of the value of `C0`: a value
/// `n + 1` structs deep, past `CORE_DEPTH_LIMIT` (the form of R-319 the
/// user accepted as an internal error, W8-02). `folded`: each `const` after
/// the one it reads, so the check folds the value of `C0` and lowering
/// writes it whole; else before, and `C0` passes its value through a call,
/// so the build-time evaluation writes it (`consts_stage`).
fn const_chain(n: usize, folded: bool) -> String {
    let mut s: String = (0..n).map(|i| format!("pub struct S{i} {{\n  a: S{},\n}}\n", i + 1)).collect();
    s += &format!("pub struct S{n} {{\n  b: U32,\n}}\nfn pass(x: S0) -> S0 {{\n  x\n}}\n");
    let (mut i, mut consts) = (0, Vec::new());
    while i < n {
        let (end, k) = ((i + 100).min(n), consts.len());
        let open: String = (i..end).map(|j| format!("S{j} {{ a: ")).collect();
        let inner = if end == n { format!("S{n} {{ b: 7 }}") } else { format!("C{}", k + 1) };
        let value = format!("{open}{inner}{}", " }".repeat(end - i));
        let value = if k == 0 && !folded { format!("pass({value})") } else { value };
        consts.push(format!("pub const C{k}: S{i} = {value}\n"));
        i = end;
    }
    if folded {
        consts.reverse();
    }
    s + &consts.concat() + "@export\npub fn get() -> U32 {\n  let _ = C0\n  7\n}\n"
}

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    onsa_diag::stack::spawn("depth", f).unwrap().join().unwrap()
}

/// Lowering `src`, a package of the file `m.onsa` with a C target: the error
/// rendered (none: empty) and whether the verifier's phase ran; with
/// `build`, the build of the target (and its error).
fn lowered(src: String, build: bool) -> (String, bool) {
    const MANIFEST: &str = "[package]\nname = \"m\"\nedition = \"2026\"\n\n[export]\nprefix = \"m_\"\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"poison\"\nprovides = []\n";
    on_large_stack(move || {
        let manifest = onsa_driver::ManifestSource {
            path: "onsa.toml".into(),
            text: MANIFEST.into(),
            form: onsa_driver::ManifestForm::File,
        };
        let file = onsa_driver::SourceFile { path: "m.onsa".into(), text: src };
        let input = onsa_driver::PackageInput { manifest: Some(manifest), files: vec![file], ..Default::default() };
        let mut loaded = onsa_driver::Loaded::from_input(input).unwrap();
        let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
        assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        let (rendered, times) = onsa_diag::timing::record(|| {
            if build {
                let built = onsa_driver::build_analyzed(&loaded, &analyzed, "host");
                built.err().map(|e| match e {
                    BuildError::Internal { sources, error } => error.render(&sources),
                    e => format!("not an internal error: {e:?}"),
                })
            } else {
                onsa_driver::lower_core(&analyzed).err().map(|e| e.render(&loaded.sources))
            }
        });
        let verified = times.phases.iter().any(|&(p, _, n)| p == onsa_diag::timing::Phase::Verify && n > 0);
        (rendered.unwrap_or_default(), verified)
    })
}

/// A `const` whose value nests past the limit stops lowering right after
/// the items are lowered (V-22 before the walks, which recurse), before the
/// verifier of the stage, and with no Core of the item.
#[test]
fn a_const_too_deep_stops_lowering_before_the_walks() {
    let n = onsa_core::CORE_DEPTH_LIMIT as usize;
    // `C0` is its structs and the literal of `S{n}`'s field deep.
    assert_eq!(lowered(const_chain(n - 2, true), false), (String::new(), true));
    let (rendered, verified) = lowered(const_chain(n - 1, true), false);
    for part in [
        "internal error",
        "the output of lowering",
        "V-22",
        "`m.C0`",
        format!("deeper than {n}").as_str(),
        "  --> m.onsa:",
    ] {
        assert!(rendered.contains(part), "`{part}` missing from:\n{rendered}");
    }
    assert!(!rendered.contains("Core of the item") && !verified, "{rendered}");
}

/// Of a Core too deep and an unsupported feature, the E0200 (a Core with
/// placeholders is dropped anyway).
#[test]
fn of_a_core_too_deep_the_e0200s_come_first() {
    let unsupported = "fn take(f: fn(U32) -> U32) -> U32 {\n  1\n}\npub rt fn mk(n: U32) -> U32 {\n  n\n}\npub fn go() -> U32 {\n  let f = mk\n  take(f)\n}\n";
    let n = onsa_core::CORE_DEPTH_LIMIT as usize;
    let (rendered, _) = lowered(format!("{}{unsupported}", const_chain(n, true)), false);
    assert!(rendered.contains("error[E0200]") && !rendered.contains("V-22"), "{rendered}");
}

/// The build-time evaluation that writes a value past the limit is
/// rejected at its stage, with no Core of the item (and no C).
#[test]
fn a_const_the_build_evaluates_too_deep_is_rejected_at_its_stage() {
    let n = onsa_core::CORE_DEPTH_LIMIT as usize;
    assert_eq!(lowered(const_chain(n - 2, false), true).0, "");
    let (rendered, _) = lowered(const_chain(n - 1, false), true);
    for part in ["internal error", "the build-time `const` evaluation", "V-22", "`m.C0`"] {
        assert!(rendered.contains(part), "`{part}` missing from:\n{rendered}");
    }
    assert!(!rendered.contains("Core of the item"), "{rendered}");
}

/// The form the user accepted (W8-02, R-319): a chain of `const`s past the
/// limit is an internal error of the command, exit 101, as `onsa` runs it.
#[test]
fn a_const_too_deep_is_an_internal_error_of_the_command() {
    let text = const_chain(onsa_core::CORE_DEPTH_LIMIT as usize, true).replace("@export\n", "");
    let request =
        onsa_tests::serve::Request { words: "dump --core".into(), files: vec![("m.onsa".into(), text.into())] };
    let answer = onsa_tests::serve::answer(&request);
    let err = String::from_utf8_lossy(&answer.err);
    assert_eq!((answer.code, answer.out.is_empty()), (101, true), "{err}");
    assert!(err.contains("V-22") && err.contains("`m.C0`") && !err.contains("Core of the item"), "{err}");
}

// The forms of the most nodes a level of the source (W8-02 U5b, the break
// side's H1): at the source depth 256 (§2.5), the limit, each lowers in
// `CORE_DEPTH_LIMIT` (a `match~` in an arm, about 5 nodes a level, the most).

const LP: &str = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x * 0.5 + prev~(x) * 0.5\n}\n";

/// `n` times `wrap` around `inner`.
fn nested(n: usize, inner: &str, wrap: impl Fn(String, usize) -> String) -> String {
    (0..n).fold(inner.to_string(), wrap)
}

/// A flow of `body` after [`LP`] and `before`.
fn flow_of(before: &str, body: String) -> String {
    format!(
        "{LP}{before}pub flow f(x: F32 at sample, c: Bool at sample, k: U32 at sample) -> F32 at sample {{\n  {body}\n}}\n"
    )
}

/// `src` is 256 levels deep (§2.5) and lowers, with no error.
fn lowers_at_the_source_limit(src: String) {
    let text = src.clone();
    let levels = on_large_stack(move || onsa_syntax::parse(onsa_diag::FileId(0), &text).levels);
    assert_eq!(levels.iter().max(), Some(&256), "{levels:?}");
    assert_eq!(lowered(src, false), (String::new(), true));
}

#[test]
fn nested_calls_of_a_flow_at_the_source_limit_lower() {
    lowers_at_the_source_limit(flow_of("", nested(255, "x", |e, _| format!("lp~({e})"))));
}

#[test]
fn a_match_of_a_flow_nested_in_an_arm_at_the_source_limit_lowers() {
    let body = nested(254, "x", |e, _| format!("match~ k {{\n 0 => {e},\n _ => lp~(x),\n }}"));
    lowers_at_the_source_limit(flow_of("", body));
}

#[test]
fn an_if_of_a_flow_nested_at_the_source_limit_lowers() {
    lowers_at_the_source_limit(flow_of("", nested(127, "x", |e, _| format!("if~ c {{ {e} }} else {{ lp~(x) }}"))));
}

#[test]
fn sums_of_a_par_nested_at_the_source_limit_lower() {
    let sum2 = "pub rt fn sum2(xs: [F32; 2]) -> F32 {\n  xs[0] + xs[1]\n}\n";
    let body = nested(63, "lp~(lp~(lp~(x)))", |e, i| format!("sum2(par~ i{i} in 0 ..< 2 {{ lp~({e}) }})"));
    lowers_at_the_source_limit(flow_of(sum2, body));
}

#[test]
fn a_chain_of_tries_at_the_source_limit_lowers() {
    let body = nested(127, "x", |e, _| format!("g({e})?"));
    let g = "pub fn g(a: I32) -> Option[I32] {\n  Some(a)\n}\n";
    lowers_at_the_source_limit(format!("{g}pub fn f(x: I32) -> Option[I32] {{\n  Some({body})\n}}\n"));
}

#[test]
fn values_of_blocks_nested_at_the_source_limit_lower() {
    let body = nested(255, "1", |e, i| format!("{{ let a{i} = {e}\n a{i} }}"));
    lowers_at_the_source_limit(format!("pub fn f() -> I32 {{\n  {body}\n}}\n"));
}

/// A Core at the limit, of the form that takes the most stack a node
/// (nested calls that take and return a struct by value, in the C backend;
/// `CORE_DEPTH_LIMIT`), goes through every stage after lowering on the
/// stack of a command: the verifier, the fold, the copies, the dump, the
/// interpreter and the C backend.
#[test]
fn a_core_at_the_limit_goes_through_every_stage() {
    const NESTED: &str = "pub struct S {\n  a: I32,\n  b: I32,\n}\n\nfn g(s: S) -> S {\n  S { a: s.b, b: s.a }\n}\n\npub fn f(s: S) -> S {\n  g(s)\n}\n\npub fn h(a: I32) -> I32 {\n  f(S { a: a, b: 4 }).a\n}\n";
    on_large_stack(|| {
        let mut loaded =
            onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file("t.onsa", NESTED)).unwrap();
        let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
        let mut m = onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let f = m.fns.iter().position(|f| f.name == "t.f").expect("t.f");
        let call = m.fns[f].body.as_ref().and_then(|b| b.value.as_deref()).expect("`g(s)`").clone();
        let with_arg = |e: Expr| {
            let mut c = call.clone();
            let ExprKind::Call { args, .. } = &mut c.kind else { panic!("not a call: {call:?}") };
            args[0].expr = e;
            c
        };
        let ExprKind::Call { args, .. } = &call.kind else { panic!("not a call: {call:?}") };
        // The body, the calls and `s`.
        let calls = (0..onsa_core::CORE_DEPTH_LIMIT - 2).fold(args[0].expr.clone(), |e, _| with_arg(e));
        set_body(&mut m, Vec::new(), calls);
        // The copies of the new body (V-20).
        m.moves = onsa_core::lower::moves::collect(&m);
        onsa_driver::verify_core(&m, CoreStage::Lower).expect("a Core at the limit");
        onsa_core::lower::fold::fold_module(&mut m.clone());
        assert!(onsa_core::dump(&m).contains("t.g(t.g("));
        let s = onsa_interp::Value::Struct(vec![onsa_interp::Value::I32(3), onsa_interp::Value::I32(4)]);
        let got = onsa_interp::Interp::new(&m).call(FnId(f as u32), vec![s]);
        // An even number of swaps.
        assert!(
            matches!(&got, Ok(onsa_interp::Value::Struct(v)) if matches!(v[..], [onsa_interp::Value::I32(3), onsa_interp::Value::I32(4)])),
            "{got:?}"
        );
        let opts = onsa_backend_c::EmitOptions {
            package: "t".into(),
            prefix: Some("t_".into()),
            // `t.h`: a function that returns an aggregate is not exported (E0200).
            export_fns: vec!["t.h".into()],
            ..Default::default()
        };
        let c = onsa_backend_c::emit(&m, &opts).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(c.source.matches("t__g(").count() >= onsa_core::CORE_DEPTH_LIMIT as usize - 2);
    })
}
