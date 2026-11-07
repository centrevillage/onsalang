//! Every case under `tests/` (plan D-05, R-80 (5)): found by scanning, run
//! through the driver as the CLI and `onsa build` run them, and checked
//! against `tests/pending.toml` and the golden files ([`onsa_tests::run`]).
//! `UPDATE_GOLDEN=1` rewrites the golden files and the copies `.fixK` of the
//! cases that are not pending, but the copies the guard refuses
//! (`onsa_tests::copy_guard`); `UPDATE_GOLDEN=worse` rewrites those too.

#[test]
fn cases() {
    let root = onsa_tests::case::repo_root();
    let report = onsa_tests::run::run_all(&root);
    eprintln!("{}", report.summary());
    assert!(!report.cases.is_empty(), "no case under {}", root.join("tests").display());
    assert!(!report.failed(), "{}", report.failures_text());
}

/// The cases too slow to run every time (X-24): the gate item `heavy`.
#[test]
#[ignore = "heavy: the gate item `heavy` runs it"]
fn heavy_cases() {
    let root = onsa_tests::case::repo_root();
    let report = onsa_tests::run::run_heavy(&root);
    eprintln!("{}", report.summary());
    assert!(!report.cases.is_empty(), "no case under {}", root.join(onsa_tests::case::HEAVY).display());
    assert!(!report.failed(), "{}", report.failures_text());
}
