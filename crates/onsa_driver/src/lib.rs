//! Pipeline driver: loads sources and runs parse -> resolve -> check.
//!
//! M0: the pipeline is empty and every input yields no diagnostics. Each
//! milestone adds a stage here (`docs/implementation-tasks.md` §4).

use onsa_diag::{Diagnostic, SourceMap};

/// Result of `onsa check`: diagnostics only (no artifacts).
#[derive(Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
}

/// Check every file in `sources` as one package (S-11: a lone file is a
/// one-module package named after the file).
pub fn check(sources: &SourceMap) -> CheckResult {
    let _ = sources;
    CheckResult::default()
}
