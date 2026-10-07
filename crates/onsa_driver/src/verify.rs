//! The Core verifier at the stage boundaries (R-82, plan §3.4, D-15).
//!
//! [`verify_core`] is the one place the compiler runs `onsa_core::verify`.
//! Every stage function that outputs Core calls it on its output (lowering
//! in [`crate::lower_core_with`], the build-time `const` evaluation in
//! [`crate::build_resolved`]), so no caller can skip it. A failure is an
//! error of the compiler, not of the program: it comes back as a value
//! ([`VerifyFailure`]) with the stage, the rule the verifier reports, the
//! item and its Core, and the stage function returns it as the internal
//! error of S-67 ([`crate::InternalError`], W1-04).

use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};

use onsa_diag::{Diagnostic, SourceMap};

use crate::InternalError;

/// A stage boundary of the Core (plan §3.4). The target passes (W9-04) add theirs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoreStage {
    /// After lowering and normalization (`lower_core`, `lower_core_with`).
    Lower,
    /// After the build-time evaluation of the `const`s (`inline_consts`).
    Consts,
}

impl CoreStage {
    pub fn name(self) -> &'static str {
        match self {
            CoreStage::Lower => "lowering",
            CoreStage::Consts => "the build-time `const` evaluation",
        }
    }
}

/// The verifier rejected the Core a stage produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifyFailure {
    pub stage: CoreStage,
    /// The function or `const` and the broken rule, as the verifier reports them.
    pub error: onsa_core::VerifyError,
    /// The Core of that item (`onsa dump --core` form), for the bug report.
    pub item_core: String,
}

impl fmt::Display for VerifyFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "internal error: the Core verifier rejected the output of {}: in `{}`: {}",
            self.stage.name(),
            self.error.fn_name,
            self.error.message
        )
    }
}

impl VerifyFailure {
    /// The headline and the Core of the item.
    pub fn report(&self) -> String {
        let mut s = self.to_string();
        if !self.item_core.is_empty() {
            s.push_str("\nCore of the item:\n");
            s.push_str(self.item_core.trim_end());
        }
        s
    }
}

/// Why lowering produced no Core.
#[derive(Debug, Clone)]
pub enum LowerError {
    /// The program uses features lowering does not support (E0200): all of
    /// them, each once (S-67).
    Diagnostics(Vec<Diagnostic>),
    /// An internal error (S-67): a panic, a lowering failure that is not an
    /// unsupported feature, or a Core the verifier rejects.
    Internal(InternalError),
}

impl LowerError {
    /// The diagnostics of lowering or the build as they are reported: every
    /// one, each once (S-67). The one place that reduces them.
    pub fn reported(diagnostics: Vec<Diagnostic>) -> LowerError {
        LowerError::Diagnostics(crate::reduce::exact(diagnostics))
    }

    /// The diagnostics in text form, or the internal error.
    pub fn render(&self, sources: &SourceMap) -> String {
        match self {
            LowerError::Diagnostics(d) => onsa_diag::to_text(sources, d),
            LowerError::Internal(e) => e.render(sources),
        }
    }
}

impl From<VerifyFailure> for LowerError {
    fn from(v: VerifyFailure) -> Self {
        LowerError::Internal(v.into())
    }
}

impl From<InternalError> for LowerError {
    fn from(e: InternalError) -> Self {
        LowerError::Internal(e)
    }
}

static DEBUG_ONLY: AtomicBool = AtomicBool::new(false);

/// Run the verifier only in debug builds of the compiler, for the rest of
/// the process. Only the CLI calls this, to keep its behavior until W8-02
/// runs the verifier in release builds too. Without it (the tests, and
/// every other user of the driver), the verifier always runs.
pub fn verify_core_in_debug_only() {
    DEBUG_ONLY.store(true, Ordering::Relaxed);
}

/// Verify the Core `stage` produced (R-82). The only caller of `onsa_core::verify`.
pub fn verify_core(module: &onsa_core::Module, stage: CoreStage) -> Result<(), VerifyFailure> {
    if DEBUG_ONLY.load(Ordering::Relaxed) && !cfg!(debug_assertions) {
        return Ok(());
    }
    onsa_core::verify(module).map_err(|error| VerifyFailure {
        stage,
        item_core: onsa_core::dump_item(module, &error.fn_name),
        error,
    })
}
