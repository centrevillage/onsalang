//! The Core verifier at the stage boundaries (R-82, plan §3.4, D-15).
//!
//! Every stage that outputs Core verifies its output, in every build, so no
//! caller can skip it. Lowering is a stage of `onsa_core` and verifies
//! itself (`onsa_core::lower_with`, which fails with
//! `onsa_core::LowerFailure::Verify`); the stages of the driver (the
//! build-time `const` evaluation in [`crate::build_resolved`]) call
//! [`verify_core`]. A failure is an error of the compiler, not of the
//! program: it comes back as a value ([`VerifyFailure`]) with the stage, the
//! rule the verifier reports, the item and its Core, and the stage function
//! returns it as the internal error of S-67 ([`crate::InternalError`], W1-04).

use std::fmt;

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
            "internal error: the Core verifier rejected the output of {}: {}: in `{}`: {}",
            self.stage.name(),
            self.error.rule,
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

/// Why lowering failed, as the driver reports it. The diagnostics are as
/// lowering made them (the caller fills their sources first).
impl From<onsa_core::LowerFailure> for LowerError {
    fn from(f: onsa_core::LowerFailure) -> Self {
        match f {
            onsa_core::LowerFailure::Diagnostics(d) => LowerError::reported(d),
            onsa_core::LowerFailure::Internal { span, message } => InternalError::lowering(span, message).into(),
            onsa_core::LowerFailure::Verify { error, item_core } => {
                VerifyFailure { stage: CoreStage::Lower, error, item_core }.into()
            }
        }
    }
}

/// Verify the Core a stage of the driver produced (R-82).
pub fn verify_core(module: &onsa_core::Module, stage: CoreStage) -> Result<(), VerifyFailure> {
    onsa_core::verify::with_item(module).map_err(|(error, item_core)| VerifyFailure { stage, error, item_core })
}
