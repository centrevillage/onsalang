//! The analysis of std alone, made once and continued by the analyses of the
//! packages that depend on it (W5-18): a copy of it, each stage run on what
//! is after its part ([`Start`]). A continued analysis is the fresh one of
//! the package, as std's part is the same whatever is after it, but where a
//! package writes in std's tables (an `impl` of a builtin type or of a std
//! type): there it falls back to the fresh one ([`Fallback`]).

use std::sync::{Arc, Mutex, PoisonError};

use crate::{Analysis, DefId, DefKind, ModId, Package, analyze, flatten, run};

/// Where the stages start in an analysis (D-15): what is before is of the
/// base it continues, each stage done; all of a fresh one is after. Its
/// readers are the ranges below, and [`analyze_on`] alone writes it.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Start {
    pkgs: usize,
    mods: u32,
    defs: u32,
}

/// A continued analysis met a package that writes in std's tables: it is
/// dropped for the fresh one.
#[derive(Debug)]
pub(crate) struct Fallback;

impl Analysis {
    /// The packages of `flat` (the order of [`flatten`]) the stages run on.
    pub(crate) fn new_pkgs<'f, 'p>(
        &self,
        flat: &'f [&'p Package],
    ) -> impl Iterator<Item = (usize, &'p Package)> + use<'f, 'p> {
        flat.iter().copied().enumerate().skip(self.start.pkgs)
    }

    /// The modules the stages run on.
    pub(crate) fn new_mods(&self) -> impl Iterator<Item = ModId> + use<> {
        (self.start.mods..self.modules.mods.len() as u32).map(ModId)
    }

    /// The defs the stages run on, those there now.
    pub(crate) fn new_defs(&self) -> impl Iterator<Item = DefId> + use<> {
        (self.start.defs..self.defs.len() as u32).map(DefId)
    }

    /// Whether the stages run on `d`.
    pub(crate) fn is_new(&self, d: DefId) -> bool {
        d.0 >= self.start.defs
    }

    /// Whether this analysis continued a base (it did not fall back).
    pub fn continues(&self) -> bool {
        self.start.defs > 0
    }
}

/// std analyzed alone, which the analyses of the packages that depend on it
/// continue ([`analyze_on`]). Empty when std alone has a diagnostic: every
/// analysis is then fresh.
#[derive(Debug)]
pub struct Base {
    std: Arc<Package>,
    pub(crate) analysis: Option<Analysis>,
}

impl Base {
    /// The base of `std`. A def of a flow in it is an internal error: the
    /// defs a flow makes are numbered after the user's in a fresh analysis,
    /// so a std with a flow needs another order (`ModId`, `DefId` the same).
    pub fn new(std: Arc<Package>) -> Base {
        let a = analyze(&std);
        if let Some(f) = a.defs.iter().find(|d| matches!(d.kind, DefKind::Flow(_))) {
            onsa_diag::internal::bug(
                Some(f.span),
                "std declares a flow, which its base does not number as a fresh analysis",
            );
        }
        let clean = std.modules.iter().all(|m| m.parsed.diagnostics.is_empty())
            && a.diagnostics.is_empty()
            && a.path_diagnostics.is_empty();
        Base { std, analysis: clean.then_some(a) }
    }

    /// Whether analyses continue it (std alone has no diagnostic).
    pub fn usable(&self) -> bool {
        self.analysis.is_some()
    }

    /// A copy of the base to continue with `pkg`, whose first package is its
    /// std (the same value): none for another package.
    fn copy_for(&self, pkg: &Package) -> Option<Analysis> {
        let base = self.analysis.as_ref()?;
        if !std::ptr::eq(*flatten(pkg).first()?, &*self.std) {
            return None;
        }
        let mut a = base.clone();
        a.start = Start { pkgs: a.modules.roots.len(), mods: a.modules.mods.len() as u32, defs: a.defs.len() as u32 };
        Some(a)
    }
}

/// Analyze `pkg` continuing `base`: the same as [`analyze`], which it falls
/// back to for a package with another std or that writes in std's tables.
/// The lock is held while the base is copied.
pub fn analyze_on(pkg: &Package, base: &Mutex<Base>) -> Analysis {
    // Poisoned when a copy panicked: nothing writes the base under the lock,
    // so it is whole.
    let copy = base.lock().unwrap_or_else(PoisonError::into_inner).copy_for(pkg);
    match copy.map(|a| run(pkg, a)) {
        Some(Ok(a)) => a,
        Some(Err(Fallback)) | None => analyze(pkg),
    }
}
