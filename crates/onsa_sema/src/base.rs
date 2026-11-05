//! The analysis of std alone, made once and continued by the analyses of the
//! packages that depend on it (W5-18): a copy of it, each stage run on what
//! is after its part ([`Start`]). A continued analysis is the fresh one of
//! the package, as std's part is the same whatever is after it, but where a
//! package writes in std's tables (an `impl` of a builtin type or of a std
//! type): there it falls back to the fresh one ([`Fallback`]).

use std::sync::{Arc, Mutex, PoisonError};

use onsa_diag::FileId;
use onsa_syntax::ParsedAst;
use serde::{Deserialize, Serialize};

use crate::{Analysis, DefId, DefKind, ModId, Module, Package, PackageRole, analyze, flatten, run, std_modules};

/// Where the stages start in an analysis (D-15): what is before is of the
/// base it continues, each stage done; all of a fresh one is after. Its
/// readers are the ranges below, and [`analyze_on`] alone writes it.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
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

/// Why a base was not written or read back.
#[derive(Debug)]
pub enum BaseError {
    /// The package is not the embedded std, the one package read back.
    NotEmbedded,
    /// std alone has a diagnostic: a fresh analysis reports it, which reads
    /// the tree a std read back has not ([`Module::tree`]).
    Unusable,
    /// The format's: a value that does not write, or bytes that do not read.
    Format(postcard::Error),
    /// Bytes are left after the base.
    Trailing(usize),
    /// The modules read are not those of the embedded std.
    OtherModules,
}

/// std analyzed alone, which the analyses of the packages that depend on it
/// continue ([`analyze_on`]). Empty when std alone has a diagnostic: every
/// analysis is then fresh.
#[derive(Debug)]
pub struct Base {
    pub(crate) std: Arc<Package>,
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

    /// The bytes [`Base::decode`] reads: each module but its text and its
    /// tree, and the analysis. A table is written in the order of its
    /// entries, so the bytes are the same from tables of the same seed
    /// ([`onsa_diag::hash::with_seed`]), and another seed reads them.
    pub fn encode(&self) -> Result<Vec<u8>, BaseError> {
        if !is_embedded(&self.std) {
            return Err(BaseError::NotEmbedded);
        }
        let Some(analysis) = &self.analysis else { return Err(BaseError::Unusable) };
        let modules: Vec<_> = self.std.modules.iter().map(|m| (&m.segments, m.file, &m.parsed)).collect();
        postcard::to_stdvec(&(modules, analysis)).map_err(BaseError::Format)
    }

    /// The base [`Base::encode`] wrote and its std, the texts of the modules
    /// taken from [`std_modules`]. The tables are made again with this
    /// thread's seed. Its std is the one analyses continue it from
    /// ([`Base::copy_for`]).
    pub fn decode(bytes: &[u8]) -> Result<(Arc<Package>, Base), BaseError> {
        type Written = (Vec<(Vec<String>, FileId, ParsedAst)>, Analysis);
        let ((parts, analysis), rest): (Written, _) = postcard::take_from_bytes(bytes).map_err(BaseError::Format)?;
        if !rest.is_empty() {
            return Err(BaseError::Trailing(rest.len()));
        }
        let table = std_modules();
        if parts.len() != table.len() || parts.iter().zip(table).any(|(p, m)| p.0 != m.segments) {
            return Err(BaseError::OtherModules);
        }
        let modules = parts
            .into_iter()
            .zip(table)
            .map(|((segments, file, parsed), m)| Module {
                segments,
                file,
                text: m.text.to_string(),
                parsed,
                tree: None,
            })
            .collect();
        let std = Arc::new(Package::std(modules));
        Ok((std.clone(), Base { std, analysis: Some(analysis) }))
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

/// Whether `pkg` is the embedded std: what [`Base::decode`] makes from the
/// bytes and [`std_modules`] is `pkg`.
fn is_embedded(pkg: &Package) -> bool {
    let table = std_modules();
    pkg.role == PackageRole::Std
        && pkg.deps.is_empty()
        && pkg.modules.len() == table.len()
        && pkg.modules.iter().zip(table).all(|(m, t)| m.segments == t.segments && m.text == t.text)
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
