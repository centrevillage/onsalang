//! The manifest `onsa.toml` (spec §15.3): its typed values with their places
//! ([`Spanned`]), the closed table ([`table`]) and the one reader ([`read`]).

mod read;
pub mod table;

pub use read::{read, shown};

use std::collections::BTreeMap;
use std::ops::Range;

use onsa_diag::{Diagnostic, FileId};

use crate::ManifestForm;

/// A value of the manifest with its places in the text, in bytes: `key`, the
/// key that names it (for a table, the last key of its header); `span`, the
/// value (for a table, from its header to its last value). An implicit table
/// (`targets` of `[targets.t]`) has the place of the key that made it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Spanned<T> {
    pub value: T,
    pub key: Range<usize>,
    pub span: Range<usize>,
}

impl<T> Spanned<T> {
    /// A value without a place (made by a test).
    pub fn new(value: T) -> Spanned<T> {
        Spanned { value, key: 0..0, span: 0..0 }
    }
}

/// The manifest `onsa.toml` (spec §15.3). `[export]` and `[targets.*]` are
/// used by `onsa build` (T4-5); `bind` is read but not supported yet.
#[derive(Debug, Default, Clone)]
pub struct Manifest {
    pub package: Spanned<ManifestPackage>,
    /// By package name.
    pub dependencies: BTreeMap<String, Spanned<String>>,
    pub export: Option<Spanned<ManifestExport>>,
    /// By target name.
    pub targets: BTreeMap<String, Spanned<ManifestTarget>>,
}

#[derive(Debug, Default, Clone)]
pub struct ManifestPackage {
    pub name: Spanned<String>,
    pub edition: Option<Spanned<String>>,
}

/// `[export]`: what the C ABI exposes (spec §14.2, §15.3).
#[derive(Debug, Default, Clone)]
pub struct ManifestExport {
    /// C symbol prefix (default `onsa_`). What is exported is the `@export`
    /// of the items (§14.2, [`crate::ExportSettings::of`]).
    pub prefix: Option<Spanned<String>>,
}

/// `[targets.<name>]` (spec §15.3).
#[derive(Debug, Default, Clone)]
pub struct ManifestTarget {
    pub kind: Spanned<String>,
    /// Target triple, or `host`; required in the build of a target that
    /// gives C or native code (`table::Need`).
    pub platform: Option<Spanned<String>>,
    /// `kind = "source"`: the language (`c` in this version).
    pub lang: Option<Spanned<String>>,
    /// `strict` (default) or `strict-ftz` (§15.5).
    pub fp: Option<Spanned<String>>,
    /// Effects the target provides (`Alloc` decides the heap).
    pub provides: Vec<Spanned<String>>,
    /// `poison` / `trap` / `reset` / `halt` (spec §9.2).
    pub panic: Option<Spanned<String>>,
    pub panic_messages: Option<Spanned<bool>>,
    pub main_frame: Option<Spanned<String>>,
    pub memory: Option<Spanned<ManifestMemory>>,
    /// By module path.
    pub bind: BTreeMap<String, Spanned<String>>,
    /// The diagnostics of its build that need no source, which the other
    /// commands do not report: the E0200 of its values and its platform, and
    /// the E1104 of `platform` (§15.3, §18.1, S-154).
    pub build_diagnostics: Vec<Diagnostic>,
}

/// `[targets.<name>.memory]` (§12.4, §15.3): checked by every command, and
/// not used yet (W9-05, W9-06).
#[derive(Debug, Default, Clone)]
pub struct ManifestMemory {
    pub bulk: Option<Spanned<bool>>,
    /// Bytes, 0 or more.
    pub fast_budget: Option<Spanned<i64>>,
    pub bulk_budget: Option<Spanned<i64>>,
}

/// The manifest of an input as read: its values and the diagnostics of its
/// check (`Stage::Manifest`, §18.1), which stop every command before the
/// sources are read. `file` is the file its places are in: `onsa.toml`, or
/// for a test fragment its case file.
#[derive(Debug, Clone)]
pub struct ManifestRead {
    pub file: FileId,
    pub form: ManifestForm,
    /// Empty (no name) when the text is not TOML (E1101).
    pub manifest: Manifest,
    pub diagnostics: Vec<Diagnostic>,
}
