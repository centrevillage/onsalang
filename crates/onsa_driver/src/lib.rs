//! Pipeline driver: loads a package (S-11), embeds `std` (D-07), and runs
//! parse -> analyze. Each milestone adds a stage (`history/implementation-tasks.md` §4).
//!
//! Every public stage function runs in [`guard`]: a panic or another failure
//! of the compiler comes back as an [`InternalError`] (S-67), never as a
//! diagnostic, whatever the command. The diagnostics a command reports are
//! reduced in one place, [`reduce`] (S-59).

pub mod build;
pub mod graph;
mod input;
pub mod interface;
pub mod internal;
pub mod reduce;
mod testing;
pub mod verify;

pub use input::{
    Loaded, ManifestSource, PackageInput, SourceFile, load, module_path, read_input, read_package_input, read_sources,
    slash_path,
};
pub use internal::{InternalError, Origin, guard, guard_on_stack};
pub use testing::{TestFailure, TestOptions, TestOutcome, TestReport, TestRun, TestStatus, run_tests};

use std::collections::HashMap;
use std::sync::Arc;

use onsa_diag::{Diagnostic, FileId, SourceMap, Span};
use onsa_sema::{Module, Package};

/// The embedded standard library: its package name, version and modules
/// (generated from `std/`, R-80 (4)).
pub use onsa_sema::{STD_PACKAGE, STD_VERSION, StdModule, std_modules};

/// Result of `onsa check`: diagnostics only (no artifacts).
#[derive(Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
}

/// The manifest `onsa.toml` (spec §15.3). `[export]` and `[targets.*]` are
/// used by `onsa build` (T4-5); `bind` is read but not supported yet.
#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct Manifest {
    pub package: ManifestPackage,
    #[serde(default)]
    pub dependencies: HashMap<String, String>,
    #[serde(default)]
    pub export: Option<ManifestExport>,
    #[serde(default)]
    pub targets: HashMap<String, ManifestTarget>,
}

/// `[export]`: what the C ABI exposes (spec §14.2, §15.3).
#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct ManifestExport {
    /// C symbol prefix (default `onsa_`).
    pub prefix: Option<String>,
    /// Flows by module path (`dsp.voice`).
    #[serde(default)]
    pub flows: Vec<String>,
    /// Functions by module path (`util.onsa_version`).
    #[serde(default)]
    pub fns: Vec<String>,
}

/// `[targets.<name>]` (spec §15.3).
#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct ManifestTarget {
    pub kind: String,
    /// Target triple, or `host`.
    pub platform: String,
    /// `kind = "source"`: the language (`c` in this version).
    pub lang: Option<String>,
    /// `strict` (default) or `strict-ftz`.
    pub numeric: Option<String>,
    /// Effects the target provides (`Alloc` decides the heap).
    #[serde(default)]
    pub provides: Vec<String>,
    /// `poison` / `trap` / `reset` / `halt` (spec §9.2).
    pub panic: Option<String>,
    pub panic_messages: Option<bool>,
    pub main_frame: Option<String>,
    pub memory: Option<ManifestMemory>,
    #[serde(default)]
    pub bind: HashMap<String, String>,
}

#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct ManifestMemory {
    pub bulk_threshold: Option<u32>,
}

#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct ManifestPackage {
    pub name: String,
    #[serde(default)]
    pub edition: String,
}

impl Manifest {
    /// The top-level tables of the manifest: the fields of [`Manifest`], in
    /// one place (W4-02 closes the table on the same list).
    pub const TOP_LEVEL_KEYS: &'static [&'static str] = &["package", "dependencies", "export", "targets"];

    /// Read a manifest from its text: the one reader of `onsa.toml` (S-99,
    /// R-80 (5)). The errors keep the line, the column and the excerpt. The
    /// top-level tables named in `extra_tables` are returned as they are
    /// beside the manifest (the test fragments pass `["test"]`; `onsa.toml`
    /// passes none, so a `[test]` there is read like any other key the
    /// manifest does not know).
    pub fn parse(text: &str, extra_tables: &[&str]) -> Result<(Manifest, toml::Table), String> {
        let manifest: Manifest = toml::from_str(text).map_err(|e| e.to_string())?;
        let mut extra = toml::Table::new();
        if !extra_tables.is_empty() {
            let mut table: toml::Table = toml::from_str(text).map_err(|e| e.to_string())?;
            for name in extra_tables {
                if let Some(v) = table.remove(*name) {
                    extra.insert((*name).to_string(), v);
                }
            }
        }
        Ok((manifest, extra))
    }
}

fn std_package(sources: &mut SourceMap) -> Package {
    let modules = std_modules()
        .iter()
        .map(|m| {
            let file = sources.add(format!("{STD_PACKAGE}/{}", m.file), m.text);
            let segments = m.segments.iter().map(|s| s.to_string()).collect();
            Module { segments, file, text: m.text.to_string(), parsed: parse_file(file, m.text) }
        })
        .collect();
    Package::std(modules)
}

/// The dependency graph of a package, made once (R-88 (1), design 3.3): the
/// user's package with the embedded std as its implicit dependency (§15.3).
/// The std is one shared value however many packages depend on it.
/// `[dependencies]` is not read here (the pin of std and the other
/// dependencies are the manifest check's, W4-02). The caller makes `std`
/// once and passes it to every package of the graph, so that `flatten`
/// lists it once (it compares the `Arc`s).
fn package_graph(name: &str, modules: Vec<Module>, std: &Arc<Package>) -> Package {
    Package::new(name, modules, vec![std.clone()])
}

/// Parse one file; a panic names the file (S-67).
fn parse_file(file: FileId, text: &str) -> onsa_syntax::Parsed {
    let _scope = onsa_diag::internal::item_scope(Span::new(file, 0, 0));
    onsa_syntax::parse(file, text)
}

/// Parse only (the `mode = "parse"` depth of the test cases, D-05).
pub fn parse_only(sources: &SourceMap) -> Result<CheckResult, InternalError> {
    guard(|| {
        let mut result = CheckResult::default();
        for (id, file) in sources.files() {
            let parsed = parse_file(id, file.text());
            let diagnostics = parsed.diagnostics.clone();
            result.diagnostics.extend(reduce::per_unit([(id, &parsed.units)], diagnostics).diagnostics);
        }
        result
    })
}

/// The canonical text of a file (`onsa fmt`), or its syntax diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formatted {
    Text(String),
    /// The file has syntax diagnostics: it is not formatted (spec §18.2).
    Syntax(Vec<Diagnostic>),
}

/// Format the file `file` of `sources` (`onsa fmt`).
pub fn format_file(sources: &SourceMap, file: FileId) -> Result<Formatted, InternalError> {
    guard(|| {
        let text = sources.file(file).text();
        let parsed = parse_file(file, text);
        // A panic names the file (S-67).
        let _scope = onsa_diag::internal::item_scope(Span::new(file, 0, 0));
        formatted(&parsed, file, onsa_syntax::format(&parsed, text))
    })?
}

/// What `onsa fmt` makes of the formatter's result: an output that is not
/// the program of the input is an internal error at the first difference,
/// without a diagnostic code (`spec/tools.md` §3.5).
fn formatted(
    parsed: &onsa_syntax::Parsed,
    file: FileId,
    result: Result<String, onsa_syntax::fmt::FormatError>,
) -> Result<Formatted, InternalError> {
    use onsa_syntax::fmt::FormatError;
    match result {
        Ok(out) => Ok(Formatted::Text(out)),
        Err(FormatError::Syntax) => Ok(Formatted::Syntax(reduce::syntax_report(parsed, file))),
        Err(FormatError::Unverified(d)) => Err(InternalError::unverified(&d)),
    }
}

/// The CST of a file (`onsa dump --cst`, R-86): the text of its leaves
/// (the source, byte for byte) or, with `tree`, the tree as indented lines.
/// A file with syntax diagnostics has a CST too; they are not reported here.
/// The tree is checked (`Cst::validate`) by the parse itself: a broken tree is
/// an internal error.
pub fn cst_dump(sources: &SourceMap, file: FileId, tree: bool) -> Result<String, InternalError> {
    guard(|| {
        let text = sources.file(file).text();
        let parsed = parse_file(file, text);
        if tree { parsed.cst.tree(text) } else { parsed.cst.text(text) }
    })
}

/// The levels (spec §2.5) of each top-level item of a file that parsed, one
/// line each, in the order of the file (`onsa dump --levels`, for the fmt
/// properties: `tools/fmt_props.py`).
pub fn levels_dump(sources: &SourceMap, file: FileId) -> Result<String, InternalError> {
    guard(|| {
        let parsed = parse_file(file, sources.file(file).text());
        parsed.levels.iter().map(|l| format!("{l}\n")).collect()
    })
}

/// The structural difference of two files (`onsa diff --ast`).
#[derive(Debug, Clone)]
pub enum AstDiff {
    Items(Vec<onsa_syntax::diff::ItemDiff>),
    /// A file has syntax diagnostics: the files are not compared (spec §18.2).
    /// The diagnostics of both files (`reduce::syntax_report`).
    Syntax(Vec<Diagnostic>),
}

/// Compare the files `old` and `new` of `sources` (`onsa diff --ast`).
pub fn diff_ast(sources: &SourceMap, old: FileId, new: FileId) -> Result<AstDiff, InternalError> {
    guard(|| {
        let files = [old, new];
        let parsed: Vec<onsa_syntax::Parsed> =
            files.iter().map(|&file| parse_file(file, sources.file(file).text())).collect();
        if parsed.iter().any(|p| p.syntax_errors()) {
            // Both files are reported, not only the first with an error (`spec/tools.md` §3.1).
            // A file on both sides is reported once.
            let n = if old == new { 1 } else { 2 };
            return AstDiff::Syntax(
                parsed.iter().zip(files).take(n).flat_map(|(p, file)| reduce::syntax_report(p, file)).collect(),
            );
        }
        AstDiff::Items(onsa_syntax::diff::diff(&parsed[0], &parsed[1]))
    })
}

/// Check a loaded package. `std` is appended to `sources`. With a file passed
/// inside the package (`focus`), the whole package is checked and only the
/// diagnostics of that file are kept (§15.1: `check` and the LSP; S-159).
pub fn check_loaded(loaded: &mut Loaded) -> Result<CheckResult, InternalError> {
    let mut result = CheckResult { diagnostics: analyze_loaded(loaded)?.diagnostics };
    // SPEC-GAP(S-636): the outcome is that of the kept diagnostics: none in
    // the passed file is exit 0, whatever the other files have.
    if let Some(focus) = loaded.focus {
        result.diagnostics.retain(|d| d.span.file == focus);
    }
    Ok(result)
}

/// A checked package with its analysis, for the stages after `check`
/// (Core lowering, interpretation, backends).
pub struct Analyzed {
    pub pkg: Package,
    pub analysis: onsa_sema::Analysis,
    /// One diagnostic for each unit (spec §18.1, [`reduce::per_unit`]).
    pub diagnostics: Vec<Diagnostic>,
    /// For each of `diagnostics`, its unit in `units`.
    pub diagnostic_units: Vec<Option<usize>>,
    /// The units of the package's files (`onsa_syntax::units`), in one table.
    pub units: Vec<reduce::Unit>,
}

impl Analyzed {
    /// The units (of `units`) whose check depends on what the check did not
    /// read ([`onsa_sema::Analysis::unread_users`]): fixing the cause can
    /// show an error they held back. Computed when asked (the tests of the
    /// fix candidates ask; no command does).
    pub fn unread_units(&self) -> std::collections::BTreeSet<usize> {
        let files: Vec<FileId> = self.pkg.modules.iter().map(|m| m.file).collect();
        let spans = self.analysis.unread_users(&files);
        reduce::units_of(self.pkg.modules.iter().map(|m| (m.file, &m.parsed.units)), &spans)
    }
}

/// Parse and analyze a loaded package, keeping the analysis (`std` is
/// appended to `sources`), with the diagnostics of its paths
/// ([`Loaded::input_diagnostics`]).
pub fn analyze_loaded(loaded: &mut Loaded) -> Result<Analyzed, InternalError> {
    let modules = loaded.modules.clone();
    let name = loaded.name.clone();
    let paths = guard(|| loaded.input_diagnostics())?;
    analyze(&mut loaded.sources, &name, &modules, paths)
}

/// The analysis of a package. `paths`, the diagnostics of the input's paths,
/// are outside every unit: each is reported (§2.3).
fn analyze(
    sources: &mut SourceMap,
    name: &str,
    modules: &[(FileId, Vec<String>)],
    paths: Vec<Diagnostic>,
) -> Result<Analyzed, InternalError> {
    guard(|| {
        let user_modules: Vec<Module> = modules
            .iter()
            .map(|(file, path)| {
                let text = sources.file(*file).text().to_string();
                let parsed = parse_file(*file, &text);
                Module { segments: path.clone(), file: *file, text, parsed }
            })
            .collect();
        let std = Arc::new(std_package(sources));
        let pkg = package_graph(name, user_modules, &std);
        let analysis = onsa_sema::analyze(&pkg);
        let mut all: Vec<Diagnostic> = pkg.modules.iter().flat_map(|m| m.parsed.diagnostics.iter().cloned()).collect();
        onsa_sema::rename_fixes(&pkg, &analysis, &mut all);
        all.extend(analysis.diagnostics.iter().cloned());
        let files = pkg.modules.iter().map(|m| (m.file, &m.parsed.units));
        let reduce::Reduced { mut diagnostics, mut diagnostic_units, units } = reduce::per_unit(files, all);
        let paths: Vec<Diagnostic> = paths.into_iter().chain(analysis.path_diagnostics.iter().cloned()).collect();
        diagnostic_units.extend(paths.iter().map(|_| None));
        diagnostics.extend(paths);
        fill_found(sources, &mut diagnostics);
        debug_contract(sources, &diagnostics);
        Analyzed { pkg, analysis, diagnostics, diagnostic_units, units }
    })
}

pub use graph::{GraphError, graph};
pub use interface::{Interface, interface, render_json, render_text};

pub use verify::{CoreStage, LowerError, VerifyFailure, verify_core, verify_core_in_debug_only};

/// Lower a checked package to Core (T3-3). Only meaningful when
/// `Analyzed::diagnostics` is empty; lowering diagnostics (E0200 for
/// features outside the core, every one once, S-67) come back as the
/// error, and so does an internal error (a Core the verifier rejects, R-82).
pub fn lower_core(analyzed: &Analyzed) -> Result<onsa_core::Module, LowerError> {
    lower_core_with(analyzed, &onsa_core::LowerOptions::default())
}

/// [`lower_core`] with the target's memory settings (T4-5): the lowering
/// stage, verified at its boundary.
pub fn lower_core_with(analyzed: &Analyzed, opts: &onsa_core::LowerOptions) -> Result<onsa_core::Module, LowerError> {
    let lowered = guard(|| {
        let mut r = onsa_core::lower_with(&analyzed.pkg, &analyzed.analysis, opts);
        // Every diagnostic names the offending source (§18.1).
        if let Err(onsa_core::LowerFailure::Unsupported(d)) = &mut r {
            fill_found_with(d, |file| package_text(&analyzed.pkg, file));
        }
        r
    })?;
    let module = match lowered {
        Ok(m) => m,
        Err(onsa_core::LowerFailure::Unsupported(d)) => return Err(LowerError::reported(d)),
        Err(onsa_core::LowerFailure::Internal { span, message }) => {
            return Err(LowerError::Internal(InternalError::lowering(span, message)));
        }
    };
    verify_core(&module, CoreStage::Lower)?;
    Ok(module)
}

pub use build::{
    BuildError, BuildOptions, BuildOutput, BuildReport, ExportSettings, Platform, ResolvedTarget, TargetSettings,
    build, build_analyzed, build_resolved, host_triple, platform, resolve_target,
};

/// In debug builds (the tests, the fuzzing), a diagnostic that breaks its
/// rules (a required fix or note missing, edits that overlap or cut a token,
/// plan D-04) is an internal error: the stage that made it is wrong (W3-02 D11).
/// Release builds report the diagnostic as it is.
pub(crate) fn debug_contract(sources: &SourceMap, diagnostics: &[Diagnostic]) {
    if cfg!(debug_assertions) {
        let problems = onsa_syntax::diagnostic_contract(sources, diagnostics);
        if !problems.is_empty() {
            onsa_diag::internal::bug(
                diagnostics.first().map(|d| d.span),
                format!("a diagnostic breaks the rules of diagnostics: {}", problems.join("; ")),
            );
        }
    }
}

/// Every diagnostic names the offending source (`found`, §18.1): when the
/// emitter left it out, take the text of the span.
pub(crate) fn fill_found(sources: &SourceMap, diagnostics: &mut [Diagnostic]) {
    fill_found_with(diagnostics, |file| Some(sources.file(file).text()));
}

/// [`fill_found`] with the text of each file from `text_of` (lowering has
/// the package, not the source map). A file `text_of` does not know is an
/// internal error: every span lowering reports is in the package.
fn fill_found_with<'t>(diagnostics: &mut [Diagnostic], text_of: impl Fn(FileId) -> Option<&'t str>) {
    for d in diagnostics {
        // A panic names the file of the diagnostic (S-67).
        let _scope = onsa_diag::internal::item_scope(Span::new(d.span.file, 0, 0));
        if d.found.as_deref().is_none_or(str::is_empty) {
            let Some(file) = text_of(d.span.file) else {
                onsa_diag::internal::bug(Some(d.span), "a diagnostic in a file the package does not hold");
            };
            // The blanks are the space and the tab (§2.5, S-441): a range of
            // other characters (NBSP, a line separator, a CR alone) has its
            // `found`.
            let text = file[d.span.start as usize..d.span.end as usize]
                .trim_matches(|c| onsa_syntax::lexer::is_blank(c) || c == '\n');
            if !text.is_empty() {
                d.found = Some(text.to_string());
            }
        }
    }
}

/// The text of `file` among the modules of `pkg` and its dependencies.
fn package_text(pkg: &Package, file: FileId) -> Option<&str> {
    onsa_sema::flatten(pkg).into_iter().flat_map(|p| &p.modules).find(|m| m.file == file).map(|m| m.text.as_str())
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    /// R-204: an output of fmt that is not the program of its input is an
    /// internal error (101) that names the first difference and its place in
    /// the input, without a diagnostic code (`spec/tools.md` §3.5). A
    /// correct fmt does not make one, so the output is a false one.
    #[test]
    fn an_unverified_output_is_an_internal_error_at_the_place_in_the_input() {
        let mut sources = SourceMap::default();
        let file = sources.add("m.onsa", "fn f() -> I32 {\n  let a = 1\n  a // keep\n}\n");
        let text = sources.file(file).text();
        let parsed = onsa_syntax::parse(file, text);
        let fake = "fn f() -> I32 {\n  let a = 1\n  a\n}\n";
        let result = onsa_syntax::fmt::verify(&parsed, text, fake).map(|()| fake.to_string());
        let e = formatted(&parsed, file, result).unwrap_err();
        assert_eq!(e.origin, internal::Origin::Unverified);
        let shown = e.render(&sources);
        assert!(shown.starts_with("internal error: the output of fmt is not the same program: comment 1"), "{shown}");
        assert!(shown.contains("  --> m.onsa:3:5\n"), "{shown}");
        assert!(!shown.contains("error["), "{shown}");
        // The real formatter gives the text.
        assert_eq!(format_file(&sources, file), Ok(Formatted::Text(text.to_string())));
    }

    #[test]
    fn std_parses_and_analyzes_cleanly() {
        let mut sources = SourceMap::default();
        let std = std_package(&mut sources);
        for m in &std.modules {
            assert!(m.parsed.diagnostics.is_empty(), "std/{}: {:?}", m.path(), m.parsed.diagnostics);
        }
        let pkg = Package::new("empty", Vec::new(), vec![Arc::new(std)]);
        let analysis = onsa_sema::analyze(&pkg);
        assert!(analysis.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analysis.diagnostics));
    }

    /// R-80 (4), D-15: the std table that `onsa_sema/build.rs` generates is
    /// the package that the driver's own reading of `std/` gives (§15.1): the
    /// same files, in the same order, with the same module paths and texts.
    #[test]
    fn the_generated_std_table_is_the_package_read_from_the_std_directory() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
        let read = read_sources(&root).expect("std/ reads");
        assert!(!read.is_empty());
        let from_dir: Vec<(Vec<String>, String, String)> =
            read.iter().map(|f| (module_path(Path::new(&f.path)), f.path.clone(), f.text.clone())).collect();
        let table: Vec<(Vec<String>, String, String)> = std_modules()
            .iter()
            .map(|m| (m.segments.iter().map(|s| s.to_string()).collect(), m.file.to_string(), m.text.to_string()))
            .collect();
        assert_eq!(table, from_dir);
    }

    /// R-88 (1): a package that two packages of the graph depend on is one
    /// value, analyzed once. Here std is a dependency of the user's package
    /// and of `mid`, which the user's package depends on too: this version
    /// takes no dependency other than std (§19.1), so no case can write this.
    #[test]
    fn a_package_shared_in_the_graph_is_analyzed_once() {
        let mut sources = SourceMap::default();
        let std = Arc::new(std_package(&mut sources));
        let std_modules_count = std.modules.len();
        let src = "use std.math.{sqrt}\n\npub fn half(x: F32) -> F32 {\n  sqrt(x) * 0.5\n}\n";
        let file = sources.add("mid/m.onsa", src);
        let module = Module { segments: vec!["m".into()], file, text: src.to_string(), parsed: parse_file(file, src) };
        let mid = Arc::new(Package::new("mid", vec![module], vec![std.clone()]));
        let pkg = Package::new("user", Vec::new(), vec![std, mid]);
        let flat = onsa_sema::flatten(&pkg);
        assert_eq!(flat.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), [STD_PACKAGE, "mid", "user"]);
        let analysis = onsa_sema::analyze(&pkg);
        assert!(analysis.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analysis.diagnostics));
        assert_eq!(analysis.modules.names, [STD_PACKAGE, "mid", "user"]);
        let std_files = analysis.modules.mods.iter().filter(|m| m.pkg == 0 && m.file.is_some()).count();
        assert_eq!(std_files, std_modules_count);
        let sqrt = analysis.defs.iter().filter(|d| d.name == "sqrt" && analysis.modules.pkg_of(d.module) == 0).count();
        assert_eq!(sqrt, 1);
    }

    /// A deserializer that only records the fields a struct asks for.
    struct FieldsOf<'a>(&'a mut Vec<&'static str>);

    impl<'de> serde::Deserializer<'de> for FieldsOf<'_> {
        type Error = serde::de::value::Error;

        fn deserialize_any<V: serde::de::Visitor<'de>>(self, _: V) -> Result<V::Value, Self::Error> {
            Err(serde::de::Error::custom("not a struct"))
        }

        fn deserialize_struct<V: serde::de::Visitor<'de>>(
            self,
            _: &'static str,
            fields: &'static [&'static str],
            _: V,
        ) -> Result<V::Value, Self::Error> {
            self.0.extend_from_slice(fields);
            Err(serde::de::Error::custom("fields recorded"))
        }

        serde::forward_to_deserialize_any! {
            bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf
            option unit unit_struct newtype_struct seq tuple tuple_struct map enum identifier ignored_any
        }
    }

    #[test]
    fn top_level_keys_are_the_manifest_fields() {
        let mut fields = Vec::new();
        let _ = <Manifest as serde::Deserialize>::deserialize(FieldsOf(&mut fields));
        fields.sort_unstable();
        let mut keys = Manifest::TOP_LEVEL_KEYS.to_vec();
        keys.sort_unstable();
        assert_eq!(fields, keys);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path(Path::new("dsp/voice.onsa")), ["dsp", "voice"]);
        assert_eq!(module_path(Path::new("util.onsa")), ["util"]);
        assert_eq!(module_path(Path::new("a.b.onsa")), ["a.b"]);
    }
}
