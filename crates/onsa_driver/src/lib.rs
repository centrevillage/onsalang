//! Pipeline driver: loads a package (S-11), embeds `std` (D-07), and runs
//! parse -> analyze. Each milestone adds a stage (`history/implementation-tasks.md` §4).
//!
//! Every public stage function runs in [`guard`]: a panic or another failure
//! of the compiler comes back as an [`InternalError`] (S-67), never as a
//! diagnostic, whatever the command. The diagnostics a command reports are
//! reduced in one place, [`reduce`] (S-59).

pub mod build;
mod consts;
mod file_commands;
pub mod graph;
mod input;
pub mod interface;
pub mod internal;
pub mod manifest;
mod platform;
pub mod reduce;
mod testing;
pub mod verify;

pub use build::{
    BuildError, BuildOptions, BuildOutput, BuildReport, ExportSettings, ResolvedTarget, TargetSettings, build,
    build_analyzed, build_resolved, resolve_target,
};
pub use file_commands::{AstDiff, Formatted, cst_dump, diff_ast, format_file, levels_dump, parse_only};
pub use graph::{GraphError, graph};
pub use input::{
    Loaded, ManifestForm, ManifestSource, PackageInput, SourceFile, load, module_path, read_input, read_package_input,
    read_sources, slash_path,
};
pub use interface::{Interface, interface, render_json, render_text};
pub use internal::{InternalError, Origin, guard, guard_on_stack};
pub use manifest::{Manifest, ManifestExport, ManifestMemory, ManifestPackage, ManifestRead, ManifestTarget, Spanned};
pub use platform::{Platform, host_triple, platform};
pub use testing::{TestFailure, TestOptions, TestOutcome, TestReport, TestRun, TestStatus, run_tests};
pub use verify::{CoreStage, LowerError, VerifyFailure, verify_core, verify_core_in_debug_only};

use std::sync::{Arc, Mutex, OnceLock};

use onsa_diag::timing::{Phase, phase};
use onsa_diag::{Diagnostic, FileId, SharedFiles, SourceMap, Span};
use onsa_sema::{Module, Package};

/// The embedded standard library: its package name, version and modules
/// (generated from `std/`, R-80 (4)).
pub use onsa_sema::{STD_PACKAGE, STD_VERSION, StdModule, std_modules};

/// Result of `onsa check`: diagnostics only (no artifacts).
#[derive(Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
}

/// The embedded std parsed once in the process (X-20 E (i)): its files are
/// the same [`SharedFiles`] in every check, so its parse, made with their
/// ids, is valid in each. With it, its analysis alone, which every check
/// continues (W5-18). The parse and that analysis are counted in the phases
/// of the check that makes them, the first of the process.
struct Std {
    files: SharedFiles,
    package: Arc<Package>,
    base: Mutex<onsa_sema::Base>,
}

// Shared by the threads of a process (the tests check on many).
const _: () = {
    const fn shared<T: Send + Sync>() {}
    shared::<Std>()
};

/// [`Std`], made by the first check of the process. A panic of the parse or
/// of the analysis leaves it unmade (`OnceLock`): the next check makes it again.
fn std_parsed() -> &'static Std {
    static STD: OnceLock<Std> = OnceLock::new();
    STD.get_or_init(|| {
        let files =
            SharedFiles::new(std_modules().iter().map(|m| (format!("{STD_PACKAGE}/{}", m.file), m.text.into())));
        let modules = files
            .files()
            .zip(std_modules())
            .map(|((file, f), m)| {
                let segments = m.segments.iter().map(|s| s.to_string()).collect();
                Module { segments, file, text: m.text.to_string(), parsed: parse_file(file, f.text()) }
            })
            .collect();
        let package = Arc::new(Package::std(modules));
        let base = Mutex::new(onsa_sema::Base::new(package.clone()));
        Std { files, package, base }
    })
}

/// The std of every check ([`std_parsed`]), its files attached to `sources`.
fn std_package(sources: &mut SourceMap) -> Arc<Package> {
    let std = std_parsed();
    sources.share(&std.files);
    std.package.clone()
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
    let _syntax = phase(Phase::Syntax);
    let _scope = onsa_diag::internal::item_scope(Span::new(file, 0, 0));
    onsa_syntax::parse(file, text)
}

/// Check a loaded package. `std` is attached to `sources`. With a file passed
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
    /// The flow each `[[plugin]]` names, in their order (S-718): what the
    /// build reads (none: it names none).
    pub plugin_flows: Vec<Option<onsa_sema::DefId>>,
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
/// attached to `sources`), with the diagnostics of its paths
/// ([`Loaded::input_diagnostics`]).
/// A package whose manifest has diagnostics is not analyzed: the command
/// stops on them first (§18.1), and one that did not is an internal error.
pub fn analyze_loaded(loaded: &mut Loaded) -> Result<Analyzed, InternalError> {
    let modules = loaded.modules.clone();
    let name = loaded.name.clone();
    let paths = guard(|| {
        if let Some(d) = loaded.manifest_diagnostics().first() {
            onsa_diag::internal::bug(Some(d.span), "the manifest has diagnostics, and they did not stop the command");
        }
        loaded.input_diagnostics()
    })?;
    let flows = loaded.manifest.iter().flat_map(|m| {
        let at = |f: &Spanned<String>| Span::new(m.file, f.span.start as u32, f.span.end as u32);
        m.manifest.plugin_flow_paths.iter().map(move |f| (f.value.clone(), at(f)))
    });
    analyze(&mut loaded.sources, &name, &modules, paths, &flows.collect::<Vec<_>>())
}

/// The package of the user's modules, parsed, on the std of the process.
fn user_package(sources: &mut SourceMap, name: &str, modules: &[(FileId, Vec<String>)]) -> Package {
    let user_modules: Vec<Module> = modules
        .iter()
        .map(|(file, path)| {
            let text = sources.file(*file).text().to_string();
            let parsed = parse_file(*file, &text);
            Module { segments: path.clone(), file: *file, text, parsed }
        })
        .collect();
    let std = std_package(sources);
    package_graph(name, user_modules, &std)
}

/// The analysis of a package. `paths`, the diagnostics of the input's paths
/// (with the module path each names), are outside every unit: each is
/// reported (§2.3). `flows` are the paths of the `[[plugin]]` (S-718).
fn analyze(
    sources: &mut SourceMap,
    name: &str,
    modules: &[(FileId, Vec<String>)],
    mut paths: Vec<(Diagnostic, Vec<String>)>,
    flows: &[manifest::plugin::PluginFlow],
) -> Result<Analyzed, InternalError> {
    guard(|| {
        let pkg = user_package(sources, name, modules);
        let analysis = onsa_sema::analyze_on(&pkg, &std_parsed().base);
        let _report = phase(Phase::Report);
        let mut all: Vec<Diagnostic> = pkg.modules.iter().flat_map(|m| m.parsed.diagnostics.iter().cloned()).collect();
        all.extend(analysis.diagnostics.iter().cloned());
        let files = pkg.modules.iter().map(|m| (m.file, &m.parsed.units));
        let reduce::Reduced { mut diagnostics, mut diagnostic_units, units } = reduce::per_unit(files, all);
        let plugin_flows = manifest::plugin::resolve(&analysis, flows);
        manifest::plugin::note_named(&analysis, &pkg, flows, &plugin_flows, &mut diagnostics, &mut paths);
        // The candidates of the E0320 the check reports alone (R-305).
        onsa_sema::rename_fixes(&pkg, &analysis, &mut diagnostics);
        let paths = paths.into_iter().map(|(d, _)| d).chain(analysis.path_diagnostics.iter().cloned());
        let paths: Vec<Diagnostic> = paths.collect();
        diagnostic_units.extend(paths.iter().map(|_| None));
        diagnostics.extend(paths);
        fill_found(sources, &mut diagnostics);
        debug_contract(sources, &diagnostics, None);
        Analyzed { pkg, analysis, diagnostics, diagnostic_units, units, plugin_flows }
    })
}

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
        let _lower = phase(Phase::Lower);
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
    let verify = phase(Phase::Verify);
    verify_core(&module, CoreStage::Lower)?;
    drop(verify);
    Ok(module)
}

/// In debug builds (the tests, the fuzzing), a diagnostic that breaks its
/// rules (a required fix or note missing, edits that overlap or cut a token,
/// plan D-04) is an internal error: the stage that made it is wrong (W3-02 D11).
/// Release builds report the diagnostic as it is. `toml` is the file
/// `onsa.toml`, which is not cut by the lexer of Onsa.
pub(crate) fn debug_contract(sources: &SourceMap, diagnostics: &[Diagnostic], toml: Option<FileId>) {
    if cfg!(debug_assertions) {
        let problems = onsa_syntax::diagnostic_contract(sources, diagnostics, toml);
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
mod base_tests;
#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn std_parses_and_analyzes_cleanly() {
        let mut sources = SourceMap::default();
        let std = std_package(&mut sources);
        for m in &std.modules {
            assert!(m.parsed.diagnostics.is_empty(), "std/{}: {:?}", m.path(), m.parsed.diagnostics);
        }
        let pkg = Package::new("empty", Vec::new(), vec![std]);
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
        let std = std_package(&mut sources);
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

    /// §14.2, S-639 (dp1): the build exports the `@export` of its own package
    /// only; a dependency's (`mid`, a form no case can write, §19.1) is
    /// checked the same and not exported. The order (A4, not in the spec) is
    /// of the paths of the modules (`a.c` before `b`, though `b` is read
    /// first), and in a module of the declarations (`zed` before `alpha`).
    #[test]
    fn the_exports_are_of_the_package_itself_in_the_order_of_the_modules() {
        let mut sources = SourceMap::default();
        let std = std_package(&mut sources);
        let mut module = |pkg: &str, path: &[&str], src: &str| {
            let file = sources.add(format!("{pkg}/{}.onsa", path.join("/")), src);
            let segments = path.iter().map(|s| s.to_string()).collect();
            Module { segments, file, text: src.into(), parsed: parse_file(file, src) }
        };
        let mid = module("mid", &["m"], "@export\npub fn half(x: F32) -> F32 {\n  x * 0.5\n}\n");
        let fns = "@export\npub fn zed() -> I32 {\n  1\n}\n\npub fn not_out() -> I32 {\n  2\n}\n\n\
                   @export\npub fn alpha() -> I32 {\n  3\n}\n";
        let b = module("user", &["b"], fns);
        let ac = module("user", &["a", "c"], "@export\npub fn mid() -> I32 {\n  4\n}\n");
        let mid = Arc::new(Package::new("mid", vec![mid], vec![std.clone()]));
        let analysis = onsa_sema::analyze(&Package::new("user", vec![b, ac], vec![std, mid]));
        assert!(analysis.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analysis.diagnostics));
        let names: Vec<String> = analysis.exports().into_iter().map(|d| analysis.qualified_name(d)).collect();
        assert_eq!(names, ["a.c.mid", "b.zed", "b.alpha"]);
        assert!(analysis.defs.iter().any(|d| d.name == "half" && d.export.is_some()));
    }

    /// X-20 E (i): once std is parsed in the process, a check parses the
    /// user's files only, and its package depends on the one std (the
    /// other tests may have parsed it first: the result is the same).
    #[test]
    fn the_std_is_parsed_once_in_the_process() {
        let std = std_parsed();
        let input = PackageInput::single_file("m.onsa", "fn f() -> I32 {\n  1\n}\n");
        let mut loaded = Loaded::from_input(input).expect("the input loads");
        let (analyzed, times) = onsa_diag::timing::record(|| analyze_loaded(&mut loaded).expect("no internal error"));
        let syntax = times.phases.iter().find(|p| p.0 == Phase::Syntax).map(|p| p.2);
        assert_eq!(syntax, Some(1), "{times:?}");
        assert!(Arc::ptr_eq(&analyzed.pkg.deps[0], &std.package));
    }

    /// The user's files keep their ids, from 0 in the order the input loads
    /// them and the manifest after them (`onsa_tests::fix_contract::apply_alone`
    /// reads the one file of a single-file input as `FileId(0)`), and std's
    /// modules have the ids of its shared files in every check.
    #[test]
    fn the_user_files_keep_their_ids() {
        let check = || {
            let text = "[package]\nname = \"p\"\nedition = \"2026\"\n".to_string();
            let manifest = ManifestSource { path: "onsa.toml".into(), text, form: ManifestForm::File };
            let file = |path: &str| SourceFile { path: path.into(), text: "pub fn f() -> I32 {\n  1\n}\n".into() };
            let input = PackageInput {
                manifest: Some(manifest),
                files: vec![file("a.onsa"), file("b.onsa")],
                ..Default::default()
            };
            let mut loaded = Loaded::from_input(input).expect("the input loads");
            let analyzed = analyze_loaded(&mut loaded).expect("no internal error");
            assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
            let user: Vec<FileId> = analyzed.pkg.modules.iter().map(|m| m.file).collect();
            assert_eq!((user, loaded.toml_file()), (vec![FileId(0), FileId(1)], Some(FileId(2))));
            let std: Vec<FileId> = analyzed.pkg.deps[0].modules.iter().map(|m| m.file).collect();
            for &f in &std {
                assert_eq!(loaded.sources.file(f).text(), package_text(&analyzed.pkg, f).unwrap());
            }
            std
        };
        let shared: Vec<FileId> = std_parsed().files.files().map(|(f, _)| f).collect();
        assert_eq!(check(), shared);
        assert_eq!(check(), shared);
    }

    #[test]
    fn module_paths() {
        assert_eq!(module_path(Path::new("dsp/voice.onsa")), ["dsp", "voice"]);
        assert_eq!(module_path(Path::new("util.onsa")), ["util"]);
        assert_eq!(module_path(Path::new("a.b.onsa")), ["a.b"]);
    }
}
