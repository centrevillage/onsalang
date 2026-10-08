//! Pipeline driver: loads a package (S-11), embeds `std` (D-07), and runs
//! parse -> analyze. Each milestone adds a stage (`docs/implementation-tasks.md` §4).
//!
//! Every public stage function runs in [`guard`]: a panic or another failure
//! of the compiler comes back as an [`InternalError`] (S-67), never as a
//! diagnostic, whatever the command. The diagnostics a command reports are
//! reduced in one place, [`reduce`] (S-59).

pub mod build;
pub mod graph;
pub mod interface;
pub mod internal;
pub mod reduce;
pub mod verify;

pub use internal::{InternalError, Origin, guard, guard_on_stack};

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use onsa_diag::{Diagnostic, FileId, SourceMap, Span};
use onsa_sema::{Module, Package};

/// The standard library, embedded so that `wasm32` builds need no file I/O.
const STD: &[(&str, &str)] = &[
    ("math", include_str!("../../../std/math.onsa")),
    ("dsp", include_str!("../../../std/dsp.onsa")),
    ("dsp.test", include_str!("../../../std/dsp/test.onsa")),
    ("array", include_str!("../../../std/array.onsa")),
    ("test", include_str!("../../../std/test.onsa")),
    ("test.gen", include_str!("../../../std/test/gen.onsa")),
];

/// The name of the embedded standard library's package.
pub const STD_PACKAGE: &str = "std";

/// The embedded std modules: (module path under `std`, source text).
pub fn std_modules() -> &'static [(&'static str, &'static str)] {
    STD
}

/// Result of `onsa check`: diagnostics only (no artifacts).
#[derive(Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
}

/// Files of one package, loaded into a `SourceMap` with their module paths.
#[derive(Debug)]
pub struct Loaded {
    pub sources: SourceMap,
    pub name: String,
    pub root: Option<PathBuf>,
    pub modules: Vec<(FileId, String)>,
    /// The manifest; `None` for a single file without `onsa.toml` (spec §15.1).
    pub manifest: Option<Manifest>,
}

/// One source file of a package input: its path (relative to the package
/// root with a manifest; as given without one) and its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFile {
    pub path: String,
    pub text: String,
}

/// What a build reads, without the file system (R-80 (5), plan D-05): the
/// manifest value and the list of sources. `onsa_driver::read_input` makes
/// one from files; the tests and `onsa_web` make one from their own data.
#[derive(Debug, Clone, Default)]
pub struct PackageInput {
    /// `None`: no `onsa.toml`; every file is a module named after its stem
    /// (one file is a one-module package, spec §15.1).
    pub manifest: Option<Manifest>,
    pub files: Vec<SourceFile>,
    /// The package root on disk, when there is one (the default output directory of `build`).
    pub root: Option<PathBuf>,
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

/// Module path of a file relative to the package root: `dsp/voice.onsa` -> `dsp.voice`.
pub fn module_path(rel: &Path) -> String {
    let no_ext = rel.with_extension("");
    no_ext.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join(".")
}

/// Load a package from `paths` (S-11): one `onsa.toml` or a directory is a
/// package; otherwise every `.onsa` file is a module named after its stem
/// (one file is a one-module package).
pub fn load(paths: &[PathBuf]) -> Result<Loaded, String> {
    Ok(Loaded::from_input(read_input(paths)?))
}

impl Loaded {
    /// The sources of `input` in a `SourceMap` with their module paths. Reads
    /// no file: this is where the CLI, the tests and `onsa_web` meet.
    pub fn from_input(input: PackageInput) -> Loaded {
        let mut loaded = Loaded {
            sources: SourceMap::default(),
            name: String::new(),
            root: input.root,
            modules: Vec::new(),
            manifest: None,
        };
        if let Some(m) = &input.manifest {
            loaded.name = m.package.name.clone();
        }
        for f in input.files {
            let module = if input.manifest.is_some() {
                module_path(Path::new(&f.path))
            } else {
                Path::new(&f.path).file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
            };
            if loaded.name.is_empty() {
                loaded.name = module.clone();
            }
            let id = loaded.sources.add(f.path, f.text);
            loaded.modules.push((id, module));
        }
        loaded.manifest = input.manifest;
        loaded
    }
}

/// Read the package input at `paths` from the file system (S-11): one
/// `onsa.toml` or a directory is a package; otherwise the files themselves.
pub fn read_input(paths: &[PathBuf]) -> Result<PackageInput, String> {
    if paths.len() == 1 {
        let p = &paths[0];
        let manifest = if p.is_dir() {
            let m = p.join("onsa.toml");
            m.exists().then_some(m)
        } else if p.file_name().is_some_and(|n| n == "onsa.toml") {
            Some(p.clone())
        } else {
            None
        };
        if let Some(manifest) = manifest {
            let (m, root) = read_manifest(&manifest)?;
            let files = read_sources(&root)?;
            return Ok(PackageInput { manifest: Some(m), files, root: Some(root) });
        }
        if p.is_dir() {
            return Err(format!("{} has no onsa.toml", p.display()));
        }
    }
    let mut input = PackageInput::default();
    for p in paths {
        let text = std::fs::read_to_string(p).map_err(|e| format!("cannot read {}: {e}", p.display()))?;
        input.files.push(SourceFile { path: p.to_string_lossy().into_owned(), text });
    }
    Ok(input)
}

/// Read `onsa.toml`: the manifest and the package root (its directory).
pub fn read_manifest(manifest: &Path) -> Result<(Manifest, PathBuf), String> {
    let text = std::fs::read_to_string(manifest).map_err(|e| format!("cannot read {}: {e}", manifest.display()))?;
    let (m, _) = Manifest::parse(&text, &[]).map_err(|e| format!("{}: {e}", manifest.display()))?;
    Ok((m, manifest.parent().unwrap_or(Path::new(".")).to_path_buf()))
}

/// The `.onsa` files of the package at `root` (spec §15.1: recursively,
/// except the root's `tests/` and `target/`), sorted, with paths relative to it.
pub fn read_sources(root: &Path) -> Result<Vec<SourceFile>, String> {
    let mut files = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        let entries = std::fs::read_dir(&d).map_err(|e| format!("cannot read {}: {e}", d.display()))?;
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().into_owned();
            if p.is_dir() {
                if d == root && (name == "tests" || name == "target") {
                    continue;
                }
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                files.push(p);
            }
        }
    }
    files.sort();
    let mut out = Vec::new();
    for p in files {
        let text = std::fs::read_to_string(&p).map_err(|e| format!("cannot read {}: {e}", p.display()))?;
        let rel = p.strip_prefix(root).unwrap_or(&p).to_path_buf();
        out.push(SourceFile { path: rel.to_string_lossy().into_owned(), text });
    }
    Ok(out)
}

fn std_package(sources: &mut SourceMap) -> Package {
    let modules = STD
        .iter()
        .map(|(path, text)| {
            let file = sources.add(format!("std/{}.onsa", path.replace('.', "/")), *text);
            Module { path: path.to_string(), file, text: text.to_string(), parsed: parse_file(file, text) }
        })
        .collect();
    Package { name: STD_PACKAGE.into(), modules, deps: Vec::new(), is_std: true }
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
            result.diagnostics.extend(parse_file(id, file.text()).diagnostics);
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
        match onsa_syntax::format(&parsed, text) {
            Some(out) => Formatted::Text(out),
            None => Formatted::Syntax(parsed.syntax_report()),
        }
    })
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
    /// The diagnostics of both files (`Parsed::syntax_report`).
    Syntax(Vec<Diagnostic>),
}

/// Compare the files `old` and `new` of `sources` (`onsa diff --ast`).
pub fn diff_ast(sources: &SourceMap, old: FileId, new: FileId) -> Result<AstDiff, InternalError> {
    guard(|| {
        let parsed: Vec<onsa_syntax::Parsed> =
            [old, new].iter().map(|&file| parse_file(file, sources.file(file).text())).collect();
        if parsed.iter().any(|p| p.syntax_errors()) {
            // Both files are reported, not only the first with an error (`docs/onsa-tools.md` §3.1).
            return AstDiff::Syntax(
                parsed.iter().filter(|p| p.syntax_errors()).flat_map(|p| p.syntax_report()).collect(),
            );
        }
        AstDiff::Items(onsa_syntax::diff::diff(&parsed[0], &parsed[1]))
    })
}

/// Check the files already in `sources` as one package whose modules are
/// named after the file stems. `std` is appended to `sources`.
pub fn check(sources: &mut SourceMap) -> Result<CheckResult, InternalError> {
    let modules: Vec<(FileId, String)> = sources
        .files()
        .map(|(id, f)| {
            let stem = Path::new(f.name()).file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
            (id, stem)
        })
        .collect();
    let name = modules.first().map(|(_, s)| s.clone()).unwrap_or_default();
    check_package(sources, &name, &modules)
}

/// Check a loaded package. `std` is appended to `sources`.
pub fn check_loaded(loaded: &mut Loaded) -> Result<CheckResult, InternalError> {
    let modules = loaded.modules.clone();
    let name = loaded.name.clone();
    check_package(&mut loaded.sources, &name, &modules)
}

/// A checked package with its analysis, for the stages after `check`
/// (Core lowering, interpretation, backends).
pub struct Analyzed {
    pub pkg: Package,
    pub analysis: onsa_sema::Analysis,
    pub diagnostics: Vec<Diagnostic>,
}

/// Parse and analyze a loaded package, keeping the analysis (`std` is
/// appended to `sources`).
pub fn analyze_loaded(loaded: &mut Loaded) -> Result<Analyzed, InternalError> {
    let modules = loaded.modules.clone();
    let name = loaded.name.clone();
    analyze_package(&mut loaded.sources, &name, &modules)
}

pub fn analyze_package(
    sources: &mut SourceMap,
    name: &str,
    modules: &[(FileId, String)],
) -> Result<Analyzed, InternalError> {
    guard(|| {
        let user_modules: Vec<Module> = modules
            .iter()
            .map(|(file, path)| {
                let text = sources.file(*file).text().to_string();
                let parsed = parse_file(*file, &text);
                Module { path: path.clone(), file: *file, text, parsed }
            })
            .collect();
        let std = std_package(sources);
        let pkg = Package { name: name.to_string(), modules: user_modules, deps: vec![std], is_std: false };
        let analysis = onsa_sema::analyze(&pkg);
        let mut diagnostics = reduce::per_unit(&pkg, analysis.diagnostics.clone());
        fill_found(sources, &mut diagnostics);
        debug_contract(sources, &diagnostics);
        Analyzed { pkg, analysis, diagnostics }
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

/// `check` is the analysis without keeping it (one path for `check`,
/// `test` and the builds, D-15).
pub fn check_package(
    sources: &mut SourceMap,
    name: &str,
    modules: &[(FileId, String)],
) -> Result<CheckResult, InternalError> {
    Ok(CheckResult { diagnostics: analyze_package(sources, name, modules)?.diagnostics })
}

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
fn fill_found(sources: &SourceMap, diagnostics: &mut [Diagnostic]) {
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
            let text = &file[d.span.start as usize..d.span.end as usize];
            if !text.trim().is_empty() {
                d.found = Some(text.trim().to_string());
            }
        }
    }
}

/// The text of `file` among the modules of `pkg` and its dependencies.
fn package_text(pkg: &Package, file: FileId) -> Option<&str> {
    pkg.modules
        .iter()
        .find(|m| m.file == file)
        .map(|m| m.text.as_str())
        .or_else(|| pkg.deps.iter().find_map(|d| package_text(d, file)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn std_parses_and_analyzes_cleanly() {
        let mut sources = SourceMap::default();
        let std = std_package(&mut sources);
        for m in &std.modules {
            assert!(m.parsed.diagnostics.is_empty(), "std/{}: {:?}", m.path, m.parsed.diagnostics);
        }
        let pkg = Package { name: "empty".into(), modules: Vec::new(), deps: vec![std], is_std: false };
        let analysis = onsa_sema::analyze(&pkg);
        assert!(analysis.diagnostics.is_empty(), "{}", onsa_diag::to_text(&sources, &analysis.diagnostics));
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
        assert_eq!(module_path(Path::new("dsp/voice.onsa")), "dsp.voice");
        assert_eq!(module_path(Path::new("util.onsa")), "util");
    }
}

// ---------------------------------------------------------------- tests (T3-8)

/// Options of `onsa test`.
#[derive(Debug, Default, Clone)]
pub struct TestOptions {
    /// Run only tests whose name contains this substring.
    pub filter: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestStatus {
    Ok,
    Failed,
}

/// Outcome of one `test` block.
#[derive(Debug, Clone)]
pub struct TestOutcome {
    pub name: String,
    pub status: TestStatus,
    /// For failures: the message in the S-16 form (`assert <src>` or the panic text).
    pub message: Option<String>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Default)]
pub struct TestReport {
    pub tests: Vec<TestOutcome>,
}

impl TestReport {
    pub fn failed(&self) -> usize {
        self.tests.iter().filter(|t| t.status == TestStatus::Failed).count()
    }

    pub fn passed(&self) -> usize {
        self.tests.len() - self.failed()
    }

    /// Text report: one line per test and a summary (spec §11.8, S-16).
    pub fn render_text(&self, sources: &SourceMap) -> String {
        let mut out = String::new();
        for t in &self.tests {
            match t.status {
                TestStatus::Ok => out.push_str(&format!("test \"{}\" ok\n", t.name)),
                TestStatus::Failed => {
                    let at = t.span.map(|s| {
                        format!("{}:{}", sources.file(s.file).name(), sources.file(s.file).line_col(s.start).line)
                    });
                    out.push_str(&format!(
                        "test \"{}\" failed at {}: {}\n",
                        t.name,
                        at.unwrap_or_else(|| "?".into()),
                        t.message.as_deref().unwrap_or("")
                    ));
                }
            }
        }
        out.push_str(&format!("{} passed, {} failed\n", self.passed(), self.failed()));
        out
    }

    /// `[{ "name", "status": "ok" | "failed", "message"?, "span"? }]`.
    pub fn render_json(&self, sources: &SourceMap) -> String {
        let items: Vec<serde_json::Value> = self
            .tests
            .iter()
            .map(|t| {
                let mut o = serde_json::Map::new();
                o.insert("name".into(), t.name.clone().into());
                o.insert("status".into(), (if t.status == TestStatus::Ok { "ok" } else { "failed" }).into());
                if let Some(m) = &t.message {
                    o.insert("message".into(), m.clone().into());
                }
                if let Some(s) = t.span {
                    let file = sources.file(s.file);
                    let lc = file.line_col(s.start);
                    o.insert("span".into(), serde_json::json!({ "file": file.name(), "line": lc.line, "col": lc.col }));
                }
                o.insert("kind".into(), "test".into());
                serde_json::Value::Object(o)
            })
            .collect();
        serde_json::to_string_pretty(&items).expect("report serializes")
    }
}

/// What `onsa test` did with a lowered module.
#[derive(Debug, Clone)]
pub enum TestRun {
    /// Every `test` block ran.
    Ran(TestReport),
    /// The module holds forms the interpreter of this version cannot run:
    /// E0200 for each (spec §18.1, S-224), and no test ran.
    Unsupported(Vec<Diagnostic>),
}

/// Run every `test` block of the lowered module (T3-8). `assert` failures
/// and panics (spec §9.2) fail the test and name the position; a failure of
/// the interpreter itself is an internal error (S-67, R-137). Before any test
/// runs, the forms the interpreter cannot run are E0200, all at once
/// ([`onsa_interp::unsupported`]), so what is reported does not depend on
/// the code the tests reach. The interpreter runs on the stack of a command
/// (R-05).
pub fn run_tests(
    sources: &SourceMap,
    module: &onsa_core::Module,
    opts: &TestOptions,
) -> Result<TestRun, InternalError> {
    guard_on_stack(|| {
        let unsupported = onsa_interp::unsupported(module);
        if unsupported.is_empty() {
            return TestRun::Ran(run_tests_unguarded(module, opts));
        }
        let mut diagnostics = reduce::exact(unsupported.iter().map(onsa_interp::Unsupported::diagnostic).collect());
        fill_found(sources, &mut diagnostics);
        debug_contract(sources, &diagnostics);
        TestRun::Unsupported(diagnostics)
    })
}

fn run_tests_unguarded(module: &onsa_core::Module, opts: &TestOptions) -> TestReport {
    let interp = onsa_interp::Interp::new(module);
    let mut report = TestReport::default();
    for (i, f) in module.fns.iter().enumerate() {
        let Some(name) = f.name.strip_prefix("test.") else { continue };
        if f.body.is_none() {
            continue;
        }
        if opts.filter.as_deref().is_some_and(|needle| !name.contains(needle)) {
            continue;
        }
        let outcome = match interp.call(onsa_core::FnId(i as u32), Vec::new()) {
            Ok(_) => TestOutcome { name: name.to_string(), status: TestStatus::Ok, message: None, span: None },
            Err(onsa_interp::Failure::Panic(p)) => {
                let message = match p.message.strip_prefix("assertion failed: ") {
                    Some(src) => format!("assert {src}"),
                    None => p.message.clone(),
                };
                TestOutcome {
                    name: name.to_string(),
                    status: TestStatus::Failed,
                    message: Some(message),
                    span: Some(p.span),
                }
            }
            // `run_tests` found every one before the tests ran.
            Err(onsa_interp::Failure::Unsupported(u)) => onsa_diag::internal::bug(
                Some(u.span),
                format!("the interpreter reached `{}`, which the check before the tests did not find", u.std_fn),
            ),
        };
        report.tests.push(outcome);
    }
    report
}
