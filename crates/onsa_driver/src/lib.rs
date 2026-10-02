//! Pipeline driver: loads a package (S-11), embeds `std` (D-07), and runs
//! parse -> analyze. Each milestone adds a stage (`docs/implementation-tasks.md` §4).

pub mod graph;
pub mod interface;

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
}

/// Minimal manifest (spec §15.3); the rest is read in M4.
#[derive(Debug, Default, serde::Deserialize)]
pub struct Manifest {
    pub package: ManifestPackage,
    #[serde(default)]
    pub dependencies: HashMap<String, String>,
}

#[derive(Debug, Default, serde::Deserialize)]
pub struct ManifestPackage {
    pub name: String,
    #[serde(default)]
    pub edition: String,
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
            return load_package(&manifest);
        }
        if p.is_dir() {
            return Err(format!("{} has no onsa.toml", p.display()));
        }
    }
    let mut loaded = Loaded { sources: SourceMap::default(), name: String::new(), root: None, modules: Vec::new() };
    for p in paths {
        let text = std::fs::read_to_string(p).map_err(|e| format!("cannot read {}: {e}", p.display()))?;
        let stem = p.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
        if loaded.name.is_empty() {
            loaded.name = stem.clone();
        }
        let id = loaded.sources.add(p.to_string_lossy(), text);
        loaded.modules.push((id, stem));
    }
    Ok(loaded)
}

fn load_package(manifest: &Path) -> Result<Loaded, String> {
    let text = std::fs::read_to_string(manifest).map_err(|e| format!("cannot read {}: {e}", manifest.display()))?;
    let m: Manifest = toml::from_str(&text).map_err(|e| format!("{}: {e}", manifest.display()))?;
    let root = manifest.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut files = Vec::new();
    let mut stack = vec![root.clone()];
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
    let mut loaded =
        Loaded { sources: SourceMap::default(), name: m.package.name, root: Some(root.clone()), modules: Vec::new() };
    for p in files {
        let text = std::fs::read_to_string(&p).map_err(|e| format!("cannot read {}: {e}", p.display()))?;
        let rel = p.strip_prefix(&root).unwrap_or(&p).to_path_buf();
        let id = loaded.sources.add(rel.to_string_lossy(), text);
        loaded.modules.push((id, module_path(&rel)));
    }
    Ok(loaded)
}

fn std_package(sources: &mut SourceMap) -> Package {
    let modules = STD
        .iter()
        .map(|(path, text)| {
            let file = sources.add(format!("std/{}.onsa", path.replace('.', "/")), *text);
            Module { path: path.to_string(), file, text: text.to_string(), parsed: onsa_syntax::parse(file, text) }
        })
        .collect();
    Package { name: "std".into(), modules, deps: Vec::new(), is_std: true }
}

/// Parse only (the `mode: parse` depth of `tests/spec`, D-05).
pub fn parse_only(sources: &SourceMap) -> CheckResult {
    let mut result = CheckResult::default();
    for (id, file) in sources.files() {
        result.diagnostics.extend(onsa_syntax::parse(id, file.text()).diagnostics);
    }
    result
}

/// Check the files already in `sources` as one package whose modules are
/// named after the file stems. `std` is appended to `sources`.
pub fn check(sources: &mut SourceMap) -> CheckResult {
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
pub fn check_loaded(loaded: &mut Loaded) -> CheckResult {
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
pub fn analyze_loaded(loaded: &mut Loaded) -> Analyzed {
    let modules = loaded.modules.clone();
    let name = loaded.name.clone();
    analyze_package(&mut loaded.sources, &name, &modules)
}

pub fn analyze_package(sources: &mut SourceMap, name: &str, modules: &[(FileId, String)]) -> Analyzed {
    let user_modules: Vec<Module> = modules
        .iter()
        .map(|(file, path)| {
            let text = sources.file(*file).text().to_string();
            let parsed = onsa_syntax::parse(*file, &text);
            Module { path: path.clone(), file: *file, text, parsed }
        })
        .collect();
    let std = std_package(sources);
    let pkg = Package { name: name.to_string(), modules: user_modules, deps: vec![std], is_std: false };
    let analysis = onsa_sema::analyze(&pkg);
    let mut diagnostics = merge(&pkg, analysis.diagnostics.clone());
    fill_found(sources, &mut diagnostics);
    Analyzed { pkg, analysis, diagnostics }
}

pub use graph::graph;
pub use interface::{Interface, interface, render_json, render_text};

/// Lower a checked package to Core (T3-3). Only meaningful when
/// `Analyzed::diagnostics` is empty; lowering diagnostics (E0200 for
/// features outside the core) come back as the error.
pub fn lower_core(analyzed: &Analyzed) -> Result<onsa_core::Module, Vec<Diagnostic>> {
    onsa_core::lower(&analyzed.pkg, &analyzed.analysis)
}

pub fn check_package(sources: &mut SourceMap, name: &str, modules: &[(FileId, String)]) -> CheckResult {
    let user_modules: Vec<Module> = modules
        .iter()
        .map(|(file, path)| {
            let text = sources.file(*file).text().to_string();
            let parsed = onsa_syntax::parse(*file, &text);
            Module { path: path.clone(), file: *file, text, parsed }
        })
        .collect();
    let std = std_package(sources);
    let pkg = Package { name: name.to_string(), modules: user_modules, deps: vec![std], is_std: false };
    let analysis = onsa_sema::analyze(&pkg);
    let mut diagnostics = merge(&pkg, analysis.diagnostics);
    fill_found(sources, &mut diagnostics);
    CheckResult { diagnostics }
}

/// Every diagnostic names the offending source (`found`, §18.1): when the
/// emitter left it out, take the text of the span.
fn fill_found(sources: &SourceMap, diagnostics: &mut [Diagnostic]) {
    for d in diagnostics {
        if d.found.as_deref().is_none_or(str::is_empty) {
            let file = sources.file(d.span.file);
            let text = &file.text()[d.span.start as usize..d.span.end as usize];
            if !text.trim().is_empty() {
                d.found = Some(text.trim().to_string());
            }
        }
    }
}

/// P-01: one diagnostic per item. Parser diagnostics win over analysis
/// diagnostics for the same item; otherwise the earliest wins.
fn merge(pkg: &Package, sema: Vec<Diagnostic>) -> Vec<Diagnostic> {
    // Item spans of every user module, keyed by file.
    let mut items: HashMap<FileId, Vec<Span>> = HashMap::new();
    let mut out: Vec<Diagnostic> = Vec::new();
    let mut parser_items: std::collections::HashSet<(FileId, usize)> = Default::default();
    for m in &pkg.modules {
        let spans: Vec<Span> = m.parsed.ast.root.iter().map(|&i| m.parsed.ast.item(i).span).collect();
        for d in &m.parsed.diagnostics {
            if let Some(i) = spans.iter().position(|s| s.contains(d.span.start) || (s.start == d.span.start)) {
                parser_items.insert((m.file, i));
            }
            out.push(d.clone());
        }
        items.insert(m.file, spans);
    }
    let mut best: HashMap<(FileId, usize), Diagnostic> = HashMap::new();
    for d in sema {
        let Some(spans) = items.get(&d.span.file) else {
            // Diagnostics inside `std` (none expected) are kept as is.
            out.push(d);
            continue;
        };
        match spans.iter().position(|s| s.contains(d.span.start) || s.start == d.span.start) {
            Some(i) => {
                if parser_items.contains(&(d.span.file, i)) {
                    continue;
                }
                let key = (d.span.file, i);
                let replace = best.get(&key).is_none_or(|b| d.span.start < b.span.start);
                if replace {
                    best.insert(key, d);
                }
            }
            None => out.push(d),
        }
    }
    out.extend(best.into_values());
    out.sort_by_key(|d| (d.span.file, d.span.start));
    out
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

    #[test]
    fn module_paths() {
        assert_eq!(module_path(Path::new("dsp/voice.onsa")), "dsp.voice");
        assert_eq!(module_path(Path::new("util.onsa")), "util");
    }
}
