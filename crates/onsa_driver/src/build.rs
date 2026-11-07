//! `onsa build --target <name>` (T4-5, spec §15.3, §14.2, §13.4): reads the
//! manifest's `[export]` and `[targets.<name>]`, checks the effects of the
//! items with `@export` (E0610), lowers with the target's memory settings, emits C, writes the
//! files and, when the platform is the host and the kind is `staticlib`,
//! compiles them with `cc` and archives them with `ar`. Cross targets get
//! the sources and the intended flags (`onsa_build.json`).

use std::path::{Path, PathBuf};
use std::process::Command;

use onsa_backend_c::{EmitOptions, ExportFlow, PanicMode};
use onsa_core::{LowerOptions, Module};
use onsa_diag::{Code, Diagnostic, SourceMap, Stage};
use onsa_sema::package_tree::{BUILD_DIR, MANIFEST};

use crate::consts::consts_stage;
use crate::manifest::table::After;
use crate::platform::{Platform, host_triple, platform};
use crate::{
    Analyzed, InternalError, Loaded, LowerError, Manifest, ManifestTarget, Spanned, guard, read_package_input,
};

#[derive(Debug, Clone, Default)]
pub struct BuildOptions {
    pub target: String,
    /// Output directory (default `target/<name>/` next to the manifest).
    pub out: Option<PathBuf>,
}

#[derive(Debug)]
pub enum BuildError {
    /// Manifest or usage problems (exit 2).
    Usage(String),
    /// The package or its exports do not check (exit 1).
    Diagnostics { sources: SourceMap, diagnostics: Vec<Diagnostic> },
    /// The manifest's diagnostics and those of the target's build that need
    /// no source, in one report before the sources are read; or, when
    /// `after_sources`, those of [`after_sources`] after their check (exit 2,
    /// §18.1, S-832).
    Manifest { sources: SourceMap, diagnostics: Vec<Diagnostic>, after_sources: bool },
    /// An internal error (S-67, exit 101): a panic, a broken Core (R-82), or
    /// generated C the C compiler rejects. `sources` renders its position.
    Internal { sources: SourceMap, error: Box<InternalError> },
}

#[derive(Debug, serde::Serialize)]
pub struct BuildReport {
    pub target: String,
    pub platform: String,
    pub kind: String,
    pub out_dir: PathBuf,
    /// Generated files, relative to `out_dir`.
    pub files: Vec<String>,
    pub cflags: Vec<String>,
    /// The archive, when compiled on the host.
    pub archive: Option<String>,
    /// Why nothing was compiled (cross target, `source` kind).
    pub note: Option<String>,
}

/// A target of the manifest, resolved and validated: its name and settings.
#[derive(Debug, Clone)]
pub struct ResolvedTarget {
    pub name: String,
    pub settings: TargetSettings,
}

/// What a build exports (spec §14.2, §15.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportSettings {
    /// The C prefix of the exported names (`[export] prefix`, §14.2): no
    /// default (R-121 (1), S-95); a build with exports stops without one
    /// (E1104, S-832).
    pub prefix: Option<String>,
    /// Flows by module path.
    pub flows: Vec<String>,
    /// Functions by module path.
    pub fns: Vec<String>,
}

impl ExportSettings {
    /// The items with `@export` of the package of `analyzed`
    /// ([`onsa_sema::Analysis::exports`]), and the `prefix` of `manifest`.
    pub fn of(analyzed: &Analyzed, manifest: Option<&Manifest>) -> ExportSettings {
        let a = &analyzed.analysis;
        let prefix = manifest.and_then(|m| Some(m.export.value.prefix.as_ref()?.value.clone()));
        let (mut flows, mut fns) = (Vec::new(), Vec::new());
        for d in a.exports() {
            let list = if a.def(d).as_flow().is_some() { &mut flows } else { &mut fns };
            list.push(a.qualified_name(d));
        }
        ExportSettings { prefix, flows, fns }
    }
}

/// Find `[targets.<target>]` in the manifest of `loaded` and validate it:
/// the diagnostics of the manifest and of the target's values stop the build
/// together (§18.1, S-827).
pub fn resolve_target(loaded: &Loaded, target: &str) -> Result<ResolvedTarget, BuildError> {
    let Some(read) = &loaded.manifest else {
        return Err(BuildError::Usage("no onsa.toml: a build needs the manifest's targets".into()));
    };
    let (manifest, t) = (&read.manifest, read.manifest.targets.get(target));
    let mut diagnostics = read.diagnostics.clone();
    diagnostics.extend(t.into_iter().flat_map(|t| t.value.build_diagnostics.iter().cloned()));
    if !diagnostics.is_empty() {
        return Err(BuildError::Manifest { sources: loaded.sources.clone(), diagnostics, after_sources: false });
    }
    let Some(t) = t else {
        let names: Vec<&String> = manifest.targets.keys().collect();
        return Err(BuildError::Usage(format!(
            "no target `{target}` in {MANIFEST} (targets: {})",
            if names.is_empty() {
                "none".to_string()
            } else {
                names.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
            }
        )));
    };
    let settings = TargetSettings::from_manifest(target, &t.value)?;
    Ok(ResolvedTarget { name: target.to_string(), settings })
}

/// What a build produces before anything is written: the Core module after
/// every stage, the settings, the C unit and the files as `build` writes them.
#[derive(Debug)]
pub struct BuildOutput {
    pub module: Module,
    pub settings: TargetSettings,
    /// What is exported, as the build read it.
    pub export: ExportSettings,
    pub unit: onsa_backend_c::CUnit,
    /// `(file name, text)` in the order `build` writes them.
    pub files: Vec<(String, String)>,
}

/// The build of an analyzed package for `target` of its manifest, without the
/// file system (R-80 (5), R-89 (3)): the one entry the tests and `onsa_web`
/// share with `onsa build`.
pub fn build_analyzed(loaded: &Loaded, analyzed: &Analyzed, target: &str) -> Result<BuildOutput, BuildError> {
    let resolved = resolve_target(loaded, target)?;
    build_resolved(loaded, analyzed, &resolved)
}

/// The stages of a build after the analysis: the export checks, lowering
/// with the target's settings, the build-time `const` evaluation and C.
pub fn build_resolved(
    loaded: &Loaded,
    analyzed: &Analyzed,
    resolved: &ResolvedTarget,
) -> Result<BuildOutput, BuildError> {
    let internal =
        |error: InternalError| BuildError::Internal { sources: loaded.sources.clone(), error: Box::new(error) };
    guard(|| build_stages(loaded, analyzed, resolved)).map_err(internal)?
}

fn build_stages(loaded: &Loaded, analyzed: &Analyzed, resolved: &ResolvedTarget) -> Result<BuildOutput, BuildError> {
    // Lowering and the build report every diagnostic, each once (S-67): the
    // build's own go through `LowerError::reported`, as lowering's do.
    let diagnostics = |e: LowerError| match e {
        LowerError::Diagnostics(diagnostics) => {
            crate::debug_contract(&loaded.sources, &diagnostics, loaded.toml_file());
            BuildError::Diagnostics { sources: loaded.sources.clone(), diagnostics }
        }
        LowerError::Internal(e) => BuildError::Internal { sources: loaded.sources.clone(), error: Box::new(e) },
    };
    let internal =
        |error: InternalError| BuildError::Internal { sources: loaded.sources.clone(), error: Box::new(error) };
    if !analyzed.diagnostics.is_empty() {
        // The check's diagnostics, already reduced per unit.
        return Err(BuildError::Diagnostics {
            sources: loaded.sources.clone(),
            diagnostics: analyzed.diagnostics.clone(),
        });
    }
    let settings = &resolved.settings;
    let export = &ExportSettings::of(analyzed, loaded.manifest());
    let sources = loaded.sources.clone();
    let emit_opts = EmitOptions {
        package: loaded.name.clone(),
        prefix: export.prefix.clone(),
        exports: export.flows.iter().map(|f| ExportFlow { flow: f.clone() }).collect(),
        export_fns: export.fns.clone(),
        panic: settings.panic,
        bulk_threshold: None,
        provides_alloc: settings.provides_alloc,
        panic_messages: settings.panic_messages,
        locate: Some(Box::new(move |span: onsa_diag::Span| {
            let f = sources.file(span.file);
            (f.name().to_string(), f.line_col(span.start).line)
        })),
        ptr_size: settings.platform.ptr_size,
        cflags: settings.platform.cflags.clone(),
    };
    // They stop the build before its own checks (E0610) and the C backend's (E0302), S-839.
    let late = after_sources(loaded.manifest(), &emit_opts);
    if !late.is_empty() {
        return Err(BuildError::Manifest { sources: loaded.sources.clone(), diagnostics: late, after_sources: true });
    }
    let export_diags = check_exports(analyzed, settings);
    if !export_diags.is_empty() {
        return Err(diagnostics(LowerError::reported(export_diags)));
    }

    // Lower and emit.
    // `bulk_threshold` is not a key of §15.3: `memory.bulk` replaces it (W9-06).
    let lower_opts = LowerOptions { ptr_size: settings.platform.ptr_size, ..Default::default() };
    let module = crate::lower_core_with(analyzed, &lower_opts).map_err(diagnostics)?;
    // The exports are the entries of the build (spec §15.2, S-242): the
    // evaluation of the `const`s and the C unit start from them.
    let roots = onsa_backend_c::export_roots(&module, &emit_opts);
    let module = consts_stage(module, &roots).map_err(internal)?;
    let unit = onsa_backend_c::emit(&module, &emit_opts).map_err(|d| diagnostics(LowerError::reported(d)))?;
    let files = unit.files(&loaded.name);
    Ok(BuildOutput { module, settings: settings.clone(), export: export.clone(), unit, files })
}

/// The diagnostics of the manifest that the sources make required, after
/// their check (§14.2, §18.1, S-832): those of `manifest` whose
/// [`After`] holds of the build's `opts`. The one place of them.
pub(crate) fn after_sources(manifest: Option<&Manifest>, opts: &EmitOptions) -> Vec<Diagnostic> {
    let holds = |when: &After| match when {
        After::Exports => opts.exports_any(),
    };
    let all = manifest.into_iter().flat_map(|m| &m.after_sources);
    all.filter(|(when, _)| holds(when)).map(|(_, d)| d.clone()).collect()
}

/// Build the package at `path` for `target`: a package directory or its
/// `onsa.toml`; `None` is the package above the working directory (§15.1,
/// [`read_package_input`]). A `.onsa` file is a usage error: the result of
/// `build` is the whole package.
pub fn build(path: Option<&Path>, opts: &BuildOptions) -> Result<BuildReport, BuildError> {
    let input = read_package_input(path).map_err(BuildError::Usage)?;
    let mut loaded = Loaded::from_input(input).map_err(BuildError::Usage)?;
    let resolved = resolve_target(&loaded, &opts.target)?;
    let root = guard(|| match &loaded.root {
        Some(root) => root.clone(),
        None => onsa_diag::internal::bug(None, "a package read from a path has no root"),
    });
    let root = match root {
        Ok(root) => root,
        Err(error) => return Err(BuildError::Internal { sources: loaded.sources, error: Box::new(error) }),
    };
    let analyzed = match crate::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(error) => return Err(BuildError::Internal { sources: loaded.sources, error: Box::new(error) }),
    };
    let output = build_resolved(&loaded, &analyzed, &resolved)?;
    let settings = &output.settings;

    // Write.
    let out_dir = opts.out.clone().unwrap_or_else(|| root.join(BUILD_DIR).join(&opts.target));
    std::fs::create_dir_all(&out_dir)
        .map_err(|e| BuildError::Usage(format!("cannot create {}: {e}", out_dir.display())))?;
    let mut files = Vec::new();
    for (name, text) in &output.files {
        std::fs::write(out_dir.join(name), text)
            .map_err(|e| BuildError::Usage(format!("cannot write {}: {e}", out_dir.join(name).display())))?;
        files.push(name.clone());
    }
    let source_name = onsa_backend_c::CUnit::source_name(&loaded.name);

    let mut report = BuildReport {
        target: opts.target.clone(),
        platform: settings.platform.triple.clone(),
        kind: settings.kind.clone(),
        out_dir: out_dir.clone(),
        files,
        cflags: settings.platform.cflags.clone(),
        archive: None,
        note: None,
    };

    // Compile on the host.
    if settings.kind == crate::manifest::table::STATICLIB {
        if settings.platform.is_host() && !settings.platform.msvc {
            let obj = format!("onsa_{}.o", loaded.name);
            let lib = format!("libonsa_{}.a", loaded.name);
            let cc = Command::new("cc")
                .args(&settings.platform.cflags)
                .arg("-c")
                .arg(out_dir.join(&source_name))
                .arg("-I")
                .arg(&out_dir)
                .arg("-o")
                .arg(out_dir.join(&obj))
                .output()
                .map_err(|e| BuildError::Usage(format!("cannot run cc: {e}")))?;
            if !cc.status.success() {
                // The C is the compiler's output: rejecting it is a bug of the compiler.
                return Err(BuildError::Internal {
                    sources: loaded.sources,
                    error: Box::new(InternalError::generated_c(format!(
                        "the C compiler rejected the generated C (`cc` exited with {}):\n{}",
                        cc.status,
                        String::from_utf8_lossy(&cc.stderr).trim_end()
                    ))),
                });
            }
            let ar = Command::new("ar")
                .arg("rcs")
                .arg(out_dir.join(&lib))
                .arg(out_dir.join(&obj))
                .output()
                .map_err(|e| BuildError::Usage(format!("cannot run ar: {e}")))?;
            if !ar.status.success() {
                return Err(BuildError::Usage(format!("ar failed:\n{}", String::from_utf8_lossy(&ar.stderr))));
            }
            report.files.push(obj);
            report.files.push(lib.clone());
            report.archive = Some(lib);
        } else {
            report.note = Some(format!(
                "sources only: `{}` is not the host ({}); compile with: cc {} -c {source_name}",
                settings.platform.triple,
                host_triple(),
                settings.platform.cflags.join(" ")
            ));
        }
    } else {
        report.note = Some("kind = \"source\": C sources only".into());
    }
    let json = serde_json::to_string_pretty(&report).expect("report serializes");
    std::fs::write(out_dir.join("onsa_build.json"), json)
        .map_err(|e| BuildError::Usage(format!("cannot write onsa_build.json: {e}")))?;
    report.files.push("onsa_build.json".into());
    Ok(report)
}

/// The validated `[targets.<name>]` settings.
#[derive(Debug, Clone)]
pub struct TargetSettings {
    pub kind: String,
    pub platform: Platform,
    pub panic: PanicMode,
    pub panic_messages: bool,
    pub provides_alloc: bool,
}

impl TargetSettings {
    /// The settings of `t`, whose values the build supports (its
    /// [`ManifestTarget::build_diagnostics`] are empty, so it has a platform
    /// this version knows).
    pub fn from_manifest(name: &str, t: &ManifestTarget) -> Result<TargetSettings, BuildError> {
        let triple = t.platform.as_ref().map_or("", |p| p.value.as_str());
        let platform =
            platform(triple).unwrap_or_else(|m| onsa_diag::internal::bug(None, format!("[targets.{name}]: {m}")));
        let panic = match text(&t.panic) {
            None => {
                if platform.hosted {
                    PanicMode::Poison
                } else {
                    PanicMode::Reset
                }
            }
            // The check of the manifest stopped every other value (E1103, `table::PANIC`).
            Some(v) => PanicMode::parse(v).unwrap_or_else(|| {
                onsa_diag::internal::bug(None, format!("[targets.{name}]: the panic setting `{v}`"))
            }),
        };
        Ok(TargetSettings {
            kind: t.kind.value.clone(),
            platform,
            panic,
            panic_messages: t.panic_messages.as_ref().is_none_or(|b| b.value),
            provides_alloc: t.provides.iter().any(|e| e.value == crate::manifest::table::ALLOC),
        })
    }
}

/// The text of a string of the manifest that may be left out.
fn text(v: &Option<Spanned<String>>) -> Option<&str> {
    v.as_ref().map(|s| s.value.as_str())
}

/// E0610: an exported function uses only the effects the target provides
/// (§14.2). The checks of the declarations are the check's (§14.2).
fn check_exports(analyzed: &Analyzed, settings: &TargetSettings) -> Vec<Diagnostic> {
    let a = &analyzed.analysis;
    let mut out = Vec::new();
    for d in a.exports() {
        let Some(f) = a.def(d).as_fn() else { continue };
        let error = |uses: &str| {
            let msg = format!(
                "the exported function `{}` uses {uses}, which the target does not provide (§14.2)",
                a.qualified_name(d)
            );
            Diagnostic::new(Stage::Build, Code::E0610, a.def(d).name_span, msg)
        };
        if f.effects.alloc && !settings.provides_alloc {
            out.push(error("`Alloc`"));
        }
        out.extend(f.effects.other.iter().map(|e| error(&format!("`{e}`"))));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageInput;

    /// S-154, S-827, §18.1: the build of a target reports the manifest's
    /// diagnostics and the E0200 of that target's values together, before
    /// the sources; another target's values are not its; a name not in the
    /// manifest is a usage error.
    #[test]
    fn a_build_stops_on_the_manifest_and_the_values_of_its_target_together() {
        let manifest = |extra: &str| {
            let text = format!(
                "[package]\nname = \"p\"\nedition = \"2026\"\n{extra}\
                 [targets.t]\nkind = \"exe\"\nplatform = \"host\"\n\
                 [targets.u]\nkind = \"staticlib\"\nplatform = \"host\"\n"
            );
            let source = crate::ManifestSource { path: MANIFEST.into(), text, form: crate::ManifestForm::File };
            let files = vec![crate::SourceFile { path: "a.onsa".into(), text: "pub fn f() -> I32 { 1 }\n".into() }];
            Loaded::from_input(PackageInput { manifest: Some(source), files, ..Default::default() }).unwrap()
        };
        let codes = |loaded: &Loaded, target: &str| match resolve_target(loaded, target) {
            Err(BuildError::Manifest { diagnostics, .. }) => diagnostics.iter().map(|d| d.code).collect(),
            Ok(_) => Vec::new(),
            Err(e) => panic!("{e:?}"),
        };
        let clean = manifest("");
        assert_eq!(codes(&clean, "t"), [Code::E0200]);
        assert_eq!(codes(&clean, "u"), []);
        assert!(matches!(resolve_target(&clean, "v"), Err(BuildError::Usage(m)) if m.contains("no target `v`")));
        let broken = manifest("colour = 1\n");
        assert_eq!(codes(&broken, "t"), [Code::E1102, Code::E0200]);
        assert_eq!(codes(&broken, "u"), [Code::E1102]);
        assert_eq!(broken.manifest_diagnostics().len(), 1, "the check reports the E1102 alone");
    }

    /// S-832, §14.2: `prefix` is required by a build whose package has
    /// `@export` items, after the check of its sources (an error of the check
    /// is reported alone); not by a package without them, whose build reads
    /// no prefix (R-121 (1)); the check does not report it.
    #[test]
    fn a_build_with_exports_needs_a_prefix_after_the_check() {
        let build = |export: &str, src: &str| {
            let text = format!(
                "[package]\nname = \"p\"\nedition = \"2026\"\n{export}[targets.t]\nkind = \"source\"\nlang = \"c\"\n\
                 platform = \"host\"\n"
            );
            let source = crate::ManifestSource { path: MANIFEST.into(), text, form: crate::ManifestForm::File };
            let files = vec![crate::SourceFile { path: "a.onsa".into(), text: src.into() }];
            let mut loaded =
                Loaded::from_input(PackageInput { manifest: Some(source), files, ..Default::default() }).unwrap();
            assert!(loaded.manifest_diagnostics().is_empty());
            let analyzed =
                crate::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
            build_analyzed(&loaded, &analyzed, "t")
        };
        let exported = "@export\npub fn f() -> I32 {\n  1\n}\n";
        match build("", exported) {
            Err(BuildError::Manifest { diagnostics, .. }) => {
                let found: Vec<(Code, &str, usize)> =
                    diagnostics.iter().map(|d| (d.code, d.message.as_str(), d.fixes.len())).collect();
                assert_eq!(found, [(Code::E1104, "missing key `export.prefix`", 1)]);
            }
            other => panic!("{other:?}"),
        }
        let broken = "@export\npub fn f() -> I32 {\n  true\n}\n";
        match build("", broken) {
            Err(BuildError::Diagnostics { diagnostics, .. }) => {
                assert!(diagnostics.iter().all(|d| d.code != Code::E1104), "{diagnostics:?}")
            }
            other => panic!("{other:?}"),
        }
        let out = build("[export]\nprefix = \"vc_\"\n", exported).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(out.export.prefix.as_deref(), Some("vc_"));
        assert_eq!(out.unit.fns.iter().map(|f| f.symbol.as_str()).collect::<Vec<_>>(), ["vc_f"]);
        // An E0610 of the build too (the target provides no `Alloc`): the E1104 first, as the check
        // passes; the E0610 after the `prefix` is written (S-832, §18.1: the check of the sources is the check's).
        let alloc = "@export\npub fn f() -> U32 uses {Alloc} {\n  2\n}\n";
        let codes = |r: Result<BuildOutput, BuildError>| match r {
            Err(BuildError::Manifest { diagnostics, .. } | BuildError::Diagnostics { diagnostics, .. }) => {
                diagnostics.iter().map(|d| d.code).collect::<Vec<_>>()
            }
            other => panic!("{other:?}"),
        };
        assert_eq!(codes(build("", alloc)), [Code::E1104]);
        assert_eq!(codes(build("[export]\nprefix = \"vc_\"\n", alloc)), [Code::E0610]);
        // No `@export`: no prefix, none read, and no name of the export (no header, no `take_panic`).
        let out = build("", "pub fn f() -> I32 {\n  1\n}\n").unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!((out.export.prefix, out.unit.headers.len(), out.unit.take_panic), (None, 0, None));
    }

    #[test]
    fn target_settings_defaults() {
        let target = |kind: &str, platform: &str| ManifestTarget {
            kind: Spanned::new(kind.into()),
            platform: Some(Spanned::new(platform.into())),
            ..Default::default()
        };
        let t = target("staticlib", "host");
        let s = TargetSettings::from_manifest("t", &t).unwrap();
        assert_eq!(s.panic, PanicMode::Poison);
        assert!(!s.provides_alloc);
        let t = target("staticlib", "thumbv7em-none-eabihf");
        assert_eq!(TargetSettings::from_manifest("t", &t).unwrap().panic, PanicMode::Reset);
        // Every value of `panic` the manifest takes is a mode (the check of the
        // manifest stops the others, E1103).
        for &p in crate::manifest::table::PANIC {
            let t = ManifestTarget { panic: Some(Spanned::new(p.into())), ..target("staticlib", "host") };
            assert!(TargetSettings::from_manifest("t", &t).is_ok(), "{p}");
        }
    }
}
