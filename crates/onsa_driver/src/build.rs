//! `onsa build --target <name>` (T4-5, spec §15.3, §14.2, §13.4): reads the
//! manifest's `[export]` and `[targets.<name>]`, checks the effects of the
//! items with `@export` (E0610), lowers with the target's memory settings, emits C, writes the
//! files and, when the platform is the host and the kind is `staticlib`,
//! compiles them with `cc` and archives them with `ar`. Cross targets get
//! the sources and the intended flags (`onsa_build.json`).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use onsa_backend_c::{EmitOptions, ExportFlow, PanicMode};
use onsa_core::{ConstId, Expr, ExprKind, Lit, LowerOptions, Module, Ty, TypeDefKind};
use onsa_diag::{Code, Diagnostic, SourceMap, Stage};
use onsa_interp::{ArrayData, Interp, Value};
use onsa_sema::package_tree::{BUILD_DIR, MANIFEST};

use crate::{
    Analyzed, CoreStage, InternalError, Loaded, LowerError, Manifest, ManifestTarget, Spanned, guard,
    read_package_input,
};

/// A build platform (spec §15.3 item 1, §13.4): pointer width and the
/// compiler flags that keep the IEEE semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Platform {
    pub triple: String,
    pub arch: String,
    pub os: String,
    pub ptr_size: u32,
    /// Has an operating system (hosted): `poison` is the default panic mode.
    pub hosted: bool,
    pub msvc: bool,
    pub cflags: Vec<String>,
}

/// Triple of the machine the compiler runs on.
pub fn host_triple() -> String {
    let arch = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        "x86" => "i686",
        "arm" => "armv7",
        other => other,
    };
    let os = match std::env::consts::OS {
        "macos" => "apple-darwin",
        "linux" => "unknown-linux-gnu",
        "windows" => "pc-windows-msvc",
        "freebsd" => "unknown-freebsd",
        other => other,
    };
    format!("{arch}-{os}")
}

/// Resolve a target triple (`"host"` is the compiler's own machine).
pub fn platform(triple: &str) -> Result<Platform, String> {
    let triple = if triple == "host" { host_triple() } else { triple.to_string() };
    let parts: Vec<&str> = triple.split('-').collect();
    if parts.len() < 2 {
        return Err(format!("`{triple}` is not a target triple (`<arch>-<vendor>-<os>[-<abi>]`)"));
    }
    let arch = parts[0].to_string();
    let rest = parts[1..].join("-");
    let ptr_size = match arch.as_str() {
        "x86_64" | "aarch64" | "arm64" | "riscv64" | "powerpc64" | "mips64" | "wasm64" => 8,
        "i686" | "i586" | "i386" | "riscv32" | "xtensa" | "arm" | "wasm32" | "mips" | "powerpc" => 4,
        a if a.starts_with("thumbv") || a.starts_with("armv") || a.starts_with("riscv32") => 4,
        a => return Err(format!("unknown architecture `{a}` in `{triple}`")),
    };
    let bare = rest.contains("none") || rest.contains("eabi") && !rest.contains("linux");
    let msvc = rest.contains("msvc");
    let os = if bare {
        "none".to_string()
    } else if rest.contains("darwin") || rest.contains("apple") {
        "macos".into()
    } else if rest.contains("linux") {
        "linux".into()
    } else if rest.contains("windows") {
        "windows".into()
    } else if rest.contains("freebsd") {
        "freebsd".into()
    } else {
        return Err(format!("unknown operating system in `{triple}`"));
    };
    // The flags the generated C needs (spec §13.4) are the backend's; then
    // the optimization level, then the flags of the architecture.
    let (fp, opt) = if msvc { (onsa_backend_c::FP_CFLAGS_MSVC, "/O2") } else { (onsa_backend_c::FP_CFLAGS, "-O2") };
    let mut cflags: Vec<String> = fp.iter().chain([&opt]).map(|f| f.to_string()).collect();
    match arch.as_str() {
        "i686" | "i586" | "i386" if !msvc => cflags.extend(["-m32".into(), "-msse2".into(), "-mfpmath=sse".into()]),
        a if a.starts_with("thumbv") => {
            cflags.extend(["-mthumb".into(), "-ffreestanding".into(), "-DONSA_NO_TLS".into()]);
            if rest.ends_with("hf") {
                cflags.push("-mfloat-abi=hard".into());
            }
        }
        _ => {}
    }
    Ok(Platform { triple, arch, os, ptr_size, hosted: !bare, msvc, cflags })
}

impl Platform {
    /// The compiler runs on this platform (so `cc` can build for it).
    pub fn is_host(&self) -> bool {
        let host = platform(&host_triple()).ok();
        host.is_some_and(|h| h.arch == self.arch && h.os == self.os)
    }
}

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
    /// no source, in one report before the sources are read (exit 2, §18.1).
    Manifest { sources: SourceMap, diagnostics: Vec<Diagnostic> },
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
    /// The C prefix of the exported names (default `onsa_`).
    pub prefix: String,
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
        let prefix = manifest.and_then(|m| Some(m.export.as_ref()?.value.prefix.as_ref()?.value.clone()));
        let (mut flows, mut fns) = (Vec::new(), Vec::new());
        for d in a.exports() {
            let list = if a.def(d).as_flow().is_some() { &mut flows } else { &mut fns };
            list.push(a.qualified_name(d));
        }
        ExportSettings { prefix: prefix.unwrap_or_else(|| "onsa_".into()), flows, fns }
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
        return Err(BuildError::Manifest { sources: loaded.sources.clone(), diagnostics });
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
    let export_diags = check_exports(analyzed, settings);
    if !export_diags.is_empty() {
        return Err(diagnostics(LowerError::reported(export_diags)));
    }

    // Lower and emit.
    // `bulk_threshold` is not a key of §15.3: `memory.bulk` replaces it (W9-06).
    let lower_opts = LowerOptions { bulk_threshold: None, ptr_size: settings.platform.ptr_size };
    let module = crate::lower_core_with(analyzed, &lower_opts).map_err(diagnostics)?;
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
    // The exports are the entries of the build (spec §15.2, S-242): the
    // evaluation of the `const`s and the C unit start from them.
    let roots = onsa_backend_c::export_roots(&module, &emit_opts);
    let module = consts_stage(module, &roots).map_err(internal)?;
    let unit = onsa_backend_c::emit(&module, &emit_opts).map_err(|d| diagnostics(LowerError::reported(d)))?;
    let files = unit.files(&loaded.name);
    Ok(BuildOutput { module, settings: settings.clone(), export: export.clone(), unit, files })
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
    if settings.kind == "staticlib" {
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
    /// [`ManifestTarget::build_diagnostics`] are empty).
    pub fn from_manifest(name: &str, t: &ManifestTarget) -> Result<TargetSettings, BuildError> {
        let usage = |m: String| BuildError::Usage(format!("[targets.{name}]: {m}"));
        let platform = platform(&t.platform.value).map_err(&usage)?;
        let panic = match text(&t.panic) {
            None => {
                if platform.hosted {
                    PanicMode::Poison
                } else {
                    PanicMode::Reset
                }
            }
            Some("poison") => PanicMode::Poison,
            Some("trap") => PanicMode::Trap,
            Some("reset") => PanicMode::Reset,
            Some("halt") => PanicMode::Halt,
            // The check of the manifest stopped every other value (E1103, `table::PANIC`).
            Some(other) => onsa_diag::internal::bug(None, format!("[targets.{name}]: the panic setting `{other}`")),
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

/// The build-time `const` evaluation as a stage: [`inline_consts`] of the
/// `const`s that `roots` reach, then the verifier at its boundary (R-82).
///
/// The evaluation and the reach are the same set (S-242, W2-13): a `const`
/// that no entry reaches is not evaluated, so its initializer cannot stop the
/// build (an internal error of the evaluation), and every `const` the C unit
/// reaches after the evaluation was offered to it (the reach of the
/// evaluated module from the same roots is a part of this one: an evaluated
/// initializer calls nothing).
fn consts_stage(mut module: Module, roots: &[onsa_core::FnId]) -> Result<Module, InternalError> {
    let reached = onsa_core::reach(&module, roots).consts;
    let replacements = crate::guard_on_stack(|| inline_consts(&module, &reached))?;
    for (i, e) in replacements {
        module.consts[i].init = e;
    }
    crate::verify_core(&module, CoreStage::Consts)?;
    Ok(module)
}

/// `const` initializers that call functions are evaluated with the
/// interpreter at build time (spec §6.6, T3-9): the literals that replace
/// them, so the C backend can emit a static initializer. Only the `const`s
/// of `reached`, and only through [`consts_stage`], which runs it on the
/// stack of a command (R-05).
fn inline_consts(module: &Module, reached: &BTreeSet<ConstId>) -> Vec<(usize, Expr)> {
    let mut replacements: Vec<(usize, Expr)> = Vec::new();
    {
        let interp = Interp::new(module);
        for &id in reached {
            let (i, c) = (id.0 as usize, module.const_(id));
            if is_static_init(&c.init) {
                continue;
            }
            // A panic names this `const` (S-67).
            let _scope = onsa_diag::internal::item_scope(c.init.span);
            // Each `const` is an evaluation of its own from call depth 0, as
            // in `onsa test` (spec §12.5). One that panics or reaches a form
            // the interpreter cannot run stays as it is, and the C backend
            // stops at it with E0200; E0419 at the initializer (spec §6.6,
            // S-222) is W9-03's. A failure of the interpreter itself unwinds
            // to the guard of `consts_stage` (S-67).
            let v = match interp.const_value(id) {
                Ok(v) => v,
                Err(onsa_interp::Failure::Panic(_) | onsa_interp::Failure::Unsupported(_)) => continue,
            };
            if let Some(e) = value_to_expr(module, &v, &c.ty, c.init.span) {
                replacements.push((i, e));
            }
        }
    }
    replacements
}

fn is_static_init(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Const(_) | ExprKind::Zeroed => true,
        ExprKind::Unary(_, x) => is_static_init(x),
        ExprKind::Struct { fields, .. } | ExprKind::Variant { fields, .. } => fields.iter().all(is_static_init),
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => xs.iter().all(is_static_init),
        ExprKind::Repeat { elem, .. } => is_static_init(elem),
        _ => false,
    }
}

/// A literal / aggregate expression with the value `v`.
pub fn value_to_expr(m: &Module, v: &Value, ty: &Ty, span: onsa_diag::Span) -> Option<Expr> {
    let lit = |l: Lit| Some(Expr::new(ty.clone(), span, ExprKind::Lit(l)));
    match (v, ty) {
        (Value::I8(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I16(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I32(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I64(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U8(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U16(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U32(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U64(x), _) => lit(Lit::Int(*x as i128)),
        (Value::F32(x), _) => lit(Lit::F32(*x)),
        (Value::F64(x), _) => lit(Lit::F64(*x)),
        (Value::Bool(x), _) => lit(Lit::Bool(*x)),
        (Value::Char(x), _) => lit(Lit::Char(*x)),
        (Value::Unit, _) => lit(Lit::Unit),
        (Value::Array(data), Ty::Array(elem, _)) => {
            let xs: Vec<Expr> = match data {
                ArrayData::F32(xs) => {
                    xs.iter().map(|x| Expr::new((**elem).clone(), span, ExprKind::Lit(Lit::F32(*x)))).collect()
                }
                ArrayData::Any(vs) => vs.iter().map(|x| value_to_expr(m, x, elem, span)).collect::<Option<Vec<_>>>()?,
            };
            Some(Expr::new(ty.clone(), span, ExprKind::Array(xs)))
        }
        (Value::Tuple(vs), Ty::Tuple(ts)) => {
            let xs = vs.iter().zip(ts).map(|(x, t)| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Tuple(xs)))
        }
        (Value::Struct(vs), Ty::Struct(id)) => {
            let TypeDefKind::Struct { fields } = &m.ty(*id).kind else { return None };
            let xs =
                vs.iter().zip(fields).map(|(x, (_, t))| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Struct { ty: *id, fields: xs }))
        }
        (Value::Enum { tag, fields: vs }, Ty::Enum(id)) => {
            let TypeDefKind::Enum { variants } = &m.ty(*id).kind else { return None };
            let (_, tys) = variants.get(*tag as usize)?;
            let xs = vs.iter().zip(tys).map(|(x, t)| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Variant { ty: *id, tag: *tag, fields: xs }))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageInput;

    /// S-242, W2-13: the build-time evaluation evaluates the `const`s that the
    /// entries reach (one reaches `READ` through `get`), and no other
    /// (`UNREAD` keeps its initializer, a call), so the evaluation and the
    /// reach are the same set.
    #[test]
    fn the_const_stage_evaluates_only_the_reached_consts() {
        let src = "fn three() -> U32 {\n  3\n}\n\nfn four() -> U32 {\n  4\n}\n\nconst READ: U32 = three()\n\nconst UNREAD: U32 = four()\n\npub fn get() -> U32 {\n  READ\n}\n";
        let mut loaded = Loaded::from_input(PackageInput::single_file("t.onsa", src)).unwrap();
        let analyzed = crate::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        assert!(analyzed.diagnostics.is_empty());
        let module = crate::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let get = module.fns.iter().position(|f| f.name.ends_with("get")).map(|i| onsa_core::FnId(i as u32));
        let module = consts_stage(module, &[get.unwrap()]).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let init = |name: &str| &module.consts.iter().find(|c| c.name.ends_with(name)).unwrap().init.kind;
        assert!(matches!(init("READ"), ExprKind::Lit(Lit::Int(3))), "{:?}", init("READ"));
        assert!(matches!(init("UNREAD"), ExprKind::Call { .. }), "{:?}", init("UNREAD"));
    }

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

    #[test]
    fn platforms() {
        let p = platform("aarch64-apple-darwin").unwrap();
        assert_eq!((p.ptr_size, p.hosted, p.msvc, p.os.as_str()), (8, true, false, "macos"));
        assert!(p.cflags.contains(&"-ffp-contract=off".to_string()));
        let p = platform("thumbv7em-none-eabihf").unwrap();
        assert_eq!((p.ptr_size, p.hosted), (4, false));
        assert!(p.cflags.iter().any(|f| f == "-mfloat-abi=hard"));
        assert!(p.cflags.iter().any(|f| f == "-DONSA_NO_TLS"));
        let p = platform("i686-unknown-linux-gnu").unwrap();
        assert_eq!(p.ptr_size, 4);
        assert!(p.cflags.iter().any(|f| f == "-mfpmath=sse"));
        let p = platform("x86_64-pc-windows-msvc").unwrap();
        assert!(p.msvc && p.cflags.iter().any(|f| f == "/fp:strict"));
        assert!(platform("host").unwrap().is_host());
        assert!(platform("sparc-sun-solaris").is_err());
        assert!(platform("nonsense").is_err());
    }

    #[test]
    fn target_settings_defaults() {
        let target = |kind: &str, platform: &str| ManifestTarget {
            kind: Spanned::new(kind.into()),
            platform: Spanned::new(platform.into()),
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
