//! `onsa build --target <name>` (T4-5, spec §15.3, §14.2, §13.4): reads the
//! manifest's `[export]` and `[targets.<name>]`, checks the exports (E0809,
//! E0610), lowers with the target's memory settings, emits C, writes the
//! files and, when the platform is the host and the kind is `staticlib`,
//! compiles them with `cc` and archives them with `ar`. Cross targets get
//! the sources and the intended flags (`onsa_build.json`).

use std::path::{Path, PathBuf};
use std::process::Command;

use onsa_backend_c::{EmitOptions, ExportFlow, PanicMode};
use onsa_core::{ConstId, Expr, ExprKind, Lit, LowerOptions, Module, Ty, TypeDefKind};
use onsa_diag::{Code, Diagnostic, SourceMap};
use onsa_interp::{ArrayData, Interp, Value};
use onsa_sema::def::DefKind;
use onsa_sema::ty::Rate;
use onsa_syntax::ast::Vis;

use crate::{
    Analyzed, CoreStage, InternalError, Loaded, LowerError, Manifest, ManifestExport, ManifestTarget, PackageInput,
    VerifyFailure, guard, read_manifest, read_sources,
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
    let mut cflags: Vec<String> = if msvc {
        vec!["/std:c11".into(), "/O2".into(), "/fp:strict".into()]
    } else {
        vec!["-std=c11".into(), "-O2".into(), "-ffp-contract=off".into(), "-fno-fast-math".into()]
    };
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

/// A target of the manifest, resolved and validated: its name, its
/// settings and the manifest's `[export]`.
#[derive(Debug, Clone)]
pub struct ResolvedTarget {
    pub name: String,
    pub settings: TargetSettings,
    pub export: ExportSettings,
}

/// `[export]` with its defaults applied (spec §14.2, §15.3).
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
    pub fn from_manifest(e: Option<&ManifestExport>) -> ExportSettings {
        let e = e.cloned().unwrap_or_default();
        ExportSettings { prefix: e.prefix.unwrap_or_else(|| "onsa_".into()), flows: e.flows, fns: e.fns }
    }
}

/// Find `[targets.<target>]` in `manifest` and validate it. `manifest_name`
/// names the manifest in the messages.
pub fn resolve_target(manifest: &Manifest, manifest_name: &str, target: &str) -> Result<ResolvedTarget, BuildError> {
    let Some(t) = manifest.targets.get(target) else {
        let mut names: Vec<&String> = manifest.targets.keys().collect();
        names.sort();
        return Err(BuildError::Usage(format!(
            "no target `{target}` in {manifest_name} (targets: {})",
            if names.is_empty() {
                "none".to_string()
            } else {
                names.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
            }
        )));
    };
    let settings = TargetSettings::from_manifest(target, t)?;
    Ok(ResolvedTarget {
        name: target.to_string(),
        settings,
        export: ExportSettings::from_manifest(manifest.export.as_ref()),
    })
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
    let Some(manifest) = &loaded.manifest else {
        return Err(BuildError::Usage("no onsa.toml: a build needs the manifest's targets".into()));
    };
    let resolved = resolve_target(manifest, "onsa.toml", target)?;
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
    let export = &resolved.export;
    let export_diags = check_exports(analyzed, export, settings);
    if !export_diags.is_empty() {
        return Err(diagnostics(LowerError::reported(export_diags)));
    }

    // Lower and emit.
    let lower_opts = LowerOptions { bulk_threshold: settings.bulk_threshold, ptr_size: settings.platform.ptr_size };
    let module = crate::lower_core_with(analyzed, &lower_opts).map_err(diagnostics)?;
    let module = consts_stage(module).map_err(|v| internal(v.into()))?;
    let sources = loaded.sources.clone();
    let emit_opts = EmitOptions {
        package: loaded.name.clone(),
        prefix: export.prefix.clone(),
        exports: export.flows.iter().map(|f| ExportFlow { flow: f.clone() }).collect(),
        export_fns: export.fns.clone(),
        panic: settings.panic,
        bulk_threshold: settings.bulk_threshold,
        provides_alloc: settings.provides_alloc,
        panic_messages: settings.panic_messages,
        locate: Some(Box::new(move |span: onsa_diag::Span| {
            let f = sources.file(span.file);
            (f.name().to_string(), f.line_col(span.start).line)
        })),
        ptr_size: settings.platform.ptr_size,
    };
    let unit = onsa_backend_c::emit(&module, &emit_opts).map_err(|d| diagnostics(LowerError::reported(d)))?;
    let mut files = vec![(onsa_backend_c::RUNTIME_HEADER_NAME.to_string(), unit.runtime_header.clone())];
    files.extend(unit.headers.iter().cloned());
    files.push((onsa_backend_c::CUnit::source_name(&loaded.name), unit.source.clone()));
    Ok(BuildOutput { module, settings: settings.clone(), export: export.clone(), unit, files })
}

/// Build the package at `path` (a directory or its `onsa.toml`) for `target`.
pub fn build(path: &Path, opts: &BuildOptions) -> Result<BuildReport, BuildError> {
    let manifest_path = if path.is_dir() { path.join("onsa.toml") } else { path.to_path_buf() };
    if !manifest_path.exists() {
        return Err(BuildError::Usage(format!("{}: no onsa.toml", manifest_path.display())));
    }
    // The order of the errors: the manifest, the target, the sources.
    let (manifest, root) = read_manifest(&manifest_path).map_err(BuildError::Usage)?;
    let resolved = resolve_target(&manifest, &manifest_path.display().to_string(), &opts.target)?;
    let files = read_sources(&root).map_err(BuildError::Usage)?;
    let input = PackageInput { manifest: Some(manifest), files, root: Some(root.clone()) };
    let mut loaded = Loaded::from_input(input);
    let analyzed = match crate::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(error) => return Err(BuildError::Internal { sources: loaded.sources, error: Box::new(error) }),
    };
    let output = build_resolved(&loaded, &analyzed, &resolved)?;
    let settings = &output.settings;

    // Write.
    let out_dir = opts.out.clone().unwrap_or_else(|| root.join("target").join(&opts.target));
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
    pub bulk_threshold: Option<u32>,
}

impl TargetSettings {
    pub fn from_manifest(name: &str, t: &ManifestTarget) -> Result<TargetSettings, BuildError> {
        let usage = |m: String| BuildError::Usage(format!("[targets.{name}]: {m}"));
        match t.kind.as_str() {
            "staticlib" => {}
            "source" => {
                if t.lang.as_deref().unwrap_or("c") != "c" {
                    return Err(usage(format!(
                        "lang = \"{}\": only `c` in this version (E0200)",
                        t.lang.clone().unwrap_or_default()
                    )));
                }
            }
            other => {
                return Err(usage(format!(
                    "kind = \"{other}\": only `staticlib` and `source` in this version (E0200)"
                )));
            }
        }
        let platform = platform(&t.platform).map_err(&usage)?;
        match t.numeric.as_deref().unwrap_or("strict") {
            "strict" | "strict-ftz" => {}
            "relaxed" => {
                return Err(usage(
                    "numeric = \"relaxed\" cannot be a target profile; use `@relaxed` per flow (spec §15.5)".into(),
                ));
            }
            other => return Err(usage(format!("unknown numeric profile `{other}`"))),
        }
        let panic = match t.panic.as_deref() {
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
            Some(other) => {
                return Err(usage(format!("unknown panic setting `{other}` (poison / trap / reset / halt)")));
            }
        };
        for e in &t.provides {
            if e != "Alloc" {
                return Err(usage(format!("provides `{e}`: only `Alloc` exists in this version (E0200)")));
            }
        }
        if !t.bind.is_empty() {
            return Err(usage("`bind` is not supported in this version (E0200)".into()));
        }
        Ok(TargetSettings {
            kind: t.kind.clone(),
            platform,
            panic,
            panic_messages: t.panic_messages.unwrap_or(true),
            provides_alloc: t.provides.iter().any(|e| e == "Alloc"),
            bulk_threshold: t.memory.as_ref().and_then(|m| m.bulk_threshold),
        })
    }
}

/// E0809 (exported `Ctl` inputs need `@param`, §11.7) and E0610 (exported
/// functions may use only provided effects, §14.2), plus unknown names.
fn check_exports(analyzed: &Analyzed, export: &ExportSettings, settings: &TargetSettings) -> Vec<Diagnostic> {
    let a = &analyzed.analysis;
    let mut out = Vec::new();
    let no_span = onsa_diag::Span::new(onsa_diag::FileId(0), 0, 0);
    for name in &export.flows {
        let found = a.defs.iter().enumerate().find(|(i, d)| {
            matches!(d.kind, DefKind::Flow(_)) && a.qualified_name(onsa_sema::DefId(*i as u32)) == *name
        });
        let Some((_, def)) = found else {
            out.push(Diagnostic::new(Code::E0302, no_span, format!("[export] flows: cannot find the flow `{name}`")));
            continue;
        };
        if def.vis != Vis::Pub {
            out.push(Diagnostic::new(Code::E0303, def.name_span, format!("the exported flow `{name}` must be `pub`")));
        }
        let Some(f) = def.as_flow() else { continue };
        for input in &f.inputs {
            if input.rate == Rate::Ctl && input.param.is_none() {
                out.push(
                    Diagnostic::new(
                        Code::E0809,
                        input.span,
                        format!(
                            "the exported flow `{name}` needs `@param` on its `Ctl` input `{}` (§11.7)",
                            input.name
                        ),
                    )
                    .with_fix(onsa_diag::Fix::InsertBefore {
                        insert_before: "@param(min: 0.0, max: 1.0, default: 0.0) ".into(),
                    }),
                );
            }
        }
    }
    for name in &export.fns {
        let found =
            a.defs.iter().enumerate().find(|(i, d)| {
                matches!(d.kind, DefKind::Fn(_)) && a.qualified_name(onsa_sema::DefId(*i as u32)) == *name
            });
        let Some((_, def)) = found else {
            out.push(Diagnostic::new(Code::E0302, no_span, format!("[export] fns: cannot find the function `{name}`")));
            continue;
        };
        if def.vis != Vis::Pub {
            out.push(Diagnostic::new(
                Code::E0303,
                def.name_span,
                format!("the exported function `{name}` must be `pub`"),
            ));
        }
        let Some(f) = def.as_fn() else { continue };
        if f.effects.alloc && !settings.provides_alloc {
            out.push(Diagnostic::new(
                Code::E0610,
                def.name_span,
                format!("the exported function `{name}` uses `Alloc`, which the target does not provide (§14.2)"),
            ));
        }
        for e in &f.effects.other {
            out.push(Diagnostic::new(
                Code::E0610,
                def.name_span,
                format!("the exported function `{name}` uses `{e}`, which the target does not provide (§14.2)"),
            ));
        }
    }
    out
}

/// The build-time `const` evaluation as a stage: [`inline_consts`], then the
/// verifier at its boundary (R-82).
fn consts_stage(mut module: Module) -> Result<Module, VerifyFailure> {
    inline_consts(&mut module);
    crate::verify_core(&module, CoreStage::Consts)?;
    Ok(module)
}

/// `const` initializers that call functions are evaluated with the
/// interpreter at build time (spec §6.6, T3-9) and replaced by literals so
/// the C backend can emit a static initializer. Only through [`consts_stage`].
fn inline_consts(module: &mut Module) {
    let mut replacements: Vec<(usize, Expr)> = Vec::new();
    {
        let interp = Interp::new(module);
        for (i, c) in module.consts.iter().enumerate() {
            if is_static_init(&c.init) {
                continue;
            }
            // A panic names this `const` (S-67).
            let _scope = onsa_diag::internal::item_scope(c.init.span);
            if let Ok(v) = interp.const_value(ConstId(i as u32))
                && let Some(e) = value_to_expr(module, &v, &c.ty, c.init.span)
            {
                replacements.push((i, e));
            }
        }
    }
    for (i, e) in replacements {
        module.consts[i].init = e;
    }
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
        let t = ManifestTarget { kind: "staticlib".into(), platform: "host".into(), ..Default::default() };
        let s = TargetSettings::from_manifest("t", &t).unwrap();
        assert_eq!(s.panic, PanicMode::Poison);
        assert!(!s.provides_alloc);
        let t =
            ManifestTarget { kind: "staticlib".into(), platform: "thumbv7em-none-eabihf".into(), ..Default::default() };
        assert_eq!(TargetSettings::from_manifest("t", &t).unwrap().panic, PanicMode::Reset);
        let t = ManifestTarget { kind: "clap".into(), platform: "host".into(), ..Default::default() };
        assert!(matches!(TargetSettings::from_manifest("t", &t), Err(BuildError::Usage(_))));
        let t = ManifestTarget {
            kind: "staticlib".into(),
            platform: "host".into(),
            numeric: Some("relaxed".into()),
            ..Default::default()
        };
        assert!(matches!(TargetSettings::from_manifest("t", &t), Err(BuildError::Usage(_))));
    }
}
