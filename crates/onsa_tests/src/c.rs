//! Shared helper for the C backend tests: source file → `CUnit`.

use std::path::Path;

use onsa_backend_c::{CUnit, EmitOptions, ExportFlow, PanicMode};

/// Lower `src` and emit C with every flow of the file exported.
pub fn emit_c(root: &Path, src: &str, bulk_threshold: Option<u32>, provides_alloc: bool) -> CUnit {
    emit_c_with(root, src, bulk_threshold, provides_alloc, PanicMode::Trap)
}

/// [`emit_c`] with a panic mode (T4-4).
pub fn emit_c_with(
    root: &Path,
    src: &str,
    bulk_threshold: Option<u32>,
    provides_alloc: bool,
    panic: PanicMode,
) -> CUnit {
    let path = root.join(src);
    let mut loaded = onsa_driver::load(std::slice::from_ref(&path)).unwrap_or_else(|e| panic!("{src}: {e}"));
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    assert!(
        analyzed.diagnostics.is_empty(),
        "{src}: check diagnostics:\n{}",
        onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics)
    );
    let lower_opts = onsa_core::LowerOptions { bulk_threshold, ..Default::default() };
    let module = match onsa_driver::lower_core_with(&analyzed, &lower_opts) {
        Ok(m) => m,
        Err(d) => panic!("{src}: lowering diagnostics:\n{}", onsa_diag::to_text(&loaded.sources, &d)),
    };
    let package = Path::new(src).file_stem().unwrap().to_string_lossy().into_owned();
    let sources = loaded.sources.clone();
    let opts = EmitOptions {
        package,
        exports: module.flows.iter().map(|f| ExportFlow { flow: f.name.clone() }).collect(),
        panic,
        bulk_threshold,
        provides_alloc,
        locate: Some(Box::new(move |span: onsa_diag::Span| {
            let f = sources.file(span.file);
            (f.name().rsplit('/').next().unwrap_or(f.name()).to_string(), f.line_col(span.start).line)
        })),
        ..Default::default()
    };
    match onsa_backend_c::emit(&module, &opts) {
        Ok(u) => u,
        Err(d) => panic!("{src}: C backend diagnostics:\n{}", onsa_diag::to_text(&loaded.sources, &d)),
    }
}

/// `onsa_voice.h` etc. joined into one golden file, and back.
pub fn join_headers(unit: &CUnit) -> String {
    let mut s = String::new();
    for (name, text) in &unit.headers {
        s.push_str(&format!("/* ==== {name} ==== */\n"));
        s.push_str(text);
    }
    s
}
