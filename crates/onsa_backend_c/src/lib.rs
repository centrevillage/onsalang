//! C11 backend (M4: T4-1 `onsa.h`, T4-2 Core → C, T4-3 flow API and export
//! wrappers). Pure: it turns a [`onsa_core::Module`] into strings, so it
//! builds for `wasm32` and the driver does the file I/O and compiling (T4-5).
//!
//! Shape of the output (docs/implementation-tasks.md §1 D-10):
//!
//! - one translation unit per package; every internal function is
//!   `static inline` and named by its qualified name with `.` → `__`
//!   (`dsp__voice__tick`), monomorphized names keep their `__`;
//! - `[T; N]` becomes `typedef struct { T a[N]; } onsa_arr_<T>_<N>` so arrays
//!   are values; tuples and enums become structs (enums: a tag and a union);
//! - a function returning an aggregate takes an output pointer first
//!   (`sret`, spec §12.7); borrowed aggregates are `const T*`, `inout` is
//!   `T*`, scalars go by value;
//! - every `F32` operation is wrapped in `(float)` and the file starts with
//!   `#pragma STDC FP_CONTRACT OFF` (through `onsa.h`), spec §13.4;
//! - only what is reachable from the exported flows and functions is
//!   emitted; `render` and tests never reach C (they need `Buf`, D-08).

mod emit;
mod export;
mod names;
mod reach;

use onsa_core::Module;
use onsa_diag::{Code, Diagnostic, FileId, Span};

/// The runtime header every generated file includes (T4-1).
pub const RUNTIME_HEADER: &str = include_str!("../../../runtime/c/onsa.h");

/// Target `panic` setting (spec §9.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PanicMode {
    /// `setjmp` / `longjmp` in the export wrappers; rt panics poison the instance (T4-4).
    Poison,
    /// Trap instruction (the default of this backend when nothing is chosen).
    #[default]
    Trap,
    /// Call the firmware's reset hook.
    Reset,
    /// Spin forever.
    Halt,
}

impl PanicMode {
    pub fn define(self) -> &'static str {
        match self {
            PanicMode::Poison => "ONSA_PANIC_POISON",
            PanicMode::Trap => "ONSA_PANIC_TRAP",
            PanicMode::Reset => "ONSA_PANIC_RESET",
            PanicMode::Halt => "ONSA_PANIC_HALT",
        }
    }
}

/// A flow to export (manifest `[export] flows`, spec §15.3), by qualified name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportFlow {
    pub flow: String,
}

/// Source positions for panic messages, when the caller can map spans.
pub type Locator = Box<dyn Fn(Span) -> (String, u32)>;

/// What to emit and how (manifest `[export]` and the target, spec §15.3).
pub struct EmitOptions {
    pub package: String,
    /// C symbol prefix of the exports (`onsa_`).
    pub prefix: String,
    pub exports: Vec<ExportFlow>,
    /// Exported plain functions, by qualified name.
    pub export_fns: Vec<String>,
    pub panic: PanicMode,
    /// `memory.bulk_threshold` of the target (spec §12.4); `None` = all fast.
    pub bulk_threshold: Option<u32>,
    /// The target provides `Alloc`: emit `_new` / `_free`.
    pub provides_alloc: bool,
    /// `panic_messages = false` strips the message strings (spec §9.2).
    pub panic_messages: bool,
    /// Maps a span to `(file, line)` for panic locations; absent → `("", 0)`.
    pub locate: Option<Locator>,
    /// Pointer width of the target in bytes (the bulk slot, spans in states), T4-5.
    pub ptr_size: u32,
}

impl Default for EmitOptions {
    fn default() -> Self {
        EmitOptions {
            package: "onsa".into(),
            prefix: "onsa_".into(),
            exports: Vec::new(),
            export_fns: Vec::new(),
            panic: PanicMode::Trap,
            bulk_threshold: None,
            provides_alloc: false,
            panic_messages: true,
            locate: None,
            ptr_size: onsa_core::layout::PTR_SIZE,
        }
    }
}

impl std::fmt::Debug for EmitOptions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EmitOptions")
            .field("package", &self.package)
            .field("prefix", &self.prefix)
            .field("exports", &self.exports)
            .field("export_fns", &self.export_fns)
            .field("panic", &self.panic)
            .field("bulk_threshold", &self.bulk_threshold)
            .field("provides_alloc", &self.provides_alloc)
            .field("panic_messages", &self.panic_messages)
            .field("ptr_size", &self.ptr_size)
            .finish()
    }
}

/// The generated files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CUnit {
    /// `onsa_<package>.c`
    pub source: String,
    /// `(file name, contents)` — one `onsa_<flow>.h` per exported flow.
    pub headers: Vec<(String, String)>,
    /// `onsa.h`
    pub runtime_header: String,
    /// The C API of each exported flow, as the backend named it.
    pub flows: Vec<FlowApi>,
}

/// The names of an exported flow's C API (spec §11.6, §14.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlowApi {
    /// Qualified flow name (`voice.voice`).
    pub flow: String,
    /// The prefix of every name of the API (`onsa_voice`: `onsa_voice_init`, `onsa_voice_params`).
    pub symbol: String,
    /// The prefix of its macros (`ONSA_VOICE`: `ONSA_VOICE_SIZE`).
    pub upper: String,
    /// Its header (`onsa_voice.h`).
    pub header: String,
}

impl CUnit {
    pub fn source_name(package: &str) -> String {
        format!("onsa_{}.c", names::ident(package))
    }
}

pub(crate) fn unsupported(span: Span, what: &str) -> Diagnostic {
    Diagnostic::new(Code::E0200, span, format!("the C backend does not support {what} in this version"))
}

pub(crate) fn no_span() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// Emit the C translation unit and headers for `module`.
pub fn emit(module: &Module, opts: &EmitOptions) -> Result<CUnit, Vec<Diagnostic>> {
    emit::emit_unit(module, opts)
}

#[cfg(test)]
mod tests;
