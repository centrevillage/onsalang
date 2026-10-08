//! C11 backend (M4: T4-1 `onsa.h`, T4-2 Core → C, T4-3 flow API and export
//! wrappers; W2-09: the public and the internal runtime header, the flags). Pure: it turns a [`onsa_core::Module`] into strings, so it
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
//! - the `.c` starts with a comment of the flags it needs and includes the
//!   internal header `onsa__runtime.h`, which checks the flags (`#error`) and
//!   turns contraction off for the compilers that know the STDC pragma; the
//!   headers of a host read the public `onsa.h` alone (spec §13.4, §14.2,
//!   S-53, S-54);
//! - every `F32` operation is wrapped in `(float)`; a `@fp(relaxed)` function
//!   is relaxed by the runtime's marks (`ONSA_FP_RELAXED_FN`,
//!   `ONSA_FP_RELAXED_BODY`), spec §15.5, S-287;
//! - only what is reachable from the exported flows and functions is
//!   emitted; `render` and tests never reach C (they need `Buf`, D-08).

mod emit;
mod export;
mod names;

use onsa_core::Module;
use onsa_diag::unsupported::Feature;
use onsa_diag::{Diagnostic, FileId, Span, Stage};

/// The public runtime header (spec §14.2, S-53): the types and the ABI
/// version a host reads through the header of a package. The same text for
/// every package and target.
pub const PUBLIC_HEADER: &str = include_str!("../../../runtime/c/onsa.h");
/// Its file name, as the headers of the packages include it.
pub const RUNTIME_HEADER_NAME: &str = "onsa.h";

/// The source of the internal runtime header that only the generated `.c`
/// includes (T4-1, S-53): [`internal_header`] writes the constants of
/// `onsa_core` into it.
const INTERNAL_HEADER_SOURCE: &str = include_str!("../../../runtime/c/onsa__runtime.h");
/// Its file name, as the generated `.c` includes it.
pub const INTERNAL_HEADER_NAME: &str = "onsa__runtime.h";
/// The line of [`INTERNAL_HEADER_SOURCE`] that [`internal_header`] replaces.
const CONSTANTS_MARKER: &str = "/* @onsa-core-constants@ */";

/// How many times `needle` occurs in `hay` (for the check of the marker at
/// compile time).
const fn occurrences(hay: &str, needle: &str) -> usize {
    let (h, n) = (hay.as_bytes(), needle.as_bytes());
    let mut count = 0;
    let mut i = 0;
    while i + n.len() <= h.len() {
        let mut j = 0;
        while j < n.len() && h[i + j] == n[j] {
            j += 1;
        }
        if j == n.len() {
            count += 1;
            i += n.len();
        } else {
            i += 1;
        }
    }
    count
}

// The marker is in the internal header exactly once: the build of the
// compiler stops otherwise, so a header without the constants is never written.
const _: () = assert!(occurrences(INTERNAL_HEADER_SOURCE, CONSTANTS_MARKER) == 1);
const _: () = assert!(occurrences(PUBLIC_HEADER, CONSTANTS_MARKER) == 0);

/// The internal runtime header, `onsa__runtime.h`, as the backend writes it:
/// its source with the values the backends share written from `onsa_core`
/// (plan D-15), so the C and the interpreter read one definition.
pub fn internal_header() -> String {
    use onsa_core::prim::{NAN_BITS_F32, NAN_BITS_F64};
    let constants = format!(
        "/* to_bits() of a NaN (spec §3.4, S-106): onsa_core::prim::NAN_BITS_F32 / _F64 */\n\
         #define ONSA_NAN_BITS_F32 UINT32_C({NAN_BITS_F32:#010X})\n\
         #define ONSA_NAN_BITS_F64 UINT64_C({NAN_BITS_F64:#018X})"
    );
    INTERNAL_HEADER_SOURCE.replacen(CONSTANTS_MARKER, &constants, 1)
}

/// The compiler flags the generated C needs (spec §13.4) from a compiler
/// like GCC or Clang, and from MSVC: what `onsa build` passes for a target
/// (with the flags of its architecture and the optimization level) and what
/// the first comment of the generated `.c` lists.
pub const FP_CFLAGS: &[&str] = &["-std=c11", "-ffp-contract=off", "-fno-fast-math"];
pub const FP_CFLAGS_MSVC: &[&str] = &["/std:c11", "/fp:strict"];

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
    /// The compiler flags of the target (spec §13.4), for the first comment
    /// of the `.c`; [`FP_CFLAGS`] when nothing is chosen.
    pub cflags: Vec<String>,
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
            cflags: FP_CFLAGS.iter().map(|f| f.to_string()).collect(),
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
            .field("cflags", &self.cflags)
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
    /// `onsa.h`: the public runtime header ([`PUBLIC_HEADER`]), the one a host
    /// reads (not the runtime of the generated code, which is `internal_header`).
    pub runtime_header: String,
    /// `onsa__runtime.h`, the internal runtime header ([`internal_header`]).
    pub internal_header: String,
    /// The C API of each exported flow, as the backend named it.
    pub flows: Vec<FlowApi>,
    /// The C API of each exported function (`[export] fns`), as the backend named it.
    pub fns: Vec<FnApi>,
    /// `<prefix>take_panic`: how an exported function reports a panic in this
    /// version (`panic = "poison"` only; spec §14.2 replaces it by the status, W10-03).
    pub take_panic: Option<String>,
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
    /// The `Init` inputs `<symbol>_init` takes after `s` and `bulk`, by value
    /// and in order (this version; spec §14.2 passes a `const <p>_config*`, W10-02).
    pub init_args: Vec<ApiField>,
    /// The fields of `<symbol>_params`, in order.
    pub params_fields: Vec<ApiField>,
    /// The `sample` inputs and outputs `<symbol>_process` takes after `s` and
    /// `params`, in order (this version: one argument each; spec §11.6 groups
    /// two or more in `In` / `Out`, W10-03).
    pub process_args: Vec<IoArg>,
}

/// A scalar value of the API: a field of a struct or an argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiField {
    /// The Onsa name (an input of the flow, a parameter of the function).
    pub name: String,
    /// Its C identifier.
    pub c_name: String,
    /// Its C type (`float`, `int32_t`).
    pub c_type: String,
}

/// A `Span` argument of `<p>_process`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IoArg {
    /// The Onsa name: the `sample` input, or the output (`out`, or a field of a struct output).
    pub name: String,
    /// The C parameter name.
    pub c_name: String,
    /// The C type of an element.
    pub c_type: String,
    /// `Some(n)`: `[Span[T]; n]`, an array of `n` channel pointers (`T* const*`).
    pub planar: Option<u32>,
    pub output: bool,
}

/// The C API of an exported function (spec §14.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnApi {
    /// Qualified name (`util.version`).
    pub fn_: String,
    /// Its C name (`vc_version`).
    pub symbol: String,
    /// The header that declares it (`vc_util.h`).
    pub header: String,
    /// The parameters, in order.
    pub params: Vec<FnParam>,
    /// The C type of the returned value; `None` for a function without one.
    pub ret: Option<String>,
}

/// A parameter of an exported function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnParam {
    pub field: ApiField,
    pub kind: FnParamKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnParamKind {
    /// A scalar by value.
    Scalar,
    /// An `inout` scalar: `T*`.
    InoutScalar,
    /// A `Span` of scalars: `const T* name, uint32_t name_len` (`T*` when `inout`).
    Span { inout: bool },
}

impl CUnit {
    pub fn source_name(package: &str) -> String {
        format!("onsa_{}.c", names::ident(package))
    }

    /// The headers a host includes (spec §14.2), as `(file name, text)`: the
    /// runtime header and one per export. The internal header (S-53) is not
    /// one of them.
    pub fn public_headers(&self) -> Vec<(&str, &str)> {
        let mut v = vec![(RUNTIME_HEADER_NAME, self.runtime_header.as_str())];
        v.extend(self.headers.iter().map(|(n, t)| (n.as_str(), t.as_str())));
        v
    }

    /// Every file of the unit, as `(file name, text)`, in the order a build
    /// writes them: the public headers, the internal header, the `.c` last
    /// (spec §14.2: `kind = "source"` writes the internal header too).
    pub fn files(&self, package: &str) -> Vec<(String, String)> {
        let mut v = vec![
            (RUNTIME_HEADER_NAME.to_string(), self.runtime_header.clone()),
            (INTERNAL_HEADER_NAME.to_string(), self.internal_header.clone()),
        ];
        v.extend(self.headers.iter().cloned());
        v.push((Self::source_name(package), self.source.clone()));
        v
    }
}

/// The C spelling of a scalar type at the API boundary (`float`, `int32_t`,
/// `bool`), as the headers write it; `None` for a type that is not a scalar.
/// For the tools that drive the API (the conformance harness).
pub fn scalar_c(ty: &onsa_core::Ty) -> Option<&'static str> {
    names::scalar_c(ty)
}

/// The C identifier of an Onsa name (a field of `<flow>_params`), as the
/// headers write it.
pub fn c_ident(name: &str) -> String {
    names::ident(name)
}

/// E0200 for `feature` (S-224), with the details its phrase takes.
pub(crate) fn unsupported(span: Span, feature: Feature, details: &[&str]) -> Diagnostic {
    feature.diagnostic(Stage::Build, span, details)
}

pub(crate) fn no_span() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// Emit the C translation unit and headers for `module`: what
/// [`export_roots`] reach ([`onsa_core::reach`]).
pub fn emit(module: &Module, opts: &EmitOptions) -> Result<CUnit, Vec<Diagnostic>> {
    emit::emit_unit(module, opts)
}

/// The entries of the unit that `opts` exports (spec §15.2): the roots of
/// the reach of [`emit`], and of the build-time evaluation of the `const`s
/// before it (S-242).
pub fn export_roots(module: &Module, opts: &EmitOptions) -> Vec<onsa_core::FnId> {
    emit::export_roots(module, opts)
}

#[cfg(test)]
mod tests;
