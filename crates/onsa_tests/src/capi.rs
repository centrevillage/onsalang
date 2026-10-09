//! How a driver program calls the C API of this version (spec §11.6,
//! §14.2): the one place the tools that drive the generated C (the
//! conformance harness, [`crate::conformance`]; the host steps,
//! [`crate::host`]) learn the form of each call (K-14).
//!
//! The names come from what the C backend recorded ([`FlowApi`], [`FnApi`],
//! plan D-15); this module only knows how this version passes them. When the
//! API changes (W10-02: `init` takes a `const <p>_config*`; W10-03: `In` /
//! `Out`, the status of an exported function, NULL `bulk` / `cfg`), this
//! module is what changes: the steps of the cases and the comparisons do not.
//!
//! This version:
//!
//! ```text
//! int  <p>_init(<p>* s, void* bulk, <the Init inputs by value>, float sample_rate);
//! void <p>_reset(<p>* s);
//! int  <p>_process(<p>* s, const <p>_params* p, <a pointer per input>, <a pointer per output>, uint32_t frames);
//! T    <f>(<args>);   int <prefix>take_panic(void);   /* panic = "poison" */
//! ```

use onsa_backend_c::{ApiField, FlowApi, FnApi, FnParamKind, IoArg};

/// The `init` inputs of an `init` call.
pub enum Cfg<'a> {
    /// The C expression of each input ([`FlowApi::init_args`]).
    Values(&'a dyn Fn(&ApiField) -> String),
    /// A NULL `cfg` (spec §14.2).
    Null,
}

/// What this version of the API cannot express: a failure of the run that
/// waits for the work that changes the API (not an error of the case).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub String);

/// The declarations of the state's storage: `mem` (`<P>_SIZE` bytes aligned
/// to `<P>_ALIGN`) and `bulk` (`<P>_BULK_SIZE` bytes, one more so that the
/// array is never empty; aligned to 16, as this version's header has no
/// `<P>_BULK_ALIGN`).
pub fn storage(api: &FlowApi, mem: &str, bulk: &str) -> String {
    let up = &api.upper;
    format!(
        "static _Alignas({up}_ALIGN) unsigned char {mem}[{up}_SIZE];\n\
         static _Alignas(16) unsigned char {bulk}[{up}_BULK_SIZE + 1];\n"
    )
}

/// The C type of `sample_rate` (`init` takes an `F32`, spec §11.6).
pub const SAMPLE_RATE_C: &str = "float";

/// The C type of the state.
pub fn state_type(api: &FlowApi) -> String {
    api.symbol.clone()
}

/// The C type of the `block` inputs.
pub fn params_type(api: &FlowApi) -> String {
    format!("{}_params", api.symbol)
}

/// The expression of an `init` call (its status, an `int`).
pub fn init(api: &FlowApi, s: &str, bulk: &str, cfg: Cfg<'_>, sample_rate: &str) -> Result<String, Unsupported> {
    let mut args = vec![s.to_string(), bulk.to_string()];
    match cfg {
        Cfg::Values(value) => args.extend(api.init_args.iter().map(value)),
        Cfg::Null => {
            return Err(Unsupported(
                "this version's `init` takes the `init` inputs by value: there is no `cfg` pointer to pass NULL \
                 (W10-02, W10-03)"
                    .into(),
            ));
        }
    }
    args.push(sample_rate.to_string());
    Ok(format!("{}_init({})", api.symbol, args.join(", ")))
}

/// The statement of a `reset` call (spec §14.2: `void`, S-198).
pub fn reset(api: &FlowApi, s: &str) -> String {
    format!("{}_reset({s});", api.symbol)
}

/// The expression of a `process` call (its status, an `int`). `io` gives the
/// C expression of each `sample` input and output ([`FlowApi::process_args`]):
/// a pointer (`const T*` / `T*`), an array of channel pointers for `[Span[T]; N]`,
/// or `NULL`.
pub fn process(api: &FlowApi, s: &str, params: &str, io: &dyn Fn(&IoArg) -> String, frames: &str) -> String {
    let mut args = vec![s.to_string(), params.to_string()];
    args.extend(api.process_args.iter().map(io));
    args.push(frames.to_string());
    format!("{}_process({})", api.symbol, args.join(", "))
}

/// An argument of an exported function, as the caller holds it.
pub enum FnArg {
    /// A scalar: its C expression.
    Scalar(String),
    /// A span: the pointer and the length.
    Span(String, String),
}

/// The statements of a call of an exported function: the status into
/// `status` (an `int`), the result into `result` (when the function returns
/// one). This version reports a panic through `<prefix>take_panic()` (`None`
/// when the target's `panic` is not `"poison"`: a panicking call does not
/// return, so the status is 0, spec §14.2).
pub fn call_fn(
    api: &FnApi,
    take_panic: Option<&str>,
    args: &[FnArg],
    status: &str,
    result: Option<&str>,
) -> Result<String, Unsupported> {
    let mut c = Vec::new();
    for (p, a) in api.params.iter().zip(args) {
        match (p.kind, a) {
            (FnParamKind::Scalar, FnArg::Scalar(e)) => c.push(e.clone()),
            (FnParamKind::Span { .. }, FnArg::Span(ptr, len)) => {
                c.push(ptr.clone());
                c.push(len.clone());
            }
            (FnParamKind::InoutScalar, _) => {
                return Err(Unsupported(format!("the `inout` parameter `{}`", p.field.name)));
            }
            _ => return Err(Unsupported(format!("the parameter `{}` in this form", p.field.name))),
        }
    }
    let call = format!("{}({})", api.symbol, c.join(", "));
    let mut s = match (result, &api.ret) {
        (Some(r), Some(_)) => format!("{r} = {call};"),
        (None, None) => format!("{call};"),
        _ => return Err(Unsupported("a result that does not match the function's return type".into())),
    };
    match take_panic {
        Some(t) => s.push_str(&format!(" {status} = {t}();")),
        None => s.push_str(&format!(" {status} = 0;")),
    }
    Ok(s)
}
