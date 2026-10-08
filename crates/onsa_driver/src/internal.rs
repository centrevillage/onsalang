//! The internal error of S-67 (Q-06): every failure of the compiler itself
//! ends here, in one form, whatever the command.
//!
//! - A panic anywhere in a stage, caught by [`guard`] (every public stage
//!   function of the driver runs its body in it, so no caller can skip it).
//! - A stage's own report of a broken invariant ([`onsa_diag::internal::bug`]).
//! - A lowering failure that is not an unsupported feature (`internal(...)`
//!   in `onsa_core::lower`).
//! - The Core verifier rejecting the output of a stage ([`VerifyFailure`], R-82).
//! - The C compiler rejecting the C the compiler generated.
//!
//! The command stops; the exit code is 101 and there is no diagnostic code
//! (spec §18.1, §18.2): the repair loop must not try to fix the program.

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::panic::{AssertUnwindSafe, PanicHookInfo};
use std::sync::Once;

use onsa_diag::internal::InternalBug;
use onsa_diag::{SourceMap, Span};

use crate::VerifyFailure;

/// Where an internal error comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// A panic in a stage (an indexing out of range, an `unwrap`, a
    /// [`onsa_diag::internal::bug`]). `location` is where in the compiler.
    Panic { location: Option<String> },
    /// Lowering reached a state it cannot be in (`internal(...)`).
    Lowering,
    /// The Core verifier rejected the output of a stage (R-82).
    Verify(VerifyFailure),
    /// The C compiler rejected the generated C.
    GeneratedC,
}

/// An internal error (S-67): a bug of the compiler, exit code 101.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InternalError {
    pub origin: Origin,
    /// The position: the source the stage was at, or the item it worked on.
    pub span: Option<Span>,
    pub message: String,
}

impl InternalError {
    pub fn lowering(span: Span, message: String) -> InternalError {
        InternalError { origin: Origin::Lowering, span: Some(span), message }
    }

    pub fn generated_c(message: String) -> InternalError {
        InternalError { origin: Origin::GeneratedC, span: None, message }
    }

    /// The text form, on standard error (S-67). An internal error has no JSON
    /// form (spec §18.2, S-182): with `--json` the commands print nothing on
    /// standard output and this text on standard error, exit 101.
    pub fn render(&self, sources: &SourceMap) -> String {
        let mut out = String::new();
        match &self.origin {
            // The verifier's report names the stage, the item and its Core.
            Origin::Verify(v) => out.push_str(&v.report()),
            _ => out.push_str(&format!("internal error: {}", self.message)),
        }
        out.push('\n');
        if let Some(at) = self.span.and_then(|s| position(sources, s)) {
            let _ = writeln!(out, "  --> {at}");
        }
        if let Origin::Panic { location: Some(l) } = &self.origin {
            let _ = writeln!(out, "  = at {l}");
        }
        out.push_str("  = note: this is a bug in the compiler, not in the program\n");
        if self.origin == Origin::GeneratedC {
            // The C toolchain is outside the compiler.
            out.push_str("  = note: when the C toolchain itself is broken, this may not be a bug in the compiler\n");
        }
        out
    }
}

impl From<VerifyFailure> for InternalError {
    fn from(v: VerifyFailure) -> Self {
        InternalError { message: v.to_string(), origin: Origin::Verify(v), span: None }
    }
}

/// `file:line:col` of `span`, when `sources` holds its file.
fn position(sources: &SourceMap, span: Span) -> Option<String> {
    if span.file.0 as usize >= sources.len() {
        return None;
    }
    let file = sources.file(span.file);
    let text = file.text();
    let mut at = (span.start as usize).min(text.len());
    // The span of a broken stage may cut a character; render the start of it.
    while !text.is_char_boundary(at) {
        at -= 1;
    }
    let lc = file.line_col(at as u32);
    Some(format!("{}:{}:{}", file.name(), lc.line, lc.col))
}

/// What the panic hook saw inside a guard.
struct Caught {
    message: String,
    location: Option<String>,
    item: Option<Span>,
}

thread_local! {
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    static CAUGHT: RefCell<Option<Caught>> = const { RefCell::new(None) };
}

static HOOK: Once = Once::new();

/// Install the panic hook once per process: inside a guard it records the
/// panic instead of printing it; elsewhere the previous hook runs.
fn install_hook() {
    HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info: &PanicHookInfo<'_>| {
            if DEPTH.with(Cell::get) == 0 {
                previous(info);
                return;
            }
            let caught = Caught {
                message: payload_message(info.payload()),
                location: info.location().map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column())),
                item: onsa_diag::internal::current_item(),
            };
            CAUGHT.with(|c| *c.borrow_mut() = Some(caught));
        }));
    });
}

fn payload_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(b) = payload.downcast_ref::<InternalBug>() {
        b.message.clone()
    } else if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "a panic without a message".into()
    }
}

/// Run `f`; a panic in it becomes the internal error of S-67. The position
/// is the source an [`InternalBug`] names, else the item the stage marked
/// with [`onsa_diag::internal::item_scope`].
pub fn guard<T>(f: impl FnOnce() -> T) -> Result<T, InternalError> {
    install_hook();
    DEPTH.with(|d| d.set(d.get() + 1));
    let result = std::panic::catch_unwind(AssertUnwindSafe(f));
    DEPTH.with(|d| d.set(d.get() - 1));
    result.map_err(|payload| {
        let caught = CAUGHT.with(|c| c.borrow_mut().take());
        let bug_span = payload.downcast_ref::<InternalBug>().and_then(|b| b.span);
        match caught {
            Some(c) => InternalError {
                origin: Origin::Panic { location: c.location },
                span: bug_span.or(c.item),
                message: c.message,
            },
            None => InternalError {
                origin: Origin::Panic { location: None },
                span: bug_span,
                message: payload_message(payload.as_ref()),
            },
        }
    })
}

/// [`guard`] on a thread with the stack of a command
/// ([`onsa_diag::stack::run`]): the current thread when it is one, else a new
/// one. Every run of the interpreter goes through it (R-05).
pub fn guard_on_stack<T: Send>(f: impl FnOnce() -> T + Send) -> Result<T, InternalError> {
    onsa_diag::stack::run(|| guard(f))
}

#[cfg(test)]
mod tests {
    use super::*;
    use onsa_diag::FileId;

    /// P-2: from a thread that is not a command's, `guard_on_stack` guards
    /// on the new thread and keeps the position of the panic; a guard around
    /// `onsa_diag::stack::run` does not see it (the hook ran on the other
    /// thread).
    #[test]
    fn guard_on_stack_keeps_the_position_from_another_thread() {
        assert!(!onsa_diag::stack::is_command_thread());
        let e = guard_on_stack(|| -> u32 { onsa_diag::internal::bug(None, "inside") }).unwrap_err();
        assert!(matches!(e.origin, Origin::Panic { location: Some(_) }), "{:?}", e.origin);
        let e = guard(|| onsa_diag::stack::run(|| -> u32 { onsa_diag::internal::bug(None, "outside") })).unwrap_err();
        assert_eq!(e.message, "outside");
        assert_eq!(e.origin, Origin::Panic { location: None });
    }

    #[test]
    fn guard_on_stack_runs_on_a_command_thread() {
        assert_eq!(guard_on_stack(onsa_diag::stack::is_command_thread), Ok(true));
        let e = guard_on_stack(|| -> u32 { onsa_diag::internal::bug(None, "on the stack") }).unwrap_err();
        assert_eq!(e.message, "on the stack");
    }

    fn sources() -> SourceMap {
        let mut s = SourceMap::default();
        s.add("m.onsa", "fn f() {}\nfn g() {}\n");
        s
    }

    #[test]
    fn a_panic_names_the_item_and_the_compiler_location() {
        let item = Span::new(FileId(0), 10, 19);
        let e = guard(|| {
            let _scope = onsa_diag::internal::item_scope(item);
            let v: Vec<u32> = Vec::new();
            v[3]
        })
        .unwrap_err();
        assert_eq!(e.span, Some(item));
        assert!(e.message.contains("index out of bounds"), "{e:?}");
        let Origin::Panic { location: Some(l) } = &e.origin else { panic!("{e:?}") };
        assert!(l.contains("internal.rs"), "{l}");
        let text = e.render(&sources());
        assert!(text.starts_with("internal error: index out of bounds"), "{text}");
        assert!(text.contains("  --> m.onsa:2:1\n"), "{text}");
        assert!(text.contains("not in the program"), "{text}");
        // the scope ended with the unwinding
        assert_eq!(onsa_diag::internal::current_item(), None);
    }

    #[test]
    fn a_bug_names_its_own_source() {
        let at = Span::new(FileId(0), 3, 4);
        let e = guard(|| {
            let _scope = onsa_diag::internal::item_scope(Span::new(FileId(0), 0, 9));
            onsa_diag::internal::bug(Some(at), "a field of a non-record")
        })
        .unwrap_err();
        assert_eq!(e.span, Some(at));
        assert_eq!(e.message, "a field of a non-record");
        assert!(e.render(&sources()).contains("  --> m.onsa:1:4\n"));
    }

    #[test]
    fn generated_c_names_the_toolchain() {
        let e = InternalError::generated_c("the C compiler rejected the generated C (`cc` exited with 1)".into());
        let text = e.render(&sources());
        assert!(text.contains("`cc` exited with 1"), "{text}");
        assert!(text.contains("the C toolchain itself is broken"), "{text}");
    }

    #[test]
    fn nested_guards_and_values() {
        assert_eq!(guard(|| 7), Ok(7));
        let inner = guard(|| guard(|| panic!("inner")).map_err(|e| e.message)).unwrap();
        assert_eq!(inner, Err("inner".to_string()));
        // without a scope or a source, no position
        let e = guard(|| panic!("free")).unwrap_err();
        assert_eq!(e.span, None);
        assert!(!e.render(&sources()).contains("-->"));
    }

    #[test]
    fn a_span_inside_a_character_renders_its_start() {
        let mut s = SourceMap::default();
        s.add("u.onsa", "let a = \"音\"\n");
        let e = InternalError::lowering(Span::new(FileId(0), 10, 11), "x".into());
        assert!(e.render(&s).contains("  --> u.onsa:1:10\n"), "{}", e.render(&s));
        // a span of a file the map does not hold has no position
        let e = InternalError::lowering(Span::new(FileId(5), 0, 0), "x".into());
        assert!(!e.render(&s).contains("-->"));
    }
}
