//! What the stages know when the compiler fails inside (S-67, Q-06).
//!
//! An internal error is a bug of the compiler, not of the program: the
//! command stops with exit code 101 and no diagnostic code (spec §18.1,
//! §18.2). The driver catches it (`onsa_driver::guard`). This module holds
//! the two things every stage can reach without depending on the driver:
//!
//! - [`item_scope`]: the item a stage is working on, so that a panic names
//!   the position of the item (S-67: "the position of the item and the
//!   internal message").
//! - [`bug`]: a stage reports a broken invariant of its own ([`InternalBug`]).

use std::cell::RefCell;

use crate::Span;

thread_local! {
    static ITEMS: RefCell<Vec<Span>> = const { RefCell::new(Vec::new()) };
}

/// The item being worked on, until the guard is dropped.
#[must_use = "the scope ends when the guard is dropped"]
pub struct ItemScope(());

impl Drop for ItemScope {
    fn drop(&mut self) {
        ITEMS.with(|s| {
            s.borrow_mut().pop();
        });
    }
}

/// Mark `span` as the item the current thread works on (a file while it is
/// parsed, a declaration while it is checked, lowered or emitted).
pub fn item_scope(span: Span) -> ItemScope {
    ITEMS.with(|s| s.borrow_mut().push(span));
    ItemScope(())
}

/// The innermost item of the current thread, if a stage named one.
pub fn current_item() -> Option<Span> {
    ITEMS.with(|s| s.borrow().last().copied())
}

/// A broken invariant a stage found itself (the panic payload of [`bug`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InternalBug {
    /// The source the stage was at, when it knows one.
    pub span: Option<Span>,
    pub message: String,
}

/// Stop with an internal error: the stage found a state it cannot be in.
/// The driver's guard turns it into the internal error of S-67.
pub fn bug(span: Option<Span>, message: impl Into<String>) -> ! {
    std::panic::panic_any(InternalBug { span, message: message.into() })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;

    #[test]
    fn scopes_nest_and_end() {
        assert_eq!(current_item(), None);
        let a = Span::new(FileId(0), 1, 2);
        let b = Span::new(FileId(0), 3, 4);
        let ga = item_scope(a);
        {
            let _gb = item_scope(b);
            assert_eq!(current_item(), Some(b));
        }
        assert_eq!(current_item(), Some(a));
        drop(ga);
        assert_eq!(current_item(), None);
    }
}
