//! The names of the bounds of Onsa that are no trait (§4.5, §4.6): the
//! one place that knows them, for the prelude and the checks that read them
//! (`onsa_sema`) and the table of the forms of other languages
//! ([`crate::foreign`]).

/// The kind constraint `Copy` (§4.6): written in bounds, never derived.
pub const COPY: &str = "Copy";
/// The kind constraint `Dup` (§4.6).
pub const DUP: &str = "Dup";
/// The implicit requirement `Escape` of a type parameter (§4.5): a name of
/// the prelude (§15.1), no kind constraint.
pub const ESCAPE: &str = "Escape";

/// The kind constraints (§4.6): the names a bound takes that are no trait, so
/// that the head of a declaration does not take them (`copy_bound` of
/// [`crate::foreign`]) and the candidate of a derive leaves them out (S-463).
/// The one list.
pub const KIND_CONSTRAINTS: [&str; 2] = [COPY, DUP];
