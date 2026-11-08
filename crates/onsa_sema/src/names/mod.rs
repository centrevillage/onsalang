//! The names stage (spec §15.1): the module tree of every package, the
//! prelude, the defs and the tables of the items, and the imports. The
//! signatures are lowered after it (`crate::sig`).
//!
//! The parts are in a module each: `collect` (the tree and the items),
//! `prelude` (the names in scope everywhere), `imports` (each `use`),
//! `clash` (the E0304 of two names of one space, and of a binding),
//! `heading` (the E0304 of the names of a heading), `cycles` (the E0310 of
//! the dependencies of the `use`), `lookup` (the lookups of a path, for a
//! `use` and outside one), `typed` (the types an alias and `Self` stand
//! for in a path) and `rename` (the uses the candidate of an E0320 renames).
//! The names of the bodies are in `body`.

pub(crate) mod body;
mod clash;
pub(crate) mod collect;
mod cycles;
mod heading;
mod imports;
mod lookup;
mod prelude;
pub(crate) mod rename;
#[cfg(test)]
mod tests;
mod typed;

use crate::sig::Sema;

pub(crate) use clash::hides;
pub(crate) use cycles::{ImportGraph, cycle_diagnostic};
pub use cycles::{cyclic, file_key};
pub(crate) use heading::{param_clashes, param_name};
pub(crate) use typed::{BuiltinMember, PathEnd, builtin_member, builtin_ty, self_outside_impl};

/// The name of the receiver of a method (§2.2, §6.2): the binding its
/// heading and its body see.
pub(crate) const SELF_VALUE: &str = "self";

/// Whether `name` is `Self`, the type of the `impl` (§2.2): the one
/// comparison of the names stage and the signatures, each of which reads
/// what it stands for.
pub(crate) fn is_self_type(name: &str) -> bool {
    name == "Self"
}

/// The text after `use` of a `use` of `path` taking `names` (none: the path
/// alone), in the form fmt writes (§15.1, S-598): a list of one name is the
/// last element of the path, `a.b` for `a.{b}`.
pub(crate) fn use_form<S: AsRef<str>>(path: &[S], names: Option<&[&str]>) -> String {
    let list = match names {
        Some([one]) => Some(one.to_string()),
        Some(list) => Some(format!("{{{}}}", list.join(", "))),
        None => None,
    };
    path.iter().map(|s| s.as_ref()).chain(list.as_deref()).collect::<Vec<_>>().join(".")
}

/// The names stage, in its order: the tree, the prelude, the items (those
/// of `std.core` then in the prelude, S-659) and their clashes, each `use` and the clashes of their names, the cycles of
/// their dependencies, then the `use` whose head is no head (their
/// candidates read the graph). A `use` reads the tables of the tree, the
/// prelude and the items, never another `use` (§15.1), so the modules are
/// resolved in any order. The names of the clashes are errors where they
/// are used (§18.1, S-675), so they are known before what reads them. The
/// items a flow generates are made with it, and a `use` of one its signature
/// does not give fails once the signatures are lowered
/// ([`Sema::fail_ungenerated`], R-50).
pub(crate) fn collect_names(s: &mut Sema<'_>) {
    s.build_module_tree();
    // A continued analysis has std's prelude.
    let fresh = !s.a.continues();
    if fresh {
        prelude::build(s.a);
    }
    s.collect_items();
    if fresh {
        prelude::declared(s);
    }
    s.check_item_clashes();
    for m in s.a.new_mods() {
        s.resolve_imports(m);
    }
    s.check_use_clashes();
    s.check_cycles();
    s.report_use_heads();
}
