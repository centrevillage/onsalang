//! The names stage (spec §15.1): the module tree of every package, the
//! prelude, the defs and scopes of the items, and the imports. The
//! signatures are lowered after it (`crate::sig`).
//!
//! The parts are in a module each: `collect` (the tree and the items),
//! `prelude` (the names in scope everywhere) and `imports` (each `use`).

mod collect;
mod imports;
mod prelude;

use crate::def::ModId;
use crate::sig::Sema;

/// The names stage, in its order: the tree, the prelude, the items, the
/// cycles of the imports, then each `use`. A `use` reads the tables of the
/// first three, never another `use` (§15.1), so the modules are resolved in
/// any order.
pub(crate) fn collect_names(s: &mut Sema<'_>) {
    s.build_module_tree();
    prelude::build(&mut s.a);
    s.collect_items();
    let (cycles, _) = s.a.modules.check_cycles();
    s.a.diagnostics.extend(cycles);
    for m in 0..s.a.modules.mods.len() {
        s.resolve_imports(ModId(m as u32));
    }
}
