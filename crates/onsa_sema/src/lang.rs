//! The lang items of std (S-71, R-79): the enums of `std.core` the compiler
//! knows, its one table of them. Their variants are in the prelude by their
//! names alone and not members of their types (§4.1, S-607), and `?` reads
//! them (§9.1). The sema stages read [`LangItems`]; lowering and the backends
//! read what the stages recorded.

use serde::{Deserialize, Serialize};

use crate::Analysis;
use crate::def::DefId;
use crate::resolve::Entity;
use crate::sig::Sema;

/// Of `std.core`: the enum, the variant `?` goes on with, the one it leaves with.
const ENUMS: [(&str, &str, &str); 2] = [("Option", "Some", "None"), ("Result", "Ok", "Err")];

/// The rows of [`ENUMS`], for what is said of one of them.
pub(crate) const OPTION: usize = 0;
pub(crate) const RESULT: usize = 1;

/// The representative of the type parameters with `Ordinal` (`traits::Rep`):
/// of `std.core`, with no `pub`, so that no program names it.
const ANY_ORDINAL: &str = "AnyOrdinal";

/// A row of [`ENUMS`] in the analysis: the enum and the indices of its variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LangEnum {
    pub def: DefId,
    pub keep: u32,
    pub exit: u32,
}

/// The rows of [`ENUMS`]: none with no `std.core` (unit tests of a package
/// with no std). Of std alone, which [`crate::analyze_on`] does not read again.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LangItems {
    enums: [Option<LangEnum>; ENUMS.len()],
    any_ordinal: Option<DefId>,
}

impl LangItems {
    /// The row of the enum `d`, if it is one of them.
    pub fn of(&self, d: DefId) -> Option<LangEnum> {
        self.enums.iter().flatten().find(|l| l.def == d).copied()
    }

    /// Whether `d` is the enum of the row `row`.
    pub(crate) fn is(&self, row: usize, d: DefId) -> bool {
        self.enums[row].is_some_and(|l| l.def == d)
    }

    /// The enum `Option`.
    pub(crate) fn option(&self) -> Option<DefId> {
        self.enums[OPTION].map(|l| l.def)
    }

    /// [`ANY_ORDINAL`].
    pub(crate) fn any_ordinal(&self) -> Option<DefId> {
        self.any_ordinal
    }
}

/// The variant of `Option` that holds a value, which a `narrow_from` of a
/// pair `as` converts always gives. Asked of what std declares, so with no
/// std a bug.
pub(crate) fn some(a: &Analysis) -> String {
    let some = a.modules.lang.enums[OPTION].and_then(|l| a.def(l.def).as_enum()?.variants.get(l.keep as usize));
    match some {
        Some(v) => v.name.clone(),
        None => onsa_diag::internal::bug(None, "`Option` is not declared"),
    }
}

/// Fills the rows from the `pub` items of `std.core` in the prelude, and puts
/// the variants of each enum there, by their names as written. The embedded
/// std has them all, so one missing is a bug.
pub(crate) fn declared(s: &mut Sema<'_>) {
    for (row, (ty, keep, exit)) in ENUMS.into_iter().enumerate() {
        let Some(&Entity::Def(def)) = s.a.prelude.get(ty) else {
            onsa_diag::internal::bug(None, format!("`std.core` declares no `{ty}`"))
        };
        let names: Vec<String> = s.variants(def).into_iter().map(|(name, _)| name).collect();
        let index = |name: &str| match names.iter().position(|n| n == name) {
            Some(i) => i as u32,
            None => onsa_diag::internal::bug(None, format!("`{ty}` declares no `{name}`")),
        };
        s.a.modules.lang.enums[row] = Some(LangEnum { def, keep: index(keep), exit: index(exit) });
        for (i, name) in names.into_iter().enumerate() {
            s.a.prelude.insert(name, Entity::Variant(def, i as u32));
        }
    }
    let Some(&any) = s.a.modules.core.and_then(|m| s.a.modules.get(m).items.get(ANY_ORDINAL)) else {
        onsa_diag::internal::bug(None, format!("`std.core` declares no `{ANY_ORDINAL}`"))
    };
    s.a.modules.lang.any_ordinal = Some(any);
}
