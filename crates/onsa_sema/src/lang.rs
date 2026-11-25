//! The lang items of std (S-71, R-79): the enums and the effect `Alloc` of
//! `std.core` (D-08), the struct of `std.text` and the effect of `std.random`
//! the compiler knows, its one table of them. The variants of the enums are in the prelude by their names
//! alone and not members of their types (§4.1, S-607), and `?` reads them
//! (§9.1). The sema stages read [`LangItems`]; lowering and the backends read
//! what the stages recorded.

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

/// Of `std.core`: the effect of the heap (D-08), the one effect of a row
/// phase 1 gives a meaning (`crate::sig::read_effects`).
const ALLOC: &str = "Alloc";

/// The representative of the type parameters with `Ordinal` (`traits::Rep`):
/// of `std.core`, with no `pub`, so that no program names it.
const ANY_ORDINAL: &str = "AnyOrdinal";

/// Of `std`: the module and the struct of a string of a fixed capacity, a
/// literal is a value of (§4.2, S-614), and its fields, the bytes and the
/// length used.
const FIXED_STR: (&str, &str, [&str; 2]) = ("text", "FixedStr", ["bytes", "len"]);

/// Of `std`: the module and the effect a `test` is given with `Alloc` (§8.5),
/// which no row of a program can have in this version (S-97, D-08).
const RANDOM: (&str, &str) = ("random", "Random");

/// A row of [`ENUMS`] in the analysis: the enum and the indices of its variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LangEnum {
    pub def: DefId,
    pub keep: u32,
    pub exit: u32,
}

/// [`FIXED_STR`] in the analysis: the struct and the indices of its fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LangFixedStr {
    pub def: DefId,
    pub bytes: u32,
    pub len: u32,
}

/// The rows of [`ENUMS`], [`ALLOC`], [`FIXED_STR`] and [`RANDOM`]: none with no
/// `std.core` (unit tests of a package with no std). Of std alone, which
/// [`crate::analyze_on`] does not read again.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LangItems {
    enums: [Option<LangEnum>; ENUMS.len()],
    any_ordinal: Option<DefId>,
    fixed_str: Option<LangFixedStr>,
    random: Option<DefId>,
    alloc: Option<DefId>,
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
    pub fn option(&self) -> Option<DefId> {
        self.enums[OPTION].map(|l| l.def)
    }

    /// [`ANY_ORDINAL`].
    pub(crate) fn any_ordinal(&self) -> Option<DefId> {
        self.any_ordinal
    }

    /// [`FIXED_STR`], if `d` is it.
    pub fn fixed_str(&self, d: DefId) -> Option<LangFixedStr> {
        self.fixed_str.filter(|l| l.def == d)
    }

    /// [`RANDOM`].
    pub(crate) fn random(&self) -> Option<DefId> {
        self.random
    }

    /// [`ALLOC`] (read through [`crate::Analysis::alloc`]).
    pub(crate) fn alloc(&self) -> Option<DefId> {
        self.alloc
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
    match s.a.prelude.get(ALLOC) {
        Some(&Entity::Def(d)) => s.a.modules.lang.alloc = Some(d),
        _ => onsa_diag::internal::bug(None, format!("`std.core` declares no `{ALLOC}`")),
    }
    for (row, (ty, keep, exit)) in ENUMS.into_iter().enumerate() {
        let Some(&Entity::Def(def)) = s.a.prelude.get(ty) else {
            onsa_diag::internal::bug(None, format!("`std.core` declares no `{ty}`"))
        };
        let names: Vec<String> = s.variants(def).into_iter().map(|(name, _)| name).collect();
        let index = |name| position(&names, ty, name);
        s.a.modules.lang.enums[row] = Some(LangEnum { def, keep: index(keep), exit: index(exit) });
        for (i, name) in names.into_iter().enumerate() {
            s.a.prelude.insert(name, Entity::Variant(def, i as u32));
        }
    }
    let Some(&any) = s.a.modules.core.and_then(|m| s.a.modules.get(m).items.get(ANY_ORDINAL)) else {
        onsa_diag::internal::bug(None, format!("`std.core` declares no `{ANY_ORDINAL}`"))
    };
    s.a.modules.lang.any_ordinal = Some(any);
    let (module, ty, [bytes, len]) = FIXED_STR;
    let def = item_of_std(s, module, ty);
    let names = s.field_names(def);
    let (bytes, len) = (position(&names, ty, bytes), position(&names, ty, len));
    s.a.modules.lang.fixed_str = Some(LangFixedStr { def, bytes, len });
    s.a.modules.lang.random = Some(item_of_std(s, RANDOM.0, RANDOM.1));
}

/// The item `name` of the module `module` of std, which the embedded std declares.
fn item_of_std(s: &Sema<'_>, module: &str, name: &str) -> DefId {
    let std = s.a.modules.core.and_then(|m| s.a.modules.get(m).parent);
    let m = std.and_then(|r| s.a.modules.get(r).children.get(module).copied());
    match m.and_then(|m| s.a.modules.get(m).items.get(name)) {
        Some(&def) => def,
        None => onsa_diag::internal::bug(None, format!("`std.{module}` declares no `{name}`")),
    }
}

/// The index of `name` in `names`, the members std declares of `ty`.
fn position(names: &[String], ty: &str, name: &str) -> u32 {
    match names.iter().position(|n| n == name) {
        Some(i) => i as u32,
        None => onsa_diag::internal::bug(None, format!("`{ty}` declares no `{name}`")),
    }
}
