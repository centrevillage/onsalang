//! The closed table of the manifest `onsa.toml` (spec §15.3, D-15): every
//! table, key and kind of value, in one place. The reader walks the TOML by
//! these rows ([`super::read`]); no other place compares the spelling of a key.
//! A row names the values this version does not support, with their
//! [`Feature`] (E0200 in the build of the target, S-154): the one place a
//! later work takes them out of.

use onsa_diag::unsupported::Feature;

/// A table of the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Table {
    /// The top level.
    Root,
    Package,
    /// `[dependencies]`: a key for each package ([`named`]).
    Dependencies,
    Export,
    /// `[targets]`: a table for each target ([`named`]).
    Targets,
    /// `[targets.<name>]`.
    Target,
    /// `[targets.<name>.memory]`.
    Memory,
    /// `[targets.<name>.bind]`: a key for each module ([`named`]).
    Bind,
    /// `[[plugin]]`.
    Plugin,
    /// `au = { subtype, manufacturer }` of a `[[plugin]]`.
    Au,
}

/// What a key holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Str,
    Bool,
    Int,
    /// An array of strings.
    Strs,
    Table(Table),
    /// An array of tables (`[[plugin]]`).
    Tables(Table),
}

/// The typed slot of a key; with its table, it names one row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Field {
    Package,
    Dependencies,
    Export,
    Targets,
    Plugin,
    Name,
    Edition,
    Prefix,
    Kind,
    Platform,
    Lang,
    Fp,
    Provides,
    Panic,
    PanicMessages,
    MainFrame,
    Memory,
    Bind,
    Bulk,
    FastBudget,
    BulkBudget,
    Flow,
    Id,
    Vendor,
    Version,
    Category,
    Au,
    Subtype,
    Manufacturer,
}

/// Whether the reader of this version reads the value of a key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Read {
    Yes,
    /// A key of the table whose value is not read yet (its work reads it:
    /// `memory` W9-05/W9-06, `[[plugin]]` U4).
    Later,
}

/// The rule of a value beyond its shape; a value that breaks it is an E1103
/// at the value (§15.3, §18.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    Any,
    /// One of a closed list (the list is the note, S-597), with a note for
    /// every value outside it.
    OneOf(&'static [&'static str], Option<&'static str>),
    /// A `snake_case` identifier other than `std` (§15.3, S-628).
    PackageName,
    /// `snake_case` names joined by `.` (§15.2, S-827).
    ModulePath,
    /// The form of `prefix` (§14.2).
    Prefix,
    /// The version of the embedded std (§15.3, S-83).
    StdVersion,
    /// A number of bytes: 0 or more (S-827).
    Bytes,
}

/// Where a key is required (§15.3): one lacking is an E1104 at the key of
/// its table ([`super::read`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Need {
    No,
    /// In every manifest, by the check of every command.
    Always,
    /// In a target whose `kind` is one of `kinds`, or whose `kind` and
    /// `lang` are `or`; not in one whose `kind` (or that `lang`) is not
    /// read. `build`: by the build of the target (its
    /// [`super::ManifestTarget::build_diagnostics`]), else by every command.
    Target {
        kinds: &'static [&'static str],
        or: Option<(&'static str, &'static str)>,
        build: bool,
    },
    /// In a package with `@export` items, by the build after the check of
    /// its sources (§14.2, S-832): [`super::Manifest::missing_prefix`].
    Exports,
}

/// The values of a key of a target this version does not support: each is
/// an E0200 in the build of the target, at the value (an element of an
/// array: at the element), and not in the other commands (§15.3, S-154).
/// A value its row's rule breaks is not one of them (S-827); the default
/// values are not (S-825).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unsupported {
    /// A string, or each element of an array of strings, outside the list
    /// of the values this version supports: a value the rule takes and the
    /// list does not name is unsupported.
    Except(&'static [&'static str]),
    True,
    /// Any value; a table that has an entry, at its key (S-824).
    Any,
}

/// A key of a table.
#[derive(Debug, Clone, Copy)]
pub struct Row {
    pub table: Table,
    pub key: &'static str,
    pub field: Field,
    pub shape: Shape,
    pub read: Read,
    pub rule: Rule,
    pub need: Need,
    pub unsupported: Option<(Unsupported, Feature)>,
}

const fn row(table: Table, key: &'static str, field: Field, shape: Shape, read: Read) -> Row {
    Row { table, key, field, shape, read, rule: Rule::Any, need: Need::No, unsupported: None }
}

impl Row {
    const fn with(self, rule: Rule) -> Row {
        Row { rule, ..self }
    }

    const fn need(self, need: Need) -> Row {
        Row { need, ..self }
    }

    const fn unsupported(self, values: Unsupported, feature: Feature) -> Row {
        Row { unsupported: Some((values, feature)), ..self }
    }
}

use Read::{Later, Yes};
use Rule::OneOf;
use Shape::{Bool, Int, Str, Strs};
use Unsupported::{Any, Except};

/// The effect of `provides` that gives the heap (§15.3).
pub const ALLOC: &str = "Alloc";

/// The values of `panic` (§9.2), which `onsa build` maps to its modes.
pub const PANIC: &[&str] = &["poison", "trap", "reset", "halt"];

/// The kind of a static library, which `cc` and `ar` build on the host.
pub const STATICLIB: &str = "staticlib";
const SOURCE: &str = "source";
/// The kinds an outer C toolchain builds (§15.3): with a platform not the
/// host, an E0200 of the build (S-161).
pub const TOOLCHAIN: &[&str] = &["exe", "clap", "vst3", "au", STATICLIB];
const KINDS: &[&str] = &["exe", "clap", "vst3", "au", "wasm-worklet", STATICLIB, SOURCE];
const FP_NOTE: &str = "a fn or a flow takes a relaxed profile with `@fp(relaxed)` (§15.5)";

/// The rows of §15.3, table by table.
pub static ROWS: &[Row] = &[
    row(Table::Root, "package", Field::Package, Shape::Table(Table::Package), Yes).need(Need::Always),
    row(Table::Root, "dependencies", Field::Dependencies, Shape::Table(Table::Dependencies), Yes),
    row(Table::Root, "export", Field::Export, Shape::Table(Table::Export), Yes).need(Need::Exports),
    row(Table::Root, "targets", Field::Targets, Shape::Table(Table::Targets), Yes),
    row(Table::Root, "plugin", Field::Plugin, Shape::Tables(Table::Plugin), Yes),
    row(Table::Package, "name", Field::Name, Str, Yes).with(Rule::PackageName).need(Need::Always),
    row(Table::Package, "edition", Field::Edition, Str, Yes).with(OneOf(&["2026"], None)).need(Need::Always),
    row(Table::Export, "prefix", Field::Prefix, Str, Yes).with(Rule::Prefix).need(Need::Exports),
    row(Table::Target, "kind", Field::Kind, Str, Yes)
        .with(OneOf(KINDS, None))
        .need(Need::Always)
        .unsupported(Except(&[STATICLIB, SOURCE]), Feature::ManifestKind),
    // The targets that give C or native code (R-47).
    row(Table::Target, "platform", Field::Platform, Str, Yes).need(Need::Target {
        kinds: TOOLCHAIN,
        or: Some((SOURCE, "c")),
        build: true,
    }),
    row(Table::Target, "lang", Field::Lang, Str, Yes)
        .with(OneOf(&["c", "js"], None))
        .need(Need::Target { kinds: &[SOURCE], or: None, build: false })
        .unsupported(Except(&["c"]), Feature::ManifestLang),
    row(Table::Target, "fp", Field::Fp, Str, Yes)
        .with(OneOf(&["strict", "strict-ftz"], Some(FP_NOTE)))
        .unsupported(Except(&["strict"]), Feature::ManifestFp),
    row(Table::Target, "provides", Field::Provides, Strs, Yes).unsupported(Except(&[ALLOC]), Feature::ManifestProvides),
    row(Table::Target, "panic", Field::Panic, Str, Yes).with(OneOf(PANIC, None)),
    row(Table::Target, "panic_messages", Field::PanicMessages, Bool, Yes),
    row(Table::Target, "main_frame", Field::MainFrame, Str, Yes)
        .with(OneOf(&["stack", "static"], None))
        .unsupported(Except(&["stack"]), Feature::ManifestMainFrame),
    row(Table::Target, "memory", Field::Memory, Shape::Table(Table::Memory), Yes),
    row(Table::Target, "bind", Field::Bind, Shape::Table(Table::Bind), Yes).unsupported(Any, Feature::ManifestBind),
    row(Table::Memory, "bulk", Field::Bulk, Bool, Yes).unsupported(Unsupported::True, Feature::ManifestBulk),
    row(Table::Memory, "fast_budget", Field::FastBudget, Int, Yes)
        .with(Rule::Bytes)
        .unsupported(Any, Feature::ManifestBudgets),
    row(Table::Memory, "bulk_budget", Field::BulkBudget, Int, Yes)
        .with(Rule::Bytes)
        .unsupported(Any, Feature::ManifestBudgets),
    row(Table::Plugin, "flow", Field::Flow, Str, Later),
    row(Table::Plugin, "id", Field::Id, Str, Later),
    row(Table::Plugin, "name", Field::Name, Str, Later),
    row(Table::Plugin, "vendor", Field::Vendor, Str, Later),
    row(Table::Plugin, "version", Field::Version, Str, Later),
    row(Table::Plugin, "category", Field::Category, Str, Later),
    // Read for its keys (E1102); its values are U4's.
    row(Table::Plugin, "au", Field::Au, Shape::Table(Table::Au), Yes),
    // SPEC-GAP(S-826): §15.3 does not give the kinds of these values.
    row(Table::Au, "subtype", Field::Subtype, Str, Later),
    row(Table::Au, "manufacturer", Field::Manufacturer, Str, Later),
];

/// The rule of the names of a table of names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Names {
    /// `snake_case` names joined by `.`, else an E1103 at the name (S-827).
    ModulePath,
    /// A `snake_case` identifier, else an E1103 at the name; the word names
    /// what is named (§15.3, S-828).
    SnakeCase(&'static str),
    /// Only `std`: another package is an E0200 at its key, whose value is
    /// not read (§15.3, S-154, S-827 (d′)).
    Std,
}

/// Every entry of a table whose keys are names the writer chooses.
#[derive(Debug, Clone, Copy)]
pub struct Named {
    pub shape: Shape,
    pub rule: Rule,
    pub names: Names,
}

/// The entries of a table of names (§15.3), or `None` for a table of rows.
pub fn named(table: Table) -> Option<Named> {
    let (shape, rule, names) = match table {
        Table::Dependencies => (Str, Rule::StdVersion, Names::Std),
        Table::Bind => (Str, Rule::ModulePath, Names::ModulePath),
        Table::Targets => (Shape::Table(Table::Target), Rule::Any, Names::SnakeCase("target")),
        _ => return None,
    };
    Some(Named { shape, rule, names })
}

/// The row of `key` in `table`.
pub fn find(table: Table, key: &str) -> Option<&'static Row> {
    ROWS.iter().find(|r| r.table == table && r.key == key)
}

/// The row of `field` in `table`.
pub fn row_of(table: Table, field: Field) -> Option<&'static Row> {
    ROWS.iter().find(|r| r.table == table && r.field == field)
}

/// The top-level table a test fragment holds beside the manifest, which the
/// test runner reads (`[test]`, [`crate::ManifestForm::Fragment`]).
pub const FRAGMENT_TEST: &str = "test";

/// The note of an E1102 in `table` at `path` (§18.1): the keys it takes, in
/// the order of the rows; at the top, the names of the tables.
pub fn keys_note(table: Table, path: &str) -> String {
    let keys: Vec<String> = ROWS
        .iter()
        .filter(|r| r.table == table)
        .map(|r| match r.shape {
            Shape::Table(_) if table == Table::Root => format!("`[{}]`", r.key),
            Shape::Tables(_) => format!("`[[{}]]`", r.key),
            _ => format!("`{}`", r.key),
        })
        .collect();
    match table {
        Table::Root => format!("the tables of the manifest are {}", keys.join(", ")),
        _ => format!("the keys of `{path}` are {}", keys.join(", ")),
    }
}
