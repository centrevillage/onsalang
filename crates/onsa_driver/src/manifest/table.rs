//! The closed table of the manifest `onsa.toml` (spec §15.3, D-15): every
//! table, key and kind of value, in one place. The reader walks the TOML by
//! these rows ([`super::read`]); no other place compares the spelling of a key.

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

/// A key of a table.
#[derive(Debug, Clone, Copy)]
pub struct Row {
    pub table: Table,
    pub key: &'static str,
    pub field: Field,
    pub shape: Shape,
    pub read: Read,
}

const fn row(table: Table, key: &'static str, field: Field, shape: Shape, read: Read) -> Row {
    Row { table, key, field, shape, read }
}

use Read::{Later, Yes};
use Shape::{Bool, Int, Str, Strs};

/// The rows of §15.3, table by table.
pub static ROWS: &[Row] = &[
    row(Table::Root, "package", Field::Package, Shape::Table(Table::Package), Yes),
    row(Table::Root, "dependencies", Field::Dependencies, Shape::Table(Table::Dependencies), Yes),
    row(Table::Root, "export", Field::Export, Shape::Table(Table::Export), Yes),
    row(Table::Root, "targets", Field::Targets, Shape::Table(Table::Targets), Yes),
    row(Table::Root, "plugin", Field::Plugin, Shape::Tables(Table::Plugin), Yes),
    row(Table::Package, "name", Field::Name, Str, Yes),
    row(Table::Package, "edition", Field::Edition, Str, Yes),
    row(Table::Export, "prefix", Field::Prefix, Str, Yes),
    row(Table::Target, "kind", Field::Kind, Str, Yes),
    row(Table::Target, "platform", Field::Platform, Str, Yes),
    row(Table::Target, "lang", Field::Lang, Str, Yes),
    row(Table::Target, "fp", Field::Fp, Str, Yes),
    row(Table::Target, "provides", Field::Provides, Strs, Yes),
    row(Table::Target, "panic", Field::Panic, Str, Yes),
    row(Table::Target, "panic_messages", Field::PanicMessages, Bool, Yes),
    row(Table::Target, "main_frame", Field::MainFrame, Str, Yes),
    row(Table::Target, "memory", Field::Memory, Shape::Table(Table::Memory), Yes),
    row(Table::Target, "bind", Field::Bind, Shape::Table(Table::Bind), Yes),
    row(Table::Memory, "bulk", Field::Bulk, Bool, Later),
    row(Table::Memory, "fast_budget", Field::FastBudget, Int, Later),
    row(Table::Memory, "bulk_budget", Field::BulkBudget, Int, Later),
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

/// The shape of every entry of a table whose keys are names the writer
/// chooses (§15.3), or `None` for a table of rows.
pub fn named(table: Table) -> Option<Shape> {
    match table {
        Table::Dependencies | Table::Bind => Some(Str),
        Table::Targets => Some(Shape::Table(Table::Target)),
        _ => None,
    }
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
