//! The one reader of `onsa.toml` (S-99, R-80 (5)): the TOML tree of
//! `toml_edit`, walked by the rows of [`table`], into the typed [`Manifest`]
//! with the places of its keys and values.

use std::collections::BTreeMap;
use std::ops::Range;

use toml_edit::{ImDocument, Item, TableLike};

use super::table::{self, Field, Read, Shape, Table};
use super::{Manifest, ManifestExport, ManifestMemory, ManifestPackage, ManifestTarget, Spanned};
use crate::{ManifestForm, ManifestSource};

/// Read the manifest of `source`. The errors name it by its file string
/// (`onsa.toml` for a package root, S-234) and keep the line and the column.
pub fn read(source: &ManifestSource) -> Result<Manifest, String> {
    let doc = ImDocument::parse(source.text.as_str()).map_err(|e| format!("{}: {e}", source.path))?;
    Reader { source }.manifest(doc.as_table()).map_err(|e| format!("{}: {e}", source.path))
}

struct Reader<'s> {
    source: &'s ManifestSource,
}

/// A value read by the shape of its row.
enum Typed<'a> {
    Str(String),
    Bool(bool),
    Int(i64),
    Strs(Vec<Spanned<String>>),
    Table(&'a dyn TableLike, Table),
}

/// A key read, with its dotted path (for the messages) and its places.
struct Got<'a> {
    value: Typed<'a>,
    path: String,
    key: Range<usize>,
    span: Range<usize>,
}

/// The keys of one table, read by its rows; each is taken once.
struct Fields<'a> {
    table: Table,
    path: String,
    got: Vec<(Field, Got<'a>)>,
}

impl<'s> Reader<'s> {
    fn manifest(&self, root: &dyn TableLike) -> Result<Manifest, String> {
        let mut f = self.fields(Table::Root, root, "")?;
        let package = self.table(f.need(Field::Package)?, |f| {
            Ok(ManifestPackage { name: f.need(Field::Name)?.str(), edition: f.take(Field::Edition).map(Got::str) })
        })?;
        let dependencies = self.strings(f.take(Field::Dependencies))?;
        let export = f
            .take(Field::Export)
            .map(|g| self.table(g, |f| Ok(ManifestExport { prefix: f.take(Field::Prefix).map(Got::str) })));
        let targets = match f.take(Field::Targets) {
            Some(g) => self.map(g, |g| self.table(g, |f| self.target(f)))?,
            None => BTreeMap::new(),
        };
        f.done();
        Ok(Manifest { package, dependencies, export: export.transpose()?, targets })
    }

    fn target(&self, f: &mut Fields) -> Result<ManifestTarget, String> {
        Ok(ManifestTarget {
            kind: f.need(Field::Kind)?.str(),
            platform: f.need(Field::Platform)?.str(),
            lang: f.take(Field::Lang).map(Got::str),
            numeric: f.take(Field::Numeric).map(Got::str),
            provides: f.take(Field::Provides).map(Got::strs).unwrap_or_default(),
            panic: f.take(Field::Panic).map(Got::str),
            panic_messages: f.take(Field::PanicMessages).map(Got::bool),
            main_frame: f.take(Field::MainFrame).map(Got::str),
            memory: f.take(Field::Memory).map(|g| self.table(g, |f| self.memory(f))).transpose()?,
            bind: self.strings(f.take(Field::Bind))?,
        })
    }

    fn memory(&self, f: &mut Fields) -> Result<ManifestMemory, String> {
        let bulk_threshold = match f.take(Field::BulkThreshold) {
            Some(g) => {
                let path = g.path.clone();
                let n = g.int();
                let value = u32::try_from(n.value).map_err(|_| {
                    self.error(n.span.start, format!("`{path}`: invalid value: integer `{}`, expected u32", n.value))
                })?;
                Some(Spanned { value, key: n.key, span: n.span })
            }
            None => None,
        };
        Ok(ManifestMemory { bulk_threshold })
    }

    /// The keys of `t`, the table `table` at `path`, read by its rows.
    fn fields<'a>(&self, table: Table, t: &'a dyn TableLike, path: &str) -> Result<Fields<'a>, String> {
        let mut got = Vec::new();
        for (key, item) in t.iter() {
            if table == Table::Root && self.source.form == ManifestForm::Fragment && key == table::FRAGMENT_TEST {
                continue;
            }
            // A key the table does not know is skipped, as before the table
            // was closed (U2a2 makes this branch the E1102).
            let Some(row) = table::find(table, key) else { continue };
            if row.read == Read::Later {
                continue;
            }
            got.push((row.field, self.got(row.shape, t, key, item, path)?));
        }
        Ok(Fields { table, path: path.to_string(), got })
    }

    /// The value of `key` of `t` read as `shape`.
    fn got<'a>(
        &self,
        shape: Shape,
        t: &'a dyn TableLike,
        key: &str,
        item: &'a Item,
        path: &str,
    ) -> Result<Got<'a>, String> {
        let path = if path.is_empty() { key.to_string() } else { format!("{path}.{key}") };
        // An implicit table has no span of its own: the place of its key.
        let key_span = t.key(key).and_then(|k| k.span()).unwrap_or_default();
        let span = item.span().unwrap_or_else(|| key_span.clone());
        let wrong = |at: usize, found: &str, expected: &str| {
            self.error(at, format!("`{path}`: invalid type: {found}, expected {expected}"))
        };
        let expected = match shape {
            Shape::Str => "a string",
            Shape::Bool => "a boolean",
            Shape::Int => "an integer",
            Shape::Strs => "an array of strings",
            Shape::Table(_) => "a table",
            Shape::Tables(_) => "an array of tables",
        };
        let not = || wrong(span.start, item.type_name(), expected);
        let value = match shape {
            Shape::Str => Typed::Str(item.as_str().ok_or_else(not)?.to_string()),
            Shape::Bool => Typed::Bool(item.as_bool().ok_or_else(not)?),
            Shape::Int => Typed::Int(item.as_integer().ok_or_else(not)?),
            Shape::Strs => {
                let mut out = Vec::new();
                for v in item.as_array().ok_or_else(not)? {
                    let at = v.span().unwrap_or_default();
                    let s = v.as_str().ok_or_else(|| wrong(at.start, v.type_name(), "a string"))?;
                    out.push(Spanned { value: s.to_string(), key: key_span.clone(), span: at });
                }
                Typed::Strs(out)
            }
            Shape::Table(table) => Typed::Table(item.as_table_like().ok_or_else(not)?, table),
            Shape::Tables(_) => onsa_diag::internal::bug(None, format!("`{path}`: an array of tables is not read yet")),
        };
        Ok(Got { value, path, key: key_span, span })
    }

    /// The table of `got` built by `build` from its keys.
    fn table<T>(&self, got: Got, build: impl FnOnce(&mut Fields) -> Result<T, String>) -> Result<Spanned<T>, String> {
        let (t, table) = got.as_table();
        let mut f = self.fields(table, t, &got.path)?;
        let value = build(&mut f)?;
        f.done();
        Ok(Spanned { value, key: got.key, span: got.span })
    }

    /// The entries of the table of names of `got` ([`table::named`]), each built by `each`.
    fn map<'a, T>(
        &self,
        got: Got<'a>,
        each: impl Fn(Got<'a>) -> Result<T, String>,
    ) -> Result<BTreeMap<String, T>, String> {
        let (t, table) = got.as_table();
        let Some(shape) = table::named(table) else {
            onsa_diag::internal::bug(None, format!("`{}` is read as a table of names", got.path));
        };
        let mut out = BTreeMap::new();
        for (key, item) in t.iter() {
            out.insert(key.to_string(), each(self.got(shape, t, key, item, &got.path)?)?);
        }
        Ok(out)
    }

    /// A table of names whose entries are strings (`[dependencies]`, `bind`); none when not written.
    fn strings(&self, got: Option<Got>) -> Result<BTreeMap<String, Spanned<String>>, String> {
        got.map_or_else(|| Ok(BTreeMap::new()), |g| self.map(g, |g| Ok(g.str())))
    }

    /// `message` at the byte `at` of the text, by its line and column (from 1).
    fn error(&self, at: usize, message: String) -> String {
        let text = &self.source.text;
        let before = text.get(..at).unwrap_or(text);
        let start = before.rfind('\n').map_or(0, |i| i + 1);
        let line = before.matches('\n').count() + 1;
        format!("line {line}, column {}: {message}", before[start..].chars().count() + 1)
    }
}

impl<'a> Fields<'a> {
    fn take(&mut self, field: Field) -> Option<Got<'a>> {
        let i = self.got.iter().position(|(f, _)| *f == field)?;
        Some(self.got.swap_remove(i).1)
    }

    /// A key the reader requires: `[package]`, `name`, `kind` and, as
    /// before the table was closed, `platform` in every target (U3 moves it
    /// to the build, E1104).
    fn need(&mut self, field: Field) -> Result<Got<'a>, String> {
        self.take(field).ok_or_else(|| {
            let Some(row) = table::row_of(self.table, field) else {
                onsa_diag::internal::bug(None, format!("no row for {field:?} in {:?}", self.table));
            };
            match self.table {
                Table::Root => format!("missing table `[{}]`", row.key),
                _ => format!("`[{}]`: missing key `{}`", self.path, row.key),
            }
        })
    }

    /// Every key read was taken: a key the builder leaves would be lost silently.
    fn done(self) {
        if let Some((field, g)) = self.got.first() {
            onsa_diag::internal::bug(None, format!("`{}` ({field:?}) is read but not built", g.path));
        }
    }
}

impl<'a> Got<'a> {
    fn mismatch(&self) -> ! {
        onsa_diag::internal::bug(None, format!("`{}` is built as another shape than its row", self.path))
    }

    fn spanned<T>(&self, value: T) -> Spanned<T> {
        Spanned { value, key: self.key.clone(), span: self.span.clone() }
    }

    fn str(self) -> Spanned<String> {
        match &self.value {
            Typed::Str(s) => self.spanned(s.clone()),
            _ => self.mismatch(),
        }
    }

    fn bool(self) -> Spanned<bool> {
        match self.value {
            Typed::Bool(b) => self.spanned(b),
            _ => self.mismatch(),
        }
    }

    fn int(self) -> Spanned<i64> {
        match self.value {
            Typed::Int(n) => self.spanned(n),
            _ => self.mismatch(),
        }
    }

    fn strs(self) -> Vec<Spanned<String>> {
        match self.value {
            Typed::Strs(v) => v,
            _ => self.mismatch(),
        }
    }

    fn as_table(&self) -> (&'a dyn TableLike, Table) {
        match self.value {
            Typed::Table(t, table) => (t, table),
            _ => self.mismatch(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(text: &str, form: ManifestForm) -> ManifestSource {
        ManifestSource { path: "onsa.toml".into(), text: text.into(), form }
    }

    fn file(text: &str) -> Result<Manifest, String> {
        read(&source(text, ManifestForm::File))
    }

    const FULL: &str = "[package]\nname = \"voice\"\nedition = \"2026\"\n\n[dependencies]\nstd = \"0.1.0\"\n\n\
                        [export]\nprefix = \"vc_\"\n\n[targets.daisy]\nkind = \"staticlib\"\n\
                        platform = \"thumbv7em-none-eabihf\"\nlang = \"c\"\nnumeric = \"strict-ftz\"\n\
                        provides = [\"Alloc\"]\npanic = \"reset\"\npanic_messages = false\nmain_frame = \"static\"\n\n\
                        [targets.daisy.memory]\nbulk_threshold = 64\n\n[targets.daisy.bind]\n\
                        \"audio.device\" = \"daisy_hal.audio\"\n";

    /// Every key the reader reads becomes its typed value, with the places of
    /// its key and its value (a table: the last key of its header).
    #[test]
    fn the_rows_make_typed_values_with_their_places() {
        let m = file(FULL).unwrap();
        let at = |r: &Range<usize>| &FULL[r.clone()];
        let p = &m.package.value;
        assert_eq!((p.name.value.as_str(), at(&p.name.key), at(&p.name.span)), ("voice", "name", "\"voice\""));
        assert_eq!(p.edition.as_ref().unwrap().value, "2026");
        assert_eq!(at(&m.package.key), "package");
        assert_eq!(m.dependencies["std"].value, "0.1.0");
        assert_eq!(at(&m.dependencies["std"].key), "std");
        assert_eq!(m.export.as_ref().unwrap().value.prefix.as_ref().unwrap().value, "vc_");
        let t = &m.targets["daisy"];
        assert_eq!(at(&t.key), "daisy");
        assert!(at(&t.span).starts_with("[targets.daisy]"), "{:?}", at(&t.span));
        let t = &t.value;
        assert_eq!((t.kind.value.as_str(), t.platform.value.as_str()), ("staticlib", "thumbv7em-none-eabihf"));
        assert_eq!(t.lang.as_ref().unwrap().value, "c");
        assert_eq!(t.provides.iter().map(|p| at(&p.span)).collect::<Vec<_>>(), ["\"Alloc\""]);
        assert_eq!(t.panic.as_ref().unwrap().value, "reset");
        assert!(!t.panic_messages.as_ref().unwrap().value);
        assert_eq!(t.main_frame.as_ref().unwrap().value, "static");
        assert_eq!(t.bind["audio.device"].value, "daisy_hal.audio");
        assert_eq!(at(&t.bind["audio.device"].key), "\"audio.device\"");
    }

    /// The old names `numeric` and `memory.bulk_threshold` are read as before
    /// (U2a2 takes them out), and the keys the reader before the closed table
    /// did not know (`fp`, `memory.bulk`, `[[plugin]]`, any other) are
    /// skipped with their values unchecked.
    #[test]
    fn the_old_names_are_read_and_the_other_keys_skipped_as_before() {
        let m = file(FULL).unwrap();
        let t = &m.targets["daisy"].value;
        assert_eq!(t.numeric.as_ref().unwrap().value, "strict-ftz");
        assert_eq!(t.memory.as_ref().unwrap().value.bulk_threshold.as_ref().unwrap().value, 64);
        let other = "x = 1\n[package]\nname = \"a\"\nflows = 2\n[targets.t]\nkind = \"s\"\nplatform = \"h\"\nfp = 3\n\
                     [targets.t.memory]\nbulk = \"no\"\n[[plugin]]\nflow = 4\n[test]\nmode = 5\n";
        for form in [ManifestForm::File, ManifestForm::Fragment] {
            let m = read(&source(other, form)).unwrap();
            assert!(m.targets["t"].value.numeric.is_none());
        }
        for (text, e) in [
            (
                "[package]\nname = \"a\"\n[targets.t]\nkind = \"s\"\nplatform = \"h\"\nnumeric = 1\n",
                "line 6, column 11",
            ),
            (
                "[package]\nname = \"a\"\n[targets.t]\nkind = \"s\"\nplatform = \"h\"\n[targets.t.memory]\nbulk_threshold = -1\n",
                "expected u32",
            ),
        ] {
            let err = file(text).unwrap_err();
            assert!(err.contains(e), "{err}");
        }
    }

    /// The errors of the reading name the manifest by its file string and
    /// keep the line and the column; a text that is not TOML is the error of
    /// the TOML parser, and so is a nesting deeper than its limit (no stack
    /// runs out).
    #[test]
    fn the_errors_name_the_file_and_the_place() {
        let cases = [
            ("[package]\nname = 3\n", "onsa.toml: line 2, column 8: `package.name`: invalid type: integer"),
            ("[package]\nname = \"a\"\nedition = 2026\n", "onsa.toml: line 3, column 11: `package.edition`"),
            ("", "onsa.toml: missing table `[package]`"),
            ("[package]\nedition = \"2026\"\n", "onsa.toml: `[package]`: missing key `name`"),
            (
                "[package]\nname = \"a\"\n[targets.t]\nkind = \"s\"\n",
                "onsa.toml: `[targets.t]`: missing key `platform`",
            ),
            (
                "[package]\nname = \"a\"\n[targets.t]\nkind = \"s\"\nplatform = \"h\"\nprovides = [\"Alloc\", 1]\n",
                "line 6, column 22",
            ),
            ("[package\n", "onsa.toml: TOML parse error at line 1, column 9"),
        ];
        for (text, e) in cases {
            let err = file(text).unwrap_err();
            assert!(err.starts_with(e) || err.contains(e), "{text:?}: {err}");
        }
        let deep = format!("[package]\nname = \"a\"\nx = {}1{}\n", "[".repeat(100), "]".repeat(100));
        let err = file(&deep).unwrap_err();
        assert!(err.starts_with("onsa.toml: TOML parse error") && err.contains("recursion limit"), "{err}");
    }

    /// The top-level `[test]` of a fragment is the test runner's, skipped
    /// with its values unchecked (in `onsa.toml` it is, in this version, a key
    /// the table does not know).
    #[test]
    fn a_fragment_skips_its_test_table() {
        let text = "\n[package]\nname = \"a\"\n[test]\nmode = 1\n[[test.fix]]\nk = 2\n";
        assert_eq!(read(&source(text, ManifestForm::Fragment)).unwrap().package.value.name.value, "a");
    }

    /// The table has one row for a key of a table and for a field of a
    /// table, and a table of rows for every table a row holds.
    #[test]
    fn the_rows_of_the_table_are_one_each() {
        for r in table::ROWS {
            assert!(std::ptr::eq(table::find(r.table, r.key).unwrap(), r), "{}", r.key);
            assert!(std::ptr::eq(table::row_of(r.table, r.field).unwrap(), r), "{}", r.key);
            if let Shape::Table(t) | Shape::Tables(t) = r.shape {
                let rows = table::ROWS.iter().any(|x| x.table == t);
                assert!(rows || table::named(t).is_some() || t == Table::Au, "{}", r.key);
            }
        }
    }
}
