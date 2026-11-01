//! The one reader of `onsa.toml` (S-99, R-80 (5)): the TOML tree of
//! `toml_edit`, walked by the rows of [`table`], into the typed [`Manifest`]
//! with the places of its keys and values, and the diagnostics of its check
//! (§18.1): every one of the manifest, which is one unit.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;

use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};
use toml_edit::{ImDocument, Item, TableLike};

use super::table::{self, Field, Read, Shape, Table};
use super::{Manifest, ManifestExport, ManifestMemory, ManifestPackage, ManifestRead, ManifestTarget, Spanned};
use crate::{ManifestForm, ManifestSource};

/// Read the manifest of `source`, whose places are in `file`. The
/// diagnostics are those of the keys (E1101, E1102, the E1103 of a target
/// name); a wrong value or a missing key is still an error of the reading
/// (U2b), which names the manifest by its file string (`onsa.toml` for a
/// package root, S-234) and keeps the line and the column.
pub fn read(source: &ManifestSource, file: FileId) -> Result<ManifestRead, String> {
    let done = |manifest, diagnostics| ManifestRead { file, form: source.form, manifest, diagnostics };
    let doc = match ImDocument::parse(source.text.as_str()) {
        Ok(doc) => doc,
        // The TOML parser stops at its first error: one E1101, and no other.
        Err(e) => {
            let text = source.text.as_str();
            let at = e.span().unwrap_or_default();
            let floor = |i: usize| (0..=i.min(text.len())).rev().find(|&k| text.is_char_boundary(k)).unwrap_or(0);
            let (start, mut end) = (floor(at.start), floor(at.end));
            // A range of blanks and line ends (the end of a line) is empty: it has no `found`.
            if text[start..end].trim().is_empty() {
                end = start;
            }
            let reason = e.message().trim_end().replace('\n', "; ");
            let message = if reason.is_empty() { String::new() } else { format!(": {reason}") };
            let d = Diagnostic::new(
                Stage::Manifest,
                Code::E1101,
                Span::new(file, start as u32, end as u32),
                format!("the manifest is not valid TOML{message}"),
            );
            return Ok(done(Manifest::default(), vec![d]));
        }
    };
    let reader = Reader { source, file, diagnostics: RefCell::default() };
    let manifest = reader.manifest(doc.as_table());
    let diagnostics = reader.diagnostics.into_inner();
    match manifest {
        Ok(m) => Ok(done(m, diagnostics)),
        // An error of the reading beside a diagnostic: the diagnostics are
        // reported (all stop the command with exit 2; U2b makes the errors diagnostics).
        Err(_) if !diagnostics.is_empty() => Ok(done(Manifest::default(), diagnostics)),
        Err(e) => Err(format!("{}: {e}", source.path)),
    }
}

struct Reader<'s> {
    source: &'s ManifestSource,
    file: FileId,
    diagnostics: RefCell<Vec<Diagnostic>>,
}

/// A value read by the shape of its row.
enum Typed<'a> {
    Str(String),
    Bool(bool),
    Strs(Vec<Spanned<String>>),
    Table(&'a dyn TableLike, Table),
    /// The tables of an array of tables, each a [`Typed::Table`].
    Tables(Vec<Got<'a>>),
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
        // `[[plugin]]` is walked for its keys; its values are U4's.
        for p in f.take(Field::Plugin).map(Got::tables).unwrap_or_default() {
            self.table(p, |f| f.take(Field::Au).map_or(Ok(()), |g| self.table(g, |_| Ok(())).map(drop)))?;
        }
        f.done();
        Ok(Manifest { package, dependencies, export: export.transpose()?, targets })
    }

    fn target(&self, f: &mut Fields) -> Result<ManifestTarget, String> {
        Ok(ManifestTarget {
            kind: f.need(Field::Kind)?.str(),
            platform: f.need(Field::Platform)?.str(),
            lang: f.take(Field::Lang).map(Got::str),
            fp: f.take(Field::Fp).map(Got::str),
            provides: f.take(Field::Provides).map(Got::strs).unwrap_or_default(),
            panic: f.take(Field::Panic).map(Got::str),
            panic_messages: f.take(Field::PanicMessages).map(Got::bool),
            main_frame: f.take(Field::MainFrame).map(Got::str),
            memory: f.take(Field::Memory).map(|g| self.table(g, |_| Ok(ManifestMemory {}))).transpose()?,
            bind: self.strings(f.take(Field::Bind))?,
        })
    }

    /// The keys of `t`, the table `table` at `path`, read by its rows.
    fn fields<'a>(&self, table: Table, t: &'a dyn TableLike, path: &str) -> Result<Fields<'a>, String> {
        let mut got = Vec::new();
        for (key, item) in t.iter() {
            if table == Table::Root && self.source.form == ManifestForm::Fragment && key == table::FRAGMENT_TEST {
                continue;
            }
            let Some(row) = table::find(table, key) else {
                self.unknown(table, t, key, item, path);
                continue;
            };
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
        let path = dotted(path, key);
        // An implicit table has no span of its own: the place of its key.
        let key_span = key_span(t, key, item);
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
            // No key read yet holds an integer (`fast_budget`, `bulk_budget`: W9-05).
            Shape::Int => onsa_diag::internal::bug(None, format!("`{path}`: an integer is not read yet")),
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
            Shape::Tables(table) => {
                let one = |t: &'a dyn TableLike, at: Option<Range<usize>>| Got {
                    value: Typed::Table(t, table),
                    path: path.clone(),
                    key: key_span.clone(),
                    span: at.unwrap_or_else(|| span.clone()),
                };
                match item.as_array_of_tables() {
                    Some(a) => Typed::Tables(a.iter().map(|t| one(t, t.span())).collect()),
                    None => {
                        let mut out = Vec::new();
                        for v in item.as_array().ok_or_else(not)? {
                            let at = v.span();
                            let t = v
                                .as_inline_table()
                                .ok_or_else(|| wrong(at.clone().unwrap_or_default().start, v.type_name(), "a table"))?;
                            out.push(one(t, at));
                        }
                        Typed::Tables(out)
                    }
                }
            }
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
            if table == Table::Targets {
                self.snake_case(key, key_span(t, key, item), "target");
            }
            out.insert(key.to_string(), each(self.got(shape, t, key, item, &got.path)?)?);
        }
        Ok(out)
    }

    /// The E1102 of `key` of `t`, the table `table` at `path`, which the
    /// table does not know: at the key (for a table, that of its header), with
    /// the keys the table takes. A table it does not know is not walked.
    fn unknown(&self, table: Table, t: &dyn TableLike, key: &str, item: &Item, path: &str) {
        let full = dotted(path, key);
        // A table is named so only where a header writes it; a dotted key and
        // an inline table are keys as the writer wrote them.
        let what = match item {
            Item::ArrayOfTables(_) => format!("table `[[{full}]]`"),
            Item::Table(t) if !t.is_dotted() => format!("table `[{full}]`"),
            _ => format!("key `{full}`"),
        };
        let d =
            Diagnostic::new(Stage::Manifest, Code::E1102, self.span(key_span(t, key, item)), format!("unknown {what}"))
                .with_rule(table::keys_note(table, path));
        self.diagnostics.borrow_mut().push(d);
    }

    /// The rule of a name the manifest gives (§15.3): a `snake_case`
    /// identifier, as a module name (§2.3), else an E1103 at `at`. The one
    /// place of the rule, for the names of the targets and of the package.
    fn snake_case(&self, name: &str, at: Range<usize>, what: &str) {
        if !onsa_syntax::is_module_name(name) {
            let d = Diagnostic::new(
                Stage::Manifest,
                Code::E1103,
                self.span(at),
                format!("the {what} name `{name}` is not a `snake_case` identifier"),
            )
            .with_rule(format!("a {what} name is a `snake_case` identifier, as a module name (§2.3, §15.3)"));
            self.diagnostics.borrow_mut().push(d);
        }
    }

    fn span(&self, at: Range<usize>) -> Span {
        Span::new(self.file, at.start as u32, at.end as u32)
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

    fn tables(self) -> Vec<Got<'a>> {
        match self.value {
            Typed::Tables(v) => v,
            _ => self.mismatch(),
        }
    }
}

/// `key` under the dotted `path` (empty at the top).
fn dotted(path: &str, key: &str) -> String {
    if path.is_empty() { key.to_string() } else { format!("{path}.{key}") }
}

/// The place of `key` of `t` (of `item` when the key has none).
fn key_span(t: &dyn TableLike, key: &str, item: &Item) -> Range<usize> {
    t.key(key).and_then(|k| k.span()).or_else(|| item.span()).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(text: &str, form: ManifestForm) -> ManifestSource {
        ManifestSource { path: "onsa.toml".into(), text: text.into(), form }
    }

    fn read_as(text: &str, form: ManifestForm) -> Result<ManifestRead, String> {
        read(&source(text, form), FileId(0))
    }

    /// The manifest of `text`, which has no diagnostic.
    fn file(text: &str) -> Result<Manifest, String> {
        let r = read_as(text, ManifestForm::File)?;
        assert!(r.diagnostics.is_empty(), "{text:?}: {:?}", r.diagnostics);
        Ok(r.manifest)
    }

    /// The codes and the texts of the places of the diagnostics of `text`,
    /// in the order of the text (the walk's order is not the printed one).
    fn diagnostics(text: &str, form: ManifestForm) -> Vec<(Code, &str)> {
        let mut r = read_as(text, form).unwrap();
        r.diagnostics.sort_by_key(|d| d.span.start);
        r.diagnostics.iter().map(|d| (d.code, &text[d.span.start as usize..d.span.end as usize])).collect()
    }

    const FULL: &str = "[package]\nname = \"voice\"\nedition = \"2026\"\n\n[dependencies]\nstd = \"0.1.0\"\n\n\
                        [export]\nprefix = \"vc_\"\n\n[targets.daisy]\nkind = \"staticlib\"\n\
                        platform = \"thumbv7em-none-eabihf\"\nlang = \"c\"\nfp = \"strict-ftz\"\n\
                        provides = [\"Alloc\"]\npanic = \"reset\"\npanic_messages = false\nmain_frame = \"static\"\n\n\
                        [targets.daisy.memory]\nbulk = true\n\n[targets.daisy.bind]\n\
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
        assert_eq!(t.fp.as_ref().unwrap().value, "strict-ftz");
        assert_eq!(t.provides.iter().map(|p| at(&p.span)).collect::<Vec<_>>(), ["\"Alloc\""]);
        assert_eq!(t.panic.as_ref().unwrap().value, "reset");
        assert!(!t.panic_messages.as_ref().unwrap().value);
        assert_eq!(t.main_frame.as_ref().unwrap().value, "static");
        assert!(t.memory.is_some());
        assert_eq!(t.bind["audio.device"].value, "daisy_hal.audio");
        assert_eq!(at(&t.bind["audio.device"].key), "\"audio.device\"");
    }

    /// A manifest with every row of the table reads without a diagnostic: a
    /// row the reader reads but its builder does not take is an internal
    /// error ([`Fields::done`]), so a new row fails here until it is built.
    /// The values of the rows not read yet ([`Read::Later`]) are not checked.
    #[test]
    fn a_manifest_with_every_row_reads() {
        let header = |table: Table| match table {
            Table::Root | Table::Dependencies | Table::Targets | Table::Bind => None,
            Table::Package => Some("[package]"),
            Table::Export => Some("[export]"),
            Table::Target => Some("[targets.t]"),
            Table::Memory => Some("[targets.t.memory]"),
            Table::Plugin => Some("[[plugin]]"),
            Table::Au => Some("[plugin.au]"),
        };
        let mut text = String::new();
        let mut last = None;
        for r in table::ROWS {
            let Some(h) = header(r.table) else { continue };
            if last != Some(h) {
                text.push_str(&format!("{h}\n"));
                last = Some(h);
            }
            let value = match r.shape {
                Shape::Str => "\"x\"",
                Shape::Bool => "true",
                Shape::Int => "1",
                Shape::Strs => "[\"Alloc\"]",
                Shape::Table(_) | Shape::Tables(_) => continue,
            };
            text.push_str(&format!("{} = {value}\n", r.key));
        }
        let m = file(&text).unwrap_or_else(|e| panic!("{text}\n{e}"));
        assert_eq!(m.targets["t"].value.fp.as_ref().unwrap().value, "x", "{text}");
        let other = "[package]\nname = \"a\"\n[targets.t]\nkind = \"s\"\nplatform = \"h\"\n[targets.t.memory]\n\
                     bulk = \"no\"\nfast_budget = \"many\"\n[[plugin]]\nflow = 4\nau = { subtype = 1 }\n";
        file(other).unwrap();
    }

    /// E1102 (§18.1, S-99): every key a table does not know, at the key (a
    /// table at the key of its header), with the keys of its table in a note
    /// and no candidate (S-597). The old names (S-166) and `flows`, `fns`
    /// (S-639) are such keys; a table the reader does not know is not walked.
    #[test]
    fn every_unknown_key_is_an_e1102_with_the_keys_of_its_table() {
        let text = "x = 1\n[package]\nname = \"a\"\nflows = 2\n[export]\nfns = []\n[targets.t]\nkind = \"s\"\n\
                    platform = \"h\"\nnumeric = \"strict\"\n[targets.t.memory]\nbulk_threshold = 64\n\
                    [targets.t.mem]\nanything = 1\n[[plugin]]\nwhat = 4\nau = { zz = 1 }\n[[extra]]\n";
        let found = diagnostics(text, ManifestForm::File);
        let expected = ["x", "flows", "fns", "numeric", "bulk_threshold", "mem", "what", "zz", "extra"];
        assert_eq!(found, expected.map(|k| (Code::E1102, k)));
        let mut r = read_as(text, ManifestForm::File).unwrap();
        r.diagnostics.sort_by_key(|d| d.span.start);
        let notes: Vec<&str> = r.diagnostics.iter().map(|d| d.notes[0].message.as_str()).collect();
        assert_eq!(
            notes[0],
            "the tables of the manifest are `[package]`, `[dependencies]`, `[export]`, `[targets]`, `[[plugin]]`"
        );
        assert_eq!(notes[1], "the keys of `package` are `name`, `edition`");
        assert!(notes[3].starts_with("the keys of `targets.t` are `kind`, `platform`, `lang`, `fp`,"), "{}", notes[3]);
        assert_eq!(notes[4], "the keys of `targets.t.memory` are `bulk`, `fast_budget`, `bulk_budget`");
        assert_eq!(notes[7], "the keys of `plugin.au` are `subtype`, `manufacturer`");
        for d in &r.diagnostics {
            assert!(d.fixes.is_empty() && d.notes.len() == 1 && d.notes[0].span.is_none(), "{d:?}");
            assert_eq!(d.stage, Stage::Manifest);
        }
    }

    /// The top-level `[test]` is the test runner's in a fragment, skipped with
    /// its values unchecked, and an E1102 in `onsa.toml` (A3).
    #[test]
    fn test_is_a_table_of_a_fragment_only() {
        let text = "\n[package]\nname = \"a\"\n[test]\nmode = 1\n[[test.fix]]\nk = 2\n";
        assert_eq!(diagnostics(text, ManifestForm::Fragment), []);
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1102, "test")]);
    }

    /// E1103 (S-828): a target name that is not a `snake_case` identifier, at
    /// the name in its header, beside the other diagnostics.
    #[test]
    fn a_target_name_is_snake_case() {
        let text = "[package]\nname = \"a\"\n[targets.ok_1]\nkind = \"s\"\nplatform = \"h\"\n\
                    [targets.\"../x\"]\nkind = \"s\"\nplatform = \"h\"\nzz = 1\n[targets.Host]\nkind = \"s\"\nplatform = \"h\"\n";
        let found = diagnostics(text, ManifestForm::File);
        assert_eq!(found, [(Code::E1103, "\"../x\""), (Code::E1102, "zz"), (Code::E1103, "Host")]);
    }

    /// The errors of the reading of the values name the manifest by its file
    /// string and keep the line and the column.
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
            ("[package]\nname = \"a\"\n[[plugin]]\nau = 3\n", "line 4, column 6: `plugin.au`: invalid type"),
        ];
        for (text, e) in cases {
            let err = file(text).unwrap_err();
            assert!(err.starts_with(e) || err.contains(e), "{text:?}: {err}");
        }
        // Beside a diagnostic, the diagnostics are reported (until U2b).
        assert_eq!(diagnostics("[packag]\nname = \"a\"\n", ManifestForm::File), [(Code::E1102, "packag")]);
    }

    /// E1101: a text that is not TOML is one diagnostic at the place of the
    /// TOML parser's error, and no other; a duplicated key is one, and so is
    /// a nesting deeper than the parser's limit (no stack runs out).
    #[test]
    fn a_text_that_is_not_toml_is_one_e1101() {
        let deep = format!("[package]\nname = \"a\"\nzz = 1\nx = {}1{}\n", "[".repeat(100), "]".repeat(100));
        for (text, line) in [
            ("[package\nname = \"a\"\nzz = 1\n", 1),
            ("[package]\nname = \"a\"\nname = \"b\"\nzz = 1\n", 3),
            (deep.as_str(), 4),
            ("[package]\nname = \"a\"\na =", 3),
        ] {
            let r = read_as(text, ManifestForm::File).unwrap();
            assert_eq!(r.diagnostics.len(), 1, "{text:?}: {:?}", r.diagnostics);
            let d = &r.diagnostics[0];
            assert_eq!(d.code, Code::E1101);
            assert_eq!(text[..d.span.start as usize].matches('\n').count() + 1, line, "{text:?}: {d:?}");
            assert!(!d.message.contains('\n'), "{}", d.message);
            assert!(r.manifest.package.value.name.value.is_empty());
        }
        // A reason the parser does not give leaves no `: ` behind.
        let r = read_as("[package]\nname = \"a\"\na =", ManifestForm::File).unwrap();
        assert_eq!(r.diagnostics[0].message, "the manifest is not valid TOML");
        let r = read_as("[package]\nname = \"a\"\na =\n", ManifestForm::File).unwrap();
        assert!(r.diagnostics[0].message.starts_with("the manifest is not valid TOML: invalid"), "{:?}", r.diagnostics);
    }

    /// E1102 names a table only where a header writes it; a dotted key and an
    /// inline table are keys, as written.
    #[test]
    fn an_unknown_table_is_one_a_header_writes() {
        let text = "top.k = 1\n[package]\nname = \"a\"\nfoo.bar = 1\nx = { y = 1 }\n[bogus]\n[[extra]]\n[a.b]\n";
        let mut r = read_as(text, ManifestForm::File).unwrap();
        r.diagnostics.sort_by_key(|d| d.span.start);
        let messages: Vec<&str> = r.diagnostics.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(
            messages,
            [
                "unknown key `top`",
                "unknown key `package.foo`",
                "unknown key `package.x`",
                "unknown table `[bogus]`",
                "unknown table `[[extra]]`",
                "unknown table `[a]`",
            ]
        );
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
                assert!(rows || table::named(t).is_some(), "{}", r.key);
            }
        }
    }
}
