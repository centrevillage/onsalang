//! The one reader of `onsa.toml` (S-99, R-80 (5)): the TOML tree of
//! `toml_edit`, walked by the rows of [`table`], into the typed [`Manifest`]
//! with the places of its keys and values, and the diagnostics of its check
//! (§18.1): every one of the manifest, which is one unit.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, FileId, Span, Stage};
use toml_edit::{ImDocument, Item, TableLike};

use super::table::{self, Field, Names, Read, Rule, Shape, Table};
use super::{Manifest, ManifestExport, ManifestMemory, ManifestPackage, ManifestRead, ManifestTarget, Spanned};
use crate::{ManifestForm, ManifestSource, STD_PACKAGE, STD_VERSION};

/// Read the manifest of `source`, whose places are in `file`. The
/// diagnostics are every one of its check, each independent of the others
/// (E1101, E1102, E1103, the E0200 of a dependency, §18.1); a missing key is
/// still an error of the reading (U2b2), which names the manifest by its file
/// string (`onsa.toml` for a package root, S-234).
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
    let reader = Reader { source, file, diagnostics: RefCell::default(), missing: RefCell::default() };
    let manifest = reader.manifest(doc.as_table());
    let diagnostics = reader.diagnostics.into_inner();
    match reader.missing.into_inner() {
        // A missing key beside a diagnostic: the diagnostics are reported
        // (both stop the command with exit 2; U2b2 makes it an E1104).
        Some(e) if diagnostics.is_empty() => Err(format!("{}: {e}", source.path)),
        _ => Ok(done(manifest, diagnostics)),
    }
}

struct Reader<'s> {
    source: &'s ManifestSource,
    file: FileId,
    diagnostics: RefCell<Vec<Diagnostic>>,
    /// The first key the reader requires that is not written ([`Reader::need`]).
    missing: RefCell<Option<String>>,
}

/// A value read by the shape of its row.
enum Typed<'a> {
    Str(String),
    Bool(bool),
    Int(i64),
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

/// The keys of one table, read by its rows; each is taken once. `wrong`
/// holds the keys written with a value of another type (an E1103 each).
struct Fields<'a> {
    table: Table,
    path: String,
    got: Vec<(Field, Got<'a>)>,
    wrong: Vec<Field>,
}

impl<'s> Reader<'s> {
    fn manifest(&self, root: &dyn TableLike) -> Manifest {
        let mut f = self.fields(Table::Root, root, "");
        let package = self.need(&mut f, Field::Package).map(|g| {
            self.table(g, |f| ManifestPackage {
                name: self.need(f, Field::Name).map(Got::str).unwrap_or_default(),
                edition: f.take(Field::Edition).map(Got::str),
            })
        });
        let dependencies = self.strings(f.take(Field::Dependencies));
        let export = f
            .take(Field::Export)
            .map(|g| self.table(g, |f| ManifestExport { prefix: f.take(Field::Prefix).map(Got::str) }));
        let targets = f.take(Field::Targets).map(|g| self.map(g, |g| self.table(g, |f| self.target(f))));
        // `[[plugin]]` is walked for its keys; its values are U4's.
        for p in f.take(Field::Plugin).map(Got::tables).unwrap_or_default() {
            self.table(p, |f| f.take(Field::Au).map(|g| self.table(g, |_| ())));
        }
        f.done();
        Manifest { package: package.unwrap_or_default(), dependencies, export, targets: targets.unwrap_or_default() }
    }

    fn target(&self, f: &mut Fields) -> ManifestTarget {
        ManifestTarget {
            kind: self.need(f, Field::Kind).map(Got::str).unwrap_or_default(),
            platform: self.need(f, Field::Platform).map(Got::str).unwrap_or_default(),
            lang: f.take(Field::Lang).map(Got::str),
            fp: f.take(Field::Fp).map(Got::str),
            provides: f.take(Field::Provides).map(Got::strs).unwrap_or_default(),
            panic: f.take(Field::Panic).map(Got::str),
            panic_messages: f.take(Field::PanicMessages).map(Got::bool),
            main_frame: f.take(Field::MainFrame).map(Got::str),
            memory: f.take(Field::Memory).map(|g| {
                self.table(g, |f| ManifestMemory {
                    bulk: f.take(Field::Bulk).map(Got::bool),
                    fast_budget: f.take(Field::FastBudget).map(Got::int),
                    bulk_budget: f.take(Field::BulkBudget).map(Got::int),
                })
            }),
            bind: self.strings(f.take(Field::Bind)),
        }
    }

    /// The keys of `t`, the table `table` at `path`, read by its rows.
    fn fields<'a>(&self, table: Table, t: &'a dyn TableLike, path: &str) -> Fields<'a> {
        let mut f = Fields { table, path: path.to_string(), got: Vec::new(), wrong: Vec::new() };
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
            match self.got(row.shape, row.rule, t, key, item, path) {
                Some(g) => f.got.push((row.field, g)),
                None => f.wrong.push(row.field),
            }
        }
        f
    }

    /// The value of `key` of `t` read as `shape`, checked by `rule`. A value
    /// of another type is an E1103 at the value (an element of an array: at
    /// the element, and the others are read) and is not read: none, and a
    /// table is not walked.
    fn got<'a>(
        &self,
        shape: Shape,
        rule: Rule,
        t: &'a dyn TableLike,
        key: &str,
        item: &'a Item,
        path: &str,
    ) -> Option<Got<'a>> {
        let path = dotted(path, key);
        // An implicit table has no span of its own: the place of its key.
        let key_span = key_span(t, key, item);
        let span = item.span().unwrap_or_else(|| key_span.clone());
        let expected = match shape {
            Shape::Str => "a string",
            Shape::Bool => "a boolean",
            Shape::Int => "an integer",
            Shape::Strs => "an array of strings",
            Shape::Table(_) => "a table",
            Shape::Tables(_) => "an array of tables",
        };
        let wrong = |at: Option<Range<usize>>, found: &str| {
            let at = at.unwrap_or_else(|| span.clone());
            self.e1103(at, format!("`{path}` takes {expected}, found {found}"), &[]);
        };
        let value = match shape {
            Shape::Str => item.as_str().map(|s| Typed::Str(s.to_string())),
            Shape::Bool => item.as_bool().map(Typed::Bool),
            Shape::Int => item.as_integer().map(Typed::Int),
            Shape::Strs => item.as_array().map(|a| {
                let each = |v: &toml_edit::Value| {
                    let s = v.as_str();
                    if s.is_none() {
                        wrong(v.span(), v.type_name());
                    }
                    Some(Spanned { value: s?.to_string(), key: key_span.clone(), span: v.span().unwrap_or_default() })
                };
                Typed::Strs(a.iter().filter_map(each).collect())
            }),
            Shape::Table(table) => item.as_table_like().map(|t| Typed::Table(t, table)),
            Shape::Tables(table) => {
                let one = |t: &'a dyn TableLike, at: Option<Range<usize>>| Got {
                    value: Typed::Table(t, table),
                    path: path.clone(),
                    key: key_span.clone(),
                    span: at.unwrap_or_else(|| span.clone()),
                };
                match item.as_array_of_tables() {
                    Some(a) => Some(Typed::Tables(a.iter().map(|t| one(t, t.span())).collect())),
                    None => item.as_array().map(|a| {
                        let each = |v: &'a toml_edit::Value| {
                            let t = v.as_inline_table();
                            if t.is_none() {
                                wrong(v.span(), v.type_name());
                            }
                            Some(one(t?, v.span()))
                        };
                        Typed::Tables(a.iter().filter_map(each).collect())
                    }),
                }
            }
        };
        let Some(value) = value else {
            wrong(None, item.type_name());
            return None;
        };
        let got = Got { value, path, key: key_span, span };
        self.check(rule, &got);
        Some(got)
    }

    /// The E1103 of a value that breaks the rule of its row (§15.3, §14.2),
    /// with the rule in a note (S-597).
    fn check(&self, rule: Rule, got: &Got) {
        let path = &got.path;
        let (message, notes) = match (rule, &got.value) {
            (Rule::OneOf(values, also), Typed::Str(v)) if !values.contains(&v.as_str()) => {
                let list: Vec<String> = values.iter().map(|v| format!("`\"{v}\"`")).collect();
                let mut notes = vec![format!("the values of `{path}` are {}", list.join(", "))];
                notes.extend(also.map(str::to_string));
                (format!("`\"{v}\"` is not a value of `{path}`"), notes)
            }
            (Rule::PackageName, Typed::Str(v)) if v == STD_PACKAGE => (
                format!("the package name cannot be `{STD_PACKAGE}`"),
                vec![format!("`{STD_PACKAGE}` is the name of the embedded standard library (§15.3)")],
            ),
            (Rule::PackageName, Typed::Str(v)) => return self.snake_case(v, got.span.clone(), "package"),
            (Rule::Prefix, Typed::Str(v)) if !is_prefix(v) => (
                format!("`\"{v}\"` is not a `prefix`"),
                vec![
                    "a `prefix` is of lowercase letters, digits and `_`, begins with a letter, ends with `_`, \
                      has no `__` and does not begin with `onsa_` (§14.2)"
                        .to_string(),
                ],
            ),
            (Rule::StdVersion, Typed::Str(v)) if v != STD_VERSION => (
                format!("`\"{v}\"` is not the version of the embedded std"),
                vec![format!("the embedded std is version `{STD_VERSION}` (§15.3)")],
            ),
            (Rule::Bytes, Typed::Int(n)) if *n < 0 => (
                format!("`{path}` is `{n}`, not a number of bytes"),
                vec!["a number of bytes is 0 or more".to_string()],
            ),
            _ => return,
        };
        self.e1103(got.span.clone(), message, &notes);
    }

    /// The table of `got` built by `build` from its keys.
    fn table<T>(&self, got: Got, build: impl FnOnce(&mut Fields) -> T) -> Spanned<T> {
        let (t, table) = got.as_table();
        let mut f = self.fields(table, t, &got.path);
        let value = build(&mut f);
        f.done();
        Spanned { value, key: got.key, span: got.span }
    }

    /// The entries of the table of names of `got` ([`table::named`]), each
    /// built by `each`, and the diagnostics of their names.
    fn map<'a, T>(&self, got: Got<'a>, each: impl Fn(Got<'a>) -> T) -> BTreeMap<String, T> {
        let (t, table) = got.as_table();
        let Some(named) = table::named(table) else {
            onsa_diag::internal::bug(None, format!("`{}` is read as a table of names", got.path));
        };
        let mut out = BTreeMap::new();
        for (key, item) in t.iter() {
            let at = key_span(t, key, item);
            match named.names {
                Names::SnakeCase(what) => self.snake_case(key, at, what),
                // Another package than std: its key, and no more (§15.3, S-827 (d′)).
                Names::Std if key != STD_PACKAGE => {
                    self.push(Feature::ManifestDependency.diagnostic(Stage::Manifest, self.span(at), &[key]));
                    continue;
                }
                Names::Std | Names::Any => {}
            }
            if let Some(g) = self.got(named.shape, named.rule, t, key, item, &got.path) {
                out.insert(key.to_string(), each(g));
            }
        }
        out
    }

    /// A key the reader requires: `[package]`, `name`, `kind` and, as
    /// before the table was closed, `platform` in every target (U3 moves it
    /// to the build, E1104). The first one missing is the error of the
    /// reading; the walk goes on (a key of another type is an E1103 already).
    fn need<'a>(&self, f: &mut Fields<'a>, field: Field) -> Option<Got<'a>> {
        let got = f.take(field);
        if got.is_none() && !f.wrong.contains(&field) {
            let Some(row) = table::row_of(f.table, field) else {
                onsa_diag::internal::bug(None, format!("no row for {field:?} in {:?}", f.table));
            };
            let e = match f.table {
                Table::Root => format!("missing table `[{}]`", row.key),
                _ => format!("`[{}]`: missing key `{}`", f.path, row.key),
            };
            self.missing.borrow_mut().get_or_insert(e);
        }
        got
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
        self.push(d);
    }

    /// The rule of a name the manifest gives (§15.3): a `snake_case`
    /// identifier, as a module name (§2.3), else an E1103 at `at`. The one
    /// place of the rule, for the names of the targets and of the package.
    fn snake_case(&self, name: &str, at: Range<usize>, what: &str) {
        if !onsa_syntax::is_module_name(name) {
            self.e1103(
                at,
                format!("the {what} name `{name}` is not a `snake_case` identifier"),
                &[format!("a {what} name is a `snake_case` identifier, as a module name (§2.3, §15.3)")],
            );
        }
    }

    /// An E1103 at `at`, with `notes` without a place and no candidate (S-597).
    fn e1103(&self, at: Range<usize>, message: String, notes: &[String]) {
        let d = Diagnostic::new(Stage::Manifest, Code::E1103, self.span(at), message);
        self.push(notes.iter().fold(d, |d, n| d.with_rule(n.clone())));
    }

    fn push(&self, d: Diagnostic) {
        self.diagnostics.borrow_mut().push(d);
    }

    fn span(&self, at: Range<usize>) -> Span {
        Span::new(self.file, at.start as u32, at.end as u32)
    }

    /// A table of names whose entries are strings (`[dependencies]`, `bind`); none when not written.
    fn strings(&self, got: Option<Got>) -> BTreeMap<String, Spanned<String>> {
        got.map(|g| self.map(g, Got::str)).unwrap_or_default()
    }
}

/// The form of `prefix` (§14.2): lowercase letters, digits and `_`, from a
/// letter to a `_`, without `__` and not from `onsa_`, the runtime's names.
fn is_prefix(p: &str) -> bool {
    let b = p.as_bytes();
    b.first().is_some_and(u8::is_ascii_lowercase)
        && b.last() == Some(&b'_')
        && b.iter().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == b'_')
        && !p.contains("__")
        && !p.starts_with("onsa_")
}

impl<'a> Fields<'a> {
    fn take(&mut self, field: Field) -> Option<Got<'a>> {
        let i = self.got.iter().position(|(f, _)| *f == field)?;
        Some(self.got.swap_remove(i).1)
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
            let value = match (r.shape, r.rule) {
                (_, Rule::OneOf(values, _)) => format!("\"{}\"", values[values.len() - 1]),
                (_, Rule::Prefix) => "\"x_\"".into(),
                (Shape::Str, _) => "\"x\"".into(),
                (Shape::Bool, _) => "true".into(),
                (Shape::Int, _) => "0".into(),
                (Shape::Strs, _) => "[\"Alloc\"]".into(),
                (Shape::Table(_) | Shape::Tables(_), _) => continue,
            };
            text.push_str(&format!("{} = {value}\n", r.key));
        }
        let m = file(&text).unwrap_or_else(|e| panic!("{text}\n{e}"));
        assert_eq!(m.targets["t"].value.fp.as_ref().unwrap().value, "strict-ftz", "{text}");
        let memory = &m.targets["t"].value.memory.as_ref().unwrap().value;
        assert_eq!((memory.bulk.as_ref().unwrap().value, memory.fast_budget.as_ref().unwrap().value), (true, 0));
        let other = "[package]\nname = \"a\"\n[targets.t]\nkind = \"source\"\nplatform = \"h\"\n\
                     [[plugin]]\nflow = 4\nau = { subtype = 1 }\n";
        file(other).unwrap();
    }

    /// E1102 (§18.1, S-99): every key a table does not know, at the key (a
    /// table at the key of its header), with the keys of its table in a note
    /// and no candidate (S-597). The old names (S-166) and `flows`, `fns`
    /// (S-639) are such keys; a table the reader does not know is not walked.
    #[test]
    fn every_unknown_key_is_an_e1102_with_the_keys_of_its_table() {
        let text = "x = 1\n[package]\nname = \"a\"\nflows = 2\n[export]\nfns = []\n[targets.t]\nkind = \"exe\"\n\
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
        let text = "[package]\nname = \"a\"\n[targets.ok_1]\nkind = \"exe\"\nplatform = \"h\"\n\
                    [targets.\"../x\"]\nkind = \"exe\"\nplatform = \"h\"\nzz = 1\n[targets.Host]\nkind = \"exe\"\nplatform = \"h\"\n";
        let found = diagnostics(text, ManifestForm::File);
        assert_eq!(found, [(Code::E1103, "\"../x\""), (Code::E1102, "zz"), (Code::E1103, "Host")]);
    }

    /// A missing key the reader requires is an error of the reading, which
    /// names the manifest by its file string (U2b2 makes it an E1104); beside
    /// a diagnostic, before or after it in the text, the diagnostics are
    /// reported, and a key of another type is not missing.
    #[test]
    fn a_missing_key_is_an_error_until_a_diagnostic() {
        let cases = [
            ("", "onsa.toml: missing table `[package]`"),
            ("[package]\nedition = \"2026\"\n", "onsa.toml: `[package]`: missing key `name`"),
            (
                "[package]\nname = \"a\"\n[targets.t]\nkind = \"exe\"\n",
                "onsa.toml: `[targets.t]`: missing key `platform`",
            ),
        ];
        for (text, e) in cases {
            assert_eq!(file(text).unwrap_err(), e, "{text:?}");
        }
        assert_eq!(diagnostics("[packag]\nname = \"a\"\n", ManifestForm::File), [(Code::E1102, "packag")]);
        let text = "[package]\nedition = \"2026\"\n[targets.t]\nkind = \"exe\"\nfp = \"loose\"\n";
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "\"loose\"")]);
        assert_eq!(diagnostics("package = 3\n", ManifestForm::File), [(Code::E1103, "3")]);
    }

    /// E1103 (S-99): a value of another type than its row's is at the value
    /// (an element of an array: at the element, beside the others); a value
    /// that should be a table is not walked. Each is independent of the
    /// others, and the walk goes on after it (§18.1).
    #[test]
    fn a_value_of_another_type_is_an_e1103_at_the_value() {
        let text = "[package]\nname = 3\nedition = 2026\n[dependencies]\nstd = 1\n[export]\nprefix = true\n\
                    [targets.t]\nkind = \"exe\"\nplatform = \"h\"\nprovides = [\"Alloc\", 1, \"Fs\", false]\n\
                    panic_messages = \"no\"\nbind = 2\nmemory = { bulk = \"yes\", fast_budget = 1.5, bulk_budget = \"2\" }\n\
                    [targets.u]\nkind = 1\nplatform = \"h\"\n[targets.v]\nkind = \"exe\"\nplatform = \"h\"\n\
                    lang = [\"c\"]\n[targets.w]\nzz = 1\nplatform = \"h\"\n";
        let found = diagnostics(text, ManifestForm::File);
        let expected =
            ["3", "2026", "1", "true", "1", "false", "\"no\"", "2", "\"yes\"", "1.5", "\"2\"", "1", "[\"c\"]"];
        let mut all: Vec<(Code, &str)> = expected.iter().map(|&v| (Code::E1103, v)).collect();
        all.push((Code::E1102, "zz"));
        assert_eq!(found, all);
        let r = read_as(text, ManifestForm::File).unwrap();
        assert!(r.diagnostics.iter().all(|d| d.fixes.is_empty() && d.stage == Stage::Manifest), "{:?}", r.diagnostics);
        let m = r.manifest;
        let provides: Vec<&str> = m.targets["t"].value.provides.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(provides, ["Alloc", "Fs"]);
        for (text, value) in [("targets = 1\n", "1"), ("[targets]\nt = 2\n", "2"), ("plugin = [1, {}]\n", "1")] {
            let text = format!("{text}[package]\nname = \"a\"\n");
            assert_eq!(diagnostics(&text, ManifestForm::File), [(Code::E1103, value)], "{text}");
        }
        // A module of `bind` takes a string (the form of the path is U3's).
        let text = "[package]\nname = \"a\"\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n[targets.t.bind]\n\
                    \"audio.device\" = 3\n\"x\" = \"y\"\n";
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "3")]);
    }

    /// E1103 (S-99, S-597): a value outside the closed list of its key, with
    /// the list in a note and no candidate; `fp` also names `@fp(relaxed)`.
    #[test]
    fn a_value_outside_its_closed_list_is_an_e1103_with_the_list() {
        let text = "[package]\nname = \"a\"\nedition = \"2025\"\n[targets.t]\nkind = \"plugin\"\nplatform = \"h\"\n\
                    lang = \"C\"\nfp = \"relaxed\"\npanic = \"abort\"\nmain_frame = \"heap\"\n\
                    [targets.u]\nkind = \"wasm-worklet\"\nplatform = \"h\"\nlang = \"js\"\nfp = \"strict-ftz\"\n\
                    panic = \"halt\"\nmain_frame = \"static\"\n";
        let mut r = read_as(text, ManifestForm::File).unwrap();
        r.diagnostics.sort_by_key(|d| d.span.start);
        let found: Vec<&str> =
            r.diagnostics.iter().map(|d| &text[d.span.start as usize..d.span.end as usize]).collect();
        assert_eq!(found, ["\"2025\"", "\"plugin\"", "\"C\"", "\"relaxed\"", "\"abort\"", "\"heap\""]);
        let notes = |i: usize| r.diagnostics[i].notes.iter().map(|n| n.message.as_str()).collect::<Vec<_>>();
        assert_eq!(notes(0), ["the values of `package.edition` are `\"2026\"`"]);
        assert_eq!(
            notes(1),
            ["the values of `targets.t.kind` are `\"exe\"`, `\"clap\"`, `\"vst3\"`, `\"au\"`, `\"wasm-worklet\"`, \
                 `\"staticlib\"`, `\"source\"`"]
        );
        assert_eq!(notes(3).len(), 2);
        assert!(notes(3)[1].contains("@fp(relaxed)"), "{:?}", notes(3));
        for d in &r.diagnostics {
            assert_eq!(d.code, Code::E1103);
            assert!(d.fixes.is_empty() && d.notes.iter().all(|n| n.span.is_none()), "{d:?}");
        }
    }

    /// E1103: the package name is a `snake_case` identifier and not `std`
    /// (S-628, R-47), by the rule of the target names.
    #[test]
    fn the_package_name_is_snake_case_and_not_std() {
        for (name, bad) in [("voice_2", false), ("Voice", true), ("my-synth", true), ("", true), ("std", true)] {
            let text = format!("[package]\nname = \"{name}\"\n");
            let r = read_as(&text, ManifestForm::File).unwrap();
            assert_eq!(r.diagnostics.len(), usize::from(bad), "{name}: {:?}", r.diagnostics);
            if bad {
                assert_eq!((r.diagnostics[0].code, r.diagnostics[0].span.start), (Code::E1103, 17), "{name}");
            }
        }
        let r = read_as("[package]\nname = \"std\"\n", ManifestForm::File).unwrap();
        assert!(r.diagnostics[0].notes[0].message.contains("embedded standard library"), "{:?}", r.diagnostics);
    }

    /// E1103: the form of `prefix` (§14.2, S-95, R-121 (2)), written or not
    /// any `@export`.
    #[test]
    fn a_prefix_has_its_form() {
        let good = ["vc_", "my_synth_", "a1_", "x_"];
        let bad = ["", "vc", "Vc_", "_vc_", "1a_", "v__", "a__b_", "vc-_", "onsa_", "onsa_x_", "é_"];
        for (p, ok) in good.iter().map(|p| (p, true)).chain(bad.iter().map(|p| (p, false))) {
            let text = format!("[package]\nname = \"a\"\n[export]\nprefix = \"{p}\"\n");
            let found = diagnostics(&text, ManifestForm::File);
            let expected = if ok { vec![] } else { vec![(Code::E1103, format!("\"{p}\""))] };
            let found: Vec<(Code, String)> = found.into_iter().map(|(c, t)| (c, t.to_string())).collect();
            assert_eq!(found, expected, "{p:?}");
        }
    }

    /// The version of std is the embedded std's, else an E1103 with it in a
    /// note (S-83, R-88 (2)); each package other than std is an E0200 at its
    /// key, whose value is not read (S-154, S-827 (d′)).
    #[test]
    fn std_is_the_one_dependency_at_the_embedded_version() {
        let text = format!(
            "[package]\nname = \"a\"\n[dependencies]\nfx = \"1.0.0\"\nstd = \"{}\"\nfy = 3\nfz = {{ path = 1 }}\n",
            crate::STD_VERSION
        );
        assert_eq!(
            diagnostics(&text, ManifestForm::File),
            [(Code::E0200, "fx"), (Code::E0200, "fy"), (Code::E0200, "fz")]
        );
        let r = read_as(&text, ManifestForm::File).unwrap();
        assert!(r.diagnostics.iter().all(|d| d.stage == Stage::Manifest && d.message.contains("`std`")));
        let text = "[package]\nname = \"a\"\n[dependencies]\nstd = \"0.0.0\"\n";
        let r = read_as(text, ManifestForm::File).unwrap();
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "\"0.0.0\"")]);
        assert!(r.diagnostics[0].notes[0].message.contains(crate::STD_VERSION), "{:?}", r.diagnostics);
    }

    /// `fast_budget` and `bulk_budget` are numbers of bytes, 0 or more (S-827).
    #[test]
    fn a_budget_is_0_or_more() {
        let text = "[package]\nname = \"a\"\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n[targets.t.memory]\n\
                    fast_budget = 0\nbulk_budget = -1\n[targets.u]\nkind = \"exe\"\nplatform = \"h\"\n\
                    memory = { fast_budget = -9223372036854775808, bulk_budget = 9223372036854775807 }\n";
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "-1"), (Code::E1103, "-9223372036854775808")]);
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
