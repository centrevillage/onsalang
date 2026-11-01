//! The one reader of `onsa.toml` (S-99, R-80 (5)): the TOML tree of
//! `toml_edit`, walked by the rows of [`table`], into the typed [`Manifest`]
//! with the places of its keys and values, and the diagnostics of its check
//! (§18.1): every one of the manifest, which is one unit.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;

use onsa_diag::unsupported::Feature;
use onsa_diag::{Code, Diagnostic, FileId, Fix, Span, Stage};
use toml_edit::{ImDocument, Item, TableLike};

use super::table::{self, Field, Names, Need, Read, Row, Rule, Shape, Table, Unsupported};
use super::{Manifest, ManifestExport, ManifestMemory, ManifestPackage, ManifestRead, ManifestTarget, Spanned};
use crate::{ManifestForm, ManifestSource, STD_PACKAGE, STD_VERSION};

/// Read the manifest of `source`, whose places are in `file`. The
/// diagnostics are every one of its check, each independent of the others
/// (E1101, E1102, E1103, E1104, the E0200 of a dependency, §18.1).
pub fn read(source: &ManifestSource, file: FileId) -> ManifestRead {
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
                shown(&format!("the manifest is not valid TOML{message}")),
            );
            return done(Manifest::default(), vec![d]);
        }
    };
    let reader = Reader {
        source,
        file,
        diagnostics: RefCell::default(),
        target: RefCell::default(),
        package: RefCell::default(),
        missing_prefix: RefCell::default(),
    };
    let manifest = reader.manifest(doc.as_table());
    done(manifest, reader.diagnostics.into_inner())
}

/// `s` with its characters that print as something else (a control
/// character, a line end) escaped, as `\u{1b}` and `\n`: the one place a
/// text of the manifest goes into a message (U2b1's review).
pub fn shown(s: &str) -> String {
    s.chars().map(|c| if matches!(c, '"' | '\'') { c.to_string() } else { c.escape_debug().to_string() }).collect()
}

/// `d` with its texts [`shown`].
fn escaped(mut d: Diagnostic) -> Diagnostic {
    d.message = shown(&d.message);
    for n in &mut d.notes {
        n.message = shown(&n.message);
    }
    d
}

struct Reader<'s> {
    source: &'s ManifestSource,
    file: FileId,
    diagnostics: RefCell<Vec<Diagnostic>>,
    /// The diagnostics of the build of the target being read ([`ManifestTarget::build_diagnostics`]).
    target: RefCell<Vec<Diagnostic>>,
    /// The package name as read, for the candidate of `prefix` (`<package>_`).
    package: RefCell<String>,
    /// [`Manifest::missing_prefix`].
    missing_prefix: RefCell<Option<Diagnostic>>,
}

/// How a table is written (TOML), which decides where a key it lacks is
/// inserted ([`Reader::insertion`], S-836).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Written {
    /// Under its header `[a]` (or `[[a]]`).
    Header,
    /// By dotted keys `a.k = …`.
    Dotted,
    /// Only by the header of a table under it (`[a.b]`), or not at all.
    Absent,
    /// `a = { … }`, which a line cannot extend: no candidate (S-836).
    Inline,
}

/// A value read by the shape of its row.
enum Typed<'a> {
    Str(String),
    Bool(bool),
    Int(i64),
    Strs(Vec<Spanned<String>>),
    Table(&'a dyn TableLike, Table, Written),
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
/// `key` is the place of the E1104 of a key it lacks: the key that names
/// the table, or the start of the body when it is not written.
struct Fields<'a> {
    table: Table,
    path: String,
    got: Vec<(Field, Got<'a>)>,
    wrong: Vec<Field>,
    key: Range<usize>,
    written: Written,
}

impl<'s> Reader<'s> {
    fn manifest(&self, root: &dyn TableLike) -> Manifest {
        // The body starts after the line `// onsa.toml` of a fragment.
        let body = match self.source.form {
            ManifestForm::File => 0,
            ManifestForm::Fragment => self.source.text.find('\n').map_or(0, |i| i + 1),
        };
        let mut f = self.fields(Table::Root, root, "", body..body, Written::Header);
        let package = self.need_table(&mut f, Field::Package, |f| ManifestPackage {
            name: self.need(f, Field::Name, None, None).map(Got::str).unwrap_or_default(),
            edition: self.need(f, Field::Edition, None, None).map(Got::str),
        });
        self.package.replace(package.value.name.value.clone());
        let dependencies = self.strings(f.take(Field::Dependencies));
        let export = self.need_table(&mut f, Field::Export, |f| ManifestExport {
            prefix: self.need(f, Field::Prefix, None, None).map(Got::str),
        });
        let targets = f.take(Field::Targets).map(|g| self.map(g, |g| self.table(g, |f| self.target(f))));
        // `[[plugin]]` is walked for its keys; its values are U4's.
        for p in f.take(Field::Plugin).map(Got::tables).unwrap_or_default() {
            self.table(p, |f| f.take(Field::Au).map(|g| self.table(g, |_| ())));
        }
        f.done();
        let missing_prefix = self.missing_prefix.take();
        Manifest { package, dependencies, export, targets: targets.unwrap_or_default(), missing_prefix }
    }

    fn target(&self, f: &mut Fields) -> ManifestTarget {
        let kind = self.need(f, Field::Kind, None, None).map(Got::str);
        let k = kind.as_ref().map(|k| k.value.as_str());
        let lang = self.need(f, Field::Lang, k, None).map(Got::str);
        let platform = self.need(f, Field::Platform, k, lang.as_ref().map(|l| l.value.as_str())).map(Got::str);
        let mut t = ManifestTarget {
            kind: kind.unwrap_or_default(),
            platform,
            lang,
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
            build_diagnostics: Vec::new(),
        };
        if let Some(p) = &t.platform {
            self.platform(&t.kind, p);
        }
        // Its keys and those of its tables are read: every diagnostic of its build is made.
        t.build_diagnostics = self.target.take();
        t
    }

    /// The keys of `t`, the table `table` at `path`, read by its rows.
    fn fields<'a>(
        &self,
        table: Table,
        t: &'a dyn TableLike,
        path: &str,
        key: Range<usize>,
        written: Written,
    ) -> Fields<'a> {
        let mut f = Fields { table, path: path.to_string(), got: Vec::new(), wrong: Vec::new(), key, written };
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
                Some(g) => {
                    self.unsupported(row, &g);
                    f.got.push((row.field, g))
                }
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
            Shape::Table(table) => {
                let written = match item {
                    Item::Table(t) if t.is_dotted() => Written::Dotted,
                    Item::Table(t) if t.is_implicit() => Written::Absent,
                    Item::Table(_) => Written::Header,
                    _ => Written::Inline,
                };
                item.as_table_like().map(|t| Typed::Table(t, table, written))
            }
            Shape::Tables(table) => {
                let one = |t: &'a dyn TableLike, at: Option<Range<usize>>, written| Got {
                    value: Typed::Table(t, table, written),
                    path: path.clone(),
                    key: key_span.clone(),
                    span: at.unwrap_or_else(|| span.clone()),
                };
                match item.as_array_of_tables() {
                    Some(a) => Some(Typed::Tables(a.iter().map(|t| one(t, t.span(), Written::Header)).collect())),
                    None => item.as_array().map(|a| {
                        let each = |v: &'a toml_edit::Value| {
                            let t = v.as_inline_table();
                            if t.is_none() {
                                wrong(v.span(), v.type_name());
                            }
                            Some(one(t?, v.span(), Written::Inline))
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
            (Rule::ModulePath, Typed::Str(v)) => return self.module_path(v, got.span.clone()),
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

    /// The E0200 of each value of `got` its row does not support, for the
    /// build of its target (S-154, S-824): at the value, an element, or the
    /// key of a table.
    fn unsupported(&self, row: &Row, got: &Got) {
        let Some((values, feature)) = row.unsupported else { return };
        let at = |span: &Range<usize>, details: &[&str]| {
            self.report(true, feature.diagnostic(Stage::Manifest, self.span(span.clone()), details))
        };
        match (values, &got.value) {
            // A value outside the closed list of the rule is an E1103 alone (S-827).
            (Unsupported::Except(vs), Typed::Str(v))
                if !vs.contains(&v.as_str())
                    && !matches!(row.rule, Rule::OneOf(all, _) if !all.contains(&v.as_str())) =>
            {
                at(&got.span, &[v])
            }
            (Unsupported::Except(vs), Typed::Strs(es)) => {
                es.iter().filter(|e| !vs.contains(&e.value.as_str())).for_each(|e| at(&e.span, &[&e.value]))
            }
            (Unsupported::True, Typed::Bool(true)) | (Unsupported::Any, Typed::Int(_)) => at(&got.span, &[]),
            (Unsupported::Any, Typed::Table(t, ..)) if !t.is_empty() => at(&got.key, &[]),
            _ => {}
        }
    }

    /// The E0200 of the build of a target with the platform `p`, written
    /// whether it is required or not (§15.3): a platform this version does
    /// not know (S-824); a known one other than the host for a kind of
    /// [`table::TOOLCHAIN`] the version supports, at the kind (S-161).
    fn platform(&self, kind: &Spanned<String>, p: &Spanned<String>) {
        let (k, kinds) = (kind.value.as_str(), row(Table::Target, Field::Kind).unsupported);
        let supported = matches!(kinds, Some((Unsupported::Except(vs), _)) if vs.contains(&k));
        let d = match crate::build::platform(&p.value) {
            Err(_) => Feature::ManifestPlatform
                .diagnostic(Stage::Manifest, self.span(p.span.clone()), &[&p.value])
                .with_rule(crate::build::platforms_note()),
            Ok(t) if !t.is_host() && supported && table::TOOLCHAIN.contains(&k) => {
                Feature::ManifestCross.diagnostic(Stage::Manifest, self.span(kind.span.clone()), &[k, &p.value])
            }
            Ok(_) => return,
        };
        self.report(true, d);
    }

    /// The table of `got` built by `build` from its keys.
    fn table<T>(&self, got: Got, build: impl FnOnce(&mut Fields) -> T) -> Spanned<T> {
        let (t, table, written) = got.as_table();
        let mut f = self.fields(table, t, &got.path, got.key.clone(), written);
        let value = build(&mut f);
        f.done();
        Spanned { value, key: got.key, span: got.span }
    }

    /// The entries of the table of names of `got` ([`table::named`]), each
    /// built by `each`, and the diagnostics of their names.
    fn map<'a, T>(&self, got: Got<'a>, each: impl Fn(Got<'a>) -> T) -> BTreeMap<String, T> {
        let (t, table, _) = got.as_table();
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
                Names::ModulePath => self.module_path(key, at),
                Names::Std => {}
            }
            if let Some(g) = self.got(named.shape, named.rule, t, key, item, &got.path) {
                out.insert(key.to_string(), each(g));
            }
        }
        out
    }

    /// A key its row requires ([`Need`], §15.3), in a target of `kind` and
    /// `lang` as read. Each one missing is an E1104 at [`Fields::key`], with
    /// the insertion of its value when its closed list has one value
    /// (S-597), or of `<package>_` when it is a `prefix` (§14.2); a key of
    /// another type is not missing (an E1103 already).
    fn need<'a>(&self, f: &mut Fields<'a>, field: Field, kind: Option<&str>, lang: Option<&str>) -> Option<Got<'a>> {
        let got = f.take(field);
        let row = row(f.table, field);
        let build = match row.need {
            Need::No => return got,
            Need::Always | Need::Exports => false,
            Need::Target { kinds, or, build } => {
                let k = kind.is_some_and(|k| kinds.contains(&k));
                if !k && !or.is_some_and(|(k, l)| kind == Some(k) && lang == Some(l)) {
                    return got;
                }
                build
            }
        };
        if got.is_none() && !f.wrong.contains(&field) {
            let path = dotted(&f.path, row.key);
            let d = Diagnostic::new(
                Stage::Manifest,
                Code::E1104,
                self.span(f.key.clone()),
                format!("missing key `{path}`"),
            );
            let value = match row.rule {
                Rule::OneOf([only], _) => Some(only.to_string()),
                Rule::Prefix => Some(format!("{}_", self.package.borrow())).filter(|p| is_prefix(p)),
                _ => None,
            };
            let fix = value.and_then(|v| self.insertion(f, row.key, &format!("\"{v}\"")));
            let d = fix.into_iter().fold(d, Diagnostic::with_fix);
            match row.need {
                Need::Exports => drop(self.missing_prefix.replace(Some(escaped(d)))),
                _ => self.report(build, d),
            }
        }
        got
    }

    /// A table the reader requires, built by `build`; one not written has
    /// every key missing (one of another type is an E1103 already).
    fn need_table<T: Default>(&self, f: &mut Fields, field: Field, build: impl FnOnce(&mut Fields) -> T) -> Spanned<T> {
        if let Some(g) = f.take(field) {
            return self.table(g, build);
        }
        let row = row(f.table, field);
        let (Shape::Table(table), false, Need::Always | Need::Exports) =
            (row.shape, f.wrong.contains(&field), row.need)
        else {
            return Spanned::default();
        };
        let path = dotted(&f.path, row.key);
        let mut absent =
            Fields { table, path, got: Vec::new(), wrong: Vec::new(), key: f.key.clone(), written: Written::Absent };
        Spanned { value: build(&mut absent), key: f.key.clone(), span: f.key.clone() }
    }

    /// The candidate inserting `key = value` in the table of `f` (S-597,
    /// S-836): a line after its header; a dotted key `a.key` at the head of
    /// the line of its key, before every header (a table of the top level);
    /// `[a]` and the line at the end of the manifest when it has no header
    /// (not before a dotted key of the top level, which it would take in);
    /// none in an inline table, which a line cannot extend (the candidate
    /// adds lines only, S-836). Every line is a comment line in a fragment.
    fn insertion(&self, f: &Fields, key: &str, value: &str) -> Option<Fix> {
        let text = self.source.text.as_str();
        let line = format!("{key} = {value}");
        let (at, lines) = match f.written {
            Written::Header => (text[f.key.end..].find('\n').map(|i| f.key.end + i + 1), vec![line.clone()]),
            Written::Dotted => (Some(line_head(text, f.key.start)), vec![format!("{}.{line}", f.path)]),
            Written::Absent => (None, vec![format!("[{}]", f.path), line.clone()]),
            Written::Inline => return None,
        };
        let mark = if self.source.form == ManifestForm::Fragment { "// " } else { "" };
        let mut insert: String = lines.iter().map(|l| format!("{mark}{l}\n")).collect();
        let at = at.unwrap_or_else(|| {
            if !text.is_empty() && !text.ends_with('\n') {
                insert.insert(0, '\n');
            }
            text.len()
        });
        Some(Fix::insert(format!("insert `{line}`"), self.file, at as u32, insert))
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

    /// The form of a module path of `bind` (§15.2, §15.3): `snake_case`
    /// module names (§2.3) joined by `.`, else an E1103 at `at` (S-827).
    fn module_path(&self, path: &str, at: Range<usize>) {
        if !path.split('.').all(onsa_syntax::is_module_name) {
            let note = "a module path is `snake_case` module names joined by `.` (§2.3, §15.2)".to_string();
            self.e1103(at, format!("`\"{path}\"` is not a module path"), &[note]);
        }
    }

    /// An E1103 at `at`, with `notes` without a place and no candidate (S-597).
    fn e1103(&self, at: Range<usize>, message: String, notes: &[String]) {
        let d = Diagnostic::new(Stage::Manifest, Code::E1103, self.span(at), message);
        self.push(notes.iter().fold(d, |d, n| d.with_rule(n.clone())));
    }

    fn push(&self, d: Diagnostic) {
        self.report(false, d);
    }

    /// `d` in the check of every command, or with `build` in the build of the target being read.
    fn report(&self, build: bool, d: Diagnostic) {
        let into = if build { &self.target } else { &self.diagnostics };
        into.borrow_mut().push(escaped(d));
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

    fn as_table(&self) -> (&'a dyn TableLike, Table, Written) {
        match self.value {
            Typed::Table(t, table, written) => (t, table, written),
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

/// The row of `field` in `table`, which the reader asks for.
fn row(table: Table, field: Field) -> &'static table::Row {
    table::row_of(table, field)
        .unwrap_or_else(|| onsa_diag::internal::bug(None, format!("no row for {field:?} in {table:?}")))
}

/// The head of the line of `at` (after a byte order mark at the start).
fn line_head(text: &str, at: usize) -> usize {
    text[..at].rfind('\n').map_or(if text.starts_with('\u{feff}') { 3 } else { 0 }, |i| i + 1)
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

    fn read_as(text: &str, form: ManifestForm) -> ManifestRead {
        read(&source(text, form), FileId(0))
    }

    /// The manifest of `text`, which has no diagnostic.
    fn file(text: &str) -> Manifest {
        let r = read_as(text, ManifestForm::File);
        assert!(r.diagnostics.is_empty(), "{text:?}: {:?}", r.diagnostics);
        r.manifest
    }

    /// The codes and the texts of the places of the diagnostics of `text`,
    /// in the order of the text (the walk's order is not the printed one).
    fn diagnostics(text: &str, form: ManifestForm) -> Vec<(Code, &str)> {
        let mut r = read_as(text, form);
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
        let m = file(FULL);
        let at = |r: &Range<usize>| &FULL[r.clone()];
        let p = &m.package.value;
        assert_eq!((p.name.value.as_str(), at(&p.name.key), at(&p.name.span)), ("voice", "name", "\"voice\""));
        assert_eq!(p.edition.as_ref().unwrap().value, "2026");
        assert_eq!(at(&m.package.key), "package");
        assert_eq!(m.dependencies["std"].value, "0.1.0");
        assert_eq!(at(&m.dependencies["std"].key), "std");
        assert_eq!(m.export.value.prefix.as_ref().unwrap().value, "vc_");
        let t = &m.targets["daisy"];
        assert_eq!(at(&t.key), "daisy");
        assert!(at(&t.span).starts_with("[targets.daisy]"), "{:?}", at(&t.span));
        let t = &t.value;
        assert_eq!(
            (t.kind.value.as_str(), t.platform.as_ref().unwrap().value.as_str()),
            ("staticlib", "thumbv7em-none-eabihf")
        );
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
        let m = file(&text);
        assert_eq!(m.targets["t"].value.fp.as_ref().unwrap().value, "strict-ftz", "{text}");
        let memory = &m.targets["t"].value.memory.as_ref().unwrap().value;
        assert_eq!((memory.bulk.as_ref().unwrap().value, memory.fast_budget.as_ref().unwrap().value), (true, 0));
        let other = "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"source\"\nplatform = \"h\"\nlang = \"c\"\n\
                     [[plugin]]\nflow = 4\nau = { subtype = 1 }\n";
        file(other);
    }

    /// E1102 (§18.1, S-99): every key a table does not know, at the key (a
    /// table at the key of its header), with the keys of its table in a note
    /// and no candidate (S-597). The old names (S-166) and `flows`, `fns`
    /// (S-639) are such keys; a table the reader does not know is not walked.
    #[test]
    fn every_unknown_key_is_an_e1102_with_the_keys_of_its_table() {
        let text = "x = 1\n[package]\nname = \"a\"\nedition = \"2026\"\nflows = 2\n[export]\nfns = []\n[targets.t]\nkind = \"exe\"\n\
                    platform = \"h\"\nnumeric = \"strict\"\n[targets.t.memory]\nbulk_threshold = 64\n\
                    [targets.t.mem]\nanything = 1\n[[plugin]]\nwhat = 4\nau = { zz = 1 }\n[[extra]]\n";
        let found = diagnostics(text, ManifestForm::File);
        let expected = ["x", "flows", "fns", "numeric", "bulk_threshold", "mem", "what", "zz", "extra"];
        assert_eq!(found, expected.map(|k| (Code::E1102, k)));
        let mut r = read_as(text, ManifestForm::File);
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
        let text = "\n[package]\nname = \"a\"\nedition = \"2026\"\n[test]\nmode = 1\n[[test.fix]]\nk = 2\n";
        assert_eq!(diagnostics(text, ManifestForm::Fragment), []);
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1102, "test")]);
    }

    /// E1103 (S-828): a target name that is not a `snake_case` identifier, at
    /// the name in its header, beside the other diagnostics.
    #[test]
    fn a_target_name_is_snake_case() {
        let text = "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.ok_1]\nkind = \"exe\"\nplatform = \"h\"\n\
                    [targets.\"../x\"]\nkind = \"exe\"\nplatform = \"h\"\nzz = 1\n[targets.Host]\nkind = \"exe\"\nplatform = \"h\"\n";
        let found = diagnostics(text, ManifestForm::File);
        assert_eq!(found, [(Code::E1103, "\"../x\""), (Code::E1102, "zz"), (Code::E1103, "Host")]);
    }

    /// E1104 (S-99, §15.3): every required key missing is one, at the key
    /// naming its table (the start of the body when the table is not
    /// written); a key of another type is not missing, and `lang` is
    /// required by `kind = "source"` only (not by a kind not read).
    #[test]
    fn every_missing_required_key_is_an_e1104() {
        let text = "[package]\nedition = \"2026\"\n[targets.t]\nplatform = \"h\"\n[targets.s]\nkind = \"source\"\n\
                    platform = \"h\"\n[targets.u]\nkind = 1\nplatform = \"h\"\n[targets.e]\nkind = \"exe\"\n\
                    [targets.m.memory]\nbulk = true\n";
        let r = read_as(text, ManifestForm::File);
        let mut found: Vec<(&str, &str)> = r
            .diagnostics
            .iter()
            .map(|d| (&text[d.span.start as usize..d.span.end as usize], d.message.as_str()))
            .collect();
        found.sort();
        let expected = [
            ("1", "`targets.u.kind` takes a string, found integer"),
            ("m", "missing key `targets.m.kind`"),
            ("package", "missing key `package.name`"),
            ("s", "missing key `targets.s.lang`"),
            ("t", "missing key `targets.t.kind`"),
        ];
        assert_eq!(found, expected);
        let e1104: Vec<&Diagnostic> = r.diagnostics.iter().filter(|d| d.code == Code::E1104).collect();
        assert!(e1104.len() == 4 && e1104.iter().all(|d| d.stage == Stage::Manifest && d.fixes.is_empty()));
        // No `[package]`: its two keys at the start of the body (a fragment's after `// onsa.toml`).
        for (form, text, at) in [(ManifestForm::File, "# c\n\n[targets]\n", 0), (ManifestForm::Fragment, "    \n\n", 5)]
        {
            let r = read_as(text, form);
            let found: Vec<(u32, u32, usize)> =
                r.diagnostics.iter().map(|d| (d.span.start, d.span.end, d.fixes.len())).collect();
            assert_eq!(found, [(at, at, 0), (at, at, 1)], "{text:?}");
        }
        // Of another type: an E1103, and not missing.
        for text in ["package = 1\n", "[package]\nname = 3\nedition = 2026\n"] {
            assert!(diagnostics(text, ManifestForm::File).iter().all(|(c, _)| *c == Code::E1103), "{text}");
        }
    }

    /// The text after the candidate of the E1104 of `edition` of `text`.
    fn fixed(text: &str, form: ManifestForm) -> Option<String> {
        let r = read_as(text, form);
        let d = r.diagnostics.iter().find(|d| d.message == "missing key `package.edition`").unwrap();
        let fix = d.fixes.first()?;
        let mut out = text.to_string();
        let e = &fix.edits()[0];
        out.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
        Some(out)
    }

    /// The candidate of `edition` (S-597, S-836) is a line where the form of
    /// `[package]` puts a key, which leaves the keys of the other tables
    /// where they were; after it the manifest has no E1104 of `edition` and no
    /// new diagnostic. An inline table has none.
    #[test]
    fn the_candidate_of_edition_is_a_line_where_the_table_takes_it() {
        let cases = [
            ("[package]\nname = \"a\"\n", "[package]\nedition = \"2026\"\nname = \"a\"\n"),
            (
                "[package] # p\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n",
                "[package] # p\nedition = \"2026\"\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n",
            ),
            ("name = 1\n[package]", "name = 1\n[package]\nedition = \"2026\"\n"),
            (
                "targets.t.kind = \"exe\"\ntargets.t.platform = \"h\"\npackage.name = \"a\"\n",
                "targets.t.kind = \"exe\"\ntargets.t.platform = \"h\"\npackage.edition = \"2026\"\npackage.name = \"a\"\n",
            ),
            ("\u{feff}package.name = \"a\"", "\u{feff}package.edition = \"2026\"\npackage.name = \"a\""),
            (
                "targets.t.kind = \"exe\"\ntargets.t.platform = \"h\"",
                "targets.t.kind = \"exe\"\ntargets.t.platform = \"h\"\n[package]\nedition = \"2026\"\n",
            ),
            ("[package.x]\ny = 1\n", "[package.x]\ny = 1\n[package]\nedition = \"2026\"\n"),
        ];
        for (text, after) in cases {
            let new = fixed(text, ManifestForm::File).unwrap();
            assert_eq!(new, after, "{text:?}");
            let r = read_as(&new, ManifestForm::File);
            let before = read_as(text, ManifestForm::File).diagnostics.len();
            assert_eq!(r.diagnostics.len(), before - 1, "{new:?}: {:?}", r.diagnostics);
            assert!(r.diagnostics.iter().all(|d| d.message != "missing key `package.edition`"), "{new:?}");
        }
        let text = "    \n[package]\nname = \"a\"\n";
        assert_eq!(
            fixed(text, ManifestForm::Fragment).unwrap(),
            "    \n[package]\n// edition = \"2026\"\nname = \"a\"\n"
        );
        let text = "    \n[test]\nmode = \"check\"\n";
        let after = "    \n[test]\nmode = \"check\"\n// [package]\n// edition = \"2026\"\n";
        assert_eq!(fixed(text, ManifestForm::Fragment).unwrap(), after);
        assert_eq!(fixed("package = { name = \"a\" }\n", ManifestForm::File), None);
    }

    /// The E1104 of a `prefix` not written (§14.2, S-832) is the build's,
    /// not the check's ([`Manifest::missing_prefix`]): at the key of
    /// `[export]`, or the start of the body without it. Its candidate (S-597,
    /// S-836) is `prefix = "<package>_"` where that is a `prefix`, as a line
    /// where `[export]` takes it, and none in an inline table; after it the
    /// manifest has no E1104 of `prefix` and no diagnostic.
    #[test]
    fn a_prefix_not_written_is_an_e1104_of_the_build_with_the_line_of_its_package() {
        let head = |name: &str| format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n");
        let cases = [
            ("a", "", Some("[export]\nprefix = \"a_\"\n")),
            ("my_synth", "[export] # e\n[targets.t]\nkind = \"source\"\nlang = \"c\"\n", None),
            ("v2", "export.x = 1\n", None),
            ("a", "export = {}\n", None),
            ("onsa", "", None),
            ("onsa_tools", "", None),
            ("synth_", "", None),
        ];
        for (name, rest, appended) in cases {
            // A key of the top level is before every header.
            let (top, dotted) = (rest.starts_with("export "), rest.starts_with("export."));
            let text = if top || dotted { format!("{rest}{}", head(name)) } else { format!("{}{rest}", head(name)) };
            let r = read_as(&text, ManifestForm::File);
            assert_eq!(r.diagnostics.iter().filter(|d| d.code != Code::E1102).count(), 0, "{text:?}");
            let d = r.manifest.missing_prefix.unwrap_or_else(|| panic!("{text:?}: no E1104"));
            assert_eq!(
                (d.code, d.stage, d.message.as_str()),
                (Code::E1104, Stage::Manifest, "missing key `export.prefix`")
            );
            let place = &text[d.span.start as usize..d.span.end as usize];
            assert_eq!(place, if rest.is_empty() { "" } else { "export" }, "{text:?}");
            let fixed = d.fixes.first().map(|fix| {
                let (e, mut out) = (&fix.edits()[0], text.clone());
                out.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
                out
            });
            let want = match (appended, rest) {
                (Some(a), _) => Some(format!("{text}{a}")),
                (None, r) if r.starts_with("[export]") => {
                    Some(text.replace("# e\n", &format!("# e\nprefix = \"{name}_\"\n")))
                }
                (None, _) if dotted => Some(text.replace("export.x", "export.prefix = \"v2_\"\nexport.x")),
                (None, _) => None,
            };
            assert_eq!(fixed, want, "{text:?}");
            if let Some(new) = fixed {
                let again = read_as(&new, ManifestForm::File);
                assert!(again.manifest.missing_prefix.is_none(), "{new:?}");
                assert_eq!(again.diagnostics.len(), r.diagnostics.len(), "{new:?}: {:?}", again.diagnostics);
            }
        }
        // Written, or of another type (an E1103): none.
        for text in ["[export]\nprefix = \"a_\"\n", "export = 1\n", "[export]\nprefix = 1\n"] {
            let text = format!("{text}{}", head("a"));
            assert!(read_as(&text, ManifestForm::File).manifest.missing_prefix.is_none(), "{text}");
        }
        // A fragment: comment lines at its end.
        let r = read_as(&format!("    \n{}", head("a")), ManifestForm::Fragment);
        let fix = &r.manifest.missing_prefix.unwrap().fixes[0];
        assert_eq!(fix.edits()[0].replace, "// [export]\n// prefix = \"a_\"\n");
    }

    /// A text of the manifest in a message or a note has its control
    /// characters and line ends escaped.
    #[test]
    fn a_text_in_a_message_is_escaped() {
        let r = read_as(
            "[package]\nname = \"a\\u001b[31mX\\nY\"\nedition = \"2026\"\n\"k\\u0007\" = 1\n",
            ManifestForm::File,
        );
        let mut messages: Vec<&str> = r.diagnostics.iter().map(|d| d.message.as_str()).collect();
        messages.sort();
        assert_eq!(
            messages,
            ["the package name `a\\u{1b}[31mX\\nY` is not a `snake_case` identifier", "unknown key `package.k\\u{7}`"]
        );
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
                    lang = [\"c\"]\n[targets.w]\nzz = 1\nkind = \"exe\"\nplatform = \"h\"\n";
        let found = diagnostics(text, ManifestForm::File);
        let expected =
            ["3", "2026", "1", "true", "1", "false", "\"no\"", "2", "\"yes\"", "1.5", "\"2\"", "1", "[\"c\"]"];
        let mut all: Vec<(Code, &str)> = expected.iter().map(|&v| (Code::E1103, v)).collect();
        all.push((Code::E1102, "zz"));
        assert_eq!(found, all);
        let r = read_as(text, ManifestForm::File);
        assert!(r.diagnostics.iter().all(|d| d.fixes.is_empty() && d.stage == Stage::Manifest), "{:?}", r.diagnostics);
        let m = r.manifest;
        let provides: Vec<&str> = m.targets["t"].value.provides.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(provides, ["Alloc", "Fs"]);
        for (text, value) in [("targets = 1\n", "1"), ("[targets]\nt = 2\n", "2"), ("plugin = [1, {}]\n", "1")] {
            let text = format!("{text}[package]\nname = \"a\"\nedition = \"2026\"\n");
            assert_eq!(diagnostics(&text, ManifestForm::File), [(Code::E1103, value)], "{text}");
        }
        // A module of `bind` takes a string (the form of the path is U3's).
        let text = "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n[targets.t.bind]\n\
                    \"audio.device\" = 3\n\"x\" = \"y\"\n";
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "3")]);
    }

    /// The codes and the texts of the places of the diagnostics of the build
    /// of `target` that need no source, in the order of the text.
    fn built<'a>(text: &'a str, target: &str) -> Vec<(Code, &'a str)> {
        let mut r = read_as(text, ManifestForm::File);
        let t = &mut r.manifest.targets.get_mut(target).unwrap().value;
        assert!(t.build_diagnostics.iter().all(|d| d.stage == Stage::Manifest && d.fixes.is_empty()));
        t.build_diagnostics.sort_by_key(|d| d.span.start);
        t.build_diagnostics.iter().map(|d| (d.code, &text[d.span.start as usize..d.span.end as usize])).collect()
    }

    /// S-154, S-824, S-825, S-827: each value a target's row does not support
    /// is an E0200 of the build of that target only (not of the check), at
    /// the value, an element of `provides` or the key of a `bind` with an
    /// entry; the default values pass; a value of another type or outside the
    /// closed list is an E1103 only; a budget below 0 is both.
    #[test]
    fn the_unsupported_values_of_a_target_are_e0200s_of_its_build() {
        let text = "[package]\nname = \"a\"\nedition = \"2026\"\n\
                    [targets.t]\nkind = \"exe\"\nplatform = \"host\"\nlang = \"js\"\nfp = \"strict-ftz\"\n\
                    provides = [\"Alloc\", \"Fs\", \"Io\"]\nmain_frame = \"static\"\n\
                    memory = { bulk = true, fast_budget = 0, bulk_budget = -1 }\nbind.\"a.b\" = \"c\"\n\
                    [targets.u]\nkind = \"clap\"\nplatform = \"host\"\n[targets.u.bind]\nm = \"n\"\n\
                    [targets.d]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nfp = \"strict\"\nprovides = []\n\
                    main_frame = \"stack\"\n[targets.d.memory]\nbulk = false\n[targets.d.bind]\n\
                    [targets.e]\nkind = \"dll\"\nplatform = \"host\"\nfp = \"ftz\"\nprovides = [1]\nmain_frame = 2\n\
                    memory = { bulk = \"y\", fast_budget = \"z\" }\n";
        let t = ["\"exe\"", "\"js\"", "\"strict-ftz\"", "\"Fs\"", "\"Io\"", "\"static\"", "true", "0", "-1", "bind"];
        assert_eq!(built(text, "t"), t.map(|v| (Code::E0200, v)));
        assert_eq!(built(text, "u"), [(Code::E0200, "\"clap\""), (Code::E0200, "bind")]);
        assert_eq!(built(text, "d"), []);
        assert_eq!(built(text, "e"), []);
        let check = ["-1", "\"dll\"", "\"ftz\"", "1", "2", "\"y\"", "\"z\""];
        assert_eq!(diagnostics(text, ManifestForm::File), check.map(|v| (Code::E1103, v)));
        let r = read_as(text, ManifestForm::File);
        let fs = r.manifest.targets["t"].value.build_diagnostics.iter().find(|d| d.message.contains("Fs"));
        assert_eq!(fs.unwrap().message, "this version does not support `provides` other than `Alloc` (`Fs`)");
    }

    /// R-47, §15.3, §18.1: `platform` is required in the build of a target
    /// that gives C or native code (`exe`, a plugin, `staticlib`, `source`
    /// with `lang = "c"`): an E1104 at the key of the target, without a
    /// candidate, and not in the check. Not in `source` with `lang = "js"`
    /// or `wasm-worklet`, nor where `kind` or `lang` is missing or not read.
    #[test]
    fn platform_is_required_in_the_build_of_a_target_of_c_or_native_code() {
        let kinds = ["exe", "clap", "vst3", "au", "staticlib", "source\"\nlang = \"c"];
        let not = ["source\"\nlang = \"js", "wasm-worklet", "source", "source\"\nlang = \"x", "source\"\nlang = 1 #\""];
        for (kind, needed) in kinds.iter().map(|k| (*k, true)).chain(not.iter().map(|k| (*k, false))) {
            let text = format!("[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"{kind}\"\n");
            let r = read_as(&text, ManifestForm::File);
            let t = &r.manifest.targets["t"].value;
            let e1104: Vec<&Diagnostic> = t.build_diagnostics.iter().filter(|d| d.code == Code::E1104).collect();
            assert_eq!(e1104.len(), needed as usize, "{kind}: {:?}", t.build_diagnostics);
            assert!(
                e1104.iter().all(|d| &text[d.span.start as usize..d.span.end as usize] == "t" && d.fixes.is_empty())
            );
            assert!(r.diagnostics.iter().all(|d| d.code != Code::E1104 || !d.message.contains("platform")), "{kind}");
        }
        for text in ["[targets.t]\nlang = \"c\"\n", "[targets.t]\nkind = 1\n"] {
            let text = format!("[package]\nname = \"a\"\nedition = \"2026\"\n{text}");
            assert_eq!(built(&text, "t"), [], "{text}");
        }
    }

    /// S-824: a platform this version does not tell (not a triple, an
    /// unknown architecture, an unknown system) is one E0200 of the build at
    /// the value, with what this version knows in a note; one written where
    /// it is not required too. Only a platform it tells is a cross one
    /// (S-161): `staticlib` with an unknown platform is the one E0200.
    #[test]
    fn a_platform_this_version_does_not_tell_is_one_e0200_of_the_build() {
        let target = |kind: &str, platform: &str| {
            format!(
                "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"{kind}\"\nplatform = \"{platform}\"\n"
            )
        };
        for p in ["nonsense", "zz80-none", "x86_64-unknown-plan9"] {
            let text = target("staticlib", p);
            assert_eq!(built(&text, "t"), [(Code::E0200, format!("\"{p}\"").as_str())], "{p}");
            assert!(read_as(&text, ManifestForm::File).diagnostics.is_empty(), "{p}");
            let r = read_as(&text, ManifestForm::File);
            let d = &r.manifest.targets["t"].value.build_diagnostics[0];
            assert!(
                d.notes.iter().any(|n| n.message.contains("`\"host\"`") && n.message.contains("`thumbv*`")),
                "{d:?}"
            );
        }
        let js = target("source\"\nlang = \"js", "nonsense");
        assert_eq!(built(&js, "t"), [(Code::E0200, "\"js\""), (Code::E0200, "\"nonsense\"")]);
        for p in [
            "host",
            "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "thumbv7em-none-eabihf",
            "riscv32imac-unknown-none-elf",
        ] {
            assert!(crate::build::platform(p).is_ok(), "{p}");
        }
    }

    /// S-161: a known platform other than the host for a kind an outer C
    /// toolchain builds is an E0200 of the build at the kind, with
    /// `kind = "source"` and `lang = "c"` in a note; `source` is not one, and
    /// a kind already unsupported (`exe`) is not reported twice.
    #[test]
    fn a_cross_staticlib_is_an_e0200_of_the_build_at_its_kind() {
        let target = |kind: &str| {
            format!(
                "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"{kind}\"\nplatform = \"thumbv7em-none-eabihf\"\n"
            )
        };
        let text = target("staticlib");
        assert_eq!(built(&text, "t"), [(Code::E0200, "\"staticlib\"")]);
        let r = read_as(&text, ManifestForm::File);
        let d = &r.manifest.targets["t"].value.build_diagnostics[0];
        assert!(d.notes.iter().any(|n| n.message.contains("`kind = \"source\"` with `lang = \"c\"`")), "{d:?}");
        assert_eq!(built(&target("source\"\nlang = \"c"), "t"), []);
        assert_eq!(built(&target("exe"), "t"), [(Code::E0200, "\"exe\"")]);
        let host = text.replace("thumbv7em-none-eabihf", "host");
        assert_eq!(built(&host, "t"), []);
    }

    /// [`table::TOOLCHAIN`] and the kinds of every [`Need`] are kinds of
    /// §15.3, and a kind of the toolchain is one the row of `kind` supports:
    /// else the E0200 of a cross platform (S-161) would never be made, and a
    /// required key never missing.
    #[test]
    fn the_kinds_the_reader_names_are_kinds_and_a_toolchain_kind_is_supported() {
        let k = row(Table::Target, Field::Kind);
        let (Rule::OneOf(kinds, _), Some((Unsupported::Except(supported), _))) = (k.rule, k.unsupported) else {
            panic!("the row of `kind`: {k:?}")
        };
        assert!(table::TOOLCHAIN.iter().all(|t| kinds.contains(t)), "{:?}", table::TOOLCHAIN);
        assert!(table::TOOLCHAIN.iter().any(|t| supported.contains(t)), "{supported:?}");
        for r in table::ROWS {
            if let Need::Target { kinds: of, or, .. } = r.need {
                assert!(of.iter().chain(or.as_ref().map(|(k, _)| k)).all(|t| kinds.contains(t)), "{}", r.key);
            }
        }
    }

    /// S-827, §15.2, §15.3: a key and a value of `bind` are module paths,
    /// `snake_case` names (§2.3) joined by `.`; another form is an E1103 of
    /// the check (the key at the key, the value at the value), besides the
    /// E0200 of a `bind` with an entry.
    #[test]
    fn a_key_and_a_value_of_bind_are_module_paths() {
        let bind = |key: &str, value: &str| {
            format!(
                "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"source\"\nlang = \"c\"\n\
                     platform = \"host\"\n[targets.t.bind]\n\"{key}\" = \"{value}\"\n"
            )
        };
        for ok in ["a", "a.b", "match.x_1", "a_.b2"] {
            assert_eq!(diagnostics(&bind(ok, ok), ManifestForm::File), [], "{ok}");
            assert_eq!(built(&bind(ok, ok), "t"), [(Code::E0200, "bind")], "{ok}");
        }
        for bad in ["", "A", "a..b", ".a", "a.", "1a", "a-b", "a.B", "_a"] {
            let text = bind(bad, "m");
            let found = diagnostics(&text, ManifestForm::File);
            assert_eq!(found, [(Code::E1103, format!("\"{bad}\"").as_str())], "key {bad:?}");
            let text = bind("m", bad);
            let found = diagnostics(&text, ManifestForm::File);
            assert_eq!(found, [(Code::E1103, format!("\"{bad}\"").as_str())], "value {bad:?}");
        }
    }

    /// Every row that names a [`Feature`] gives it the details its phrase
    /// takes (the value for a string, none for the others), and its values
    /// are of the shape of the row.
    #[test]
    fn the_feature_of_a_row_takes_its_details() {
        for r in table::ROWS {
            let Some((values, feature)) = r.unsupported else { continue };
            let details = matches!(values, Unsupported::Except(_)) as usize;
            assert_eq!(feature.arity(), details, "{}", r.key);
            // The row's shape is one its values are read from (else the reader reports none).
            let fits = match values {
                Unsupported::Except(_) => matches!(r.shape, Shape::Str | Shape::Strs),
                Unsupported::True => r.shape == Shape::Bool,
                Unsupported::Any => matches!(r.shape, Shape::Int | Shape::Table(_)),
            };
            assert!(fits, "{}: {values:?} on {:?}", r.key, r.shape);
        }
    }

    /// E1103 (S-99, S-597): a value outside the closed list of its key, with
    /// the list in a note and no candidate; `fp` also names `@fp(relaxed)`.
    #[test]
    fn a_value_outside_its_closed_list_is_an_e1103_with_the_list() {
        let text = "[package]\nname = \"a\"\nedition = \"2025\"\n[targets.t]\nkind = \"plugin\"\nplatform = \"h\"\n\
                    lang = \"C\"\nfp = \"relaxed\"\npanic = \"abort\"\nmain_frame = \"heap\"\n\
                    [targets.u]\nkind = \"wasm-worklet\"\nplatform = \"h\"\nlang = \"js\"\nfp = \"strict-ftz\"\n\
                    panic = \"halt\"\nmain_frame = \"static\"\n";
        let mut r = read_as(text, ManifestForm::File);
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
            let text = format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n");
            let r = read_as(&text, ManifestForm::File);
            assert_eq!(r.diagnostics.len(), usize::from(bad), "{name}: {:?}", r.diagnostics);
            if bad {
                assert_eq!((r.diagnostics[0].code, r.diagnostics[0].span.start), (Code::E1103, 17), "{name}");
            }
        }
        let r = read_as("[package]\nname = \"std\"\nedition = \"2026\"\n", ManifestForm::File);
        assert!(r.diagnostics[0].notes[0].message.contains("embedded standard library"), "{:?}", r.diagnostics);
    }

    /// E1103: the form of `prefix` (§14.2, S-95, R-121 (2)), written or not
    /// any `@export`.
    #[test]
    fn a_prefix_has_its_form() {
        let good = ["vc_", "my_synth_", "a1_", "x_"];
        let bad = ["", "vc", "Vc_", "_vc_", "1a_", "v__", "a__b_", "vc-_", "onsa_", "onsa_x_", "é_"];
        for (p, ok) in good.iter().map(|p| (p, true)).chain(bad.iter().map(|p| (p, false))) {
            let text = format!("[package]\nname = \"a\"\nedition = \"2026\"\n[export]\nprefix = \"{p}\"\n");
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
            "[package]\nname = \"a\"\nedition = \"2026\"\n[dependencies]\nfx = \"1.0.0\"\nstd = \"{}\"\nfy = 3\nfz = {{ path = 1 }}\n",
            crate::STD_VERSION
        );
        assert_eq!(
            diagnostics(&text, ManifestForm::File),
            [(Code::E0200, "fx"), (Code::E0200, "fy"), (Code::E0200, "fz")]
        );
        let r = read_as(&text, ManifestForm::File);
        assert!(r.diagnostics.iter().all(|d| d.stage == Stage::Manifest && d.message.contains("`std`")));
        let text = "[package]\nname = \"a\"\nedition = \"2026\"\n[dependencies]\nstd = \"0.0.0\"\n";
        let r = read_as(text, ManifestForm::File);
        assert_eq!(diagnostics(text, ManifestForm::File), [(Code::E1103, "\"0.0.0\"")]);
        assert!(r.diagnostics[0].notes[0].message.contains(crate::STD_VERSION), "{:?}", r.diagnostics);
    }

    /// `fast_budget` and `bulk_budget` are numbers of bytes, 0 or more (S-827).
    #[test]
    fn a_budget_is_0_or_more() {
        let text = "[package]\nname = \"a\"\nedition = \"2026\"\n[targets.t]\nkind = \"exe\"\nplatform = \"h\"\n[targets.t.memory]\n\
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
            let r = read_as(text, ManifestForm::File);
            assert_eq!(r.diagnostics.len(), 1, "{text:?}: {:?}", r.diagnostics);
            let d = &r.diagnostics[0];
            assert_eq!(d.code, Code::E1101);
            assert_eq!(text[..d.span.start as usize].matches('\n').count() + 1, line, "{text:?}: {d:?}");
            assert!(!d.message.contains('\n'), "{}", d.message);
            assert!(r.manifest.package.value.name.value.is_empty());
        }
        // A reason the parser does not give leaves no `: ` behind.
        let r = read_as("[package]\nname = \"a\"\na =", ManifestForm::File);
        assert_eq!(r.diagnostics[0].message, "the manifest is not valid TOML");
        let r = read_as("[package]\nname = \"a\"\na =\n", ManifestForm::File);
        assert!(r.diagnostics[0].message.starts_with("the manifest is not valid TOML: invalid"), "{:?}", r.diagnostics);
    }

    /// E1102 names a table only where a header writes it; a dotted key and an
    /// inline table are keys, as written.
    #[test]
    fn an_unknown_table_is_one_a_header_writes() {
        let text = "top.k = 1\n[package]\nname = \"a\"\nedition = \"2026\"\nfoo.bar = 1\nx = { y = 1 }\n[bogus]\n[[extra]]\n[a.b]\n";
        let mut r = read_as(text, ManifestForm::File);
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
