//! The closed list of the forms of other languages, `spec/foreign-forms.toml`
//! (S-250), against the table of the compiler, `onsa_syntax::foreign` (W3-15,
//! D-15):
//!
//! - the rows are one to one by their `id`, with the same stage and code;
//! - every example of a row runs through the entry of a case (a single-file
//!   package, as `onsa check` reads it, [`crate::fix_contract::check_text`]):
//!   the row's code is reported at `at`, of the row's stage; with `fixed`,
//!   candidate K applied alone gives `fixed[K-1]` (compared as the `.fixK`
//!   files are, the width of blanks aside) and there are as many candidates;
//!   with `property`, `clean` (the check after candidate 1 reports nothing)
//!   and `same_code` (S-247) hold; and every candidate keeps the contract of
//!   §18.1 (S-236, S-302: [`crate::fix_contract::check_candidate`]);
//! - every example of a row that a matcher of several rows names
//!   (`Matcher::many`) gives the diagnostic of that row, its message and its
//!   rule (the first note): the code and the place alone do not tell it from
//!   another row of the matcher ([`chosen_rows`]);
//! - a row whose examples do not pass yet waits in `tests/pending.toml` (kind
//!   `foreign-form`, the `id` as target): a listed row that passes, and a
//!   row that fails and is not listed, are failures, as for the other kinds.
//!
//! The number of the `fixed` texts is the spec's (§18.1); their text is a copy
//! of the implementation's output (Q-04, X-3): a text that differs is a
//! failure of its own ([`Report::copy_failures`]), which no entry silences.
//! A listed row does not judge, rewrite or count its copies as a reason to
//! wait (they are counted, [`Report::unjudged_copies`]). `UPDATE_GOLDEN=1`
//! rewrites a text that differs, unless the guard refuses
//! ([`crate::copy_guard::text`]; `UPDATE_GOLDEN=worse` rewrites it anyway,
//! [`Report::forced`]): only the body of each `'''…'''` literal changes
//! (its line ends as they were, LF or CR LF), the comments and the other
//! fields stay, and the file read again must hold the same values but the
//! texts rewritten ([`rewrite`]). The data file is the spec's (the tests'
//! side writes it); this module changes nothing else in it.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;

use onsa_diag::Code;
use onsa_syntax::foreign::{MATCHERS, Phase, READS, ROWS, RowId, WAITING};

use crate::fix_contract::{self, TextCheck};
use crate::golden::Update;
use crate::pending::{Kind, Pending};

/// The file, relative to the repository root.
pub const PATH: &str = "spec/foreign-forms.toml";

#[derive(Debug, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    #[serde(default)]
    form: Vec<Form>,
}

#[derive(Debug, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
struct Form {
    id: String,
    #[allow(dead_code)]
    kind: String,
    #[allow(dead_code)]
    origin: String,
    stage: String,
    code: String,
    #[allow(dead_code)]
    spec: Vec<String>,
    #[allow(dead_code)]
    rule: String,
    #[serde(default)]
    example: Vec<Example>,
}

#[derive(Debug, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
struct Example {
    source: String,
    /// The main position; the forms whose position the spec does not set leave it out.
    #[serde(default)]
    at: Option<String>,
    #[serde(default)]
    fixed: Option<Vec<toml::Spanned<String>>>,
    #[serde(default)]
    property: Option<Vec<String>>,
    /// The number of candidates, for an example checked by its properties.
    #[serde(default)]
    candidates: Option<usize>,
}

/// What the table says of a row: its stage and code, and its message and
/// rule when a matcher of several rows names it ([`chosen_rows`]).
#[derive(Clone, Copy)]
struct Kind1 {
    phase: Phase,
    code: Code,
    told: Option<Told>,
}

/// What tells a row from the other rows of its matcher: its message and its
/// rule (the first note of its diagnostic, S-114).
#[derive(Clone, Copy, PartialEq)]
struct Told {
    message: &'static str,
    rule: &'static str,
}

impl Told {
    fn of(id: RowId) -> Told {
        let r = onsa_syntax::foreign::row(id);
        Told { message: r.message, rule: r.rule }
    }

    fn is(self, d: &onsa_diag::Diagnostic) -> bool {
        d.message == self.message && d.notes.first().is_some_and(|n| n.span.is_none() && n.message == self.rule)
    }
}

/// The rows that a matcher of several rows chooses among
/// (`Matcher::many`, of [`MATCHERS`] and [`READS`]): every example of such a
/// row gives its diagnostic ([`Told`]), so that a matcher that names another
/// of its rows fails. Two rows of one matcher that a diagnostic cannot tell
/// apart are a failure (`Err`).
fn chosen_rows() -> Result<Vec<RowId>, Vec<String>> {
    let many = || MATCHERS.iter().chain(READS).filter(|m| m.rows.len() > 1);
    let mut alike = Vec::new();
    for m in many() {
        for (i, &a) in m.rows.iter().enumerate() {
            for &b in m.rows[i + 1..].iter().filter(|&&b| Told::of(b) == Told::of(a)) {
                alike.push(format!(
                    "{a:?} and {b:?} of one matcher have the same message and rule: no example tells them apart"
                ));
            }
        }
    }
    if !alike.is_empty() {
        return Err(alike);
    }
    Ok(many().flat_map(|m| m.rows.iter().copied()).collect())
}

/// What [`check`] found.
#[derive(Debug, Default)]
pub struct Report {
    /// The rows checked, and how many examples.
    pub rows: usize,
    pub examples: usize,
    /// The rows whose examples fail and that `tests/pending.toml` lists.
    pub pending: Vec<String>,
    /// Failures: of the data, of the one-to-one, of a row not listed, of a
    /// listed row that passes.
    pub failures: Vec<String>,
    /// The `fixed` texts compared with the text after their candidate.
    pub copies: usize,
    /// The rows checked by their message and rule ([`chosen_rows`]).
    pub chosen: usize,
    /// The `fixed` texts of rows not listed that differ (`UPDATE_GOLDEN=1`
    /// rewrites them), or whose rewriting the guard refused: never silenced,
    /// never a reason to wait.
    pub copy_failures: Vec<String>,
    /// The `fixed` texts `UPDATE_GOLDEN=1` rewrote: `<id> example <i> fixed <k>`.
    pub rewritten: Vec<String>,
    /// Those of `rewritten` the guard refused and `UPDATE_GOLDEN=worse`
    /// wrote: `<id> example <i> fixed <k> (<what only the new text reports>)`.
    pub forced: Vec<String>,
    /// The `fixed` texts of listed rows that differ, not judged.
    pub unjudged_copies: usize,
}

/// A `fixed` text that differs from the text after its candidate.
struct CopyDiff {
    /// The example in its row, and the text in `fixed` (from 0).
    example: usize,
    k: usize,
    /// The copy, and the text after the candidate.
    copy: String,
    actual: String,
    message: String,
}

/// What one example does: its problems (the promises) and its copies.
#[derive(Default)]
struct Outcome {
    problems: Vec<String>,
    copies: Vec<CopyDiff>,
    compared: usize,
}

/// A `fixed` text to rewrite: the form, the example, the text in `fixed`
/// (from 0), and the text after the candidate.
struct Rewrite {
    form: usize,
    example: usize,
    k: usize,
    text: String,
}

/// Check the data file under `root` against the table, with the list of
/// things pending; `update` says whether the `fixed` texts that differ are
/// rewritten.
pub fn check(root: &Path, update: Update) -> Report {
    let mut report = Report::default();
    let text = match std::fs::read_to_string(root.join(PATH)) {
        Ok(t) => t,
        Err(e) => {
            report.failures.push(format!("{PATH}: {e}"));
            return report;
        }
    };
    let file: File = match toml::from_str(&text) {
        Ok(f) => f,
        Err(e) => {
            report.failures.push(format!("{PATH}: {e}"));
            return report;
        }
    };
    let pending = match Pending::load(root) {
        Ok(p) => p,
        Err(e) => {
            report.failures.push(e);
            return report;
        }
    };
    report.failures.extend(one_to_one(&file.form));
    let chosen = chosen_rows().unwrap_or_else(|alike| {
        report.failures.extend(alike);
        Vec::new()
    });
    let rows: BTreeMap<&str, Kind1> = ROWS
        .iter()
        .map(|r| (r.name, Kind1 { phase: r.phase, code: r.code, told: chosen.contains(&r.id).then(|| Told::of(r.id)) }))
        .chain(WAITING.iter().map(|w| (w.name, Kind1 { phase: w.phase, code: w.code, told: None })))
        .collect();
    let mut rewrite_to: Vec<Rewrite> = Vec::new();
    for (f, form) in file.form.iter().enumerate() {
        let Some(row) = rows.get(form.id.as_str()) else { continue };
        report.rows += 1;
        report.examples += form.example.len();
        report.chosen += usize::from(row.told.is_some());
        let mut problems = Vec::new();
        if form.example.is_empty() {
            problems.push("no example".to_string());
        }
        let mut copies = Vec::new();
        for (i, ex) in form.example.iter().enumerate() {
            let mut done = example(*row, ex);
            report.copies += done.compared;
            for p in done.problems {
                problems.push(format!("example {}: {p}", i + 1));
            }
            for c in &mut done.copies {
                c.example = i;
            }
            copies.extend(done.copies);
        }
        let listed = pending.get(Kind::ForeignForm, &form.id);
        // A listed row does not judge its copies (its output is not the one to keep): counted only.
        if listed.is_some() {
            report.unjudged_copies += copies.len();
        }
        for c in copies.into_iter().filter(|_| listed.is_none()) {
            let ex = format!("{}: example {}", form.id, c.example + 1);
            if !update.writes() {
                report.copy_failures.push(format!("{ex}: {} (UPDATE_GOLDEN=1 rewrites it)", c.message));
                continue;
            }
            let at = format!("{} example {} fixed {}", form.id, c.example + 1, c.k + 1);
            match crate::copy_guard::text(&c.copy, &c.actual) {
                Ok(found) if found.is_empty() => {}
                Ok(found) if update == Update::Worse => report.forced.push(format!("{at} ({})", found.join(", "))),
                Ok(found) => {
                    let what = format!("the copy `fixed` {}", c.k + 1);
                    let to = "the example's `property` (`clean`, `same_code`)";
                    report.copy_failures.push(format!("{ex}: {}", crate::copy_guard::refused(&what, &found, to)));
                    continue;
                }
                Err(e) => {
                    report.copy_failures.push(format!("{ex}: the copy `fixed` {} is not rewritten: {e}", c.k + 1));
                    continue;
                }
            }
            report.rewritten.push(at);
            rewrite_to.push(Rewrite { form: f, example: c.example, k: c.k, text: c.actual });
        }
        match (problems.is_empty(), listed) {
            (true, None) => {}
            (true, Some(e)) => report.failures.push(format!(
                "{}: the row passes but is listed in tests/pending.toml (until {}); remove the entry",
                form.id, e.until
            )),
            (false, Some(_)) => report.pending.push(form.id.clone()),
            (false, None) => {
                report.failures.push(format!("{}:\n  {}", form.id, problems.join("\n  ").replace('\n', "\n  ")))
            }
        }
    }
    // Nothing checked is a failure, not a pass.
    if report.rows == 0 || report.examples == 0 || report.copies == 0 || report.chosen == 0 {
        report
            .failures
            .push(format!("{PATH}: no row, no example, no `fixed` text or no row by its message was checked"));
    }
    for e in pending.of_kind(Kind::ForeignForm) {
        if !file.form.iter().any(|f| f.id == e.target) {
            report.failures.push(format!("tests/pending.toml: `{}` is not a row of {PATH}", e.target));
        }
    }
    if !rewrite_to.is_empty() {
        let mut file = file;
        if let Err(e) = rewrite(&text, &mut file, &rewrite_to)
            .and_then(|new| std::fs::write(root.join(PATH), new).map_err(|e| format!("cannot write {PATH}: {e}")))
        {
            report.failures.push(e);
            report.rewritten.clear();
            report.forced.clear();
        }
    }
    report
}

/// `text` (the data file, read as `file`) with the `fixed` texts of
/// `rewrite_to` written in their `'''…'''` literals; nothing else changes. A
/// literal that holds a CR LF gets CR LF line ends. `file` gets the new
/// texts, and the new data file must read the same as it. `Err`: a text that
/// no literal string can hold, a literal of another form, or a file that
/// reads otherwise.
fn rewrite(text: &str, file: &mut File, rewrite_to: &[Rewrite]) -> Result<String, String> {
    let mut edits: Vec<(std::ops::Range<usize>, String)> = Vec::new();
    for Rewrite { form: f, example: e, k, text: actual } in rewrite_to {
        let form = &mut file.form[*f];
        let at = format!("{}: example {} fixed {}", form.id, e + 1, k + 1);
        let Some(s) = form.example[*e].fixed.as_mut().and_then(|v| v.get_mut(*k)) else {
            return Err(format!("{PATH}: {at}: no such text"));
        };
        let span = s.span();
        let old = &text[span.clone()];
        if !(old.starts_with("'''") && old.ends_with("'''") && old.len() >= 6) {
            return Err(format!("{PATH}: {at}: the text is not a `'''` literal string; rewrite it by hand"));
        }
        if actual.contains("'''") || actual.ends_with('\'') {
            return Err(format!(
                "{PATH}: {at}: a `'''` literal string cannot hold the text after it; write it by hand"
            ));
        }
        // The reader (`toml_edit`) reads a CR LF of a literal string as LF: the value is the LF form.
        let value = actual.replace("\r\n", "\n");
        let nl = if old.contains("\r\n") { "\r\n" } else { "\n" };
        edits.push((span, format!("'''{nl}{}'''", value.replace('\n', nl))));
        *s.get_mut() = value;
    }
    edits.sort_by_key(|(r, _)| std::cmp::Reverse(r.start));
    let mut out = text.to_string();
    for (r, new) in edits {
        out.replace_range(r, &new);
    }
    let again: File = toml::from_str(&out).map_err(|e| format!("{PATH}: the rewritten file does not read: {e}"))?;
    if again != *file {
        return Err(format!("{PATH}: the rewritten file reads otherwise than the texts rewritten; nothing written"));
    }
    Ok(out)
}

/// The rows of the file and of the table, one to one (D-15).
fn one_to_one(forms: &[Form]) -> Vec<String> {
    let mut out = Vec::new();
    for (i, f) in forms.iter().enumerate() {
        if forms[..i].iter().any(|g| g.id == f.id) {
            out.push(format!("{PATH}: `{}` is two rows", f.id));
        }
        let table = ROWS
            .iter()
            .map(|r| (r.name, r.phase, r.code))
            .chain(WAITING.iter().map(|w| (w.name, w.phase, w.code)))
            .find(|r| r.0 == f.id);
        match table {
            None => out.push(format!("{PATH}: `{}` has no row in `onsa_syntax::foreign` (ROWS or WAITING)", f.id)),
            Some((_, phase, code)) => {
                if phase.name() != f.stage {
                    out.push(format!(
                        "`{}`: the stage is `{}` in {PATH}, `{}` in the table",
                        f.id,
                        f.stage,
                        phase.name()
                    ));
                }
                if code.as_str() != f.code {
                    out.push(format!("`{}`: the code is {} in {PATH}, {} in the table", f.id, f.code, code.as_str()));
                }
            }
        }
    }
    for name in ROWS.iter().map(|r| r.name).chain(WAITING.iter().map(|w| w.name)) {
        if !forms.iter().any(|f| f.id == name) {
            out.push(format!("`onsa_syntax::foreign` has `{name}`, which {PATH} does not"));
        }
    }
    out
}

/// What one example of `row` does not do.
fn example(row: Kind1, ex: &Example) -> Outcome {
    let mut out = Vec::new();
    let (mut copies, mut compared) = (Vec::new(), 0);
    let run: TextCheck = match fix_contract::check_text(&ex.source) {
        Ok(r) => r,
        Err(e) => {
            return Outcome {
                problems: vec![format!("the check ends in an internal error: {e}")],
                ..Outcome::default()
            };
        }
    };
    let sources = &run.loaded.sources;
    let place = |d: &onsa_diag::Diagnostic| {
        let lc = sources.file(d.span.file).line_col(d.span.start);
        format!("{}:{}", lc.line, lc.col)
    };
    let ds = &run.analyzed.diagnostics;
    let reported: Vec<String> = onsa_diag::printed_order(sources, ds)
        .into_iter()
        .map(|i| format!("{} at {}", ds[i].code.as_str(), place(&ds[i])))
        .collect();
    let at = |d: &onsa_diag::Diagnostic| ex.at.as_ref().is_none_or(|a| place(d) == *a);
    let where_ = ex.at.as_deref().unwrap_or("any place");
    let Some(d) = run.analyzed.diagnostics.iter().find(|d| d.code == row.code && at(d)) else {
        out.push(format!("no {} at {where_}; the check reports {:?}", row.code.as_str(), reported));
        return Outcome { problems: out, ..Outcome::default() };
    };
    if let Some(told) = row.told.filter(|t| !t.is(d)) {
        let rule = d.notes.first().map(|n| n.message.as_str());
        out.push(format!(
            "{} at {where_} is not of the row (its matcher names several rows): the message {:?} and the rule {rule:?}, \
             not {:?} and {:?}",
            row.code.as_str(),
            d.message,
            told.message,
            told.rule
        ));
    }
    if d.stage != row.phase.stage() {
        out.push(format!(
            "{} at {where_} of the {} stage, not {}",
            row.code.as_str(),
            d.stage.name(),
            row.phase.name()
        ));
    }
    if let Some(n) = ex.candidates
        && n != d.fixes.len()
    {
        out.push(format!("{} candidates, `candidates` says {n}", d.fixes.len()));
    }
    if let Some(fixed) = &ex.fixed
        && fixed.len() != d.fixes.len()
    {
        out.push(format!("{} candidates, `fixed` has {}", d.fixes.len(), fixed.len()));
    }
    let properties = ex.property.as_deref().unwrap_or_default();
    for p in properties {
        if p != "clean" && p != "same_code" {
            out.push(format!("unknown property `{p}`"));
        }
    }
    for (k, fix) in d.fixes.iter().enumerate() {
        let after = match fix_contract::check_candidate(&run, d, fix) {
            Ok(a) => a,
            Err(e) => {
                out.push(format!("candidate {}: cannot be checked: {e}", k + 1));
                continue;
            }
        };
        for p in &after.problems {
            out.push(format!("candidate {} `{}`: {p}", k + 1, fix.title()));
        }
        // The copies, when there are as many as the candidates (else the number is fixed by hand first).
        if let Some(want) = ex.fixed.as_ref().filter(|f| f.len() == d.fixes.len()).map(|f| f[k].get_ref()) {
            compared += 1;
            if let Some(diff) = crate::fixes::first_difference(want, &after.text) {
                copies.push(CopyDiff {
                    example: 0,
                    k,
                    copy: want.clone(),
                    actual: after.text.clone(),
                    message: format!("candidate {}: the text after it differs from the copy `fixed`: {diff}", k + 1),
                });
            }
        }
        if k == 0 {
            if properties.iter().any(|p| p == "clean") && !after.diagnostics.is_empty() {
                let left: Vec<String> = after.diagnostics.iter().map(|d| d.code.as_str().to_string()).collect();
                out.push(format!("`clean`: the check after candidate 1 reports {left:?}"));
            }
            if properties.iter().any(|p| p == "same_code")
                && let Some(diff) = fix_contract::same_code(&ex.source, &after.text)
            {
                out.push(format!("`same_code`: {diff}"));
            }
        }
    }
    if d.fixes.is_empty() && (ex.fixed.as_ref().is_some_and(|f| !f.is_empty()) || !properties.is_empty()) {
        out.push("no candidate, but the example has `fixed` or `property`".into());
    }
    Outcome { problems: out, copies, compared }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root(tag: &str, forms: &str, pending: &str) -> std::path::PathBuf {
        let root = crate::c::scratch_dir("onsa_test", &format!("foreign_forms_{tag}"));
        let _ = std::fs::remove_dir_all(&root);
        for (p, text) in [(PATH, forms), (crate::pending::PATH, pending)] {
            let p = root.join(p);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, text).unwrap();
        }
        root
    }

    const FORMS: &str = r#"
[[form]]
id = "semicolon"
kind = "foreign"
origin = "C"
stage = "syntax"
code = "E0020"
spec = ["2.5"]
rule = "r"

[[form.example]]
source = '''
pub fn f() -> I32 {
  let a = 1;
  a
}
'''
at = "2:12"
fixed = ['''
pub fn f() -> I32 {
  let a = 1
  a
}
''']

[[form]]
id = "let_mut"
kind = "foreign"
origin = "Rust"
stage = "syntax"
code = "E0020"
spec = ["5.1"]
rule = "r"

[[form.example]]
source = '''
pub fn f() -> I32 {
  let mut a = 1
  a
}
'''
at = "2:4"
property = ["clean"]
"#;

    /// The guard form of the float literals of one pattern (S-317): the
    /// candidate of the E0020 leaves nothing at all (`clean`) and keeps the
    /// contract; the forms whose alternatives differ are E0002.
    #[test]
    fn float_patterns_merge_into_one_guard() {
        let f = |ty: &str, arm: &str| {
            format!("pub fn f(x: {ty}) -> I32 {{\n  match x {{\n    {arm} => 1,\n    _ => 0,\n  }}\n}}\n")
        };
        for src in [
            f("F32", "0.5 | 1.5"),
            f("Option[F32]", "Some(0.5) | Some(1.5)"),
            f("(F32, I32)", "(0.5, n) | (1.5, n)"),
            f("Option[F32]", "Some(0.5 | 1.5)"),
            f("(F32, F32)", "(0.5, 1.5) | (1.5, 0.5)"),
            f("(F32, I32)", "(0.5 | 1.5, 1) | (2.5, 1)"),
        ] {
            let run = fix_contract::check_text(&src).unwrap();
            let d = &run.analyzed.diagnostics;
            assert_eq!(d.len(), 1, "{src}: {d:?}");
            assert_eq!((d[0].code, d[0].fixes.len()), (Code::E0020, 1), "{src}");
            let after = fix_contract::check_candidate(&run, &d[0], &d[0].fixes[0]).unwrap();
            assert!(after.diagnostics.is_empty(), "{src}\n{}\n{:?}", after.text, after.diagnostics);
            assert!(after.problems.is_empty(), "{src}: {:?}", after.problems);
        }
        for src in [
            f("(F32, I32)", "(0.5, 1) | (1.5, 2)"),
            f("Option[F32]", "Some(0.5) | Some(y)"),
            f("F32", "0.5 // half\n    | 1.5"),
        ] {
            let run = fix_contract::check_text(&src).unwrap();
            let d = &run.analyzed.diagnostics;
            assert_eq!(d.iter().map(|d| (d.code, d.fixes.len())).collect::<Vec<_>>(), [(Code::E0002, 0)], "{src}");
        }
    }

    const LISTED: &str = "[[pending]]\nkind = \"foreign-form\"\ntarget = \"let_mut\"\nreasons = [\"S-250\"]\nuntil = \"W3-15\"\nnote = \"n\"\n";

    #[test]
    fn rows_pass_fail_and_wait() {
        let r = check(&root("plain", FORMS, ""), Update::Off);
        assert_eq!((r.rows, r.examples), (2, 2));
        // `let_mut`'s place is wrong: it fails, not listed.
        assert!(r.failures.iter().any(|f| f.starts_with("let_mut:") && f.contains("no E0020 at 2:4")), "{r:?}");
        assert!(!r.failures.iter().any(|f| f.starts_with("semicolon:")), "{r:?}");
        // The table has rows the file does not: one to one.
        assert!(r.failures.iter().any(|f| f.contains("has `loop`, which")), "{r:?}");
        // Listed, it waits.
        let r = check(&root("listed", FORMS, LISTED), Update::Off);
        assert_eq!(r.pending, ["let_mut"]);
        // A listed row that passes.
        let fixed = FORMS.replace("at = \"2:4\"", "at = \"2:3\"");
        let r = check(&root("passes", &fixed, LISTED), Update::Off);
        assert!(r.failures.iter().any(|f| f.contains("let_mut: the row passes but is listed")), "{r:?}");
        // A `fixed` that differs.
        let wrong = FORMS.replace("  let a = 1\n  a\n}\n''']", "  let a = 2\n  a\n}\n''']");
        let r = check(&root("wrong", &wrong, ""), Update::Off);
        assert!(!r.failures.iter().any(|f| f.starts_with("semicolon:")), "a copy is not a failure of the row: {r:?}");
        assert_eq!(r.copies, 1);
        assert!(
            r.copy_failures.len() == 1
                && r.copy_failures[0]
                    .starts_with("semicolon: example 1: candidate 1: the text after it differs from the copy `fixed`"),
            "{r:?}"
        );
        // Listed, a row whose copy alone differs passes: the copy keeps no row waiting.
        let listed = LISTED.replace("let_mut", "semicolon");
        let r = check(&root("wrong_listed", &wrong, &listed), Update::Off);
        assert!(r.copy_failures.is_empty(), "{r:?}");
        assert!(r.failures.iter().any(|f| f.contains("semicolon: the row passes but is listed")), "{r:?}");
        // The number of `fixed` is the row's promise: compared, never a copy.
        let two = FORMS.replace("  a\n}\n''']", "  a\n}\n''', '''x''']");
        let r = check(&root("two", &two, ""), Update::Off);
        assert!(r.failures.iter().any(|f| f.contains("1 candidates, `fixed` has 2")), "{r:?}");
        assert!(r.copy_failures.is_empty() && r.copies == 0, "{r:?}");
    }

    /// A row of a matcher of several rows is told by its diagnostic (A29): a
    /// row `octal_prefix` whose example the lexer reads as `leading_zero`, of
    /// the same code, stage and place, fails; the rows of one matcher differ.
    #[test]
    fn a_row_of_many_is_told_by_its_message() {
        let form = |value: &str| {
            format!(
                "[[form]]\nid = \"octal_prefix\"\nkind = \"foreign\"\norigin = \"C\"\nstage = \"lexical\"\n\
                 code = \"E0020\"\nspec = [\"2.4\"]\nrule = \"r\"\n\n[[form.example]]\nsource = '''\n\
                 pub fn f() -> I32 {{\n  let n: I32 = {value}\n  n\n}}\n'''\nat = \"2:16\"\n"
            )
        };
        assert!(chosen_rows().is_ok_and(|rows| !rows.is_empty()));
        let r = check(&root("many_own", &form("0o17"), ""), Update::Off);
        assert_eq!((r.rows, r.chosen), (1, 1), "{r:?}");
        assert!(!r.failures.iter().any(|f| f.starts_with("octal_prefix:")), "{r:?}");
        let r = check(&root("many_other", &form("017"), ""), Update::Off);
        assert!(
            r.failures.iter().any(|f| f.starts_with("octal_prefix:") && f.contains("E0020 at 2:16 is not of the row")),
            "{r:?}"
        );
    }

    /// `UPDATE_GOLDEN=1` writes the bodies of the `'''` literals only: the
    /// comments and the other fields stay, and the file reads the same but
    /// the texts rewritten.
    #[test]
    fn a_rewrite_changes_the_bodies_of_the_texts_only() {
        let text = FORMS.replace(
            "[[form.example]]\nsource = '''\npub fn f() -> I32 {\n  let a",
            "# a comment\n[[form.example]]\nsource = '''\npub fn f() -> I32 {\n  let a",
        );
        let read = |t: &str| toml::from_str::<File>(t).unwrap();
        let mut file = read(&text);
        let span = file.form[0].example[0].fixed.as_ref().unwrap()[0].span();
        let to = |k: usize, text: &str| Rewrite { form: 0, example: 0, k, text: text.into() };
        let new = rewrite(&text, &mut file, &[to(0, "pub fn g() {}\n")]).unwrap();
        assert_eq!(&new[..span.start], &text[..span.start]);
        assert_eq!(&new[span.start..span.start + 21], "'''\npub fn g() {}\n'''");
        assert_eq!(&new[span.start + 21..], &text[span.end..]);
        assert!(new.contains("# a comment\n"));
        let mut want = read(&text);
        *want.form[0].example[0].fixed.as_mut().unwrap()[0].get_mut() = "pub fn g() {}\n".into();
        assert_eq!(read(&new), want);
        // A text a literal string cannot hold is written by hand.
        let mut file = read(&text);
        let e = rewrite(&text, &mut file, &[to(0, "x = '''\n")]).unwrap_err();
        assert!(e.contains("cannot hold"), "{e}");
        let e = rewrite(&text, &mut read(&text), &[to(1, "x\n")]).unwrap_err();
        assert!(e.contains("no such text"), "{e}");
    }

    /// A data file with CR LF line ends keeps them in the texts rewritten (L5).
    #[test]
    fn a_rewrite_keeps_the_line_ends() {
        let text = FORMS.replace('\n', "\r\n");
        let mut file: File = toml::from_str(&text).unwrap();
        let span = file.form[0].example[0].fixed.as_ref().unwrap()[0].span();
        let to = Rewrite { form: 0, example: 0, k: 0, text: "pub fn g() {}\nx\n".into() };
        let new = rewrite(&text, &mut file, &[to]).unwrap();
        assert_eq!(&new[span.start..span.start + 26], "'''\r\npub fn g() {}\r\nx\r\n'''");
        assert!(!new.replace("\r\n", "").contains('\n'), "every line end is CR LF");
    }

    /// The guard (X-3) on the `fixed` texts: a copy that leaves nothing where
    /// the text after the candidate holds a new error is not rewritten
    /// (`UPDATE_GOLDEN=worse` rewrites it and lists it); a copy that holds an
    /// error the output does not is rewritten; a listed row's copy is counted,
    /// not judged.
    #[test]
    fn the_guard_keeps_a_copy_that_holds_a_rule() {
        // The check reports the E0020 of the unit only; after the candidate, the E0302 of `b`.
        let src = "pub fn f() -> I32 {\n  let a = 1;\n  b\n}\n";
        let forms = FORMS.replace("pub fn f() -> I32 {\n  let a = 1;\n  a\n}\n'''", &format!("{src}'''"));
        let read = |r: &Path| std::fs::read_to_string(r.join(PATH)).unwrap();
        let r0 = root("guard", &forms, LISTED);
        let r = check(&r0, Update::Rewrite);
        assert!(r.rewritten.is_empty(), "{r:?}");
        assert!(
            matches!(&r.copy_failures[..], [m] if m.starts_with("semicolon: example 1: UPDATE_GOLDEN=1 does not rewrite \
                the copy `fixed` 1") && m.contains("E0302 at m.onsa:3:3") && m.contains("`property`")),
            "{r:?}"
        );
        assert_eq!(read(&r0), forms, "nothing written");
        let r = check(&r0, Update::Worse);
        assert!(r.copy_failures.is_empty(), "{r:?}");
        assert_eq!(r.rewritten, ["semicolon example 1 fixed 1"]);
        assert_eq!(r.forced, ["semicolon example 1 fixed 1 (E0302 at m.onsa:3:3)"]);
        assert!(read(&r0).contains("  let a = 1\n  b\n}\n''']"), "{}", read(&r0));
        // A copy that holds an error (`c`) the output does not: rewritten.
        let wrong = FORMS.replace("  let a = 1\n  a\n}\n''']", "  let a = 1\n  c\n}\n''']");
        let r1 = root("guard_wrong", &wrong, LISTED);
        let r = check(&r1, Update::Rewrite);
        assert!(r.copy_failures.is_empty() && r.forced.is_empty(), "{r:?}");
        assert_eq!(r.rewritten, ["semicolon example 1 fixed 1"]);
        assert_eq!(read(&r1), FORMS);
        // Listed: not judged, not rewritten, counted.
        let listed = LISTED.replace("let_mut", "semicolon");
        let r2 = root("guard_listed", &wrong, &listed);
        let r = check(&r2, Update::Rewrite);
        assert!(r.copy_failures.is_empty() && r.rewritten.is_empty() && r.unjudged_copies == 1, "{r:?}");
        assert_eq!(read(&r2), wrong);
        for r in [r0, r1, r2] {
            let _ = std::fs::remove_dir_all(r);
        }
    }
}
