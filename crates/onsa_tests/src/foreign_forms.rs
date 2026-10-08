//! The closed list of the forms of other languages, `docs/foreign-forms.toml`
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
//! - a row whose examples do not pass yet waits in `tests/pending.toml` (kind
//!   `foreign-form`, the `id` as target): a listed row that passes, and a
//!   row that fails and is not listed, are failures, as for the other kinds.
//!
//! The data file is the spec's (the tests' side writes it); this module reads
//! it and never changes it.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;

use onsa_diag::Code;
use onsa_syntax::foreign::{Phase, ROWS, WAITING};

use crate::fix_contract::{self, TextCheck};
use crate::pending::{Kind, Pending};

/// The file, relative to the repository root.
pub const PATH: &str = "docs/foreign-forms.toml";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    #[serde(default)]
    form: Vec<Form>,
}

#[derive(Debug, Deserialize)]
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

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Example {
    source: String,
    /// The main position; the forms whose position the spec does not set leave it out.
    #[serde(default)]
    at: Option<String>,
    #[serde(default)]
    fixed: Option<Vec<String>>,
    #[serde(default)]
    property: Option<Vec<String>>,
    /// The number of candidates, for an example checked by its properties.
    #[serde(default)]
    candidates: Option<usize>,
}

/// What the table says of a row: its stage and code.
#[derive(Clone, Copy)]
struct Kind1 {
    phase: Phase,
    code: Code,
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
}

/// Check the data file under `root` against the table, with the list of
/// things pending.
pub fn check(root: &Path) -> Report {
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
    let rows: BTreeMap<&str, Kind1> = ROWS
        .iter()
        .map(|r| (r.name, Kind1 { phase: r.phase, code: r.code }))
        .chain(WAITING.iter().map(|w| (w.name, Kind1 { phase: w.phase, code: w.code })))
        .collect();
    for form in &file.form {
        let Some(row) = rows.get(form.id.as_str()) else { continue };
        report.rows += 1;
        report.examples += form.example.len();
        let mut problems = Vec::new();
        if form.example.is_empty() {
            problems.push("no example".to_string());
        }
        for (i, ex) in form.example.iter().enumerate() {
            for p in example(*row, ex) {
                problems.push(format!("example {}: {p}", i + 1));
            }
        }
        let listed = pending.get(Kind::ForeignForm, &form.id);
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
    if report.rows == 0 || report.examples == 0 {
        report.failures.push(format!("{PATH}: no row or no example was checked"));
    }
    for e in pending.of_kind(Kind::ForeignForm) {
        if !file.form.iter().any(|f| f.id == e.target) {
            report.failures.push(format!("tests/pending.toml: `{}` is not a row of {PATH}", e.target));
        }
    }
    report
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
fn example(row: Kind1, ex: &Example) -> Vec<String> {
    let mut out = Vec::new();
    let run: TextCheck = match fix_contract::check_text(&ex.source) {
        Ok(r) => r,
        Err(e) => return vec![format!("the check ends in an internal error: {e}")],
    };
    let sources = &run.loaded.sources;
    let place = |d: &onsa_diag::Diagnostic| {
        let lc = sources.file(d.span.file).line_col(d.span.start);
        format!("{}:{}", lc.line, lc.col)
    };
    let reported: Vec<String> =
        run.analyzed.diagnostics.iter().map(|d| format!("{} at {}", d.code.as_str(), place(d))).collect();
    let at = |d: &onsa_diag::Diagnostic| ex.at.as_ref().is_none_or(|a| place(d) == *a);
    let where_ = ex.at.as_deref().unwrap_or("any place");
    let Some(d) = run.analyzed.diagnostics.iter().find(|d| d.code == row.code && at(d)) else {
        out.push(format!("no {} at {where_}; the check reports {:?}", row.code.as_str(), reported));
        return out;
    };
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
        if let Some(want) = ex.fixed.as_ref().and_then(|f| f.get(k))
            && let Some(diff) = crate::fixes::first_difference(want, &after.text)
        {
            out.push(format!("candidate {}: the text after it differs from `fixed`: {diff}", k + 1));
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
    out
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
        let r = check(&root("plain", FORMS, ""));
        assert_eq!((r.rows, r.examples), (2, 2));
        // `let_mut`'s place is wrong: it fails, not listed.
        assert!(r.failures.iter().any(|f| f.starts_with("let_mut:") && f.contains("no E0020 at 2:4")), "{r:?}");
        assert!(!r.failures.iter().any(|f| f.starts_with("semicolon:")), "{r:?}");
        // The table has rows the file does not: one to one.
        assert!(r.failures.iter().any(|f| f.contains("has `loop`, which")), "{r:?}");
        // Listed, it waits.
        let r = check(&root("listed", FORMS, LISTED));
        assert_eq!(r.pending, ["let_mut"]);
        // A listed row that passes.
        let fixed = FORMS.replace("at = \"2:4\"", "at = \"2:3\"");
        let r = check(&root("passes", &fixed, LISTED));
        assert!(r.failures.iter().any(|f| f.contains("let_mut: the row passes but is listed")), "{r:?}");
        // A `fixed` that differs.
        let wrong = FORMS.replace("  let a = 1\n  a\n}\n''']", "  let a = 2\n  a\n}\n''']");
        let r = check(&root("wrong", &wrong, ""));
        assert!(r.failures.iter().any(|f| f.starts_with("semicolon:") && f.contains("differs from `fixed`")), "{r:?}");
    }
}
