//! The markers against the diagnostics, and the fmt and parser checks of a file.

use std::fmt::Write as _;

use onsa_diag::{Code, Diagnostic, FileId, SourceMap};

use crate::Expected;

use super::{CaseRun, CheckedMarker, Problem, Stage};

/// Compare the markers with the diagnostics, record every marker compared,
/// and report a difference. Whether they match. Every diagnostic is also
/// checked against the rules of diagnostics (a break is an internal error).
pub(super) fn compare(
    run: &mut CaseRun,
    sources: &SourceMap,
    expected: &[(FileId, Expected)],
    actual: &[Diagnostic],
    stage: Stage,
    target: Option<&str>,
) -> bool {
    let actual_pos: Vec<(FileId, Code, u32, u32)> = actual
        .iter()
        .map(|d| {
            let lc = sources.file(d.span.file).line_col(d.span.start);
            (d.span.file, d.code, lc.line, lc.col)
        })
        .collect();
    for p in onsa_syntax::diagnostic_contract(sources, actual) {
        run.problems.push(Problem::Internal(format!("a diagnostic breaks the rules of diagnostics (plan D-04): {p}")));
    }
    let mut used = vec![false; actual_pos.len()];
    // Markers with a column first, so a marker without one cannot take their diagnostic.
    let mut order: Vec<usize> = (0..expected.len()).collect();
    order.sort_by_key(|&i| expected[i].1.col.is_none());
    let mut all = true;
    let mut matched = vec![false; expected.len()];
    for i in order {
        let (f, e) = &expected[i];
        let hit = actual_pos.iter().enumerate().position(|(k, (af, code, line, col))| {
            !used[k] && af == f && *code == e.code && *line == e.line && e.col.is_none_or(|c| c == *col)
        });
        match hit {
            Some(k) => {
                used[k] = true;
                matched[i] = true;
            }
            None => all = false,
        }
    }
    for (i, (f, e)) in expected.iter().enumerate() {
        run.checked.push(CheckedMarker {
            code: e.code,
            file: sources.file(*f).name().to_string(),
            line: e.line,
            stage,
            target: target.map(str::to_string),
            matched: matched[i],
        });
    }
    let ok = all && used.iter().all(|u| *u);
    if !ok {
        let render_e = |(f, e): &(FileId, Expected)| {
            let col = e.col.map(|c| format!(":{c}")).unwrap_or_default();
            format!("{}@{}:{}{col}", e.code.as_str(), sources.file(*f).name(), e.line)
        };
        let render_a = |(f, code, line, col): &(FileId, Code, u32, u32)| {
            format!("{}@{}:{line}:{col}", code.as_str(), sources.file(*f).name())
        };
        let mut msg = match target {
            Some(t) => format!("the build of `{t}` differs from the markers\n"),
            None => format!("the {stage:?} diagnostics differ from the markers\n").to_lowercase(),
        };
        let none = |v: Vec<String>| if v.is_empty() { "(none)".to_string() } else { v.join(" ") };
        let _ = writeln!(msg, "  expected: {}", none(expected.iter().map(render_e).collect()));
        let _ = writeln!(msg, "  actual:   {}", none(actual_pos.iter().map(render_a).collect()));
        let _ = write!(msg, "  {}", onsa_diag::to_text(sources, actual).replace('\n', "\n  "));
        run.problems.push(Problem::Failed(msg.trim_end().to_string()));
    }
    ok
}

/// A code only the syntax stage reports: its markers come from the parser alone.
fn syntax_only(c: Code) -> bool {
    c.stages() == [onsa_diag::Stage::Syntax]
}

/// The diagnostics of the parser alone (before the later stages; one per
/// unit, as `check` chooses, `onsa_driver::reduce`) against the markers of the
/// file: each one
/// matches a marker of its line and code, and every marker of a code only
/// the syntax stage reports is one of them. Markers of a code that later
/// stages report too (E0020, E0408, ...) are compared by the check only.
pub(super) fn parser_markers(run: &mut CaseRun, sources: &SourceMap, file: FileId, markers: &[(FileId, Expected)]) {
    let f = sources.file(file);
    let parsed = onsa_syntax::parse(file, f.text());
    let reduced = onsa_driver::reduce::per_unit([(file, &parsed.units)], parsed.diagnostics.clone()).diagnostics;
    let mut actual: Vec<(u32, Code)> = reduced.iter().map(|d| (f.line_col(d.span.start).line, d.code)).collect();
    let mut expected: Vec<(u32, Code)> =
        markers.iter().filter(|(mf, _)| *mf == file).map(|(_, m)| (m.line, m.code)).collect();
    expected.sort();
    actual.sort();
    // Each parser diagnostic takes a marker of its line and code.
    let mut free = expected.clone();
    let mut unmatched = Vec::new();
    for a in &actual {
        match free.iter().position(|e| e == a) {
            Some(i) => {
                free.remove(i);
            }
            None => unmatched.push(*a),
        }
    }
    let missing: Vec<(u32, Code)> = free.into_iter().filter(|(_, c)| syntax_only(*c)).collect();
    if !unmatched.is_empty() || !missing.is_empty() {
        let show = |v: &[(u32, Code)]| {
            if v.is_empty() {
                "(none)".to_string()
            } else {
                v.iter().map(|(l, c)| format!("{}@{l}", c.as_str())).collect::<Vec<_>>().join(" ")
            }
        };
        run.problems.push(Problem::Failed(format!(
            "{}: the parser's diagnostics differ from the markers\n  without a marker: {}\n  markers of syntax-only codes the parser does not report: {}\n  {}",
            f.name(),
            show(&unmatched),
            show(&missing),
            onsa_diag::to_text(sources, &reduced).replace('\n', "\n  ")
        )));
    }
}

/// A file without markers is already canonical: `fmt` leaves it unchanged
/// and is idempotent (M1, T1-9). A case that says `canonical = false` (a line
/// break fmt moves, W3-11) is not compared with the normal form, and only
/// that: fmt takes it, its output parses with no diagnostic and is taken
/// again unchanged, and fmt changes one of the files of the case at least
/// (else the setting is to go; the caller judges it from the result: whether
/// fmt changed this file). That the output is the program of the input is
/// checked by `onsa_syntax::format` itself (R-204, `spec/tools.md`
/// §3.5); a failed check is a problem of the case.
pub(super) fn canonical(run: &mut CaseRun, name: &str, text: &str, normal: bool) -> bool {
    // `of` names the input of the format that failed: the file, or fmt's own output.
    let unverified = |of: &str, text: &str, d: &onsa_syntax::diff::Difference| {
        let line = text[..d.at.start as usize].matches('\n').count() + 1;
        Problem::Failed(format!("{name}: fmt changes the program of {of}: {} (line {line})", d.place))
    };
    let parsed = onsa_syntax::parse(FileId(0), text);
    let out = match onsa_syntax::format(&parsed, text) {
        Ok(out) => out,
        Err(onsa_syntax::fmt::FormatError::Syntax) => {
            run.problems.push(Problem::Failed(format!("{name}: fmt refused it (diagnostics)")));
            return false;
        }
        Err(onsa_syntax::fmt::FormatError::Unverified(d)) => {
            run.problems.push(unverified("the file", text, &d));
            return true;
        }
    };
    if normal && out != text {
        run.problems.push(Problem::Failed(format!("{name}: fmt changes it\n{}", first_diff(text, &out))));
        return true;
    }
    let again = onsa_syntax::parse(FileId(0), &out);
    if !normal && !again.diagnostics.is_empty() {
        run.problems.push(Problem::Failed(format!("{name}: the output of fmt does not parse\n{out}")));
        return true;
    }
    match onsa_syntax::format(&again, &out) {
        Ok(twice) if twice == out => {}
        Err(onsa_syntax::fmt::FormatError::Unverified(d)) => run.problems.push(unverified("its own output", &out, &d)),
        _ => run.problems.push(Problem::Failed(format!("{name}: fmt is not idempotent on it"))),
    }
    out != text
}

fn first_diff(a: &str, b: &str) -> String {
    let (al, bl): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    for i in 0..al.len().max(bl.len()) {
        let x = al.get(i).copied().unwrap_or("<eof>");
        let y = bl.get(i).copied().unwrap_or("<eof>");
        if x != y {
            return format!("  line {}:\n  - {x}\n  + {y}", i + 1);
        }
    }
    String::from("  (no line diff; whitespace at end?)")
}

/// T2-12: every diagnostic of a negative example carries the offending source
/// (`found`, §18.1), but one whose main range is empty: there `found` is not
/// given (§18.1: an empty range or one of blanks has none; a line that ends
/// where it cannot is reported at the end of its code, W3-06). Whether a code
/// needs a fix candidate is the registry's (`Code::fix_rule`), checked on
/// every diagnostic by [`compare`].
pub(super) fn negative_rules(run: &mut CaseRun, path: &str, diags: &[Diagnostic]) {
    if !path.contains("negative") {
        return;
    }
    for d in diags.iter().filter(|d| lacks_found(d)) {
        run.problems.push(Problem::Failed(format!("{} at {} has no `found` text", d.code.as_str(), d.span.start)));
    }
}

/// The diagnostic has a main range with text but no `found` ([`negative_rules`]).
pub(super) fn lacks_found(d: &Diagnostic) -> bool {
    !d.span.is_empty() && d.found.as_deref().is_none_or(str::is_empty)
}
