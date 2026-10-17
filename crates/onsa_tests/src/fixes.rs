//! The expected fix candidates of a case (W3-02, R-87 (1), S-81, plan D-04).
//!
//! A case declares `fixes = N` in its `[test]` table. Next to each source file
//! `F` of the case, `F.fix1` .. `F.fixN` hold the text of `F` after the K-th
//! candidate of every diagnostic of the check is applied at once; a
//! diagnostic without a K-th candidate changes nothing for K. A file that no
//! K-th candidate edits has no `F.fixK` (an unchanged file is the original).
//!
//! The spec promises the number of the candidates (§18.1), not their text or
//! order (X-3, X3-1a): the `.fixK` files are copies of the implementation's
//! output (Q-04), change detectors, not the spec's expectation. A copy that
//! differs or is missing is [`Problem::FixCopy`], never a failure of the
//! contract: no entry of `tests/pending.toml` silences it, and a case listed
//! as a whole does not judge, rewrite or count its copies
//! ([`crate::run::reconcile`]). `UPDATE_GOLDEN=1` rewrites it (creates it,
//! removes the copy of a file no candidate edits), unless the guard refuses
//! changing or removing a copy ([`crate::copy_guard`]), and the parent reads
//! the change. The number (`fixes = N`) is the test's and is never rewritten. A
//! copy is compared token by token:
//! **the width of whitespace is ignored; every token but whitespace (newlines
//! and comments included) is compared by kind and text, in order, with the
//! kind of the gap before it (nothing, spaces, a newline:
//! `onsa_syntax::token::gap_before`).** So `f (x)` and `f(x)`, `a . b` and
//! `a.b` differ (the candidates of the spacing rules are seen), while one
//! space and two are the same (the width a removed `pub(pkg)` leaves is not
//! the spec's); the lines and the comments are compared. The gap before a
//! newline (spaces at the end of a line, the CR of a CR LF) and the
//! indentation at the start of the file are not compared.
//!
//! The runner checks, for a case with `fixes = N` ([`compare`]):
//! 1. for every K in 1..=N, some diagnostic has a K-th candidate (nothing passes vacuously);
//! 2. no diagnostic has more than N candidates (the count is the expectation's);
//! 3. the K-th candidates of different diagnostics do not overlap (else split
//!    the case: an error of the case);
//! 4. the result matches the copy `F.fixK` (a file the candidates edit has
//!    one; a file they do not edit has none): else a `FixCopy`; when
//!    rewriting, a K that changes or removes a copy goes through the guard
//!    first, and is written whole or not at all;
//!
//! and over the repository ([`orphans`]):
//! 5. a `.fixK` file that no case declares fails.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use onsa_diag::{Diagnostic, FileId, SourceMap};
use onsa_syntax::TokenKind;
use onsa_syntax::token::{Gap, gap_before};

use crate::golden::Update;
use crate::run::Problem;

/// The expectation of candidate `k` for the source file at `source`: `<source>.fix<k>`.
pub fn path(source: &Path, k: u32) -> PathBuf {
    let mut s = source.as_os_str().to_os_string();
    s.push(format!(".fix{k}"));
    PathBuf::from(s)
}

/// `<source>.fix<k>` split into the source's name and `k`, when the name has that form.
pub fn split_name(name: &str) -> Option<(&str, u32)> {
    let (base, k) = name.rsplit_once(".fix")?;
    if base.is_empty() || k.is_empty() || !k.bytes().all(|b| b.is_ascii_digit()) || k.starts_with('0') {
        return None;
    }
    Some((base, k.parse().ok()?))
}

/// What [`compare`] found of the copies.
#[derive(Debug, Default)]
pub struct CopyCheck {
    pub problems: Vec<Problem>,
    /// The copies read and compared (or rewritten).
    pub copies: usize,
    /// The copies written or removed (`UPDATE_GOLDEN=1`).
    pub rewritten: Vec<PathBuf>,
    /// Those of `rewritten` the guard refused and `UPDATE_GOLDEN=worse`
    /// wrote, with the diagnostics only the new texts report.
    pub forced: Vec<(PathBuf, String)>,
    /// The candidates K whose copies went through the guard.
    pub guarded: usize,
}

/// The guard of the copies of one K ([`crate::copy_guard::case`]): the
/// texts of the copies and the texts after the candidates, each in place of
/// its file; the diagnostics only the second reports, or why it cannot tell.
pub type Guard<'a> = &'a dyn Fn(&BTreeMap<FileId, String>, &BTreeMap<FileId, String>) -> Result<Vec<String>, String>;

/// Compare the candidates of `diagnostics` with the `.fixK` files. `files` are
/// the source files of the case and where they are on disk. `update`: whether
/// to rewrite the copies that differ (`Off` for a pending case), through
/// `guard` when a copy changes or goes.
pub fn compare(
    sources: &SourceMap,
    files: &[(FileId, PathBuf)],
    diagnostics: &[Diagnostic],
    n: u32,
    update: Update,
    guard: Guard<'_>,
) -> CopyCheck {
    let mut done = CopyCheck::default();
    let out = &mut done.problems;
    let at = |d: &Diagnostic| {
        let f = sources.file(d.span.file);
        let lc = f.line_col(d.span.start);
        format!("{} at {}:{}:{}", d.code.as_str(), f.name(), lc.line, lc.col)
    };
    for d in diagnostics {
        if d.fixes.len() > n as usize {
            out.push(Problem::Failed(format!(
                "fixes: {} has {} candidates, more than `fixes = {n}` declares",
                at(d),
                d.fixes.len()
            )));
        }
    }
    for k in 1..=n {
        let with_k: Vec<&Diagnostic> = diagnostics.iter().filter(|d| d.fixes.len() >= k as usize).collect();
        if with_k.is_empty() {
            out.push(Problem::Failed(format!(
                "fixes: no diagnostic has a candidate {k} (`fixes = {n}`; the check reports {} diagnostics)",
                diagnostics.len()
            )));
            continue;
        }
        let edits: Vec<(&onsa_diag::Edit, &Diagnostic)> =
            with_k.iter().flat_map(|d| d.fixes[k as usize - 1].edits().iter().map(move |e| (e, *d))).collect();
        let plain: Vec<&onsa_diag::Edit> = edits.iter().map(|(e, _)| *e).collect();
        if let Some((a, b)) = onsa_diag::overlap(&plain) {
            out.push(Problem::Case(format!(
                "fixes: the candidates {k} of {} and {} overlap; put them in different cases",
                at(edits[a].1),
                at(edits[b].1)
            )));
            continue;
        }
        if let Some((e, d)) = edits.iter().find(|(e, _)| !files.iter().any(|(f, _)| *f == e.span.file)) {
            out.push(Problem::Failed(format!(
                "fixes: candidate {k} of {} edits a file outside the case ({})",
                at(d),
                sources.file(e.span.file).name()
            )));
            continue;
        }
        let texts = match onsa_diag::apply(sources, plain.iter().copied()) {
            Ok(t) => t,
            Err(e) => {
                out.push(Problem::Failed(format!("fixes: the candidates {k} cannot be applied: {e}")));
                continue;
            }
        };
        // Every copy is read first: the old side of the guard holds them all.
        let mut old: BTreeMap<FileId, String> = BTreeMap::new();
        let mut plans: Vec<(PathBuf, Option<&String>, bool)> = Vec::new();
        let mut unread = false;
        for (file, disk) in files {
            let copy = path(disk, k);
            let name = copy.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
            let expected = match std::fs::read_to_string(&copy) {
                Ok(t) => Some(t),
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(e) => {
                    out.push(Problem::Case(format!("fixes: cannot read {name}: {e}")));
                    unread = true;
                    continue;
                }
            };
            let source = sources.file(*file).name();
            let actual = texts.get(file);
            let why = match (actual, &expected) {
                (None, None) => None,
                (Some(actual), Some(expected)) => first_difference(expected, actual)
                    .map(|diff| format!("{source} after the candidates {k} differs from the copy {name}: {diff}")),
                (Some(_), None) => Some(format!("the candidates {k} edit {source}, but its copy {name} is missing")),
                (None, Some(_)) => Some(format!("no candidate {k} edits {source}, but it has the copy {name}")),
            };
            let had = expected.is_some();
            if let Some(t) = expected {
                done.copies += 1;
                old.insert(*file, t);
            }
            match why {
                None => {}
                Some(why) if !update.writes() => {
                    out.push(Problem::FixCopy(format!("fixes: {why} (UPDATE_GOLDEN=1 rewrites the copy)")))
                }
                Some(_) => plans.push((copy, actual, had)),
            }
        }
        if unread || plans.is_empty() {
            continue;
        }
        // Changing or removing a copy goes through the guard; creating one does not.
        let mut forced = None;
        if plans.iter().any(|(_, _, had)| *had) {
            done.guarded += 1;
            let names = || {
                plans
                    .iter()
                    .map(|(c, _, _)| c.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            match guard(&old, &texts) {
                Ok(found) if found.is_empty() => {}
                Ok(found) if update == Update::Worse => forced = Some(found.join(", ")),
                Ok(found) => {
                    out.push(Problem::FixCopy(format!(
                        "fixes: {}",
                        crate::copy_guard::refused(
                            &format!("the copies of the candidates {k} ({})", names()),
                            &found,
                            "a property of `[[test.fix]]` (`clean`, `same_code`, `leaves`)"
                        )
                    )));
                    continue;
                }
                Err(e) => {
                    out.push(Problem::FixCopy(format!(
                        "fixes: the copies of the candidates {k} ({}) are not rewritten: {e}",
                        names()
                    )));
                    continue;
                }
            }
        }
        for (copy, actual, _) in plans {
            let written = match actual {
                Some(actual) => std::fs::write(&copy, actual),
                None => std::fs::remove_file(&copy),
            };
            match written {
                Ok(()) => {
                    if let Some(found) = &forced {
                        done.forced.push((copy.clone(), found.clone()));
                    }
                    done.rewritten.push(copy);
                }
                Err(e) => out.push(Problem::Case(format!("fixes: cannot rewrite {}: {e}", copy.display()))),
            }
        }
    }
    done
}

/// One compared token: the gap before it (`None`: not compared), its kind
/// and text, and its line.
type Compared<'a> = (Option<Gap>, TokenKind, &'a str, usize);

/// The tokens compared: every token but whitespace, with the kind of the gap
/// before it ([`onsa_syntax::token::gap_before`]). The gap before a newline
/// (spaces at the end of a line) is not compared: `None` there, and a
/// newline is one whether it is LF or CR LF (§2.5). The start of the file counts as
/// the start of a line, so its indentation is not compared either (a token
/// after a newline has the gap `Newline` with or without indentation).
fn compared(text: &str) -> Vec<Compared<'_>> {
    let tokens = onsa_syntax::lex(FileId(0), text).tokens;
    (0..tokens.len())
        .filter(|&i| !matches!(tokens[i].kind, TokenKind::Whitespace | TokenKind::Eof))
        .map(|i| {
            let t = tokens[i];
            let s = if t.kind == TokenKind::Newline { "\n" } else { &text[t.span.start as usize..t.span.end as usize] };
            let gap = if t.kind == TokenKind::Newline {
                None
            } else if tokens[..i].iter().all(|p| p.kind == TokenKind::Whitespace) {
                Some(Gap::Newline)
            } else {
                Some(gap_before(&tokens, i))
            };
            (gap, t.kind, s, text[..t.span.start as usize].matches('\n').count() + 1)
        })
        .collect()
}

/// Where `actual` first differs from `expected` (the width of whitespace aside).
pub(crate) fn first_difference(expected: &str, actual: &str) -> Option<String> {
    let (e, a) = (compared(expected), compared(actual));
    let token = |t: Option<&Compared>| match t {
        Some((_, TokenKind::Newline, _, line)) => format!("a newline (line {line})"),
        Some((_, _, s, line)) => format!("`{s}` (line {line})"),
        None => "the end".to_string(),
    };
    let gap = |g: Option<Gap>| match g {
        Some(Gap::None) => "nothing",
        Some(Gap::Space) => "a space",
        Some(Gap::Newline) => "a line break",
        None => "(not compared)",
    };
    let same_token = |x: Option<&Compared>, y: Option<&Compared>| x.map(|t| (t.1, t.2)) == y.map(|t| (t.1, t.2));
    let i = (0..e.len().max(a.len())).find(|&i| {
        let (x, y) = (e.get(i), a.get(i));
        !same_token(x, y) || x.map(|t| t.0) != y.map(|t| t.0)
    })?;
    let (x, y) = (e.get(i), a.get(i));
    if same_token(x, y) {
        return Some(format!(
            "before {}: expected {}, got {}",
            token(y),
            gap(x.and_then(|t| t.0)),
            gap(y.and_then(|t| t.0))
        ));
    }
    Some(format!("expected {}, got {}", token(x), token(y)))
}

/// The `.fixK` files under `root/tests` that no case declares: the case of
/// the source file is missing, or declares fewer candidates than K.
/// `declared` holds every source file of a case on disk (from the root) with
/// its `fixes = N`.
pub fn orphans(root: &Path, declared: &[(PathBuf, u32)]) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![root.join(crate::case::TESTS)];
    while let Some(d) = stack.pop() {
        let entries = match std::fs::read_dir(&d) {
            Ok(e) => e,
            Err(e) => {
                out.push(format!("{}: cannot read the directory: {e}", d.display()));
                continue;
            }
        };
        for e in entries {
            let e = match e {
                Ok(e) => e,
                Err(e) => {
                    out.push(format!("{}: cannot read an entry: {e}", d.display()));
                    continue;
                }
            };
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            let name = e.file_name().to_string_lossy().into_owned();
            let Some((base, k)) = split_name(&name) else { continue };
            let source = p.with_file_name(base);
            let rel = p.strip_prefix(root).unwrap_or(&p).to_string_lossy().replace('\\', "/");
            match declared.iter().find(|(s, _)| root.join(s) == source) {
                Some((_, n)) if k <= *n => {}
                Some((_, n)) => {
                    out.push(format!("{rel}: its case declares `fixes = {n}`, not {k}; remove it or declare it"))
                }
                None => out.push(format!("{rel}: no case declares fix files for {base}; remove it or declare `fixes`")),
            }
        }
    }
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names() {
        assert_eq!(split_name("a.onsa.fix1"), Some(("a.onsa", 1)));
        assert_eq!(split_name("a.onsa.fix12"), Some(("a.onsa", 12)));
        assert_eq!(split_name("a.onsa.fix"), None);
        assert_eq!(split_name("a.onsa.fix0"), None);
        assert_eq!(split_name("a.onsa.fixx"), None);
        assert_eq!(path(Path::new("t/a.onsa"), 2), PathBuf::from("t/a.onsa.fix2"));
    }

    /// The copies (Q-04, X-3): a copy that differs, is missing or is of a file
    /// no candidate edits is a `FixCopy`; writing rewrites only the copies,
    /// never the number.
    #[test]
    fn copies_are_rewritten_but_the_number_is_not() {
        use onsa_diag::{Code, Fix, Span, Stage};
        let dir = crate::c::scratch_dir("onsa_test", "fix_copies");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mut sources = SourceMap::default();
        let a = sources.add("a.onsa", "let mut n = 0\n");
        let b = sources.add("b.onsa", "x\n");
        let files = vec![(a, dir.join("a.onsa")), (b, dir.join("b.onsa"))];
        let (copy_a, copy_b) = (dir.join("a.onsa.fix1"), dir.join("b.onsa.fix1"));
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, Span::new(a, 0, 7), "m").with_fix(Fix::replace(
            "var",
            Span::new(a, 0, 7),
            "var",
        ));
        let pass: Guard = &|_, _| Ok(Vec::new());
        let run = |n: u32, write: bool| {
            let update = if write { Update::Rewrite } else { Update::Off };
            compare(&sources, &files, std::slice::from_ref(&d), n, update, pass)
        };
        let copy = |r: &CopyCheck, text: &str| {
            r.problems.len() == 1 && matches!(&r.problems[0], Problem::FixCopy(m) if m.contains(text))
        };
        // Missing; written, it is created, and then the same.
        let r = run(1, false);
        assert!(copy(&r, "its copy a.onsa.fix1 is missing"), "{r:?}");
        let r = run(1, true);
        assert!(r.problems.is_empty() && r.rewritten == [copy_a.clone()], "{r:?}");
        assert_eq!(std::fs::read_to_string(&copy_a).unwrap(), "var n = 0\n");
        let r = run(1, false);
        assert!(r.problems.is_empty() && r.copies == 1, "{r:?}");
        // The width of blanks is not a difference: nothing rewritten.
        std::fs::write(&copy_a, "var  n = 0\n").unwrap();
        assert!(run(1, true).rewritten.is_empty());
        assert_eq!(std::fs::read_to_string(&copy_a).unwrap(), "var  n = 0\n");
        // A copy that differs.
        std::fs::write(&copy_a, "var n = 1\n").unwrap();
        assert!(copy(&run(1, false), "a.onsa after the candidates 1 differs from the copy a.onsa.fix1"));
        assert_eq!(run(1, true).rewritten, std::slice::from_ref(&copy_a));
        assert_eq!(std::fs::read_to_string(&copy_a).unwrap(), "var n = 0\n");
        // The copy of a file no candidate edits: removed when written.
        std::fs::write(&copy_b, "y\n").unwrap();
        assert!(copy(&run(1, false), "no candidate 1 edits b.onsa, but it has the copy b.onsa.fix1"));
        assert_eq!(run(1, true).rewritten, std::slice::from_ref(&copy_b));
        assert!(!copy_b.exists());
        // The number is never rewritten: a candidate 2 that is not there, and
        // more candidates than declared, fail when writing too.
        let r = run(2, true);
        assert!(
            r.problems.iter().any(|p| matches!(p, Problem::Failed(m) if m.contains("no diagnostic has a candidate 2")))
        );
        assert!(!dir.join("a.onsa.fix2").exists());
        let two = d.clone().with_fix(Fix::replace("val", Span::new(a, 0, 7), "let"));
        let r = compare(&sources, &files, std::slice::from_ref(&two), 1, Update::Rewrite, pass);
        assert!(
            r.problems.iter().any(|p| matches!(p, Problem::Failed(m) if m.contains("more than `fixes = 1`"))),
            "{r:?}"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The guard (X-3): changing or removing a copy asks it, creating one
    /// does not; a refusal writes nothing of the K, `worse` writes it all and
    /// records it, an error of the guard writes nothing even with `worse`.
    /// The old side holds every copy of the K, the new side the texts after.
    #[test]
    fn the_guard_decides_a_rewriting_of_the_whole_candidate() {
        use onsa_diag::{Code, Fix, Span, Stage};
        use std::cell::RefCell;
        let dir = crate::c::scratch_dir("onsa_test", "fix_guard");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mut sources = SourceMap::default();
        let a = sources.add("a.onsa", "let mut n = 0\n");
        let b = sources.add("b.onsa", "x\n");
        let files = vec![(a, dir.join("a.onsa")), (b, dir.join("b.onsa"))];
        let (copy_a, copy_b) = (dir.join("a.onsa.fix1"), dir.join("b.onsa.fix1"));
        let d = Diagnostic::new(Stage::Syntax, Code::E0020, Span::new(a, 0, 7), "m").with_fix(Fix::replace(
            "var",
            Span::new(a, 0, 7),
            "var",
        ));
        type Texts = BTreeMap<FileId, String>;
        let seen: RefCell<Vec<(Texts, Texts)>> = RefCell::new(Vec::new());
        let answer: RefCell<Result<Vec<String>, String>> = RefCell::new(Ok(vec!["E0302 at b.onsa:1:1".into()]));
        let guard: Guard = &|old, new| {
            seen.borrow_mut().push((old.clone(), new.clone()));
            answer.borrow().clone()
        };
        let run = |update| compare(&sources, &files, std::slice::from_ref(&d), 1, update, guard);
        // Creating: the guard is not asked, even when it would refuse.
        let r = run(Update::Rewrite);
        assert!(r.problems.is_empty() && r.rewritten == [copy_a.clone()] && r.guarded == 0, "{r:?}");
        assert!(seen.borrow().is_empty());
        // Changing one copy and removing another: refused, nothing written.
        std::fs::write(&copy_a, "var n = 1\n").unwrap();
        std::fs::write(&copy_b, "y\n").unwrap();
        let r = run(Update::Rewrite);
        assert_eq!(r.guarded, 1);
        assert!(r.rewritten.is_empty(), "{r:?}");
        let refused = |m: &str| {
            m.contains("does not rewrite the copies of the candidates 1 (a.onsa.fix1, b.onsa.fix1)")
                && m.contains("reports E0302 at b.onsa:1:1")
                && m.contains("`leaves`")
        };
        assert!(matches!(&r.problems[..], [Problem::FixCopy(m)] if refused(m)), "{r:?}");
        assert_eq!(std::fs::read_to_string(&copy_a).unwrap(), "var n = 1\n");
        assert!(copy_b.exists());
        let (old, new) = seen.borrow()[0].clone();
        assert_eq!(old, BTreeMap::from([(a, "var n = 1\n".to_string()), (b, "y\n".to_string())]));
        assert_eq!(new, BTreeMap::from([(a, "var n = 0\n".to_string())]));
        // An error of the guard: nothing written, even with `worse`.
        *answer.borrow_mut() = Err("the check of the copies ends in an internal error: x".into());
        let r = run(Update::Worse);
        assert!(r.rewritten.is_empty() && r.forced.is_empty(), "{r:?}");
        assert!(
            matches!(&r.problems[..], [Problem::FixCopy(m)] if m.contains("are not rewritten: the check")),
            "{r:?}"
        );
        // `worse`: written, and recorded.
        *answer.borrow_mut() = Ok(vec!["E0302 at b.onsa:1:1".into()]);
        let r = run(Update::Worse);
        assert!(r.problems.is_empty(), "{r:?}");
        assert_eq!(r.rewritten, [copy_a.clone(), copy_b.clone()]);
        assert_eq!(
            r.forced.iter().map(|(p, f)| (p.clone(), f.as_str())).collect::<Vec<_>>(),
            [(copy_a.clone(), "E0302 at b.onsa:1:1"), (copy_b.clone(), "E0302 at b.onsa:1:1")]
        );
        assert_eq!(std::fs::read_to_string(&copy_a).unwrap(), "var n = 0\n");
        assert!(!copy_b.exists());
        // Nothing new after it: written.
        std::fs::write(&copy_a, "var n = 1\n").unwrap();
        *answer.borrow_mut() = Ok(Vec::new());
        let r = run(Update::Rewrite);
        assert!(r.problems.is_empty() && r.rewritten == [copy_a.clone()] && r.forced.is_empty(), "{r:?}");
        // Comparing only: the guard is not asked.
        let asked = seen.borrow().len();
        std::fs::write(&copy_a, "var n = 1\n").unwrap();
        assert_eq!(run(Update::Off).problems.len(), 1);
        assert_eq!(seen.borrow().len(), asked);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn the_width_of_whitespace_is_ignored_and_its_presence_lines_and_comments_are_not() {
        assert_eq!(first_difference("let a = 1 // c\n", "let  a  =  1    // c\n"), None, "one space or more");
        assert!(first_difference("let a = 1\n", "let a=1\n").is_some(), "a space or none");
        assert!(first_difference("f(x)\n", "f (x)\n").is_some(), "`f (x)` is not `f(x)`");
        assert!(first_difference("a.b\n", "a . b\n").is_some(), "`a . b` is not `a.b`");
        assert!(first_difference("x?\n", "x ?\n").is_some(), "`x ?` is not `x?`");
        assert!(first_difference("a.b\n", "a\n.b\n").is_some(), "a line break before `.` is not nothing");
        assert_eq!(first_difference("a\n", "a \n"), None, "spaces at the end of a line");
        assert_eq!(first_difference("a\n", "a\t\n"), None, "a tab at the end of a line");
        assert_eq!(first_difference("a\nb\n", "a\r\nb\r\n"), None, "CR LF and LF");
        assert_eq!(first_difference("a\n", " a\n"), None, "the indentation at the start of the file");
        assert_eq!(first_difference("f\n  a\n", "f\na\n"), None, "the indentation after a newline");
        let d = first_difference("f(x)\n", "f (x)\n").unwrap();
        assert_eq!(d, "before `(` (line 1): expected nothing, got a space");
        assert!(first_difference("let a = 1\n", "let a =\n1\n").is_some(), "a newline moved");
        assert!(first_difference("let a = 1 // c\n", "let a = 1 // d\n").is_some(), "a comment changed");
        assert!(first_difference("var a = 1\n", "let a = 1\n").is_some());
    }
}
