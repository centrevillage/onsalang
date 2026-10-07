//! The expected fix candidates of a case (W3-02, R-87 (1), S-81, plan D-04).
//!
//! A case declares `fixes = N` in its `[test]` table. Next to each source file
//! `F` of the case, `F.fix1` .. `F.fixN` hold the text of `F` after the K-th
//! candidate of every diagnostic of the check is applied at once; a
//! diagnostic without a K-th candidate changes nothing for K. A file that no
//! K-th candidate edits has no `F.fixK` (an unchanged file is the original).
//!
//! The spec fixes the number and order of the candidates and the text they
//! give (§18.1), not which tokens an edit covers, its title or the messages.
//! So the expectation is the text after applying, compared token by token:
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
//! 4. the result matches `F.fixK` (or `F` when there is none, and a `F.fixK`
//!    of a file no candidate edits fails);
//!
//! and over the repository ([`orphans`]):
//! 5. a `.fixK` file that no case declares fails.

use std::path::{Path, PathBuf};

use onsa_diag::{Diagnostic, FileId, SourceMap};
use onsa_syntax::TokenKind;
use onsa_syntax::token::{Gap, gap_before};

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

/// Compare the candidates of `diagnostics` with the `.fixK` files. `files` are
/// the source files of the case and where they are on disk.
pub fn compare(sources: &SourceMap, files: &[(FileId, PathBuf)], diagnostics: &[Diagnostic], n: u32) -> Vec<Problem> {
    let mut out = Vec::new();
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
        for (file, disk) in files {
            let original = sources.file(*file).text();
            let expect_path = path(disk, k);
            let name = expect_path.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
            let expected = match std::fs::read_to_string(&expect_path) {
                Ok(t) => {
                    if !texts.contains_key(file) {
                        out.push(Problem::Failed(format!(
                            "fixes: no candidate {k} edits {}; remove {name}",
                            sources.file(*file).name()
                        )));
                        continue;
                    }
                    t
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => original.to_string(),
                Err(e) => {
                    out.push(Problem::Case(format!("fixes: cannot read {name}: {e}")));
                    continue;
                }
            };
            let actual = texts.get(file).map(String::as_str).unwrap_or(original);
            if let Some(diff) = first_difference(&expected, actual) {
                let what =
                    if texts.contains_key(file) { "after the candidates" } else { "unchanged by the candidates" };
                out.push(Problem::Failed(format!(
                    "fixes: {} {what} {k} differs from {}: {diff}",
                    sources.file(*file).name(),
                    if expect_path.exists() { name } else { "the source (there is no fix file)".into() }
                )));
            }
        }
    }
    out
}

/// One compared token: the gap before it (`None`: not compared), its kind
/// and text, and its line.
type Compared<'a> = (Option<Gap>, TokenKind, &'a str, usize);

/// The tokens compared: every token but whitespace, with the kind of the gap
/// before it ([`onsa_syntax::token::gap_before`]). The gap before a newline
/// (spaces at the end of a line, the CR of a CR LF, which is whitespace to
/// the lexer) is not compared: `None` there. The start of the file counts as
/// the start of a line, so its indentation is not compared either (a token
/// after a newline has the gap `Newline` with or without indentation).
fn compared(text: &str) -> Vec<Compared<'_>> {
    let tokens = onsa_syntax::lex(FileId(0), text).tokens;
    (0..tokens.len())
        .filter(|&i| !matches!(tokens[i].kind, TokenKind::Whitespace | TokenKind::Eof))
        .map(|i| {
            let t = tokens[i];
            let s = &text[t.span.start as usize..t.span.end as usize];
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
fn first_difference(expected: &str, actual: &str) -> Option<String> {
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
