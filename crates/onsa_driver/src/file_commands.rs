//! The commands on one file, outside the check of a package: the parse
//! alone, `onsa fmt`, `onsa dump --cst` and `--levels`, `onsa diff --ast`.

use onsa_diag::{Diagnostic, FileId, SourceMap, Span};

use crate::{CheckResult, InternalError, Loaded, guard, parse_file, reduce};

/// Parse only (the `mode = "parse"` depth of the test cases, D-05): the
/// Onsa files of `loaded` (not its `onsa.toml`).
pub fn parse_only(loaded: &Loaded) -> Result<CheckResult, InternalError> {
    guard(|| {
        let mut result = CheckResult::default();
        for id in loaded.modules.iter().map(|(f, _)| *f).chain(loaded.root_tests.iter().copied()) {
            let parsed = parse_file(id, loaded.sources.file(id).text());
            let diagnostics = parsed.diagnostics.clone();
            result.diagnostics.extend(reduce::per_unit([(id, &parsed.units)], diagnostics).diagnostics);
        }
        result
    })
}

/// The canonical text of a file (`onsa fmt`), or its syntax diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formatted {
    Text(String),
    /// The file has syntax diagnostics: it is not formatted (spec §18.2).
    Syntax(Vec<Diagnostic>),
}

/// Format the file `file` of `sources` (`onsa fmt`).
pub fn format_file(sources: &SourceMap, file: FileId) -> Result<Formatted, InternalError> {
    guard(|| {
        let text = sources.file(file).text();
        let parsed = parse_file(file, text);
        // A panic names the file (S-67).
        let _scope = onsa_diag::internal::item_scope(Span::new(file, 0, 0));
        formatted(&parsed, file, onsa_syntax::format(&parsed, text))
    })?
}

/// What `onsa fmt` makes of the formatter's result: an output that is not
/// the program of the input is an internal error at the first difference,
/// without a diagnostic code (`spec/tools.md` §3.5).
fn formatted(
    parsed: &onsa_syntax::Parsed,
    file: FileId,
    result: Result<String, onsa_syntax::fmt::FormatError>,
) -> Result<Formatted, InternalError> {
    use onsa_syntax::fmt::FormatError;
    match result {
        Ok(out) => Ok(Formatted::Text(out)),
        Err(FormatError::Syntax) => Ok(Formatted::Syntax(reduce::syntax_report(parsed, file))),
        Err(FormatError::Unverified(d)) => Err(InternalError::unverified(&d)),
    }
}

/// The CST of a file (`onsa dump --cst`, R-86): the text of its leaves
/// (the source, byte for byte) or, with `tree`, the tree as indented lines.
/// A file with syntax diagnostics has a CST too; they are not reported here.
/// The tree is checked (`Cst::validate`) by the parse itself: a broken tree is
/// an internal error.
pub fn cst_dump(sources: &SourceMap, file: FileId, tree: bool) -> Result<String, InternalError> {
    guard(|| {
        let text = sources.file(file).text();
        let parsed = parse_file(file, text);
        if tree { parsed.cst.tree(text) } else { parsed.cst.text(text) }
    })
}

/// The levels (spec §2.5) of each top-level item of a file that parsed, one
/// line each, in the order of the file (`onsa dump --levels`, for the fmt
/// properties: `tools/fmt_props.py`).
pub fn levels_dump(sources: &SourceMap, file: FileId) -> Result<String, InternalError> {
    guard(|| {
        let parsed = parse_file(file, sources.file(file).text());
        parsed.levels.iter().map(|l| format!("{l}\n")).collect()
    })
}

/// The structural difference of two files (`onsa diff --ast`).
#[derive(Debug, Clone)]
pub enum AstDiff {
    Items(Vec<onsa_syntax::diff::ItemDiff>),
    /// A file has syntax diagnostics: the files are not compared (spec §18.2).
    /// The diagnostics of both files (`reduce::syntax_report`).
    Syntax(Vec<Diagnostic>),
}

/// Compare the files `old` and `new` of `sources` (`onsa diff --ast`).
pub fn diff_ast(sources: &SourceMap, old: FileId, new: FileId) -> Result<AstDiff, InternalError> {
    guard(|| {
        let files = [old, new];
        let parsed: Vec<onsa_syntax::Parsed> =
            files.iter().map(|&file| parse_file(file, sources.file(file).text())).collect();
        if parsed.iter().any(|p| p.syntax_errors()) {
            // Both files are reported, not only the first with an error (`spec/tools.md` §3.1).
            // A file on both sides is reported once.
            let n = if old == new { 1 } else { 2 };
            return AstDiff::Syntax(
                parsed.iter().zip(files).take(n).flat_map(|(p, file)| reduce::syntax_report(p, file)).collect(),
            );
        }
        AstDiff::Items(onsa_syntax::diff::diff(&parsed[0], &parsed[1]))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::internal;

    /// R-204: an output of fmt that is not the program of its input is an
    /// internal error (101) that names the first difference and its place in
    /// the input, without a diagnostic code (`spec/tools.md` §3.5). A
    /// correct fmt does not make one, so the output is a false one.
    #[test]
    fn an_unverified_output_is_an_internal_error_at_the_place_in_the_input() {
        let mut sources = SourceMap::default();
        let file = sources.add("m.onsa", "fn f() -> I32 {\n  let a = 1\n  a // keep\n}\n");
        let text = sources.file(file).text();
        let parsed = onsa_syntax::parse(file, text);
        let fake = "fn f() -> I32 {\n  let a = 1\n  a\n}\n";
        let result = onsa_syntax::fmt::verify(&parsed, text, fake).map(|()| fake.to_string());
        let e = formatted(&parsed, file, result).unwrap_err();
        assert_eq!(e.origin, internal::Origin::Unverified);
        let shown = e.render(&sources);
        assert!(shown.starts_with("internal error: the output of fmt is not the same program: comment 1"), "{shown}");
        assert!(shown.contains("  --> m.onsa:3:5\n"), "{shown}");
        assert!(!shown.contains("error["), "{shown}");
        // The real formatter gives the text.
        assert_eq!(format_file(&sources, file), Ok(Formatted::Text(text.to_string())));
    }
}
