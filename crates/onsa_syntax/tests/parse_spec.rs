//! Every file under `tests/spec` (except `mode: none`) must parse; the only
//! diagnostics allowed are those marked on the same line with `//~ CODE`
//! (D-05). M1, T1-11.

use std::path::Path;

use onsa_diag::{FileId, SourceMap};

fn spec_files() -> Vec<std::path::PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec");
    let mut files = Vec::new();
    let mut stack = vec![dir];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap().flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                files.push(p);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn spec_files_parse() {
    let files = spec_files();
    assert!(!files.is_empty());
    let mut failures = Vec::new();
    for p in &files {
        let text = std::fs::read_to_string(p).unwrap();
        if text.starts_with("//! mode: none") {
            continue;
        }
        let parsed = onsa_syntax::parse(FileId(0), &text);
        let mut sources = SourceMap::default();
        let f = sources.add(p.to_string_lossy(), text.clone());
        let src = sources.file(f);
        let mut expected: Vec<(u32, String)> = Vec::new();
        for (i, line) in text.lines().enumerate() {
            if let Some(idx) = line.find("//~") {
                for m in line[idx + 3..].split("//~") {
                    if let Some(code) = m.split_whitespace().next() {
                        expected.push((i as u32 + 1, code.to_string()));
                    }
                }
            }
        }
        let mut actual: Vec<(u32, String)> =
            parsed.diagnostics.iter().map(|d| (src.line_col(d.span.start).line, d.code.as_str().to_string())).collect();
        expected.sort();
        actual.sort();
        if expected != actual {
            failures.push(format!(
                "{}\n  expected {expected:?}\n  actual   {actual:?}\n{}",
                p.display(),
                onsa_diag::to_text(&sources, &parsed.diagnostics)
            ));
        }
    }
    assert!(failures.is_empty(), "{} spec file(s) failed:\n{}", failures.len(), failures.join("\n"));
}
