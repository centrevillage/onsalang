//! Every spec example (not `mode: none`, no `//~` markers) is already canonical:
//! `fmt` must leave it unchanged and be idempotent (M1, T1-9).

use std::path::Path;

use onsa_diag::FileId;

#[test]
fn spec_files_are_canonical() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec");
    let mut files = Vec::new();
    let mut stack = vec![dir.clone()];
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
    assert!(!files.is_empty());
    let mut failures = Vec::new();
    for p in &files {
        let text = std::fs::read_to_string(p).unwrap();
        if text.starts_with("//! mode: none") || text.contains("//~") {
            continue;
        }
        let parsed = onsa_syntax::parse(FileId(0), &text);
        let Some(out) = onsa_syntax::format(&parsed, &text) else {
            failures.push(format!("{}: refused (diagnostics)", p.display()));
            continue;
        };
        if out != text {
            let diff = first_diff(&text, &out);
            failures.push(format!("{}: changed\n{}", p.display(), diff));
            continue;
        }
        let again = onsa_syntax::parse(FileId(0), &out);
        let out2 = onsa_syntax::format(&again, &out).unwrap();
        if out2 != out {
            failures.push(format!("{}: not idempotent\n{}", p.display(), first_diff(&out, &out2)));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
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
