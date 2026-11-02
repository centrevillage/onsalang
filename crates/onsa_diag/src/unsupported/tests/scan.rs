//! The scan of the Rust source of the crates: the code without the tests, and
//! where the test modules are. The tests of `unsupported` read it, and
//! `onsa_cases --test-items` (which includes this file) gives where the test
//! modules are to the gate item cross-check, which matches them with the
//! tools' reading (`tools/repo.py`: `test_lines` and the test files of
//! `NOT_CODE`; RF-21).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// The `.rs` files under `dir`, recursively.
fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            rust_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

/// The text without comments (each comment a space, and the line breaks
/// of a block comment), and for each character whether it is inside a
/// string or character literal.
fn lex(text: &str) -> (Vec<char>, Vec<bool>) {
    let c: Vec<char> = text.chars().collect();
    let (mut out, mut lit) = (Vec::new(), Vec::new());
    let at = |i: usize| c.get(i).copied();
    let mut i = 0;
    while i < c.len() {
        let ch = c[i];
        if ch == '/' && at(i + 1) == Some('/') {
            while i < c.len() && c[i] != '\n' {
                i += 1;
            }
            out.push(' ');
            lit.push(false);
            continue;
        }
        if ch == '/' && at(i + 1) == Some('*') {
            let (from, mut depth) = (i, 0);
            while i < c.len() {
                if c[i] == '/' && at(i + 1) == Some('*') {
                    depth += 1;
                    i += 2;
                } else if c[i] == '*' && at(i + 1) == Some('/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            let breaks = c[from..i.min(c.len())].iter().filter(|&&x| x == '\n').count();
            out.extend(std::iter::once(' ').chain(std::iter::repeat_n('\n', breaks)));
            lit.extend(std::iter::repeat_n(false, 1 + breaks));
            continue;
        }
        let ident_before = i > 0 && (c[i - 1].is_alphanumeric() || c[i - 1] == '_');
        // A literal from `i` to `end` (exclusive).
        let mut end = None;
        if !ident_before && (ch == 'r' || (ch == 'b' && at(i + 1) == Some('r'))) {
            let mut j = i + if ch == 'b' { 2 } else { 1 };
            let mut hashes = 0;
            while at(j) == Some('#') {
                hashes += 1;
                j += 1;
            }
            if at(j) == Some('"') {
                j += 1;
                while j < c.len() && !(c[j] == '"' && (1..=hashes).all(|k| at(j + k) == Some('#'))) {
                    j += 1;
                }
                end = Some(j + 1 + hashes);
            }
        }
        if end.is_none() && ch == '"' {
            let mut j = i + 1;
            while j < c.len() && c[j] != '"' {
                j += if c[j] == '\\' { 2 } else { 1 };
            }
            end = Some(j + 1);
        }
        if end.is_none() && ch == '\'' {
            if at(i + 1) == Some('\\') {
                let mut j = i + 2;
                while j < c.len() && c[j] != '\'' {
                    j += 1;
                }
                end = Some(j + 1);
            } else if at(i + 2) == Some('\'') {
                end = Some(i + 3);
            }
        }
        match end {
            Some(e) => {
                let e = e.min(c.len());
                out.extend_from_slice(&c[i..e]);
                lit.extend(std::iter::repeat_n(true, e - i));
                i = e;
            }
            None => {
                out.push(ch);
                lit.push(false);
                i += 1;
            }
        }
    }
    (out, lit)
}

/// The end of the item that starts at `i` (after its attributes): its
/// `;`, or the `}` that closes its first `{`, outside literals and
/// outside `(...)` / `[...]`.
fn item_end(c: &[char], lit: &[bool], mut i: usize) -> usize {
    let mut depth = 0i32;
    while i < c.len() {
        if !lit[i] {
            match c[i] {
                '(' | '[' => depth += 1,
                ')' | ']' => depth -= 1,
                ';' if depth == 0 => return i + 1,
                '{' if depth == 0 => {
                    let mut braces = 0;
                    while i < c.len() {
                        if !lit[i] {
                            if c[i] == '{' {
                                braces += 1;
                            } else if c[i] == '}' {
                                braces -= 1;
                                if braces == 0 {
                                    return i + 1;
                                }
                            }
                        }
                        i += 1;
                    }
                    return i;
                }
                _ => {}
            }
        }
        i += 1;
    }
    i
}

/// The items marked `#[cfg(test)]` (a `mod x;` to its `;`, an item with a
/// body to its closing brace) of a lexed text ([`lex`]): from the
/// attribute, from the item after its attributes, and the item's end.
fn test_items(c: &[char], lit: &[bool]) -> Vec<(usize, usize, usize)> {
    let attr: Vec<char> = "#[cfg(test)]".chars().collect();
    let mut items = Vec::new();
    let mut i = 0;
    while i + attr.len() <= c.len() {
        if lit[i] || c[i..i + attr.len()] != attr[..] {
            i += 1;
            continue;
        }
        let mut j = i + attr.len();
        // further attributes of the same item
        loop {
            while j < c.len() && c[j].is_whitespace() {
                j += 1;
            }
            if c.get(j) == Some(&'#') && c.get(j + 1) == Some(&'[') {
                // to the `]` that closes the attribute
                let mut depth = 0;
                j += 1;
                while j < c.len() {
                    if !lit[j] {
                        match c[j] {
                            '[' => depth += 1,
                            ']' => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                    j += 1;
                }
                j += 1;
            } else {
                break;
            }
        }
        let end = item_end(c, lit, j);
        items.push((i, j, end));
        i = end;
    }
    items
}

/// The code of a source file without comments and without the items
/// marked `#[cfg(test)]`, and the names of the `#[cfg(test)] mod x;` files.
pub fn non_test_code(text: &str) -> (String, Vec<String>) {
    let (c, lit) = lex(text);
    let mut keep = vec![true; c.len()];
    let mut test_mods = Vec::new();
    for (i, j, end) in test_items(&c, &lit) {
        let item: String = c[j..end].iter().collect();
        let words: Vec<&str> =
            item.split(|x: char| !(x.is_alphanumeric() || x == '_')).filter(|w| !w.is_empty()).collect();
        if item.trim_end().ends_with(';')
            && let Some(k) = words.iter().position(|w| *w == "mod")
            && let Some(name) = words.get(k + 1)
        {
            test_mods.push(name.to_string());
        }
        for k in keep.iter_mut().take(end).skip(i) {
            *k = false;
        }
    }
    (c.iter().zip(&keep).filter(|(_, k)| **k).map(|(x, _)| *x).collect(), test_mods)
}

/// The files of the modules `test_mods` declared in `file`.
fn module_paths(file: &Path, test_mods: &[String]) -> Vec<PathBuf> {
    let stem = file.file_stem().unwrap().to_string_lossy();
    let dir = if ["lib", "main", "mod"].contains(&stem.as_ref()) {
        file.parent().unwrap().to_path_buf()
    } else {
        file.with_extension("")
    };
    test_mods.iter().flat_map(|m| [dir.join(format!("{m}.rs")), dir.join(m)]).collect()
}

/// Every `.rs` file of the `src/` of the crates in `crates` with its text, its
/// code without the tests ([`non_test_code`]), and whether it is the file of a test module.
pub fn crate_sources(crates: &Path) -> Vec<(PathBuf, String, String, bool)> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(crates).unwrap() {
        let src = entry.unwrap().path().join("src");
        if src.is_dir() {
            rust_files(&src, &mut files);
        }
    }
    let mut code_of = Vec::new();
    let mut test_files = Vec::new();
    for f in files {
        let text = std::fs::read_to_string(&f).unwrap_or_else(|e| panic!("{}: {e}", f.display()));
        let (code, test_mods) = non_test_code(&text);
        test_files.extend(module_paths(&f, &test_mods));
        code_of.push((f, text, code));
    }
    let test = |f: &Path| test_files.iter().any(|t| f.starts_with(t));
    // Every file is read before: a test module's file may come before the file that declares it.
    code_of
        .into_iter()
        .map(|(f, text, code)| {
            let t = test(&f);
            (f, text, code, t)
        })
        .collect()
}

/// The lines (from 1) of the `#[cfg(test)] mod x { … }` of a source file,
/// as the scan reads them: from the attribute to the closing brace.
fn test_module_lines(text: &str) -> BTreeSet<usize> {
    let (c, lit) = lex(text);
    let line = |k: usize| 1 + c[..k].iter().filter(|&&x| x == '\n').count();
    let mut lines = BTreeSet::new();
    for (i, j, end) in test_items(&c, &lit) {
        let head: String = c[j..end].iter().take_while(|&&x| x != '{' && x != ';').collect();
        if c[end - 1] == '}' && head.split_whitespace().rev().nth(1) == Some("mod") {
            lines.extend(line(i)..=line(end - 1));
        }
    }
    lines
}

/// Where the test modules of `sources` are, a line per file, its path from
/// `root` first: `<path> *` for the file of a test module, else `<path>` and
/// the lines of its test modules ([`test_module_lines`]); no line for a file
/// with neither (RF-21: the form of the gate item cross-check).
pub fn test_module_answers(root: &Path, sources: &[(PathBuf, String, String, bool)]) -> Vec<String> {
    let mut out = Vec::new();
    for (f, text, _, test) in sources {
        let rel = f.strip_prefix(root).unwrap_or(f).to_string_lossy();
        let lines: Vec<String> = test_module_lines(text).iter().map(usize::to_string).collect();
        if *test {
            out.push(format!("{rel} *"));
        } else if !lines.is_empty() {
            out.push(format!("{rel} {}", lines.join(" ")));
        }
    }
    out
}
