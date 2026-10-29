//! Shared by the sweeps of the `use` lines (`use_model.rs`, `use_repair_loop.rs`, `use_shapes.rs`; W4-03
//! U3a2/t2): a fixed-seed generator, packages kept as texts in memory, one run of `onsa check --json .`
//! with its diagnostics read, and the application of one candidate (a `fixes` entry of a diagnostic).
//!
//! A sweep writes a package from its texts, runs the command, and compares the diagnostics with what the
//! spec fixes. A candidate is applied to the texts and the files it changed are written again, so every
//! trial is a fresh run of the command on a scratch directory (`Dir`, removed on drop). Or the sweep
//! checks the texts in this process as the command does (`check_input`), with no file written (X-16).

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::Path;

use onsa_driver::{ManifestSource, PackageInput, SourceFile};
use serde_json::Value;

use super::{Dir, doc_of, run};

/// A small generator with a fixed seed (splitmix64), so that a failing package can be written again
/// from its seed alone.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x2545_F491_4F6C_DD1D).wrapping_add(0x9E37_79B9_7F4A_7C15))
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A number in `0..n` (`n` > 0).
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }

    /// A number in `lo..=hi`.
    pub fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }

    /// True in `percent` of 100.
    pub fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            let j = self.below(i + 1);
            xs.swap(i, j);
        }
    }
}

/// The files of a package: the path under the root (`a/b.onsa`) to the text.
pub type Texts = BTreeMap<String, String>;

/// The manifest of a scratch package named `name`.
fn manifest(name: &str) -> String {
    format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n")
}

/// A scratch package named `name` with the files of `texts`.
pub fn package(tag: &str, name: &str, texts: &Texts) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", &manifest(name));
    write_texts(&d, texts);
    d
}

/// The input of a package named `name` with the files of `texts`, all of them modules, sorted part by part
/// as the files of a package root are read (`a/b.onsa` before `a.onsa`), so that they are numbered as
/// they are from the disk.
pub fn input_of(name: &str, texts: &Texts) -> PackageInput {
    let mut files: Vec<SourceFile> =
        texts.iter().map(|(path, text)| SourceFile { path: path.clone(), text: text.clone() }).collect();
    files.sort_by(|a, b| a.path.split('/').cmp(b.path.split('/')));
    PackageInput {
        manifest: Some(ManifestSource { path: "onsa.toml".into(), text: manifest(name) }),
        files,
        ..PackageInput::default()
    }
}

/// `input` with the texts of `texts` for its files of the same paths (the manifest, the modules and the
/// root's `tests/`); a file `texts` does not name keeps its text.
pub fn with_texts(input: &PackageInput, texts: &Texts) -> PackageInput {
    let mut out = input.clone();
    for f in out.files.iter_mut().chain(out.root_tests.iter_mut()) {
        if let Some(text) = texts.get(&f.path) {
            f.text = text.clone();
        }
    }
    if let Some(m) = out.manifest.as_mut() {
        if let Some(text) = texts.get(&m.path) {
            m.text = text.clone();
        }
    }
    out
}

/// Write the files of `texts` (the manifest stays, and so does a file that `texts` does not name). A file
/// whose text on the disk is already the same is not written again: a trial changes one file or two, and
/// each file written costs the disk a block whatever its size (X-16).
pub fn write_texts(d: &Dir, texts: &Texts) {
    for (f, t) in texts {
        if std::fs::read(d.root().join(f)).is_ok_and(|old| old == t.as_bytes()) {
            continue;
        }
        d.write(f, t);
    }
}

/// One diagnostic of `check --json`, with the fields the sweeps read.
#[derive(Clone, Debug)]
pub struct Diag {
    pub code: String,
    pub file: String,
    pub line: u64,
    pub col: u64,
    pub message: String,
    pub fixes: Vec<Value>,
    pub notes: usize,
    /// The notes that point at a place (`span`).
    pub spanned_notes: usize,
}

impl Diag {
    fn from(v: &Value) -> Diag {
        let span = &v["span"];
        Diag {
            code: v["code"].as_str().expect("a code").to_string(),
            file: span["file"].as_str().expect("a file").to_string(),
            line: span["line"].as_u64().expect("a line"),
            col: span["col"].as_u64().expect("a column"),
            message: v["message"].as_str().expect("a message").to_string(),
            fixes: v["fixes"].as_array().cloned().unwrap_or_default(),
            notes: v["notes"].as_array().map(|n| n.len()).unwrap_or(0),
            spanned_notes: v["notes"]
                .as_array()
                .map(|n| n.iter().filter(|x| x.get("span").is_some()).count())
                .unwrap_or(0),
        }
    }
}

/// The result of one `onsa check --json .` in a package.
pub struct Checked {
    pub code: i32,
    pub stderr: String,
    pub diags: Vec<Diag>,
}

impl Checked {
    pub fn of_code(&self, code: &str) -> Vec<&Diag> {
        self.diags.iter().filter(|d| d.code == code).collect()
    }
}

/// `onsa check --json .` in `root`. An exit by a signal fails the test (`run`); the document is read as
/// a whole, so a command that ended with something other than a document fails here with its text.
pub fn check_package(root: &Path) -> Checked {
    let out = run(root, &["check", "--json", "."]);
    if out.code != 0 && out.code != 1 || out.stderr.contains("internal error") {
        return Checked { code: out.code, stderr: out.stderr, diags: Vec::new() };
    }
    let diags = diags_of(&doc_of(&out));
    Checked { code: out.code, stderr: out.stderr, diags }
}

fn diags_of(doc: &Value) -> Vec<Diag> {
    doc["diagnostics"].as_array().expect("diagnostics").iter().map(Diag::from).collect()
}

/// `onsa check --json .` on the package of `input`, run in this process as the command runs it (on a
/// thread of the command's stack, under its guard) and read from the document it prints, with no file
/// written or read (X-16). The reading of a package from its directory, the exit code and the printing
/// are the business of the tests that run the command. The exit code is the command's: 2 for an input
/// that does not load, 101 with `internal error` for an internal error, else 1 with diagnostics and 0.
pub fn check_input(input: &PackageInput) -> Checked {
    let input = input.clone();
    let ran = onsa_diag::stack::spawn("check", move || {
        onsa_driver::guard(|| -> Result<String, (i32, String)> {
            let mut loaded = onsa_driver::Loaded::from_input(input).map_err(|e| (2, e))?;
            let result = onsa_driver::check_loaded(&mut loaded).map_err(|e| (101, format!("internal error: {e:?}")))?;
            Ok(onsa_diag::to_json(&loaded.sources, &result.diagnostics))
        })
    })
    .expect("spawn the thread of the check")
    .join()
    .unwrap_or_else(|_| panic!("the check panicked outside its guard"));
    match ran {
        Ok(Ok(json)) => {
            let doc: Value = serde_json::from_str(&json).expect("the document is one JSON value");
            let diags = diags_of(&doc);
            Checked { code: if diags.is_empty() { 0 } else { 1 }, stderr: String::new(), diags }
        }
        Ok(Err((code, stderr))) => Checked { code, stderr, diags: Vec::new() },
        Err(e) => Checked { code: 101, stderr: format!("internal error: {e:?}"), diags: Vec::new() },
    }
}

/// True when the command ended as a check does: exit code 0 or 1 and no internal error.
pub fn ended_well(c: &Checked) -> bool {
    (c.code == 0 || c.code == 1) && !c.stderr.contains("internal error")
}

/// The byte offset of a line and column (from 1, in characters) in `text`.
pub fn offset(text: &str, line: u64, col: u64) -> usize {
    let mut start = 0;
    for (i, l) in text.split_inclusive('\n').enumerate() {
        if i as u64 + 1 == line {
            let in_line = l.char_indices().nth(col as usize - 1).map(|(b, _)| b).unwrap_or(l.len());
            return start + in_line;
        }
        start += l.len();
    }
    text.len()
}

/// Apply every edit of one candidate (a `fixes` entry) to the texts, from the end of each file.
pub fn apply_fix_texts(texts: &mut Texts, fix: &Value) {
    let mut by_file: BTreeMap<String, Vec<(usize, usize, String)>> = BTreeMap::new();
    for e in fix["edits"].as_array().expect("edits") {
        let sp = &e["span"];
        let file = sp["file"].as_str().expect("file").to_string();
        let text = texts.get(&file).unwrap_or_else(|| panic!("an edit of {file}, which is not in the package"));
        let a = offset(text, sp["line"].as_u64().unwrap(), sp["col"].as_u64().unwrap());
        let b = offset(text, sp["end_line"].as_u64().unwrap(), sp["end_col"].as_u64().unwrap());
        by_file.entry(file).or_default().push((a, b, e["replace"].as_str().expect("replace").to_string()));
    }
    for (file, mut edits) in by_file {
        edits.sort_by(|x, y| y.0.cmp(&x.0));
        let text = texts.get_mut(&file).unwrap();
        for (a, b, rep) in edits {
            text.replace_range(a..b, &rep);
        }
    }
}

/// The names in backticks of a message (`the modules `a`, `b.c` import each other`), as written.
pub fn quoted(message: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = message;
    while let Some(a) = rest.find('`') {
        let after = &rest[a + 1..];
        match after.find('`') {
            Some(b) => {
                out.push(after[..b].to_string());
                rest = &after[b + 1..];
            }
            None => break,
        }
    }
    out
}

/// Read every file of the `.onsa` tree under `root` into texts, leaving out `target` and the names that
/// start with a dot (the directories a command makes).
pub fn read_tree(root: &Path) -> Texts {
    fn go(base: &Path, dir: &Path, out: &mut Texts) {
        let mut entries: Vec<_> = std::fs::read_dir(dir).expect("read a directory").map(|e| e.unwrap()).collect();
        entries.sort_by_key(|e| e.file_name());
        for e in entries {
            let name = e.file_name().to_string_lossy().into_owned();
            if name.starts_with('.') || (dir == base && name == "target") {
                continue;
            }
            let p = e.path();
            if p.is_dir() {
                go(base, &p, out);
            } else if let Ok(text) = std::fs::read_to_string(&p) {
                let rel = p.strip_prefix(base).unwrap().to_string_lossy().replace('\\', "/");
                out.insert(rel, text);
            }
        }
    }
    let mut out = Texts::new();
    go(root, root, &mut out);
    out
}
