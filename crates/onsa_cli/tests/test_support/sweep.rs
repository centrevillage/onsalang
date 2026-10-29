//! Shared by the sweeps of the `use` lines (`use_model.rs`, `use_repair_loop.rs`, `use_shapes.rs`; W4-03
//! U3a2/t2): a fixed-seed generator, packages kept as texts in memory, one run of `onsa check --json .`
//! with its diagnostics read, and the application of one candidate (a `fixes` entry of a diagnostic).
//!
//! A sweep writes a package from its texts, runs the command, and compares the diagnostics with what the
//! spec fixes. A candidate is applied to the texts and the files it changed are written again, so every
//! trial is a fresh run of the command on a scratch directory (`Dir`, removed on drop).

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::Path;

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

/// A scratch package named `name` with the files of `texts`.
pub fn package(tag: &str, name: &str, texts: &Texts) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", &format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n"));
    write_texts(&d, texts);
    d
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
    let doc = doc_of(&out);
    let diags = doc["diagnostics"].as_array().expect("diagnostics").iter().map(Diag::from).collect();
    Checked { code: out.code, stderr: out.stderr, diags }
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
