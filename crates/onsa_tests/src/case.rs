//! Finding the cases: every `.onsa` file and every package directory (with
//! `onsa.toml`) under `tests/`, except [`EXCLUDED`] (plan D-05, R-80 (5)).

use std::path::{Path, PathBuf};

use onsa_driver::{PackageInput, SourceFile};

use crate::fragment::{self, TestSettings};

/// The directory scanned, relative to the repository root.
pub const TESTS: &str = "tests";

/// Directories under `tests/` that hold no cases, with the reason. Every other
/// directory is scanned, so a new one is never skipped silently.
pub const EXCLUDED: &[(&str, &str)] = &[
    (
        "tests/review-phase1",
        "reproduction inputs of the phase-1 review, with the expected and current output in comments; \
         a work that fixes one moves it into a case (plan §8.3 10)",
    ),
    (
        "tests/fuzz",
        "inputs the fuzzing of `check` and `fmt` saved (Q-06, W1-04): mutated sources that crashed the compiler, \
         replayed by `tools/fuzz.py` (the gate item `fuzz`), not cases",
    ),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum CaseKind {
    File,
    Package,
}

/// A case, read and with its fragment parsed.
#[derive(Debug, Clone)]
pub struct Case {
    /// From the repository root, `/`-separated (the form of `tests/pending.toml`).
    pub path: String,
    pub kind: CaseKind,
    /// The name of its golden files: the file stem or the directory name.
    pub name: String,
    /// The input and the settings, or why the case cannot be read.
    pub setup: Result<Setup, String>,
}

#[derive(Debug, Clone)]
pub struct Setup {
    pub input: PackageInput,
    pub test: TestSettings,
}

impl Setup {
    /// Target names of the manifest, sorted.
    pub fn targets(&self) -> Vec<String> {
        let mut t: Vec<String> =
            self.input.manifest.as_ref().map(|m| m.targets.keys().cloned().collect()).unwrap_or_default();
        t.sort();
        t
    }
}

/// Every case under `root/tests`, sorted by path, and the directories that
/// cannot be read. `tests/` itself is never a package, even with an `onsa.toml`.
pub fn collect(root: &Path) -> (Vec<Case>, Vec<String>) {
    let mut out = Vec::new();
    let mut errors = Vec::new();
    let top = root.join(TESTS);
    let mut stack = vec![top.clone()];
    while let Some(d) = stack.pop() {
        let rel = rel_path(root, &d);
        if EXCLUDED.iter().any(|(x, _)| *x == rel) {
            continue;
        }
        if d != top && d.join("onsa.toml").exists() {
            out.push(read_package(root, &d));
            continue;
        }
        let entries = match std::fs::read_dir(&d) {
            Ok(e) => e,
            Err(e) => {
                errors.push(format!("{rel}: cannot read the directory: {e}"));
                continue;
            }
        };
        for e in entries {
            let p = match e {
                Ok(e) => e.path(),
                Err(e) => {
                    errors.push(format!("{rel}: cannot read an entry: {e}"));
                    continue;
                }
            };
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                out.push(read_file(root, &p));
            }
        }
    }
    if top.join("onsa.toml").exists() {
        errors
            .push(format!("{TESTS}/onsa.toml: the root of the cases is not a package; move it into a case directory"));
    }
    out.sort_by(|a, b| a.path.cmp(&b.path));
    (out, errors)
}

/// `p` relative to `root`, `/`-separated.
pub fn rel_path(root: &Path, p: &Path) -> String {
    let rel = p.strip_prefix(root).unwrap_or(p);
    rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join("/")
}

fn read_file(root: &Path, p: &Path) -> Case {
    let path = rel_path(root, p);
    let name = p.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
    let setup = (|| {
        let text = std::fs::read_to_string(p).map_err(|e| format!("cannot read: {e}"))?;
        let frag = fragment::parse(&text)?.unwrap_or_default();
        // With a manifest the file is the one module of a package (its path
        // is relative to that package root); without, it is shown by its path.
        let file_path = if frag.manifest.is_some() {
            p.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
        } else {
            path.clone()
        };
        let input =
            PackageInput { manifest: frag.manifest, files: vec![SourceFile { path: file_path, text }], root: None };
        Ok(Setup { input, test: frag.test })
    })();
    Case { path, kind: CaseKind::File, name, setup }
}

fn read_package(root: &Path, dir: &Path) -> Case {
    let path = rel_path(root, dir);
    let name = dir.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
    let setup = (|| {
        let input = onsa_driver::read_input(&[dir.to_path_buf()])?;
        let mut test = None;
        for f in &input.files {
            let Some(frag) = fragment::parse(&f.text).map_err(|e| format!("{}: {e}", f.path))? else { continue };
            if frag.manifest.is_some() {
                return Err(format!(
                    "{}: the fragment of a package holds only `[test]` (the manifest is its onsa.toml)",
                    f.path
                ));
            }
            if test.is_some() {
                return Err(format!("{}: a second fragment; a package has at most one", f.path));
            }
            test = Some(frag.test);
        }
        Ok(Setup { input, test: test.unwrap_or_default() })
    })();
    Case { path, kind: CaseKind::Package, name, setup }
}

/// The repository root, from this crate.
pub fn repo_root() -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    p.canonicalize().unwrap_or(p)
}
