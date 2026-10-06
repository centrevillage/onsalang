//! Golden files (Q-04): change detectors, never the ground of a meaning. A
//! case declares which outputs it compares (`[test] golden`, `golden_graph`);
//! the file names follow from the case and the target (plan D-05):
//!
//! ```text
//! tests/golden/core/<case>.core              onsa dump --core
//! tests/golden/interface/<case>.txt          onsa interface
//! tests/golden/graph/<case>.<flow>.dot       onsa graph
//! tests/golden/c/<case>.<target>.c / .h      the C of a target (headers joined)
//! ```
//!
//! `UPDATE_GOLDEN=1` rewrites them; the parent approves the change.

use std::collections::BTreeSet;
use std::path::Path;

use crate::case::{Case, rel_path};
use crate::fragment::GoldenKind;

pub const DIR: &str = "tests/golden";

pub fn core_path(name: &str) -> String {
    format!("{DIR}/core/{name}.core")
}

pub fn interface_path(name: &str) -> String {
    format!("{DIR}/interface/{name}.txt")
}

pub fn graph_path(name: &str, flow: &str) -> String {
    format!("{DIR}/graph/{name}.{flow}.dot")
}

/// The `.c` and `.h` of a target.
pub fn c_paths(name: &str, target: &str) -> [String; 2] {
    [format!("{DIR}/c/{name}.{target}.c"), format!("{DIR}/c/{name}.{target}.h")]
}

/// Every golden file the case declares, whether or not it runs.
pub fn declared(case: &Case) -> Vec<String> {
    let Ok(setup) = &case.setup else { return Vec::new() };
    let mut out = Vec::new();
    for k in &setup.test.golden {
        match k {
            GoldenKind::Core => out.push(core_path(&case.name)),
            GoldenKind::Interface => out.push(interface_path(&case.name)),
            GoldenKind::C => {
                for t in setup.targets() {
                    out.extend(c_paths(&case.name, &t));
                }
            }
        }
    }
    for f in &setup.test.golden_graph {
        out.push(graph_path(&case.name, f));
    }
    out
}

/// Whether `UPDATE_GOLDEN` is set.
pub fn updating() -> bool {
    std::env::var_os("UPDATE_GOLDEN").is_some()
}

/// Compare `actual` with the golden file `rel`, or rewrite it when updating
/// and `write` (a pending case never rewrites). A problem message when it
/// differs or is missing.
pub fn compare(root: &Path, rel: &str, actual: &str, write: bool) -> Option<String> {
    let path = root.join(rel);
    if updating() && write {
        if let Some(dir) = path.parent() {
            let _ = std::fs::create_dir_all(dir);
        }
        return std::fs::write(&path, actual).err().map(|e| format!("cannot write {rel}: {e}"));
    }
    match std::fs::read_to_string(&path) {
        Ok(expected) if expected == actual => None,
        Ok(_) => Some(format!("{rel} differs (run with UPDATE_GOLDEN=1 to accept)")),
        Err(_) => Some(format!("{rel} is missing (run with UPDATE_GOLDEN=1 to create it)")),
    }
}

/// Golden files that no case declares (sources of cases, `.onsa`, are not golden files).
pub fn orphans(root: &Path, declared: &BTreeSet<String>) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![root.join(DIR)];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_none_or(|x| x != "onsa") && !e.file_name().to_string_lossy().starts_with('.') {
                let rel = rel_path(root, &p);
                if !declared.contains(&rel) {
                    out.push(rel);
                }
            }
        }
    }
    out.sort();
    out
}
