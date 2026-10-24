//! Generates the table of the embedded std from the files under `std/`
//! (R-80 (4)): a file added to `std/` is a module with no other registration.
//!
//! The files are collected by the rule of spec §15.1 (`src/std_tree.rs`,
//! unit-tested on scratch trees); the module path is the file's path under
//! `std/` without `.onsa`, `.` between its parts. An item that §15.1 makes an
//! error (a `.onsa` link, an unreadable directory) stops the build. The
//! driver's tests check the table against the driver's own reading of the
//! directory (`read_sources`).

#[path = "src/std_tree.rs"]
mod std_tree;

use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let root = manifest_dir.join("../../std");
    println!("cargo:rerun-if-changed=../../std");
    let files = std_tree::onsa_files(&root).unwrap_or_else(|e| panic!("the std tree: {e}"));
    let mut out = String::from("&[\n");
    for rel in &files {
        let parts: Vec<&str> = rel.components().map(|c| c.as_os_str().to_str().expect("UTF-8 name")).collect();
        let file = parts.join("/");
        let module = file.strip_suffix(".onsa").expect(".onsa").replace('/', ".");
        let abs = root.join(rel);
        let abs = abs.to_str().expect("UTF-8 path");
        out.push_str(&format!("    StdModule {{ path: {module:?}, file: {file:?}, text: include_str!({abs:?}) }},\n"));
    }
    out.push_str("]\n");
    let dest = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR")).join("std_modules.rs");
    std::fs::write(&dest, out).expect("write the std table");
}
