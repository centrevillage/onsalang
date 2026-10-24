//! The files of a package tree, read by the rule of spec §15.1: the one place
//! of that rule (D-15). The driver reads the user's packages with it,
//! `build.rs` includes this file (`#[path]`) to generate the std table, and
//! the unit tests check it on scratch trees.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// The manifest of a package; the directory that holds it is a package root.
pub const MANIFEST: &str = "onsa.toml";
/// The root's directory whose role is left to the second phase (§15.1, §19.1).
pub const TESTS_DIR: &str = "tests";
/// The root's directory of the build outputs (§15.1, §18.2).
pub const BUILD_DIR: &str = "target";
/// The suffix of the name of a module file.
pub const SUFFIX: &str = ".onsa";

/// Whether `dir` has an `onsa.toml`: an item of any kind by that name, a link
/// too. It is opened only where it is read as the manifest.
// SPEC-GAP(S-634): an `onsa.toml` that is a broken link, a directory or a
// FIFO is there: a child directory with one is a nested package and is not
// opened; found above a passed file, it is read as the manifest and fails
// (exit 2).
pub fn has_manifest(dir: &Path) -> Result<bool, String> {
    let manifest = dir.join(MANIFEST);
    match manifest.symlink_metadata() {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(format!("cannot read {}: {e}", manifest.display())),
    }
}

/// The `.onsa` files under `root`, as paths relative to it, sorted part by
/// part. As §15.1 collects a package: names that start with `.` and the
/// root's `tests/` and `target/` are left out before their kind is looked
/// at; a directory with an `onsa.toml` is another package and is not opened;
/// links are not followed; files and links whose names do not end in `.onsa`
/// are left out. An item named `….onsa` that is neither a regular file nor a
/// directory (a link, a FIFO) is an error, and so is a directory or an entry
/// that cannot be read. The kind is that of the directory entry, so no file
/// is opened here (a FIFO does not block).
///
/// A work list, not a recursion: no link is followed, so every directory is
/// opened once, and the stack does not grow with the depth of the tree.
pub fn onsa_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    let mut dirs = vec![root.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        let entries = std::fs::read_dir(&dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
        for e in entries {
            let e = e.map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
            let path = e.path();
            let name = e.file_name();
            if name.as_encoded_bytes().starts_with(b".")
                || (dir == root && (name == OsStr::new(TESTS_DIR) || name == OsStr::new(BUILD_DIR)))
            {
                continue;
            }
            let ty = e.file_type().map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            if !ty.is_dir() && !name.as_encoded_bytes().ends_with(SUFFIX.as_bytes()) {
                continue;
            }
            // SPEC-GAP(S-633): a name that is not UTF-8 is left out like the
            // other items when it is not a directory and does not end in
            // `.onsa`; otherwise it would be part of a module path: exit 2.
            if name.to_str().is_none() {
                return Err(format!("{}: the name is not UTF-8", path.display()));
            }
            if ty.is_dir() {
                if !has_manifest(&path)? {
                    dirs.push(path);
                }
            } else if ty.is_file() {
                files.push(path.strip_prefix(root).expect("under the root").to_path_buf());
            } else {
                return Err(format!("{}: a `.onsa` item that is not a regular file or a directory", path.display()));
            }
        }
    }
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::onsa_files;
    use std::path::{Path, PathBuf};

    /// A scratch directory of its own, removed at the end.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(tag: &str) -> Scratch {
            let p = std::env::temp_dir().join(format!("onsa_package_tree_{}_{tag}", std::process::id()));
            let _ = std::fs::remove_dir_all(&p);
            std::fs::create_dir_all(&p).unwrap();
            Scratch(p)
        }

        fn file(&self, rel: &str) {
            let p = self.0.join(rel);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, "").unwrap();
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn rel(files: Vec<PathBuf>) -> Vec<String> {
        files
            .iter()
            .map(|p| p.components().map(|c| c.as_os_str().to_str().unwrap()).collect::<Vec<_>>().join("/"))
            .collect()
    }

    #[test]
    fn the_onsa_files_are_collected_sorted_part_by_part() {
        let s = Scratch::new("sorted");
        for f in ["math.onsa", "dsp.onsa", "dsp/test.onsa", "test/gen.onsa", "test.onsa", "a/b/c.onsa"] {
            s.file(f);
        }
        let got = rel(onsa_files(&s.0).unwrap());
        assert_eq!(got, ["a/b/c.onsa", "dsp/test.onsa", "dsp.onsa", "math.onsa", "test/gen.onsa", "test.onsa"]);
    }

    #[test]
    fn names_with_a_dot_the_roots_tests_and_target_and_other_files_are_left_out() {
        let s = Scratch::new("left_out");
        for f in [
            "m.onsa",
            ".hid.onsa",
            ".cache/c.onsa",
            ".DS_Store",
            "tests/t.onsa",
            "target/u.onsa",
            "README.md",
            "math.onsa.orig",
            "math.onsa.rej",
            "deep/tests/k.onsa",
            "deep/target/k.onsa",
            "nested/onsa.toml",
            "nested/n.onsa",
        ] {
            s.file(f);
        }
        let got = rel(onsa_files(&s.0).unwrap());
        assert_eq!(got, ["deep/target/k.onsa", "deep/tests/k.onsa", "m.onsa"]);
    }

    #[cfg(unix)]
    #[test]
    fn links_are_not_followed_and_a_link_named_onsa_is_an_error() {
        use std::os::unix::fs::symlink;
        let s = Scratch::new("links");
        s.file("m.onsa");
        s.file("sub/x.onsa");
        // Not ending in `.onsa`: left out, not followed.
        symlink(s.0.join("sub"), s.0.join("linked_dir")).unwrap();
        symlink(s.0.join("m.onsa"), s.0.join("m_link")).unwrap();
        symlink(s.0.join("missing"), s.0.join("broken")).unwrap();
        assert_eq!(rel(onsa_files(&s.0).unwrap()), ["m.onsa", "sub/x.onsa"]);
        for (tag, target) in [("to_file", "m.onsa"), ("to_dir", "sub"), ("broken", "missing")] {
            let s2 = Scratch::new(&format!("link_{tag}"));
            s2.file("m.onsa");
            std::fs::create_dir_all(s2.0.join("sub")).unwrap();
            symlink(s2.0.join(target), s2.0.join("l.onsa")).unwrap();
            let e = onsa_files(&s2.0).unwrap_err();
            assert!(e.contains("l.onsa"), "{tag}: {e}");
        }
    }

    #[test]
    fn a_directory_that_cannot_be_read_is_an_error() {
        assert!(onsa_files(Path::new("/nonexistent/onsa_package_tree")).is_err());
    }
}
