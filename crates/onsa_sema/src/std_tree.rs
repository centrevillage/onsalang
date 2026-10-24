//! The files of the std tree, read by the rule of spec §15.1. Shared by
//! `build.rs` (`#[path]`), which generates the std table from it, and by the
//! unit tests of this crate, which check it on scratch trees.

use std::path::{Path, PathBuf};

/// The `.onsa` files under `root`, as paths relative to it, sorted part by
/// part (the order of the driver's `read_sources`). As §15.1 collects a
/// package: names that start with `.` and the root's `tests/` and `target/`
/// are left out before their kind is looked at; a directory with an
/// `onsa.toml` is another package and is not opened; links are not followed;
/// files and links whose names do not end in `.onsa` are left out. An item
/// named `….onsa` that is neither a regular file nor a directory (a link, a
/// FIFO) is an error, and so is a directory that cannot be read.
pub fn onsa_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect(root, root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect(root: &Path, dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    for e in entries {
        let e = e.map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
        let path = e.path();
        let name = e.file_name();
        let name = name.to_str().ok_or_else(|| format!("{}: the name is not UTF-8", path.display()))?;
        if name.starts_with('.') || (dir == root && (name == "tests" || name == "target")) {
            continue;
        }
        let ty = e.file_type().map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        if ty.is_dir() {
            let manifest = path.join("onsa.toml");
            match manifest.symlink_metadata() {
                Ok(_) => {}
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => collect(root, &path, files)?,
                Err(e) => return Err(format!("cannot read {}: {e}", manifest.display())),
            }
        } else if name.ends_with(".onsa") {
            if !ty.is_file() {
                return Err(format!("{}: a `.onsa` item that is not a regular file or a directory", path.display()));
            }
            files.push(path.strip_prefix(root).expect("under the root").to_path_buf());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::onsa_files;
    use std::path::{Path, PathBuf};

    /// A scratch directory of its own, removed at the end.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(tag: &str) -> Scratch {
            let p = std::env::temp_dir().join(format!("onsa_std_tree_{}_{tag}", std::process::id()));
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
        assert!(onsa_files(Path::new("/nonexistent/onsa_std_tree")).is_err());
    }
}
