//! How `onsa fmt` writes a file (plan S-56; S-535, provisional: the reading (2), (2a), (2i) of the draft),
//! in temporary directories only: a temporary file in the directory of the file the path names, renamed
//! over it. A link is followed and stays a link, the mode bits stay, a read-only file and a directory where
//! no temporary file can be made are errors of input and output (exit code 2, the other files are still
//! processed, `docs/onsa-tools.md` §3.1), and no temporary file is left. The hard link is in
//! `fmt_rewrites.rs` (`fmt_writes_a_new_file_and_leaves_the_old_one_whole`).

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");
const ROUGH: &str = "fn f(a: I32) -> I32 {\n  let x = 0XaB + a\n  return x\n}\n";
const ROUGH_OUT: &str = "fn f(a: I32) -> I32 {\n  let x = 0xAB + a\n  x\n}\n";

/// A temporary directory of the test; its directories get their mode back before it is removed.
struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_write_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, mode: u32) -> PathBuf {
        let p = self.0.join(name);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&p, ROUGH).unwrap();
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(mode)).unwrap();
        p
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let sub = std::fs::read_dir(&self.0).into_iter().flatten().flatten().map(|e| e.path());
        for d in sub.filter(|p| p.is_dir()).chain([self.0.clone()]) {
            let _ = std::fs::set_permissions(&d, std::fs::Permissions::from_mode(0o755));
        }
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fmt(paths: &[&Path]) -> Output {
    Command::new(ONSA).arg("fmt").args(paths).output().expect("run onsa")
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn names(d: &Path) -> Vec<String> {
    let mut v: Vec<String> =
        std::fs::read_dir(d).unwrap().map(|e| e.unwrap().file_name().to_string_lossy().into_owned()).collect();
    v.sort();
    v
}

fn mode(p: &Path) -> u32 {
    std::fs::metadata(p).unwrap().permissions().mode() & 0o777
}

#[test]
fn fmt_keeps_the_mode_of_the_file_it_replaces() {
    let d = Dir::new("mode");
    for m in [0o600, 0o640, 0o755] {
        let p = d.file(&format!("m{m:o}.onsa"), m);
        let out = fmt(&[&p]);
        assert_eq!(code(&out), 0, "{out:?}");
        assert_eq!(std::fs::read_to_string(&p).unwrap(), ROUGH_OUT);
        assert_eq!(mode(&p), m, "the mode of the file stays");
    }
    assert_eq!(names(&d.0), ["m600.onsa", "m640.onsa", "m755.onsa"]);
}

#[test]
fn fmt_writes_the_file_a_link_names_and_keeps_the_link() {
    let d = Dir::new("link");
    let target = d.file("other/target.onsa", 0o644);
    let link = d.0.join("link.onsa");
    std::os::unix::fs::symlink("other/target.onsa", &link).unwrap();
    let out = fmt(&[&link]);
    assert_eq!(code(&out), 0, "{out:?}");
    assert!(std::fs::symlink_metadata(&link).unwrap().file_type().is_symlink(), "the link stays a link");
    assert_eq!(std::fs::read_to_string(&target).unwrap(), ROUGH_OUT);
    assert_eq!(names(&d.0), ["link.onsa", "other"]);
    assert_eq!(names(&d.0.join("other")), ["target.onsa"], "the temporary file was in the directory of the target");
}

#[test]
fn fmt_does_not_replace_a_read_only_file_and_writes_the_others() {
    let d = Dir::new("read_only");
    let (a, ro, b) = (d.file("a.onsa", 0o644), d.file("ro.onsa", 0o444), d.file("b.onsa", 0o644));
    let out = fmt(&[&a, &ro, &b]);
    assert_eq!(code(&out), 2, "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("cannot write") && err.contains("ro.onsa"), "{err}");
    assert_eq!(std::fs::read_to_string(&ro).unwrap(), ROUGH, "the read-only file is not replaced");
    assert_eq!(mode(&ro), 0o444);
    assert_eq!(std::fs::read_to_string(&a).unwrap(), ROUGH_OUT);
    assert_eq!(std::fs::read_to_string(&b).unwrap(), ROUGH_OUT);
    assert_eq!(names(&d.0), ["a.onsa", "b.onsa", "ro.onsa"]);
}

#[test]
fn fmt_cannot_write_a_file_in_a_directory_where_no_temporary_file_can_be_made() {
    let d = Dir::new("closed_dir");
    let p = d.file("closed/x.onsa", 0o644);
    let closed = d.0.join("closed");
    std::fs::set_permissions(&closed, std::fs::Permissions::from_mode(0o555)).unwrap();
    let out = fmt(&[&p]);
    let (text, entries) = (std::fs::read_to_string(&p).unwrap(), names(&closed));
    std::fs::set_permissions(&closed, std::fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(code(&out), 2, "{out:?}");
    assert!(String::from_utf8_lossy(&out.stderr).contains("cannot write"), "{out:?}");
    assert_eq!(text, ROUGH, "the file is not written in place");
    assert_eq!(entries, ["x.onsa"]);
}

/// W3-12/b 7: a file whose name is near the 255 bytes of `NAME_MAX` (one of ASCII letters, one of
/// letters of three bytes) is written: the name of the temporary file keeps the first bytes of the name
/// only. No temporary file is left, and the mode stays.
#[test]
fn fmt_writes_a_file_whose_name_is_long() {
    let d = Dir::new("long_name");
    let ascii = format!("{}.onsa", "a".repeat(245));
    let wide = format!("{}.onsa", "\u{3042}".repeat(83));
    assert_eq!((ascii.len(), wide.len()), (250, 254));
    let paths = [d.file(&ascii, 0o644), d.file(&wide, 0o600)];
    let out = fmt(&[&paths[0], &paths[1]]);
    assert_eq!(code(&out), 0, "{out:?}");
    for p in &paths {
        assert_eq!(std::fs::read_to_string(p).unwrap(), ROUGH_OUT);
    }
    assert_eq!((mode(&paths[0]), mode(&paths[1])), (0o644, 0o600));
    let mut want = vec![ascii, wide];
    want.sort();
    assert_eq!(names(&d.0), want);
}
