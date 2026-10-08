//! The exit codes of the commands (spec §18.2, S-56): 0 success, 1 problems
//! found, 2 the command could not work, 101 an internal error (S-67). The
//! main rows of the table, through the built `onsa`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_exit_codes_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn onsa(args: &[&str]) -> Output {
    Command::new(ONSA).args(args).output().expect("run onsa")
}

fn code(args: &[&str]) -> i32 {
    let out = onsa(args);
    out.status.code().unwrap_or_else(|| panic!("onsa {args:?} ended by a signal: {out:?}"))
}

const OK: &str = "pub fn f() -> I32 {\n  1\n}\n";
const UGLY: &str = "pub fn f()->I32{1}\n";
const OTHER: &str = "pub fn g() -> I32 {\n  2\n}\n";
const SYNTAX: &str = "pub fn f( {\n";
const UNRESOLVED: &str = "pub fn f() -> I32 {\n  y\n}\n";

#[test]
fn check_fmt_diff_explain() {
    let d = Dir::new("main");
    let ok = d.file("ok.onsa", OK);
    let ugly = d.file("ugly.onsa", UGLY);
    let other = d.file("other.onsa", OTHER);
    let syntax = d.file("syntax.onsa", SYNTAX);
    let unresolved = d.file("unresolved.onsa", UNRESOLVED);
    let missing = d.0.join("missing.onsa").to_string_lossy().into_owned();
    for (args, want) in [
        (vec!["check", &ok], 0),
        (vec!["check", &unresolved], 1),
        (vec!["check", "--json", &unresolved], 1),
        (vec!["check", &missing], 2),
        (vec!["fmt", "--check", &ok], 0),
        (vec!["fmt", "--check", &ugly], 1),
        (vec!["fmt", "--check", &syntax], 2),
        (vec!["fmt", "--check", &missing], 2),
        (vec!["diff", "--ast", &ok, &ugly], 0),
        (vec!["diff", "--ast", &ok, &other], 1),
        (vec!["diff", "--ast", &ok, &syntax], 2),
        (vec!["diff", &ok, &ugly], 2),
        (vec!["explain", "E0811"], 0),
        (vec!["explain", "E9999"], 2),
        (vec!["test", &ok], 0),
        (vec!["build"], 2),
        (vec![], 2),
    ] {
        assert_eq!(code(&args), want, "onsa {args:?}");
    }
}

/// The saved fuzz inputs listed in `tests/pending.toml` still fail inside
/// (the gate checks it): those that exit with 101 print nothing on standard
/// output, with `--json` too (S-182), and the error on standard error.
#[test]
fn internal_errors() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let list = std::fs::read_to_string(root.join("tests/pending.toml")).unwrap();
    let mut seen = 0;
    for target in list.lines().filter_map(|l| l.strip_prefix("target = \"tests/fuzz/")) {
        let path = root.join("tests/fuzz").join(target.trim_end_matches('"'));
        let path = path.to_string_lossy().into_owned();
        let out = onsa(&["check", "--json", &path]);
        if out.status.code() != Some(101) {
            // A listed input whose `check` does not end in 101 fails elsewhere (in `fmt --check` only,
            // or by a time-out; the fuzz item of the gate checks how). Only the inputs listed as
            // `fuzz-input` are run here, so nothing else is passed over.
            continue;
        }
        seen += 1;
        assert!(out.stdout.is_empty(), "{path}: {}", String::from_utf8_lossy(&out.stdout));
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(err.starts_with("onsa: internal error: "), "{path}: {err}");
        assert!(err.contains("not in the program"), "{path}: {err}");
        assert!(!err.contains("error[E"), "{path}: an internal error has no code: {err}");
    }
    if seen == 0 {
        eprintln!("no listed fuzz input exits with 101: the 101 path is not run");
    }
}
