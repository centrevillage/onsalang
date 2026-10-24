//! Symbolic links, hard links, FIFOs and unreadable items in the tree of a package, and links in the
//! path that is given (spec §15.1; S-592, S-272, S-622; R-47; W4-14 U1).
//!
//! What the spec fixes, and so what is checked here:
//! - an item whose name starts with `.` (and the root's `target/`) is left out before its kind is
//!   looked at, a link or a FIFO too, so such an item is never an error;
//! - the links in the tree are not followed. An item whose name ends in `.onsa` that is neither a
//!   regular file nor a directory (a link to a file or to a directory, a broken link, a FIFO) is a
//!   usage error (exit code 2); a link or another special file whose name does not end in `.onsa`
//!   is left out without a word, and a loop of links does not happen. A hard link is a regular
//!   file, and each of its paths is a module;
//! - a directory that cannot be read and a `.onsa` file that cannot be read are an I/O error (exit
//!   code 2); the directories that are not gathered (by name, nested packages) are not opened;
//! - the links in the path that is given are resolved to find the root (the middle of the path
//!   too), and only for that: the module name and the `span.file` of a single file with no manifest
//!   stay as passed. `onsa.toml` may be a link, and its target is the manifest; as a path it is the
//!   directory it is in (S-622).
//!
//! A FIFO can make a command wait for ever, so every run here ends by force after a while (a test
//! that hangs fails; it never stalls the run). Tests that need a permission denied are skipped when
//! the process is allowed to read anything (the superuser).
//!
//! Not written here: the tree without links (`package_tree.rs`), the choice of the package
//! (`package_input.rs`), the names (E0320, U2). A FIFO given as the path itself is not written (the
//! spec does not say what it is; reading it would wait for a writer).
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work
//! that fixes their cause.

#![cfg(unix)]

mod test_support;

use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;
use test_support::*;

const OK_TEST: &str = "pub fn f() -> I32 {\n  1\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";

/// One error (E0302 at line 2), so that a file read twice would show twice.
const ONE_ERROR: &str = "pub fn f() -> I32 {\n  zzz\n}\n\ntest \"t\" {\n  assert f() == 1\n}\n";

const LIMIT: u64 = 10;

fn s(x: &str) -> String {
    x.to_string()
}

fn manifest(name: &str) -> String {
    format!("[package]\nname = \"{name}\"\nedition = \"2026\"\n")
}

/// The scratch directory, with the permissions given back before it is removed.
struct Tree(Dir);

impl Tree {
    fn bare(tag: &str) -> Tree {
        Tree(Dir::bare(&format!("links_{tag}")))
    }

    fn root(&self) -> &Path {
        self.0.root()
    }

    fn write(&self, rel: &str, text: &str) {
        self.0.write(rel, text);
    }

    fn at(&self, rel: &str) -> PathBuf {
        self.0.root().join(rel)
    }

    /// `at(rel)` becomes a link to `target` (the text of the link, as it is).
    fn link(&self, rel: &str, target: &str) {
        let p = self.at(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        symlink(target, &p).unwrap_or_else(|e| panic!("link {rel} -> {target}: {e}"));
    }

    fn fifo(&self, rel: &str) {
        let p = self.at(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        let st = Command::new("mkfifo").arg(&p).status().expect("run mkfifo");
        assert!(st.success(), "mkfifo {rel}");
    }

    fn chmod(&self, rel: &str, mode: u32) {
        fs::set_permissions(self.at(rel), fs::Permissions::from_mode(mode)).unwrap();
    }

    /// A package `pkg` with `a.onsa` (a test) and `sub/b.onsa` (a test).
    fn package(&self, root: &str, a: &str) {
        self.write(&format!("{root}/onsa.toml"), &manifest("demo"));
        self.write(&format!("{root}/a.onsa"), a);
        self.write(&format!("{root}/sub/b.onsa"), OK_TEST);
    }
}

fn restore(p: &Path) {
    let Ok(md) = fs::symlink_metadata(p) else { return };
    if md.is_dir() {
        let _ = fs::set_permissions(p, fs::Permissions::from_mode(0o755));
        if let Ok(rd) = fs::read_dir(p) {
            for e in rd.flatten() {
                restore(&e.path());
            }
        }
    } else if md.is_file() {
        let _ = fs::set_permissions(p, fs::Permissions::from_mode(0o644));
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        restore(self.0.root());
    }
}

fn go(cwd: &Path, args: &[&str]) -> Out {
    run_limited(cwd, args, LIMIT)
}

fn check_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = go(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

fn tests_json(cwd: &Path, args: &[&str]) -> (Out, Value) {
    let mut a = vec!["test", "--json"];
    a.extend_from_slice(args);
    let out = go(cwd, &a);
    let doc = doc_of(&out);
    (out, doc)
}

fn code_files(doc: &Value) -> Vec<(String, String)> {
    diagnostics(doc).iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).file)).collect()
}

fn ids(doc: &Value) -> Vec<(String, String)> {
    identities(doc)
}

/// A command that ended in 2 without a diagnostic (§18.2).
fn assert_usage_error(out: &Out, json: bool, what: &str) {
    assert_eq!(out.code, 2, "{what}: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.is_empty(), "{what}: the reason is on the standard error");
    if json {
        assert_eq!(out.stdout, "", "{what}: nothing on the standard output with --json");
    }
}

/// The three ways to read the package `pkg` of the tree: a usage error each.
fn assert_refused(t: &Tree, pkg: &str, what: &str) {
    let arg = t.at(pkg).to_string_lossy().into_owned();
    assert_usage_error(&go(t.root(), &["check", "--json", &arg]), true, &format!("{what}: check"));
    assert_usage_error(&go(t.root(), &["test", "--json", &arg]), true, &format!("{what}: test"));
    assert_usage_error(&go(t.root(), &["interface", "--json", &arg]), true, &format!("{what}: interface"));
}

/// A package `pkg` that is clean, and reads as the modules `a` and `sub.b` only.
fn assert_reads_as_a_and_sub_b(t: &Tree, pkg: &str, what: &str) {
    let arg = t.at(pkg).to_string_lossy().into_owned();
    let (out, doc) = check_json(t.root(), &[&arg]);
    assert_eq!(out.code, 0, "{what}: check: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{what}: {doc}");
    let (out, doc) = tests_json(t.root(), &[&arg]);
    assert_eq!(out.code, 0, "{what}: test: {}{}", out.stdout, out.stderr);
    assert_eq!(ids(&doc), [(s("a"), s("t")), (s("sub.b"), s("t"))], "{what}");
}

// ---- links in the tree -----------------------------------------------------------------------------

/// S-592 (1): a link whose name ends in `.onsa` is a usage error, whatever it points at.
#[test]
fn a_link_named_onsa_is_a_usage_error_whatever_it_points_at() {
    let cases: &[(&str, &str)] = &[
        ("c.onsa", "a.onsa"),          // to a file in the package
        ("sub/c.onsa", "../a.onsa"),   // the same, one level down
        ("e.onsa", "../ext/e.onsa"),   // to a file outside
        ("d.onsa", "sub"),             // to a directory in the package
        ("x.onsa", "../ext"),          // to a directory outside
        ("gone.onsa", "nowhere.onsa"), // broken, as a file
        ("g.onsa", "nowhere"),         // broken, as a directory
        ("loop.onsa", "."),            // a loop
        ("sub/up.onsa", ".."),         // to the parent
        ("self.onsa", "self.onsa"),    // a link to itself
        ("c2.onsa", "c3"),             // a link to a link (c3 does not end in `.onsa`)
    ];
    for (i, (name, target)) in cases.iter().enumerate() {
        let t = Tree::bare(&format!("onsa_named_{i}"));
        t.write("ext/e.onsa", OK_TEST);
        t.package("pkg", OK_TEST);
        if *name == "c2.onsa" {
            t.link("pkg/c3", "a.onsa");
        }
        t.link(&format!("pkg/{name}"), target);
        assert_refused(&t, "pkg", &format!("{name} -> {target}"));
    }
}

/// S-592 (1), S-272: a link whose name does not end in `.onsa` is not followed and not an error, so
/// the package reads as if it was not there: the same two modules, every error once, no loop.
fn add_links_of_other_names(t: &Tree) {
    t.write("ext/e.onsa", ONE_ERROR);
    t.write("ext/sub2/e2.onsa", ONE_ERROR);
    t.link("pkg/d", "sub"); // a directory in the package
    t.link("pkg/out", "../ext"); // a directory outside
    t.link("pkg/loop", "."); // a loop
    t.link("pkg/sub/up", ".."); // to the parent
    t.link("pkg/gonedir", "nowhere"); // broken
    t.link("pkg/gonefile", "nowhere.txt");
    t.link("pkg/c.txt", "a.onsa"); // a file
    t.link("pkg/c", "a.onsa");
    t.link("pkg/e", "../ext/e.onsa");
    t.link("pkg/self", "self"); // a link to itself
    t.link("pkg/sub/deeplink", "../../ext");
}

#[test]
fn a_link_with_another_name_is_left_out_and_not_followed() {
    let t = Tree::bare("other_names_clean");
    t.package("pkg", OK_TEST);
    add_links_of_other_names(&t);
    assert_reads_as_a_and_sub_b(&t, "pkg", "links of other names");
}

/// A file that has an error is reported once, though a link to its directory or to it is there
/// (a loop would show it many times).
#[test]
fn an_error_is_reported_once_whatever_links_point_at_the_file() {
    let t = Tree::bare("other_names_error");
    t.package("pkg", ONE_ERROR);
    add_links_of_other_names(&t);
    let arg = t.at("pkg").to_string_lossy().into_owned();
    let (out, doc) = check_json(t.root(), &[&arg]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("a.onsa"))], "{doc}");
}

/// S-592: the name is looked at before the kind. A dot name (any kind) and the root's `target`
/// (a link too) are left out, so none of them is an error.
#[test]
fn a_name_left_out_is_left_out_before_its_kind_is_looked_at() {
    let t = Tree::bare("name_first");
    t.package("pkg", OK_TEST);
    t.write("ext/e.onsa", ONE_ERROR);
    t.link("pkg/.l.onsa", "a.onsa");
    t.link("pkg/.d.onsa", "sub");
    t.link("pkg/.g.onsa", "nowhere.onsa");
    t.link("pkg/.loop.onsa", ".");
    t.link("pkg/sub/.up.onsa", "..");
    t.fifo("pkg/.p.onsa");
    t.fifo("pkg/sub/.q.onsa");
    t.link("pkg/target", "../ext");
    assert_reads_as_a_and_sub_b(&t, "pkg", "dot names and a linked target");
}

/// S-592: a hard link is a regular file, so each of its paths is a module (and its tests run twice,
/// once under each module).
#[test]
fn a_hard_link_is_a_regular_file_and_each_path_is_a_module() {
    let t = Tree::bare("hard");
    t.package("pkg", OK_TEST);
    fs::hard_link(t.at("pkg/a.onsa"), t.at("pkg/h.onsa")).unwrap();
    let arg = t.at("pkg").to_string_lossy().into_owned();
    let (out, doc) = tests_json(t.root(), &[&arg]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(ids(&doc), [(s("a"), s("t")), (s("h"), s("t")), (s("sub.b"), s("t"))]);
}

// ---- special files -----------------------------------------------------------------------------------

/// S-592: a FIFO whose name ends in `.onsa` is a usage error, and it is not opened (opening it
/// would wait for ever; the run is stopped by force and the test fails if it is).
#[test]
fn a_fifo_named_onsa_is_a_usage_error_and_is_not_opened() {
    for (i, rel) in ["p.onsa", "sub/p.onsa", "deep/er/q.onsa"].iter().enumerate() {
        let t = Tree::bare(&format!("fifo_named_{i}"));
        t.package("pkg", OK_TEST);
        t.fifo(&format!("pkg/{rel}"));
        assert_refused(&t, "pkg", rel);
    }
}

/// S-592: a FIFO with another name is left out without a word.
#[test]
fn a_fifo_with_another_name_is_left_out() {
    let t = Tree::bare("fifo_other");
    t.package("pkg", OK_TEST);
    t.fifo("pkg/p");
    t.fifo("pkg/p.fifo");
    t.fifo("pkg/sub/p.txt");
    t.fifo("pkg/onsa.toml.fifo");
    assert_reads_as_a_and_sub_b(&t, "pkg", "FIFOs of other names");
}

/// A FIFO below a directory that is not gathered is not looked at: a dot directory, the root's
/// `target/` and a nested package are not opened.
#[test]
fn nothing_below_a_directory_that_is_not_gathered_is_looked_at() {
    let t = Tree::bare("fifo_not_gathered");
    t.package("pkg", OK_TEST);
    t.fifo("pkg/.hid/p.onsa");
    t.link("pkg/.hid/l.onsa", "nowhere.onsa");
    t.fifo("pkg/target/p.onsa");
    t.write("pkg/inner/onsa.toml", &manifest("inner"));
    t.fifo("pkg/inner/p.onsa");
    t.link("pkg/inner/l.onsa", "nowhere.onsa");
    assert_reads_as_a_and_sub_b(&t, "pkg", "FIFOs below directories that are not gathered");
}

// ---- unreadable items (S-592 (3)) ---------------------------------------------------------------------

/// True when the superuser (or another reason) lets a process read what the mode forbids; the
/// tests of permissions have nothing to show then.
fn permissions_do_not_bite(t: &Tree) -> bool {
    t.write("probe/x", "x");
    t.chmod("probe", 0o000);
    let open = fs::read_dir(t.at("probe")).is_ok();
    t.chmod("probe", 0o755);
    if open {
        eprintln!("skipped: the permission 000 does not stop reading here");
    }
    open
}

#[test]
fn a_directory_or_a_onsa_file_that_cannot_be_read_is_an_io_error() {
    let t = Tree::bare("unreadable");
    if permissions_do_not_bite(&t) {
        return;
    }
    t.package("dir", OK_TEST);
    t.write("dir/locked/c.onsa", OK_TEST);
    t.chmod("dir/locked", 0o000);
    assert_refused(&t, "dir", "an unreadable directory");
    t.package("file", OK_TEST);
    t.write("file/c.onsa", OK_TEST);
    t.chmod("file/c.onsa", 0o000);
    assert_refused(&t, "file", "an unreadable .onsa file");
    // the file is the one given
    let out = go(t.root(), &["check", "--json", &t.at("file/c.onsa").to_string_lossy()]);
    assert_usage_error(&out, true, "an unreadable .onsa file given by its path");
}

/// §15.1: what is not gathered is not opened, and what is not a `.onsa` file is not read.
#[test]
fn items_that_are_left_out_are_not_opened() {
    let t = Tree::bare("unreadable_left_out");
    if permissions_do_not_bite(&t) {
        return;
    }
    t.package("pkg", OK_TEST);
    t.write("pkg/.hid/q.onsa", OK_TEST);
    t.write("pkg/target/g.onsa", OK_TEST);
    t.write("pkg/inner/onsa.toml", &manifest("inner"));
    t.write("pkg/inner/locked/z.onsa", OK_TEST);
    t.write("pkg/README.md", "text\n");
    t.write("pkg/.q.onsa", OK_TEST);
    for rel in ["pkg/.hid", "pkg/target", "pkg/inner/locked"] {
        t.chmod(rel, 0o000);
    }
    for rel in ["pkg/README.md", "pkg/.q.onsa"] {
        t.chmod(rel, 0o000);
    }
    assert_reads_as_a_and_sub_b(&t, "pkg", "unreadable items that are left out");
}

// ---- links in the path that is given (S-272, S-622) ------------------------------------------------

/// A package `base` whose `sub/b.onsa` has an error, and a clean `a.onsa`.
fn base_with_error(t: &Tree) {
    t.write("base/onsa.toml", &manifest("base"));
    t.write("base/a.onsa", OK_TEST);
    t.write("base/sub/b.onsa", ONE_ERROR);
}

/// §15.1: a link to the root, or a link in the middle of the path, is resolved to find the
/// manifest, and the files are named from the root all the same.
#[test]
fn a_link_in_the_given_path_is_resolved_to_find_the_root() {
    let t = Tree::bare("path_dir_link");
    base_with_error(&t);
    t.link("rlink", "base"); // the root
    t.link("lnk", "base/sub"); // a directory below the root
    t.write("elsewhere/keep", "x");
    for (cwd, arg) in [
        (t.root().to_path_buf(), s("rlink")),
        (t.root().to_path_buf(), s("rlink/sub/b.onsa")),
        (t.root().to_path_buf(), s("lnk/b.onsa")),
        // S-637: a link that is given by a name that is neither `.onsa` nor `onsa.toml` (`cut -> base/sub/b.onsa`) is not written: the spec does not say whether the given name or the name it points at decides.
        (t.at("elsewhere"), t.at("rlink").to_string_lossy().into_owned()),
        (t.at("elsewhere"), t.at("lnk/b.onsa").to_string_lossy().into_owned()),
    ] {
        let (out, doc) = check_json(&cwd, &[&arg]);
        assert_eq!(out.code, 1, "{arg}: {}{}", out.stdout, out.stderr);
        assert_eq!(code_files(&doc), [(s("E0302"), s("sub/b.onsa"))], "{arg}: {doc}");
    }
}

/// S-272: the module of a file that is given as a link is the module of the file it points at, in
/// its package (`outfile.onsa -> base/sub/b.onsa` is `sub.b` of `base`).
#[test]
fn a_file_link_given_from_outside_is_the_module_of_its_target_in_the_target_package() {
    let t = Tree::bare("path_file_link");
    t.write("base/onsa.toml", &manifest("base"));
    t.write("base/a.onsa", ONE_ERROR);
    t.write("base/sub/b.onsa", OK_TEST);
    t.link("outfile.onsa", "base/sub/b.onsa");
    let (out, doc) = check_json(t.root(), &["outfile.onsa"]);
    assert_eq!(out.code, 0, "the error of a.onsa is not printed: {}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{doc}");
}

/// §15.1: the search starts at the place the link points at. A file that is a link in a package to a
/// place with no manifest above it is a package of its own: its module name and `span.file` are as
/// passed (`pkg/x.onsa`, the module `x`), though a manifest is above the link.
#[test]
fn a_link_in_a_package_to_a_place_with_no_manifest_is_a_single_file_as_passed() {
    let t = Tree::bare("path_to_loose");
    t.write("pkg/onsa.toml", &manifest("demo"));
    t.write("pkg/a.onsa", ONE_ERROR);
    t.write("loose/real.onsa", ONE_ERROR);
    t.link("pkg/x.onsa", "../loose/real.onsa");
    let (out, doc) = check_json(t.root(), &["pkg/x.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("pkg/x.onsa"))], "{doc}");
    let (out, doc) = tests_json(t.root(), &["pkg/x.onsa"]);
    assert_eq!(out.code, 1, "the error is the check's: {}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("pkg/x.onsa"))], "{doc}");
    // the same without the error: the module is `x`
    t.write("loose/real.onsa", OK_TEST);
    let (out, doc) = tests_json(t.root(), &["pkg/x.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(ids(&doc), [(s("x"), s("t"))], "{doc}");
    let (cwd_out, cwd_doc) = tests_json(&t.at("pkg"), &["x.onsa"]);
    assert_eq!(cwd_out.code, 0, "{}{}", cwd_out.stdout, cwd_out.stderr);
    assert_eq!(ids(&cwd_doc), [(s("x"), s("t"))], "{cwd_doc}");
}

/// S-622: `x/onsa.toml -> ../y/onsa.toml`. The manifest passed as a path is the directory it is in,
/// so `x` and `x/onsa.toml` give the same input: the files of `x`, not of `y`, and the manifest
/// that is read is the target of the link.
fn x_and_y(t: &Tree, y_manifest: &str) {
    t.write("x/a.onsa", ONE_ERROR);
    t.write("y/onsa.toml", y_manifest);
    t.write("y/b.onsa", ONE_ERROR);
    t.link("x/onsa.toml", "../y/onsa.toml");
}

#[test]
fn a_manifest_given_as_a_link_is_the_directory_it_is_in() {
    let t = Tree::bare("manifest_link");
    x_and_y(&t, &manifest("shared"));
    for (cwd, args) in [
        (t.root().to_path_buf(), vec!["x"]),
        (t.root().to_path_buf(), vec!["x/onsa.toml"]),
        (t.root().to_path_buf(), vec!["x/a.onsa"]),
        (t.at("x"), vec!["onsa.toml"]),
        (t.at("x"), vec![]),
    ] {
        let (out, doc) = check_json(&cwd, &args);
        assert_eq!(out.code, 1, "{args:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(code_files(&doc), [(s("E0302"), s("a.onsa"))], "{args:?} from {cwd:?}: {doc}");
    }
    // `y` is its own package
    let (out, doc) = check_json(t.root(), &["y/onsa.toml"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("b.onsa"))], "{doc}");
}

const BUILD_TARGET: &str = "\n[export]\nprefix = \"pk_\"\nfns = [\"a.f\"]\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// S-622, §15.1: the target of the link is the manifest that is read. The target `host` is in the
/// manifest of `y` only, and `build --target host` of `x` finds it: it builds into `x/target/`.
#[test]
fn the_target_of_a_manifest_link_is_the_manifest_that_is_read() {
    let t = Tree::bare("manifest_link_read");
    x_and_y(&t, &format!("{}{BUILD_TARGET}", manifest("shared")));
    t.write("x/a.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    for (cwd, args) in [(t.root().to_path_buf(), vec!["x"]), (t.at("x"), vec![])] {
        let mut a = vec!["build", "--target", "host"];
        a.extend_from_slice(&args);
        let out = go(&cwd, &a);
        assert_eq!(out.code, 0, "{a:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(t.at("x/target/host").is_dir(), "{a:?}: built into the root `x`");
        assert!(!t.at("y/target").exists(), "{a:?}: nothing is built in `y`");
        fs::remove_dir_all(t.at("x/target")).expect("remove the output of the build");
    }
}

/// S-622: the manifest is given as a path, it is a link, and it has no target: an I/O error. (Whether
/// a broken `onsa.toml` found by the search upward, or in a directory that is given, counts as found
/// is not written in the spec, and no test here says.)
#[test]
fn a_manifest_given_as_a_path_that_is_a_link_with_no_target_is_an_io_error() {
    let t = Tree::bare("manifest_link_broken");
    t.write("x/a.onsa", OK_TEST);
    t.link("x/onsa.toml", "../nowhere.toml");
    for (cwd, arg) in [(t.root().to_path_buf(), "x/onsa.toml"), (t.at("x"), "onsa.toml"), (t.at("x"), "./onsa.toml")] {
        for cmd in ["check", "test", "interface"] {
            let out = go(&cwd, &[cmd, "--json", arg]);
            assert_usage_error(&out, true, &format!("{cmd} {arg} from {cwd:?}"));
        }
    }
}

/// §15.1: a child directory whose `onsa.toml` is a link is a nested package as well: the manifest is
/// the target of the link, and the package around it does not gather below it.
#[test]
fn a_nested_package_whose_manifest_is_a_link_is_left_out() {
    let t = Tree::bare("nested_manifest_link");
    t.package("pkg", OK_TEST);
    t.write("shared/m.toml", &manifest("inner"));
    t.write("pkg/inner/z.onsa", ONE_ERROR);
    t.link("pkg/inner/onsa.toml", "../../shared/m.toml");
    assert_reads_as_a_and_sub_b(&t, "pkg", "a nested package with a linked manifest");
    // and a file of it belongs to it: its `use` of the outer module is not found
    t.write("pkg/inner/z.onsa", "use a.{f}\n");
    let (out, doc) = check_json(t.root(), &["pkg/inner/z.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("z.onsa"))], "{doc}");
}

/// S-622, §15.1: `onsa.toml` as a path is the directory it is in, and its target is the manifest. A
/// link named `onsa.toml` that points at a directory has no manifest to read: an I/O error.
#[test]
fn a_manifest_link_that_points_at_a_directory_is_an_io_error() {
    let t = Tree::bare("manifest_link_dir");
    t.write("p/onsa.toml", &manifest("p"));
    t.write("p/a.onsa", OK_TEST);
    t.write("p/sub/b.onsa", OK_TEST);
    t.write("w2/keep", "x");
    t.link("w2/onsa.toml", "../p");
    for (cwd, arg) in [(t.root().to_path_buf(), "w2/onsa.toml"), (t.at("w2"), "onsa.toml")] {
        for cmd in ["check", "test", "interface"] {
            let out = go(&cwd, &[cmd, "--json", arg]);
            assert_usage_error(&out, true, &format!("{cmd} {arg} from {cwd:?}"));
        }
    }
}

/// §15.1: a link in the middle of the path is resolved to find the root, also when its name is
/// `onsa.toml` and it points at a directory: `w2/onsa.toml/sub/b.onsa` is `sub/b.onsa` of `p`. (The
/// name `onsa.toml` makes a difference only for the last part of the path.)
#[test]
fn a_file_below_a_manifest_link_to_a_directory_is_a_file_of_that_directorys_package() {
    let t = Tree::bare("manifest_link_dir_below");
    t.write("p/onsa.toml", &manifest("p"));
    t.write("p/a.onsa", OK_TEST);
    t.write("p/sub/b.onsa", ONE_ERROR);
    t.write("w2/keep", "x");
    t.link("w2/onsa.toml", "../p");
    let (out, doc) = check_json(t.root(), &["w2/onsa.toml/sub/b.onsa"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(code_files(&doc), [(s("E0302"), s("sub/b.onsa"))], "{doc}");
}
