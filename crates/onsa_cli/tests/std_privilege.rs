//! The privilege of `std` and a package of a user (spec §15.1, §15.2; R-88 (1)): the `target` declarations
//! are the implementation's for the embedded `std` only. A module of a user whose path is the name of a
//! dependency or of a module of std (`std.onsa`, `std/math.onsa`, a single file `std.onsa`) is the user's
//! module: its `target` declarations are E0200 (§15.2), and the name is E0304 (§15.1: a root module that has
//! the name of a dependency, `std` included). Both are reported; neither takes the privilege of std.
//!
//! The cases of the other forms are `tests/spec/module/target_user_*` (a user package, the forms of the
//! declarations) and `tests/spec/packages/std_names_target_user` (modules named like modules of std).

mod test_support;

use std::collections::BTreeSet;

use test_support::*;

const TARGET: &str = "target fn sqrt(x: F32) -> F32\n";

/// The (code, file) pairs of the diagnostics of `onsa check --json <arg>` run in `d`.
fn pairs(d: &Dir, arg: &str) -> BTreeSet<(String, String)> {
    let out = run(d.root(), &["check", "--json", arg]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = doc_of(&out);
    diagnostics(&doc).iter().map(|x| (str_of(x, "code").to_string(), str_of(&x["span"], "file").to_string())).collect()
}

fn set(items: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    items.iter().map(|(c, f)| (c.to_string(), f.to_string())).collect()
}

#[test]
fn a_root_module_named_std_has_no_target_privilege() {
    let d = Dir::pkg("priv_std_file");
    d.write("std.onsa", TARGET);
    assert_eq!(pairs(&d, "."), set(&[("E0200", "std.onsa"), ("E0304", "std.onsa")]));
}

#[test]
fn a_root_directory_named_std_has_no_target_privilege() {
    let d = Dir::pkg("priv_std_dir");
    d.write("std/math.onsa", TARGET);
    assert_eq!(pairs(&d, "."), set(&[("E0200", "std/math.onsa"), ("E0304", "std/math.onsa")]));
}

/// A module of the user with the path of a module of std, but not at the root of a dependency's name:
/// `math.onsa` is the user's `math`, and `a/std.onsa` is `a.std`. Only E0200.
#[test]
fn modules_with_the_paths_of_std_modules_that_are_not_clashes_have_no_privilege() {
    let d = Dir::pkg("priv_std_like");
    d.write("math.onsa", TARGET);
    d.write("a/std.onsa", "target fn other(x: F32) -> F32\n");
    assert_eq!(pairs(&d, "."), set(&[("E0200", "math.onsa"), ("E0200", "a/std.onsa")]));
}

/// A single file is a package of one module named by the file (§15.1), and `std.onsa` is a module named like
/// the dependency.
#[test]
fn a_single_file_named_std_has_no_target_privilege() {
    let d = Dir::bare("priv_std_single");
    d.write("std.onsa", TARGET);
    assert_eq!(pairs(&d, "std.onsa"), set(&[("E0200", "std.onsa"), ("E0304", "std.onsa")]));
}
