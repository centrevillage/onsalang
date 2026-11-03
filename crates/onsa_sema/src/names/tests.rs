//! Unit tests of the names stage (§15.1): the names of the prelude, the
//! name diagnostics, and the modules and packages a `use` and a body name.

use onsa_diag::{Code, FileId};

use crate::tests::{check, codes, pkg};
use crate::{Analysis, Package, analyze};

/// The guard-form candidates of the syntax stage bind names no identifier of
/// the file spells (`onsa_syntax::foreign::guard_name`, S-253): visible
/// without being written are only the names of the prelude, and none of them
/// is one of those.
#[test]
fn the_prelude_has_no_name_of_the_guard_candidates() {
    let a = check("pub fn f() -> I32 {\n  1\n}\n");
    assert!(!a.prelude.is_empty());
    for n in 1..=100 {
        let name = onsa_syntax::foreign::guard_name(n);
        assert!(!a.prelude.contains_key(&name), "{name} is a name of the prelude");
    }
}

#[test]
fn name_diagnostics() {
    let a = check("pub fn f(x: Missing) {}\n");
    assert_eq!(codes(&a), vec![Code::E0302]);
    let a = check("pub fn f() {}\npub fn f() {}\n");
    assert_eq!(codes(&a), vec![Code::E0304]);
    let a = check("pub flow v(x: F32 at sample) -> F32 at sample { x }\npub fn v() {}\n");
    assert_eq!(codes(&a), vec![Code::E0305]);
    let a = check("test \"a\" { assert true }\ntest \"a\" { assert true }\n");
    assert_eq!(codes(&a), vec![Code::E0306]);
    let a = check("pub fn f(x: Str) uses {Fs} {}\n");
    assert_eq!(codes(&a), vec![Code::E0302]);
    let a = analyze(&pkg(&[("a", "use b.{g}\npub fn f() {}\n"), ("b", "use a.{f}\npub fn g() {}\n")]));
    assert_eq!(codes(&a), vec![Code::E0310]);
    // A `priv` item is within its module (§15.1, S-36).
    let a =
        analyze(&pkg(&[("a", "priv fn hidden() {}\npub fn shown() {}\n"), ("b", "use a.{hidden}\nuse a.{shown}\n")]));
    assert_eq!(codes(&a), vec![Code::E0303]);
    let a = analyze(&pkg(&[("a", "use a.{x}\n")]));
    assert_eq!(codes(&a), vec![Code::E0302]);
}

/// S-666 (until it is decided): a `use` takes the module of a directory with
/// no file of its own (`a` and `a.b` of `a/b/c.onsa` alone) like a module with
/// no items, and a path through it takes what is under it.
#[test]
fn a_use_takes_the_module_of_a_directory_only_and_goes_through_it() {
    let c = ("a.b.c", "pub fn f() -> I32 {\n  1\n}\n");
    for head in ["use a\n", "use a.{b}\n", "use a.b\n"] {
        let a = analyze(&pkg(&[c, ("main", head)]));
        assert_eq!(codes(&a), [], "{head}: {:?}", a.diagnostics);
    }
    let a = analyze(&pkg(&[c, ("main", "use a.b.c.{f}\n\npub fn g() -> I32 {\n  f()\n}\n")]));
    assert_eq!(codes(&a), [], "{:?}", a.diagnostics);
}

/// A package of the modules `files`, their files numbered from `first`.
fn pkg_at(name: &str, first: u32, files: &[(&str, &str)], deps: Vec<std::sync::Arc<Package>>) -> Package {
    let mut p = pkg(files);
    for (k, m) in p.modules.iter_mut().enumerate() {
        m.file = FileId(first + k as u32);
        m.parsed = onsa_syntax::parse(m.file, &m.text);
    }
    Package::new(name, p.modules, deps)
}

/// R-39, R-88: a body names another module or a package through a `use`
/// alone. The E0302 of a head that a `use` could name has the candidate that
/// adds that `use` (after the last `use`, or before the first item), unless
/// it closes a cycle of imports; a package the package does not depend on is
/// no head (§15.1).
#[test]
fn a_body_names_modules_and_packages_through_a_use_alone() {
    use std::sync::Arc;
    let s = Arc::new(pkg_at("s", 10, &[("m", "pub fn f() -> I32 {\n  1\n}\n")], Vec::new()));
    let mid = Arc::new(pkg_at("mid", 20, &[("x", "pub fn g() -> I32 {\n  1\n}\n")], vec![s]));
    let user = |main: &str| analyze(&pkg_at("t", 0, &[("main", main)], vec![mid.clone()]));
    let one = |a: &Analysis| -> (String, Vec<(u32, String)>) {
        assert_eq!(codes(a), [Code::E0302], "{:?}", a.diagnostics);
        let d = &a.diagnostics[0];
        let edits = d.fixes.iter().flat_map(|f| f.edits()).map(|e| (e.span.start, e.replace.clone())).collect();
        (d.found.clone().unwrap_or_default(), edits)
    };
    let body = "pub fn h() -> I32 {\n  NAME\n}\n";
    let a = user(&body.replace("NAME", "s.m.f()"));
    assert_eq!(one(&a), ("s".into(), Vec::new()));
    let a = user(&body.replace("NAME", "mid.x.g()"));
    assert_eq!(one(&a), ("mid".into(), vec![(0, "use mid\n".into())]));
    let a = user(&format!("use mid.x.{{g}}\n\n{}", body.replace("NAME", "mid.x.g()")));
    assert_eq!(one(&a), ("mid".into(), vec![(13, "\nuse mid".into())]));
    let fixed = user(&format!("use mid\n\n{}", body.replace("NAME", "mid.x.g()")));
    assert_eq!(codes(&fixed), [], "{:?}", fixed.diagnostics);
    // `b` names `a`, which imports `b`: `use a` in `b` would close a cycle.
    let b = ("b", "pub fn g() -> I32 {\n  a.f()\n}\n");
    for (a_src, fixes) in [("use b\n\npub fn f() -> I32 {\n  1\n}\n", 0), ("pub fn f() -> I32 {\n  1\n}\n", 1)] {
        let an = analyze(&pkg(&[("a", a_src), b]));
        assert_eq!(codes(&an), [Code::E0302], "{:?}", an.diagnostics);
        assert_eq!(an.diagnostics[0].fixes.len(), fixes, "{a_src}");
    }
}

/// R-39: the candidate that adds `use X` is for a path with no `use`, where a
/// member follows the head (`util.f()`, `util.SIZE`), and not when the rest is
/// not found (`util.nosuch`, R-268: applying it would leave an E0302). A module
/// or a package alone at the place of a type, a value, a callee, the type of
/// an `impl` or an array length is not fixed by the `use`: E0302 with none
/// (W4-03 U2b/b: `j_type_std`, `j_value_util`, `j_call_std`, `j_impl_util`,
/// `j_arr_len`, `j_field_util`, and a call of the name of the module itself).
#[test]
fn the_candidate_of_a_use_needs_a_member_after_the_head() {
    let util = ("util", "pub const SIZE: U32 = 4\n\npub fn double(x: I32) -> I32 {\n  x * 2\n}\n");
    let cases = [
        ("pub fn k(x: util) -> I32 {\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  let x = util\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  util()\n}\n", 0),
        ("impl util {\n}\n", 0),
        ("pub fn k(a: [I32; util]) -> I32 {\n  1\n}\n", 0),
        ("pub fn k() -> I32 {\n  main(1)\n}\n", 0),
        ("pub fn k() -> I32 {\n  util.nosuch\n}\n", 0),
        ("pub fn k() -> I32 {\n  util.double(2)\n}\n", 1),
        ("pub fn k() -> U32 {\n  util.SIZE\n}\n", 1),
        ("pub fn k(a: [I32; util.SIZE]) -> I32 {\n  1\n}\n", 1),
    ];
    for (main, fixes) in cases {
        let a = analyze(&pkg(&[("main", main), util]));
        let e0302: Vec<_> = a.diagnostics.iter().filter(|d| d.code == Code::E0302).collect();
        assert_eq!(e0302.len(), 1, "{main}: {:?}", a.diagnostics);
        assert_eq!(e0302[0].fixes.len(), fixes, "{main}: {:?}", e0302[0]);
    }
}

/// S-670: a `target` declaration out of `std`, of the module or a member of an `impl`, with an
/// `else` body or none, is the one E0200 of the names stage; its `else` body is not read (no
/// E0301 for a name it does not find), and a use of the member finds it (no E0413).
#[test]
fn a_target_declaration_out_of_std_is_one_e0200_and_its_else_body_is_not_read() {
    let a = check("target fn f() -> I32 else { missing }\n");
    assert_eq!(codes(&a), vec![Code::E0200]);
    let src = "pub struct V { g: F32 }\nimpl V {\n  target fn level(self) -> F32 else { missing }\n  target fn bare(self) -> F32\n}\n\
               pub fn f(v: V) -> F32 {\n  v.level() + v.bare()\n}\n";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0200, Code::E0200]);
    let lines: Vec<u32> = a.diagnostics.iter().map(|d| d.span.start).collect();
    assert_eq!(lines, [src.find("target fn level").unwrap() as u32, src.find("target fn bare").unwrap() as u32]);
}
