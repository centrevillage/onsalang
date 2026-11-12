//! Unit tests of the packages (`flatten`, their roles), and the helpers
//! the unit tests of the crate share: a package of sources parsed in
//! memory, its analysis, its codes and its declarations by name.

use std::sync::{Arc, LazyLock, Mutex};

use onsa_diag::{Code, FileId};

use crate::ty::Ty;
use crate::{Analysis, Base, Module, Package, analyze_on};

pub(crate) fn pkg(files: &[(&str, &str)]) -> Package {
    let modules = files
        .iter()
        .enumerate()
        .map(|(i, (path, text))| {
            Module::new(
                path.split('.').map(str::to_string).collect(),
                FileId(i as u32),
                text.to_string(),
                onsa_syntax::parse(FileId(i as u32), text),
            )
        })
        .collect();
    Package::new("t", modules, vec![std_package()])
}

/// The embedded standard library (D-07, R-80 (4)), so that the spec examples
/// (`use std.math.{exp, cos}`) check here as they do in the driver.
pub(crate) fn std_package() -> Arc<Package> {
    static STD: LazyLock<Arc<Package>> = LazyLock::new(parsed_std);
    STD.clone()
}

fn parsed_std() -> Arc<Package> {
    let modules = crate::std_modules()
        .iter()
        .enumerate()
        .map(|(i, m)| {
            let id = FileId(100 + i as u32);
            Module::new(
                m.segments.iter().map(|s| s.to_string()).collect(),
                id,
                m.text.to_string(),
                onsa_syntax::parse(id, m.text),
            )
        })
        .collect();
    Arc::new(Package::std(modules))
}

/// The one analysis of std the tests continue, which only a test of more than
/// that makes again.
static BASE: LazyLock<Mutex<Base>> = LazyLock::new(|| Mutex::new(Base::new(std_package())));

/// The analysis of `p`, on [`BASE`] when it depends on the std of the tests.
pub(crate) fn analyze(p: &Package) -> Analysis {
    analyze_on(p, &BASE)
}

pub(crate) fn check(src: &str) -> Analysis {
    analyze(&pkg(&[("main", src)]))
}

pub(crate) fn codes(a: &Analysis) -> Vec<Code> {
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

/// The codes of [`check`] of `src`, sorted.
pub(crate) fn codes_of(src: &str) -> Vec<Code> {
    codes(&check(src))
}

pub(crate) fn named(a: &Analysis, name: &str) -> crate::TyId {
    let d = a.defs.iter().rposition(|d| d.name == name && d.owner.is_none()).unwrap_or_else(|| panic!("no def {name}"));
    a.types.find(&Ty::Named(crate::DefId(d as u32), Vec::new())).unwrap_or_else(|| panic!("{name} not interned"))
}

pub(crate) fn def(a: &Analysis, name: &str) -> crate::DefId {
    crate::DefId(a.defs.iter().rposition(|d| d.name == name && d.owner.is_none()).unwrap() as u32)
}

/// R-88 (1): `flatten` lists the dependencies first, depth-first, the package
/// last, and a package that several packages depend on (the same value) once,
/// where it is first reached.
#[test]
fn flatten_lists_a_shared_package_once() {
    use std::sync::Arc;
    let leaf = |name: &str| Arc::new(Package::new(name, Vec::new(), Vec::new()));
    let s = leaf("s");
    let x = leaf("x");
    let a = Arc::new(Package::new("a", Vec::new(), vec![s.clone(), x.clone()]));
    let b = Arc::new(Package::new("b", Vec::new(), vec![x.clone(), s.clone()]));
    let root = Package::new("t", Vec::new(), vec![a, s.clone(), b]);
    let names: Vec<&str> = crate::flatten(&root).iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, ["s", "x", "a", "b", "t"]);
}

/// R-88 (1): packages are the same when they are the same value, not when
/// their names are: two values named alike are two packages.
#[test]
fn flatten_tells_packages_apart_by_value_not_by_name() {
    use std::sync::Arc;
    let one = Arc::new(Package::new("s", Vec::new(), Vec::new()));
    let other = Arc::new(Package::new("s", Vec::new(), Vec::new()));
    let root = Package::new("t", Vec::new(), vec![one.clone(), other, one]);
    let flat = crate::flatten(&root);
    assert_eq!(flat.len(), 3);
    assert!(!std::ptr::eq(flat[0], flat[1]));
}

/// The role, not the name, marks the embedded std (R-88 (1)): a package
/// named `std` that depends on it is an ordinary one.
#[test]
fn the_role_marks_std() {
    let std = std::sync::Arc::new(Package::std(Vec::new()));
    let a = crate::analyze(&Package::new(crate::STD_PACKAGE, Vec::new(), vec![std]));
    assert_eq!(a.modules.names, [crate::STD_PACKAGE, crate::STD_PACKAGE]);
    assert!(a.modules.is_std(a.modules.roots[0]));
    assert!(!a.modules.is_std(a.modules.roots[1]));
}
