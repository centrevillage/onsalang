//! Unit tests of [`crate::Analysis::unread_users`] (X-3).

use onsa_diag::FileId;

use crate::{Analysis, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package::new("t", modules, Vec::new()))
}

/// The names of the defs of the file whose spans `unread_users` gives, in
/// the order of the defs.
fn users(a: &Analysis) -> Vec<&str> {
    let spans = a.unread_users(&[FileId(0)]);
    a.defs.iter().filter(|d| spans.contains(&d.span)).map(|d| d.name.as_str()).collect()
}

#[test]
fn the_users_of_an_unknown_derive_list() {
    // S-460: the list of `Pt` is not known; `ordered` declares it, `made` makes one, `wraps`
    // takes it inside another type; `calls`, `helper` and `plain` do none of these.
    let src = "#[derive(PartialEq)]\npub struct Pt {\n  x: I32,\n}\n\n\
               fn ordered(a: Pt, b: Pt) -> Bool {\n  a < b\n}\n\n\
               fn made() -> I32 {\n  let p = Pt { x: 1 }\n  p.x\n}\n\n\
               fn wraps(ps: [(Pt, I32); 2]) -> I32 {\n  1\n}\n\n\
               fn calls() -> Bool {\n  helper()\n}\n\n\
               fn helper() -> Bool {\n  true\n}\n\n\
               fn plain(x: I32) -> I32 {\n  x\n}\n";
    let a = check(src);
    let pt = a.defs.iter().position(|d| d.name == "Pt").unwrap();
    assert!(a.defs[pt].as_struct().unwrap().derives.is_none());
    assert_eq!(users(&a), ["Pt", "ordered", "made", "wraps"]);
}

#[test]
fn the_users_of_a_type_that_failed_to_resolve() {
    // `Missng` is no type (E0302): `g` declares it, `caller` calls `g`, `other` does not.
    let src = "fn g(p: Missng) -> I32 {\n  1\n}\n\n\
               fn caller() -> I32 {\n  g(1)\n}\n\n\
               fn other() -> I32 {\n  2\n}\n";
    let a = check(src);
    assert!(!a.diagnostics.is_empty());
    assert_eq!(users(&a), ["g", "caller"]);
}

#[test]
fn the_users_of_an_item_read_in_part() {
    // A syntax error cuts the fields of `S` (S-260): `field` reads one, `other` does not.
    let src = "pub struct S {\n  x: I32,\n  y: I32 +,\n}\n\n\
               fn field(s: S) -> I32 {\n  s.x\n}\n\n\
               fn other() -> I32 {\n  2\n}\n";
    let a = check(src);
    let s = crate::DefId(a.defs.iter().position(|d| d.name == "S").unwrap() as u32);
    assert!(a.partly_read(s), "{:?}", a.failed);
    assert_eq!(users(&a), ["S", "field"]);
}

#[test]
fn a_check_with_nothing_unread_has_no_users() {
    let a = check("pub struct P {\n  x: I32,\n}\n\nfn f(p: P) -> I32 {\n  p.x\n}\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    assert!(users(&a).is_empty());
    // Another file's defs are not given.
    let a = check("#[derive(PartialEq)]\npub struct Pt {\n  x: I32,\n}\n");
    assert!(a.unread_users(&[FileId(1)]).is_empty());
}
