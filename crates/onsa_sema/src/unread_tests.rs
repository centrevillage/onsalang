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

#[test]
fn the_callers_of_an_rt_function_whose_body_read_a_held_name_are_users() {
    // `Gone` is a name of a failed `use`, held as an error (§18.1): `r1` reads it in a type place only, so its
    // body is checked to its end, but the call `v.f()` on a value of the error type has no callee and makes no
    // edge of the rt recursion. When the `use` is fixed to give the struct `S`, `f -> r1 -> f` is an E0903 at
    // the call in `f`, the earliest of the cycle: `f` calls `r1`, so it is a user too (X-3/U1c/b, F1; W4-03 U3c).
    let src = "use util.{Gone}\n\npub struct S {\n  a: I32,\n}\n\n\
               impl S {\n  pub rt fn f(self) -> I32 {\n    r1()\n  }\n}\n\n\
               pub rt fn r1() -> I32 {\n  let o: Option[Gone] = None\n  match o {\n    Some(v) => v.f(),\n    None => 0,\n  }\n}\n\n\
               pub fn other() -> I32 {\n  2\n}\n";
    let a = check(src);
    let r1 = crate::DefId(a.defs.iter().position(|d| d.name == "r1").unwrap() as u32);
    assert!(a.bodies[&r1].complete && a.bodies[&r1].read_unread, "{:?}", a.diagnostics);
    let users = users(&a);
    assert_eq!(users, ["f", "r1"], "{:?}", a.diagnostics);
}

#[test]
fn a_body_that_reads_a_constant_in_a_hole_is_a_user() {
    // `Missng` is no type (E0302), so the type of `K` failed to resolve: `in_hole` reads `K` in a hole of a
    // string only (§2.4), whose target the hole keeps (W4-04 U4/b, F4); `in_expr` reads it in an expression;
    // `other` reads neither.
    let src = "const K: Missng = 1\n\n\
               fn in_hole() -> Str uses {Alloc} {\n  \"{K}\"\n}\n\n\
               fn in_expr() -> I32 {\n  let k = K\n  1\n}\n\n\
               fn other() -> I32 {\n  2\n}\n";
    let a = check(src);
    assert_eq!(users(&a), ["K", "in_hole", "in_expr"], "{:?}", a.diagnostics);
}
