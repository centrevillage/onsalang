//! The record of the names of a body (W4-04 U2a): the bindings and their
//! numbers, the anonymous functions and their captures, the sites of the
//! bindings of `match`, `for` and a choice, the origins, the scopes, the
//! holes of a string, and a body the walk stops in.

use onsa_diag::FileId;
use onsa_syntax::ast::{ExprKind, Mode, PatKind};

use super::{BindingId, BindingKind, BodyNames, Origin, PatRes, PathRes, ScopeId};
use crate::body::{LocalId, Target};
use crate::{Analysis, DefId, Module, Package, analyze};

fn analysis(src: &str) -> (Analysis, Module) {
    let module = || Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.into(),
        parsed: onsa_syntax::parse(FileId(0), src),
    };
    (analyze(&Package::new("t", vec![module()], Vec::new())), module())
}

fn def(a: &Analysis, name: &str) -> DefId {
    DefId(a.defs.iter().position(|d| d.name == name).unwrap_or_else(|| panic!("no def {name}")) as u32)
}

fn names<'a>(a: &'a Analysis, name: &str) -> &'a BodyNames {
    &a.names[&def(a, name)]
}

fn binding_names(n: &BodyNames) -> Vec<&str> {
    n.bindings.iter().map(|b| b.name.as_str()).collect()
}

/// The binding named `name` (the first one).
fn binding(n: &BodyNames, name: &str) -> BindingId {
    BindingId(n.bindings.iter().position(|b| b.name == name).unwrap_or_else(|| panic!("no binding {name}")) as u32)
}

#[test]
fn locals_are_numbered_in_source_order_as_the_types_stage_numbers_them() {
    let src = "pub fn f(a: I32, _: I32, b: I32) -> I32 {\n  let c = a + b\n  var d = c\n  d = d + 1\n  d\n}\n";
    let (a, _) = analysis(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let n = names(&a, "f");
    assert!(n.complete);
    assert_eq!(binding_names(n), ["a", "b", "c", "d"]);
    let kinds: Vec<BindingKind> = n.bindings.iter().map(|b| b.kind).collect();
    assert_eq!(
        kinds,
        [BindingKind::Param(Mode::Borrow), BindingKind::Param(Mode::Borrow), BindingKind::Let, BindingKind::Var]
    );
    assert_eq!(n.bindings[0].origin, Origin::Param(0));
    assert_eq!(n.bindings[1].origin, Origin::Param(2));
    assert!(matches!(n.bindings[2].origin, Origin::Let(_)));
    assert!(matches!(n.bindings[3].origin, Origin::Var(_)));
    // The target of `d = d + 1` is no read.
    let reads: Vec<u32> = n.bindings.iter().map(|b| b.reads).collect();
    assert_eq!(reads, [1, 1, 1, 2]);
    // A parameter and a `var` have no pattern; the `let` has its own.
    assert!(n.bindings[0].sites.is_empty() && n.bindings[3].sites.is_empty());
    assert_eq!(n.pats.get(&n.bindings[2].sites[0]), Some(&PatRes::Bind(BindingId(2))));
    // The numbers are those of the locals of the types stage, and each path to
    // a local is the one its target names.
    let body = &a.bodies[&def(&a, "f")];
    let locals: Vec<&str> = body.locals.iter().map(|l| l.name.as_str()).collect();
    assert_eq!(locals, binding_names(n));
    assert_eq!(n.paths.len(), 6);
    for (e, r) in &n.paths {
        let PathRes::Local(b) = r else { panic!("{r:?}") };
        assert!(matches!(body.targets.get(e), Some(Target::Local(l)) if *l == LocalId(b.0)), "{e:?}");
    }
}

#[test]
fn anonymous_functions_capture_what_they_and_those_inside_them_read() {
    let src = "pub fn apply(f: fn(U32) -> U32) -> U32 { f(1) }\npub fn g(k: U32, m: U32) -> U32 {\n  apply(fn(i) { apply(fn(j) { j + k }) + i + m })\n}\n";
    let (a, _) = analysis(src);
    let n = names(&a, "g");
    assert_eq!(binding_names(n), ["k", "m", "i", "j"]);
    let mut closures: Vec<_> = n.captures.iter().collect();
    assert_eq!(closures.len(), 2);
    closures.sort_by_key(|(e, _)| e.0);
    // The outer one reads `k` through the inner one, before `m`.
    let (k, m) = (binding(n, "k"), binding(n, "m"));
    let caps: Vec<&Vec<BindingId>> = closures.iter().map(|(_, c)| *c).collect();
    assert!(caps.contains(&&vec![k, m]) && caps.contains(&&vec![k]), "{caps:?}");
    let outer = closures.iter().find(|(_, c)| c.len() == 2).unwrap().0;
    let i = &n.bindings[binding(n, "i").0 as usize];
    assert_eq!(i.kind, BindingKind::ClosureParam(Mode::Borrow));
    assert_eq!(i.origin, Origin::Closure { closure: *outer, param: 0 });
    assert_eq!(n.bindings[k.0 as usize].reads, 1);
}

#[test]
fn the_branches_of_a_choice_bind_one_binding_with_a_site_each() {
    let src = "pub fn n(q: ((I32, I32), I32)) -> I32 {\n  match q {\n    ((x, 0) | (0, x), 1) | ((x, 1) | (1, x), 2) => x,\n    (y, _) => 0,\n  }\n}\npub fn s() -> I32 {\n  var t = 0\n  for i in 0..<4 {\n    t = t + i\n  }\n  let (u, u) = (1, 2)\n  t\n}\n";
    let (a, module) = analysis(src);
    let ast = &module.parsed.ast;
    let n = names(&a, "n");
    assert_eq!(binding_names(n), ["q", "x", "y"]);
    let x = &n.bindings[1];
    assert_eq!(x.kind, BindingKind::MatchBind);
    assert_eq!(x.sites.len(), 4);
    for p in &x.sites {
        assert!(matches!(&ast.pat(*p).kind, PatKind::Bind(id) if id.name == "x"));
        assert_eq!(n.pats.get(p), Some(&PatRes::Bind(BindingId(1))));
    }
    let Origin::Arm { scrutinee, arm: 0 } = x.origin else { panic!("{:?}", x.origin) };
    assert!(matches!(&ast.expr(scrutinee).kind, ExprKind::Path(p) if p.segments[0].name == "q"));
    assert!(matches!(n.bindings[2].origin, Origin::Arm { arm: 1, .. }));
    // The two arms are sibling scopes under the block of the body.
    let (sx, sy) = (n.bindings[1].scope, n.bindings[2].scope);
    assert_ne!(sx, sy);
    assert_eq!(n.scopes[sx.0 as usize].parent, n.scopes[sy.0 as usize].parent);

    let s = names(&a, "s");
    assert_eq!(binding_names(s), ["t", "i", "u", "u"]);
    let i = &s.bindings[1];
    assert_eq!(i.kind, BindingKind::For { moved: false });
    assert!(matches!(i.origin, Origin::For(_)));
    assert_eq!(i.sites.len(), 1);
    // `t` is read twice (`t + i` and the result), assigned once.
    assert_eq!((s.bindings[0].reads, i.reads), (2, 1));
    // Two bindings of one name in one pattern are two bindings (E0304).
    assert_ne!(s.bindings[2].sites, s.bindings[3].sites);
}

#[test]
fn self_and_the_holes_of_a_string_are_bindings_of_the_scopes_of_the_body() {
    let src = "pub struct P { x: I32 }\nimpl P {\n  pub fn m(self, n: I32) -> Str {\n    let y = self.x + n\n    \"{y} and {n}\"\n  }\n}\n";
    let (a, _) = analysis(src);
    let n = names(&a, "m");
    assert!(n.complete);
    assert_eq!(binding_names(n), ["self", "n", "y"]);
    let me = &n.bindings[0];
    assert_eq!((me.kind, me.origin), (BindingKind::SelfParam(Mode::Borrow), Origin::SelfParam));
    assert!(me.sites.is_empty());
    assert_eq!(n.bindings[1].origin, Origin::Param(0));
    // The parameters are in the first scope; the `let` in the block under it.
    assert_eq!((me.scope, n.scopes[0].parent), (ScopeId(0), None));
    let y = &n.bindings[2];
    assert_eq!(n.scopes[y.scope.0 as usize].parent, Some(ScopeId(0)));
    assert_eq!(n.scopes[y.scope.0 as usize].bindings, [BindingId(2)]);
    let mut holes: Vec<_> = n.interp.iter().map(|((_, k), r)| (*k, r.clone())).collect();
    holes.sort_by_key(|(k, _)| *k);
    assert_eq!(holes, [(0, vec![(0, PathRes::Local(BindingId(2)))]), (2, vec![(0, PathRes::Local(BindingId(1)))])]);
    assert_eq!((me.reads, n.bindings[1].reads, y.reads), (1, 2, 1));
}

#[test]
fn a_type_argument_in_an_expression_stops_the_walk_of_its_body() {
    let src = "pub struct Q[T] { v: T }\npub fn id(x: I32) -> I32 { x }\npub fn t() -> I32 {\n  let a = 1\n  let b = id::[I32](a)\n  let c = 2\n  c\n}\npub fn s() -> I32 {\n  let k = 1\n  let q = Q::[I32] { v: k }\n  0\n}\npub fn r() -> I32 {\n  let k = 1\n  let q = Q { v: k }\n  0\n}\nconst K: I32 = 1\ntest \"w\" {\n  let w = K\n  assert w == 1\n}\n";
    let (a, _) = analysis(src);
    let t = names(&a, "t");
    assert!(!t.complete);
    assert_eq!(binding_names(t), ["a"]);
    assert_eq!(t.bindings[0].reads, 0);
    let s = names(&a, "s");
    assert!(!s.complete);
    assert_eq!(s.bindings[0].reads, 0);
    let r = names(&a, "r");
    assert!(r.complete);
    assert_eq!(r.bindings[0].reads, 1);
    // The struct of a literal is resolved from W4-04 U2b.
    assert!(r.structs.is_empty());
    // A `const` and a test have a record too.
    assert!(names(&a, "K").complete && names(&a, "K").bindings.is_empty());
    let w = names(&a, "test \"w\"");
    assert!(w.complete);
    assert_eq!((binding_names(w), w.bindings[0].reads), (vec!["w"], 1));
}
